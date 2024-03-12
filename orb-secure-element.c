/**
 * @file orb-secure-element.c
 * @brief A tool for generating cryptographical signatures for Iris code using
 * SE050
 *
 * The tool accepts no command line arguments.
 *
 * It reads a SHA256 hash from standart input and produce signature
 * on stdout. All errors are logged to stderr.
 *
 * Exists with 0 exit code if signing was successfull.
 *
 * Usage examples:
 *
 * 0. Assuming that iris_code is stored in iris_code.bin file and you want to
 * get its signature in iris_code.signature
 *
 * 1. Run orb-secure-element and feed its base64 encoded data:
 *
 * $ cat iris_code.bin | openssl dgst -sha256 -binary | base64 | \
 * ./orb-secure-element | base64 -d > iris_code.signature
 *
 * 2. Verify the signature
 *
 * openssl dgst -sha256 -verify
 * /usr/persistent/se/keystore/sss_<keyid>_0002_0040.bin -signature \
 * iris_code.signature iris_code.bin
 */

#include "fsl_sss_api.h"
#include <errno.h>
#include <fsl_sss_se05x_apis.h>
#include <limits.h>
#include <nxLog_App.h>
#include <openssl/bio.h>
#include <openssl/evp.h>
#include <openssl/sha.h>
#include <se05x_APDU.h>
#include <seccomp.h>
#include <signal.h>
#include <stdio.h>
#include <string.h>
#include <sys/file.h>
#include <sys/stat.h>

#include <linux/seccomp.h> /* Definition of SECCOMP_* constants */
#include <sys/prctl.h>

// Hard-coded path to plug-and-trust keystorage
//
#define KEYSTORE_PATH "/usr/persistent/se/keystore"

// Session key for opening connection to SE050
#define JETSON_ECKEY_AUTH (0x70000000)

// Timeout for secure element operations, if exceeded, the application
// terminates
#define SE_TIMEOUT 10

// How many APDU commands can be sent in one session
// ADPUs sent:
// Se05x_API_ECDSASign
// Se05x_API_CloseSession
// SM_Close
#define MAX_ADPU_IN_SESSION 3
// Custom error codes
//

#define EXIT_SIGN_FAILED     1
#define EXIT_TIMEOUT         2
#define EXIT_NOT_PROVISIONED 3
#define EXIT_BAD_INPUT       4
#define EXIT_INTERNAL_ERROR  5

// Helper macro for checking for errors. If 'func' returns not
//'kStatus_SSS_Success', print a message and jump to 'out'
#define CALL_WITH_CHECK(func, msg, out)                                        \
    {                                                                          \
        status = func;                                                         \
        if (status != kStatus_SSS_Success) {                                   \
            LOG_E(msg "function: " #func " on: " __FILE__ ":%d failed. ",      \
                  __LINE__);                                                   \
            goto out;                                                          \
        }                                                                      \
    }

/// List of syscalls which the binary is allowed to use
const static int allowed_syscalls[] = {
    SCMP_SYS(bind),      SCMP_SYS(brk),          SCMP_SYS(clock_nanosleep),
    SCMP_SYS(close),     SCMP_SYS(exit),         SCMP_SYS(exit_group),
    SCMP_SYS(faccessat), SCMP_SYS(flock),        SCMP_SYS(fstat),
    SCMP_SYS(fsync),     SCMP_SYS(futex),        SCMP_SYS(getpid),
    SCMP_SYS(getrandom), SCMP_SYS(gettid),       SCMP_SYS(ioctl),
    SCMP_SYS(lseek),     SCMP_SYS(nanosleep),    SCMP_SYS(openat),
    SCMP_SYS(prctl),     SCMP_SYS(read),         SCMP_SYS(recv),
    SCMP_SYS(recvfrom),  SCMP_SYS(rt_sigaction), SCMP_SYS(send),
    SCMP_SYS(sendto),    SCMP_SYS(setitimer),    SCMP_SYS(setsockopt),
    SCMP_SYS(sigreturn), SCMP_SYS(socket),       SCMP_SYS(unlinkat),
    SCMP_SYS(write),     SCMP_SYS(writev),
};

#define EC_KEY_SIZE             256
#define SCP03_MAX_AUTH_KEY_SIZE 52

static sss_status_t prepare_host_eckey(
    SE05x_AuthCtx_ECKey_t *auth, sss_key_store_t *host_key_store,
    uint32_t host_ECDSA_pair_keyid /*key id of host ECkey pair. *.HOST.ECDSA */,
    uint32_t SE_ECKA_pub_keyid /*Key id of PK.SE.ECKA on host*/)
{
    sss_status_t status = kStatus_SSS_Fail;

    // We need to have a few transient keys created, first key id is
    // `host_ephemeral_key'
    const uint32_t host_ephemeral_key = 0x800;
    auth->pStatic_ctx = calloc(sizeof(*auth->pStatic_ctx), 1);
    auth->pDyn_ctx = calloc(sizeof(*auth->pDyn_ctx), 1);
    if (auth->pStatic_ctx == NULL || auth->pDyn_ctx == NULL) {
        goto free;
    }

    /* Init master secret */
    CALL_WITH_CHECK(
        sss_key_object_init(&auth->pStatic_ctx->masterSec, host_key_store), "",
        free);
    CALL_WITH_CHECK(sss_key_object_allocate_handle(
                        &auth->pStatic_ctx->masterSec, host_ephemeral_key + 1,
                        kSSS_KeyPart_Default, kSSS_CipherType_AES,
                        SCP03_MAX_AUTH_KEY_SIZE, kKeyObject_Mode_Transient),
                    "", free);

    /* Init Allocate ENC Session Key */
    CALL_WITH_CHECK(sss_key_object_init(&auth->pDyn_ctx->Enc, host_key_store),
                    "", free_masterSec);
    CALL_WITH_CHECK(sss_key_object_allocate_handle(
                        &auth->pDyn_ctx->Enc, host_ephemeral_key + 2,
                        kSSS_KeyPart_Default, kSSS_CipherType_AES,
                        SCP03_MAX_AUTH_KEY_SIZE, kKeyObject_Mode_Transient),
                    "", free_ENC_session_key);

    /* Init Allocate MAC Session Key */
    CALL_WITH_CHECK(sss_key_object_init(&auth->pDyn_ctx->Mac, host_key_store),
                    "", free_ENC_session_key);
    CALL_WITH_CHECK(sss_key_object_allocate_handle(
                        &auth->pDyn_ctx->Mac, host_ephemeral_key + 3,
                        kSSS_KeyPart_Default, kSSS_CipherType_AES,
                        SCP03_MAX_AUTH_KEY_SIZE, kKeyObject_Mode_Transient),
                    "", free_ENC_session_key);

    /* Init Allocate DEC/Rmac Session Key */
    CALL_WITH_CHECK(sss_key_object_init(&auth->pDyn_ctx->Rmac, host_key_store),
                    "", free_MAC_session_key);
    CALL_WITH_CHECK(sss_key_object_allocate_handle(
                        &auth->pDyn_ctx->Rmac, host_ephemeral_key + 4,
                        kSSS_KeyPart_Default, kSSS_CipherType_AES,
                        SCP03_MAX_AUTH_KEY_SIZE, kKeyObject_Mode_Transient),
                    "", free_MAC_session_key);

    return kStatus_SSS_Success;
free_DEC_session_key:
    sss_key_object_free(&auth->pDyn_ctx->Rmac);
free_MAC_session_key:
    sss_key_object_free(&auth->pDyn_ctx->Mac);
free_ENC_session_key:
    sss_key_object_free(&auth->pDyn_ctx->Enc);
free_masterSec:
    sss_key_object_free(&auth->pStatic_ctx->masterSec);
free:
    free(auth->pStatic_ctx);
    free(auth->pDyn_ctx);
out:
    return status;
}

void free_session_keys(SE05x_AuthCtx_ECKey_t *auth)
{
    // This destructor should be synchronised with prepare_host_eckey()
    sss_key_object_free(&auth->pDyn_ctx->Rmac);
    sss_key_object_free(&auth->pDyn_ctx->Mac);
    sss_key_object_free(&auth->pDyn_ctx->Enc);
    sss_key_object_free(&auth->pStatic_ctx->masterSec);
    free(auth->pStatic_ctx);
    free(auth->pDyn_ctx);
}

sss_status_t open_se050_session(sss_session_t *host_session,
                                sss_key_store_t *host_keystore,
                                sss_session_t *se050_session,
                                SE_Connect_Ctx_t *connectCtx)
{
    sss_status_t status;
    int ret;

    LOG_I("Open ECkey connection to SE");

    connectCtx->connType = kType_SE_Conn_Type_T1oI2C;
    connectCtx->auth.authType = kSSS_AuthType_ECKey;
    connectCtx->session_policy = calloc(sizeof(sss_policy_session_u), 1);
    if (!connectCtx->session_policy) {
        LOG_E("Failed to allocate session policy");
        status = kStatus_SSS_Fail;
        goto out;
    }

    CALL_WITH_CHECK(prepare_host_eckey(&connectCtx->auth.ctx.eckey,
                                       host_keystore, JETSON_ECKEY_AUTH,
                                       kSE05x_AppletResID_KP_ECKEY_USER),
                    "", free_session_policy);
    connectCtx->session_policy->has_MaxDurationOfSession_sec = true;
    connectCtx->session_policy->maxDurationOfSession_sec = SE_TIMEOUT;
    connectCtx->session_policy->has_MaxOperationsInSession = true;
    connectCtx->session_policy->maxOperationsInSession = MAX_ADPU_IN_SESSION;
    connectCtx->session_policy->allowRefresh = false;
    CALL_WITH_CHECK(sss_session_open(se050_session, kType_SSS_SE_SE05x,
                                     JETSON_ECKEY_AUTH,
                                     kSSS_ConnectionType_Encrypted, connectCtx),
                    "", free_session_keys);

    return status;

free_session_keys:
    free_session_keys(&connectCtx->auth.ctx.eckey);
free_session_policy:
    free(connectCtx->session_policy);
out:
    return status;
}

/** Sign SHA256 Digest
 *
 */
static sss_status_t sign_digest(sss_session_t *se050_session,
                                const char *iris_code_digest,
                                const size_t iris_code_digest_sz,
                                char *iris_code_signature,
                                size_t *iris_code_signature_sz)
{
    uint32_t keyid = SE050_SIGN_KEY;
    sss_status_t status = kStatus_SSS_Success;
    smStatus_t sm_status;
    Se05xSession_t *pSe05xSession =
        &((sss_se05x_session_t *)se050_session)->s_ctx;
    SE05x_Result_t result = kSE05x_Result_FAILURE;

    if (SHA256_DIGEST_LENGTH != iris_code_digest_sz) {
        LOG_E("Unexpected length of digest, expected %d, got %zu",
              SHA256_DIGEST_LENGTH, iris_code_digest_sz);
        goto err;
    }
    SE05x_ECSignatureAlgo_t ecSignAlgo = kSE05x_ECSignatureAlgo_SHA_256;
    sm_status = Se05x_API_ECDSASign(
        pSe05xSession, keyid, ecSignAlgo, iris_code_digest,
        SHA256_DIGEST_LENGTH, iris_code_signature, iris_code_signature_sz);

    if (sm_status != SM_OK) {
        LOG_E("Signing failed: %x", sm_status);
        goto err;
    }
    LOG_AU8_I(iris_code_signature, *iris_code_signature_sz);

    return kStatus_SSS_Success;
err:
    return kStatus_SSS_Fail;
}

/** Read the sha256 digest from 'f'. It is expected that input contains a single
 * hash.
 */
static sss_status_t read_digest(BIO *bio_in, char *digest,
                                const size_t digest_sz)
{
    BIO *b64;
    int ret;
    char tmp[1];

    /* setup base64 decoder */
    b64 = BIO_new(BIO_f_base64());
    BIO_set_flags(b64, BIO_FLAGS_BASE64_NO_NL);
    bio_in = BIO_push(b64, bio_in);

    /* Read the hash */
    ret = BIO_read(bio_in, digest, digest_sz);
    if (ret < 0) {
        LOG_E("Reading from stdin failed");
        goto err;
    }

    if (ret != digest_sz) {
        LOG_E("Digest(hash) is too short, read %d bytes, expected %zu", ret,
              digest_sz);
        goto err;
    }

    /* Check if there is extra data after the hash */
    ret = BIO_read(bio_in, tmp, sizeof(tmp));
    if (ret != 0) {
        LOG_E("Extra data after hash, expected %zu bytes, got more", digest_sz);
        goto err;
    }

    BIO_pop(b64);
    BIO_free(b64);
    return kStatus_SSS_Success;

err:
    return kStatus_SSS_Fail;
}

/** Print base64 encoded signature
 */
static sss_status_t print_signature(FILE *f, const char *signature,
                                    const size_t signature_sz)
{
    BIO *bio_out, *b64;
    int ret;

    /* setup output BIO chain */
    bio_out = BIO_new_fp(f, BIO_NOCLOSE);

    /* setup base64 encoder */
    b64 = BIO_new(BIO_f_base64());
    bio_out = BIO_push(b64, bio_out);
    BIO_set_flags(bio_out, BIO_FLAGS_BASE64_NO_NL); // Write everything in one
                                                    // line

    /* Writing using BIO_write produces base64 output */
    ret = BIO_write(bio_out, signature, signature_sz);
    if (ret < 0) {
        LOG_E("Failed to write base64 output: %d", ret);
        goto err;
    }
    if (ret != signature_sz) {
        LOG_E("Output truncated to %d bytes", ret);
        goto err;
    }

    BIO_flush(bio_out);
    /* Tell BIO to close stdout on BIO_free_all()*/
    BIO_set_close(bio_out, 1);
    BIO_free_all(bio_out);
    return kStatus_SSS_Success;
err:
    BIO_free_all(bio_out);
    return kStatus_SSS_Fail;
}

static sss_status_t sign_iris_code(const char *digest, const size_t digest_sz,
                                   char *signature, size_t *signature_sz)
{

    sss_session_t host_session = {0};
    sss_key_store_t host_keystore = {0};
    sss_session_t se050_session = {0};
    sss_status_t status = kStatus_SSS_Success;
    SE_Connect_Ctx_t *connectCtx;

    connectCtx = calloc(sizeof(SE_Connect_Ctx_t), 1);

    if (connectCtx == NULL) {
        LOG_E("Out of memory");
        status = kStatus_SSS_Fail;
        goto out;
    };

    CALL_WITH_CHECK(sss_session_open(&host_session, kType_SSS_Software, 0,
                                     kSSS_ConnectionType_Plain, KEYSTORE_PATH),
                    "", free_connection_ctx);
    CALL_WITH_CHECK(sss_key_store_context_init(&host_keystore, &host_session),
                    "", host_session_close);
    CALL_WITH_CHECK(sss_key_store_load(&host_keystore),
                    "Failed to load keystore from \"" KEYSTORE_PATH "\" ",
                    host_keystore_free);

    CALL_WITH_CHECK(open_se050_session(&host_session, &host_keystore,
                                       &se050_session, connectCtx),
                    "", host_keystore_free);

    CALL_WITH_CHECK(
        sign_digest(&se050_session, digest, digest_sz, signature, signature_sz),
        "", se050_session_close);

    /* Key store is deliberately not saved, we don't expect any new keys to be
     * created on the host side */

    /* CALL_WITH_CHECK(sss_key_store_save(&host_keystore), "",
     * host_keystore_free); */

se050_session_close:
    sss_session_close(&se050_session);
    free_session_keys(&connectCtx->auth.ctx.eckey);
    free(connectCtx->session_policy);
host_keystore_free:
    sss_key_store_context_free(&host_keystore);
host_session_close:
    sss_session_close(&host_session);
free_connection_ctx:
    free(connectCtx);

out:
    return status;
}

static void alarm_handler(int unused)
{
#ifdef NEVER_FAIL
    LOG_E("Timeout waiting from SE050, print fake base64");
    printf(
        "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
        "fffffffffffffffffffffffffff");
    exit(0);
#else  // NEVER_FAIL
    LOG_E("Timeout waiting from SE050");
    exit(EXIT_TIMEOUT);
#endif // NEVER_FAIL
}

static int init_seccomp(void)
{
    scmp_filter_ctx ctx;
    int rc;

    ctx = seccomp_init(SCMP_ACT_KILL);
    if (ctx == NULL)
        goto err;

    for (int i = 0; i < ARRAY_SIZE(allowed_syscalls); i++) {
        rc = seccomp_rule_add(ctx, SCMP_ACT_ALLOW, allowed_syscalls[i], 0);
        if (rc != 0)
            goto err;
    }

    rc = seccomp_load(ctx);
    if (rc < 0)

        goto err;
    return 0;
err:
    LOG_E("Failed to initialize seccomp");
    return -1;
}

// Puts a lock on on /usr/persistent/se/keystore/sss_fat.bin. If any other
// process is is using plug&trust, it will wait. The file description is not
// saved, but that is ok, because the lock will be released when the process
// terminates.
static int lock_executable(void)
{
    int fd = open(KEYSTORE_PATH "/" FAT_FILENAME, O_RDONLY);
    if (fd < 0) {
        return -1;
    }

    return flock(fd, LOCK_EX);
}

int main(int argc, char *argv[])
{
    sss_status_t status = kStatus_SSS_Success;
    char digest[SHA256_DIGEST_LENGTH];
    size_t digest_sz = sizeof(digest);
    char signature[256];
    size_t signature_sz = sizeof(signature);
    BIO *bio_in;
    struct sigaction act = {0};
    int ret = EXIT_SUCCESS;

    ret = prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0, 0);
    if (ret < 0) {
        LOG_E("Failed to set PR_SET_NO_NEW_PRIVS: errno: %d", errno);
        return 99;
    }

    ret = init_seccomp();
    if (ret < 0) {
        LOG_E("Failed to initialize seccomp");
        return EXIT_INTERNAL_ERROR;
    }

    if (argc > 2) {
        LOG_E("Too many arguments, 1 expected");
        ret = EXIT_BAD_INPUT;
        goto out;
    }

    if (argc == 1) {
        /* read digest from stdin */
        bio_in = BIO_new_fp(stdin, BIO_NOCLOSE);
    } else {
        /* Take digest from cmdline */
        bio_in = BIO_new_mem_buf(argv[1], -1);
    }

    if (0 != lock_executable()) {
#ifdef NEVER_FAIL
        LOG_E("Failed to acquire lock on " KEYSTORE_PATH "/" FAT_FILENAME
              ", printing a pre-defined signature");
        printf("ddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd"
               "dddd"
               "ddddddddddddddddddddddddddddd");
        ret = EXIT_SUCCESS;
#else  // NEVER_FAIL
        LOG_E("Failed to acquire lock on " KEYSTORE_PATH "/" FAT_FILENAME);
        ret = EXIT_INTERNAL_ERROR;
#endif // NEVER_FAIL
        goto free_bio;
    }

    status = read_digest(bio_in, digest, digest_sz);
    if (status != kStatus_SSS_Success) {
        LOG_E("Failed to read digest");
        ret = EXIT_BAD_INPUT;
        goto free_bio;
    }

    act.sa_flags = SA_RESTART;
    act.sa_handler = &alarm_handler;

    if (-1 == sigaction(SIGALRM, &act, NULL)) {
        perror("sigalarm");
        ret = EXIT_INTERNAL_ERROR;
        goto free_bio;
    }

    alarm(SE_TIMEOUT);
    status = sign_iris_code(digest, digest_sz, signature, &signature_sz);
    alarm(0);

    if (status != kStatus_SSS_Success) {
#ifdef NEVER_FAIL
        LOG_E(
            "Failed to sign digest, err: %x, printing a pre-defined signature",
            status);
        printf("eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee"
               "eeeeee"
               "eeeeeeeeeeeeeeeeeeeeeeeeeee");
        ret = EXIT_SUCCESS;
#else  // NEVER_FAIL
        LOG_E("Failed to sign digest: %x", status);
        ret = EXIT_SIGN_FAILED;
#endif // NEVER_FAIL

        goto free_bio;
    } else {
        LOG_I("Successfully signed digest");
        delete_old_pairing_keys();
    }

    status = print_signature(stdout, signature, signature_sz);
    if (status != kStatus_SSS_Success) {
        LOG_E("Failed to print signature");
        ret = EXIT_INTERNAL_ERROR;
        goto free_bio;
    }

free_bio:
    BIO_free_all(bio_in);
out:

    return ret;
}

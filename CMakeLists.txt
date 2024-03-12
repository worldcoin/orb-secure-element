CMAKE_MINIMUM_REQUIRED(VERSION 3.5.0)

project (orb-secure-element)

set(name "orb-sign-iris-code")
SET(
    APPS
    orb-sign-iris-code
    orb-sign-attestation
)

SET(
    SE050_SIGN_KEY
    0x70000002
    0x70000001
)

foreach(n IN ZIP_LISTS APPS SE050_SIGN_KEY)
    add_executable(${n_0} orb-secure-element.c)
    target_compile_definitions(${n_0} PRIVATE SE050_SIGN_KEY=${n_1})

    target_link_libraries(${n_0} plug_and_trust crypto seccomp)
    target_include_directories(
        ${n_0}
        PUBLIC
        ../
        ${INC_DIR}
        )
endforeach()

install(TARGETS ${APPS} RUNTIME)

ADD_DEFINITIONS(-DSSS_USE_FTR_FILE)
ADD_DEFINITIONS(-DSMCOM_T1oI2C)
ADD_DEFINITIONS(-DT1oI2C)
ADD_DEFINITIONS(-DT1oI2C_UM11225)

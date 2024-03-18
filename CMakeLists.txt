CMAKE_MINIMUM_REQUIRED(VERSION 3.15.0)
include(FetchContent)
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

ADD_DEFINITIONS(-DSSS_USE_FTR_FILE)
ADD_DEFINITIONS(-DSMCOM_T1oI2C)
ADD_DEFINITIONS(-DT1oI2C)
ADD_DEFINITIONS(-DT1oI2C_UM11225)

FetchContent_Declare(
  plugandtrust
  GIT_REPOSITORY https://github.com/NXP/plug-and-trust.git
  GIT_TAG        5137b450fcdeb034f7713fecd37d5d565f4309d4 #v04.05.00
)
FetchContent_MakeAvailable(plugandtrust)
set(SIMW_LIB_DIR ${plugandtrust_SOURCE_DIR})
include(${plugandtrust_SOURCE_DIR}/simw_lib.cmake)

foreach(n IN ZIP_LISTS APPS SE050_SIGN_KEY)
    add_executable(${n_0} orb-secure-element.c ${SIMW_SE_SOURCES} ${SIMW_SE_AUTH_SOURCES})
    target_compile_definitions(${n_0} PRIVATE SE050_SIGN_KEY=${n_1})

    target_link_libraries(${n_0} crypto seccomp)
    target_include_directories(
        ${n_0}
        PUBLIC
        ./
        )

    TARGET_INCLUDE_DIRECTORIES(
        ${n_0}
        PUBLIC
        ${SIMW_INC_DIR}
    )

endforeach()
install(TARGETS ${APPS} RUNTIME)

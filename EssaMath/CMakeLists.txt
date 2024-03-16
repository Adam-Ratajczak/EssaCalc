project("EssaMath"
    VERSION 1.0.1
    DESCRIPTION "Essa Math library"
)
include(${PROJECT_SOURCE_DIR}/cmake/SetEnv.cmake)

file(GLOB_RECURSE SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/src/cxx/*.c" "${CMAKE_CURRENT_SOURCE_DIR}/src/cxx/*.cpp")
file(GLOB_RECURSE HEADERS_PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include/*.h" "${CMAKE_CURRENT_SOURCE_DIR}/include/*.hpp")
file(GLOB_RECURSE CORE_LISP_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/src/lisp/*.lisp" "${CMAKE_CURRENT_SOURCE_DIR}/src/lisp/*.asd")

add_custom_command(OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/maxima.a
  COMMAND ${ECL_BIN_PATH} --norc
  --eval '(require :asdf)'
  --eval '(push \"${CMAKE_CURRENT_SOURCE_DIR}/src/lisp/\" asdf:*central-registry*)'
  --eval '(asdf:make-build :maxima :type :static-library :move-here \"${CMAKE_CURRENT_BINARY_DIR}\" :init-name \"init_lib_MAXIMA\")'
  --eval '(quit)'
  DEPENDS ${CORE_LISP_SOURCES})

include(${PROJECT_SOURCE_DIR}/cmake/LibraryConfig.cmake)

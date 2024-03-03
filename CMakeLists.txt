cmake_minimum_required(VERSION 3.17)
project(EssaMath CXX)

set(CMAKE_MODULE_PATH "${CMAKE_MODULE_PATH}" "${CMAKE_SOURCE_DIR}/cmake/Modules/")
set(CMAKE_EXPORT_COMPILE_COMMANDS 1)

# find_package(PkgConfig REQUIRED)

# pkg_check_modules(GTK4 REQUIRED gtk4)
# include_directories(${GTK4_INCLUDE_DIRS})

find_package(ECL REQUIRED)
include_directories(${ECL_INCLUDE_DIR})

file(GLOB_RECURSE SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/src/cxx/EssaMath/*.c" "${CMAKE_CURRENT_SOURCE_DIR}/src/cxx/*.cpp")
file(GLOB_RECURSE CORE_LISP_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/src/lisp/*.lisp" "${CMAKE_CURRENT_SOURCE_DIR}/src/lisp/*.asd")

add_executable(EssaMath ${SOURCES})

add_custom_command(OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/maxima.a
  COMMAND ${ECL_BIN_PATH} --norc
  --eval '(require :asdf)'
  --eval '(push \"${CMAKE_CURRENT_SOURCE_DIR}/src/lisp/\" asdf:*central-registry*)'
  --eval '(asdf:make-build :maxima :type :static-library :move-here \"${CMAKE_CURRENT_BINARY_DIR}\" :init-name \"init_lib_MAXIMA\")'
  --eval '(quit)'
  DEPENDS ${CORE_LISP_SOURCES})

add_custom_target(maxima ALL DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/maxima.a)

add_dependencies(EssaMath maxima)

target_link_libraries(EssaMath
  ${ECL_LIBRARIES}
  ${CMAKE_CURRENT_BINARY_DIR}/maxima.a
  m  # Link against the math library
)

# target_link_libraries(EssaMath ${GTK4_LIBRARIES})

# Install the executable to /usr/local/bin
install(TARGETS EssaMath DESTINATION /usr/local/bin)

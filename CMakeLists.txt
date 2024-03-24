cmake_minimum_required(VERSION 3.17)

set(CMAKE_MODULE_PATH "${CMAKE_MODULE_PATH}" "${CMAKE_SOURCE_DIR}/cmake/Modules/")
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED true)
set(BUILD_SHARED_LIBS ON)

find_package(ECL REQUIRED)
include_directories(${ECL_INCLUDE_DIR})

add_subdirectory(EssaMath)
# add_subdirectory(Tests)

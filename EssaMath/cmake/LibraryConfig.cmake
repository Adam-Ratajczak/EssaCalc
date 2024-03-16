# Target
add_library(EssaMath
  ${SOURCES}
  ${HEADERS_PUBLIC}
  ${HEADERS_PRIVATE}
  )

# Alias:
#   - Foo::foo alias of foo
add_library(Essa::Math ALIAS EssaMath)

add_custom_target(maxima ALL DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/maxima.a)
add_dependencies(EssaMath maxima)

target_link_libraries(EssaMath
  ${ECL_LIBRARIES}
  ${CMAKE_CURRENT_BINARY_DIR}/maxima.a
  m  # Link against the math library
)

# C++11
target_compile_features(EssaMath PUBLIC cxx_std_11)

target_compile_definitions(EssaMath PUBLIC
  "${PROJECT_NAME_UPPERCASE}_DEBUG=$<CONFIG:Debug>")

# Global includes. Used by all targets
# Note:
#   - header can be included by C++ code `#include <foo/foo.h>`
#   - header location in project: ${CMAKE_CURRENT_BINARY_DIR}/generated_headers
target_include_directories(
  EssaMath PUBLIC
    "$<BUILD_INTERFACE:${PROJECT_SOURCE_DIR}>"
    "$<BUILD_INTERFACE:${GENERATED_HEADERS_DIR}>"
    "$<INSTALL_INTERFACE:.>"
)

install(
    TARGETS              "EssaMath"
    EXPORT               "${TARGETS_EXPORT_NAME}"
    LIBRARY DESTINATION  "${CMAKE_INSTALL_LIBDIR}"
    ARCHIVE DESTINATION  "${CMAKE_INSTALL_LIBDIR}"
    RUNTIME DESTINATION  "${CMAKE_INSTALL_BINDIR}"
    INCLUDES DESTINATION "${CMAKE_INSTALL_INCLUDEDIR}"
)

install(
    FILES ${HEADERS_PUBLIC}
    DESTINATION "${CMAKE_INSTALL_INCLUDEDIR}/Essa/Math"
)

install(
    FILES       "${GENERATED_HEADERS_DIR}/essa/version.h"
    DESTINATION "${CMAKE_INSTALL_INCLUDEDIR}/Essa/Math"
)

install(
    FILES       "${PROJECT_CONFIG_FILE}"
                "${VERSION_CONFIG_FILE}"
    DESTINATION "${CONFIG_INSTALL_DIR}"
)

# Config
#   - <prefix>/lib/cmake/Foo/FooTargets.cmake
install(
  EXPORT      "${TARGETS_EXPORT_NAME}"
  FILE        "$EssaMathTargets.cmake"
  DESTINATION "${CONFIG_INSTALL_DIR}"
  NAMESPACE   "$Essa::"
)

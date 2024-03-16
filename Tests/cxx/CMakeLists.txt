project(MyTest)

find_package(EssaMath REQUIRED)

add_executable(MyTest main.cpp)

target_link_libraries(MyTest PRIVATE EssaMath)

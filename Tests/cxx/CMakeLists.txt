project(MyTest)

find_package(EssaMath 1.0.1 CONFIG REQUIRED)

add_executable(MyTest main.cpp)

target_link_libraries(MyTest PRIVATE EssaMath::essamath)

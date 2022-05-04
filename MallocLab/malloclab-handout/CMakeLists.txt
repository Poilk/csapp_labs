project(malloc)

foreach(version std book-sample baseline)
    set(target_name phony-${PROJECT_NAME}-${version})
    # just for clion code insight
    add_executable(${target_name} mdriver.c mm-${version}.c memlib.c fsecs.c fcyc.c clock.c ftimer.c driverlib.c)
    target_compile_definitions(${target_name} PUBLIC DRIVER)

    # real build and test command
    add_custom_target(malloc-${version}-test
            COMMAND make clean && make VERSION=${version}
            COMMAND ./mdriver -l
            WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})
endforeach()
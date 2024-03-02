#include <codecvt>
#include <iostream>
#include <locale>
#include <stdio.h>
#include <ecl/ecl.h>
#include <stdlib.h>
#include <string.h>
#include <string>
#include "LispApi.hpp"

extern "C"{
    void init_lib_MAXIMA(cl_object);
} 

void init_ecl(int argc, char **argv){
    cl_boot(argc, argv);
    ecl_init_module(NULL, init_lib_MAXIMA);
}

void free_ecl(){
    cl_shutdown();
}

std::string evaluate(std::string _exp) {
    _exp = "\"" + _exp + "\"";
    cl_object arg1 = c_string_to_object(_exp.c_str());
    cl_object name = ecl_make_symbol("api-eval", "MAXIMA");
    cl_object output = cl_funcall(2, name, arg1);

    static_assert(sizeof(ecl_character)==sizeof(wchar_t),"sizes must be the same");
    
    std::wstring _str = reinterpret_cast<wchar_t*>(output->string.self);
    _str = _str.substr(0, _str.find_last_of(L")") + 1);
    using convert_typeX = std::codecvt_utf8<wchar_t>;
    std::wstring_convert<convert_typeX, wchar_t> converterX;

    return converterX.to_bytes(_str);
}


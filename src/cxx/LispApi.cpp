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

void evaluate(std::string _exp, std::string& _res, std::string& _err) {
    _exp = "\"" + _exp + "\"";
    cl_object arg1 = c_string_to_object(_exp.c_str());
    cl_object name = ecl_make_symbol("api-eval", "MAXIMA");
    cl_object output = cl_funcall(2, name, arg1);

    static_assert(sizeof(ecl_character)==sizeof(wchar_t),"sizes must be the same");
    
    std::wstring _str = reinterpret_cast<wchar_t*>(output->string.self);
    using convert_typeX = std::codecvt_utf8<wchar_t>;
    std::wstring_convert<convert_typeX, wchar_t> converterX;

    if(_str.find(L"SIMP")){
        _str = _str.substr(0, _str.find_last_of(L")") + 1);
        _res = converterX.to_bytes(_str);
        std::string::size_type _pos = _res.find("\n");
        while(_pos != std::string::npos){
            _res = _res.substr(0, _pos) + _res.substr(_pos + 1);
            _pos = _res.find("\n");
        }
        _err = "";
    }else{
        _err = converterX.to_bytes(_str);
        _res = "";
    }
}


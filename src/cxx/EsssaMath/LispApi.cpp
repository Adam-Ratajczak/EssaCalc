#include <codecvt>
#include <iostream>
#include <locale>
#include <stdexcept>
#include <stdio.h>
#include <ecl/ecl.h>
#include <stdlib.h>
#include <string.h>
#include <string>

std::string to_lower(std::string const& _str){
    std::string _result;
    for(auto& c : _str){
        _result += std::tolower(c);
    }

    return _result;
}

std::string get_type(std::istream& _ss){
    char c;

    std::string result;
    while(!_ss.eof()){
        _ss.read(&c, 1);

        if(c == ' ' || c == ')'){
            break;
        }

        result += c;
    }

    return result;
}

extern "C"{
    void init_lib_MAXIMA(cl_object);
} 

namespace Essa::Math {

std::string evaluate(const std::string& _exp) {
    try{
        std::string exp = "\"" + _exp + ";\"";
        
        cl_object arg1 = c_string_to_object(exp.c_str());
        cl_object name = ecl_make_symbol("api-eval", "MAXIMA");
        cl_object output = cl_funcall(2, name, arg1);

        static_assert(sizeof(ecl_character)==sizeof(wchar_t),"sizes must be the same");
            
        std::wstring _str = reinterpret_cast<wchar_t*>(output->string.self);

        using convert_typeX = std::codecvt_utf8<wchar_t>;
        std::wstring_convert<convert_typeX, wchar_t> converterX;

        std::string _res = converterX.to_bytes(_str);

        auto _pos = _res.find(" SIMP");
        while(_pos != std::string::npos){
            _res = _res.substr(0, _pos) + _res.substr(_pos + 5);
            _pos = _res.find(" SIMP");
        }

        _pos = _res.find(" RATSIMP");
        while(_pos != std::string::npos){
            _res = _res.substr(0, _pos) + _res.substr(_pos + 8);
            _pos = _res.find(" RATSIMP");
        }

        return _res;
    }catch(std::range_error&){
        return evaluate(_exp);
    }
}

void load(const std::string& path){
    std::string exp = "\"" + path + "\"";
        
    cl_object arg1 = c_string_to_object(exp.c_str());
    cl_object name = ecl_make_symbol("api-load", "MAXIMA");
    cl_object output = cl_funcall(2, name, arg1);
}

void init_math(int argc, char **argv){
    cl_boot(argc, argv);
    ecl_init_module(NULL, init_lib_MAXIMA);

    cl_eval(c_string_to_object("(initialize-runtime-globals)"));
}

void free_math(){
    cl_shutdown();
}

}
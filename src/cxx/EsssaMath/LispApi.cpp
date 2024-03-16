#include <cctype>
#include <codecvt>
#include <cstddef>
#include <iostream>
#include <locale>
#include <memory>
#include <sstream>
#include <stdexcept>
#include <stdio.h>
#include <ecl/ecl.h>
#include <stdlib.h>
#include <string.h>
#include <string>
#include "LispApi.hpp"

std::string to_lower(std::string const& _str){
    std::string _result;
    for(auto& c : _str){
        _result += std::tolower(c);
    }

    return _result;
}

extern "C"{
    void init_lib_MAXIMA(cl_object);
} 

namespace Essa::Math {

std::shared_ptr<LispObject> LispObject::Parse(std::istream& _ss){
    std::deque<Token> _tokens;
    char c;
    std::string _res;
    while(!_ss.eof()){
        _ss.read(&c, 1);

        if(!_res.empty() && (std::isspace(c) || c == '(' || c == ')')){
            _tokens.push_back(Token{._type = Token::Type::STRING, ._str = _res});
            _res = "";
        }

        if(c == '('){
            _tokens.push_back(Token{._type = Token::Type::LEFT, ._str = "("});
        }else if(c == ')'){
            _tokens.push_back(Token{._type = Token::Type::RIGHT, ._str = ")"});
        }else if(!std::isspace(c)){
            _res += c;
        }
    }

    bool _isalnum = true;

    for(const auto& _s : _res){
        _isalnum &= std::isalnum(_s) || (_s == '%') || (_s == '$') || (_s == '.');
    }

    if(_isalnum){
        _tokens.push_back(Token{._type = Token::Type::STRING, ._str = _res});
    }

    if(_tokens.front()._type == Token::Type::LEFT){
        return std::make_shared<LispList>(_tokens);
    }else{
        return std::make_shared<LispValue>(_tokens);
    }
}

LispList::LispList(std::deque<Token>& _tokens) : LispObject(_tokens){
    _tokens.pop_front();
    _tokens.pop_front();

    _name += _tokens.front()._str;
    _tokens.pop_front();
    _tokens.pop_front();

    while(_tokens.front()._type != Token::Type::RIGHT){
        if(_tokens.front()._type == Token::Type::LEFT){
            _objectVec.push_back(std::make_shared<LispList>(_tokens));
        }else{
            _objectVec.push_back(std::make_shared<LispValue>(_tokens));
        }
    }

    _tokens.pop_front();
}

std::string LispList::ToString() const{
    std::string _op;
    bool _braces = false;
    bool _initial = false;

    if(_name == "MPLUS"){
        _op = "+";
        _braces = true;
        _initial = false;
    }else if(_name == "MMINUS"){
        _op = "-";
        _braces = true;
        _initial = true;
    }else if(_name == "MTIMES"){
        _op = "*";
        _braces = true;
        _initial = false;
    }else if(_name == "MQUOTIENT" || _name == "RAT"){
        _op = "/";
        _braces = true;
        _initial = false;
    }else if(_name == "MEXPT"){
        _op = "^";
        _braces = false;
        _initial = false;
    }else if(_name == "MLESSP"){
        _op = "<";
        _braces = false;
        _initial = false;
    }else if(_name == "MLEQP"){
        _op = "<=";
        _braces = false;
        _initial = false;
    }else if(_name == "MEQUAL"){
        _op = "=";
        _braces = false;
        _initial = false;
    }else if(_name == "MGEQP"){
        _op = ">=";
        _braces = false;
        _initial = false;
    }else if(_name == "MGREATERP"){
        _op = ">";
        _braces = false;
        _initial = false;
    }else if(_name.front() == '%'){
        std::string _result = to_lower(_name.substr(1)) + "(";

        for(size_t i = 0; i < _objectVec.size(); i++){
            if(i != 0){
                _result += ",";
            }

            _result += _objectVec[i]->ToString();
        }

        _result += ")";
        return _result;
    }else{
        return "";
    }
    std::string _result;

    if(_braces) _result += "(";

    for(size_t i = 0; i < _objectVec.size(); i++){
        if(i == 0 && _initial || i != 0){
            _result += _op;
        }

        _result += _objectVec[i]->ToString();
    }

    if(_braces) _result += ")";

    return _result;
}

LispValue::LispValue(std::deque<Token>& _tokens) : LispObject(_tokens){
    _value = to_lower(_tokens.front()._str);
    if(_value.front() == '$'){
        _value = _value.substr(1);
    }
    _tokens.pop_front();
}

std::string LispValue::ToString() const{
    return _value;
}

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

        std::stringstream ss;
        ss << _res;
        auto _obj = LispObject::Parse(ss);
        return _obj->ToString();
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
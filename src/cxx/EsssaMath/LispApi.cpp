#include <codecvt>
#include <iostream>
#include <locale>
#include <memory>
#include <stdio.h>
#include <ecl/ecl.h>
#include <stdlib.h>
#include <string.h>
#include <string>
#include <sstream>

#include "Expression.hpp"

std::string to_lower(std::string const& _str){
    std::string _result;
    for(auto& c : _str){
        _result += std::tolower(c);
    }

    return _result;
}

std::string get_type(std::istream& _ss){
    char c;
    while(!_ss.eof()){
        _ss.read(&c, 1);
        if(c != ' ' && c != ')'){
            break;
        }
    }

    std::string result;
    if(c == '('){
        while(!_ss.eof()){
            _ss.read(&c, 1);

            if(c == ')'){
                result += c;
                break;
            }else{
                result += c;
            }
        }
    }else{
        result += c;
        while(!_ss.eof()){
            _ss.read(&c, 1);

            if(c == ' ' || c == ')'){
                break;
            }else{
                result += c;
            }
        }
    }

    return result;
}

extern "C"{
    void init_lib_MAXIMA(cl_object);
} 

namespace Essa::Math {

void init_math(int argc, char **argv){
    cl_boot(argc, argv);
    ecl_init_module(NULL, init_lib_MAXIMA);
}

void free_math(){
    cl_shutdown();
}

class LispExpression : virtual public Expression{
public:
    static std::shared_ptr<Expression> ParseLispObject(std::string ss);
    static std::shared_ptr<Expression> ParseLispObject(std::istream& _ss);
    virtual void ParseLispObject(std::string const& _typeStr, std::istream& _ss) = 0;
};

class LispBinary : public Binary, public LispExpression{
public:
    void ParseLispObject(std::string const& _typeStr, std::istream& _ss) override;
};

class LispUnary : public Unary, public LispExpression{
public:
    void ParseLispObject(std::string const& _typeStr, std::istream& _ss) override;
};

class LispValue : public Value, public LispExpression{
public:
    void ParseLispObject(std::string const& _typeStr, std::istream& _ss) override;
};

std::shared_ptr<Expression> LispExpression::ParseLispObject(std::string _str){
    std::stringstream ss;
    ss.write(_str.c_str(), _str.size());

    return LispExpression::ParseLispObject(ss);
}

std::shared_ptr<Expression> LispExpression::ParseLispObject(std::istream& _ss){
    std::string _type = get_type(_ss);
    std::shared_ptr<LispExpression> _expr;

    if(_type.find("(%") != std::string::npos){
        _expr = std::make_shared<LispUnary>();
    }else if(_type.find("(") != std::string::npos){
        _expr = std::make_shared<LispBinary>();
    }else{
        _expr = std::make_shared<LispValue>();
    }

    _expr->ParseLispObject(_type, _ss);
    return _expr;
}

void LispUnary::ParseLispObject(std::string const& _typeStr, std::istream& _ss){
    _type = _typeStr.substr(2);
    _type = to_lower(_type.substr(0, _type.find(" SIMP)")));
    _expr = LispExpression::ParseLispObject(_ss);
}

void LispBinary::ParseLispObject(std::string const& _typeStr, std::istream& _ss){
    std::string type = _typeStr.substr(1);
    type = type.substr(0, type.find(" SIMP)"));
    if(type == "MPLUS"){
        _type = Type::ADD;
    }else if(type == "MTIMES"){
        _type = Type::MUL;
    }else if(type == "RAT"){
        _type = Type::DIV;
    }else if(type == "MEXPT"){
        _type = Type::POW;
    }else{
        _type = Type::UNDEFINED;
    }
    _expr1 = LispExpression::ParseLispObject(_ss);
    _expr2 = LispExpression::ParseLispObject(_ss);
}

void LispValue::ParseLispObject(std::string const& _typeStr, std::istream& _ss){
    if(_typeStr.front() == '%'){
        _type = Type::CONSTANT;
        _val = to_lower(_typeStr.substr(1));
    }else if(_typeStr.front() == '$'){
        _type = Type::VARIABLE;
        _val = to_lower(_typeStr.substr(1));
    }else{
        _type = Type::VALUE;
        _val = to_lower(_typeStr);
    }
}

std::shared_ptr<Expression> evaluate(std::string _exp) {
    _exp = "\"" + _exp + "\"";
    cl_object arg1 = c_string_to_object(_exp.c_str());
    cl_object name = ecl_make_symbol("api-eval", "MAXIMA");
    cl_object output = cl_funcall(2, name, arg1);

    static_assert(sizeof(ecl_character)==sizeof(wchar_t),"sizes must be the same");
    
    std::wstring _str = reinterpret_cast<wchar_t*>(output->string.self);
    using convert_typeX = std::codecvt_utf8<wchar_t>;
    std::wstring_convert<convert_typeX, wchar_t> converterX;

    _str = _str.substr(0, _str.find_last_of(L")") + 1);
    std::string _res = converterX.to_bytes(_str);
    std::string::size_type _pos = _res.find("\n");
    while(_pos != std::string::npos){
        _res = _res.substr(0, _pos) + _res.substr(_pos + 1);
        _pos = _res.find("\n");
    }

    return LispExpression::ParseLispObject(_res);
}

std::shared_ptr<Expression> Expression::Parse(std::string _str){
    return evaluate(_str + ";");
}

std::shared_ptr<Expression> Expression::IndefIntegral(std::string _var){
    std::stringstream ss;
    WriteExpr(ss);

    return evaluate("integrate(" + ss.str() + "," + _var + ");");
}

std::shared_ptr<Expression> Expression::Derivative(std::string _var){
    std::stringstream ss;
    WriteExpr(ss);

    return evaluate("derivative(" + ss.str() + "," + _var + ");");
}

}
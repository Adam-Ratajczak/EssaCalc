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

void init_math(int argc, char **argv){
    cl_boot(argc, argv);
    ecl_init_module(NULL, init_lib_MAXIMA);

    cl_eval(c_string_to_object("(initialize-runtime-globals)"));
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
    char c;
    std::string _type = get_type(_ss);
    std::shared_ptr<LispExpression> _expr;

    if(_type.empty()) return std::make_shared<LispValue>();

    if(_type.find("MMINUS") != std::string::npos){
        _ss.read(&c, 1);
        auto _object =  LispExpression::ParseLispObject(_ss);
        _object->_negative = true;

        return _object;
    }

    if(_type.find("(%") != std::string::npos){
        _expr = std::make_shared<LispUnary>();
    }else if(_type.find("(") != std::string::npos){
        _expr = std::make_shared<LispBinary>();
    }else{
        _expr = std::make_shared<LispValue>();
        _type = _type;
    }

    _expr->ParseLispObject(_type, _ss);
    return _expr;
}

void LispUnary::ParseLispObject(std::string const& _typeStr, std::istream& _ss){
    char c;
    _ss.read(&c, 1);
    _type = _typeStr.substr(3);
    _type = to_lower(_type);
    _expr = LispExpression::ParseLispObject(_ss);
    _ss.read(&c, 1);
}

void LispBinary::ParseLispObject(std::string const& _typeStr, std::istream& _ss){
    std::string type = _typeStr.substr(1);
    if(type.find("MPLUS") != std::string::npos){
        _type = Type::ADD;
    }else if(type.find("MMINUS") != std::string::npos){
        _type = Type::SUB;
    }else if(type.find("MTIMES") != std::string::npos){
        _type = Type::MUL;
    }else if(type.find("MQUOTIENT") != std::string::npos){
        _type = Type::DIV;
    }else if(type.find("MEXPT") != std::string::npos){
        _type = Type::POW;
    }else{
        _type = Type::UNDEFINED;
    }
    char c;
    _ss.read(&c, 1);
    _expr1 = LispExpression::ParseLispObject(_ss);
    _expr2 = LispExpression::ParseLispObject(_ss);
    _ss.read(&c, 1);
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

    _pos = _res.find(" SIMP");
    while(_pos != std::string::npos){
        _res = _res.substr(0, _pos) + _res.substr(_pos + 5);
        _pos = _res.find(" SIMP");
    }

    auto _expr =  LispExpression::ParseLispObject(_res);
    _expr->Simplify();
    return _expr;
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
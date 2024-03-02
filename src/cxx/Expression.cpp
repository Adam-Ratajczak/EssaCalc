#include "Expression.hpp"
#include <memory>
#include <sstream>
#include <string>

std::string get_type(std::istream& _ss){
    char c;
    while(!_ss.eof()){
        _ss.read(&c, 1);
        if(c != ' '){
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

std::shared_ptr<Expression> Expression::Parse(std::string _str){
    std::stringstream ss;
    ss.write(_str.c_str(), _str.size());

    return Parse(ss);
}

std::shared_ptr<Expression> Expression::Parse(std::istream& _ss){
    std::string _type = get_type(_ss);

    if(_type.find("(%") != std::string::npos){
        return std::make_shared<Unary>(_type, _ss);
    }else if(_type.find("(") != std::string::npos){
        return std::make_shared<Binary>(_type, _ss);
    }else{
        return std::make_shared<Value>(_type);
    }
}

Unary::Unary(std::string const& _typeStr, std::istream& _ss){
    _type = _typeStr.substr(2);
    _type = _type.substr(0, _type.find(" SIMP)"));
    _expr = Expression::Parse(_ss);
}

void Unary::WriteJSON(std::ostream& _out){
    _out << "{\"func\":\"" << _type << "\",\"arg\":";
    _expr->WriteJSON(_out);
    _out << "}";
}

void Unary::WriteExpr(std::ostream& _out){

}

void Unary::WriteLatEx(std::ostream& _out){

}

Binary::Binary(std::string const& _typeStr, std::istream& _ss){
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
    _expr1 = Expression::Parse(_ss);
    _expr2 = Expression::Parse(_ss);
}

void Binary::WriteJSON(std::ostream& _out){
    std::string type;
    switch (_type) {
    case Type::ADD:
        type = "ADD";
      break;
    case Type::SUB:
        type = "SUB";
      break;
    case Type::MUL:
        type = "MUL";
      break;
    case Type::DIV:
        type = "DIV";
      break;
    case Type::POW:
        type = "POW";
      break;
    case Type::UNDEFINED:
        type = "NUL";
      break;
    }
    _out << "{\"op\":\"" << type << "\",\"arg1\":";
    _expr1->WriteJSON(_out);
    _out << ",\"arg2\":";
    _expr2->WriteJSON(_out);
    _out << "}";
}

void Binary::WriteExpr(std::ostream& _out){

}

void Binary::WriteLatEx(std::ostream& _out){

}

Value::Value(std::string const& _typeStr){
    if(_typeStr.front() == '%'){
        _type = Type::CONSTANT;
        _val = _typeStr.substr(1);
    }else if(_typeStr.front() == '$'){
        _type = Type::VARIABLE;
        _val = _typeStr.substr(1);
    }else{
        _type = Type::VALUE;
        _val = _typeStr;
    }
}

void Value::WriteJSON(std::ostream& _out){
    std::string type;
    switch (_type) {
    case Type::VALUE:
        type = "VAL";
      break;
    case Type::VARIABLE:
        type = "VAR";
      break;
    case Type::CONSTANT:
        type = "CON";
      break;
    }
    _out << "{\"type\":\"" << type << "\",\"value\":\"" << _val << "\"}";
}

void Value::WriteExpr(std::ostream& _out){

}

void Value::WriteLatEx(std::ostream& _out){

}

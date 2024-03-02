#include "Expression.hpp"
#include <cctype>
#include <memory>
#include <sstream>
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
    _type = to_lower(_type.substr(0, _type.find(" SIMP)")));
    _expr = Expression::Parse(_ss);
}

void Unary::WriteJSON(std::ostream& _out) const{
    _out << "{\"func\":\"" << _type << "\",\"arg\":";
    _expr->WriteJSON(_out);
    _out << "}";
}

void Unary::WriteExpr(std::ostream& _out) const{
    _out << _type << "(";
    _expr->WriteExpr(_out);
    _out << ")";
}

void Unary::WriteLatEx(std::ostream& _out) const{
    _out << "\\" << _type << "(";
    _expr->WriteLatEx(_out);
    _out << ")";
}

void Unary::Simplify(){
    _expr->Simplify();
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

void Binary::WriteJSON(std::ostream& _out) const{
    std::string type;
    switch (_type) {
    case Type::ADD:
        type = "add";
      break;
    case Type::SUB:
        type = "sub";
      break;
    case Type::MUL:
        type = "mul";
      break;
    case Type::DIV:
        type = "div";
      break;
    case Type::POW:
        type = "pow";
      break;
    case Type::UNDEFINED:
        type = "nil";
      break;
    }
    _out << "{\"op\":\"" << type << "\",\"arg1\":";
    _expr1->WriteJSON(_out);
    _out << ",\"arg2\":";
    _expr2->WriteJSON(_out);
    _out << "}";
}

void Binary::WriteExpr(std::ostream& _out) const{
    std::string op;
    switch (_type) {
    case Type::ADD:
        op = "+";
      break;
    case Type::SUB:
        op = "-";
      break;
    case Type::MUL:
        op = "*";
      break;
    case Type::DIV:
        op = "/";
      break;
    case Type::POW:
        op = "^";
      break;
    case Type::UNDEFINED:
        op = " ";
      break;
    }
    _out << "(";
    _expr1->WriteExpr(_out);
    _out << op;
    _expr2->WriteExpr(_out);
    _out << ")";
}

void Binary::WriteLatEx(std::ostream& _out) const{
    _out << "{(";
    switch (_type) {
    case Type::ADD:
        _expr1->WriteLatEx(_out);
        _out << "+";
        _expr2->WriteLatEx(_out);
      break;
    case Type::SUB:
        _expr1->WriteLatEx(_out);
        _out << "-";
        _expr2->WriteLatEx(_out);
      break;
    case Type::MUL:
        _expr1->WriteLatEx(_out);
        _out << "\\cdot";
        _expr2->WriteLatEx(_out);
      break;
    case Type::DIV:
        _out << "\\frac{";
        _expr1->WriteLatEx(_out);
        _out << "}{";
        _expr2->WriteLatEx(_out);
        _out << "}";
      break;
    case Type::POW:
        _expr1->WriteLatEx(_out);
        _out << "^";
        _expr2->WriteLatEx(_out);
      break;
    case Type::UNDEFINED:
        _expr1->WriteLatEx(_out);
        _out << " ";
        _expr2->WriteLatEx(_out);
      break;
    }
    _out << ")}";
}

void Binary::Simplify(){
    
}

Value::Value(std::string const& _typeStr){
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

void Value::WriteJSON(std::ostream& _out) const{
    std::string type;
    switch (_type) {
    case Type::VALUE:
        type = "val";
      break;
    case Type::VARIABLE:
        type = "var";
      break;
    case Type::CONSTANT:
        type = "const";
      break;
    }
    _out << "{\"type\":\"" << type << "\",\"value\":\"" << _val << "\"}";
}

void Value::WriteExpr(std::ostream& _out) const{
    if(_type == Type::CONSTANT){
        _out << "%" << _val;
    }else{
        _out << _val;
    }
}

void Value::WriteLatEx(std::ostream& _out) const{
    if(_type == Type::CONSTANT){
        _out << "\\" << _val;
    }else{
        _out << _val;
    }
}

void Value::Simplify(){
    
}

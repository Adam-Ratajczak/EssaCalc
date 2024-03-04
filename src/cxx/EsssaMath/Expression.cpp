#include "Expression.hpp"
#include <sstream>
#include <string>

namespace Essa::Math{
    std::string Expression::ToString() const{
        std::stringstream ss;
        WriteExpr(ss);

        return ss.str();
    }

    void Unary::WriteJSON(std::ostream& _out) const{
        _out << "{\"func\":\"" << _type << "\",\"arg\":";
        _expr->WriteJSON(_out);
        _out << "}";
    }

    void Unary::WriteExpr(std::ostream& _out) const{
        if(_negative)
            _out << "-";
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

    bool Binary::CheckSignificance(Type _op1, Type _op2){
        switch (_op1) {
        case Type::UNDEFINED:
            return true;
        case Type::POW:
            return _op2 == Type::ADD || _op2 == Type::SUB || _op2 == Type::MUL || _op2 == Type::DIV; 
        case Type::MUL:
        case Type::DIV:
            return _op2 == Type::ADD || _op2 == Type::SUB;
        case Type::ADD:
        case Type::SUB:
            return false;
          break;
        }

        return false;
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

        if(_negative){
            _out << "-";
            if(_type == Type::ADD || _type == Type::ADD){
                _out << "(";
            }
        }

        bool _needBraces = false;
        if(Binary* e = dynamic_cast<Binary*>(_expr1.get())){
            _needBraces = CheckSignificance(_type, e->_type);
        }
        _needBraces |= _expr1->_negative;
        
        if(_needBraces)
            _out << "(";
        _expr1->WriteExpr(_out);
        if(_needBraces)
            _out << ")";
        _out << op;
        _needBraces = false;
        if(Binary* e = dynamic_cast<Binary*>(_expr2.get())){
            _needBraces = CheckSignificance(_type, e->_type);
        }

        _needBraces |= _expr2->_negative;
        if(_needBraces)
            _out << "(";
        _expr2->WriteExpr(_out);
        if(_needBraces)
            _out << ")";


        if(_negative && (_type == Type::ADD || _type == Type::ADD)){
            _out << ")";
        }
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
        if(_type == Type::ADD && _expr2->_negative){
            _type = Type::SUB;
        }else if(_type == Type::SUB && !_expr2->_negative){
            _type = Type::ADD;
        }
        _expr2->_negative = false;

        _expr1->Simplify();
        _expr2->Simplify();
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
        if(_negative)
            _out << "-";
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
}

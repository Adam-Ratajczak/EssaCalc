#pragma once

#include <istream>
#include <memory>
#include <ostream>
#include <string>

class Expression{
public:
    static std::shared_ptr<Expression> Parse(std::string ss);
    static std::shared_ptr<Expression> Parse(std::istream& ss);

    virtual void WriteJSON(std::ostream& _out) {}
    virtual void WriteExpr(std::ostream& _out) {}
    virtual void WriteLatEx(std::ostream& _out) {}
};

class Binary : public Expression{
public:
    Binary(std::string const& _typeStr, std::istream& _ss);

    void WriteJSON(std::ostream& _out) override;
    void WriteExpr(std::ostream& _out) override;
    void WriteLatEx(std::ostream& _out) override;

    enum class Type{
        ADD,
        SUB,
        MUL,
        DIV,
        POW,
        UNDEFINED
    };
protected:
    Type _type;
    std::shared_ptr<Expression> _expr1;
    std::shared_ptr<Expression> _expr2;
};

class Unary : public Expression{
public:
    Unary(std::string const& _typeStr, std::istream& _ss);
    
    void WriteJSON(std::ostream& _out) override;
    void WriteExpr(std::ostream& _out) override;
    void WriteLatEx(std::ostream& _out) override;
protected:
    std::string _type;
    std::shared_ptr<Expression> _expr;
};

class Value : public Expression{
public:
    Value(std::string const& _typeStr);

    void WriteJSON(std::ostream& _out) override;
    void WriteExpr(std::ostream& _out) override;
    void WriteLatEx(std::ostream& _out) override;

    enum class Type{
        VALUE,
        VARIABLE,
        CONSTANT
    };
protected:
    Type _type;
    std::string _val;
};

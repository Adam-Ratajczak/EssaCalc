#pragma once

#include <memory>
#include <ostream>
#include <string>

namespace Essa::Math {

class Expression{
public:
    Expression() = default;
    static std::shared_ptr<Expression> Parse(std::string ss);

    virtual void WriteJSON(std::ostream& _out) const = 0;
    virtual void WriteExpr(std::ostream& _out) const = 0;
    virtual void WriteLatEx(std::ostream& _out) const = 0;
    virtual void Simplify() = 0;

    std::shared_ptr<Expression> IndefIntegral(std::string _var);
    std::shared_ptr<Expression> Derivative(std::string _var);
};

class Binary : virtual public Expression{
public:
    Binary() = default;

    void WriteJSON(std::ostream& _out) const override;
    void WriteExpr(std::ostream& _out) const override;
    void WriteLatEx(std::ostream& _out) const override;
    void Simplify() override;

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

class Unary : virtual public Expression{
public:
    Unary() = default;
    
    void WriteJSON(std::ostream& _out) const override;
    void WriteExpr(std::ostream& _out) const override;
    void WriteLatEx(std::ostream& _out) const override;
    void Simplify() override;

    enum class Type{
        SIN,
        COS,
        TAN,
        COT,
        SEC,
        CSC,
        ASIN,
        ACOS,
        ATAN,
        ACOT,
        ASEC,
        ACSC,

        LOG2,
        LOG10,
        LN,

        SQRT,
        CBRT,

        EXP,

        ERF
    };
protected:
    std::string _type;
    // Type _type;
    std::shared_ptr<Expression> _expr;
};

class Value : virtual public Expression{
public:
    Value() = default;

    void WriteJSON(std::ostream& _out) const override;
    void WriteExpr(std::ostream& _out) const override;
    void WriteLatEx(std::ostream& _out) const override;
    void Simplify() override;

    enum class Type{
        VALUE,
        VARIABLE,
        CONSTANT
    };
protected:
    Type _type;
    std::string _val;
};

}

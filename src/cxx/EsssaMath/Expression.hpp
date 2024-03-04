#pragma once

#include <memory>
#include <ostream>
#include <string>

namespace Essa::Math {

class Expression{
    friend class Binary;
    friend class Unary;
    friend class Value;

    friend class LispExpression;
public:
    Expression() = default;
    static std::shared_ptr<Expression> Parse(std::string ss);

    std::shared_ptr<Expression> IndefIntegral(std::string _var);
    std::shared_ptr<Expression> Derivative(std::string _var);

    friend std::ostream& operator<< (std::ostream& stream, const Expression& _expr){
        _expr.WriteExpr(stream);

        return stream;
    }

protected:
    virtual void WriteJSON(std::ostream& _out) const = 0;
    virtual void WriteExpr(std::ostream& _out) const = 0;
    virtual void WriteLatEx(std::ostream& _out) const = 0;
    virtual void Simplify() = 0;
    bool _negative = false;
};

class Binary : virtual public Expression{
public:
    Binary() = default;

    enum class Type{
        ADD = 0,
        SUB = 1,
        MUL = 2,
        DIV = 3,
        POW = 4,
        UNDEFINED = 5
    };

    static bool CheckSignificance(Type _op1, Type _op2);
protected:
    Type _type;
    std::shared_ptr<Expression> _expr1;
    std::shared_ptr<Expression> _expr2;

    void WriteJSON(std::ostream& _out) const override;
    void WriteExpr(std::ostream& _out) const override;
    void WriteLatEx(std::ostream& _out) const override;
    void Simplify() override;
};

class Unary : virtual public Expression{
public:
    Unary() = default;
    
protected:
    std::string _type;
    // Type _type;
    std::shared_ptr<Expression> _expr;

    void WriteJSON(std::ostream& _out) const override;
    void WriteExpr(std::ostream& _out) const override;
    void WriteLatEx(std::ostream& _out) const override;
    void Simplify() override;
};

class Value : virtual public Expression{
public:
    Value() = default;


    enum class Type{
        VALUE,
        VARIABLE,
        CONSTANT
    };
protected:
    Type _type;
    std::string _val;

    void WriteJSON(std::ostream& _out) const override;
    void WriteExpr(std::ostream& _out) const override;
    void WriteLatEx(std::ostream& _out) const override;
    void Simplify() override;
};

}

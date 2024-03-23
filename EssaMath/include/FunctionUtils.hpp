#pragma once
#include "include/SymbolTable.hpp"
#include "include/Parser.hpp"
#include "include/Expression.hpp"

namespace Essa::Math{

template<typename T>
expression<T> integrate(symbol_table<T>& _table, parser<T>& _parser, expression<T>& _expr, std::string const& _var){
    extern std::string evaluate(const std::string& _exp);
    std::string expression_string;

    if(!_table.is_variable(_var))
        expression_string = _var;
    else
        expression_string = evaluate("integrate(" + _expr.to_string() + "," + _var + ")");

    expression<T> expression;
    expression.register_symbol_table(_table);
    _parser.compile(expression_string, expression);
    return expression;
}

template<typename T>
expression<T> differentiate(symbol_table<T>& _table, parser<T>& _parser, expression<T>& _expr, std::string const& _var){
    extern std::string evaluate(const std::string& _exp);
    std::string expression_string;

    if(!_table.is_variable(_var))
        expression_string = _var;
    else
        expression_string = evaluate("diff(" + _expr.to_string() + "," + _var + ")");

    expression<T> expression;
    expression.register_symbol_table(_table);
    _parser.compile(expression_string, expression);
    return expression;
}

}

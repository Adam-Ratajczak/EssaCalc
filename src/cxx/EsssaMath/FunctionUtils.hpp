#pragma once
#include "SymbolTable.hpp"
#include "Parser.hpp"
#include "Expression.hpp"
#include "LispApi.hpp"

namespace Essa::Math{

template<typename T>
expression<T> integrate(symbol_table<T>& _table, parser<T>& _parser, expression<T>& _expr, std::string const& _var){
    std::string expression_string;

    if(!_table.is_variable(_var))
        expression_string = _var;
    else
        expression_string = evaluate("integrate(" + _expr.ToString() + "," + _var + ")");

    expression<T> expression;
    expression.register_symbol_table(_table);
    _parser.compile(expression_string, expression);
    return expression;
}

}

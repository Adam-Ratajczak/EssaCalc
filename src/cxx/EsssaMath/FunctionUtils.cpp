#include "FunctionUtils.hpp"

namespace Essa::Math{

extern std::string evaluate(const std::string& _exp);

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

template<typename T>
expression<T> differentiate(symbol_table<T>& _table, parser<T>& _parser, expression<T>& _expr, std::string const& _var){
    std::string expression_string;

    if(!_table.is_variable(_var))
        expression_string = _var;
    else
        expression_string = evaluate("diff(" + _expr.ToString() + "," + _var + ")");

    expression<T> expression;
    expression.register_symbol_table(_table);
    _parser.compile(expression_string, expression);
    return expression;
}

template expression<float> integrate(symbol_table<float>& _table, parser<float>& _parser, expression<float>& _expr, std::string const& _var);
template expression<double> integrate(symbol_table<double>& _table, parser<double>& _parser, expression<double>& _expr, std::string const& _var);
template expression<long double> integrate(symbol_table<long double>& _table, parser<long double>& _parser, expression<long double>& _expr, std::string const& _var);

template expression<float> differentiate(symbol_table<float>& _table, parser<float>& _parser, expression<float>& _expr, std::string const& _var);
template expression<double> differentiate(symbol_table<double>& _table, parser<double>& _parser, expression<double>& _expr, std::string const& _var);
template expression<long double> differentiate(symbol_table<long double>& _table, parser<long double>& _parser, expression<long double>& _expr, std::string const& _var);

}

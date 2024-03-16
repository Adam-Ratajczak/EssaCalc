#pragma once
#include "SymbolTable.hpp"
#include "Parser.hpp"
#include "Expression.hpp"

namespace Essa::Math{

template<typename T>
expression<T> integrate(symbol_table<T>& _table, parser<T>& _parser, expression<T>& _expr, std::string const& _var);

template<typename T>
expression<T> differentiate(symbol_table<T>& _table, parser<T>& _parser, expression<T>& _expr, std::string const& _var);

}

#include <cstdio>
#include <string>
#include <iostream>

#include "exprtk.hpp"

template <typename T>
void trig_function()
{
   typedef Essa::Math::symbol_table<T> symbol_table_t;
   typedef Essa::Math::expression<T>   expression_t;
   typedef Essa::Math::parser<T>       parser_t;

   const std::string expression_string =
                     "clamp(-1.0,sin(2 * pi * x) + cos(x / 2 * pi),+1.0)";

   T x;

   symbol_table_t symbol_table;
   symbol_table.add_variable("x",x);
   symbol_table.add_constants();

   expression_t expression;
   expression.register_symbol_table(symbol_table);

   parser_t parser;
   parser.compile(expression_string,expression);
   std::cout << parser.error() << "\n";
}

int main()
{
   trig_function<double>();

    return 0;
}

#include <Essa/Math/SymbolTable.hpp>
#include <iostream>
#include <Essa/Math/EssaMath.hpp>
#include <string>

template <typename T>
void trig_function()
{
   typedef Essa::Math::symbol_table<T> symbol_table_t;
   typedef Essa::Math::expression<T>   expression_t;
   typedef Essa::Math::parser<T>       parser_t;

   const std::string expression_string = "sin((2 + %pi) * x) - cos(x / 2 ^ (%e+1))";

   T x;

   symbol_table_t symbol_table;
   symbol_table.add_variable("x",x);
   symbol_table.add_constants();

   expression_t expression;
   expression.register_symbol_table(symbol_table);

   parser_t parser;
   parser.compile(expression_string, expression);

   std::cout << parser.error() << "\n";
   std::cout << expression.to_string() << "\n";

   auto integrated = Essa::Math::integrate(symbol_table, parser, expression, "x");
   std::cout << parser.error() << "\n";
   std::cout << integrated.to_string() << "\n";

   auto diff = Essa::Math::differentiate(symbol_table, parser, expression, "x");
   std::cout << parser.error() << "\n";
   std::cout << diff.to_string() << "\n";
}

int main(int argc, char **argv)
{
   Essa::Math::init_math(argc, argv);

   trig_function<double>();

   Essa::Math::free_math();

    return 0;
}
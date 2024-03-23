#include <Essa/Math/SymbolTable.hpp>
#include <complex>
#include <iostream>
#include <Essa/Math/EssaMath.hpp>
#include <string>

void trig_function_double()
{
   typedef Essa::Math::symbol_table<double> symbol_table_t;
   typedef Essa::Math::expression<double>   expression_t;
   typedef Essa::Math::parser<double>       parser_t;

   const std::string expression_string = "sin((2 + %pi) * x) - cos(x / 2 ^ (%e+1))";

   double x;

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

   for(x = 2.0; x <= 4.0; x += 0.1){
      std::cout << expression.value() << "\t\t" << integrated.value() << "\t\t" << diff.value() << "\n";
   }
}
void trig_function_complex()
{
   typedef Essa::Math::symbol_table<std::complex<double>> symbol_table_t;
   typedef Essa::Math::expression<std::complex<double>>   expression_t;
   typedef Essa::Math::parser<std::complex<double>>       parser_t;

   const std::string expression_string = "sin(x + (2 + %pi) * x * %i) - cos(x / 2 ^ (%e+1))";

   std::complex<double> x;

   symbol_table_t symbol_table;
   symbol_table.add_variable("x",x);
   symbol_table.add_constants();

   expression_t expression;
   expression.register_symbol_table(symbol_table);

   parser_t parser;
   parser.compile(expression_string, expression);

   std::cout << parser.error() << "\n";
   std::cout << expression.to_string() << "\n";

   // auto integrated = Essa::Math::integrate(symbol_table, parser, expression, "x");
   // std::cout << parser.error() << "\n";
   // std::cout << integrated.to_string() << "\n";

   // auto diff = Essa::Math::differentiate(symbol_table, parser, expression, "x");
   // std::cout << parser.error() << "\n";
   // std::cout << diff.to_string() << "\n";

   for(x = 2.0; x.real() <= 4.0; x += 0.1){
      std::cout << expression.value() << "\n";
   }
}

int main(int argc, char **argv)
{
   Essa::Math::init_math(argc, argv);

   trig_function_double();
   trig_function_complex();

   Essa::Math::free_math();

    return 0;
}
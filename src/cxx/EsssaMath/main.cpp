#include <string>
#include <iostream>

#include "EssaMath.hpp"

// template <typename T>
// void trig_function()
// {
//    typedef Essa::Math::symbol_table<T> symbol_table_t;
//    typedef Essa::Math::expression<T>   expression_t;
//    typedef Essa::Math::parser<T>       parser_t;

//    const std::string expression_string = "sin(2 * pi * x) + cos(x / 2 * pi)";

//    T x;

//    symbol_table_t symbol_table;
//    symbol_table.add_variable("x",x);
//    symbol_table.add_constants();

//    expression_t expression;
//    expression.register_symbol_table(symbol_table);

//    parser_t parser;
//    parser.compile(expression_string, expression);

//    for(x = 0.0; x <= 2.0; x += 0.1){
//       std::cout << expression.value() << "\n";
//    }
// }

int main(int argc, char **argv)
{
   Essa::Math::init_math(argc, argv);

   Essa::Math::load("/home/manjaro/Desktop/Projekty/EssaCalc/share/solve_rat_ineq/solve_rat_ineq.mac");

   std::cout << Essa::Math::evaluate("x + 2*x - y / x, simp;") << "\n";
   std::cout << Essa::Math::evaluate("solve(x^2 - 4 = 0);") << "\n";
   std::cout << Essa::Math::evaluate("solve_rat_ineq(x^2 - 4 <= 0);") << "\n";
   
   // trig_function<double>();

   Essa::Math::free_math();

    return 0;
}

#include <iostream>
#include <string>

#include "Expression.hpp"
#include "EssaMath.hpp"

using namespace Essa::Math;

int main (int argc, char **argv)
{
  init_math(argc, argv);

  auto expr1 = Expression::Parse("x/(x+1)");
  std::cout << "Function: " << *expr1 << "\n";
  auto expr1_der = expr1->Derivative("x");
  std::cout << "Derivative: " << *expr1_der << "\n";
  auto expr1_int = expr1->IndefIntegral("x");
  std::cout << "Integrate: " << *expr1_int << "\n";

  auto expr2 = Expression::Parse("1/(1+x^2)");
  std::cout << "Function: " << *expr2 << "\n";
  auto expr2_der = expr2->Derivative("x");
  std::cout << "Derivative: " << *expr2_der << "\n";
  auto expr2_int = expr2->IndefIntegral("x");
  std::cout << "Integrate: " << *expr2_int << "\n";

  auto expr3 = Expression::Parse("x/(1+x^2)");
  std::cout << "Function: " << *expr3 << "\n";
  auto expr3_der = expr3->Derivative("x");
  std::cout << "Derivative: " << *expr3_der << "\n";
  auto expr3_int = expr3->IndefIntegral("x");
  std::cout << "Integrate: " << *expr3_int << "\n";

  free_math();
  return 0;
}

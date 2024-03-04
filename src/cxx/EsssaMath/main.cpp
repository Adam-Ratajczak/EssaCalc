#include <iostream>
#include <string>

#include "Expression.hpp"
#include "EssaMath.hpp"

using namespace Essa::Math;

int main (int argc, char **argv)
{
  init_math(argc, argv);

  auto expr1 = Expression::Parse("x/(x+1)");
  std::cout << "Function: ";
  expr1->WriteExpr(std::cout);
  std::cout << "\n";
  auto expr1_der = expr1->Derivative("x");
  std::cout << "Derivative: ";
  expr1_der->WriteExpr(std::cout);
  std::cout << "\n";
  std::cout << "Integrate: ";
  auto expr1_int = expr1->IndefIntegral("x");
  expr1_int->WriteExpr(std::cout);
  std::cout << "\n";

  auto expr2 = Expression::Parse("1/(1+x^2)");
  std::cout << "Function: ";
  expr2->WriteExpr(std::cout);
  std::cout << "\n";
  auto expr2_der = expr2->Derivative("x");
  std::cout << "Derivative: ";
  expr2_der->WriteExpr(std::cout);
  std::cout << "\n";
  std::cout << "Integrate: ";
  auto expr2_int = expr2->IndefIntegral("x");
  expr2_int->WriteExpr(std::cout);
  std::cout << "\n";

  auto expr3 = Expression::Parse("x/(1+x^2)");
  std::cout << "Function: ";
  expr3->WriteExpr(std::cout);
  std::cout << "\n";
  auto expr3_der = expr3->Derivative("x");
  std::cout << "Derivative: ";
  expr3_der->WriteExpr(std::cout);
  std::cout << "\n";
  std::cout << "Integrate: ";
  auto expr3_int = expr3->IndefIntegral("x");
  expr3_int->WriteExpr(std::cout);
  std::cout << "\n";

  free_math();
  return 0;
}

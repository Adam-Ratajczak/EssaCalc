#include <iostream>
#include <string>

#include "Expression.hpp"
#include "LispApi.hpp"

int main (int argc, char **argv)
{
  init_ecl(argc, argv);

  std::string _res, _err;
  evaluate("integrate(x/(x+1), x);", _res, _err);
  std::cout << _res << '\n';
  auto expr = Expression::Parse(_res);
  expr->WriteJSON(std::cout);
  std::cout << "\n";
  expr->WriteExpr(std::cout);
  std::cout << "\n";
  expr->WriteLatEx(std::cout);
  std::cout << "\n";
  evaluate("integrate(1/(1+x^2), x);", _res, _err);
  std::cout << _res << '\n';
  expr = Expression::Parse(_res);
  expr->WriteJSON(std::cout);
  std::cout << "\n";
  expr->WriteExpr(std::cout);
  std::cout << "\n";
  expr->WriteLatEx(std::cout);
  std::cout << "\n";
  evaluate("integrate(x/(1+x^2), x);", _res, _err);
  std::cout << _res << '\n';
  expr = Expression::Parse(_res);
  expr->WriteJSON(std::cout);
  std::cout << "\n";
  expr->WriteExpr(std::cout);
  std::cout << "\n";
  expr->WriteLatEx(std::cout);
  std::cout << "\n";

  free_ecl();
  return 0;
}

#include <iostream>
#include <string>

#include "LispApi.hpp"

int main (int argc, char **argv)
{
  init_ecl(argc, argv);

  std::string _res, _err;
  evaluate("integrate(x/(x+1), x);", _res, _err);
  std::cout << _res << '\n';
  evaluate("integrate(1/(1+x^2), x);", _res, _err);
  std::cout << _res << '\n';
  evaluate("integrate(x/(1+x^2), x);", _res, _err);
  std::cout << _res << '\n';

  free_ecl();
  return 0;
}

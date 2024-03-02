#include <ecl/ecl.h>
#include <iostream>
#include <string>

#include "LispApi.hpp"

int main (int argc, char **argv)
{
  init_ecl(argc, argv);

  std::string _result = evaluate("integrate(x/(x+1), x);");
  std::cout << _result << '\n';
  // _result = evaluate("integrate(1/(1+x^2), x);");
  // std::cout << _result << '\n';

  free_ecl();
  return 0;
}

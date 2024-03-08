#include <iostream>
#include <string>

#include "fparser.hpp"

#include <iostream>
#include <string>

int main()
{
    std::string function;
    double minx, maxx, step;
    FunctionParser fparser;

    fparser.AddConstant("pi", 3.1415926535897932);

    while(true)
    {
        std::cout << "f(x) = ";
        std::getline(std::cin, function);
        if(std::cin.fail()) return 0;

        int res = fparser.Parse(function, "x");
        if(res < 0) break;

        std::cout << std::string(res+7, ' ') << "^\n"
                  << fparser.ErrorMsg() << "\n\n";
    }

    std::cout << "min x: ";
    std::cin >> minx;
    std::cout << "max x: ";
    std::cin >> maxx;
    std::cout << "step: ";
    std::cin >> step;
    if(std::cin.fail()) return 0;

    double vals[] = { 0,1 };
    for(vals[0] = minx; vals[0] <= maxx; vals[0] += step)
    {
        std::cout << "f(" << vals[0] << ") = " << fparser.Eval(vals)
                  << std::endl;
    }

    return 0;
}

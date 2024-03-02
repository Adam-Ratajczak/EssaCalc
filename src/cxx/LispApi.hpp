#pragma once
#include <string>
void evaluate(std::string _exp, std::string& _res, std::string& _err);
void init_ecl(int argc, char **argv);
void free_ecl();

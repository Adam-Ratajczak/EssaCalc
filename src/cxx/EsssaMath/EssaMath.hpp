// #include "Defines.hpp"
// #include "Expression.hpp"
// #include "ExpressionHelper.hpp"
// #include "ExpressionNodes.hpp"
// #include "Functions.hpp"
// #include "Generator.hpp"
// #include "Lexer.hpp"
// #include "NodeAllocator.hpp"
// #include "Numeric.hpp"
// #include "OperatorHelpers.hpp"
// #include "Operators.hpp"
// #include "Parser.hpp"
// #include "ParserHelpers.hpp"
// #include "ParserRtl.hpp"
// #include "SymbolTable.hpp"
// #include "Token.hpp"

#include <string>

namespace Essa::Math{
    
void init_math(int argc, char **argv);

std::string evaluate(const std::string& _expr);
void load(const std::string& _expr);

void  free_math();

}
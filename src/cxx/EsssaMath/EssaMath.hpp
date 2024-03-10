#include "Defines.hpp"
#include "Expression.hpp"
#include "ExpressionHelper.hpp"
#include "ExpressionNodes.hpp"
#include "Functions.hpp"
#include "Generator.hpp"
#include "Lexer.hpp"
#include "NodeAllocator.hpp"
#include "Numeric.hpp"
#include "OperatorHelpers.hpp"
#include "Operators.hpp"
#include "Parser.hpp"
#include "ParserHelpers.hpp"
#include "ParserRtl.hpp"
#include "SymbolTable.hpp"
#include "Token.hpp"

namespace Essa::Math{
    
void init_math(int argc, char **argv);
void  free_math();

}
#pragma once

#include "ParserRtl.hpp"
#include <istream>
#include <memory>
#include <sstream>
#include <string>
#include <vector>

namespace Essa::Math{

class LispObject{
public: 
    struct Token{
        enum class Type{
            LEFT, RIGHT, STRING
        };

        Type _type;
        std::string _str;
    };
    LispObject(std::deque<Token>& _tokens){}

    static std::shared_ptr<LispObject> Parse(std::istream& _ss);

    virtual std::string ToString() const = 0;
};

class LispList : public LispObject{
public:
    LispList(std::deque<Token>& _tokens);
    std::string ToString() const override;
private:
    std::string _name;
    std::vector<std::shared_ptr<LispObject>> _objectVec;
};

class LispValue : public LispObject{
public:
    LispValue(std::deque<Token>& _tokens);
    std::string ToString() const override;
private:
    std::string _value;
};
    
void init_math(int argc, char **argv);

std::string evaluate(const std::string& _expr);
void load(const std::string& _expr);

void  free_math();

}

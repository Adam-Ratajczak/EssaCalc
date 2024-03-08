/***************************************************************************\
|* Function Parser for C++ v4.5.2                                          *|
|*-------------------------------------------------------------------------*|
|* Copyright: Juha Nieminen, Joel Yliluoma                                 *|
|*                                                                         *|
|* This library is distributed under the terms of the                      *|
|* GNU Lesser General Public License version 3.                            *|
|* (See lgpl.txt and gpl.txt for the license text.)                        *|
\***************************************************************************/

#include "fpconfig.hpp"
#include "fparser.hpp"

#include <set>
#include <cstdlib>
#include <cstring>
#include <cctype>
#include <cmath>
#include <cassert>
#include <limits>

#include "fptypes.hpp"
#include "fpaux.hpp"
using namespace FUNCTIONPARSERTYPES;

#ifdef FP_USE_THREAD_SAFE_EVAL_WITH_ALLOCA
#ifndef FP_USE_THREAD_SAFE_EVAL
#define FP_USE_THREAD_SAFE_EVAL
#endif
#endif

#ifdef __GNUC__
# define likely(x)       __builtin_expect(!!(x), 1)
# define unlikely(x)     __builtin_expect(!!(x), 0)
#else
# define likely(x)   (x)
# define unlikely(x) (x)
#endif

//=========================================================================
// Opcode analysis functions
//=========================================================================
// These functions are used by the Parse() bytecode optimizer (mostly from
// code in fp_opcode_add.inc).

bool FUNCTIONPARSERTYPES::IsLogicalOpcode(unsigned op)
{
    switch(op)
    {
      case cAnd: case cAbsAnd:
      case cOr:  case cAbsOr:
      case cNot: case cAbsNot:
      case cNotNot: case cAbsNotNot:
      case cEqual: case cNEqual:
      case cLess: case cLessOrEq:
      case cGreater: case cGreaterOrEq:
          return true;
      default: break;
    }
    return false;
}

bool FUNCTIONPARSERTYPES::IsComparisonOpcode(unsigned op)
{
    switch(op)
    {
      case cEqual: case cNEqual:
      case cLess: case cLessOrEq:
      case cGreater: case cGreaterOrEq:
          return true;
      default: break;
    }
    return false;
}

unsigned FUNCTIONPARSERTYPES::OppositeComparisonOpcode(unsigned op)
{
    switch(op)
    {
      case cLess: return cGreater;
      case cGreater: return cLess;
      case cLessOrEq: return cGreaterOrEq;
      case cGreaterOrEq: return cLessOrEq;
    }
    return op;
}

bool FUNCTIONPARSERTYPES::IsNeverNegativeValueOpcode(unsigned op)
{
    switch(op)
    {
      case cAnd: case cAbsAnd:
      case cOr:  case cAbsOr:
      case cNot: case cAbsNot:
      case cNotNot: case cAbsNotNot:
      case cEqual: case cNEqual:
      case cLess: case cLessOrEq:
      case cGreater: case cGreaterOrEq:
      case cSqrt: case cRSqrt: case cSqr:
      case cHypot:
      case cAbs:
      case cAcos: case cCosh:
          return true;
      default: break;
    }
    return false;
}

bool FUNCTIONPARSERTYPES::IsAlwaysIntegerOpcode(unsigned op)
{
    switch(op)
    {
      case cAnd: case cAbsAnd:
      case cOr:  case cAbsOr:
      case cNot: case cAbsNot:
      case cNotNot: case cAbsNotNot:
      case cEqual: case cNEqual:
      case cLess: case cLessOrEq:
      case cGreater: case cGreaterOrEq:
      case cInt: case cFloor: case cCeil: case cTrunc:
          return true;
      default: break;
    }
    return false;
}

bool FUNCTIONPARSERTYPES::IsUnaryOpcode(unsigned op)
{
    switch(op)
    {
      case cInv: case cNeg:
      case cNot: case cAbsNot:
      case cNotNot: case cAbsNotNot:
      case cSqr: case cRSqrt:
      case cDeg: case cRad:
          return true;
    }
    return (op < FUNC_AMOUNT && Functions[op].params == 1);
}

bool FUNCTIONPARSERTYPES::IsBinaryOpcode(unsigned op)
{
    switch(op)
    {
      case cAdd: case cSub: case cRSub:
      case cMul: case cDiv: case cRDiv:
      case cMod:
      case cEqual: case cNEqual: case cLess:
      case cLessOrEq: case cGreater: case cGreaterOrEq:
      case cAnd: case cAbsAnd:
      case cOr: case cAbsOr:
          return true;
    }
    return (op < FUNC_AMOUNT && Functions[op].params == 2);
}

bool FUNCTIONPARSERTYPES::IsVarOpcode(unsigned op)
{
    // See comment in declaration of FP_ParamGuardMask
    return int(op) >= VarBegin;
}

bool FUNCTIONPARSERTYPES::IsCommutativeOrParamSwappableBinaryOpcode(unsigned op)
{
    switch(op)
    {
      case cAdd:
      case cMul:
      case cEqual: case cNEqual:
      case cAnd: case cAbsAnd:
      case cOr: case cAbsOr:
      case cMin: case cMax: case cHypot:
          return true;
      case cDiv: case cSub: case cRDiv: case cRSub:
          return true;
      case cLess: case cGreater:
      case cLessOrEq: case cGreaterOrEq: return true;
    }
    return false;
}

unsigned FUNCTIONPARSERTYPES::GetParamSwappedBinaryOpcode(unsigned op)
{
    switch(op)
    {
      case cAdd:
      case cMul:
      case cEqual: case cNEqual:
      case cAnd: case cAbsAnd:
      case cOr: case cAbsOr:
      case cMin: case cMax: case cHypot:
          return op;
      case cDiv: return cRDiv;
      case cSub: return cRSub;
      case cRDiv: return cDiv;
      case cRSub: return cSub;
      case cLess: return cGreater;
      case cGreater: return cLess;
      case cLessOrEq: return cGreaterOrEq;
      case cGreaterOrEq: return cLessOrEq;
    }
    return op; // Error
}

template<bool ComplexType>
bool FUNCTIONPARSERTYPES::HasInvalidRangesOpcode(unsigned op)
{
    // Returns true, if the given opcode has a range of
    // input values that gives an error.
    if(ComplexType)
    {
        // COMPLEX:
        switch(op)
        {
          case cAtan:  // allowed range: x != +-1i
          case cAtanh: // allowed range: x != +-1
          //case cCot: // allowed range: tan(x) != 0
          //case cCsc: // allowed range: sin(x) != 0
          case cLog:   // allowed range: x != 0
          case cLog2:  // allowed range: x != 0
          case cLog10: // allowed range: x != 0
    #ifdef FP_SUPPORT_OPTIMIZER
          case cLog2by:// allowed range: x != 0
    #endif
          //case cPow: // allowed when: x != 0 or y != 0
          //case cSec: // allowed range: cos(x) != 0
          //case cTan:   // allowed range: cos(x) != 0  --> x != +-(pi/2)
          //case cTanh:  // allowed range: log(x) != -1 --> x != +-(pi/2)i
          case cRSqrt: // allowed range: x != 0
          //case cDiv: // allowed range: y != 0
          //case cRDiv: // allowed range: x != 0
          //case cInv: // allowed range: x != 0
          return true;
        }
    }
    else
    {
        // REAL:
        switch(op)
        {
          case cAcos: // allowed range: |x| <= 1
          case cAsin: // allowed range: |x| <= 1
          case cAcosh: // allowed range: x >= 1
          case cAtanh: // allowed range: |x| < 1
          //case cCot: // allowed range: tan(x) != 0
          //case cCsc: // allowed range: sin(x) != 0
          case cLog:   // allowed range: x > 0
          case cLog2:  // allowed range: x > 0
          case cLog10: // allowed range: x > 0
    #ifdef FP_SUPPORT_OPTIMIZER
          case cLog2by:// allowed range: x > 0
    #endif
          //case cPow: // allowed when: x > 0 or (x = 0 and y != 0) or (x<0)
                       // Technically, when (x<0 and y is not integer),
                       // it is not allowed, but we allow it anyway
                       // in order to make nontrivial roots work.
          //case cSec: // allowed range: cos(x) != 0
          case cSqrt: // allowed range: x >= 0
          case cRSqrt: // allowed range: x > 0
          //case cTan:   // allowed range: cos(x) != 0 --> x != +-(pi/2)
          //case cDiv: // allowed range: y != 0
          //case cRDiv: // allowed range: x != 0
          //case cInv: // allowed range: x != 0
          return true;
        }
    }
    return false;
}

template bool FUNCTIONPARSERTYPES::HasInvalidRangesOpcode<false>(unsigned op);
template bool FUNCTIONPARSERTYPES::HasInvalidRangesOpcode<true>(unsigned op);


#if(0) // Implementation moved to fpaux.hh due to linker problems
//=========================================================================
// Mathematical template functions
//=========================================================================
/* fp_pow() is a wrapper for std::pow()
 * that produces an identical value for
 * exp(1) ^ 2.0  (0x4000000000000000)
 * as exp(2.0)   (0x4000000000000000)
 * - std::pow() on x86_64
 * produces 2.0  (0x3FFFFFFFFFFFFFFF) instead!
 * See comments below for other special traits.
 */
namespace
{
    template<typename ValueT>
    inline ValueT fp_pow_with_exp_log(const ValueT& x, const ValueT& y)
    {
        // Exponentiation using exp(log(x)*y).
        // See http://en.wikipedia.org/wiki/Exponentiation#Real_powers
        // Requirements: x > 0.
        return fp_exp(fp_log(x) * y);
    }

    template<typename ValueT>
    inline ValueT fp_powi(ValueT x, unsigned long y)
    {
        // Fast binary exponentiation algorithm
        // See http://en.wikipedia.org/wiki/Exponentiation_by_squaring
        // Requirements: y is non-negative integer.
        ValueT result(1);
        while(y != 0)
        {
            if(y & 1) { result *= x; y -= 1; }
            else      { x *= x;      y /= 2; }
        }
        return result;
    }
}

template<typename ValueT>
ValueT FUNCTIONPARSERTYPES::fp_pow(const ValueT& x, const ValueT& y)
{
    if(x == ValueT(1)) return ValueT(1);
    // y is now zero or positive
    if(isLongInteger(y))
    {
        // Use fast binary exponentiation algorithm
        if(y >= ValueT(0))
            return fp_powi(x,              makeLongInteger(y));
        else
            return ValueT(1) / fp_powi(x, -makeLongInteger(y));
    }
    if(y >= ValueT(0))
    {
        // y is now positive. Calculate using exp(log(x)*y).
        if(x > ValueT(0)) return fp_pow_with_exp_log(x, y);
        if(x == ValueT(0)) return ValueT(0);
        // At this point, y > 0.0 and x is known to be < 0.0,
        // because positive and zero cases are already handled.
        if(!isInteger(y*ValueT(16)))
            return -fp_pow_with_exp_log(-x, y);
        // ^This is not technically correct, but it allows
        // functions such as cbrt(x^5), that is, x^(5/3),
        // to be evaluated when x is negative.
        // It is too complicated (and slow) to test whether y
        // is a formed from a ratio of an integer to an odd integer.
        // (And due to floating point inaccuracy, pointless too.)
        // For example, x^1.30769230769... is
        // actually x^(17/13), i.e. (x^17) ^ (1/13).
        // (-5)^(17/13) gives us now -8.204227562330453.
        // To see whether the result is right, we can test the given
        // root: (-8.204227562330453)^13 gives us the value of (-5)^17,
        // which proves that the expression was correct.
        //
        // The y*16 check prevents e.g. (-4)^(3/2) from being calculated,
        // as it would confuse functioninfo when pow() returns no error
        // but sqrt() does when the formula is converted into sqrt(x)*x.
        //
        // The errors in this approach are:
        //     (-2)^sqrt(2) should produce NaN
        //                  or actually sqrt(2)I + 2^sqrt(2),
        //                  produces -(2^sqrt(2)) instead.
        //                  (Impact: Neglible)
        // Thus, at worst, we're changing a NaN (or complex)
        // result into a negative real number result.
    }
    else
    {
        // y is negative. Utilize the x^y = 1/(x^-y) identity.
        if(x > ValueT(0)) return fp_pow_with_exp_log(ValueT(1) / x, -y);
        if(x < ValueT(0))
        {
            if(!isInteger(y*ValueT(-16)))
                return -fp_pow_with_exp_log(ValueT(-1) / x, -y);
            // ^ See comment above.
        }
        // Remaining case: 0.0 ^ negative number
    }
    // This is reached when:
    //      x=0, and y<0
    //      x<0, and y*16 is either positive or negative integer
    // It is used for producing error values and as a safe fallback.
    return fp_pow_base(x, y);
}
#endif


//=========================================================================
// Elementary (atom) parsing functions
//=========================================================================
namespace
{
    const unsigned FP_ParamGuardMask = 1U << (sizeof(unsigned) * 8u - 1u);
    // ^ This mask is used to prevent cFetch/other opcode's parameters
    //   from being confused into opcodes or variable indices within the
    //   bytecode optimizer. Because the way it is tested in bytecoderules.dat
    //   for speed reasons, it must also be the sign-bit of the "int" datatype.
    //   Perhaps an "assert(IsVarOpcode(X | FP_ParamGuardMask) == false)"
    //   might be justified to put somewhere in the code, just in case?


    /* Reads an UTF8-encoded sequence which forms a valid identifier name from
       the given input string and returns its length. If bit 31 is set, the
       return value also contains the internal function opcode (defined in
       fptypes.hh) that matches the name.
    */
    unsigned readIdentifierCommon(const char* input)
    {
        unsigned nameLength = 0;
        const unsigned maximumNameLength = 0x80000000U-8;
        /*
        Due to the manner the identifier lengths are returned from
        the readOpcode() function, the maximum supported length for
        identifiers is 0x7FFFFFFF bytes. We minus 8 here to add some
        buffer, because of the multibyteness of UTF-8.
        Function names are limited to 0xFFFF bytes instead, but because
        function names that long just are not defined, the point is moot.
        */
        const unsigned char* const uptr = (const unsigned char*) input;
        typedef signed char schar;
        while(likely(nameLength < maximumNameLength))
        {
            unsigned char byte = uptr[nameLength+0];
            /* Handle the common case of A-Za-z first */
            if(byte >= 0x40)
            {
                if(byte < 0x80) // 0x40..0x7F - most common case
                {
                    // Valid characters in 40..7F: A-Za-z_
                    // Valid bitmask for 40..5F: 01111111111111111111111111100001
                    // Valid bitmask for 60..7F: 01111111111111111111111111100000
                    if(sizeof(unsigned long) == 8)
                    {
                        const unsigned n = sizeof(unsigned long)*8-32;
                        // ^ avoids compiler warning when not 64-bit
                        unsigned long masklow6bits = 1UL << (byte & 0x3F);
                        if(masklow6bits & ~((1UL << 0) | (0x0FUL << (0x1B  ))
                                          | (1UL << n) | (0x1FUL << (0x1B+n))))
                            { ++nameLength; continue; }
                    }
                    else
                    {
                        unsigned masklow5bits = 1 << (byte & 0x1F);
                        if((masklow5bits & ~(1 | (0x1F << 0x1B))) || byte == '_')
                            { ++nameLength; continue; }
                    }
                    break;
                }
                if(byte < 0xF0)
                {
                    if(byte < 0xE0)
                    {
                        if(byte < 0xC2) break; // 0x80..0xC1
                        if(byte == 0xC2 && uptr[nameLength+1]==0xA0) break; // skip nbsp
                        // C2-DF - next common case when >= 0x40
                        // Valid sequence: C2-DF 80-BF
                        if(schar(uptr[nameLength+1]) > schar(0xBF)) break;
                        nameLength += 2;
                        continue;
                    }
                    if(byte == 0xE0) // E0
                    {
                        // Valid sequence: E0 A0-BF 80-BF
                        if((unsigned char)(uptr[nameLength+1] - 0xA0) > (0xBF-0xA0)) break;
                    }
                    else
                    {
                        if(byte == 0xED) break; // ED is invalid
                        // Valid sequence: E1-EC 80-BF 80-BF
                        //            And: EE-EF 80-BF 80-BF
                        if(byte == 0xE2)
                        {
                            // break on various space characters
                            if(uptr[nameLength+1] == 0x80
                            && (schar(uptr[nameLength+2]) <= schar(0x8B)
                            || (uptr[nameLength+2] == 0xAF))) break;
                            if(uptr[nameLength+1] == 0x81
                            && uptr[nameLength+2] == 0x9F) break;
                        } else
                        if(byte == 0xE3 && uptr[nameLength+1] == 0x80
                        && uptr[nameLength+2] == 0x80) break; // this too

                        if(schar(uptr[nameLength+1]) > schar(0xBF)) break;
                    }
                    if(schar(uptr[nameLength+2]) > schar(0xBF)) break;
                    nameLength += 3;
                    continue;
                }
                if(byte == 0xF0) // F0
                {
                    // Valid sequence: F0 90-BF 80-BF 80-BF
                    if((unsigned char)(uptr[nameLength+1] - 0x90) > (0xBF-0x90)) break;
                }
                else
                {
                    if(byte > 0xF4) break; // F5-FF are invalid
                    if(byte == 0xF4) // F4
                    {
                        // Valid sequence: F4 80-8F
                        if(schar(uptr[nameLength+1]) > schar(0x8F)) break;
                    }
                    else
                    {
                        // F1-F3
                        // Valid sequence: F1-F3 80-BF 80-BF 80-BF
                        if(schar(uptr[nameLength+1]) > schar(0xBF)) break;
                    }
                }
                if(schar(uptr[nameLength+2]) > schar(0xBF)) break;
                if(schar(uptr[nameLength+3]) > schar(0xBF)) break;
                nameLength += 4;
                continue;
            }
            if(nameLength > 0)
            {
                if(sizeof(unsigned long) == 8)
                {
                    // Valid bitmask for 00..1F: 00000000000000000000000000000000
                    // Valid bitmask for 20..3F: 00000000000000001111111111000000
                    const unsigned n = sizeof(unsigned long)*8-32;
                    // ^ avoids compiler warning when not 64-bit
                    unsigned long masklow6bits = 1UL << byte;
                    if(masklow6bits & (((1UL << 10)-1UL) << (16+n)))
                        { ++nameLength; continue; }
                }
                else
                {
                    if(byte >= '0' && byte <= '9')
                        { ++nameLength; continue; }
                }
            }
            break;
        }

        /* This function generated with make_function_name_parser.cc */
#define lO l3 lH
#define lN switch(
#define lM l4 lH
#define lL if('i' l5
#define lK 'n' l5
#define lJ 0x80000003U;
#define lI l1 3]={
#define lH case
#define lG 0x80000005U;
#define lF )==0)l0(
#define lE l8 3;}lH
#define lD std::memcmp(uptr+
#define lC l2 3 lF
#define lB lA 1]){lH
#define lA :lN uptr[
#define l9 'a' lB
#define l8 default:l0
#define l7 lG l0 5;}lH
#define l6 <<16)|
#define l5 ==uptr[
#define l4 lJ l0 3;
#define l3 0x80000004U;l0 4;
#define l2 lD 1,tmp,
#define l1 static const char tmp[
#define l0 return
lN
nameLength){lH
2:lL
0]&&'f' l5
1])l0(cIf
l6
0x80000002U;l0
2;lH
3
lA
0]){lH
l9'b':if('s' l5
2])l0(cAbs
l6
lM'r':if('g' l5
2])l0(cArg
l6
l4
lE'c' lB'o' lA
2]){lH's':l0(cCos
l6
lJ
lH't':l0(cCot
l6
lJ
lE's':if('c' l5
2])l0(cCsc
l6
l4
lE'e':if('x' l5
1]&&'p' l5
2])l0(cExp
l6
lM'i':if(lK
1]&&'t' l5
2])l0(cInt
l6
lM'l':if('o' l5
1]&&'g' l5
2])l0(cLog
l6
lM'm' lB'a':if('x' l5
2])l0(cMax
l6
lM'i':if(lK
2])l0(cMin
l6
l4
lE'p':if('o' l5
1]&&'w' l5
2])l0(cPow
l6
lM's' lB'e':if('c' l5
2])l0(cSec
l6
lM'i':if(lK
2])l0(cSin
l6
l4
lE't':if('a' l5
1]&&lK
2])l0(cTan
l6
l4
lE
4
lA
0]){lH
l9'c':if('o' l5
2]&&'s' l5
3])l0(cAcos
l6
lO's':lL
2]&&lK
3])l0(cAsin
l6
lO't':if('a' l5
2]&&lK
3])l0(cAtan
l6
l3
l8
4;}
lH'c' lB'b':if('r' l5
2]&&'t' l5
3])l0(cCbrt
l6
lO'e':lL
2]&&'l' l5
3])l0(cCeil
l6
lO'o' lA
2]){lH'n':if('j' l5
3])l0(cConj
l6
lO's':if('h' l5
3])l0(cCosh
l6
l3
l8
4;}
l8
4;}
lH'e':{lI'x','p','2'}
;if(lC
cExp2
l6
l3}
lH'i':{lI'm','a','g'}
;if(lC
cImag
l6
l3}
lH'l':{lI'o','g','2'}
;if(lC
cLog2
l6
l3}
lH'r':{lI'e','a','l'}
;if(lC
cReal
l6
l3}
lH's' lB'i':if(lK
2]&&'h' l5
3])l0(cSinh
l6
lO'q':if('r' l5
2]&&'t' l5
3])l0(cSqrt
l6
l3
l8
4;}
lH't':{lI'a','n','h'}
;if(lC
cTanh
l6
l3}
l8
4;}
lH
5
lA
0]){lH
l9'c':{lI'o','s','h'}
;if(lD
2,tmp,3
lF
cAcosh
l6
l7's':{lI'i','n','h'}
;if(lD
2,tmp,3
lF
cAsinh
l6
l7't':if('a' l5
2]){if(lK
3]){lN
uptr[4]){lH'2':l0(cAtan2
l6
lG
lH'h':l0(cAtanh
l6
lG
l8
5;}
}
l0
5;}
l0
5;l8
5;}
lH'f':{l1
4]={'l','o','o','r'}
;if(l2
4
lF
cFloor
l6
l7'h':{l1
4]={'y','p','o','t'}
;if(l2
4
lF
cHypot
l6
l7'l':{l1
4]={'o','g','1','0'}
;if(l2
4
lF
cLog10
l6
l7'p':{l1
4]={'o','l','a','r'}
;if(l2
4
lF
cPolar
l6
l7't':{l1
4]={'r','u','n','c'}
;if(l2
4
lF
cTrunc
l6
lG
l0
5;}
l8
5;}
default:break;}
l0
nameLength;
        return 0;
    }

    template<typename Value_t>
    inline unsigned readIdentifier(const char* input)
    {
        const unsigned value = readIdentifierCommon(input);
        if( (value & 0x80000000U) != 0) // Function?
        {
            // Verify that the function actually exists for this datatype
            if(IsIntType<Value_t>::result
            && !Functions[(value >> 16) & 0x7FFF].okForInt())
            {
                // If it does not exist, return it as an identifier instead
                return value & 0xFFFFu;
            }
            if(!IsComplexType<Value_t>::result
            && Functions[(value >> 16) & 0x7FFF].complexOnly())
            {
                // If it does not exist, return it as an identifier instead
                return value & 0xFFFFu;
            }
        }
        return value;
    }

    // Returns true if the entire string is a valid identifier
    template<typename Value_t>
    bool containsOnlyValidIdentifierChars(const std::string& name)
    {
        if(name.empty()) return false;
        return readIdentifier<Value_t>(name.c_str()) == (unsigned) name.size();
    }


    // -----------------------------------------------------------------------
    // Wrappers for strto... functions
    // -----------------------------------------------------------------------
    template<typename Value_t>
    inline Value_t fp_parseLiteral(const char* str, char** endptr)
    {
        return std::strtod(str, endptr);
    }

#if defined(FP_USE_STRTOLD) || defined(FP_SUPPORT_CPLUSPLUS11_MATH_FUNCS)
    template<>
    inline long double fp_parseLiteral<long double>(const char* str,
                                                    char** endptr)
    {
        using namespace std; // Just in case strtold() is not inside std::
        return strtold(str, endptr);
    }
#endif

#ifdef FP_SUPPORT_LONG_INT_TYPE
    template<>
    inline long fp_parseLiteral<long>(const char* str, char** endptr)
    {
        return std::strtol(str, endptr, 10);
    }
#endif

#ifdef FP_SUPPORT_COMPLEX_NUMBERS
    template<typename T>
    inline std::complex<T> fp_parseComplexLiteral(const char* str,
                                                  char** endptr)
    {
        T result = fp_parseLiteral<T> (str,endptr);
        const char* end = *endptr;
        if( (*end == 'i'  || *end == 'I')
        &&  !std::isalnum(end[1]) )
        {
            ++*endptr;
            return std::complex<T> (T(), result);
        }
        return std::complex<T> (result, T());
    }
#endif

#ifdef FP_SUPPORT_COMPLEX_DOUBLE_TYPE
    template<>
    inline std::complex<double> fp_parseLiteral<std::complex<double> >
    (const char* str, char** endptr)
    {
        return fp_parseComplexLiteral<double> (str,endptr);
    }
#endif

#ifdef FP_SUPPORT_COMPLEX_FLOAT_TYPE
    template<>
    inline std::complex<float> fp_parseLiteral<std::complex<float> >
    (const char* str, char** endptr)
    {
        return fp_parseComplexLiteral<float> (str,endptr);
    }
#endif

#ifdef FP_SUPPORT_COMPLEX_LONG_DOUBLE_TYPE
    template<>
    inline std::complex<long double> fp_parseLiteral<std::complex<long double> >
    (const char* str, char** endptr)
    {
        return fp_parseComplexLiteral<long double> (str,endptr);
    }
#endif

    // -----------------------------------------------------------------------
    // Hexadecimal floating point literal parsing
    // -----------------------------------------------------------------------
    inline int testXdigit(unsigned c)
    {
        if((c-'0') < 10u) return c&15; // 0..9
        if(((c|0x20)-'a') < 6u) return 9+(c&15); // A..F or a..f
        return -1; // Not a hex digit
    }

    template<typename elem_t, unsigned n_limbs, unsigned limb_bits>
    inline void addXdigit(elem_t* buffer, unsigned nibble)
    {
        for(unsigned p=0; p<n_limbs; ++p)
        {
            unsigned carry = unsigned( buffer[p] >> (elem_t)(limb_bits-4) );
            buffer[p] = (buffer[p] << 4) | nibble;
            nibble = carry;
        }
    }

    template<typename Value_t>
    Value_t parseHexLiteral(const char* str, char** endptr)
    {
        const unsigned bits_per_char = 8;

        const int MantissaBits =
            std::numeric_limits<Value_t>::radix == 2
            ? std::numeric_limits<Value_t>::digits
            : (((sizeof(Value_t) * bits_per_char) &~ 3) - 4);

        typedef unsigned long elem_t;
        const int ExtraMantissaBits = 4 + ((MantissaBits+3)&~3); // Store one digit more for correct rounding
        const unsigned limb_bits = sizeof(elem_t) * bits_per_char;
        const unsigned n_limbs   = (ExtraMantissaBits + limb_bits-1) / limb_bits;
        elem_t mantissa_buffer[n_limbs] = { 0 };

        int n_mantissa_bits = 0; // Track the number of bits
        int exponent = 0; // The exponent that will be used to multiply the mantissa
        // Read integer portion
        while(true)
        {
            int xdigit = testXdigit(*str);
            if(xdigit < 0) break;
            addXdigit<elem_t,n_limbs,limb_bits> (mantissa_buffer, xdigit);
            ++str;

            n_mantissa_bits += 4;
            if(n_mantissa_bits >= ExtraMantissaBits)
            {
                // Exhausted the precision. Parse the rest (until exponent)
                // normally but ignore the actual digits.
                for(; testXdigit(*str) >= 0; ++str)
                    exponent += 4;
                // Read but ignore decimals
                if(*str == '.')
                    for(++str; testXdigit(*str) >= 0; ++str)
                        {}
                goto read_exponent;
            }
        }
        // Read decimals
        if(*str == '.')
            for(++str; ; )
            {
                int xdigit = testXdigit(*str);
                if(xdigit < 0) break;
                addXdigit<elem_t,n_limbs,limb_bits> (mantissa_buffer, xdigit);
                ++str;

                exponent -= 4;
                n_mantissa_bits += 4;
                if(n_mantissa_bits >= ExtraMantissaBits)
                {
                    // Exhausted the precision. Skip the rest
                    // of the decimals, until the exponent.
                    while(testXdigit(*str) >= 0)
                        ++str;
                    break;
                }
            }

        // Read exponent
    read_exponent:
        if(*str == 'p' || *str == 'P')
        {
            const char* str2 = str+1;
            long p_exponent = strtol(str2, const_cast<char**> (&str2), 10);
            if(str2 != str+1 && p_exponent == (long)(int)p_exponent)
            {
                exponent += (int)p_exponent;
                str = str2;
            }
        }

        if(endptr) *endptr = const_cast<char*> (str);

        Value_t result = std::ldexp(Value_t(mantissa_buffer[0]), exponent);
        for(unsigned p=1; p<n_limbs; ++p)
        {
            exponent += limb_bits;
            result += ldexp(Value_t(mantissa_buffer[p]), exponent);
        }
        return result;
    }

#ifdef FP_SUPPORT_LONG_INT_TYPE
    template<>
    long parseHexLiteral<long>(const char* str, char** endptr)
    {
        return std::strtol(str, endptr, 16);
    }
#endif

#ifdef FP_SUPPORT_COMPLEX_DOUBLE_TYPE
    template<>
    std::complex<double>
    parseHexLiteral<std::complex<double> >(const char* str, char** endptr)
    {
        return parseHexLiteral<double> (str, endptr);
    }
#endif

#ifdef FP_SUPPORT_COMPLEX_FLOAT_TYPE
    template<>
    std::complex<float>
    parseHexLiteral<std::complex<float> >(const char* str, char** endptr)
    {
        return parseHexLiteral<float> (str, endptr);
    }
#endif

#ifdef FP_SUPPORT_COMPLEX_LONG_DOUBLE_TYPE
    template<>
    std::complex<long double>
    parseHexLiteral<std::complex<long double> >(const char* str, char** endptr)
    {
        return parseHexLiteral<long double> (str, endptr);
    }
#endif
}

//=========================================================================
// Utility functions
//=========================================================================
namespace
{
    // -----------------------------------------------------------------------
    // Add a new identifier to the specified identifier map
    // -----------------------------------------------------------------------
    // Return value will be false if the name already existed
    template<typename Value_t>
    bool addNewNameData(NamePtrsMap<Value_t>& namePtrs,
                        std::pair<NamePtr, NameData<Value_t> >& newName,
                        bool isVar)
    {
        typename NamePtrsMap<Value_t>::iterator nameIter =
            namePtrs.lower_bound(newName.first);

        if(nameIter != namePtrs.end() && newName.first == nameIter->first)
        {
            // redefining a var is not allowed.
            if(isVar) return false;

            // redefining other tokens is allowed, if the type stays the same.
            if(nameIter->second.type != newName.second.type)
                return false;

            // update the data
            nameIter->second = newName.second;
            return true;
        }

        if(!isVar)
        {
            // Allocate a copy of the name (pointer stored in the map key)
            // However, for VARIABLEs, the pointer points to VariableString,
            // which is managed separately. Thusly, only done when !IsVar.
            char* namebuf = new char[newName.first.nameLength];
            memcpy(namebuf, newName.first.name, newName.first.nameLength);
            newName.first.name = namebuf;
        }

        namePtrs.insert(nameIter, newName);
        return true;
    }
}


//=========================================================================
// Data struct implementation
//=========================================================================
template<typename Value_t>
FunctionParserBase<Value_t>::Data::Data():
    mReferenceCounter(1),
    mDelimiterChar(0),
    mParseErrorType(NO_FUNCTION_PARSED_YET),
    mEvalErrorType(0),
    mUseDegreeConversion(false),
    mErrorLocation(0),
    mVariablesAmount(0),
    mStackSize(0)
{}

template<typename Value_t>
FunctionParserBase<Value_t>::Data::Data(const Data& rhs):
    mReferenceCounter(0),
    mDelimiterChar(rhs.mDelimiterChar),
    mParseErrorType(rhs.mParseErrorType),
    mEvalErrorType(rhs.mEvalErrorType),
    mUseDegreeConversion(rhs.mUseDegreeConversion),
    mErrorLocation(rhs.mErrorLocation),
    mVariablesAmount(rhs.mVariablesAmount),
    mVariablesString(rhs.mVariablesString),
    mNamePtrs(),
    mFuncPtrs(rhs.mFuncPtrs),
    mFuncParsers(rhs.mFuncParsers),
    mByteCode(rhs.mByteCode),
    mImmed(rhs.mImmed),
#ifndef FP_USE_THREAD_SAFE_EVAL
    mStack(rhs.mStackSize),
#endif
    mStackSize(rhs.mStackSize)
{
    for(typename NamePtrsMap<Value_t>::const_iterator i = rhs.mNamePtrs.begin();
        i != rhs.mNamePtrs.end();
        ++i)
    {
        if(i->second.type == NameData<Value_t>::VARIABLE)
        {
            const std::size_t variableStringOffset =
                i->first.name - rhs.mVariablesString.c_str();
            std::pair<NamePtr, NameData<Value_t> > tmp
                (NamePtr(&mVariablesString[variableStringOffset],
                         i->first.nameLength),
                 i->second);
            mNamePtrs.insert(mNamePtrs.end(), tmp);
        }
        else
        {
            std::pair<NamePtr, NameData<Value_t> > tmp
                (NamePtr(new char[i->first.nameLength], i->first.nameLength),
                 i->second );
            memcpy(const_cast<char*>(tmp.first.name), i->first.name,
                   tmp.first.nameLength);
            mNamePtrs.insert(mNamePtrs.end(), tmp);
        }
    }
}

template<typename Value_t>
FunctionParserBase<Value_t>::Data::~Data()
{
    for(typename NamePtrsMap<Value_t>::iterator i = mNamePtrs.begin();
        i != mNamePtrs.end();
        ++i)
    {
        if(i->second.type != NameData<Value_t>::VARIABLE)
            delete[] i->first.name;
    }
}

template<typename Value_t>
void FunctionParserBase<Value_t>::incFuncWrapperRefCount
(FunctionWrapper* wrapper)
{
    ++wrapper->mReferenceCount;
}

template<typename Value_t>
unsigned FunctionParserBase<Value_t>::decFuncWrapperRefCount
(FunctionWrapper* wrapper)
{
    return --wrapper->mReferenceCount;
}

template<typename Value_t>
FunctionParserBase<Value_t>::Data::FuncWrapperPtrData::FuncWrapperPtrData():
    mRawFuncPtr(0), mFuncWrapperPtr(0), mParams(0)
{}

template<typename Value_t>
FunctionParserBase<Value_t>::Data::FuncWrapperPtrData::~FuncWrapperPtrData()
{
    if(mFuncWrapperPtr &&
       FunctionParserBase::decFuncWrapperRefCount(mFuncWrapperPtr) == 0)
        delete mFuncWrapperPtr;
}

template<typename Value_t>
FunctionParserBase<Value_t>::Data::FuncWrapperPtrData::FuncWrapperPtrData
(const FuncWrapperPtrData& rhs):
    mRawFuncPtr(rhs.mRawFuncPtr),
    mFuncWrapperPtr(rhs.mFuncWrapperPtr),
    mParams(rhs.mParams)
{
    if(mFuncWrapperPtr)
        FunctionParserBase::incFuncWrapperRefCount(mFuncWrapperPtr);
}

template<typename Value_t>
typename FunctionParserBase<Value_t>::Data::FuncWrapperPtrData&
FunctionParserBase<Value_t>::Data::FuncWrapperPtrData::operator=
(const FuncWrapperPtrData& rhs)
{
    if(&rhs != this)
    {
        if(mFuncWrapperPtr &&
           FunctionParserBase::decFuncWrapperRefCount(mFuncWrapperPtr) == 0)
            delete mFuncWrapperPtr;
        mRawFuncPtr = rhs.mRawFuncPtr;
        mFuncWrapperPtr = rhs.mFuncWrapperPtr;
        mParams = rhs.mParams;
        if(mFuncWrapperPtr)
            FunctionParserBase::incFuncWrapperRefCount(mFuncWrapperPtr);
    }
    return *this;
}


//=========================================================================
// FunctionParser constructors, destructor and assignment
//=========================================================================
template<typename Value_t>
FunctionParserBase<Value_t>::FunctionParserBase():
    mData(new Data),
    mStackPtr(0)
{
}

template<typename Value_t>
FunctionParserBase<Value_t>::~FunctionParserBase()
{
    if(--(mData->mReferenceCounter) == 0)
        delete mData;
}

template<typename Value_t>
FunctionParserBase<Value_t>::FunctionParserBase(const FunctionParserBase& cpy):
    mData(cpy.mData),
    mStackPtr(0)
{
    ++(mData->mReferenceCounter);
}

template<typename Value_t>
FunctionParserBase<Value_t>&
FunctionParserBase<Value_t>::operator=(const FunctionParserBase& cpy)
{
    if(mData != cpy.mData)
    {
        if(--(mData->mReferenceCounter) == 0) delete mData;

        mData = cpy.mData;
        ++(mData->mReferenceCounter);
    }
    return *this;
}

template<typename Value_t>
typename FunctionParserBase<Value_t>::Data*
FunctionParserBase<Value_t>::getParserData()
{
    return mData;
}

template<typename Value_t>
void FunctionParserBase<Value_t>::setDelimiterChar(char c)
{
    mData->mDelimiterChar = c;
}


//---------------------------------------------------------------------------
// Copy-on-write method
//---------------------------------------------------------------------------
template<typename Value_t>
void FunctionParserBase<Value_t>::CopyOnWrite()
{
    if(mData->mReferenceCounter > 1)
    {
        Data* oldData = mData;
        mData = new Data(*oldData);
        --(oldData->mReferenceCounter);
        mData->mReferenceCounter = 1;
    }
}

template<typename Value_t>
void FunctionParserBase<Value_t>::ForceDeepCopy()
{
    CopyOnWrite();
}


//=========================================================================
// Epsilon
//=========================================================================
template<typename Value_t>
Value_t FunctionParserBase<Value_t>::epsilon()
{
    return Epsilon<Value_t>::value;
}

template<typename Value_t>
void FunctionParserBase<Value_t>::setEpsilon(Value_t value)
{
    Epsilon<Value_t>::value = value;
}


//=========================================================================
// User-defined identifier addition functions
//=========================================================================
template<typename Value_t>
bool FunctionParserBase<Value_t>::AddConstant(const std::string& name,
                                              Value_t value)
{
    if(!containsOnlyValidIdentifierChars<Value_t>(name)) return false;

    CopyOnWrite();
    std::pair<NamePtr, NameData<Value_t> > newName
        (NamePtr(name.data(), unsigned(name.size())),
         NameData<Value_t>(NameData<Value_t>::CONSTANT, value));

    return addNewNameData(mData->mNamePtrs, newName, false);
}

template<typename Value_t>
bool FunctionParserBase<Value_t>::AddUnit(const std::string& name,
                                          Value_t value)
{
    if(!containsOnlyValidIdentifierChars<Value_t>(name)) return false;

    CopyOnWrite();
    std::pair<NamePtr, NameData<Value_t> > newName
        (NamePtr(name.data(), unsigned(name.size())),
         NameData<Value_t>(NameData<Value_t>::UNIT, value));
    return addNewNameData(mData->mNamePtrs, newName, false);
}

template<typename Value_t>
bool FunctionParserBase<Value_t>::AddFunction
(const std::string& name, FunctionPtr ptr, unsigned paramsAmount)
{
    if(!containsOnlyValidIdentifierChars<Value_t>(name)) return false;

    CopyOnWrite();
    std::pair<NamePtr, NameData<Value_t> > newName
        (NamePtr(name.data(), unsigned(name.size())),
         NameData<Value_t>(NameData<Value_t>::FUNC_PTR,
                           unsigned(mData->mFuncPtrs.size())));

    const bool success = addNewNameData(mData->mNamePtrs, newName, false);
    if(success)
    {
        mData->mFuncPtrs.push_back(typename Data::FuncWrapperPtrData());
        mData->mFuncPtrs.back().mRawFuncPtr = ptr;
        mData->mFuncPtrs.back().mParams = paramsAmount;
    }
    return success;
}

template<typename Value_t>
bool FunctionParserBase<Value_t>::addFunctionWrapperPtr
(const std::string& name, FunctionWrapper* wrapper, unsigned paramsAmount)
{
    if(!AddFunction(name, FunctionPtr(0), paramsAmount)) return false;
    mData->mFuncPtrs.back().mFuncWrapperPtr = wrapper;
    return true;
}

template<typename Value_t>
typename FunctionParserBase<Value_t>::FunctionWrapper*
FunctionParserBase<Value_t>::GetFunctionWrapper(const std::string& name)
{
    CopyOnWrite();
    NamePtr namePtr(name.data(), unsigned(name.size()));

    typename NamePtrsMap<Value_t>::iterator nameIter =
        mData->mNamePtrs.find(namePtr);

    if(nameIter != mData->mNamePtrs.end() &&
       nameIter->second.type == NameData<Value_t>::FUNC_PTR)
    {
        return mData->mFuncPtrs[nameIter->second.index].mFuncWrapperPtr;
    }
    return 0;
}

template<typename Value_t>
bool FunctionParserBase<Value_t>::CheckRecursiveLinking
(const FunctionParserBase* fp) const
{
    if(fp == this) return true;
    for(unsigned i = 0; i < fp->mData->mFuncParsers.size(); ++i)
        if(CheckRecursiveLinking(fp->mData->mFuncParsers[i].mParserPtr))
            return true;
    return false;
}

template<typename Value_t>
bool FunctionParserBase<Value_t>::AddFunction(const std::string& name,
                                              FunctionParserBase& fp)
{
    if(!containsOnlyValidIdentifierChars<Value_t>(name) ||
       CheckRecursiveLinking(&fp))
        return false;

    CopyOnWrite();
    std::pair<NamePtr, NameData<Value_t> > newName
        (NamePtr(name.data(), unsigned(name.size())),
         NameData<Value_t>(NameData<Value_t>::PARSER_PTR,
                           unsigned(mData->mFuncParsers.size())));

    const bool success = addNewNameData(mData->mNamePtrs, newName, false);
    if(success)
    {
        mData->mFuncParsers.push_back(typename Data::FuncParserPtrData());
        mData->mFuncParsers.back().mParserPtr = &fp;
        mData->mFuncParsers.back().mParams = fp.mData->mVariablesAmount;
    }
    return success;
}

template<typename Value_t>
bool FunctionParserBase<Value_t>::RemoveIdentifier(const std::string& name)
{
    CopyOnWrite();

    NamePtr namePtr(name.data(), unsigned(name.size()));

    typename NamePtrsMap<Value_t>::iterator nameIter =
        mData->mNamePtrs.find(namePtr);

    if(nameIter != mData->mNamePtrs.end())
    {
        if(nameIter->second.type == NameData<Value_t>::VARIABLE)
        {
            // Illegal attempt to delete variables
            return false;
        }
        delete[] nameIter->first.name;
        mData->mNamePtrs.erase(nameIter);
        return true;
    }
    return false;
}


//=========================================================================
// Function parsing
//=========================================================================
namespace
{
    // Error messages returned by ErrorMsg():
    const char* const ParseErrorMessage[]=
    {
        "Syntax error",                             // 0
        "Mismatched parenthesis",                   // 1
        "Missing ')'",                              // 2
        "Empty parentheses",                        // 3
        "Syntax error: Operator expected",          // 4
        "Not enough memory",                        // 5
        "An unexpected error occurred. Please make a full bug report "
        "to the author",                            // 6
        "Syntax error in parameter 'Vars' given to "
        "FunctionParser::Parse()",                  // 7
        "Illegal number of parameters to function", // 8
        "Syntax error: Premature end of string",    // 9
        "Syntax error: Expecting ( after function", // 10
        "Syntax error: Unknown identifier",         // 11
        "(No function has been parsed yet)",
        ""
    };

    template<typename Value_t>
    inline typename FunctionParserBase<Value_t>::ParseErrorType
    noCommaError(char c)
    {
        return c == ')' ?
            FunctionParserBase<Value_t>::ILL_PARAMS_AMOUNT :
            FunctionParserBase<Value_t>::SYNTAX_ERROR;
    }

    template<typename Value_t>
    inline typename FunctionParserBase<Value_t>::ParseErrorType
    noParenthError(char c)
    {
        return c == ',' ?
            FunctionParserBase<Value_t>::ILL_PARAMS_AMOUNT :
            FunctionParserBase<Value_t>::MISSING_PARENTH;
    }

    template<unsigned offset>
    struct IntLiteralMask
    {
        enum { mask =
        //    (    1UL << ('-'-offset)) |
            (0x3FFUL << ('0'-offset)) }; /* 0x3FF = 10 bits worth "1" */
        // Note: If you change fparser to support negative numbers parsing
        //       (as opposed to parsing them as cNeg followed by literal),
        //       enable the '-' line above, and change the offset value
        //       in BeginsLiteral() to '-' instead of '.'.
    };

    template<typename Value_t, unsigned offset>
    struct LiteralMask
    {
        enum { mask =
            (    1UL << ('.'-offset)) |
            IntLiteralMask<offset>::mask };
    };
#ifdef FP_SUPPORT_LONG_INT_TYPE
    template<unsigned offset>
    struct LiteralMask<long, offset>: public IntLiteralMask<offset>
    {
    };
#endif
#ifdef FP_SUPPORT_GMP_INT_TYPE
    template<unsigned offset>
    struct LiteralMask<GmpInt, offset>: public IntLiteralMask<offset>
    {
    };
#endif

    template<unsigned offset>
    struct SimpleSpaceMask
    {
        enum { mask =
            (1UL << ('\r'-offset)) |
            (1UL << ('\n'-offset)) |
            (1UL << ('\v'-offset)) |
            (1UL << ('\t'-offset)) |
            (1UL << (' ' -offset)) };
    };

    template<typename Value_t>
    inline bool BeginsLiteral(unsigned byte)
    {
        enum { n = sizeof(unsigned long)>=8 ? 0 : '.' };
        byte -= n;
        if(byte > (unsigned char)('9'-n)) return false;
        unsigned long shifted = 1UL << byte;
        const unsigned long mask = LiteralMask<Value_t, n>::mask;
        return (mask & shifted) != 0;
    }

    template<typename CharPtr>
    inline void SkipSpace(CharPtr& function)
    {
/*
        Space characters in unicode:
U+0020  SPACE                      Depends on font, often adjusted (see below)
U+00A0  NO-BREAK SPACE             As a space, but often not adjusted
U+2000  EN QUAD                    1 en (= 1/2 em)
U+2001  EM QUAD                    1 em (nominally, the height of the font)
U+2002  EN SPACE                   1 en (= 1/2 em)
U+2003  EM SPACE                   1 em
U+2004  THREE-PER-EM SPACE         1/3 em
U+2005  FOUR-PER-EM SPACE          1/4 em
U+2006  SIX-PER-EM SPACE           1/6 em
U+2007  FIGURE SPACE               Tabular width, the width of digits
U+2008  PUNCTUATION SPACE          The width of a period .
U+2009  THIN SPACE                 1/5 em (or sometimes 1/6 em)
U+200A  HAIR SPACE                 Narrower than THIN SPACE
U+200B  ZERO WIDTH SPACE           Nominally no width, but may expand
U+202F  NARROW NO-BREAK SPACE      Narrower than NO-BREAK SPACE (or SPACE)
U+205F  MEDIUM MATHEMATICAL SPACE  4/18 em
U+3000  IDEOGRAPHIC SPACE          The width of ideographic (CJK) characters.
        Also:
U+000A  \n
U+000D  \r
U+0009  \t
U+000B  \v
        As UTF-8 sequences:
            09
            0A
            0B
            0D
            20
            C2 A0
            E2 80 80-8B
            E2 80 AF
            E2 81 9F
            E3 80 80
*/
        while(true)
        {
            enum { n = sizeof(unsigned long)>=8 ? 0 : '\t' };
            typedef signed char schar;
            unsigned byte = (unsigned char)*function;
            byte -= n;
            // ^Note: values smaller than n intentionally become
            //        big values here due to integer wrap. The
            //        comparison below thus excludes them, making
            //        the effective range 0x09..0x20 (32-bit)
            //        or 0x00..0x20 (64-bit) within the if-clause.
            if(byte <= (unsigned char)(' '-n))
            {
                unsigned long shifted = 1UL << byte;
                const unsigned long mask = SimpleSpaceMask<n>::mask;
                if(mask & shifted)
                    { ++function; continue; } // \r, \n, \t, \v and space
                break;
            }
            if(likely(byte < 0xC2-n)) break;

            if(byte == 0xC2-n && function[1] == char(0xA0))
                { function += 2; continue; } // U+00A0
            if(byte == 0xE3-n &&
               function[1] == char(0x80) && function[2] == char(0x80))
                { function += 3; continue; } // U+3000
            if(byte == 0xE2-n)
            {
                if(function[1] == char(0x81))
                {
                    if(function[2] != char(0x9F)) break;
                    function += 3; // U+205F
                    continue;
                }
                if(function[1] == char(0x80))
                if(function[2] == char(0xAF) || // U+202F
                   schar(function[2]) <= schar(0x8B) // U+2000..U+200B
                  )
                {
                    function += 3;
                    continue;
                }
            }
            break;
        } // while(true)
    } // SkipSpace(CharPtr& function)
}

// ---------------------------------------------------------------------------
// Return parse error message
// ---------------------------------------------------------------------------
template<typename Value_t>
const char* FunctionParserBase<Value_t>::ErrorMsg() const
{
    return ParseErrorMessage[mData->mParseErrorType];
}

template<typename Value_t>
typename FunctionParserBase<Value_t>::ParseErrorType
FunctionParserBase<Value_t>::GetParseErrorType() const
{
    return mData->mParseErrorType;
}

template<typename Value_t>
int FunctionParserBase<Value_t>::EvalError() const
{
    return mData->mEvalErrorType;
}


// ---------------------------------------------------------------------------
// Parse variables
// ---------------------------------------------------------------------------
template<typename Value_t>
bool FunctionParserBase<Value_t>::ParseVariables
(const std::string& inputVarString)
{
    if(mData->mVariablesString == inputVarString) return true;

    /* Delete existing variables from mNamePtrs */
    for(typename NamePtrsMap<Value_t>::iterator i =
            mData->mNamePtrs.begin();
        i != mData->mNamePtrs.end(); )
    {
        if(i->second.type == NameData<Value_t>::VARIABLE)
        {
            typename NamePtrsMap<Value_t>::iterator j (i);
            ++i;
            mData->mNamePtrs.erase(j);
        }
        else ++i;
    }
    mData->mVariablesString = inputVarString;

    const std::string& vars = mData->mVariablesString;
    const unsigned len = unsigned(vars.size());

    unsigned varNumber = VarBegin;

    const char* beginPtr = vars.c_str();
    const char* finalPtr = beginPtr + len;
    while(beginPtr < finalPtr)
    {
        SkipSpace(beginPtr);
        unsigned nameLength = readIdentifier<Value_t>(beginPtr);
        if(nameLength == 0 || (nameLength & 0x80000000U)) return false;
        const char* endPtr = beginPtr + nameLength;
        SkipSpace(endPtr);
        if(endPtr != finalPtr && *endPtr != ',') return false;

        std::pair<NamePtr, NameData<Value_t> > newName
            (NamePtr(beginPtr, nameLength),
             NameData<Value_t>(NameData<Value_t>::VARIABLE, varNumber++));

        if(!addNewNameData(mData->mNamePtrs, newName, true))
        {
            return false;
        }

        beginPtr = endPtr + 1;
    }

    mData->mVariablesAmount = varNumber - VarBegin;
    return true;
}

// ---------------------------------------------------------------------------
// Parse() public interface functions
// ---------------------------------------------------------------------------
template<typename Value_t>
int FunctionParserBase<Value_t>::Parse(const char* Function,
                                       const std::string& Vars,
                                       bool useDegrees)
{
    CopyOnWrite();

    if(!ParseVariables(Vars))
    {
        mData->mParseErrorType = INVALID_VARS;
        return int(strlen(Function));
    }

    return ParseFunction(Function, useDegrees);
}

template<typename Value_t>
int FunctionParserBase<Value_t>::Parse(const std::string& Function,
                                       const std::string& Vars,
                                       bool useDegrees)
{
    CopyOnWrite();

    if(!ParseVariables(Vars))
    {
        mData->mParseErrorType = INVALID_VARS;
        return int(Function.size());
    }

    return ParseFunction(Function.c_str(), useDegrees);
}


// ---------------------------------------------------------------------------
// Main parsing function
// ---------------------------------------------------------------------------
template<typename Value_t>
int FunctionParserBase<Value_t>::ParseFunction(const char* function,
                                               bool useDegrees)
{
    mData->mUseDegreeConversion = useDegrees;
    mData->mParseErrorType = FP_NO_ERROR;

    mData->mInlineVarNames.clear();
    mData->mByteCode.clear(); mData->mByteCode.reserve(128);
    mData->mImmed.clear(); mData->mImmed.reserve(128);
    mData->mStackSize = mStackPtr = 0;

    mData->mHasByteCodeFlags = false;

    const char* ptr = Compile(function);
    mData->mInlineVarNames.clear();

    if(mData->mHasByteCodeFlags)
    {
        for(unsigned i = unsigned(mData->mByteCode.size()); i-- > 0; )
            mData->mByteCode[i] &= ~FP_ParamGuardMask;
    }

    if(mData->mParseErrorType != FP_NO_ERROR)
        return int(mData->mErrorLocation - function);

    assert(ptr); // Should never be null at this point. It's a bug otherwise.
    if(*ptr)
    {
        if(mData->mDelimiterChar == 0 || *ptr != mData->mDelimiterChar)
            mData->mParseErrorType = EXPECT_OPERATOR;
        return int(ptr - function);
    }

#ifndef FP_USE_THREAD_SAFE_EVAL
    mData->mStack.resize(mData->mStackSize);
#endif

    return -1;
}


//=========================================================================
// Parsing and bytecode compiling functions
//=========================================================================
template<typename Value_t>
inline const char* FunctionParserBase<Value_t>::SetErrorType(ParseErrorType t,
                                                             const char* pos)
{
    mData->mParseErrorType = t;
    mData->mErrorLocation = pos;
    return 0;
}

template<typename Value_t>
inline void FunctionParserBase<Value_t>::incStackPtr()
{
    if(++mStackPtr > mData->mStackSize) ++(mData->mStackSize);
}

namespace
{
    const unsigned char powi_factor_table[128] =
    {
        0,1,0,0,0,0,0,0, 0, 0,0,0,0,0,0,3,/*   0 -  15 */
        0,0,0,0,0,0,0,0, 0, 5,0,3,0,0,3,0,/*  16 -  31 */
        0,0,0,0,0,0,0,3, 0, 0,0,0,0,5,0,0,/*  32 -  47 */
        0,0,5,3,0,0,3,5, 0, 3,0,0,3,0,0,3,/*  48 -  63 */
        0,0,0,0,0,0,0,0, 0, 0,0,3,0,0,3,0,/*  64 -  79 */
        0,9,0,0,0,5,0,3, 0, 0,5,7,0,0,0,5,/*  80 -  95 */
        0,0,0,3,5,0,3,0, 0, 3,0,0,3,0,5,3,/*  96 - 111 */
        0,0,3,5,0,9,0,7, 3,11,0,3,0,5,3,0,/* 112 - 127 */
    };

    inline int get_powi_factor(long abs_int_exponent)
    {
        if(abs_int_exponent >= int(sizeof(powi_factor_table))) return 0;
        return powi_factor_table[abs_int_exponent];
    }

#if 0
    int EstimatePowiComplexity(int abs_int_exponent)
    {
        int cost = 0;
        while(abs_int_exponent > 1)
        {
            int factor = get_powi_factor(abs_int_exponent);
            if(factor)
            {
                cost += EstimatePowiComplexity(factor);
                abs_int_exponent /= factor;
                continue;
            }
            if(!(abs_int_exponent & 1))
            {
                abs_int_exponent /= 2;
                cost += 3; // sqr
            }
            else
            {
                cost += 4; // dup+mul
                abs_int_exponent -= 1;
            }
        }
        return cost;
    }
#endif

    bool IsEligibleIntPowiExponent(long int_exponent)
    {
        if(int_exponent == 0) return false;
        long abs_int_exponent = int_exponent;
    #if 0
        int cost = 0;

        if(abs_int_exponent < 0)
        {
            cost += 11;
            abs_int_exponent = -abs_int_exponent;
        }

        cost += EstimatePowiComplexity(abs_int_exponent);

        return cost < (10*3 + 4*4);
    #else
        if(abs_int_exponent < 0) abs_int_exponent = -abs_int_exponent;

        return (abs_int_exponent >= 1)
            && (abs_int_exponent <= 46 ||
              (abs_int_exponent <= 1024 &&
              (abs_int_exponent & (abs_int_exponent - 1)) == 0));
    #endif
    }

    /* Needed by fp_opcode_add.inc if tracing is enabled */
    template<typename Value_t>
    std::string findName(const NamePtrsMap<Value_t>& nameMap,
                         unsigned index,
                         typename NameData<Value_t>::DataType type)
    {
        for(typename NamePtrsMap<Value_t>::const_iterator
                iter = nameMap.begin();
            iter != nameMap.end();
            ++iter)
        {
            if(iter->second.type == type && iter->second.index == index)
                return std::string(iter->first.name,
                                   iter->first.name + iter->first.nameLength);
        }
        return "?";
    }
}

template<typename Value_t>
inline void FunctionParserBase<Value_t>::AddImmedOpcode(Value_t value)
{
    mData->mImmed.push_back(value);
    mData->mByteCode.push_back(cImmed);
}

template<typename Value_t>
inline void FunctionParserBase<Value_t>::CompilePowi(long abs_int_exponent)
{
    int num_muls=0;
    while(abs_int_exponent > 1)
    {
        long factor = get_powi_factor(abs_int_exponent);
        if(factor)
        {
            CompilePowi(factor);
            abs_int_exponent /= factor;
            continue;
        }
        if(!(abs_int_exponent & 1))
        {
            abs_int_exponent /= 2;
            mData->mByteCode.push_back(cSqr);
            // ^ Don't put AddFunctionOpcode here,
            //   it would slow down a great deal.
        }
        else
        {
            mData->mByteCode.push_back(cDup);
            incStackPtr();
            abs_int_exponent -= 1;
            ++num_muls;
        }
    }
    if(num_muls > 0)
    {
        mData->mByteCode.resize(mData->mByteCode.size()+num_muls, cMul);
        mStackPtr -= num_muls;
    }
}

template<typename Value_t>
inline bool FunctionParserBase<Value_t>::TryCompilePowi(Value_t original_immed)
{
    Value_t changed_immed = original_immed;
    for(int sqrt_count=0; /**/; ++sqrt_count)
    {
        long int_exponent = makeLongInteger(changed_immed);
        if(isLongInteger(changed_immed) &&
           IsEligibleIntPowiExponent(int_exponent))
        {
            long abs_int_exponent = int_exponent;
            if(abs_int_exponent < 0)
                abs_int_exponent = -abs_int_exponent;

            mData->mImmed.pop_back(); mData->mByteCode.pop_back();
            --mStackPtr;
            // ^Though the above is accounted for by the procedure
            // that generates cPow, we need it for correct cFetch
            // indexes in CompilePowi().

            while(sqrt_count > 0)
            {
                int opcode = cSqrt;
                if(sqrt_count == 1 && int_exponent < 0)
                {
                    opcode = cRSqrt;
                    int_exponent = -int_exponent;
                }
                mData->mByteCode.push_back(opcode);
                --sqrt_count;
            }
            if((abs_int_exponent & 1) == 0)
            {
                // This special rule fixes the optimization
                // shortcoming of (-x)^2 with minimal overhead.
                AddFunctionOpcode(cSqr);
                abs_int_exponent >>= 1;
            }
            CompilePowi(abs_int_exponent);
            if(int_exponent < 0) mData->mByteCode.push_back(cInv);
            ++mStackPtr; // Needed because cPow adding will assume this.
            return true;
        }
        if(sqrt_count >= 4) break;
        changed_immed += changed_immed;
    }

    // When we don't know whether x >= 0, we still know that
    // x^y can be safely converted into exp(y * log(x))
    // when y is _not_ integer, because we know that x >= 0.
    // Otherwise either expression will give a NaN.
    if(/*!isInteger(original_immed) ||*/
       IsNeverNegativeValueOpcode(mData->mByteCode[mData->mByteCode.size()-2]))
    {
        mData->mImmed.pop_back();
        mData->mByteCode.pop_back();
        //--mStackPtr; - accounted for by the procedure that generates cPow
        AddFunctionOpcode(cLog);
        AddImmedOpcode(original_immed);
        //incStackPtr(); - this and the next are redundant because...
        AddFunctionOpcode(cMul);
        //--mStackPtr;    - ...because the cImmed was popped earlier.
        AddFunctionOpcode(cExp);
        return true;
    }
    return false;
}

//#include "fpoptimizer/opcodename.hh"
// ^ needed only if FP_TRACE_BYTECODE_OPTIMIZATION() is used

template<typename Value_t>
inline void FunctionParserBase<Value_t>::AddFunctionOpcode(unsigned opcode)
{
#define FP_FLOAT_VERSION 1
#define FP_COMPLEX_VERSION 0
/* Function Parser for C++ v4.5.2   

  NOTE:
  Do not include this file in your project. The fparser.cc file #includes
this file internally and thus you don't need to do anything (other than keep
this file in the same directory as fparser.cc).

  This file contains generated code and is thus not intended to be to
be modified by hand. It was generated by util/bytecoderules_parser, which
is available in the development package.
*/
#define HasInvalidRangesOpcode HasInvalidRangesOpcode<IsComplexType<Value_t>::result>
#define FP_TRACE_BYTECODE_OPTIMIZATION(srcline,from,to,with) \
    /*std::cout << "Changing \"" from "\"\t(line " #srcline ")\n" \
                   "    into \"" to "\"\n" with << std::flush*/
#define FP_TRACE_OPCODENAME(op) \
    (op < VarBegin \
        ? FP_GetOpcodeName(OPCODE(op)) \
        : findName(mData->mNamePtrs,op,NameData<Value_t>::VARIABLE))
#define FP_TRACE_BYTECODE_ADD(opcode) \
    /*std::cout << "Adding opcode: " << FP_TRACE_OPCODENAME(opcode) \
                << ", bytecode length " << data->ByteCode.size() \
                << ", pointer is " << (void*)ByteCodePtr \
                << ", code is " << (data->ByteCode.empty() \
                                       ? (void*)0 \
                                       : (void*)&data->ByteCode[0]) \
                << std::endl*/
#define qH1 " B" mF
#define qG1 gT y*x;
#define qF1 hV 2;qI
#define qE1 <<"," aD
#define qD1 <<"," aB
#define qC1 "cNeg"
#define qB1 wA"," aD
#define qA1 "x[x!=Value_t(0)] "
#define q91 <<"," a8
#define q81 wA"," a1
#define q71 );qW q6
#define q61 "cPow "
#define q51 "cSqrt"
#define q41 "cSqr "
#define q31 " cExp2"
#define q21 "cExp "
#define q11 ){hD wB
#define q01 "cCeil"
#define mZ "cImag"
#define mY "cConj"
#define mX "cDup "
#define mW hO wB
#define mV "cAbs"
#define mU wQ wH" "
#define mT qS w2 wB
#define mS "cFloor"
#define mR "cTan"
#define mQ " cDup"
#define mP "cSin"
#define mO (y hX;
#define mN "[ y+x]"
#define mM hV 2 gC
#define mL " cExp"
#define mK "A " wX
#define mJ "cLess"
#define mI "[-x]" wH
#define mH "cDiv" a7
#define mG "cLog"
#define mF " cDiv"
#define mE " " a6
#define mD " " aF
#define mC "cMin"
#define mB "cMax"
#define mA aY"x "
#define m9 gN wB
#define m8 "x cPow"
#define m7 g1 oG wB
#define m6 (x);gJ
#define m5 "B cSqr"
#define m4 oH dE wB
#define m3 "[y*x]" wH
#define m2 "cGreater"
#define m1 mV" " wL
#define m0 "cNeg "
#define aZ " cAdd"
#define aY "y "
#define aX "B[IsVarOpcode(B)] "
#define aW " cSub"
#define aV gY if(dO wB
#define aU "cInv"
#define aT mX aU
#define aS "cAbsNot"
#define aR "cLessOrEq"
#define aQ "cAdd " q51
#define aP "[y*x] cPow"
#define aO "cCos"
#define aN "cLog2"
#define aM "cCosh"
#define aL "cLog10"
#define aK "B[B==A]"
#define aJ "cNotNot"
#define aI "   " a2
#define aH "cDup" aZ
#define aG "cGreaterOrEq"
#define aF "x" aZ
#define aE "cEqual"
#define aD " " aC
#define aC "A" wY
#define aB " " wU
#define aA " cNeg"
#define a9 " cRDiv"
#define a8 " B" wY
#define a7 " x" wH
#define a6 "cRSub"
#define a5 "A[IsVarOpcode(A)]"
#define a4 "x[x!=Value_t()] "
#define a3 " " a5" "
#define a2 " with" aD
#define a1 " " wG
#define a0 " cNot"
#define wZ "x[x==Value_t()]" wH
#define wY " " wC
#define wX "[x]" wH
#define wW "cNEqual"
#define wV a5 mF
#define wU "x = "<<x
#define wT "x[isInteger(x)] cPow"
#define wS a5 wH
#define wR "x[x!=Value_t(0)]" mF
#define wQ "x[x>Value_t(0)]"
#define wP "B[IsNeverNegativeValueOpcode(B)] "
#define wO "x[x==Value_t(1)] "
#define wN wA"\n"
#define wM <<"\n"
#define wL "x[x==Value_t(0)] "
#define wK "B[IsBinaryOpcode(B)&&!HasInvalidRangesOpcode(B)] " wD
#define wJ "A[IsNeverNegativeValueOpcode(A)] "
#define wI "A[IsVarOpcode(A)&&mData->mByteCode.size()>2] "
#define wH " cMul"
#define wG aY"= "<<y wM
#define wF " x A[IsComparisonOpcode(A)]"
#define wE FP_TRACE_BYTECODE_ADD
#define wD "A[IsBinaryOpcode(A)&&!HasInvalidRangesOpcode(A)] " wZ
#define wC "= "<<FP_TRACE_OPCODENAME
#define wB FP_TRACE_BYTECODE_OPTIMIZATION
#define wA "    with" aB<<
#define w9 qT q6:
#define w8 cEqual
#define w7 Lbd gY
#define w6 Lcb gY
#define w5 opcode
#define w4 B==A){
#define w3 q5 q4
#define w2 cExp:
#define w1 qO A qP
#define w0 qO h2
#define oZ qF g1
#define oY if dC
#define oX fp_pow(
#define oW fp_log(
#define oV 3 gC A
#define oU x==g1 oG
#define oT gX Lml;
#define oS q4 Lbo
#define oR 3 gH
#define oQ cSinh:
#define oP g1 0)
#define oO 0.5)){
#define oN Ldn;qT
#define oM ]==h3){
#define oL qY g8 0
#define oK .size()
#define oJ );qE
#define oI A oJ dU
#define oH g7 A=
#define oG 1)){
#define oF qU hI
#define oE Lbo oF
#define oD qT hM hB
#define oC qL 3]
#define oB :hC qQ oC
#define oA cSub oB d3 hJ
#define o9 q7=-x
#define o8 gX Loi;
#define o7 );qF
#define o6 qE A o7
#define o5 h3 d4 qL
#define o4 fp_log2(
#define o3 ==cSqr){
#define o2 qT cSqr:
#define o1 cGreater
#define o0 Default6
#define dZ Default5
#define dY Default2
#define dX Default1
#define dW ImmedPtr
#define dV gA qZ qC
#define dU h3);
#define dT gC dU
#define dS cNotNot
#define dR fp_log10(
#define dQ cAbs);
#define dP fp_abs(x)
#define dO x>oP){
#define dN mImmed
#define dM qE h3 gX
#define dL qK dJ w3
#define dK cGreaterOrEq
#define dJ =q6;
#define dI qK dJ g6
#define dH Value_t
#define dG q8 2 gH q4
#define dF q0[0]
#define dE qK qR qX
#define dD qK qR IsLogicalOpcode(h2
#define dC (qK==
#define dB hB oY
#define dA qY g8 oG
#define d9 pop_back()
#define d8 q6;q1 h3 gI
#define d7 q8 2 gC
#define d6 hR Lba;
#define d5 Default4 qU
#define d4 :if(
#define d3 qV hS d4 qL
#define d2 h3 gM if
#define d1 IsVarOpcode(
#define d0 mData->
#define hZ ]qR w4
#define hY gX Llq
#define hX ,x gX Lap
#define hW gT y+x;q8
#define hV for qA
#define hU gQ cAbs:
#define hT unsigned
#define hS cAdd
#define hR ,y gX
#define hQ qL 3 hZ
#define hP y=q3-1]qR
#define hO y gO
#define hN qY if(dP
#define hM q6:qC
#define hL :if gF
#define hK qQ h9 hS hL
#define hJ 4 qZ mW(292,aY"cAdd B[IsVarOpcode(B)]" aW mD,mN aZ" B" aW,wA"," a8(B)<<"," a1);q4
#define hI cNeg:
#define hH :qS cDup:
#define hG hS hH hK h1 wB(310,aH" " aH,"[Value_t(4)]" wH,);q4
#define hF (x!=g1
#define hE qL 2]
#define hD B g4 w4
#define hC B=hE qO B)){
#define hB if hF 0)){
#define hA gX Lng;
#define h9 qK qV
#define h8 }break;
#define h7 <dH>()){
#define h6 hR Lap;
#define h5 isEvenInteger(
#define h4 DegreesToRadians(x
#define h3 cMul
#define h2 A)){
#define h1 ]==cDup){
#define h0 hI wB(201,m0 mV,mV,);q4 Lab qU qB
#define gZ 3 h1 wB(311,aH wH" " aH,"cMul [Value_t(4)]" wH,);q4
#define gY qU hM
#define gX );q4
#define gW y,x gX Lba;
#define gV IsUnaryOpcode(
#define gU g6 w5=
#define gT q3-1]=
#define gS gR qR IsAlwaysIntegerOpcode(h2
#define gR ;oH dF
#define gQ )){qQ h9
#define gP break gR qO A gQ
#define gO =q3-1];
#define gN qJ hO
#define gM :qJ qC
#define gL d2(dO
#define gK ]=q6 q9 2 gH
#define gJ return;
#define gI );w5=
#define gH ;qI q5
#define gG qL 2 gK q0-=2;
#define gF (qL 2
#define gE y;hT B;hT
#define gD d0 mByteCode
#define gC ;qI q1
#define gB q9 2 gC h3 gI
#define gA ){if gF
#define g9 oY h3 dV
#define g8 if(x==g1
#define g7 default:
#define g6 q5 q0-=1;
#define g5 if(!q0){q2
#define g4 =hE qR
#define g3 B g4 IsNeverNegativeValueOpcode(B)){
#define g2 &&!HasInvalidRangesOpcode(
#define g1 dH(
#define g0 FP_ReDefinePointers();
#define qZ ]==q6){
#define qY if(q0[0 qZ qC
#define qX IsNeverNegativeValueOpcode(h2
#define qW gD qD
#define qV ){case
#define qU ;case
#define qT }break qU
#define qS qQ dF qV
#define qR ;if(
#define qQ switch(
#define qP )&&gD oK>
#define qO qR d1
#define qN dF w1 2){
#define qM d0 dN.d9;
#define qL q0[-
#define qK qL 1]
#define qJ oY q6){
#define qI tmp-->0;)
#define qH q4 Default0;
#define qG }}qH
#define qF d0 dN qD
#define qE AddFunctionOpcode(
#define qD .push_back(
#define qC x=q7;
#define qB hM wB(132,"x " mV,"[fp_abs(x)]",wN);q4 Lac;
#define qA (hT tmp=
#define q9 ;hV
#define q8 d0 dN.d9 q9
#define q7 q3 0]
#define q6 cImmed
#define q5 gD.d9;
#define q4 goto
#define q3 dW[
#define q2 q4 Laa;}case
#define q1 q5 qE
#define q0 ByteCodePtr
hT*q0;dH*dW;
#define FP_ReDefinePointers() q0=!gD.empty()?&gD[0]+gD oK-1:0;dW=!d0 dN.empty()?&d0 dN[0]+d0 dN oK-1:0;
g0
wE(opcode);
#if(!(FP_COMPLEX_VERSION) && !(FP_FLOAT_VERSION))
dH
x;hT
A;dH
gE
C;hT
D;qQ
w5){TailCall_cAbs:g5
cAbs:qS
h0
oH
dF
qR
qX
wB(393,wJ
mV,"A"
,aI(A)wM);gJ
qG
TailCall_cAdd:g5
hG
Lad;qT
h3
hL]==hS){if(qL
gZ
Lae;}
h8}
q4
dX
qU
d2
gF
h1
wB(313,"cDup"
a7
aZ,"[x+Value_t(1)]"
wH,wN);q4
Laf;}
}
q4
dX
oF
wB(199,qC1
aZ,"cSub"
,);q4
Lag
gY
hK
qZ
mW(127,aY"cAdd"
mD,"[y+x]"
aZ,q81);q4
Lah;qT
cRSub:qQ
hE
d3
3
qZ
mW(298,aY"cAdd"
mE
mD,mN
aZ
mE,q81);q4
Lai;qT
hI
wB(299,m0
a6
mD,"[-x]"
aZ
mE,wN);q4
Laj
qU
q6:mW(297,aY
a6
mD,mN
mE,q81);q4
Lak;qT
oA
Lal;qT
hI
wB(293,m0"B[IsVarOpcode(B)]"
aW
mD,"[-x]"
aZ" B"
aW,wA","
a8(B)wM);q4
Lam
qU
q6:mW(291,aY"B[IsVarOpcode(B)]"
aW
mD,mN" B"
aW,wA","
a8(B)<<","
a1);q4
Lan;}
w9
mW(105,aY
aF,"[y+x]"
,q81);q4
Lao;}
g8)){wB(57,"x[x==Value_t()]"
aZ,,wN);q4
Lap;h8
g7
dX:;A=dF
w0
oY
cRSub
dV
wB(290,"x"
mE
a3"cAdd"
,"[DO_STACKPLUS1] A [x]"
aZ
mE,aI(A)qD1
wM);incStackPtr();--mStackPtr;q4
Laq;}
wB(295,a6
a3"cAdd"
,"[DO_STACKPLUS1] A"
aZ
mE,aI(A)wM);incStackPtr();--mStackPtr;q4
Lba;}
qG
TailCall_cAnd:g5
cAnd
hH
wB(224,mX"cAnd"
,aJ,);q4
Lbb
gY
m9(117,mA"cAnd"
,"[fp_and(x,y)]"
,q81);q4
Lbc;h8}
qH
TailCall_cDiv:g5
cDiv
hH
wB(78,"cDup"
mF,"[Value_t()]"
wH" [Value_t(1)]"
aZ,);q4
w7
if
hF
gQ
hI
wB(125,m0
a4"cDiv"
,"[-x]"
mF,wN);q4
Lbe
qU
q6:mW(103,aY
a4"cDiv"
,"[y/x]"
,q81);q4
Lbf;}
}
g8
oG
wB(56,wO"cDiv"
,,wN);q4
Lap;h8}
qH
TailCall_cEqual:g5
w8:dA
A=dD
wB(421,"A[IsLogicalOpcode(A)] "
wO
aE,"A"
,qB1(A)wM);q4
Lap;}
}
m9(115,mA
aE,"[fp_equal(y,x)]"
,q81);q4
Lbg;}
g8
0
hU
wB(359,m1
aE,"[x] "
aE,wN);q4
Lbh
qU
cSqr:wB(361,q41
wL
aE,"[x] "
aE,wN);q4
Lbh;}
wB(411,wL
aE,"cNot"
,wN);q4
Lbi;qG
TailCall_cGreater:g5
o1:oL
hU
wB(413,m1
m2,aJ,wN);q4
Lbj;m4(417,wJ
wL
m2,"A "
aJ,qB1(A)wM);q4
Lbk;}
}
}
m9(113,mA
m2,"[fp_less(x,y)]"
,q81);q4
Lbl;qG
TailCall_cGreaterOrEq:g5
dK:qY
g8
1
hU
wB(414,mV" "
wO
aG,aJ,wN);q4
Lbj;m4(418,wJ
wO
aG,"A "
aJ,qB1(A)wM);q4
Lbk;}
}
}
m9(114,mA
aG,"[fp_lessOrEq(x,y)]"
,q81);q4
Lbm;qG
TailCall_cInv:g5
cInv:qY
if
hF)){wB(101,a4
aU,"[Value_t(1)/x]"
,wN);q4
Lbn;qG
TailCall_cLess:g5
cLess:oL)){A=dE
wB(301,wJ
wL
mJ,mK,qB1(A)wM);oS;}
}
g8
1
hU
wB(415,mV" "
wO
mJ,"cNot"
,wN);q4
Lbp;m4(419,wJ
wO
mJ,"A"
a0,qB1(A)wM);q4
Lbi;}
}
}
m9(111,mA
mJ,"[fp_less(y,x)]"
,q81);q4
Lbq;qG
TailCall_cLessOrEq:g5
cLessOrEq:oL
hU
wB(416,m1
aR,"cNot"
,wN);q4
Lbp;m4(420,wJ
wL
aR,"A"
a0,qB1(A)wM);q4
Lbi;}
}
}
m9(112,mA
aR,"[fp_lessOrEq(y,x)]"
,q81);q4
Lca;qG
TailCall_cMax:g5
cMax
hH
wB(60,mX
mB,,);q4
w6
m9(141,mA
mB,"[fp_max(x,y)]"
,q81);q4
Lcc;}
gP
cDup:hD
wB(66,aK
mQ
a3
mB,"B"
mQ,aI(A)q91(B)wM);q4
Lcb;qT
cMax:hD
wB(68,aK" "
mB
a3
mB,"B "
mB,aI(A)q91(B)wM);q4
Lcb;h8}
qG
TailCall_cMin:g5
cMin
hH
wB(59,mX
mC,,);q4
w6
m9(140,mA
mC,"[fp_min(x,y)]"
,q81);q4
Lcd;}
gP
cDup:hD
wB(65,aK
mQ
a3
mC,"B"
mQ,aI(A)q91(B)wM);q4
Lcb;qT
cMin:hD
wB(67,aK" "
mC
a3
mC,"B "
mC,aI(A)q91(B)wM);q4
Lcb;h8}
qG
TailCall_cMod:g5
cMod:qY
if
hF)){m9(104,aY
a4"cMod"
,"[fp_mod(y,x)]"
,q81);q4
Lce;}
qG
TailCall_cMul:g5
h3
hH
wB(202,"cDup"
wH,"cSqr"
,);q4
Lcf
oF
qQ
h9
cDup:wB(467,"cDup"
aA
wH,"cSqr"
aA,);q4
Lcg;oH
qK
qO
A)gA
oM
B=hQ
wB(473,aK
wH
a3
qC1
wH,m5
wH
aA,aI(A)q91(B)wM);q4
Lch;}
}
}
}
q4
dY
qU
cPow
gM
if
gF
h1
wB(314,mX
m8
wH,"[x+Value_t(1)] cPow"
,wN);q4
Lci;}
}
q4
dY
gY
g8
gQ
h3:A=hE
w0
wB(93,wS" "
wZ,wX,qB1(A)wM);q4
Lcj;}
q4
Default3;g7
Default3:;A=qK
qR
IsBinaryOpcode(A)g2
h2
qQ
hE
qV
q6:mW(92,aY
wD,wX,qB1(A)<<","
a1);q4
Lck;g7
B
g4
IsBinaryOpcode(B)g2
B)){qQ
oC
qV
q6:mW(96,aY
wK,mK,qB1(A)q91(B)<<","
a1);q4
Lcl;g7
C=oC
qO
C)){wB(94,"C[IsVarOpcode(C)] "
wK,mK,qB1(A)q91(B)<<", C"
wY(C)wM);q4
Lcm;}
if(gV
C)g2
C)){wB(95,"C[IsUnaryOpcode(C)&&!HasInvalidRangesOpcode(C)] "
wK,"B "
mK,qB1(A)q91(B)<<", C"
wY(C)wM);q4
Lcn;}
}
}
if(d1
B)){wB(90,aX
wD,wX,qB1(A)q91(B)wM);q4
Lcj;}
if(gV
B)g2
B)){wB(91,"B[IsUnaryOpcode(B)&&!HasInvalidRangesOpcode(B)] "
wD,mK,qB1(A)q91(B)wM);q4
Lco;}
}
}
if(d1
h2
wB(88,a5" "
wZ,"[x]"
,qB1(A)wM);q4
Lcp;}
if(gV
A)g2
h2
wB(89,"A[IsUnaryOpcode(A)&&!HasInvalidRangesOpcode(A)] "
wZ,wX,qB1(A)wM);q4
Lcq;}
}
}
qQ
h9
hS:qQ
hE
qV
cDup:wB(317,aH
a7,"[x+x]"
wH,wN);q4
Lda
qU
o5
3
qZ
hO
A=qL
4]w0
wB(386,a5" y"
wH
aZ
a7,wX" A "
m3
aZ,wA", "
aY"= "
<<y
qE1(A)wM);q4
Ldb;}
w9
mW(385,aY"cAdd"
a7,wX" [y*x]"
aZ,q81);q4
Ldc;qT
h3:qQ
hE
d3
3
h1
wB(319,aH
wH
a7,"cMul [x+x]"
wH,wN);q4
Ldd;w9
hP
y*oU
wB(70,"y[y*x==Value_t(1)]"
wH
a7,,q81);q4
Lde;}
wB(128,"y"
wH
a7,m3,q81);q4
Ldf;qT
hI
wB(122,qC1
a7,mI,wN);q4
Ldg
qU
cSub
hL
oM
if(qL
3
qZ
hO
A=qL
4]w0
wB(387,a5" y"
wH
aW
a7,wX" A "
m3
aW,wA", "
aY"= "
<<y
qE1(A)wM);q4
Ldh;}
}
w9
mW(102,"y"
a7,"[y*x]"
,q81);q4
Ldi;}
g8
oG
wB(55,"x[x==Value_t(1)]"
wH,,wN);q4
Lap;}
g8-oG
wB(124,"x[x==Value_t(-1)]"
wH,qC1,wN);q4
Ldj;}
g8
2)){wB(198,"x[x==Value_t(2)]"
wH,aH,wN);q4
Ldk;h8
g7
dY:;A=dF
qO
A
gQ
h3:qQ
hE
qV
hI
B=hQ
wB(470,aK
aA
wH" "
wS,m5
wH
aA,aI(A)q91(B)wM);q4
Lch;}
q4
Default4;g7
Default4:;hD
wB(461,aK
wH" "
wS,m5
wH,aI(A)q91(B)wM);q4
Ldl;}
}
q4
dZ
oF
hD
wB(464,aK
aA" "
wS,m5
aA,aI(A)q91(B)wM);q4
Lcg;}
q4
dZ;g7
dZ:;B=qK
qR
w4
wB(458,aK" "
wS,m5,aI(A)q91(B)wM);q4
Lcf;}
}
}
if(gV
h2
B=qK
qO
B
qP
1
gA
oM
C=oC
qR
C==A){D=qL
4]qR
D==B){wB(477,"D[D==B] C[C==A]"
wH" B[IsVarOpcode(B)&&mData->mByteCode.size()>1] A[IsUnaryOpcode(A)]"
wH,"D C cSqr"
wH,aI(A)q91(B)<<", C"
wY(C)<<", D"
wY(D)wM);q4
Ldm;}
}
}
}
qG
TailCall_cNEqual:g5
cNEqual:dA
A=dD
wB(422,"A[IsLogicalOpcode(A)] "
wO
wW,"A"
a0,qB1(A)wM);q4
Lbi;}
}
m9(116,mA
wW,"[fp_nequal(y,x)]"
,q81);q4
Ldn;}
g8
0
hU
wB(360,m1
wW,"[x] "
wW,wN);q4
Ldo
qU
cSqr:wB(362,q41
wL
wW,"[x] "
wW,wN);q4
Ldo;}
wB(412,wL
wW,aJ,wN);q4
Lbk;qG
TailCall_cNeg:g5
hI
qS
h3
gM
wB(123,"x"
wH
aA,mI,wN);q4
Ldp;qT
hI
wB(61,qC1
aA,,);q4
w6
wB(100,"x"
aA,"[-x]"
,wN);q4
Ldq;}
qH
TailCall_cNot:g5
cNot:qS
cAbs:wB(227,mV
a0,"cNot"
,);q4
Lea
qU
cAbsNot:A=dD
wB(389,"A[IsLogicalOpcode(A)] "
aS
a0,"A"
,aI(A)wM);q4
Lcb;}
if(A!=q6){wB(390,"A[A!=cImmed] "
aS
a0,"A cAbsNotNot"
,aI(A)wM);q4
Leb;}
q4
o0
qU
cAbsNotNot:wB(231,"cAbsNotNot"
a0,aS,);q4
Lec
qU
hS
gM
wB(424,aF
a0,"[-x] "
aE,wN);q4
Led;}
q4
o0
qU
w8:wB(220,aE
a0,wW,);q4
Lee
qU
o1:wB(218,m2
a0,aR,);q4
Lef
qU
dK:wB(219,aG
a0,mJ,);q4
Leg
qU
cLess:wB(216,mJ
a0,aG,);q4
Leh
qU
cLessOrEq:wB(217,aR
a0,m2,);q4
Lei
qU
cNEqual:wB(221,wW
a0,aE,);q4
Lej
oF
wB(226,qC1
a0,"cNot"
,);q4
Lea
qU
cNot:wB(229,"cNot"
a0,aJ,);q4
Lbb
qU
dS:wB(230,aJ
a0,"cNot"
,);q4
Lea
gY
wB(107,"x"
a0,"[fp_not(x)]"
,wN);q4
Lek;g7
o0:;A=dF
qR
qX
wB(391,wJ"cNot"
,"A "
aS,aI(A)wM);q4
Lel;qG
TailCall_cNotNot:g5
dS:qS
hS
gM
wB(423,aF" "
aJ,"[-x] "
wW,wN);q4
Lem;qT
cNot:wB(232,"cNot "
aJ,"cNot"
,);gJ}
qH
TailCall_cOr:g5
cOr
hH
wB(223,mX"cOr"
,aJ,);q4
Lbb
gY
m9(118,mA"cOr"
,"[fp_or(x,y)]"
,q81);q4
Len;h8}
qH
TailCall_cRDiv:g5
cRDiv:dA
wB(268,wO"cRDiv"
,aU,wN);q4
Leo;qG
TailCall_cRSub:g5
cRSub
d4
q0[0
h1
wB(77,"cDup"
mE,"[Value_t()]"
wH,);q4
Lep;}
qH
TailCall_cSqr:g5
cSqr:qS
cAbs:wB(204,mV" cSqr"
,"cSqr"
,);q4
Leq
oF
wB(203,m0"cSqr"
,"cSqr"
,);q4
Leq;}
qH
TailCall_cSub:g5
cSub
hH
wB(76,"cDup"
aW,"[Value_t()]"
wH,);q4
Lep
oF
wB(200,qC1
aW,"cAdd"
,);q4
Lfa
gY
g8)){wB(58,"x[x==Value_t()]"
aW,,wN);q4
Lap;}
m9(106,aY"x"
aW,"[y-x]"
,q81);q4
Lfb;}
wB(51,"x"
aW,"[-x]"
aZ,wN);q4
Lfc
gR
w0
oY
cRSub
dV
wB(289,"x"
mE
a3"cSub"
,"A"
aZ" [x]"
mE,aI(A)qD1
wM);q4
Lfd;}
wB(296,a6
a3"cSub"
,"[DO_STACKPLUS1] A"
aW
mE,aI(A)wM);incStackPtr();--mStackPtr;q4
Lfe;}
qG
g7
Default0:;A=w5
qR
IsComparisonOpcode(h2
qY
hK
qZ
mW(364,aY"cAdd"
wF,"[x-y] A"
,aI(A)qD1<<","
a1);q4
Lff;qT
hI
wB(365,qC1
wF,"[-x] {OppositeComparisonOpcode(A)}"
,aI(A)qD1
wM);q4
Lfg;}
}
}
if(d1
A
qP
0){B=q0[0
hZ
wB(475,aK" A[IsVarOpcode(A)&&mData->mByteCode.size()>0]"
,"B"
mQ,aI(A)q91(B)wM);q4
Lfh;}
}
if(gV
h2
B=dF
qO
B
qP
1){C=qK
qR
C==A){D
g4
D==B){wB(476,"D[D==B] C[C==A] B[IsVarOpcode(B)&&mData->mByteCode.size()>1] A[IsUnaryOpcode(A)]"
,"D C"
mQ,aI(A)q91(B)<<", C"
wY(C)<<", D"
wY(D)wM);q4
Lfi;}
}
}
}
}
q4
Laa;Laa:qW
w5);gJ
Lab:g6
wE(cAbs);q4
TailCall_cAbs;Lac:q7=dP;gJ
Lad:oZ
4));gG
Lfj:w5=h3;Lfk:g0
Lfl:wE(cMul);q4
TailCall_cMul;Lae:hV
4
dT
oZ
4)q71
gX
Lfj;Laf:q7=x+g1
1);gG
Lbo:w5=h3;q4
Lfl;Lag:gU
cSub;Lfm:wE(cSub);q4
TailCall_cSub;Lah:hW
2
gH
Lfn:g0
Lfo:wE(cAdd);q4
TailCall_cAdd;Lai:hW
oR
Lfp:qE
hS);Lfq:w5=cRSub;g0
wE(cRSub);q4
TailCall_cRSub;Laj:o9;qL
2
gK
q4
Lfp;Lak:hW
2
gH
q4
Lfq;Lal:hW
4
gH
Lga:qE
hS);Lgb:qE
B);Lgc:w5=cSub;g0
q4
Lfm;Lam:o9;oC=q6
q9
oR
q4
Lga;Lan:hW
oR
q4
Lgb;Lao:gT
y+x;Lap:qM
Lcb:q5
gJ
Laq:q8
oV
o7
x
q71
gX
Lfp;Lba:mM
A
gX
Lfp;Lbb:gU
dS;Lgd:wE(cNotNot);q4
TailCall_cNotNot;Lbc:gT
fp_and(x
h6
Lbd:oZ));dF
dJ
qE
dU
oZ
1));Lge:qW
q6);Lgf:w5=hS;q4
Lfn;Lbe:o9;dI
wE(cDiv);q4
TailCall_cDiv;Lbf:gT
y/x;q4
Lap;Lbg:gT
fp_equal
mO
Lbh:dI
Lgg:wE(cEqual);q4
TailCall_cEqual;Lbi:qM
q5
Lgh:w5=cNot;g0
Lgi:wE(cNot);q4
TailCall_cNot;Lbj:q8
2
gH
Lgj:w5=dS;g0
q4
Lgd;Lbk:qM
w3
Lgj;Lbl:gT
fp_less(x
h6
Lbm:gT
fp_lessOrEq(x
h6
Lbn:q7=g1
1)/x;gJ
Lbp:dG
Lgh;Lbq:gT
fp_less
mO
Lca:gT
fp_lessOrEq
mO
Lcc:gT
fp_max(x
h6
Lcd:gT
fp_min(x
h6
Lce:gT
fp_mod
mO
Lcf:gU
cSqr;Lgk:wE(cSqr);q4
TailCall_cSqr;Lcg:mM
cSqr);Lgl:w5=cNeg;g0
wE(cNeg);q4
TailCall_cNeg;Lch:hV
3
gC
cSqr);dM
Lgl;Lci:q7=x+g1
1);hE=q6
q9
2
gC
cPow);gJ
Lcj:gG
q4
Lfl;Lck:gT
x;Lgm:dG
Lfk;Lcl:qF1
qM
Lgn:hV
4
gH
Lgo:o6
x);Lgp:qW
q6
gX
Lfk;Lcm:qM
q4
Lgn;Lcn:q8
4
gC
B
gX
Lgo;Lco:q8
oR
q4
Lgo;Lcp:qK
dJ
q4
Lcb;Lcq:dI
q4
Lfl;Lda:q7=x+x;q4
Lcj;Ldb:gT
x;qL
4]dJ
q8
4
dT
o6
y*x
q71);dM
Lgf;Ldc:gT
x;d7
dU
qF
y*x
gX
Lge;Ldd:q8
4
dT
qF
x+x
gX
Lgp;Lde:qF1
q8
oR
gJ
Ldf:qG1
q4
Lgm;Ldg:o9;q4
Lcq;Ldh:gT
x;qL
4]dJ
q8
4
dT
o6
y*x
q71);dM
Lgc;Ldi:qG1
q4
Lap;Ldj:qM
w3
Lgl;Ldk:dF=cDup;dW-=1;qM
Lgq:w5=hS;q4
Lfo;Ldl:hV
2
gH
Lha:qE
cSqr
gX
Lfk;Ldm:hV
oR
q4
Lha;Ldn:gT
fp_nequal
mO
Ldo:dI
Lhb:wE(cNEqual);q4
TailCall_cNEqual;Ldp:o9;g6
oS;Ldq:o9;gJ
Lea:g6
q4
Lgi;Leb:q1
cAbsNotNot);gJ
Lec:q5
Lel:qE
cAbsNot);gJ
Led:o9;Lej:gU
w8;q4
Lgg;Lee:gU
cNEqual;q4
Lhb;Lef:gU
cLessOrEq;wE(cLessOrEq);q4
TailCall_cLessOrEq;Leg:gU
cLess;wE(cLess);q4
TailCall_cLess;Leh:gU
dK;wE(cGreaterOrEq);q4
TailCall_cGreaterOrEq;Lei:gU
o1;wE(cGreater);q4
TailCall_cGreater;Lek:q7=fp_not
m6
Lem:o9;q4
Lee;Len:gT
fp_or(x
h6
Leo:qM
q5
w5=cInv;g0
wE(cInv);q4
TailCall_cInv;Lep:oZ));dF
dJ
q4
Lfj;Leq:g6
q4
Lgk;Lfa:g6
q4
Lgq;Lfb:gT
y-x;q4
Lap;Lfc:o9;q4
Lgq;Lfd:q8
oV
oJ
hS
o7
x
q71
gX
Lfq;Lfe:mM
A
oJ
cSub
gX
Lfq;Lff:gT
x-y;d7
A);gJ
Lfg:o9;qK
dJ
q1
OppositeComparisonOpcode(A));gJ
Lfh:qW
cDup);gJ
Lfi:dF=cDup;gJ
gJ
q4
TailCall_cAnd;q4
TailCall_cMax;q4
TailCall_cMin;q4
TailCall_cMod;q4
TailCall_cNeg;q4
TailCall_cOr;q4
TailCall_cRDiv;q4
TailCall_cSub;
#endif
#if((FP_COMPLEX_VERSION) && !(FP_FLOAT_VERSION))
dH
x;dH
gE
A;hT
C;hT
D;qQ
w5){TailCall_cAbs:g5
cAbs:qS
h0}
qH
TailCall_cAdd:g5
hG
Lad;qT
h3
hL]==hS){if(qL
gZ
Lae;}
h8}
q4
dX
qU
d2
gF
h1
wB(313,"cDup"
a7
aZ,"[x+Value_t(1)]"
wH,wN);q4
Laf;}
}
q4
dX
oF
wB(199,qC1
aZ,"cSub"
,);q4
Lag
gY
hK
qZ
mW(127,aY"cAdd"
mD,"[y+x]"
aZ,q81);q4
Lah;qT
cRSub:qQ
hE
d3
3
qZ
mW(298,aY"cAdd"
mE
mD,mN
aZ
mE,q81);q4
Lai;qT
hI
wB(299,m0
a6
mD,"[-x]"
aZ
mE,wN);q4
Laj
qU
q6:mW(297,aY
a6
mD,mN
mE,q81);q4
Lak;qT
oA
Lal;qT
hI
wB(293,m0"B[IsVarOpcode(B)]"
aW
mD,"[-x]"
aZ" B"
aW,wA","
a8(B)wM);q4
Lam
qU
q6:mW(291,aY"B[IsVarOpcode(B)]"
aW
mD,mN" B"
aW,wA","
a8(B)<<","
a1);q4
Lan;}
w9
mW(105,aY
aF,"[y+x]"
,q81);q4
Lao;}
g8)){wB(57,"x[x==Value_t()]"
aZ,,wN);q4
Lap;h8
g7
dX:;A=dF
w0
oY
cRSub
dV
wB(290,"x"
mE
a3"cAdd"
,"[DO_STACKPLUS1] A [x]"
aZ
mE,aI(A)qD1
wM);incStackPtr();--mStackPtr;q4
Laq;}
wB(295,a6
a3"cAdd"
,"[DO_STACKPLUS1] A"
aZ
mE,aI(A)wM);incStackPtr();--mStackPtr;q4
Lba;}
qG
TailCall_cAnd:g5
cAnd
hH
wB(224,mX"cAnd"
,aJ,);q4
Lbb
gY
m9(117,mA"cAnd"
,"[fp_and(x,y)]"
,q81);q4
Lbc;h8}
qH
TailCall_cConj:g5
cConj:qS
cConj:wB(63,mY" "
mY,,);q4
w7
wB(193,"x "
mY,"[fp_conj(x)]"
,wN);q4
Lbe;}
qH
TailCall_cDiv:g5
cDiv
hH
wB(78,"cDup"
mF,"[Value_t()]"
wH" [Value_t(1)]"
aZ,);q4
Lbf
gY
if
hF
gQ
hI
wB(125,m0
a4"cDiv"
,"[-x]"
mF,wN);q4
Lbg
qU
q6:mW(103,aY
a4"cDiv"
,"[y/x]"
,q81);q4
Lbh;}
}
g8
oG
wB(56,wO"cDiv"
,,wN);q4
Lap;h8}
qH
TailCall_cEqual:g5
w8:dA
A=dD
wB(421,"A[IsLogicalOpcode(A)] "
wO
aE,"A"
,qB1(A)wM);q4
Lap;}
}
m9(115,mA
aE,"[fp_equal(y,x)]"
,q81);q4
Lbi;}
g8
0
hU
wB(359,m1
aE,"[x] "
aE,wN);q4
Lbj
qU
cSqr:wB(361,q41
wL
aE,"[x] "
aE,wN);q4
Lbj;}
wB(411,wL
aE,"cNot"
,wN);q4
Lbk;qG
TailCall_cGreater:g5
o1:qY
m9(113,mA
m2,"[fp_less(x,y)]"
,q81);q4
Lbl;qG
TailCall_cGreaterOrEq:g5
dK:qY
m9(114,mA
aG,"[fp_lessOrEq(x,y)]"
,q81);q4
Lbm;qG
TailCall_cImag:g5
cImag:qS
cAbs:wB(81,mV" "
mZ,"[Value_t()]"
wH,);q4
Lbn
qU
cReal:wB(80,"cReal "
mZ,"[Value_t()]"
wH,);q4
Lbn
gY
wB(192,"x "
mZ,"[fp_imag(x)]"
,wN);oS;}
qH
TailCall_cInv:g5
cInv:qY
if
hF)){wB(101,a4
aU,"[Value_t(1)/x]"
,wN);q4
Lbp;qG
TailCall_cLess:g5
cLess:oL)){A=dE
wB(301,wJ
wL
mJ,mK,qB1(A)wM);q4
Lbq;}
}
m9(111,mA
mJ,"[fp_less(y,x)]"
,q81);q4
Lca;qG
TailCall_cLessOrEq:g5
cLessOrEq:qY
m9(112,mA
aR,"[fp_lessOrEq(y,x)]"
,q81);q4
Lcb;qG
TailCall_cMax:g5
cMax
hH
wB(60,mX
mB,,);q4
w7
m9(141,mA
mB,"[fp_max(x,y)]"
,q81);q4
Lcc;}
gP
cDup:hD
wB(66,aK
mQ
a3
mB,"B"
mQ,aI(A)q91(B)wM);q4
Lbd;qT
cMax:hD
wB(68,aK" "
mB
a3
mB,"B "
mB,aI(A)q91(B)wM);q4
Lbd;h8}
qG
TailCall_cMin:g5
cMin
hH
wB(59,mX
mC,,);q4
w7
m9(140,mA
mC,"[fp_min(x,y)]"
,q81);q4
Lcd;}
gP
cDup:hD
wB(65,aK
mQ
a3
mC,"B"
mQ,aI(A)q91(B)wM);q4
Lbd;qT
cMin:hD
wB(67,aK" "
mC
a3
mC,"B "
mC,aI(A)q91(B)wM);q4
Lbd;h8}
qG
TailCall_cMod:g5
cMod:qY
if
hF)){m9(104,aY
a4"cMod"
,"[fp_mod(y,x)]"
,q81);q4
Lce;}
qG
TailCall_cMul:g5
h3
hH
wB(202,"cDup"
wH,"cSqr"
,);q4
Lcf
oF
qQ
h9
cDup:wB(467,"cDup"
aA
wH,"cSqr"
aA,);q4
Lcg;oH
qK
qO
A)gA
oM
B=hQ
wB(473,aK
wH
a3
qC1
wH,m5
wH
aA,aI(A)q91(B)wM);q4
Lch;}
}
}
}
q4
dY
qU
cPow
gM
if
gF
h1
wB(314,mX
m8
wH,"[x+Value_t(1)] cPow"
,wN);q4
Lci;}
}
q4
dY
gY
g8
gQ
h3:A=hE
w0
wB(93,wS" "
wZ,wX,qB1(A)wM);q4
Lcj;}
q4
Default3;g7
Default3:;A=qK
qR
IsBinaryOpcode(A)g2
h2
qQ
hE
qV
q6:mW(92,aY
wD,wX,qB1(A)<<","
a1);q4
Lck;g7
B
g4
IsBinaryOpcode(B)g2
B)){qQ
oC
qV
q6:mW(96,aY
wK,mK,qB1(A)q91(B)<<","
a1);q4
Lcl;g7
C=oC
qO
C)){wB(94,"C[IsVarOpcode(C)] "
wK,mK,qB1(A)q91(B)<<", C"
wY(C)wM);q4
Lcm;}
if(gV
C)g2
C)){wB(95,"C[IsUnaryOpcode(C)&&!HasInvalidRangesOpcode(C)] "
wK,"B "
mK,qB1(A)q91(B)<<", C"
wY(C)wM);q4
Lcn;}
}
}
if(d1
B)){wB(90,aX
wD,wX,qB1(A)q91(B)wM);q4
Lcj;}
if(gV
B)g2
B)){wB(91,"B[IsUnaryOpcode(B)&&!HasInvalidRangesOpcode(B)] "
wD,mK,qB1(A)q91(B)wM);q4
Lco;}
}
}
if(d1
h2
wB(88,a5" "
wZ,"[x]"
,qB1(A)wM);q4
Lcp;}
if(gV
A)g2
h2
wB(89,"A[IsUnaryOpcode(A)&&!HasInvalidRangesOpcode(A)] "
wZ,wX,qB1(A)wM);q4
Lcq;}
}
}
qQ
h9
hS:qQ
hE
qV
cDup:wB(317,aH
a7,"[x+x]"
wH,wN);q4
Lda
qU
o5
3
qZ
hO
A=qL
4]w0
wB(386,a5" y"
wH
aZ
a7,wX" A "
m3
aZ,wA", "
aY"= "
<<y
qE1(A)wM);q4
Ldb;}
w9
mW(385,aY"cAdd"
a7,wX" [y*x]"
aZ,q81);q4
Ldc;qT
h3:qQ
hE
d3
3
h1
wB(319,aH
wH
a7,"cMul [x+x]"
wH,wN);q4
Ldd;w9
hP
y*oU
wB(70,"y[y*x==Value_t(1)]"
wH
a7,,q81);q4
Lde;}
wB(128,"y"
wH
a7,m3,q81);q4
Ldf;qT
hI
wB(122,qC1
a7,mI,wN);q4
Ldg
qU
cSub
hL
oM
if(qL
3
qZ
hO
A=qL
4]w0
wB(387,a5" y"
wH
aW
a7,wX" A "
m3
aW,wA", "
aY"= "
<<y
qE1(A)wM);q4
Ldh;}
}
w9
mW(102,"y"
a7,"[y*x]"
,q81);q4
Ldi;}
g8
oG
wB(55,"x[x==Value_t(1)]"
wH,,wN);q4
Lap;}
g8-oG
wB(124,"x[x==Value_t(-1)]"
wH,qC1,wN);q4
Ldj;}
g8
2)){wB(198,"x[x==Value_t(2)]"
wH,aH,wN);q4
Ldk;h8
g7
dY:;A=dF
qO
A
gQ
h3:qQ
hE
qV
hI
B=hQ
wB(470,aK
aA
wH" "
wS,m5
wH
aA,aI(A)q91(B)wM);q4
Lch;}
q4
Default4;g7
Default4:;hD
wB(461,aK
wH" "
wS,m5
wH,aI(A)q91(B)wM);q4
Ldl;}
}
q4
dZ
oF
hD
wB(464,aK
aA" "
wS,m5
aA,aI(A)q91(B)wM);q4
Lcg;}
q4
dZ;g7
dZ:;B=qK
qR
w4
wB(458,aK" "
wS,m5,aI(A)q91(B)wM);q4
Lcf;}
}
}
if(gV
h2
B=qK
qO
B
qP
1
gA
oM
C=oC
qR
C==A){D=qL
4]qR
D==B){wB(477,"D[D==B] C[C==A]"
wH" B[IsVarOpcode(B)&&mData->mByteCode.size()>1] A[IsUnaryOpcode(A)]"
wH,"D C cSqr"
wH,aI(A)q91(B)<<", C"
wY(C)<<", D"
wY(D)wM);q4
Ldm;}
}
}
}
qG
TailCall_cNEqual:g5
cNEqual:dA
A=dD
wB(422,"A[IsLogicalOpcode(A)] "
wO
wW,"A"
a0,qB1(A)wM);q4
Lbk;}
}
m9(116,mA
wW,"[fp_nequal(y,x)]"
,q81);q4
Ldn;}
g8
0
hU
wB(360,m1
wW,"[x] "
wW,wN);q4
Ldo
qU
cSqr:wB(362,q41
wL
wW,"[x] "
wW,wN);q4
Ldo;}
wB(412,wL
wW,aJ,wN);q4
Ldp;qG
TailCall_cNeg:g5
hI
qS
h3
gM
wB(123,"x"
wH
aA,mI,wN);q4
Ldq;qT
hI
wB(61,qC1
aA,,);q4
w7
wB(100,"x"
aA,"[-x]"
,wN);q4
Lea;}
qH
TailCall_cNot:g5
cNot:qS
cAbsNotNot:wB(231,"cAbsNotNot"
a0,aS,);q4
Leb
qU
hS
gM
wB(424,aF
a0,"[-x] "
aE,wN);q4
Lec;qT
w8:wB(220,aE
a0,wW,);q4
Led
qU
o1:wB(218,m2
a0,aR,);q4
Lee
qU
dK:wB(219,aG
a0,mJ,);q4
Lef
qU
cLess:wB(216,mJ
a0,aG,);q4
Leg
qU
cLessOrEq:wB(217,aR
a0,m2,);q4
Leh
qU
cNEqual:wB(221,wW
a0,aE,);q4
Lei
qU
cNot:wB(229,"cNot"
a0,aJ,);q4
Lbb
qU
dS:wB(230,aJ
a0,"cNot"
,);q4
Lej
gY
wB(107,"x"
a0,"[fp_not(x)]"
,wN);q4
Lek;}
qH
TailCall_cNotNot:g5
dS:qS
hS
gM
wB(423,aF" "
aJ,"[-x] "
wW,wN);q4
Lel;qT
cNot:wB(232,"cNot "
aJ,"cNot"
,);gJ}
qH
TailCall_cOr:g5
cOr
hH
wB(223,mX"cOr"
,aJ,);q4
Lbb
gY
m9(118,mA"cOr"
,"[fp_or(x,y)]"
,q81);q4
Lem;h8}
qH
TailCall_cRDiv:g5
cRDiv:dA
wB(268,wO"cRDiv"
,aU,wN);q4
Len;qG
TailCall_cRSub:g5
cRSub
d4
q0[0
h1
wB(77,"cDup"
mE,"[Value_t()]"
wH,);q4
Lbn;}
qH
TailCall_cReal:g5
cReal:qY
wB(191,"x cReal"
,"[fp_real(x)]"
,wN);q4
Leo;}
qH
TailCall_cSqr:g5
cSqr:qS
cAbs:wB(204,mV" cSqr"
,"cSqr"
,);q4
Lep
oF
wB(203,m0"cSqr"
,"cSqr"
,);q4
Lep;}
qH
TailCall_cSub:g5
cSub
hH
wB(76,"cDup"
aW,"[Value_t()]"
wH,);q4
Lbn
oF
wB(200,qC1
aW,"cAdd"
,);q4
Leq
gY
g8)){wB(58,"x[x==Value_t()]"
aW,,wN);q4
Lap;}
m9(106,aY"x"
aW,"[y-x]"
,q81);q4
Lfa;}
wB(51,"x"
aW,"[-x]"
aZ,wN);q4
Lfb
gR
w0
oY
cRSub
dV
wB(289,"x"
mE
a3"cSub"
,"A"
aZ" [x]"
mE,aI(A)qD1
wM);q4
Lfc;}
wB(296,a6
a3"cSub"
,"[DO_STACKPLUS1] A"
aW
mE,aI(A)wM);incStackPtr();--mStackPtr;q4
Lfd;}
qG
g7
Default0:;A=w5
w1
0){B=q0[0
hZ
wB(475,aK" A[IsVarOpcode(A)&&mData->mByteCode.size()>0]"
,"B"
mQ,aI(A)q91(B)wM);q4
Lfe;}
}
if(gV
h2
B=dF
qO
B
qP
1){C=qK
qR
C==A){D
g4
D==B){wB(476,"D[D==B] C[C==A] B[IsVarOpcode(B)&&mData->mByteCode.size()>1] A[IsUnaryOpcode(A)]"
,"D C"
mQ,aI(A)q91(B)<<", C"
wY(C)<<", D"
wY(D)wM);q4
Lff;}
}
}
}
}
q4
Laa;Laa:qW
w5);gJ
Lab:g6
wE(cAbs);q4
TailCall_cAbs;Lac:q7=dP;gJ
Lad:oZ
4));gG
Lfg:w5=h3;Lfh:g0
Lfi:wE(cMul);q4
TailCall_cMul;Lae:hV
4
dT
oZ
4)q71
gX
Lfg;Laf:q7=x+g1
1);gG
Lbq:w5=h3;q4
Lfi;Lag:gU
cSub;Lfj:wE(cSub);q4
TailCall_cSub;Lah:hW
2
gH
Lfk:g0
Lfl:wE(cAdd);q4
TailCall_cAdd;Lai:hW
oR
Lfm:qE
hS);Lfn:w5=cRSub;g0
wE(cRSub);q4
TailCall_cRSub;Laj:o9;qL
2
gK
q4
Lfm;Lak:hW
2
gH
q4
Lfn;Lal:hW
4
gH
Lfo:qE
hS);Lfp:qE
B);Lfq:w5=cSub;g0
q4
Lfj;Lam:o9;oC=q6
q9
oR
q4
Lfo;Lan:hW
oR
q4
Lfp;Lao:gT
y+x;Lap:qM
Lbd:q5
gJ
Laq:q8
oV
o7
x
q71
gX
Lfm;Lba:mM
A
gX
Lfm;Lbb:gU
dS;Lga:wE(cNotNot);q4
TailCall_cNotNot;Lbc:gT
fp_and(x
h6
Lbe:q7=fp_conj
m6
Lbf:oZ));dF
dJ
qE
dU
oZ
1));Lgb:qW
q6);Lgc:w5=hS;q4
Lfk;Lbg:o9;dI
wE(cDiv);q4
TailCall_cDiv;Lbh:gT
y/x;q4
Lap;Lbi:gT
fp_equal
mO
Lbj:dI
Lgd:wE(cEqual);q4
TailCall_cEqual;Lbk:qM
q5
w5=cNot;g0
Lge:wE(cNot);q4
TailCall_cNot;Lbl:gT
fp_less(x
h6
Lbm:gT
fp_lessOrEq(x
h6
Lbn:oZ));dF
dJ
q4
Lfg;Lbo:q7=fp_imag
m6
Lbp:q7=g1
1)/x;gJ
Lca:gT
fp_less
mO
Lcb:gT
fp_lessOrEq
mO
Lcc:gT
fp_max(x
h6
Lcd:gT
fp_min(x
h6
Lce:gT
fp_mod
mO
Lcf:gU
cSqr;Lgf:wE(cSqr);q4
TailCall_cSqr;Lcg:mM
cSqr);Lgg:w5=cNeg;g0
wE(cNeg);q4
TailCall_cNeg;Lch:hV
3
gC
cSqr);dM
Lgg;Lci:q7=x+g1
1);hE=q6
q9
2
gC
cPow);gJ
Lcj:gG
q4
Lfi;Lck:gT
x;Lgh:dG
Lfh;Lcl:qF1
qM
Lgi:hV
4
gH
Lgj:o6
x);Lgk:qW
q6
gX
Lfh;Lcm:qM
q4
Lgi;Lcn:q8
4
gC
B
gX
Lgj;Lco:q8
oR
q4
Lgj;Lcp:qK
dJ
q4
Lbd;Lcq:dI
q4
Lfi;Lda:q7=x+x;q4
Lcj;Ldb:gT
x;qL
4]dJ
q8
4
dT
o6
y*x
q71);dM
Lgc;Ldc:gT
x;d7
dU
qF
y*x
gX
Lgb;Ldd:q8
4
dT
qF
x+x
gX
Lgk;Lde:qF1
q8
oR
gJ
Ldf:qG1
q4
Lgh;Ldg:o9;q4
Lcq;Ldh:gT
x;qL
4]dJ
q8
4
dT
o6
y*x
q71);dM
Lfq;Ldi:qG1
q4
Lap;Ldj:qM
w3
Lgg;Ldk:dF=cDup;dW-=1;qM
Lgl:w5=hS;q4
Lfl;Ldl:hV
2
gH
Lgm:qE
cSqr
gX
Lfh;Ldm:hV
oR
q4
Lgm;Ldn:gT
fp_nequal
mO
Ldo:dI
Lgn:wE(cNEqual);q4
TailCall_cNEqual;Ldp:qM
q5
w5=dS;g0
q4
Lga;Ldq:o9;g6
q4
Lbq;Lea:o9;gJ
Leb:q1
cAbsNot);gJ
Lec:o9;Lei:gU
w8;q4
Lgd;Led:gU
cNEqual;q4
Lgn;Lee:gU
cLessOrEq;wE(cLessOrEq);q4
TailCall_cLessOrEq;Lef:gU
cLess;wE(cLess);q4
TailCall_cLess;Leg:gU
dK;wE(cGreaterOrEq);q4
TailCall_cGreaterOrEq;Leh:gU
o1;wE(cGreater);q4
TailCall_cGreater;Lej:g6
q4
Lge;Lek:q7=fp_not
m6
Lel:o9;q4
Led;Lem:gT
fp_or(x
h6
Len:qM
q5
w5=cInv;g0
wE(cInv);q4
TailCall_cInv;Leo:q7=fp_real
m6
Lep:g6
q4
Lgf;Leq:g6
q4
Lgl;Lfa:gT
y-x;q4
Lap;Lfb:o9;q4
Lgl;Lfc:q8
oV
oJ
hS
o7
x
q71
gX
Lfn;Lfd:mM
A
oJ
cSub
gX
Lfn;Lfe:qW
cDup);gJ
Lff:dF=cDup;gJ
gJ
q4
TailCall_cAnd;q4
TailCall_cConj;q4
TailCall_cImag;q4
TailCall_cMax;q4
TailCall_cMin;q4
TailCall_cMod;q4
TailCall_cNeg;q4
TailCall_cOr;q4
TailCall_cRDiv;q4
TailCall_cReal;q4
TailCall_cSub;
#endif
#if((FP_FLOAT_VERSION) && !(FP_COMPLEX_VERSION))
dH
x;hT
A;dH
gE
C;hT
D;qQ
w5){TailCall_cAbs:g5
cAbs:qS
h0
oH
dF
qR
qX
wB(393,wJ
mV,"A"
,aI(A)wM);gJ
qG
TailCall_cAcos:g5
cAcos:hN<=m7(148,"x[fp_abs(x)<=Value_t(1)] cAcos"
,"[fp_acos(x)]"
,wN);q4
Lad;qG
TailCall_cAcosh:g5
cAcosh:qY
if(x>=m7(145,"x[x>=Value_t(1)] cAcosh"
,"[fp_acosh(x)]"
,wN);q4
Lae;qG
TailCall_cAdd:g5
hG
Laf;qT
h3
hL]==hS){if(qL
gZ
Lag;}
h8}
q4
dX
qU
d2
gF
h1
wB(313,"cDup"
a7
aZ,"[x+Value_t(1)]"
wH,wN);q4
Lah;}
}
q4
dX
oF
wB(199,qC1
aZ,"cSub"
,);q4
Lai
gY
hK
qZ
mW(127,aY"cAdd"
mD,"[y+x]"
aZ,q81);q4
Laj;qT
cRSub:qQ
hE
d3
3
qZ
mW(298,aY"cAdd"
mE
mD,mN
aZ
mE,q81);q4
Lak;qT
hI
wB(299,m0
a6
mD,"[-x]"
aZ
mE,wN);q4
Lal
qU
q6:mW(297,aY
a6
mD,mN
mE,q81);q4
Lam;qT
oA
Lan;qT
hI
wB(293,m0"B[IsVarOpcode(B)]"
aW
mD,"[-x]"
aZ" B"
aW,wA","
a8(B)wM);q4
Lao
qU
q6:mW(291,aY"B[IsVarOpcode(B)]"
aW
mD,mN" B"
aW,wA","
a8(B)<<","
a1);q4
Lap;}
w9
mW(105,aY
aF,"[y+x]"
,q81);q4
Laq;}
g8)){wB(57,"x[x==Value_t()]"
aZ,,wN);q4
Lba;h8
g7
dX:;A=dF
w0
oY
cRSub
dV
wB(290,"x"
mE
a3"cAdd"
,"[DO_STACKPLUS1] A [x]"
aZ
mE,aI(A)qD1
wM);incStackPtr();--mStackPtr;q4
Lbb;}
wB(295,a6
a3"cAdd"
,"[DO_STACKPLUS1] A"
aZ
mE,aI(A)wM);incStackPtr();--mStackPtr;q4
Lbc;}
qG
TailCall_cAnd:g5
cAnd
hH
wB(224,mX"cAnd"
,aJ,);q4
w7
m9(117,mA"cAnd"
,"[fp_and(x,y)]"
,q81);q4
Lbe;h8}
qH
TailCall_cAsin:g5
cAsin:hN<=m7(149,"x[fp_abs(x)<=Value_t(1)] cAsin"
,"[fp_asin(x)]"
,wN);q4
Lbf;qG
TailCall_cAsinh:g5
cAsinh:qY
wB(146,"x cAsinh"
,"[fp_asinh(x)]"
,wN);q4
Lbg;}
qH
TailCall_cAtan:g5
cAtan:qY
wB(150,"x cAtan"
,"[fp_atan(x)]"
,wN);q4
Lbh;}
qH
TailCall_cAtan2:g5
cAtan2:qY
m9(139,mA"cAtan2"
,"[fp_atan2(y,x)]"
,q81);q4
Lbi;qG
TailCall_cAtanh:g5
cAtanh:hN<m7(147,"x[fp_abs(x)<Value_t(1)] cAtanh"
,"[fp_atanh(x)]"
,wN);q4
Lbj;qG
TailCall_cCbrt:g5
cCbrt:qY
wB(151,"x cCbrt"
,"[fp_cbrt(x)]"
,wN);q4
Lbk;}
qH
TailCall_cCeil:g5
cCeil:qS
hI
wB(402,m0
q01,mS
aA,);q4
Lbl
gY
wB(135,"x "
q01,"[fp_ceil(x)]"
,wN);q4
Lbm
gS
wB(396,"A[IsAlwaysIntegerOpcode(A)] "
q01,"A"
,aI(A)wM);gJ
qG
TailCall_cCos:g5
cCos:qS
cAbs:wB(235,mV" "
aO,aO,);q4
Lbn
oF
wB(238,m0
aO,aO,);q4
Lbn
gY
wB(152,"x "
aO,"[fp_cos(x)]"
,wN);oS;oH
qN
qQ
h9
cSec:hD
wB(500,aK" cSec "
wI
aO,"B cSec "
aT,aI(A)q91(B)wM);q4
Lbp;qT
cSin:hD
wB(494,aK" "
mP" "
wI
aO,"B cSinCos"
,aI(A)q91(B)wM);q4
Lbq;h8}
qG
TailCall_cCosh:g5
cCosh:qS
cAbs:wB(236,mV" "
aM,aM,);q4
Lca
qU
cAsinh:wB(450,"cAsinh "
aM,"[DO_STACKPLUS1] "
q41"[Value_t(1)] "
aQ,);incStackPtr();--mStackPtr;q4
Lcb
oF
wB(239,m0
aM,aM,);q4
Lca
gY
wB(153,"x "
aM,"[fp_cosh(x)]"
,wN);q4
Lcc;oH
qN
oY
cSinh
q11(507,aK" cSinh "
wI
aM,"B cSinhCosh"
,aI(A)q91(B)wM);q4
Lcd;}
}
qG
TailCall_cCot:g5
cCot:A=qN
oY
cTan
q11(498,aK" "
mR" "
wI"cCot"
,"B "
mR" "
aT,aI(A)q91(B)wM);q4
Lbp;}
qG
TailCall_cCsc:g5
cCsc:A=qN
oY
cSin
q11(496,aK" "
mP" "
wI"cCsc"
,"B "
mP" "
aT,aI(A)q91(B)wM);q4
Lbp;}
qG
TailCall_cDeg:g5
cDeg:qY
wB(133,"x cDeg"
,"[RadiansToDegrees(x)]"
,wN);q4
Lce;}
qH
TailCall_cDiv:g5
cDiv:qS
cCos:wB(250,aO
mF,"cSec"
wH,);q4
Lcf
qU
cCot:wB(254,"cCot"
mF,mR
wH,);q4
Lcg
qU
cCsc:wB(252,"cCsc"
mF,mP
wH,);q4
Lch
qU
cDup:wB(78,"cDup"
mF,"[Value_t()]"
wH" [Value_t(1)]"
aZ,);q4
Lci
qU
w2
wB(408,"cExp"
mF,m0"cExp"
wH,);q4
Lcj
qU
cExp2:wB(409,"cExp2"
mF,m0"cExp2"
wH,);q4
Lck
qU
cInv:wB(213,aU
mF,"cMul"
,);q4
Lcl
qU
cPow:wB(407,"cPow"
mF,m0"cPow"
wH,);q4
Lcm
qU
cSec:wB(253,"cSec"
mF,aO
wH,);q4
Lcn
qU
cSin:wB(249,mP
mF,"cCsc"
wH,);q4
Lco
qU
cSinCos:wB(502,"cSinCos"
mF,mR,);q4
Lcp
qU
cSinhCosh:wB(509,"cSinhCosh"
mF,"cTanh"
,);q4
Lcq
qU
cTan:wB(251,mR
mF,"cCot"
wH,);q4
Lda
gY
if
hF
gQ
hI
wB(125,m0
a4"cDiv"
,"[-x]"
mF,wN);q4
Ldb
qU
q6:mW(103,aY
a4"cDiv"
,"[y/x]"
,q81);q4
Ldc;}
}
g8
oG
wB(56,wO"cDiv"
,,wN);q4
Lba;}
dB
h3
gA
qZ
hP(y/x)==fp_const_rad_to_deg
h7
wB(321,"y[(y/x)==fp_const_rad_to_deg<Value_t>()]"
wH" "
wR,"cDeg"
,q81);q4
Ldd;}
if((y/x)==fp_const_deg_to_rad
h7
wB(322,"y[(y/x)==fp_const_deg_to_rad<Value_t>()]"
wH" "
wR,"cRad"
,q81);q4
Lde;}
wB(323,"y"
wH" "
wR,"[y/x]"
wH,q81);q4
Ldf;}
}
wB(325,wR,"[Value_t(1)/x]"
wH,wN);q4
Ldg;}
gP
cDiv:hC
wB(271,aX"cDiv "
wV,"[DO_STACKPLUS1] B A"
wH
mF,aI(A)q91(B)wM);incStackPtr();--mStackPtr;q4
Ldh;qT
cRDiv:qQ
hE
qV
hM
wB(266,"x"
a9" "
wV,"A"
wH" [x]"
a9,aI(A)qD1
wM);q4
Ldi;g7
hC
wB(265,"B[IsVarOpcode(B)]"
a9" "
wV,"A"
wH" B"
a9,aI(A)q91(B)wM);q4
Ldj;}
h8}
qG
TailCall_cEqual:g5
w8:oL
hU
wB(359,m1
aE,"[x] "
aE,wN);q4
Ldk
qU
cSqr:wB(361,q41
wL
aE,"[x] "
aE,wN);q4
Ldk;}
}
m9(115,mA
aE,"[fp_equal(y,x)]"
,q81);q4
Ldl;qG
TailCall_cExp:g5
w2
qS
hS
gM
wB(404,aF
mL,q21"[fp_exp(x)]"
wH,wN);q4
Ldm;qT
cLog:A=dE
wB(340,wJ
mG
mL,"A"
,aI(A)wM);q4
oN
hM
wB(154,"x"
mL,"[fp_exp(x)]"
,wN);q4
Ldo;}
qH
TailCall_cExp2:g5
cExp2:qS
hS
gM
wB(405,aF
q31,"cExp2 [fp_exp2(x)]"
wH,wN);q4
Ldp;qT
cLog2:A=dE
wB(341,wJ
aN
q31,"A"
,aI(A)wM);q4
oN
hM
wB(155,"x"
q31,"[fp_exp2(x)]"
,wN);q4
Ldq;}
wB(479,"cExp2"
,"[DO_STACKPLUS1] [fp_log(Value_t(2))]"
wH
mL,);incStackPtr();--mStackPtr;q4
Lea;TailCall_cFloor:g5
cFloor:qS
hI
wB(401,m0
mS,q01
aA,);q4
Leb
gY
wB(136,"x "
mS,"[fp_floor(x)]"
,wN);q4
Lec
gS
wB(395,"A[IsAlwaysIntegerOpcode(A)] "
mS,"A"
,aI(A)wM);gJ
qG
TailCall_cGreater:g5
o1:qY
m9(113,mA
m2,"[fp_less(x,y)]"
,q81);q4
Led;}
g8-oO
wB(431,"x[x==Value_t(-0.5)] "
m2,m0
aS,wN);q4
Lee;qG
TailCall_cGreaterOrEq:g5
dK:qY
dB
cAbs){wB(427,mV" x[x!=Value_t(0)] "
aG,"[Value_t(0.5)/x]"
wH" "
aJ,wN);q4
Lef;}
}
m9(114,mA
aG,"[fp_lessOrEq(x,y)]"
,q81);q4
Leg;}
g8
oO
wB(430,"x[x==Value_t(0.5)] "
aG,"cAbsNotNot"
,wN);q4
Leh;qG
TailCall_cHypot:g5
cHypot
d4
dF==cSinCos){wB(84,"cSinCos cHypot"
,"[Value_t()]"
wH" [Value_t(1)]"
aZ,);q4
Lci;}
qH
TailCall_cInt:g5
cInt:qS
hM
wB(137,"x cInt"
,"[fp_int(x)]"
,wN);q4
Lei
gS
wB(397,"A[IsAlwaysIntegerOpcode(A)] cInt"
,"A"
,aI(A)wM);gJ
qG
TailCall_cInv:g5
cInv:qS
cCos:wB(256,aO" "
aU,"cSec"
,);q4
Lej
qU
cCot:wB(260,"cCot "
aU,mR,);q4
Lcp
qU
cCsc:wB(258,"cCsc "
aU,mP,);q4
Lek
qU
cInv:wB(62,aU" "
aU,,);q4
Ldn
qU
cPow:wB(355,q61
aU,m0"cPow"
,);q4
Lel
qU
cSec:wB(259,"cSec "
aU,aO,);q4
Lem
qU
cSin:wB(255,mP" "
aU,"cCsc"
,);q4
Len
qU
cSqrt:wB(206,q51" "
aU,"cRSqrt"
,);q4
Leo
qU
cTan:wB(257,mR" "
aU,"cCot"
,);q4
Lep
gY
if
hF)){wB(101,a4
aU,"[Value_t(1)/x]"
,wN);q4
Leq;h8}
qH
TailCall_cLess:g5
cLess:oL)){A=dE
wB(301,wJ
wL
mJ,mK,qB1(A)wM);q4
Lfa;}
}
dB
cAbs){wB(426,mV" x[x!=Value_t(0)] "
mJ,"[Value_t(0.5)/x]"
wH
a0,wN);q4
Lfb;}
}
m9(111,mA
mJ,"[fp_less(y,x)]"
,q81);q4
Lfc;}
g8
oO
wB(429,"x[x==Value_t(0.5)] "
mJ,aS,wN);q4
Lfd;qG
TailCall_cLessOrEq:g5
cLessOrEq:qY
m9(112,mA
aR,"[fp_lessOrEq(y,x)]"
,q81);q4
Lfe;}
g8-oO
wB(432,"x[x==Value_t(-0.5)] "
aR,m0"cAbsNotNot"
,wN);q4
Lff;qG
TailCall_cLog:g5
cLog:mT(343,q21
mG,,);q4
Ldn
qU
gL
wB(491,mU
mG,mG" [fp_log(x)]"
aZ,wN);q4
Lfg;}
o2
wB(303,q41
mG,mV" "
mG" "
aH,);q4
Lfh
aV(156,wQ" "
mG,"[fp_log(x)]"
,wN);q4
Lfi;h8}
qH
TailCall_cLog10:g5
cLog10:mT(481,q21
aL,"[DO_STACKPLUS1] [fp_log10(fp_const_e<Value_t>())]"
wH,);incStackPtr();--mStackPtr;q4
Lfj
qU
gL
wB(492,mU
aL,aL" [fp_log10(x)]"
aZ,wN);q4
Lfk;}
o2
wB(305,q41
aL,mV" "
aL" "
aH,);q4
Lfl
aV(157,wQ" "
aL,"[fp_log10(x)]"
,wN);q4
Lfm;h8}
qH
TailCall_cLog2:g5
cLog2:mT(480,q21
aN,"[DO_STACKPLUS1] [fp_log2(fp_const_e<Value_t>())]"
wH,);incStackPtr();--mStackPtr;q4
Lfn
qU
cExp2:wB(344,"cExp2 "
aN,,);q4
Ldn
qU
gL
wB(490,mU
aN,aN" [fp_log2(x)]"
aZ,wN);q4
Lfo;}
o2
wB(304,q41
aN,mV" "
aN" "
aH,);q4
Lfp
aV(158,wQ" "
aN,"[fp_log2(x)]"
,wN);q4
Lfq;h8}
qH
TailCall_cMax:g5
cMax
hH
wB(60,mX
mB,,);q4
Ldn
gY
m9(141,mA
mB,"[fp_max(x,y)]"
,q81);q4
Lga;}
gP
cDup:hD
wB(66,aK
mQ
a3
mB,"B"
mQ,aI(A)q91(B)wM);q4
oN
cMax:hD
wB(68,aK" "
mB
a3
mB,"B "
mB,aI(A)q91(B)wM);q4
Ldn;h8}
qG
TailCall_cMin:g5
cMin
hH
wB(59,mX
mC,,);q4
Ldn
gY
m9(140,mA
mC,"[fp_min(x,y)]"
,q81);q4
Lgb;}
gP
cDup:hD
wB(65,aK
mQ
a3
mC,"B"
mQ,aI(A)q91(B)wM);q4
oN
cMin:hD
wB(67,aK" "
mC
a3
mC,"B "
mC,aI(A)q91(B)wM);q4
Ldn;h8}
qG
TailCall_cMod:g5
cMod:qY
if
hF)){m9(104,aY
a4"cMod"
,"[fp_mod(y,x)]"
,q81);q4
Lgc;}
qG
TailCall_cMul:g5
h3:qS
cCsc:A=qK
w1
3
gA]==cCos){B=hQ
wB(508,aK" "
aO" A[IsVarOpcode(A)&&mData->mByteCode.size()>3] cCsc"
wH,"B cCot"
,aI(A)q91(B)wM);q4
Lgd;}
}
}
q4
dY
qU
cDup:wB(202,"cDup"
wH,"cSqr"
,);q4
Lge
qU
cInv:wB(214,aU
wH,"cDiv"
,);q4
Lgf
oF
qQ
h9
cDup:wB(467,"cDup"
aA
wH,"cSqr"
aA,);q4
Lgg;oH
qK
qO
A)gA
oM
B=hQ
wB(473,aK
wH
a3
qC1
wH,m5
wH
aA,aI(A)q91(B)wM);q4
Lgh;}
}
}
}
q4
dY
qU
cPow
gM
if
gF
h1
wB(314,mX
m8
wH,"[x+Value_t(1)] cPow"
,wN);q4
Lgi;}
}
q4
dY
gY
g8
gQ
h3:A=hE
w0
wB(93,wS" "
wZ,wX,qB1(A)wM);q4
Lgj;}
q4
Default3;g7
Default3:;A=qK
qR
IsBinaryOpcode(A)g2
h2
qQ
hE
qV
q6:mW(92,aY
wD,wX,qB1(A)<<","
a1);q4
Lgk;g7
B
g4
IsBinaryOpcode(B)g2
B)){qQ
oC
qV
q6:mW(96,aY
wK,mK,qB1(A)q91(B)<<","
a1);q4
Lgl;g7
C=oC
qO
C)){wB(94,"C[IsVarOpcode(C)] "
wK,mK,qB1(A)q91(B)<<", C"
wY(C)wM);q4
Lgm;}
if(gV
C)g2
C)){wB(95,"C[IsUnaryOpcode(C)&&!HasInvalidRangesOpcode(C)] "
wK,"B "
mK,qB1(A)q91(B)<<", C"
wY(C)wM);q4
Lgn;}
}
}
if(d1
B)){wB(90,aX
wD,wX,qB1(A)q91(B)wM);q4
Lgj;}
if(gV
B)g2
B)){wB(91,"B[IsUnaryOpcode(B)&&!HasInvalidRangesOpcode(B)] "
wD,mK,qB1(A)q91(B)wM);q4
Lgo;}
}
}
if(d1
h2
wB(88,a5" "
wZ,"[x]"
,qB1(A)wM);q4
Lgp;}
if(gV
A)g2
h2
wB(89,"A[IsUnaryOpcode(A)&&!HasInvalidRangesOpcode(A)] "
wZ,wX,qB1(A)wM);q4
Lgq;}
}
}
qQ
h9
hS:qQ
hE
qV
cDup
d4
x+oU
wB(316,"cDup[x+x==Value_t(1)]"
aZ
a7,,wN);q4
Lha;}
wB(317,aH
a7,"[x+x]"
wH,wN);q4
Lhb
qU
o5
3
qZ
hO
A=qL
4]w0
wB(386,a5" y"
wH
aZ
a7,wX" A "
m3
aZ,wA", "
aY"= "
<<y
qE1(A)wM);q4
Lhc;}
w9
mW(385,aY"cAdd"
a7,wX" [y*x]"
aZ,q81);q4
Lhd;qT
cDeg:wB(209,"cDeg"
a7,"[RadiansToDegrees(x)]"
wH,wN);q4
Lhe
qU
cDiv
oB
qV
o5
4
qZ
mW(278,"y"
wH" "
aX
mH,m3
qH1,wA","
a8(B)<<","
a1);q4
Lhf;qT
hI
wB(279,m0
aX
mH,mI
qH1,wA","
a8(B)wM);q4
Lhg
qU
q6:mW(277,aY
aX
mH,"[y*x] B"
mF,wA","
a8(B)<<","
a1);q4
Lhh;}
qT
h3:qQ
hE
d3
3
h1
if(x+oU
wB(318,"cDup[x+x==Value_t(1)]"
aZ
wH
a7,"cMul"
,wN);q4
Lhi;}
wB(319,aH
wH
a7,"cMul [x+x]"
wH,wN);q4
Lhj;w9
hP
y*oU
wB(70,"y[y*x==Value_t(1)]"
wH
a7,,q81);q4
Lhk;}
if((y*x)==fp_const_rad_to_deg
h7
wB(307,"y[(y*x)==fp_const_rad_to_deg<Value_t>()]"
wH
a7,"cDeg"
,q81);q4
Ldd;}
if((y*x)==fp_const_deg_to_rad
h7
wB(308,"y[(y*x)==fp_const_deg_to_rad<Value_t>()]"
wH
a7,"cRad"
,q81);q4
Lde;}
wB(128,"y"
wH
a7,m3,q81);q4
Lhl;qT
hI
wB(122,qC1
a7,mI,wN);q4
Lhm
qU
cRDiv:qQ
hE
qV
o5
3
qZ
mW(285,"y"
wH
a9
a7,m3
a9,q81);q4
Lhn;qT
hI
wB(286,qC1
a9
a7,mI
a9,wN);q4
Lho
qU
q6:mW(284,"y"
a9
a7,"[y*x]"
a9,q81);q4
Lhp;qT
cRad:wB(210,"cRad"
a7,"[DegreesToRadians(x)]"
wH,wN);q4
Lhq
qU
cSub
hL
oM
if(qL
3
qZ
hO
A=qL
4]w0
wB(387,a5" y"
wH
aW
a7,wX" A "
m3
aW,wA", "
aY"= "
<<y
qE1(A)wM);q4
Lia;}
}
w9
mW(102,"y"
a7,"[y*x]"
,q81);q4
Lib;}
g8
oG
wB(55,"x[x==Value_t(1)]"
wH,,wN);q4
Lba;}
g8-oG
wB(124,"x[x==Value_t(-1)]"
wH,qC1,wN);q4
Lic;}
g8
2)){wB(198,"x[x==Value_t(2)]"
wH,aH,wN);q4
Lid;}
if(x==fp_const_rad_to_deg
h7
wB(207,"x[x==fp_const_rad_to_deg<Value_t>()]"
wH,"cDeg"
,wN);q4
Lie;}
if(x==fp_const_deg_to_rad
h7
wB(208,"x[x==fp_const_deg_to_rad<Value_t>()]"
wH,"cRad"
,wN);q4
Lif;h8
g7
dY:;A=dF
qO
A
gQ
cDiv:hC
wB(274,aX"cDiv "
wS,"[DO_STACKPLUS1] A"
wH
qH1,aI(A)q91(B)wM);incStackPtr();--mStackPtr;q4
Lig;}
q4
d5
h3:qQ
hE
qV
hI
B=hQ
wB(470,aK
aA
wH" "
wS,m5
wH
aA,aI(A)q91(B)wM);q4
Lgh;}
q4
dZ;g7
dZ:;hD
wB(461,aK
wH" "
wS,m5
wH,aI(A)q91(B)wM);q4
Lih;}
}
q4
d5
hI
hD
wB(464,aK
aA" "
wS,m5
aA,aI(A)q91(B)wM);q4
Lgg;}
q4
d5
cRDiv
hL
qZ
qC
wB(267,"x"
a9" "
wS,"[DO_STACKPLUS1] "
mK
a9,aI(A)qD1
wM);incStackPtr();--mStackPtr;q4
Lii;}
wB(281,"cRDiv "
wS,"[DO_STACKPLUS1] A"
wH
a9,aI(A)wM);incStackPtr();--mStackPtr;q4
Lij;g7
Default4:;B=qK
qR
w4
wB(458,aK" "
wS,m5,aI(A)q91(B)wM);q4
Lge;}
}
}
if(gV
h2
B=qK
qO
B
qP
1
gA
oM
C=oC
qR
C==A){D=qL
4]qR
D==B){wB(477,"D[D==B] C[C==A]"
wH" B[IsVarOpcode(B)&&mData->mByteCode.size()>1] A[IsUnaryOpcode(A)]"
wH,"D C cSqr"
wH,aI(A)q91(B)<<", C"
wY(C)<<", D"
wY(D)wM);q4
Lik;}
}
}
}
qG
TailCall_cNEqual:g5
cNEqual:oL
hU
wB(360,m1
wW,"[x] "
wW,wN);q4
Lil
qU
cSqr:wB(362,q41
wL
wW,"[x] "
wW,wN);q4
Lil;}
}
m9(116,mA
wW,"[fp_nequal(y,x)]"
,q81);q4
Lim;qG
TailCall_cNeg:g5
hI
qS
h3
gM
wB(123,"x"
wH
aA,mI,wN);q4
Lin;qT
hI
wB(61,qC1
aA,,);q4
Ldn
qU
cSin:g9
wB(244,"x"
wH" "
mP
aA,mI" "
mP,wN);q4
Lio;}
qT
oQ
g9
wB(245,"x"
wH" cSinh"
aA,mI" cSinh"
,wN);q4
Lip;}
qT
cTan:g9
wB(246,"x"
wH" "
mR
aA,mI" "
mR,wN);q4
Liq;}
qT
cTanh:g9
wB(247,"x"
wH" cTanh"
aA,mI" cTanh"
,wN);q4
Lja;}
qT
hM
wB(100,"x"
aA,"[-x]"
,wN);q4
Ljb;}
qH
TailCall_cNot:g5
cNot:qS
cAbs:wB(227,mV
a0,"cNot"
,);q4
Ljc
qU
cAbsNot:A=dD
wB(389,"A[IsLogicalOpcode(A)] "
aS
a0,"A"
,aI(A)wM);q4
Ldn;}
if(A!=q6){wB(390,"A[A!=cImmed] "
aS
a0,"A cAbsNotNot"
,aI(A)wM);q4
Ljd;}
q4
o0
qU
cAbsNotNot:wB(231,"cAbsNotNot"
a0,aS,);q4
Lje
qU
w8:wB(220,aE
a0,wW,);q4
Ljf
qU
o1:wB(218,m2
a0,aR,);q4
Ljg
qU
dK:wB(219,aG
a0,mJ,);q4
Ljh
qU
cLess:wB(216,mJ
a0,aG,);q4
Lji
qU
cLessOrEq:wB(217,aR
a0,m2,);q4
Ljj
qU
cNEqual:wB(221,wW
a0,aE,);q4
Ljk
oF
wB(226,qC1
a0,"cNot"
,);q4
Ljc
qU
cNot:wB(229,"cNot"
a0,aJ,);q4
Lbd
qU
dS:wB(230,aJ
a0,"cNot"
,);q4
Ljc
gY
wB(107,"x"
a0,"[fp_not(x)]"
,wN);q4
Ljl;g7
o0:;A=dF
qR
qX
wB(391,wJ"cNot"
,"A "
aS,aI(A)wM);q4
Ljm;qG
TailCall_cNotNot:g5
dS
d4
dF==cNot){wB(232,"cNot "
aJ,"cNot"
,);gJ}
qH
TailCall_cOr:g5
cOr
hH
wB(223,mX"cOr"
,aJ,);q4
w7
m9(118,mA"cOr"
,"[fp_or(x,y)]"
,q81);q4
Ljn;h8}
qH
TailCall_cPow:g5
cPow:qY
if(!h5
x+x)){oY
cSqr){wB(22,q41"x[!isEvenInteger(x+x)] cPow"
,mV" [x+x] cPow"
,wN);q4
Ljo;}
}
if(isInteger(x
gQ
w2
wB(43,q21
wT,wX
mL,wN);q4
Ljp
qU
cExp2:wB(44,"cExp2 "
wT,wX
q31,wN);q4
Ljq
qU
cPow
hL
qZ
hP!isInteger(y)){wB(42,"y[!isInteger(y)] "
q61
wT,aP,q81);q4
Lka;}
}
wB(45,q61
wT,wX" cPow"
,wN);q4
Lkb;}
}
if(h5
x
hU
wB(434,mV" x[isEvenInteger(x)] cPow"
,"[x] cPow"
,wN);q4
Lkc
qU
h3
hL]==cAbs){wB(435,mV
wH" x[isEvenInteger(x)] cPow"
,"cMul [x] cPow"
,wN);q4
Lkd;h8}
}
g8)){wB(83,"x[x==Value_t()] cPow"
,"[Value_t()]"
wH" [Value_t(1)]"
aZ,wN);q4
Lke;}
g8
oO
wB(332,"x[x==Value_t(0.5)] cPow"
,q51,wN);q4
Lkf;}
g8
1)/g1
3)){wB(333,"x[x==Value_t(1)/Value_t(3)] cPow"
,"cCbrt"
,wN);q4
Lkg;}
g8
1)/g1-3)){wB(334,"x[x==Value_t(1)/Value_t(-3)] cPow"
,"cCbrt "
aU,wN);q4
Lkh;}
g8-oO
wB(335,"x[x==Value_t(-0.5)] cPow"
,"cRSqrt"
,wN);q4
Lki;}
g8-oG
wB(336,"x[x==Value_t(-1)] cPow"
,aU,wN);q4
Lkj;}
qQ
h9
cPow
hL
qZ
hP
h5
y)&&!h5
x*y)){wB(21,"y[isEvenInteger(y)&&!isEvenInteger(x*y)] "
q61
m8,mV" "
aP,q81);q4
Lkk;}
wB(330,aY
q61
m8,aP,q81);q4
Lka;o2
wB(46,q41
m8,"[x+x] cPow"
,wN);q4
Lkl
qU
q6:hP
y!=oP||x>=oP){wB(165,"y[y!=Value_t(0)||x>=Value_t(0)] "
m8,"[fp_pow(y,x)]"
,q81);q4
Lkm;h8}
wB(455,m8,"[DO_POWI]"
,wN)qR
TryCompilePowi(x))gJ}
qH
TailCall_cRDiv:g5
cRDiv:qS
cSinCos:wB(503,"cSinCos"
a9,"cCot"
,);q4
Lep
qU
cSinhCosh:wB(510,"cSinhCosh"
a9,"cTanh "
aU,);q4
Lkn
gY
g8
oG
wB(268,wO"cRDiv"
,aU,wN);q4
Lkj;h8}
qH
TailCall_cRSub:g5
cRSub
d4
q0[0
h1
wB(77,"cDup"
mE,"[Value_t()]"
wH,);q4
Lko;}
qH
TailCall_cRad:g5
cRad:qS
h3
gM
wB(211,"x"
wH" cRad"
,"[DegreesToRadians(x)]"
wH,wN);q4
Lkp;qT
hM
wB(134,"x cRad"
,"[DegreesToRadians(x)]"
,wN);q4
Lkq;}
qH
TailCall_cSec:g5
cSec:A=qN
qQ
h9
cCos:hD
wB(497,aK" "
aO" "
wI"cSec"
,"B "
aO" "
aT,aI(A)q91(B)wM);q4
Lbp;qT
cSin:hD
wB(495,aK" "
mP" "
wI"cSec"
,"B cSinCos "
aU,aI(A)q91(B)wM);q4
Lla;h8
qG
TailCall_cSin:g5
cSin:qS
hI
wB(240,m0
mP,mP
aA,);q4
Llb
gY
wB(159,"x "
mP,"[fp_sin(x)]"
,wN);q4
Llc;oH
qN
oY
cCsc
q11(499,aK" cCsc "
wI
mP,"B cCsc "
aT,aI(A)q91(B)wM);q4
Lbp;}
}
qG
TailCall_cSinh:g5
oQ
qS
cAcosh:wB(437,"cAcosh cSinh"
,"[DO_STACKPLUS1] "
q41"[Value_t(-1)] "
aQ,);incStackPtr();--mStackPtr;q4
Lld
qU
cAsinh:wB(349,"cAsinh cSinh"
,,);q4
Ldn
oF
wB(241,m0"cSinh"
,"cSinh"
aA,);q4
Lle
gY
wB(160,"x cSinh"
,"[fp_sinh(x)]"
,wN);q4
Llf;}
qH
TailCall_cSqr:g5
cSqr:qS
cAbs:wB(204,mV" cSqr"
,"cSqr"
,);q4
Llg
oF
wB(203,m0"cSqr"
,"cSqr"
,);q4
Llg
qU
cSqrt:A=dE
wB(338,wJ
q51" cSqr"
,"A"
,aI(A)wM);q4
Ldn;h8}
qH
TailCall_cSqrt:g5
cSqrt:qS
hS
d4
qK
o3
A=hE
w0
if(oC
o3
wB(512,"cSqr"
a3
q41
aQ,"A cHypot"
,aI(A)wM);q4
Llh;}
}
B
g4
gV
B)){A=oC
w0
if(qL
4]o3
wB(513,"cSqr"
a3"B[IsUnaryOpcode(B)] "
q41
aQ,"A B cHypot"
,"    with"
a8(B)qE1(A)wM);q4
Lli;}
}
}
o2
wB(23,q41
q51,mV,);q4
Llj
gY
if(x>=oP){wB(161,"x[x>=Value_t(0)] "
q51,"[fp_sqrt(x)]"
,wN);q4
Llk;h8}
qH
TailCall_cSub:g5
cSub
hH
wB(76,"cDup"
aW,"[Value_t()]"
wH,);q4
Lko
oF
wB(200,qC1
aW,"cAdd"
,);q4
Lll
gY
g8)){wB(58,"x[x==Value_t()]"
aW,,wN);q4
Lba;}
m9(106,aY"x"
aW,"[y-x]"
,q81);q4
Llm;}
wB(51,"x"
aW,"[-x]"
aZ,wN);q4
Lln
gR
w0
oY
cRSub
dV
wB(289,"x"
mE
a3"cSub"
,"A"
aZ" [x]"
mE,aI(A)qD1
wM);q4
Llo;}
wB(296,a6
a3"cSub"
,"[DO_STACKPLUS1] A"
aW
mE,aI(A)wM);incStackPtr();--mStackPtr;q4
Llp;}
qG
TailCall_cTan:g5
cTan:qS
cAtan2:wB(354,"cAtan2 "
mR,"cDiv"
,);q4
Lgf
oF
wB(242,m0
mR,mR
aA,);q4
Llq
gY
wB(163,"x "
mR,"[fp_tan(x)]"
,wN);q4
Lma;oH
qN
oY
cCot
q11(501,aK" cCot "
wI
mR,"B cCot "
aT,aI(A)q91(B)wM);q4
Lbp;}
}
qG
TailCall_cTanh:g5
cTanh:qS
hI
wB(243,m0"cTanh"
,"cTanh"
aA,);q4
Lmb
gY
wB(164,"x cTanh"
,"[fp_tanh(x)]"
,wN);q4
Lmc;}
qH
TailCall_cTrunc:g5
cTrunc:qS
hM
wB(138,"x cTrunc"
,"[fp_trunc(x)]"
,wN);q4
Lmd
gS
wB(394,"A[IsAlwaysIntegerOpcode(A)] cTrunc"
,"A"
,aI(A)wM);gJ
qG
g7
Default0:;A=w5
qR
IsComparisonOpcode(h2
qY
hK
qZ
mW(364,aY"cAdd"
wF,"[x-y] A"
,aI(A)qD1<<","
a1);q4
Lme;qT
cAtan
d4
dP<fp_const_pi<dH>()*g1
oO
wB(380,"cAtan[fp_abs(x)<fp_const_pi<Value_t>()*Value_t(0.5)]"
wF,"[fp_tan(x)] A"
,aI(A)qD1
wM);q4
Lmf;qT
cExp
d4
dO
wB(370,"cExp[x>Value_t(0)]"
wF,"[fp_log(x)] A"
,aI(A)qD1
wM);q4
Lmg;qT
cExp2
d4
dO
wB(371,"cExp2[x>Value_t(0)]"
wF,"[fp_log2(x)] A"
,aI(A)qD1
wM);q4
Lmh;qT
cLog:g3
wB(373,wP
mG
wF,"B [fp_exp(x)] A"
,aI(A)qD1
q91(B)wM);q4
Lmi;qT
cLog10:g3
wB(375,wP
aL
wF,"B [fp_pow(Value_t(10),x)] A"
,aI(A)qD1
q91(B)wM);q4
Lmj;qT
cLog2:g3
wB(374,wP
aN
wF,"B [fp_exp2(x)] A"
,aI(A)qD1
q91(B)wM);q4
Lmk;qT
h3
hL
qZ
hP
y>oP){wB(366,"y[y>Value_t(0)]"
wH
wF,"[x/y] A"
,aI(A)qD1<<","
a1);q4
Lml;}
if(y<oP){wB(367,"y[y<Value_t(0)]"
wH
wF,"[x/y] {OppositeComparisonOpcode(A)}"
,aI(A)qD1<<","
a1);q4
Lmm;}
qT
hI
wB(365,qC1
wF,"[-x] {OppositeComparisonOpcode(A)}"
,aI(A)qD1
wM);q4
Lmn
qU
cPow
d4
x>oP
gA
qZ
hP
y>oP){wB(368,"y[y>Value_t(0)] cPow[x>Value_t(0)]"
wF,"[fp_pow(x,Value_t(1)/y)] A"
,aI(A)qD1<<","
a1);q4
Lmo;}
}
qT
oQ
wB(381,"cSinh"
wF,"[fp_asinh(x)] A"
,aI(A)qD1
wM);q4
Lmp
qU
cSqr
d4
dO
wB(369,"cSqr[x>Value_t(0)]"
wF,mV" [fp_sqrt(x)] A"
,aI(A)qD1
wM);q4
Lmq;qT
cTanh
d4
dP<m7(382,"cTanh[fp_abs(x)<Value_t(1)]"
wF,"[fp_atanh(x)] A"
,aI(A)qD1
wM);q4
Lna;h8}
}
}
if(d1
A
qP
0){B=q0[0
hZ
wB(475,aK" A[IsVarOpcode(A)&&mData->mByteCode.size()>0]"
,"B"
mQ,aI(A)q91(B)wM);q4
Lnb;}
}
if(gV
h2
B=dF
qO
B
qP
1){C=qK
qR
C==A){D
g4
D==B){wB(476,"D[D==B] C[C==A] B[IsVarOpcode(B)&&mData->mByteCode.size()>1] A[IsUnaryOpcode(A)]"
,"D C"
mQ,aI(A)q91(B)<<", C"
wY(C)<<", D"
wY(D)wM);q4
Lnc;}
}
}
}
C=w5
qR
IsCommutativeOrParamSwappableBinaryOpcode(C)){qS
cSin:A=qK
w1
3
gA]==cCos){B=hQ
wB(505,aK" "
aO" A[IsVarOpcode(A)&&mData->mByteCode.size()>3] "
mP" C[IsCommutativeOrParamSwappableBinaryOpcode(C)]"
,"B cSinCos {GetParamSwappedBinaryOpcode(C)}"
,"    with C"
wY(C)qE1(A)q91(B)wM);q4
Lnd;}
}
qT
oQ
A=qK
w1
3
gA]==cCosh){B=hQ
wB(506,aK" "
aM" A[IsVarOpcode(A)&&mData->mByteCode.size()>3] cSinh C[IsCommutativeOrParamSwappableBinaryOpcode(C)]"
,"B cSinhCosh {GetParamSwappedBinaryOpcode(C)}"
,"    with C"
wY(C)qE1(A)q91(B)wM);q4
Lne;}
}
h8}
}
}
q4
Laa;Laa:qW
w5);gJ
Lab:g6
Lnf:wE(cAbs);q4
TailCall_cAbs;Lac:q7=dP;gJ
Lad:q7=fp_acos
m6
Lae:q7=fp_acosh
m6
Laf:oZ
4));gG
Lng:w5=h3;Lnh:g0
Lni:wE(cMul);q4
TailCall_cMul;Lag:hV
4
dT
oZ
4));Lnj:qW
q6
hA
Lah:q7=x+g1
1);gG
Lfa:w5=h3;q4
Lni;Lai:gU
cSub;Lnk:wE(cSub);q4
TailCall_cSub;Laj:hW
2
gH
Lnl:g0
Lnm:wE(cAdd);q4
TailCall_cAdd;Lak:hW
oR
Lnn:qE
hS);Lno:w5=cRSub;g0
wE(cRSub);q4
TailCall_cRSub;Lal:o9;qL
2
gK
q4
Lnn;Lam:hW
2
gH
q4
Lno;Lan:hW
4
gH
Lnp:qE
hS);Lnq:qE
B);Loa:w5=cSub;g0
q4
Lnk;Lao:o9;oC=q6
q9
oR
q4
Lnp;Lap:hW
oR
q4
Lnq;Laq:gT
y+x;Lba:qM
Ldn:q5
gJ
Lbb:q8
oV
o7
x
q71
gX
Lnn;Lbc:mM
A
gX
Lnn;Lbd:gU
dS;Lob:wE(cNotNot);q4
TailCall_cNotNot;Lbe:gT
fp_and(x
d6
Lbf:q7=fp_asin
m6
Lbg:q7=fp_asinh
m6
Lbh:q7=fp_atan
m6
Lbi:gT
fp_atan2(gW
Lbj:q7=fp_atanh
m6
Lbk:q7=fp_cbrt
m6
Lbl:q1
cFloor);Loc:w5=cNeg;g0
wE(cNeg);q4
TailCall_cNeg;Lbm:q7=fp_ceil
m6
Lbn:g6
Lod:wE(cCos);q4
TailCall_cCos;Lbo:q7=fp_cos
m6
Lbp:dF=cDup;w5=cInv;Loe:wE(cInv);q4
TailCall_cInv;Lbq:mM
cSinCos);gJ
Lca:g6
wE(cCosh);q4
TailCall_cCosh;Lcb:q1
cSqr
o7
g1
1));Lof:qW
q6
oJ
hS);Log:w5=cSqrt;g0
wE(cSqrt);q4
TailCall_cSqrt;Lcc:q7=fp_cosh
m6
Lcd:mM
cSinhCosh);gJ
Lce:q7=RadiansToDegrees
m6
Lcf:q1
cSec
hA
Lcg:q1
cTan
hA
Lch:q1
cSin
hA
Lci:oZ));dF
dJ
Loh:qE
dU
oZ
1));Loi:qW
q6);Loj:w5=hS;q4
Lnl;Lcj:q1
cNeg
oJ
cExp
hA
Lck:q1
cNeg
oJ
cExp2
hA
Lcl:g6
q4
Lfa;Lcm:q1
cNeg
oJ
cPow
hA
Lcn:q1
cCos
hA
Lco:q1
cCsc
hA
Lcp:gU
cTan;Lok:wE(cTan);q4
TailCall_cTan;Lcq:gU
cTanh;Lol:wE(cTanh);q4
TailCall_cTanh;Lda:q1
cCot
hA
Ldb:o9;dI
Lom:wE(cDiv);q4
TailCall_cDiv;Ldc:gT
y/x;q4
Lba;Ldd:qF1
q8
oR
Lon:w5=cDeg;g0
wE(cDeg);q4
TailCall_cDeg;Lde:qF1
q8
oR
Loo:w5=cRad;g0
wE(cRad);q4
TailCall_cRad;Ldf:gT
y/x;dG
Lng;Ldg:q7=g1
1)/x;q4
Lfa;Ldh:mM
oI
Lop:g0
q4
Lom;Ldi:q8
3
gC
oI
qF
x
q71);Loq:w5=cRDiv;g0
wE(cRDiv);q4
TailCall_cRDiv;Ldj:hV
3
gC
oI
qE
B
gX
Loq;Ldk:dI
Lpa:wE(cEqual);q4
TailCall_cEqual;Ldl:gT
fp_equal(gW
Ldm:d7
cExp
o7
fp_exp(x)gX
Lnj;Ldo:q7=fp_exp
m6
Ldp:d7
cExp2
o7
fp_exp2(x)gX
Lnj;Ldq:q7=fp_exp2
m6
Lea:qF
oW
g1
2))q71);Lpb:qE
h3
gI
cExp;g0
wE(cExp);q4
TailCall_cExp;Leb:q1
cCeil
gX
Loc;Lec:q7=fp_floor
m6
Led:gT
fp_less(x
d6
Lee:qM
q1
cNeg);Ljm:qE
cAbsNot);gJ
Lef:q7=g1
0.5)/x;qK=d8
dS;g0
q4
Lob;Leg:gT
fp_lessOrEq(x
d6
Leh:qM
Ljd:q5
Lpc:qE
cAbsNotNot);gJ
Lei:q7=fp_int
m6
Lej:gU
cSec;wE(cSec);q4
TailCall_cSec;Lek:gU
cSin;Lpd:wE(cSin);q4
TailCall_cSin;Lel:q1
cNeg
gI
cPow;Lpe:g0
Lpf:wE(cPow);q4
TailCall_cPow;Lem:gU
cCos;q4
Lod;Len:gU
cCsc;wE(cCsc);q4
TailCall_cCsc;Leo:q1
cRSqrt);gJ
Lep:g6
Lpg:w5=cCot;wE(cCot);q4
TailCall_cCot;Leq:q7=g1
1)/x;gJ
Lfb:q7=g1
0.5)/x;qK=d8
cNot;g0
Lph:wE(cNot);q4
TailCall_cNot;Lfc:gT
fp_less(gW
Lfd:qM
Lje:w3
Ljm;Lfe:gT
fp_lessOrEq(gW
Lff:qM
q1
cNeg
gX
Lpc;Lfg:d7
cLog
o7
oW
x)o8
Lfh:q1
dQ
qE
cLog);Lpi:qW
cDup
gX
Loj;Lfi:q7=oW
x);gJ
Lfj:qF
dR
fp_const_e<dH>()));Lpj:dF
dJ
q4
Lng;Lfk:d7
cLog10
o7
dR
x)o8
Lfl:q1
dQ
qE
cLog10
gX
Lpi;Lfm:q7=dR
x);gJ
Lfn:qF
o4
fp_const_e<dH>())gX
Lpj;Lfo:d7
cLog2
o7
o4
x)o8
Lfp:q1
dQ
qE
cLog2
gX
Lpi;Lfq:q7=o4
x);gJ
Lga:gT
fp_max(x
d6
Lgb:gT
fp_min(x
d6
Lgc:gT
fp_mod(gW
Lgd:hV
oR
q0-=3;q4
Lpg;Lge:gU
cSqr;Lpk:wE(cSqr);q4
TailCall_cSqr;Lgf:gU
cDiv;q4
Lom;Lgg:mM
cSqr
gX
Loc;Lgh:hV
3
gC
cSqr);dM
Loc;Lgi:q7=x+g1
1);gG
w5=cPow;q4
Lpf;Lgj:gG
q4
Lni;Lgk:gT
x;Lpl:dG
Lnh;Lgl:qF1
qM
Lpm:hV
4
gH
Lpn:o6
x);Lpo:qW
q6
gX
Lnh;Lgm:qM
q4
Lpm;Lgn:q8
4
gC
B
gX
Lpn;Lgo:q8
oR
q4
Lpn;Lgp:qK
dJ
q4
Ldn;Lgq:dI
q4
Lni;Lha:qM
Lpp:hV
oR
gJ
Lhb:q7=x+x;q4
Lgj;Lhc:gT
x;qL
4]dJ
q8
4
dT
o6
y*x
q71);dM
Loj;Lhd:gT
x;d7
dU
qF
y*x
o8
Lhe:q7=RadiansToDegrees(x
gX
Lgq;Lhf:qG1
q8
4
gH
Lpq:qE
dU
Lqa:qE
B
gI
cDiv;q4
Lop;Lhg:o9;oC=q6
q9
oR
q4
Lpq;Lhh:qG1
q8
oR
q4
Lqa;Lhi:q8
4
gH
q4
Lnh;Lhj:q8
4
dT
qF
x+x
gX
Lpo;Lhk:qF1
qM
q4
Lpp;Lhl:qG1
q4
Lpl;Lhm:o9;q4
Lgq;Lhn:qG1
q8
oR
Lqb:dM
Loq;Lho:o9;qL
2
gK
q4
Lqb;Lhp:qG1
dG
Loq;Lhq:q7=h4
gX
Lgq;Lia:gT
x;qL
4]dJ
q8
4
dT
o6
y*x
q71);dM
Loa;Lib:qG1
q4
Lba;Lic:qM
w3
Loc;Lid:dF=cDup;dW-=1;qM
Lqc:w5=hS;q4
Lnm;Lie:qM
w3
Lon;Lif:qM
w3
Loo;Lig:hV
oV
gX
Lpq;Lih:hV
2
gH
Lqd:qE
cSqr
gX
Lnh;Lii:q8
oV
o7
x
q71
gX
Lqb;Lij:mM
A
gX
Lqb;Lik:hV
oR
q4
Lqd;Lil:dI
Lqe:wE(cNEqual);q4
TailCall_cNEqual;Lim:gT
fp_nequal(gW
Lin:o9;q4
Lcl;Lio:o9
gB
cSin;g0
q4
Lpd;Lip:o9
gB
cSinh;g0
wE(cSinh);q4
TailCall_cSinh;Liq:o9
gB
cTan;g0
q4
Lok;Lja:o9
gB
cTanh;g0
q4
Lol;Ljb:o9;gJ
Ljc:g6
q4
Lph;Ljf:gU
cNEqual;q4
Lqe;Ljg:gU
cLessOrEq;wE(cLessOrEq);q4
TailCall_cLessOrEq;Ljh:gU
cLess;wE(cLess);q4
TailCall_cLess;Lji:gU
dK;wE(cGreaterOrEq);q4
TailCall_cGreaterOrEq;Ljj:gU
o1;wE(cGreater);q4
TailCall_cGreater;Ljk:gU
w8;q4
Lpa;Ljl:q7=fp_not
m6
Ljn:gT
fp_or(x
d6
Ljo:d7
dQ
qF
x+x);Lqf:qW
q6
gX
Lpe;Ljp:dL
Lpb;Ljq:qK=d8
cExp2;g0
wE(cExp2);q4
TailCall_cExp2;Lka:qG1
dG
Lpe;Lkb:qK
dJ
q1
h3
gX
Lpe;Lkc:dI
q4
Lpf;Lkd:q8
3
dT
qF
x
gX
Lqf;Lke:q7=g1
gX
Loh;Lkf:qM
w3
Log;Lkg:qM
q5
w5=cCbrt;g0
wE(cCbrt);q4
TailCall_cCbrt;Lkh:qM
q1
cCbrt);Lqg:w5=cInv;g0
q4
Loe;Lki:qM
q4
Leo;Lkj:qM
w3
Lqg;Lkk:qF1
q8
3
gC
dQ
qF
y*x
gX
Lqf;Lkl:q7=x+x;q4
Lkc;Lkm:gT
oX
gW
Lkn:q1
cTanh
gX
Lqg;Lko:oZ)gX
Lpj;Lkp:q7=h4
gX
Lcl;Lkq:q7=h4);gJ
Lla:mM
cSinCos
gX
Lqg;Llb:q1
cSin
gX
Loc;Llc:q7=fp_sin
m6
Lld:q1
cSqr
o7
g1-1)gX
Lof;Lle:q1
cSinh
gX
Loc;Llf:q7=fp_sinh
m6
Llg:g6
q4
Lpk;Llh:hV
4
gC
A);Lqh:w5=cHypot;g0
wE(cHypot);q4
TailCall_cHypot;Lli:hV
5
gC
A
oJ
B
gX
Lqh;Llj:gU
cAbs;q4
Lnf;Llk:q7=fp_sqrt
m6
Lll:g6
q4
Lqc;Llm:gT
y-x;q4
Lba;Lln:o9;q4
Lqc;Llo:q8
oV
oJ
hS
o7
x
q71
gX
Lno;Llp:mM
A
oJ
cSub
gX
Lno;Llq:q1
cTan
gX
Loc;Lma:q7=fp_tan
m6
Lmb:q1
cTanh
gX
Loc;Lmc:q7=fp_tanh
m6
Lmd:q7=fp_trunc
m6
Lme:gT
x-y;Lqi:q8
2
gH
Lqj:qE
A);gJ
Lmf:q7=fp_tan(x);Lqk:dL
Lqj;Lmg:q7=oW
x
gX
Lqk;Lmh:q7=o4
x
gX
Lqk;Lmi:q7=fp_exp(x
gX
Lqk;Lmj:q7=oX
g1
10),x
gX
Lqk;Lmk:q7=fp_exp2(x
gX
Lqk;Lml:gT
x/y;q4
Lqi;Lmm:gT
x/y;q8
2
gH
Lql:qE
OppositeComparisonOpcode(A));gJ
Lmn:o9;dL
Lql;Lmo:gT
oX
x,g1
1)/y
gX
Lqi;Lmp:q7=fp_asinh(x
gX
Lqk;Lmq:d7
dQ
qF
fp_sqrt(x)q71
gX
Lqj;Lna:q7=fp_atanh(x
gX
Lqk;Lnb:qW
cDup);gJ
Lnc:dF=cDup;gJ
Lnd:hV
3
gC
cSinCos);Lqm:qE
GetParamSwappedBinaryOpcode(C));gJ
Lne:hV
3
gC
cSinhCosh
gX
Lqm;gJ
q4
TailCall_cAcos;q4
TailCall_cAcosh;q4
TailCall_cAnd;q4
TailCall_cAsin;q4
TailCall_cAsinh;q4
TailCall_cAtan;q4
TailCall_cAtan2;q4
TailCall_cAtanh;q4
TailCall_cCeil;q4
TailCall_cFloor;q4
TailCall_cInt;q4
TailCall_cLog;q4
TailCall_cLog10;q4
TailCall_cLog2;q4
TailCall_cMax;q4
TailCall_cMin;q4
TailCall_cMod;q4
TailCall_cOr;q4
TailCall_cRDiv;q4
TailCall_cRad;q4
TailCall_cSec;q4
TailCall_cSin;q4
TailCall_cSinh;q4
TailCall_cSqrt;q4
TailCall_cSub;q4
TailCall_cTan;q4
TailCall_cTanh;q4
TailCall_cTrunc;
#endif
#if((FP_COMPLEX_VERSION) && (FP_FLOAT_VERSION))
dH
x;dH
gE
A;hT
C;hT
D;qQ
w5){TailCall_cAbs:g5
cAbs:qS
h0}
qH
TailCall_cAcos:g5
cAcos:qY
wB(172,"x cAcos"
,"[fp_acos(x)]"
,wN);q4
Lad;}
qH
TailCall_cAcosh:g5
cAcosh:qY
wB(169,"x cAcosh"
,"[fp_acosh(x)]"
,wN);q4
Lae;}
qH
TailCall_cAdd:g5
hG
Laf;qT
h3
hL]==hS){if(qL
gZ
Lag;}
h8}
q4
dX
qU
d2
gF
h1
wB(313,"cDup"
a7
aZ,"[x+Value_t(1)]"
wH,wN);q4
Lah;}
}
q4
dX
oF
wB(199,qC1
aZ,"cSub"
,);q4
Lai
gY
hK
qZ
mW(127,aY"cAdd"
mD,"[y+x]"
aZ,q81);q4
Laj;qT
cRSub:qQ
hE
d3
3
qZ
mW(298,aY"cAdd"
mE
mD,mN
aZ
mE,q81);q4
Lak;qT
hI
wB(299,m0
a6
mD,"[-x]"
aZ
mE,wN);q4
Lal
qU
q6:mW(297,aY
a6
mD,mN
mE,q81);q4
Lam;qT
oA
Lan;qT
hI
wB(293,m0"B[IsVarOpcode(B)]"
aW
mD,"[-x]"
aZ" B"
aW,wA","
a8(B)wM);q4
Lao
qU
q6:mW(291,aY"B[IsVarOpcode(B)]"
aW
mD,mN" B"
aW,wA","
a8(B)<<","
a1);q4
Lap;}
w9
mW(105,aY
aF,"[y+x]"
,q81);q4
Laq;}
g8)){wB(57,"x[x==Value_t()]"
aZ,,wN);q4
Lba;h8
g7
dX:;A=dF
w0
oY
cRSub
dV
wB(290,"x"
mE
a3"cAdd"
,"[DO_STACKPLUS1] A [x]"
aZ
mE,aI(A)qD1
wM);incStackPtr();--mStackPtr;q4
Lbb;}
wB(295,a6
a3"cAdd"
,"[DO_STACKPLUS1] A"
aZ
mE,aI(A)wM);incStackPtr();--mStackPtr;q4
Lbc;}
qG
TailCall_cAnd:g5
cAnd
hH
wB(224,mX"cAnd"
,aJ,);q4
w7
m9(117,mA"cAnd"
,"[fp_and(x,y)]"
,q81);q4
Lbe;h8}
qH
TailCall_cArg:g5
cArg:qY
wB(190,"x cArg"
,"[fp_arg(x)]"
,wN);q4
Lbf;}
qH
TailCall_cAsin:g5
cAsin:qY
wB(173,"x cAsin"
,"[fp_asin(x)]"
,wN);q4
Lbg;}
qH
TailCall_cAsinh:g5
cAsinh:qY
wB(170,"x cAsinh"
,"[fp_asinh(x)]"
,wN);q4
Lbh;}
qH
TailCall_cAtan:g5
cAtan:qY
if(g1
x.real(),fp_abs(x.imag()))!=g1
0,oG
wB(174,"x[Value_t(x.real(),fp_abs(x.imag()))!=Value_t(0,1)] cAtan"
,"[fp_atan(x)]"
,wN);q4
Lbi;qG
TailCall_cAtan2:g5
cAtan2:qY
m9(139,mA"cAtan2"
,"[fp_atan2(y,x)]"
,q81);q4
Lbj;qG
TailCall_cAtanh:g5
cAtanh:qY
if(g1
fp_abs(x.real()),x.imag())!=g1
1,0)){wB(171,"x[Value_t(fp_abs(x.real()),x.imag())!=Value_t(1,0)] cAtanh"
,"[fp_atanh(x)]"
,wN);q4
Lbk;qG
TailCall_cCbrt:g5
cCbrt:qY
wB(175,"x cCbrt"
,"[fp_cbrt(x)]"
,wN);q4
Lbl;}
qH
TailCall_cCeil:g5
cCeil:qS
hI
wB(402,m0
q01,mS
aA,);q4
Lbm
gY
wB(135,"x "
q01,"[fp_ceil(x)]"
,wN);q4
Lbn
gS
wB(396,"A[IsAlwaysIntegerOpcode(A)] "
q01,"A"
,aI(A)wM);gJ
qG
TailCall_cConj:g5
cConj:qS
cConj:wB(63,mY" "
mY,,);oS
gY
wB(193,"x "
mY,"[fp_conj(x)]"
,wN);q4
Lbp;}
qH
TailCall_cCos:g5
cCos:qS
cAcos:wB(346,"cAcos "
aO,,);q4
oE
wB(238,m0
aO,aO,);q4
Lbq
gY
wB(176,"x "
aO,"[fp_cos(x)]"
,wN);q4
Lca;oH
qN
qQ
h9
cSec:hD
wB(500,aK" cSec "
wI
aO,"B cSec "
aT,aI(A)q91(B)wM);q4
Lcb;qT
cSin:hD
wB(494,aK" "
mP" "
wI
aO,"B cSinCos"
,aI(A)q91(B)wM);q4
Lcc;h8}
qG
TailCall_cCosh:g5
cCosh:qS
cAsinh:wB(450,"cAsinh "
aM,"[DO_STACKPLUS1] "
q41"[Value_t(1)] "
aQ,);incStackPtr();--mStackPtr;q4
Lcd
oF
wB(239,m0
aM,aM,);q4
Lce
gY
wB(177,"x "
aM,"[fp_cosh(x)]"
,wN);q4
Lcf;oH
qN
oY
cSinh
q11(507,aK" cSinh "
wI
aM,"B cSinhCosh"
,aI(A)q91(B)wM);q4
Lcg;}
}
qG
TailCall_cCot:g5
cCot:A=qN
oY
cTan
q11(498,aK" "
mR" "
wI"cCot"
,"B "
mR" "
aT,aI(A)q91(B)wM);q4
Lcb;}
qG
TailCall_cCsc:g5
cCsc:A=qN
oY
cSin
q11(496,aK" "
mP" "
wI"cCsc"
,"B "
mP" "
aT,aI(A)q91(B)wM);q4
Lcb;}
qG
TailCall_cDeg:g5
cDeg:qY
wB(133,"x cDeg"
,"[RadiansToDegrees(x)]"
,wN);q4
Lch;}
qH
TailCall_cDiv:g5
cDiv:qS
cCos:wB(250,aO
mF,"cSec"
wH,);q4
Lci
qU
cCot:wB(254,"cCot"
mF,mR
wH,);q4
Lcj
qU
cCsc:wB(252,"cCsc"
mF,mP
wH,);q4
Lck
qU
cDup:wB(78,"cDup"
mF,"[Value_t()]"
wH" [Value_t(1)]"
aZ,);q4
Lcl
qU
w2
wB(408,"cExp"
mF,m0"cExp"
wH,);q4
Lcm
qU
cExp2:wB(409,"cExp2"
mF,m0"cExp2"
wH,);q4
Lcn
qU
cInv:wB(213,aU
mF,"cMul"
,);q4
Lco
qU
cPow:wB(407,"cPow"
mF,m0"cPow"
wH,);q4
Lcp
qU
cSec:wB(253,"cSec"
mF,aO
wH,);q4
Lcq
qU
cSin:wB(249,mP
mF,"cCsc"
wH,);q4
Lda
qU
cSinCos:wB(502,"cSinCos"
mF,mR,);q4
Ldb
qU
cSinhCosh:wB(509,"cSinhCosh"
mF,"cTanh"
,);q4
Ldc
qU
cTan:wB(251,mR
mF,"cCot"
wH,);q4
Ldd
gY
if
hF
gQ
hI
wB(125,m0
a4"cDiv"
,"[-x]"
mF,wN);q4
Lde
qU
q6:mW(103,aY
a4"cDiv"
,"[y/x]"
,q81);q4
Ldf;}
}
g8
oG
wB(56,wO"cDiv"
,,wN);q4
Lba;}
dB
h3
gA
qZ
hP(y/x)==fp_const_rad_to_deg
h7
wB(321,"y[(y/x)==fp_const_rad_to_deg<Value_t>()]"
wH" "
wR,"cDeg"
,q81);q4
Ldg;}
if((y/x)==fp_const_deg_to_rad
h7
wB(322,"y[(y/x)==fp_const_deg_to_rad<Value_t>()]"
wH" "
wR,"cRad"
,q81);q4
Ldh;}
wB(323,"y"
wH" "
wR,"[y/x]"
wH,q81);q4
Ldi;}
}
wB(325,wR,"[Value_t(1)/x]"
wH,wN);q4
Ldj;}
gP
cDiv:hC
wB(271,aX"cDiv "
wV,"[DO_STACKPLUS1] B A"
wH
mF,aI(A)q91(B)wM);incStackPtr();--mStackPtr;q4
Ldk;qT
cRDiv:qQ
hE
qV
hM
wB(266,"x"
a9" "
wV,"A"
wH" [x]"
a9,aI(A)qD1
wM);q4
Ldl;g7
hC
wB(265,"B[IsVarOpcode(B)]"
a9" "
wV,"A"
wH" B"
a9,aI(A)q91(B)wM);q4
Ldm;}
h8}
qG
TailCall_cEqual:g5
w8:oL
hU
wB(359,m1
aE,"[x] "
aE,wN);q4
Ldn
qU
cSqr:wB(361,q41
wL
aE,"[x] "
aE,wN);q4
Ldn;}
}
m9(115,mA
aE,"[fp_equal(y,x)]"
,q81);q4
Ldo;qG
TailCall_cExp:g5
w2
qS
hS
gM
wB(404,aF
mL,q21"[fp_exp(x)]"
wH,wN);q4
Ldp;qT
cLog:A=dE
wB(340,wJ
mG
mL,"A"
,aI(A)wM);oS;qT
hM
wB(178,"x"
mL,"[fp_exp(x)]"
,wN);q4
Ldq;}
qH
TailCall_cExp2:g5
cExp2:qS
hS
gM
wB(405,aF
q31,"cExp2 [fp_exp2(x)]"
wH,wN);q4
Lea;qT
cLog2:A=dE
wB(341,wJ
aN
q31,"A"
,aI(A)wM);oS;qT
hM
wB(179,"x"
q31,"[fp_exp2(x)]"
,wN);q4
Leb;}
wB(479,"cExp2"
,"[DO_STACKPLUS1] [fp_log(Value_t(2))]"
wH
mL,);incStackPtr();--mStackPtr;q4
Lec;TailCall_cFloor:g5
cFloor:qS
hI
wB(401,m0
mS,q01
aA,);q4
Led
gY
wB(136,"x "
mS,"[fp_floor(x)]"
,wN);q4
Lee
gS
wB(395,"A[IsAlwaysIntegerOpcode(A)] "
mS,"A"
,aI(A)wM);gJ
qG
TailCall_cGreater:g5
o1:qY
m9(113,mA
m2,"[fp_less(x,y)]"
,q81);q4
Lef;qG
TailCall_cGreaterOrEq:g5
dK:qY
m9(114,mA
aG,"[fp_lessOrEq(x,y)]"
,q81);q4
Leg;qG
TailCall_cHypot:g5
cHypot
d4
dF==cSinCos){wB(84,"cSinCos cHypot"
,"[Value_t()]"
wH" [Value_t(1)]"
aZ,);q4
Lcl;}
qH
TailCall_cImag:g5
cImag:qS
cAbs:wB(81,mV" "
mZ,"[Value_t()]"
wH,);q4
Leh
qU
cReal:wB(80,"cReal "
mZ,"[Value_t()]"
wH,);q4
Leh
gY
wB(192,"x "
mZ,"[fp_imag(x)]"
,wN);q4
Lei;}
qH
TailCall_cInt:g5
cInt:qS
hM
wB(137,"x cInt"
,"[fp_int(x)]"
,wN);q4
Lej
gS
wB(397,"A[IsAlwaysIntegerOpcode(A)] cInt"
,"A"
,aI(A)wM);gJ
qG
TailCall_cInv:g5
cInv:qS
cCos:wB(256,aO" "
aU,"cSec"
,);q4
Lek
qU
cCot:wB(260,"cCot "
aU,mR,);q4
Ldb
qU
cCsc:wB(258,"cCsc "
aU,mP,);q4
Lel
qU
cInv:wB(62,aU" "
aU,,);oS
qU
cPow:wB(355,q61
aU,m0"cPow"
,);q4
Lem
qU
cSec:wB(259,"cSec "
aU,aO,);q4
Len
qU
cSin:wB(255,mP" "
aU,"cCsc"
,);q4
Leo
qU
cSqrt:wB(206,q51" "
aU,"cRSqrt"
,);q4
Lep
qU
cTan:wB(257,mR" "
aU,"cCot"
,);q4
Leq
gY
if
hF)){wB(101,a4
aU,"[Value_t(1)/x]"
,wN);q4
Lfa;h8}
qH
TailCall_cLess:g5
cLess:oL)){A=dE
wB(301,wJ
wL
mJ,mK,qB1(A)wM);q4
Lfb;}
}
m9(111,mA
mJ,"[fp_less(y,x)]"
,q81);q4
Lfc;qG
TailCall_cLessOrEq:g5
cLessOrEq:qY
m9(112,mA
aR,"[fp_lessOrEq(y,x)]"
,q81);q4
Lfd;qG
TailCall_cLog:g5
cLog:mT(343,q21
mG,,);oS
qU
gL
wB(491,mU
mG,mG" [fp_log(x)]"
aZ,wN);q4
Lfe;}
oD
wB(180,qA1
mG,"[fp_log(x)]"
,wN);q4
Lff;h8}
qH
TailCall_cLog10:g5
cLog10:mT(481,q21
aL,"[DO_STACKPLUS1] [fp_log10(fp_const_e<Value_t>())]"
wH,);incStackPtr();--mStackPtr;q4
Lfg
qU
gL
wB(492,mU
aL,aL" [fp_log10(x)]"
aZ,wN);q4
Lfh;}
oD
wB(181,qA1
aL,"[fp_log10(x)]"
,wN);q4
Lfi;h8}
qH
TailCall_cLog2:g5
cLog2:mT(480,q21
aN,"[DO_STACKPLUS1] [fp_log2(fp_const_e<Value_t>())]"
wH,);incStackPtr();--mStackPtr;q4
Lfj
qU
cExp2:wB(344,"cExp2 "
aN,,);oS
qU
gL
wB(490,mU
aN,aN" [fp_log2(x)]"
aZ,wN);q4
Lfk;}
oD
wB(182,qA1
aN,"[fp_log2(x)]"
,wN);q4
Lfl;h8}
qH
TailCall_cMax:g5
cMax
hH
wB(60,mX
mB,,);oS
gY
m9(141,mA
mB,"[fp_max(x,y)]"
,q81);q4
Lfm;}
gP
cDup:hD
wB(66,aK
mQ
a3
mB,"B"
mQ,aI(A)q91(B)wM);oS;qT
cMax:hD
wB(68,aK" "
mB
a3
mB,"B "
mB,aI(A)q91(B)wM);oS;h8}
qG
TailCall_cMin:g5
cMin
hH
wB(59,mX
mC,,);oS
gY
m9(140,mA
mC,"[fp_min(x,y)]"
,q81);q4
Lfn;}
gP
cDup:hD
wB(65,aK
mQ
a3
mC,"B"
mQ,aI(A)q91(B)wM);oS;qT
cMin:hD
wB(67,aK" "
mC
a3
mC,"B "
mC,aI(A)q91(B)wM);oS;h8}
qG
TailCall_cMod:g5
cMod:qY
if
hF)){m9(104,aY
a4"cMod"
,"[fp_mod(y,x)]"
,q81);q4
Lfo;}
qG
TailCall_cMul:g5
h3:qS
cCsc:A=qK
w1
3
gA]==cCos){B=hQ
wB(508,aK" "
aO" A[IsVarOpcode(A)&&mData->mByteCode.size()>3] cCsc"
wH,"B cCot"
,aI(A)q91(B)wM);q4
Lfp;}
}
}
q4
dY
qU
cDup:wB(202,"cDup"
wH,"cSqr"
,);q4
Lfq
qU
cInv:wB(214,aU
wH,"cDiv"
,);q4
Lga
oF
qQ
h9
cDup:wB(467,"cDup"
aA
wH,"cSqr"
aA,);q4
Lgb;oH
qK
qO
A)gA
oM
B=hQ
wB(473,aK
wH
a3
qC1
wH,m5
wH
aA,aI(A)q91(B)wM);q4
Lgc;}
}
}
}
q4
dY
qU
cPow
gM
if
gF
h1
wB(314,mX
m8
wH,"[x+Value_t(1)] cPow"
,wN);q4
Lgd;}
}
q4
dY
gY
g8
gQ
h3:A=hE
w0
wB(93,wS" "
wZ,wX,qB1(A)wM);q4
Lge;}
q4
Default3;g7
Default3:;A=qK
qR
IsBinaryOpcode(A)g2
h2
qQ
hE
qV
q6:mW(92,aY
wD,wX,qB1(A)<<","
a1);q4
Lgf;g7
B
g4
IsBinaryOpcode(B)g2
B)){qQ
oC
qV
q6:mW(96,aY
wK,mK,qB1(A)q91(B)<<","
a1);q4
Lgg;g7
C=oC
qO
C)){wB(94,"C[IsVarOpcode(C)] "
wK,mK,qB1(A)q91(B)<<", C"
wY(C)wM);q4
Lgh;}
if(gV
C)g2
C)){wB(95,"C[IsUnaryOpcode(C)&&!HasInvalidRangesOpcode(C)] "
wK,"B "
mK,qB1(A)q91(B)<<", C"
wY(C)wM);q4
Lgi;}
}
}
if(d1
B)){wB(90,aX
wD,wX,qB1(A)q91(B)wM);q4
Lge;}
if(gV
B)g2
B)){wB(91,"B[IsUnaryOpcode(B)&&!HasInvalidRangesOpcode(B)] "
wD,mK,qB1(A)q91(B)wM);q4
Lgj;}
}
}
if(d1
h2
wB(88,a5" "
wZ,"[x]"
,qB1(A)wM);q4
Lgk;}
if(gV
A)g2
h2
wB(89,"A[IsUnaryOpcode(A)&&!HasInvalidRangesOpcode(A)] "
wZ,wX,qB1(A)wM);q4
Lgl;}
}
}
qQ
h9
hS:qQ
hE
qV
cDup
d4
x+oU
wB(316,"cDup[x+x==Value_t(1)]"
aZ
a7,,wN);q4
Lgm;}
wB(317,aH
a7,"[x+x]"
wH,wN);q4
Lgn
qU
o5
3
qZ
hO
A=qL
4]w0
wB(386,a5" y"
wH
aZ
a7,wX" A "
m3
aZ,wA", "
aY"= "
<<y
qE1(A)wM);q4
Lgo;}
w9
mW(385,aY"cAdd"
a7,wX" [y*x]"
aZ,q81);q4
Lgp;qT
cDeg:wB(209,"cDeg"
a7,"[RadiansToDegrees(x)]"
wH,wN);q4
Lgq
qU
cDiv
oB
qV
o5
4
qZ
mW(278,"y"
wH" "
aX
mH,m3
qH1,wA","
a8(B)<<","
a1);q4
Lha;qT
hI
wB(279,m0
aX
mH,mI
qH1,wA","
a8(B)wM);q4
Lhb
qU
q6:mW(277,aY
aX
mH,"[y*x] B"
mF,wA","
a8(B)<<","
a1);q4
Lhc;}
qT
h3:qQ
hE
d3
3
h1
if(x+oU
wB(318,"cDup[x+x==Value_t(1)]"
aZ
wH
a7,"cMul"
,wN);q4
Lhd;}
wB(319,aH
wH
a7,"cMul [x+x]"
wH,wN);q4
Lhe;w9
hP
y*oU
wB(70,"y[y*x==Value_t(1)]"
wH
a7,,q81);q4
Lhf;}
if((y*x)==fp_const_rad_to_deg
h7
wB(307,"y[(y*x)==fp_const_rad_to_deg<Value_t>()]"
wH
a7,"cDeg"
,q81);q4
Ldg;}
if((y*x)==fp_const_deg_to_rad
h7
wB(308,"y[(y*x)==fp_const_deg_to_rad<Value_t>()]"
wH
a7,"cRad"
,q81);q4
Ldh;}
wB(128,"y"
wH
a7,m3,q81);q4
Lhg;qT
hI
wB(122,qC1
a7,mI,wN);q4
Lhh
qU
cRDiv:qQ
hE
qV
o5
3
qZ
mW(285,"y"
wH
a9
a7,m3
a9,q81);q4
Lhi;qT
hI
wB(286,qC1
a9
a7,mI
a9,wN);q4
Lhj
qU
q6:mW(284,"y"
a9
a7,"[y*x]"
a9,q81);q4
Lhk;qT
cRad:wB(210,"cRad"
a7,"[DegreesToRadians(x)]"
wH,wN);q4
Lhl
qU
cSub
hL
oM
if(qL
3
qZ
hO
A=qL
4]w0
wB(387,a5" y"
wH
aW
a7,wX" A "
m3
aW,wA", "
aY"= "
<<y
qE1(A)wM);q4
Lhm;}
}
w9
mW(102,"y"
a7,"[y*x]"
,q81);q4
Lhn;}
g8
oG
wB(55,"x[x==Value_t(1)]"
wH,,wN);q4
Lba;}
g8-oG
wB(124,"x[x==Value_t(-1)]"
wH,qC1,wN);q4
Lho;}
g8
2)){wB(198,"x[x==Value_t(2)]"
wH,aH,wN);q4
Lhp;}
if(x==fp_const_rad_to_deg
h7
wB(207,"x[x==fp_const_rad_to_deg<Value_t>()]"
wH,"cDeg"
,wN);q4
Lhq;}
if(x==fp_const_deg_to_rad
h7
wB(208,"x[x==fp_const_deg_to_rad<Value_t>()]"
wH,"cRad"
,wN);q4
Lia;h8
g7
dY:;A=dF
qO
A
gQ
cDiv:hC
wB(274,aX"cDiv "
wS,"[DO_STACKPLUS1] A"
wH
qH1,aI(A)q91(B)wM);incStackPtr();--mStackPtr;q4
Lib;}
q4
d5
h3:qQ
hE
qV
hI
B=hQ
wB(470,aK
aA
wH" "
wS,m5
wH
aA,aI(A)q91(B)wM);q4
Lgc;}
q4
dZ;g7
dZ:;hD
wB(461,aK
wH" "
wS,m5
wH,aI(A)q91(B)wM);q4
Lic;}
}
q4
d5
hI
hD
wB(464,aK
aA" "
wS,m5
aA,aI(A)q91(B)wM);q4
Lgb;}
q4
d5
cRDiv
hL
qZ
qC
wB(267,"x"
a9" "
wS,"[DO_STACKPLUS1] "
mK
a9,aI(A)qD1
wM);incStackPtr();--mStackPtr;q4
Lid;}
wB(281,"cRDiv "
wS,"[DO_STACKPLUS1] A"
wH
a9,aI(A)wM);incStackPtr();--mStackPtr;q4
Lie;g7
Default4:;B=qK
qR
w4
wB(458,aK" "
wS,m5,aI(A)q91(B)wM);q4
Lfq;}
}
}
if(gV
h2
B=qK
qO
B
qP
1
gA
oM
C=oC
qR
C==A){D=qL
4]qR
D==B){wB(477,"D[D==B] C[C==A]"
wH" B[IsVarOpcode(B)&&mData->mByteCode.size()>1] A[IsUnaryOpcode(A)]"
wH,"D C cSqr"
wH,aI(A)q91(B)<<", C"
wY(C)<<", D"
wY(D)wM);q4
Lif;}
}
}
}
qG
TailCall_cNEqual:g5
cNEqual:oL
hU
wB(360,m1
wW,"[x] "
wW,wN);q4
Lig
qU
cSqr:wB(362,q41
wL
wW,"[x] "
wW,wN);q4
Lig;}
}
m9(116,mA
wW,"[fp_nequal(y,x)]"
,q81);q4
Lih;qG
TailCall_cNeg:g5
hI
qS
h3
gM
wB(123,"x"
wH
aA,mI,wN);q4
Lii;qT
hI
wB(61,qC1
aA,,);oS
qU
cSin:g9
wB(244,"x"
wH" "
mP
aA,mI" "
mP,wN);q4
Lij;}
qT
oQ
g9
wB(245,"x"
wH" cSinh"
aA,mI" cSinh"
,wN);q4
Lik;}
qT
cTan:g9
wB(246,"x"
wH" "
mR
aA,mI" "
mR,wN);q4
Lil;}
qT
cTanh:g9
wB(247,"x"
wH" cTanh"
aA,mI" cTanh"
,wN);q4
Lim;}
qT
hM
wB(100,"x"
aA,"[-x]"
,wN);q4
Lin;}
qH
TailCall_cNot:g5
cNot:qS
cAbsNotNot:wB(231,"cAbsNotNot"
a0,aS,);q4
Lio
qU
w8:wB(220,aE
a0,wW,);q4
Lip
qU
o1:wB(218,m2
a0,aR,);q4
Liq
qU
dK:wB(219,aG
a0,mJ,);q4
Lja
qU
cLess:wB(216,mJ
a0,aG,);q4
Ljb
qU
cLessOrEq:wB(217,aR
a0,m2,);q4
Ljc
qU
cNEqual:wB(221,wW
a0,aE,);q4
Ljd
qU
cNot:wB(229,"cNot"
a0,aJ,);q4
Lbd
qU
dS:wB(230,aJ
a0,"cNot"
,);q4
Lje
gY
wB(107,"x"
a0,"[fp_not(x)]"
,wN);q4
Ljf;}
qH
TailCall_cNotNot:g5
dS
d4
dF==cNot){wB(232,"cNot "
aJ,"cNot"
,);gJ}
qH
TailCall_cOr:g5
cOr
hH
wB(223,mX"cOr"
,aJ,);q4
w7
m9(118,mA"cOr"
,"[fp_or(x,y)]"
,q81);q4
Ljg;h8}
qH
TailCall_cPolar:g5
cPolar
d4
q0[0
qZ
y=q7;qJ
x
gO
wB(194,"x "
aY"cPolar"
,"[fp_polar(x,y)]"
,"    with "
aY"= "
<<y
qD1
wM);q4
Ljh;qG
TailCall_cPow:g5
cPow:qY
if(isInteger(x
gQ
w2
wB(43,q21
wT,wX
mL,wN);q4
Lji
qU
cExp2:wB(44,"cExp2 "
wT,wX
q31,wN);q4
Ljj
qU
cPow
hL
qZ
hP!isInteger(y)){wB(42,"y[!isInteger(y)] "
q61
wT,aP,q81);q4
Ljk;}
}
wB(45,q61
wT,wX" cPow"
,wN);q4
Ljl;}
}
g8)){wB(83,"x[x==Value_t()] cPow"
,"[Value_t()]"
wH" [Value_t(1)]"
aZ,wN);q4
Ljm;}
g8
oO
wB(332,"x[x==Value_t(0.5)] cPow"
,q51,wN);q4
Ljn;}
g8
1)/g1
3)){wB(333,"x[x==Value_t(1)/Value_t(3)] cPow"
,"cCbrt"
,wN);q4
Ljo;}
g8
1)/g1-3)){wB(334,"x[x==Value_t(1)/Value_t(-3)] cPow"
,"cCbrt "
aU,wN);q4
Ljp;}
g8-oO
wB(335,"x[x==Value_t(-0.5)] cPow"
,"cRSqrt"
,wN);q4
Ljq;}
g8-oG
wB(336,"x[x==Value_t(-1)] cPow"
,aU,wN);q4
Lka;}
qQ
h9
cPow
hL
qZ
mW(330,aY
q61
m8,aP,q81);q4
Ljk;o2
wB(46,q41
m8,"[x+x] cPow"
,wN);q4
Lkb
qU
q6:mW(189,aY
m8,"[fp_pow(y,x)]"
,q81);q4
Lkc;}
wB(455,m8,"[DO_POWI]"
,wN)qR
TryCompilePowi(x))gJ}
qH
TailCall_cRDiv:g5
cRDiv:qS
cSinCos:wB(503,"cSinCos"
a9,"cCot"
,);q4
Leq
qU
cSinhCosh:wB(510,"cSinhCosh"
a9,"cTanh "
aU,);q4
Lkd
gY
g8
oG
wB(268,wO"cRDiv"
,aU,wN);q4
Lka;h8}
qH
TailCall_cRSub:g5
cRSub
d4
q0[0
h1
wB(77,"cDup"
mE,"[Value_t()]"
wH,);q4
Leh;}
qH
TailCall_cRad:g5
cRad:qS
h3
gM
wB(211,"x"
wH" cRad"
,"[DegreesToRadians(x)]"
wH,wN);q4
Lke;qT
hM
wB(134,"x cRad"
,"[DegreesToRadians(x)]"
,wN);q4
Lkf;}
qH
TailCall_cReal:g5
cReal:qY
wB(191,"x cReal"
,"[fp_real(x)]"
,wN);q4
Lkg;}
qH
TailCall_cSec:g5
cSec:A=qN
qQ
h9
cCos:hD
wB(497,aK" "
aO" "
wI"cSec"
,"B "
aO" "
aT,aI(A)q91(B)wM);q4
Lcb;qT
cSin:hD
wB(495,aK" "
mP" "
wI"cSec"
,"B cSinCos "
aU,aI(A)q91(B)wM);q4
Lkh;h8
qG
TailCall_cSin:g5
cSin:qS
cAsin:wB(345,"cAsin "
mP,,);q4
oE
wB(240,m0
mP,mP
aA,);q4
Lki
gY
wB(183,"x "
mP,"[fp_sin(x)]"
,wN);q4
Lkj;oH
qN
oY
cCsc
q11(499,aK" cCsc "
wI
mP,"B cCsc "
aT,aI(A)q91(B)wM);q4
Lcb;}
}
qG
TailCall_cSinh:g5
oQ
qS
cAcosh:wB(437,"cAcosh cSinh"
,"[DO_STACKPLUS1] "
q41"[Value_t(-1)] "
aQ,);incStackPtr();--mStackPtr;q4
Lkk
qU
cAsinh:wB(349,"cAsinh cSinh"
,,);q4
oE
wB(241,m0"cSinh"
,"cSinh"
aA,);q4
Lkl
gY
wB(184,"x cSinh"
,"[fp_sinh(x)]"
,wN);q4
Lkm;}
qH
TailCall_cSqr:g5
cSqr:qS
cAbs:wB(204,mV" cSqr"
,"cSqr"
,);q4
Lkn
oF
wB(203,m0"cSqr"
,"cSqr"
,);q4
Lkn
qU
cSqrt:A=dE
wB(338,wJ
q51" cSqr"
,"A"
,aI(A)wM);oS;h8}
qH
TailCall_cSqrt:g5
cSqrt:qS
hS
d4
qK
o3
A=hE
w0
if(oC
o3
wB(512,"cSqr"
a3
q41
aQ,"A cHypot"
,aI(A)wM);q4
Lko;}
}
B
g4
gV
B)){A=oC
w0
if(qL
4]o3
wB(513,"cSqr"
a3"B[IsUnaryOpcode(B)] "
q41
aQ,"A B cHypot"
,"    with"
a8(B)qE1(A)wM);q4
Lkp;}
}
}
o2
wB(23,q41
q51,mV,);q4
Lkq
gY
wB(185,"x "
q51,"[fp_sqrt(x)]"
,wN);q4
Lla;}
qH
TailCall_cSub:g5
cSub
hH
wB(76,"cDup"
aW,"[Value_t()]"
wH,);q4
Leh
oF
wB(200,qC1
aW,"cAdd"
,);q4
Llb
gY
g8)){wB(58,"x[x==Value_t()]"
aW,,wN);q4
Lba;}
m9(106,aY"x"
aW,"[y-x]"
,q81);q4
Llc;}
wB(51,"x"
aW,"[-x]"
aZ,wN);q4
Lld
gR
w0
oY
cRSub
dV
wB(289,"x"
mE
a3"cSub"
,"A"
aZ" [x]"
mE,aI(A)qD1
wM);q4
Lle;}
wB(296,a6
a3"cSub"
,"[DO_STACKPLUS1] A"
aW
mE,aI(A)wM);incStackPtr();--mStackPtr;q4
Llf;}
qG
TailCall_cTan:g5
cTan:qS
cAtan2:wB(354,"cAtan2 "
mR,"cDiv"
,);q4
Lga
oF
wB(242,m0
mR,mR
aA,);q4
Llg
gY
wB(187,"x "
mR,"[fp_tan(x)]"
,wN);q4
Llh;oH
qN
oY
cCot
q11(501,aK" cCot "
wI
mR,"B cCot "
aT,aI(A)q91(B)wM);q4
Lcb;}
}
qG
TailCall_cTanh:g5
cTanh:qS
cAtanh:wB(352,"cAtanh cTanh"
,,);q4
oE
wB(243,m0"cTanh"
,"cTanh"
aA,);q4
Lli
gY
wB(188,"x cTanh"
,"[fp_tanh(x)]"
,wN);q4
Llj;}
qH
TailCall_cTrunc:g5
cTrunc:qS
hM
wB(138,"x cTrunc"
,"[fp_trunc(x)]"
,wN);q4
Llk
gS
wB(394,"A[IsAlwaysIntegerOpcode(A)] cTrunc"
,"A"
,aI(A)wM);gJ
qG
g7
Default0:;A=w5
w1
0){B=q0[0
hZ
wB(475,aK" A[IsVarOpcode(A)&&mData->mByteCode.size()>0]"
,"B"
mQ,aI(A)q91(B)wM);q4
Lll;}
}
if(gV
h2
B=dF
qO
B
qP
1){C=qK
qR
C==A){D
g4
D==B){wB(476,"D[D==B] C[C==A] B[IsVarOpcode(B)&&mData->mByteCode.size()>1] A[IsUnaryOpcode(A)]"
,"D C"
mQ,aI(A)q91(B)<<", C"
wY(C)<<", D"
wY(D)wM);q4
Llm;}
}
}
}
C=w5
qR
IsCommutativeOrParamSwappableBinaryOpcode(C)){qS
cSin:A=qK
w1
3
gA]==cCos){B=hQ
wB(505,aK" "
aO" A[IsVarOpcode(A)&&mData->mByteCode.size()>3] "
mP" C[IsCommutativeOrParamSwappableBinaryOpcode(C)]"
,"B cSinCos {GetParamSwappedBinaryOpcode(C)}"
,"    with C"
wY(C)qE1(A)q91(B)wM);q4
Lln;}
}
qT
oQ
A=qK
w1
3
gA]==cCosh){B=hQ
wB(506,aK" "
aM" A[IsVarOpcode(A)&&mData->mByteCode.size()>3] cSinh C[IsCommutativeOrParamSwappableBinaryOpcode(C)]"
,"B cSinhCosh {GetParamSwappedBinaryOpcode(C)}"
,"    with C"
wY(C)qE1(A)q91(B)wM);q4
Llo;}
}
h8}
}
}
q4
Laa;Laa:qW
w5);gJ
Lab:g6
Llp:wE(cAbs);q4
TailCall_cAbs;Lac:q7=dP;gJ
Lad:q7=fp_acos
m6
Lae:q7=fp_acosh
m6
Laf:oZ
4));gG
Llq:w5=h3;Lma:g0
Lmb:wE(cMul);q4
TailCall_cMul;Lag:hV
4
dT
oZ
4));Lmc:qW
q6
hY;Lah:q7=x+g1
1);gG
Lfb:w5=h3;q4
Lmb;Lai:gU
cSub;Lmd:wE(cSub);q4
TailCall_cSub;Laj:hW
2
gH
Lme:g0
Lmf:wE(cAdd);q4
TailCall_cAdd;Lak:hW
oR
Lmg:qE
hS);Lmh:w5=cRSub;g0
wE(cRSub);q4
TailCall_cRSub;Lal:o9;qL
2
gK
q4
Lmg;Lam:hW
2
gH
q4
Lmh;Lan:hW
4
gH
Lmi:qE
hS);Lmj:qE
B);Lmk:w5=cSub;g0
q4
Lmd;Lao:o9;oC=q6
q9
oR
q4
Lmi;Lap:hW
oR
q4
Lmj;Laq:gT
y+x;Lba:qM
Lbo:q5
gJ
Lbb:q8
oV
o7
x
q71
gX
Lmg;Lbc:mM
A
gX
Lmg;Lbd:gU
dS;wE(cNotNot);q4
TailCall_cNotNot;Lbe:gT
fp_and(x
d6
Lbf:q7=fp_arg
m6
Lbg:q7=fp_asin
m6
Lbh:q7=fp_asinh
m6
Lbi:q7=fp_atan
m6
Lbj:gT
fp_atan2(gW
Lbk:q7=fp_atanh
m6
Lbl:q7=fp_cbrt
m6
Lbm:q1
cFloor);Lml:w5=cNeg;g0
wE(cNeg);q4
TailCall_cNeg;Lbn:q7=fp_ceil
m6
Lbp:q7=fp_conj
m6
Lbq:g6
Lmm:wE(cCos);q4
TailCall_cCos;Lca:q7=fp_cos
m6
Lcb:dF=cDup;w5=cInv;Lmn:wE(cInv);q4
TailCall_cInv;Lcc:mM
cSinCos);gJ
Lcd:q1
cSqr
o7
g1
1));Lmo:qW
q6
oJ
hS);Lmp:w5=cSqrt;g0
wE(cSqrt);q4
TailCall_cSqrt;Lce:g6
wE(cCosh);q4
TailCall_cCosh;Lcf:q7=fp_cosh
m6
Lcg:mM
cSinhCosh);gJ
Lch:q7=RadiansToDegrees
m6
Lci:q1
cSec
hY;Lcj:q1
cTan
hY;Lck:q1
cSin
hY;Lcl:oZ));dF
dJ
Lmq:qE
dU
oZ
1));Lna:qW
q6);Lnb:w5=hS;q4
Lme;Lcm:q1
cNeg
oJ
cExp
hY;Lcn:q1
cNeg
oJ
cExp2
hY;Lco:g6
q4
Lfb;Lcp:q1
cNeg
oJ
cPow
hY;Lcq:q1
cCos
hY;Lda:q1
cCsc
hY;Ldb:gU
cTan;Lnc:wE(cTan);q4
TailCall_cTan;Ldc:gU
cTanh;Lnd:wE(cTanh);q4
TailCall_cTanh;Ldd:q1
cCot
hY;Lde:o9;dI
Lne:wE(cDiv);q4
TailCall_cDiv;Ldf:gT
y/x;q4
Lba;Ldg:qF1
q8
oR
Lnf:w5=cDeg;g0
wE(cDeg);q4
TailCall_cDeg;Ldh:qF1
q8
oR
Lng:w5=cRad;g0
wE(cRad);q4
TailCall_cRad;Ldi:gT
y/x;dG
Llq;Ldj:q7=g1
1)/x;q4
Lfb;Ldk:mM
oI
Lnh:g0
q4
Lne;Ldl:q8
3
gC
oI
qF
x
q71);Lni:w5=cRDiv;g0
wE(cRDiv);q4
TailCall_cRDiv;Ldm:hV
3
gC
oI
qE
B
gX
Lni;Ldn:dI
Lnj:wE(cEqual);q4
TailCall_cEqual;Ldo:gT
fp_equal(gW
Ldp:d7
cExp
o7
fp_exp(x)gX
Lmc;Ldq:q7=fp_exp
m6
Lea:d7
cExp2
o7
fp_exp2(x)gX
Lmc;Leb:q7=fp_exp2
m6
Lec:qF
oW
g1
2))q71);Lnk:qE
h3
gI
cExp;g0
wE(cExp);q4
TailCall_cExp;Led:q1
cCeil
oT
Lee:q7=fp_floor
m6
Lef:gT
fp_less(x
d6
Leg:gT
fp_lessOrEq(x
d6
Leh:oZ));Lnl:dF
dJ
q4
Llq;Lei:q7=fp_imag
m6
Lej:q7=fp_int
m6
Lek:gU
cSec;wE(cSec);q4
TailCall_cSec;Lel:gU
cSin;Lnm:wE(cSin);q4
TailCall_cSin;Lem:q1
cNeg
gI
cPow;Lnn:g0
Lno:wE(cPow);q4
TailCall_cPow;Len:gU
cCos;q4
Lmm;Leo:gU
cCsc;wE(cCsc);q4
TailCall_cCsc;Lep:q1
cRSqrt);gJ
Leq:g6
Lnp:w5=cCot;wE(cCot);q4
TailCall_cCot;Lfa:q7=g1
1)/x;gJ
Lfc:gT
fp_less(gW
Lfd:gT
fp_lessOrEq(gW
Lfe:d7
cLog
o7
oW
x)gX
Lna;Lff:q7=oW
x);gJ
Lfg:qF
dR
fp_const_e<dH>())gX
Lnl;Lfh:d7
cLog10
o7
dR
x)gX
Lna;Lfi:q7=dR
x);gJ
Lfj:qF
o4
fp_const_e<dH>())gX
Lnl;Lfk:d7
cLog2
o7
o4
x)gX
Lna;Lfl:q7=o4
x);gJ
Lfm:gT
fp_max(x
d6
Lfn:gT
fp_min(x
d6
Lfo:gT
fp_mod(gW
Lfp:hV
oR
q0-=3;q4
Lnp;Lfq:gU
cSqr;Lnq:wE(cSqr);q4
TailCall_cSqr;Lga:gU
cDiv;q4
Lne;Lgb:mM
cSqr
oT
Lgc:hV
3
gC
cSqr);dM
Lml;Lgd:q7=x+g1
1);gG
w5=cPow;q4
Lno;Lge:gG
q4
Lmb;Lgf:gT
x;Loa:dG
Lma;Lgg:qF1
qM
Lob:hV
4
gH
Loc:o6
x);Lod:qW
q6
gX
Lma;Lgh:qM
q4
Lob;Lgi:q8
4
gC
B
gX
Loc;Lgj:q8
oR
q4
Loc;Lgk:qK
dJ
oS;Lgl:dI
q4
Lmb;Lgm:qM
Loe:hV
oR
gJ
Lgn:q7=x+x;q4
Lge;Lgo:gT
x;qL
4]dJ
q8
4
dT
o6
y*x
q71);dM
Lnb;Lgp:gT
x;d7
dU
qF
y*x
gX
Lna;Lgq:q7=RadiansToDegrees(x
gX
Lgl;Lha:qG1
q8
4
gH
Lof:qE
dU
Log:qE
B
gI
cDiv;q4
Lnh;Lhb:o9;oC=q6
q9
oR
q4
Lof;Lhc:qG1
q8
oR
q4
Log;Lhd:q8
4
gH
q4
Lma;Lhe:q8
4
dT
qF
x+x
gX
Lod;Lhf:qF1
qM
q4
Loe;Lhg:qG1
q4
Loa;Lhh:o9;q4
Lgl;Lhi:qG1
q8
oR
Loh:dM
Lni;Lhj:o9;qL
2
gK
q4
Loh;Lhk:qG1
dG
Lni;Lhl:q7=h4
gX
Lgl;Lhm:gT
x;qL
4]dJ
q8
4
dT
o6
y*x
q71);dM
Lmk;Lhn:qG1
q4
Lba;Lho:qM
w3
Lml;Lhp:dF=cDup;dW-=1;qM
Loi:w5=hS;q4
Lmf;Lhq:qM
w3
Lnf;Lia:qM
w3
Lng;Lib:hV
oV
gX
Lof;Lic:hV
2
gH
Loj:qE
cSqr
gX
Lma;Lid:q8
oV
o7
x
q71
gX
Loh;Lie:mM
A
gX
Loh;Lif:hV
oR
q4
Loj;Lig:dI
Lok:wE(cNEqual);q4
TailCall_cNEqual;Lih:gT
fp_nequal(gW
Lii:o9;q4
Lco;Lij:o9
gB
cSin;g0
q4
Lnm;Lik:o9
gB
cSinh;g0
wE(cSinh);q4
TailCall_cSinh;Lil:o9
gB
cTan;g0
q4
Lnc;Lim:o9
gB
cTanh;g0
q4
Lnd;Lin:o9;gJ
Lio:q1
cAbsNot);gJ
Lip:gU
cNEqual;q4
Lok;Liq:gU
cLessOrEq;wE(cLessOrEq);q4
TailCall_cLessOrEq;Lja:gU
cLess;wE(cLess);q4
TailCall_cLess;Ljb:gU
dK;wE(cGreaterOrEq);q4
TailCall_cGreaterOrEq;Ljc:gU
o1;wE(cGreater);q4
TailCall_cGreater;Ljd:gU
w8;q4
Lnj;Lje:g6
wE(cNot);q4
TailCall_cNot;Ljf:q7=fp_not
m6
Ljg:gT
fp_or(x
d6
Ljh:gT
fp_polar(x
d6
Lji:dL
Lnk;Ljj:qK=d8
cExp2;g0
wE(cExp2);q4
TailCall_cExp2;Ljk:qG1
dG
Lnn;Ljl:qK
dJ
q1
h3
gX
Lnn;Ljm:q7=g1
gX
Lmq;Ljn:qM
w3
Lmp;Ljo:qM
q5
w5=cCbrt;g0
wE(cCbrt);q4
TailCall_cCbrt;Ljp:qM
q1
cCbrt);Lol:w5=cInv;g0
q4
Lmn;Ljq:qM
q4
Lep;Lka:qM
w3
Lol;Lkb:q7=x+x;dI
q4
Lno;Lkc:gT
oX
gW
Lkd:q1
cTanh
gX
Lol;Lke:q7=h4
gX
Lco;Lkf:q7=h4);gJ
Lkg:q7=fp_real
m6
Lkh:mM
cSinCos
gX
Lol;Lki:q1
cSin
oT
Lkj:q7=fp_sin
m6
Lkk:q1
cSqr
o7
g1-1)gX
Lmo;Lkl:q1
cSinh
oT
Lkm:q7=fp_sinh
m6
Lkn:g6
q4
Lnq;Lko:hV
4
gC
A);Lom:w5=cHypot;g0
wE(cHypot);q4
TailCall_cHypot;Lkp:hV
5
gC
A
oJ
B
gX
Lom;Lkq:gU
cAbs;q4
Llp;Lla:q7=fp_sqrt
m6
Llb:g6
q4
Loi;Llc:gT
y-x;q4
Lba;Lld:o9;q4
Loi;Lle:q8
oV
oJ
hS
o7
x
q71
gX
Lmh;Llf:mM
A
oJ
cSub
gX
Lmh;Llg:q1
cTan
oT
Llh:q7=fp_tan
m6
Lli:q1
cTanh
oT
Llj:q7=fp_tanh
m6
Llk:q7=fp_trunc
m6
Lll:qW
cDup);gJ
Llm:dF=cDup;gJ
Lln:hV
3
gC
cSinCos);Lon:qE
GetParamSwappedBinaryOpcode(C));gJ
Llo:hV
3
gC
cSinhCosh
gX
Lon;gJ
q4
TailCall_cAcos;q4
TailCall_cAcosh;q4
TailCall_cAnd;q4
TailCall_cArg;q4
TailCall_cAsin;q4
TailCall_cAsinh;q4
TailCall_cAtan;q4
TailCall_cAtan2;q4
TailCall_cAtanh;q4
TailCall_cCeil;q4
TailCall_cConj;q4
TailCall_cFloor;q4
TailCall_cImag;q4
TailCall_cInt;q4
TailCall_cLog;q4
TailCall_cLog10;q4
TailCall_cLog2;q4
TailCall_cMax;q4
TailCall_cMin;q4
TailCall_cMod;q4
TailCall_cOr;q4
TailCall_cPolar;q4
TailCall_cRDiv;q4
TailCall_cRad;q4
TailCall_cReal;q4
TailCall_cSec;q4
TailCall_cSin;q4
TailCall_cSinh;q4
TailCall_cSqrt;q4
TailCall_cSub;q4
TailCall_cTan;q4
TailCall_cTanh;q4
TailCall_cTrunc;
#endif
#undef FP_ReDefinePointers
#undef FP_TRACE_BYTECODE_OPTIMIZATION
#undef FP_TRACE_OPCODENAME
#undef FP_COMPLEX_VERSION
#undef FP_FLOAT_VERSION
}

#ifdef FP_SUPPORT_LONG_INT_TYPE
template<>
inline void FunctionParserBase<long>::AddFunctionOpcode(unsigned opcode)
{
    typedef long Value_t;
#define FP_FLOAT_VERSION 0
#define FP_COMPLEX_VERSION 0
#include "extrasrc/fp_opcode_add.inc"
#undef FP_COMPLEX_VERSION
#undef FP_FLOAT_VERSION
}
#endif

#ifdef FP_SUPPORT_GMP_INT_TYPE
template<>
inline void FunctionParserBase<GmpInt>::AddFunctionOpcode(unsigned opcode)
{
    typedef GmpInt Value_t;
#define FP_FLOAT_VERSION 0
#define FP_COMPLEX_VERSION 0
#include "extrasrc/fp_opcode_add.inc"
#undef FP_COMPLEX_VERSION
#undef FP_FLOAT_VERSION
}
#endif

#ifdef FP_SUPPORT_COMPLEX_DOUBLE_TYPE
template<>
inline void FunctionParserBase<std::complex<double> >::AddFunctionOpcode(unsigned opcode)
{
    typedef std::complex<double> Value_t;
#define FP_FLOAT_VERSION 1
#define FP_COMPLEX_VERSION 1
#include "extrasrc/fp_opcode_add.inc"
#undef FP_COMPLEX_VERSION
#undef FP_FLOAT_VERSION
}
#endif

#ifdef FP_SUPPORT_COMPLEX_FLOAT_TYPE
template<>
inline void FunctionParserBase<std::complex<float> >::AddFunctionOpcode(unsigned opcode)
{
    typedef std::complex<float> Value_t;
#define FP_FLOAT_VERSION 1
#define FP_COMPLEX_VERSION 1
#include "extrasrc/fp_opcode_add.inc"
#undef FP_COMPLEX_VERSION
#undef FP_FLOAT_VERSION
}
#endif

#ifdef FP_SUPPORT_COMPLEX_LONG_DOUBLE_TYPE
template<>
inline void FunctionParserBase<std::complex<long double> >::AddFunctionOpcode(unsigned opcode)
{
    typedef std::complex<long double> Value_t;
#define FP_FLOAT_VERSION 1
#define FP_COMPLEX_VERSION 1
#include "extrasrc/fp_opcode_add.inc"
#undef FP_COMPLEX_VERSION
#undef FP_FLOAT_VERSION
}
#endif

template<typename Value_t>
unsigned
FunctionParserBase<Value_t>::ParseIdentifier(const char* function)
{
    return readIdentifier<Value_t>(function);
}

template<typename Value_t>
std::pair<const char*, Value_t>
FunctionParserBase<Value_t>::ParseLiteral(const char* function)
{
    char* endptr;
#if 0 /* Profile the hex literal parser */
    if(function[0]=='0' && function[1]=='x')
    {
        // Parse hexadecimal literal if fp_parseLiteral didn't already
        Value_t val = parseHexLiteral<Value_t>(function+2, &endptr);
        if(endptr == function+2)
            return std::pair<const char*,Value_t> (function, Value_t());
        return std::pair<const char*, Value_t> (endptr, val);
    }
#endif
    Value_t val = fp_parseLiteral<Value_t>(function, &endptr);

    if(endptr == function+1 && function[0] == '0' && function[1] == 'x')
    {
        // Parse hexadecimal literal if fp_parseLiteral didn't already
        val = parseHexLiteral<Value_t>(function+2, &endptr);
        if(endptr == function+2)
            return std::pair<const char*,Value_t> (function, Value_t());
    }
    else if(endptr == function)
        return std::pair<const char*,Value_t> (function, Value_t());

    return std::pair<const char*,Value_t> (endptr, val);
}

#ifdef FP_SUPPORT_MPFR_FLOAT_TYPE
template<>
std::pair<const char*, MpfrFloat>
FunctionParserBase<MpfrFloat>::ParseLiteral(const char* function)
{
    char* endPtr;
    const MpfrFloat val = MpfrFloat::parseString(function, &endPtr);
    if(endPtr == function)
        return std::pair<const char*,MpfrFloat> (function, MpfrFloat());
    return std::pair<const char*,MpfrFloat> (endPtr, val);
}
#endif

#ifdef FP_SUPPORT_GMP_INT_TYPE
template<>
std::pair<const char*, GmpInt>
FunctionParserBase<GmpInt>::ParseLiteral(const char* function)
{
    char* endPtr;
    const GmpInt val = GmpInt::parseString(function, &endPtr);
    if(endPtr == function)
        return std::pair<const char*,GmpInt> (function, GmpInt());
    return std::pair<const char*,GmpInt> (endPtr, val);
}
#endif


template<typename Value_t>
inline const char*
FunctionParserBase<Value_t>::CompileLiteral(const char* function)
{
    std::pair<const char*, Value_t> result = ParseLiteral(function);

    if(result.first == function)
        return SetErrorType(SYNTAX_ERROR, result.first);

    AddImmedOpcode(result.second);
    incStackPtr();
    SkipSpace(result.first);
    return result.first;
}

template<typename Value_t>
const char* FunctionParserBase<Value_t>::CompileIf(const char* function)
{
    if(*function != '(') return SetErrorType(EXPECT_PARENTH_FUNC, function);

    function = CompileExpression(function+1);
    if(!function) return 0;
    if(*function != ',')
        return SetErrorType(noCommaError<Value_t>(*function), function);

    OPCODE opcode = cIf;
    if(mData->mByteCode.back() == cNotNot) mData->mByteCode.pop_back();
    if(IsNeverNegativeValueOpcode(mData->mByteCode.back()))
    {
        // If we know that the condition to be tested is always
        // a positive value (such as when produced by "x<y"),
        // we can use the faster opcode to evaluate it.
        // cIf tests whether fabs(cond) >= 0.5,
        // cAbsIf simply tests whether cond >= 0.5.
        opcode = cAbsIf;
    }

    mData->mByteCode.push_back(opcode);
    const unsigned curByteCodeSize = unsigned(mData->mByteCode.size());
    PushOpcodeParam<false>(0); // Jump index; to be set later
    PushOpcodeParam<true> (0); // Immed jump index; to be set later

    --mStackPtr;

    function = CompileExpression(function + 1);
    if(!function) return 0;
    if(*function != ',')
        return SetErrorType(noCommaError<Value_t>(*function), function);

    mData->mByteCode.push_back(cJump);
    const unsigned curByteCodeSize2 = unsigned(mData->mByteCode.size());
    const unsigned curImmedSize2 = unsigned(mData->mImmed.size());
    PushOpcodeParam<false>(0); // Jump index; to be set later
    PushOpcodeParam<true> (0); // Immed jump index; to be set later

    --mStackPtr;

    function = CompileExpression(function + 1);
    if(!function) return 0;
    if(*function != ')')
        return SetErrorType(noParenthError<Value_t>(*function), function);

    PutOpcodeParamAt<true> ( mData->mByteCode.back(), unsigned(mData->mByteCode.size()-1) );
    // ^Necessary for guarding against if(x,1,2)+1 being changed
    //  into if(x,1,3) by fp_opcode_add.inc

    // Set jump indices
    PutOpcodeParamAt<false>( curByteCodeSize2+1, curByteCodeSize );
    PutOpcodeParamAt<false>( curImmedSize2,      curByteCodeSize+1 );
    PutOpcodeParamAt<false>( unsigned(mData->mByteCode.size())-1, curByteCodeSize2);
    PutOpcodeParamAt<false>( unsigned(mData->mImmed.size()),      curByteCodeSize2+1);

    ++function;
    SkipSpace(function);
    return function;
}

template<typename Value_t>
const char* FunctionParserBase<Value_t>::CompileFunctionParams
(const char* function, unsigned requiredParams)
{
    if(*function != '(') return SetErrorType(EXPECT_PARENTH_FUNC, function);

    if(requiredParams > 0)
    {
        const char* function_end = CompileExpression(function+1);
        if(!function_end)
        {
            // If an error occurred, verify whether it was caused by ()
            ++function;
            SkipSpace(function);
            if(*function == ')')
                return SetErrorType(ILL_PARAMS_AMOUNT, function);
            // Not caused by (), use the error message given by CompileExpression()
            return 0;
        }
        function = function_end;

        for(unsigned i = 1; i < requiredParams; ++i)
        {
            if(*function != ',')
                return SetErrorType(noCommaError<Value_t>(*function), function);

            function = CompileExpression(function+1);
            if(!function) return 0;
        }
        // No need for incStackPtr() because each parse parameter calls it
        mStackPtr -= requiredParams-1;
    }
    else
    {
        incStackPtr(); // return value of function is pushed onto the stack
        ++function;
        SkipSpace(function);
    }

    if(*function != ')')
        return SetErrorType(noParenthError<Value_t>(*function), function);
    ++function;
    SkipSpace(function);
    return function;
}

template<typename Value_t>
const char* FunctionParserBase<Value_t>::CompileElement(const char* function)
{
    if(BeginsLiteral<Value_t>( (unsigned char) *function))
        return CompileLiteral(function);

    unsigned nameLength = readIdentifier<Value_t>(function);
    if(nameLength == 0)
    {
        // No identifier found
        if(*function == '(') return CompileParenthesis(function);
        if(*function == ')') return SetErrorType(MISM_PARENTH, function);
        return SetErrorType(SYNTAX_ERROR, function);
    }

    // Function, variable or constant
    if(nameLength & 0x80000000U) // Function
    {
        OPCODE func_opcode = OPCODE( (nameLength >> 16) & 0x7FFF );
        return CompileFunction(function + (nameLength & 0xFFFF), func_opcode);
    }

    NamePtr name(function, nameLength);
    const char* endPtr = function + nameLength;
    SkipSpace(endPtr);

    typename NamePtrsMap<Value_t>::iterator nameIter =
        mData->mNamePtrs.find(name);
    if(nameIter == mData->mNamePtrs.end())
    {
        // Check if it's an inline variable:
        for(typename Data::InlineVarNamesContainer::reverse_iterator iter =
                mData->mInlineVarNames.rbegin();
            iter != mData->mInlineVarNames.rend();
            ++iter)
        {
            if(name == iter->mName)
            {
                if( iter->mFetchIndex+1 == mStackPtr)
                {
                    mData->mByteCode.push_back(cDup);
                }
                else
                {
                    mData->mByteCode.push_back(cFetch);
                    PushOpcodeParam<true>(iter->mFetchIndex);
                }
                incStackPtr();
                return endPtr;
            }
        }

        return SetErrorType(UNKNOWN_IDENTIFIER, function);
    }

    const NameData<Value_t>* nameData = &nameIter->second;
    switch(nameData->type)
    {
      case NameData<Value_t>::VARIABLE: // is variable
          if(unlikely(!mData->mByteCode.empty() &&
                      mData->mByteCode.back() == nameData->index))
              mData->mByteCode.push_back(cDup);
          else
              mData->mByteCode.push_back(nameData->index);
          incStackPtr();
          return endPtr;

      case NameData<Value_t>::CONSTANT: // is constant
          AddImmedOpcode(nameData->value);
          incStackPtr();
          return endPtr;

      case NameData<Value_t>::UNIT: // is unit (error if appears here)
          break;

      case NameData<Value_t>::FUNC_PTR: // is C++ function
          function = CompileFunctionParams
              (endPtr, mData->mFuncPtrs[nameData->index].mParams);
          //if(!function) return 0;
          mData->mByteCode.push_back(cFCall);
          PushOpcodeParam<true>(nameData->index);
          return function;

      case NameData<Value_t>::PARSER_PTR: // is FunctionParser
          function = CompileFunctionParams
              (endPtr, mData->mFuncParsers[nameData->index].mParams);
          //if(!function) return 0;
          mData->mByteCode.push_back(cPCall);
          PushOpcodeParam<true>(nameData->index);
          return function;
    }

    // When it's an unit (or unrecognized type):
    return SetErrorType(SYNTAX_ERROR, function);
}

template<typename Value_t>
inline const char* FunctionParserBase<Value_t>::CompileFunction
(const char* function, unsigned func_opcode)
{
    SkipSpace(function);
    const FuncDefinition& funcDef = Functions[func_opcode];

    if(func_opcode == cIf) // "if" is a special case
        return CompileIf(function);

    unsigned requiredParams = funcDef.params;

    function = CompileFunctionParams(function, requiredParams);
    if(!function) return 0;

    if(mData->mUseDegreeConversion)
    {
        if(funcDef.flags & FuncDefinition::AngleIn)
            AddFunctionOpcode(cRad);

        AddFunctionOpcode(func_opcode);

        if(funcDef.flags & FuncDefinition::AngleOut)
            AddFunctionOpcode(cDeg);
    }
    else
    {
        AddFunctionOpcode(func_opcode);
    }
    return function;
}

template<typename Value_t>
inline const char*
FunctionParserBase<Value_t>::CompileParenthesis(const char* function)
{
    ++function; // Skip '('

    SkipSpace(function);
    if(*function == ')') return SetErrorType(EMPTY_PARENTH, function);
    function = CompileExpression(function);
    if(!function) return 0;

    if(*function != ')') return SetErrorType(MISSING_PARENTH, function);
    ++function; // Skip ')'

    SkipSpace(function);
    return function;
}

template<typename Value_t>
const char*
FunctionParserBase<Value_t>::CompilePossibleUnit(const char* function)
{
    unsigned nameLength = readIdentifier<Value_t>(function);
    if(nameLength & 0x80000000U) return function; // built-in function name
    if(nameLength != 0)
    {
        NamePtr name(function, nameLength);

        typename NamePtrsMap<Value_t>::iterator nameIter =
            mData->mNamePtrs.find(name);
        if(nameIter != mData->mNamePtrs.end())
        {
            const NameData<Value_t>* nameData = &nameIter->second;
            if(nameData->type == NameData<Value_t>::UNIT)
            {
                AddImmedOpcode(nameData->value);
                incStackPtr();
                AddFunctionOpcode(cMul);
                --mStackPtr;

                const char* endPtr = function + nameLength;
                SkipSpace(endPtr);
                return endPtr;
            }
        }
    }

    return function;
}

template<typename Value_t>
inline const char*
FunctionParserBase<Value_t>::CompilePow(const char* function)
{
    function = CompileElement(function);
    if(!function) return 0;
    function = CompilePossibleUnit(function);

    if(*function == '^')
    {
        ++function;
        SkipSpace(function);

        unsigned op = cPow;
        if(mData->mByteCode.back() == cImmed)
        {
            if(mData->mImmed.back() == fp_const_e<Value_t>())
                { op = cExp;  mData->mByteCode.pop_back();
                    mData->mImmed.pop_back(); --mStackPtr; }
            else if(mData->mImmed.back() == Value_t(2))
                { op = cExp2; mData->mByteCode.pop_back();
                    mData->mImmed.pop_back(); --mStackPtr; }
        }

        function = CompileUnaryMinus(function);
        if(!function) return 0;

        // add opcode
        AddFunctionOpcode(op);

        if(op == cPow) --mStackPtr;
    }
    return function;
}

/* Currently the power operator is skipped for integral types because its
   usefulness with them is questionable, and in the case of GmpInt, for safety
   reasons:
   - With long int almost any power, except for very small ones, would
     overflow the result, so the usefulness of this is rather questionable.
   - With GmpInt the power operator could be easily abused to make the program
     run out of memory (think of a function like "10^10^10^10^1000000").
*/
#ifdef FP_SUPPORT_LONG_INT_TYPE
template<>
inline const char*
FunctionParserBase<long>::CompilePow(const char* function)
{
    function = CompileElement(function);
    if(!function) return 0;
    return CompilePossibleUnit(function);
}
#endif

#ifdef FP_SUPPORT_GMP_INT_TYPE
template<>
inline const char*
FunctionParserBase<GmpInt>::CompilePow(const char* function)
{
    function = CompileElement(function);
    if(!function) return 0;
    return CompilePossibleUnit(function);
}
#endif

template<typename Value_t>
inline const char*
FunctionParserBase<Value_t>::CompileUnaryMinus(const char* function)
{
    char op = *function;
    switch(op)
    {
        case '-':
        case '!':
            ++function;
            SkipSpace(function);

            function = CompileUnaryMinus(function);
            if(!function) return 0;

            AddFunctionOpcode(op=='-' ? cNeg : cNot);

            return function;
        default: break;
    }
    return CompilePow(function);
}

template<typename Value_t>
inline const char*
FunctionParserBase<Value_t>::CompileMult(const char* function)
{
    function = CompileUnaryMinus(function);
    if(!function) return 0;

    Value_t pending_immed(1);
    #define FP_FlushImmed(do_reset) \
        if(pending_immed != Value_t(1)) \
        { \
            unsigned op = cMul; \
            if(!IsIntType<Value_t>::result && mData->mByteCode.back() == cInv) \
            { \
                /* (...) cInv 5 cMul -> (...) 5 cRDiv */ \
                /*           ^               ^      | */ \
                mData->mByteCode.pop_back(); \
                op = cRDiv; \
            } \
            AddImmedOpcode(pending_immed); \
            incStackPtr(); \
            AddFunctionOpcode(op); \
            --mStackPtr; \
            if(do_reset) pending_immed = Value_t(1); \
        }
    while(true)
    {
        char c = *function;
        if(c == '%')
        {
            FP_FlushImmed(true);
            ++function;
            SkipSpace(function);
            function = CompileUnaryMinus(function);
            if(!function) return 0;
            AddFunctionOpcode(cMod);
            --mStackPtr;
            continue;
        }
        if(c != '*' && c != '/') break;

        bool safe_cumulation = (c == '*' || !IsIntType<Value_t>::result);
        if(!safe_cumulation)
        {
            FP_FlushImmed(true);
        }

        ++function;
        SkipSpace(function);
        if(mData->mByteCode.back() == cImmed
        && (safe_cumulation
         || mData->mImmed.back() == Value_t(1)))
        {
            // 5 (...) cMul --> (...)      ||| 5 cMul
            // 5 (...) cDiv --> (...) cInv ||| 5 cMul
            //  ^          |              ^
            pending_immed *= mData->mImmed.back();
            mData->mImmed.pop_back();
            mData->mByteCode.pop_back();
            --mStackPtr;
            function = CompileUnaryMinus(function);
            if(!function) return 0;
            if(c == '/')
                AddFunctionOpcode(cInv);
            continue;
        }
        if(safe_cumulation
        && mData->mByteCode.back() == cMul
        && mData->mByteCode[mData->mByteCode.size()-2] == cImmed)
        {
            // (:::) 5 cMul (...) cMul -> (:::) (...) cMul  ||| 5 cMul
            // (:::) 5 cMul (...) cDiv -> (:::) (...) cDiv  ||| 5 cMul
            //             ^                   ^
            pending_immed *= mData->mImmed.back();
            mData->mImmed.pop_back();
            mData->mByteCode.pop_back();
            mData->mByteCode.pop_back();
        }
        // cDiv is not tested here because the bytecode
        // optimizer will convert this kind of cDivs into cMuls.
        bool lhs_inverted = false;
        if(!IsIntType<Value_t>::result && c == '*'
        && mData->mByteCode.back() == cInv)
        {
            // (:::) cInv (...) cMul -> (:::) (...) cRDiv
            // (:::) cInv (...) cDiv -> (:::) (...) cMul cInv
            //           ^                   ^            |
            mData->mByteCode.pop_back();
            lhs_inverted = true;
        }
        function = CompileUnaryMinus(function);
        if(!function) return 0;
        if(safe_cumulation
        && mData->mByteCode.back() == cMul
        && mData->mByteCode[mData->mByteCode.size()-2] == cImmed)
        {
            // (:::) (...) 5 cMul cMul -> (:::) (...) cMul  |||  5 Mul
            // (:::) (...) 5 cMul cDiv -> (:::) (...) cDiv  ||| /5 Mul
            //                   ^                        ^
            if(c == '*')
                pending_immed *= mData->mImmed.back();
            else
                pending_immed /= mData->mImmed.back();
            mData->mImmed.pop_back();
            mData->mByteCode.pop_back();
            mData->mByteCode.pop_back();
        }
        else
        if(safe_cumulation
        && mData->mByteCode.back() == cRDiv
        && mData->mByteCode[mData->mByteCode.size()-2] == cImmed)
        {
            // (:::) (...) 5 cRDiv cMul -> (:::) (...) cDiv  |||  5 cMul
            // (:::) (...) 5 cRDiv cDiv -> (:::) (...) cMul  ||| /5 cMul
            //                    ^                   ^
            if(c == '*')
                { c = '/'; pending_immed *= mData->mImmed.back(); }
            else
                { c = '*'; pending_immed /= mData->mImmed.back(); }
            mData->mImmed.pop_back();
            mData->mByteCode.pop_back();
            mData->mByteCode.pop_back();
        }
        if(!lhs_inverted) // if (/x/y) was changed to /(x*y), add missing cInv
        {
            AddFunctionOpcode(c == '*' ? cMul : cDiv);
            --mStackPtr;
        }
        else if(c == '*') // (/x)*y -> rdiv(x,y)
        {
            AddFunctionOpcode(cRDiv);
            --mStackPtr;
        }
        else // (/x)/y -> /(x*y)
        {
            AddFunctionOpcode(cMul);
            --mStackPtr;
            AddFunctionOpcode(cInv);
        }
    }
    FP_FlushImmed(false);
    #undef FP_FlushImmed
    return function;
}

template<typename Value_t>
inline const char*
FunctionParserBase<Value_t>::CompileAddition(const char* function)
{
    function = CompileMult(function);
    if(!function) return 0;

    Value_t pending_immed(0);
    #define FP_FlushImmed(do_reset) \
        if(pending_immed != Value_t(0)) \
        { \
            unsigned op = cAdd; \
            if(mData->mByteCode.back() == cNeg) \
            { \
                /* (...) cNeg 5 cAdd -> (...) 5 cRSub */ \
                /*           ^               ^      | */ \
                mData->mByteCode.pop_back(); \
                op = cRSub; \
            } \
            AddImmedOpcode(pending_immed); \
            incStackPtr(); \
            AddFunctionOpcode(op); \
            --mStackPtr; \
            if(do_reset) pending_immed = Value_t(0); \
        }
    while(true)
    {
        char c = *function;
        if(c != '+' && c != '-') break;
        ++function;
        SkipSpace(function);
        if(mData->mByteCode.back() == cImmed)
        {
            // 5 (...) cAdd --> (...)      ||| 5 cAdd
            // 5 (...) cSub --> (...) cNeg ||| 5 cAdd
            //  ^          |              ^
            pending_immed += mData->mImmed.back();
            mData->mImmed.pop_back();
            mData->mByteCode.pop_back();
            --mStackPtr;
            function = CompileMult(function);
            if(!function) return 0;
            if(c == '-')
                AddFunctionOpcode(cNeg);
            continue;
        }
        if(mData->mByteCode.back() == cAdd
        && mData->mByteCode[mData->mByteCode.size()-2] == cImmed)
        {
            // (:::) 5 cAdd (...) cAdd -> (:::) (...) cAdd  ||| 5 cAdd
            // (:::) 5 cAdd (...) cSub -> (:::) (...) cSub  ||| 5 cAdd
            //             ^                   ^
            pending_immed += mData->mImmed.back();
            mData->mImmed.pop_back();
            mData->mByteCode.pop_back();
            mData->mByteCode.pop_back();
        }
        // cSub is not tested here because the bytecode
        // optimizer will convert this kind of cSubs into cAdds.
        bool lhs_negated = false;
        if(mData->mByteCode.back() == cNeg)
        {
            // (:::) cNeg (...) cAdd -> (:::) (...) cRSub
            // (:::) cNeg (...) cSub -> (:::) (...) cAdd cNeg
            //           ^                   ^            |
            mData->mByteCode.pop_back();
            lhs_negated = true;
        }
        function = CompileMult(function);
        if(!function) return 0;
        if(mData->mByteCode.back() == cAdd
        && mData->mByteCode[mData->mByteCode.size()-2] == cImmed)
        {
            // (:::) (...) 5 cAdd cAdd -> (:::) (...) cAdd  |||  5 Add
            // (:::) (...) 5 cAdd cSub -> (:::) (...) cSub  ||| -5 Add
            //                   ^                        ^
            if(c == '+')
                pending_immed += mData->mImmed.back();
            else
                pending_immed -= mData->mImmed.back();
            mData->mImmed.pop_back();
            mData->mByteCode.pop_back();
            mData->mByteCode.pop_back();
        }
        else
        if(mData->mByteCode.back() == cRSub
        && mData->mByteCode[mData->mByteCode.size()-2] == cImmed)
        {
            // (:::) (...) 5 cRSub cAdd -> (:::) (...) cSub  |||  5 cAdd
            // (:::) (...) 5 cRSub cSub -> (:::) (...) cAdd  ||| -5 cAdd
            //                    ^                   ^
            if(c == '+')
                { c = '-'; pending_immed += mData->mImmed.back(); }
            else
                { c = '+'; pending_immed -= mData->mImmed.back(); }
            mData->mImmed.pop_back();
            mData->mByteCode.pop_back();
            mData->mByteCode.pop_back();
        }
        if(!lhs_negated) // if (-x-y) was changed to -(x+y), add missing cNeg
        {
            AddFunctionOpcode(c == '+' ? cAdd : cSub);
            --mStackPtr;
        }
        else if(c == '+') // (-x)+y -> rsub(x,y)
        {
            AddFunctionOpcode(cRSub);
            --mStackPtr;
        }
        else // (-x)-y -> -(x+y)
        {
            AddFunctionOpcode(cAdd);
            --mStackPtr;
            AddFunctionOpcode(cNeg);
        }
    }
    FP_FlushImmed(false);
    #undef FP_FlushImmed
    return function;
}

template<typename Value_t>
inline const char*
FunctionParserBase<Value_t>::CompileComparison(const char* function)
{
    unsigned op=0;
    while(true)
    {
        function = CompileAddition(function);
        if(!function) return 0;

        if(op)
        {
            AddFunctionOpcode(op);
            --mStackPtr;
        }
        switch(*function)
        {
          case '=':
              ++function; op = cEqual; break;
          case '!':
              if(function[1] == '=')
              { function += 2; op = cNEqual; break; }
              // If '=' does not follow '!', a syntax error will
              // be generated at the outermost parsing level
              return function;
          case '<':
              if(function[1] == '=')
              { function += 2; op = cLessOrEq; break; }
              ++function; op = cLess; break;
          case '>':
              if(function[1] == '=')
              { function += 2; op = cGreaterOrEq; break; }
              ++function; op = cGreater; break;
          default: return function;
        }
        SkipSpace(function);
    }
    return function;
}

template<typename Value_t>
inline const char* FunctionParserBase<Value_t>::CompileAnd(const char* function)
{
    std::size_t param0end=0;
    while(true)
    {
        function = CompileComparison(function);
        if(!function) return 0;

        if(param0end)
        {
            if(mData->mByteCode.back() == cNotNot) mData->mByteCode.pop_back();

            AddFunctionOpcode(cAnd);
            --mStackPtr;
        }
        if(*function != '&') break;
        ++function;
        SkipSpace(function);
        param0end = mData->mByteCode.size();
    }
    return function;
}

template<typename Value_t>
const char* FunctionParserBase<Value_t>::CompileExpression(const char* function)
{
    std::size_t param0end=0;
    while(true)
    {
        SkipSpace(function);
        function = CompileAnd(function);
        if(!function) return 0;

        if(param0end)
        {
            if(mData->mByteCode.back() == cNotNot) mData->mByteCode.pop_back();

            AddFunctionOpcode(cOr);
            --mStackPtr;
        }
        if(*function != '|') break;
        ++function;
        param0end = mData->mByteCode.size();
    }
    return function;
}

template<typename Value_t>
const char* FunctionParserBase<Value_t>::Compile(const char* function)
{
    while(true)
    {
        // Check if an identifier appears as first token:
        SkipSpace(function);
        unsigned nameLength = readIdentifier<Value_t>(function);
        if(nameLength > 0 && !(nameLength & 0x80000000U))
        {
            typename Data::InlineVariable inlineVar =
                { NamePtr(function, nameLength), 0 };

            // Check if it's an unknown identifier:
            typename NamePtrsMap<Value_t>::iterator nameIter =
                mData->mNamePtrs.find(inlineVar.mName);
            if(nameIter == mData->mNamePtrs.end())
            {
                const char* function2 = function + nameLength;
                SkipSpace(function2);

                // Check if ":=" follows the unknown identifier:
                if(function2[0] == ':' && function2[1] == '=')
                {
                    // Parse the expression that follows and create the
                    // inline variable:
                    function2 = CompileExpression(function2 + 2);
                    if(!function2) return 0;
                    if(*function2 != ';') return function2;

                    inlineVar.mFetchIndex = mStackPtr - 1;
                    mData->mInlineVarNames.push_back(inlineVar);

                    // Continue with the expression after the ';':
                    function = function2 + 1;
                    continue;
                }
            }
        }
        break;
    }

    return CompileExpression(function);
}

template<typename Value_t> template<bool PutFlag>
inline void FunctionParserBase<Value_t>::PushOpcodeParam
    (unsigned value)
{
    mData->mByteCode.push_back(value | (PutFlag ? FP_ParamGuardMask : 0u));
    if(PutFlag) mData->mHasByteCodeFlags = true;
}

template<typename Value_t> template<bool PutFlag>
inline void FunctionParserBase<Value_t>::PutOpcodeParamAt
    (unsigned value, unsigned offset)
{
    mData->mByteCode[offset] = value | (PutFlag ? FP_ParamGuardMask : 0u);
    if(PutFlag) mData->mHasByteCodeFlags = true;
}

//===========================================================================
// Function evaluation
//===========================================================================
template<typename Value_t>
Value_t FunctionParserBase<Value_t>::Eval(const Value_t* Vars)
{
    if(mData->mParseErrorType != FP_NO_ERROR) return Value_t(0);

    const unsigned* const byteCode = &(mData->mByteCode[0]);
    const Value_t* const immed = mData->mImmed.empty() ? 0 : &(mData->mImmed[0]);
    const unsigned byteCodeSize = unsigned(mData->mByteCode.size());
    unsigned IP, DP=0;
    int SP=-1;

#ifdef FP_USE_THREAD_SAFE_EVAL
    /* If Eval() may be called by multiple threads simultaneously,
     * then Eval() must allocate its own stack.
     */
#ifdef FP_USE_THREAD_SAFE_EVAL_WITH_ALLOCA
    /* alloca() allocates room from the hardware stack.
     * It is automatically freed when the function returns.
     */
    Value_t* const Stack = (Value_t*)alloca(mData->mStackSize*sizeof(Value_t));
#else
    /* Allocate from the heap. Ensure that it is freed
     * automatically no matter which exit path is taken.
     */
    struct AutoDealloc
    {
        Value_t* ptr;
        ~AutoDealloc() { delete[] ptr; }
    } AutoDeallocStack = { new Value_t[mData->mStackSize] };
    Value_t*& Stack = AutoDeallocStack.ptr;
#endif
#else
    /* No thread safety, so use a global stack. */
    std::vector<Value_t>& Stack = mData->mStack;
#endif

    for(IP=0; IP<byteCodeSize; ++IP)
    {
        switch(byteCode[IP])
        {
// Functions:
          case   cAbs: Stack[SP] = fp_abs(Stack[SP]); break;

          case  cAcos:
              if(IsComplexType<Value_t>::result == false
              && (Stack[SP] < Value_t(-1) || Stack[SP] > Value_t(1)))
              { mData->mEvalErrorType=4; return Value_t(0); }
              Stack[SP] = fp_acos(Stack[SP]); break;

          case cAcosh:
              if(IsComplexType<Value_t>::result == false
              && Stack[SP] < Value_t(1))
              { mData->mEvalErrorType=4; return Value_t(0); }
              Stack[SP] = fp_acosh(Stack[SP]); break;

          case  cAsin:
              if(IsComplexType<Value_t>::result == false
              && (Stack[SP] < Value_t(-1) || Stack[SP] > Value_t(1)))
              { mData->mEvalErrorType=4; return Value_t(0); }
              Stack[SP] = fp_asin(Stack[SP]); break;

          case cAsinh: Stack[SP] = fp_asinh(Stack[SP]); break;

          case  cAtan: Stack[SP] = fp_atan(Stack[SP]); break;

          case cAtan2: Stack[SP-1] = fp_atan2(Stack[SP-1], Stack[SP]);
                       --SP; break;

          case cAtanh:
              if(IsComplexType<Value_t>::result
              ?  (Stack[SP] == Value_t(-1) || Stack[SP] == Value_t(1))
              :  (Stack[SP] <= Value_t(-1) || Stack[SP] >= Value_t(1)))
              { mData->mEvalErrorType=4; return Value_t(0); }
              Stack[SP] = fp_atanh(Stack[SP]); break;

          case  cCbrt: Stack[SP] = fp_cbrt(Stack[SP]); break;

          case  cCeil: Stack[SP] = fp_ceil(Stack[SP]); break;

          case   cCos: Stack[SP] = fp_cos(Stack[SP]); break;

          case  cCosh: Stack[SP] = fp_cosh(Stack[SP]); break;

          case   cCot:
              {
                  const Value_t t = fp_tan(Stack[SP]);
                  if(t == Value_t(0))
                  { mData->mEvalErrorType=1; return Value_t(0); }
                  Stack[SP] = Value_t(1)/t; break;
              }

          case   cCsc:
              {
                  const Value_t s = fp_sin(Stack[SP]);
                  if(s == Value_t(0))
                  { mData->mEvalErrorType=1; return Value_t(0); }
                  Stack[SP] = Value_t(1)/s; break;
              }


          case   cExp: Stack[SP] = fp_exp(Stack[SP]); break;

          case   cExp2: Stack[SP] = fp_exp2(Stack[SP]); break;

          case cFloor: Stack[SP] = fp_floor(Stack[SP]); break;

          case cHypot:
              Stack[SP-1] = fp_hypot(Stack[SP-1], Stack[SP]);
              --SP; break;

          case    cIf:
                  if(fp_truth(Stack[SP--]))
                      IP += 2;
                  else
                  {
                      const unsigned* buf = &byteCode[IP+1];
                      IP = buf[0];
                      DP = buf[1];
                  }
                  break;

          case   cInt: Stack[SP] = fp_int(Stack[SP]); break;

          case   cLog:
              if(IsComplexType<Value_t>::result
               ?   Stack[SP] == Value_t(0)
               :   !(Stack[SP] > Value_t(0)))
              { mData->mEvalErrorType=3; return Value_t(0); }
              Stack[SP] = fp_log(Stack[SP]); break;

          case cLog10:
              if(IsComplexType<Value_t>::result
               ?   Stack[SP] == Value_t(0)
               :   !(Stack[SP] > Value_t(0)))
              { mData->mEvalErrorType=3; return Value_t(0); }
              Stack[SP] = fp_log10(Stack[SP]);
              break;

          case  cLog2:
              if(IsComplexType<Value_t>::result
               ?   Stack[SP] == Value_t(0)
               :   !(Stack[SP] > Value_t(0)))
              { mData->mEvalErrorType=3; return Value_t(0); }
              Stack[SP] = fp_log2(Stack[SP]);
              break;

          case   cMax: Stack[SP-1] = fp_max(Stack[SP-1], Stack[SP]);
                       --SP; break;

          case   cMin: Stack[SP-1] = fp_min(Stack[SP-1], Stack[SP]);
                       --SP; break;

          case   cPow:
              // x:Negative ^ y:NonInteger is failure,
              // except when the reciprocal of y forms an integer
              /*if(IsComplexType<Value_t>::result == false
              && Stack[SP-1] < Value_t(0) &&
                 !isInteger(Stack[SP]) &&
                 !isInteger(1.0 / Stack[SP]))
              { mEvalErrorType=3; return Value_t(0); }*/
              // x:0 ^ y:negative is failure
              if(Stack[SP-1] == Value_t(0) &&
                 Stack[SP] < Value_t(0))
              { mData->mEvalErrorType=3; return Value_t(0); }
              Stack[SP-1] = fp_pow(Stack[SP-1], Stack[SP]);
              --SP; break;

          case  cTrunc: Stack[SP] = fp_trunc(Stack[SP]); break;

          case   cSec:
              {
                  const Value_t c = fp_cos(Stack[SP]);
                  if(c == Value_t(0))
                  { mData->mEvalErrorType=1; return Value_t(0); }
                  Stack[SP] = Value_t(1)/c; break;
              }

          case   cSin: Stack[SP] = fp_sin(Stack[SP]); break;

          case  cSinh: Stack[SP] = fp_sinh(Stack[SP]); break;

          case  cSqrt:
              if(IsComplexType<Value_t>::result == false &&
                 Stack[SP] < Value_t(0))
              { mData->mEvalErrorType=2; return Value_t(0); }
              Stack[SP] = fp_sqrt(Stack[SP]); break;

          case   cTan: Stack[SP] = fp_tan(Stack[SP]); break;

          case  cTanh: Stack[SP] = fp_tanh(Stack[SP]); break;


// Misc:
          case cImmed: Stack[++SP] = immed[DP++]; break;

          case  cJump:
              {
                  const unsigned* buf = &byteCode[IP+1];
                  IP = buf[0];
                  DP = buf[1];
                  break;
              }

// Operators:
          case   cNeg: Stack[SP] = -Stack[SP]; break;
          case   cAdd: Stack[SP-1] += Stack[SP]; --SP; break;
          case   cSub: Stack[SP-1] -= Stack[SP]; --SP; break;
          case   cMul: Stack[SP-1] *= Stack[SP]; --SP; break;

          case   cDiv:
              if(Stack[SP] == Value_t(0))
              { mData->mEvalErrorType=1; return Value_t(0); }
              Stack[SP-1] /= Stack[SP]; --SP; break;

          case   cMod:
              if(Stack[SP] == Value_t(0))
              { mData->mEvalErrorType=1; return Value_t(0); }
              Stack[SP-1] = fp_mod(Stack[SP-1], Stack[SP]);
              --SP; break;

          case cEqual:
              Stack[SP-1] = fp_equal(Stack[SP-1], Stack[SP]);
              --SP; break;

          case cNEqual:
              Stack[SP-1] = fp_nequal(Stack[SP-1], Stack[SP]);
              --SP; break;

          case  cLess:
              Stack[SP-1] = fp_less(Stack[SP-1], Stack[SP]);
              --SP; break;

          case  cLessOrEq:
              Stack[SP-1] = fp_lessOrEq(Stack[SP-1], Stack[SP]);
              --SP; break;

          case cGreater:
              Stack[SP-1] = fp_less(Stack[SP], Stack[SP-1]);
              --SP; break;

          case cGreaterOrEq:
              Stack[SP-1] = fp_lessOrEq(Stack[SP], Stack[SP-1]);
              --SP; break;

          case   cNot: Stack[SP] = fp_not(Stack[SP]); break;

          case cNotNot: Stack[SP] = fp_notNot(Stack[SP]); break;

          case   cAnd:
              Stack[SP-1] = fp_and(Stack[SP-1], Stack[SP]);
              --SP; break;

          case    cOr:
              Stack[SP-1] = fp_or(Stack[SP-1], Stack[SP]);
              --SP; break;

// Degrees-radians conversion:
          case   cDeg: Stack[SP] = RadiansToDegrees(Stack[SP]); break;
          case   cRad: Stack[SP] = DegreesToRadians(Stack[SP]); break;

// User-defined function calls:
          case cFCall:
              {
                  const unsigned index = byteCode[++IP];
                  const unsigned params = mData->mFuncPtrs[index].mParams;
                  const Value_t retVal =
                      mData->mFuncPtrs[index].mRawFuncPtr ?
                      mData->mFuncPtrs[index].mRawFuncPtr(&Stack[SP-params+1]) :
                      mData->mFuncPtrs[index].mFuncWrapperPtr->callFunction
                      (&Stack[SP-params+1]);
                  SP -= int(params)-1;
                  Stack[SP] = retVal;
                  break;
              }

          case cPCall:
              {
                  unsigned index = byteCode[++IP];
                  unsigned params = mData->mFuncParsers[index].mParams;
                  Value_t retVal =
                      mData->mFuncParsers[index].mParserPtr->Eval
                      (&Stack[SP-params+1]);
                  SP -= int(params)-1;
                  Stack[SP] = retVal;
                  const int error =
                      mData->mFuncParsers[index].mParserPtr->EvalError();
                  if(error)
                  {
                      mData->mEvalErrorType = error;
                      return 0;
                  }
                  break;
              }


          case   cFetch:
              {
                  unsigned stackOffs = byteCode[++IP];
                  Stack[SP+1] = Stack[stackOffs]; ++SP;
                  break;
              }

#ifdef FP_SUPPORT_OPTIMIZER
          case   cPopNMov:
              {
                  unsigned stackOffs_target = byteCode[++IP];
                  unsigned stackOffs_source = byteCode[++IP];
                  Stack[stackOffs_target] = Stack[stackOffs_source];
                  SP = stackOffs_target;
                  break;
              }

          case  cLog2by:
              if(IsComplexType<Value_t>::result
               ?   Stack[SP-1] == Value_t(0)
               :   !(Stack[SP-1] > Value_t(0)))
              { mData->mEvalErrorType=3; return Value_t(0); }
              Stack[SP-1] = fp_log2(Stack[SP-1]) * Stack[SP];
              --SP;
              break;

          case cNop: break;
#endif // FP_SUPPORT_OPTIMIZER

          case cSinCos:
              fp_sinCos(Stack[SP], Stack[SP+1], Stack[SP]);
              ++SP;
              break;
          case cSinhCosh:
              fp_sinhCosh(Stack[SP], Stack[SP+1], Stack[SP]);
              ++SP;
              break;

          case cAbsNot:
              Stack[SP] = fp_absNot(Stack[SP]); break;
          case cAbsNotNot:
              Stack[SP] = fp_absNotNot(Stack[SP]); break;
          case cAbsAnd:
              Stack[SP-1] = fp_absAnd(Stack[SP-1], Stack[SP]);
              --SP; break;
          case cAbsOr:
              Stack[SP-1] = fp_absOr(Stack[SP-1], Stack[SP]);
              --SP; break;
          case cAbsIf:
              if(fp_absTruth(Stack[SP--]))
                  IP += 2;
              else
              {
                  const unsigned* buf = &byteCode[IP+1];
                  IP = buf[0];
                  DP = buf[1];
              }
              break;

          case   cDup: Stack[SP+1] = Stack[SP]; ++SP; break;

          case   cInv:
              if(Stack[SP] == Value_t(0))
              { mData->mEvalErrorType=1; return Value_t(0); }
              Stack[SP] = Value_t(1)/Stack[SP];
              break;

          case   cSqr:
              Stack[SP] = Stack[SP]*Stack[SP];
              break;

          case   cRDiv:
              if(Stack[SP-1] == Value_t(0))
              { mData->mEvalErrorType=1; return Value_t(0); }
              Stack[SP-1] = Stack[SP] / Stack[SP-1]; --SP; break;

          case   cRSub: Stack[SP-1] = Stack[SP] - Stack[SP-1]; --SP; break;

          case   cRSqrt:
              if(Stack[SP] == Value_t(0))
              { mData->mEvalErrorType=1; return Value_t(0); }
              Stack[SP] = Value_t(1) / fp_sqrt(Stack[SP]); break;

#ifdef FP_SUPPORT_COMPLEX_NUMBERS
          case   cReal: Stack[SP] = fp_real(Stack[SP]); break;
          case   cImag: Stack[SP] = fp_imag(Stack[SP]); break;
          case   cArg:  Stack[SP] = fp_arg(Stack[SP]); break;
          case   cConj: Stack[SP] = fp_conj(Stack[SP]); break;
          case   cPolar:
              Stack[SP-1] = fp_polar(Stack[SP-1], Stack[SP]);
              --SP; break;
#endif


// Variables:
          default:
              Stack[++SP] = Vars[byteCode[IP]-VarBegin];
        }
    }

    mData->mEvalErrorType=0;
    return Stack[SP];
}


//===========================================================================
// Variable deduction
//===========================================================================
namespace
{
    template<typename Value_t>
    int deduceVariables(FunctionParserBase<Value_t>& fParser,
                        const char* funcStr,
                        std::string& destVarString,
                        int* amountOfVariablesFound,
                        std::vector<std::string>* destVarNames,
                        bool useDegrees)
    {
        typedef std::set<std::string> StrSet;
        StrSet varNames;

        int oldIndex = -1;

        while(true)
        {
            destVarString.clear();
            for(StrSet::iterator iter = varNames.begin();
                iter != varNames.end();
                ++iter)
            {
                if(iter != varNames.begin()) destVarString += ",";
                destVarString += *iter;
            }

            const int index =
                fParser.Parse(funcStr, destVarString, useDegrees);
            if(index < 0) break;
            if(index == oldIndex) return index;

            unsigned nameLength = readIdentifier<Value_t>(funcStr + index);
            if(nameLength & 0x80000000U) return index;
            if(nameLength == 0) return index;

            varNames.insert(std::string(funcStr + index, nameLength));
            oldIndex = index;
        }

        if(amountOfVariablesFound)
            *amountOfVariablesFound = int(varNames.size());

        if(destVarNames)
            destVarNames->assign(varNames.begin(), varNames.end());

        return -1;
    }
}

template<typename Value_t>
int FunctionParserBase<Value_t>::ParseAndDeduceVariables
(const std::string& function,
 int* amountOfVariablesFound,
 bool useDegrees)
{
    std::string varString;
    return deduceVariables(*this, function.c_str(), varString,
                           amountOfVariablesFound, 0, useDegrees);
}

template<typename Value_t>
int FunctionParserBase<Value_t>::ParseAndDeduceVariables
(const std::string& function,
 std::string& resultVarString,
 int* amountOfVariablesFound,
 bool useDegrees)
{
    std::string varString;
    const int index =
        deduceVariables(*this, function.c_str(), varString,
                        amountOfVariablesFound, 0, useDegrees);
    if(index < 0) resultVarString = varString;
    return index;
}

template<typename Value_t>
int FunctionParserBase<Value_t>::ParseAndDeduceVariables
(const std::string& function,
 std::vector<std::string>& resultVars,
 bool useDegrees)
{
    std::string varString;
    std::vector<std::string> vars;
    const int index =
        deduceVariables(*this, function.c_str(), varString,
                        0, &vars, useDegrees);
    if(index < 0) resultVars.swap(vars);
    return index;
}


#ifdef FUNCTIONPARSER_SUPPORT_DEBUGGING
//===========================================================================
// Bytecode injection
//===========================================================================
template<typename Value_t>
void FunctionParserBase<Value_t>::InjectRawByteCode
(const unsigned* bytecode, unsigned bytecodeAmount,
 const Value_t* immed, unsigned immedAmount, unsigned stackSize)
{
    CopyOnWrite();

    mData->mByteCode.assign(bytecode, bytecode + bytecodeAmount);
    mData->mImmed.assign(immed, immed + immedAmount);
    mData->mStackSize = stackSize;

#ifndef FP_USE_THREAD_SAFE_EVAL
    mData->mStack.resize(stackSize);
#endif
}

//===========================================================================
// Debug output
//===========================================================================
#include <iomanip>
#include <sstream>
namespace
{
    inline void printHex(std::ostream& dest, unsigned n)
    {
        std::ios::fmtflags flags = dest.flags();
        dest.width(4); dest.fill('0'); std::hex(dest); //uppercase(dest);
        dest << n;
        dest.flags(flags);
    }

    void padLine(std::ostringstream& dest, unsigned destLength)
    {
        for(std::size_t currentLength = dest.str().length();
            currentLength < destLength;
            ++currentLength)
        {
            dest << ' ';
        }
    }

    const struct PowiMuliType
    {
        unsigned opcode_square;
        unsigned opcode_cumulate;
        unsigned opcode_invert;
        unsigned opcode_half;
        unsigned opcode_invhalf;
    } iseq_powi = {cSqr,cMul,cInv,cSqrt,cRSqrt},
      iseq_muli = {~unsigned(0), cAdd,cNeg, ~unsigned(0),~unsigned(0) };

    template<typename Value_t>
    Value_t ParsePowiMuli(
        const PowiMuliType& opcodes,
        const std::vector<unsigned>& ByteCode, unsigned& IP,
        unsigned limit,
        std::size_t factor_stack_base,
        std::vector<Value_t>& stack,
        bool IgnoreExcess)
    {
        Value_t result = Value_t(1);
        while(IP < limit)
        {
            if(ByteCode[IP] == opcodes.opcode_square)
            {
                if(!isInteger(result)) break;
                result *= Value_t(2);
                ++IP;
                continue;
            }
            if(ByteCode[IP] == opcodes.opcode_invert)
            {
                if(result < Value_t(0)) break;
                result = -result;
                ++IP;
                continue;
            }
            if(ByteCode[IP] == opcodes.opcode_half)
            {
                if(result > Value_t(0) && isEvenInteger(result))
                    break;
                if(isInteger(result * Value_t(0.5))) break;
                result *= Value_t(0.5);
                ++IP;
                continue;
            }
            if(ByteCode[IP] == opcodes.opcode_invhalf)
            {
                if(result > Value_t(0) && isEvenInteger(result))
                    break;
                if(isInteger(result * Value_t(-0.5))) break;
                result *= Value_t(-0.5);
                ++IP;
                continue;
            }

            unsigned dup_fetch_pos = IP;
            Value_t lhs = Value_t(1);

            if(ByteCode[IP] == cFetch)
            {
                unsigned index = ByteCode[++IP];
                if(index < factor_stack_base
                || std::size_t(index-factor_stack_base) >= stack.size())
                {
                    // It wasn't a powi-fetch after all
                    IP = dup_fetch_pos;
                    break;
                }
                lhs = stack[index - factor_stack_base];
                // Note: ^This assumes that cFetch of recentmost
                //        is always converted into cDup.
                goto dup_or_fetch;
            }

            if(ByteCode[IP] == cDup)
            {
                lhs = result;
                goto dup_or_fetch;

            dup_or_fetch:
                stack.push_back(result);
                ++IP;
                Value_t subexponent = ParsePowiMuli
                    (opcodes,
                     ByteCode, IP, limit,
                     factor_stack_base, stack,
                     IgnoreExcess);
                if(IP >= limit && IgnoreExcess)
                    return lhs*subexponent;
                if(IP >= limit || ByteCode[IP] != opcodes.opcode_cumulate)
                {
                    // It wasn't a powi-dup after all
                    IP = dup_fetch_pos;
                    break;
                }
                ++IP; // skip opcode_cumulate
                stack.pop_back();
                result += lhs*subexponent;
                continue;
            }
            break;
        }
        return result;
    }

    template<typename Value_t>
    Value_t ParsePowiSequence(const std::vector<unsigned>& ByteCode,
                              unsigned& IP, unsigned limit,
                              std::size_t factor_stack_base,
                              bool IgnoreExcess = false)
    {
        std::vector<Value_t> stack;
        stack.push_back(Value_t(1));
        return ParsePowiMuli(iseq_powi, ByteCode, IP, limit,
                             factor_stack_base, stack,
                             IgnoreExcess);
    }

    template<typename Value_t>
    Value_t ParseMuliSequence(const std::vector<unsigned>& ByteCode,
                              unsigned& IP, unsigned limit,
                              std::size_t factor_stack_base,
                              bool IgnoreExcess = false)
    {
        std::vector<Value_t> stack;
        stack.push_back(Value_t(1));
        return ParsePowiMuli(iseq_muli, ByteCode, IP, limit,
                             factor_stack_base, stack,
                             IgnoreExcess);
    }

    struct IfInfo
    {
        std::pair<int,std::string> condition;
        std::pair<int,std::string> thenbranch;
        unsigned endif_location;

        IfInfo() : condition(), thenbranch(), endif_location() { }
    };
}

template<typename Value_t>
void FunctionParserBase<Value_t>::PrintByteCode(std::ostream& dest,
                                                bool showExpression) const
{
    dest << "Size of stack: " << mData->mStackSize << "\n";

    std::ostringstream outputBuffer;
    std::ostream& output = (showExpression ? outputBuffer : dest);

    const std::vector<unsigned>& ByteCode = mData->mByteCode;
    const std::vector<Value_t>& Immed = mData->mImmed;

    std::vector<std::pair<int,std::string> > stack;
    std::vector<IfInfo> if_stack;

    for(unsigned IP = 0, DP = 0; IP <= ByteCode.size(); ++IP)
    {
    after_powi_or_muli:;
        std::string n;
        bool out_params = false;
        unsigned params = 2, produces = 1, opcode = 0;

        if(showExpression && !if_stack.empty() &&
          (   // Normal If termination rule:
              if_stack.back().endif_location == IP
              // This rule matches when cJumps are threaded:
           || (IP < ByteCode.size() && ByteCode[IP] == cJump
               && !if_stack.back().thenbranch.second.empty())
          ))
        {
            printHex(output, IP);
            if(if_stack.back().endif_location == IP)
                output << ": ----- (phi)";
            else
                output << ": ----- (phi+)";

            stack.resize(stack.size()+2);
            std::swap(stack[stack.size()-3], stack[stack.size()-1]);
            std::swap(if_stack.back().condition,  stack[stack.size()-3]);
            std::swap(if_stack.back().thenbranch, stack[stack.size()-2]);
            opcode = cIf;
            params = 3;
            --IP;
            if_stack.pop_back();
        }
        else
        {
            if(IP >= ByteCode.size()) break;
            opcode = ByteCode[IP];

            if(showExpression && (
                opcode == cSqr || opcode == cDup
             || opcode == cInv
             || opcode == cSqrt || opcode == cRSqrt
             || opcode == cFetch
            ))
            {
                unsigned changed_ip = IP;
                Value_t exponent =
                    ParsePowiSequence<Value_t>
                    (ByteCode, changed_ip,
                     if_stack.empty()
                     ? (unsigned)ByteCode.size()
                     : if_stack.back().endif_location,
                     stack.size()-1);
                std::string        operation_prefix;
                std::ostringstream operation_value;
                int prio = 0;
                if(exponent == Value_t(1.0))
                {
                    if(opcode != cDup) goto not_powi_or_muli;
                    Value_t factor =
                        ParseMuliSequence<Value_t>
                        (ByteCode, changed_ip,
                         if_stack.empty()
                         ? (unsigned)ByteCode.size()
                         : if_stack.back().endif_location,
                         stack.size()-1);
                    if(factor == Value_t(1) || factor == Value_t(-1))
                        goto not_powi_or_muli;
                    operation_prefix = "*";
                    operation_value << factor;
                    prio = 3;
                }
                else
                {
                    prio = 2;
                    operation_prefix = "^";
                    operation_value << exponent;
                }

                //unsigned explanation_before = changed_ip-2;
                unsigned explanation_before = changed_ip-1;

                const char* explanation_prefix = "_";
                for(const unsigned first_ip = IP; IP < changed_ip; ++IP)
                {
                    printHex(output, IP);
                    output << ": ";

                    const char* sep = "|";
                    if(first_ip+1 == changed_ip)
                    { sep = "="; explanation_prefix = " "; }
                    else if(IP   == first_ip) sep = "\\";
                    else if(IP+1 == changed_ip) sep = "/";
                    else explanation_prefix = "=";

                    switch(ByteCode[IP])
                    {
                        case cInv: output << "inv"; break;
                        case cNeg: output << "neg"; break;
                        case cDup: output << "dup"; break;
                        case cSqr: output << "sqr"; break;
                        case cMul: output << "mul"; break;
                        case cAdd: output << "add"; break;
                        case cCbrt: output << "cbrt"; break;
                        case cSqrt: output << "sqrt"; break;
                        case cRSqrt: output << "rsqrt"; break;
                        case cFetch:
                        {
                            unsigned index = ByteCode[++IP];
                            output << "cFetch(" << index << ")";
                            break;
                        }
                        default: break;
                    }
                    padLine(outputBuffer, 20);
                    output << sep;
                    if(IP >= explanation_before)
                    {
                        explanation_before = (unsigned)ByteCode.size();
                        output << explanation_prefix
                               << '[' << (stack.size()-1) << ']';
                        std::string last = stack.back().second;
                        if(stack.back().first >= prio)
                            last = "(" + last + ")";
                        output << last;
                        output << operation_prefix;
                        output << operation_value.str();
                    }
                    else
                    {
                        unsigned p = first_ip;
                        Value_t exp = operation_prefix=="^" ?
                            ParsePowiSequence<Value_t>
                            (ByteCode, p, IP+1, stack.size()-1, true) :
                            ParseMuliSequence<Value_t>
                            (ByteCode, p, IP+1, stack.size()-1, true);
                        std::string last = stack.back().second;
                        if(stack.back().first >= prio)
                            last = "(" + last + ")";
                        output << " ..." << last;
                        output << operation_prefix;
                        output << exp;
                    }
                    dest << outputBuffer.str() << std::endl;
                    outputBuffer.str("");
                }

                std::string& last = stack.back().second;
                if(stack.back().first >= prio)
                    last = "(" + last + ")";
                last += operation_prefix;
                last += operation_value.str();
                stack.back().first = prio;

                goto after_powi_or_muli;
            }
        not_powi_or_muli:;
            printHex(output, IP);
            output << ": ";

            switch(opcode)
            {
              case cIf:
              {
                  unsigned label = ByteCode[IP+1]+1;
                  output << "jz ";
                  printHex(output, label);
                  params = 1;
                  produces = 0;
                  IP += 2;

                  if_stack.resize(if_stack.size() + 1);
                  std::swap( if_stack.back().condition, stack.back() );
                  if_stack.back().endif_location = (unsigned) ByteCode.size();
                  stack.pop_back();
                  break;
              }
              case cAbsIf:
              {
                  unsigned dp    = ByteCode[IP+2];
                  unsigned label = ByteCode[IP+1]+1;
                  output << "jz_abs " << dp << ",";
                  printHex(output, label);
                  params = 1;
                  produces = 0;
                  IP += 2;

                  if_stack.resize(if_stack.size() + 1);
                  std::swap( if_stack.back().condition, stack.back() );
                  if_stack.back().endif_location = (unsigned) ByteCode.size();
                  stack.pop_back();
                  break;
              }

              case cJump:
              {
                  unsigned dp    = ByteCode[IP+2];
                  unsigned label = ByteCode[IP+1]+1;

                  if(!if_stack.empty() && !stack.empty())
                  {
                      std::swap(if_stack.back().thenbranch, stack.back());
                      if_stack.back().endif_location = label;
                      stack.pop_back();
                  }

                  output << "jump " << dp << ",";
                  printHex(output, label);
                  params = 0;
                  produces = 0;
                  IP += 2;
                  break;
              }
              case cImmed:
              {
                  if(showExpression)
                  {
                      std::ostringstream buf;
                      buf.precision(8);
                      buf << Immed[DP];
                      stack.push_back( std::make_pair(0, buf.str()) );
                  }
                  output.precision(8);
                  output << "push " << Immed[DP];
                  ++DP;
                  produces = 0;
                  break;
              }

              case cFCall:
                  {
                      const unsigned index = ByteCode[++IP];
                      params = mData->mFuncPtrs[index].mParams;
                      static std::string name;
                      name = "f:" + findName(mData->mNamePtrs, index,
                                             NameData<Value_t>::FUNC_PTR);
                      n = name.c_str();
                      out_params = true;
                      break;
                  }

              case cPCall:
                  {
                      const unsigned index = ByteCode[++IP];
                      params = mData->mFuncParsers[index].mParams;
                      static std::string name;
                      name = "p:" + findName(mData->mNamePtrs, index,
                                             NameData<Value_t>::PARSER_PTR);
                      n = name.c_str();
                      out_params = true;
                      break;
                  }

              default:
                  if(IsVarOpcode(opcode))
                  {
                      if(showExpression)
                      {
                          stack.push_back(std::make_pair(0,
                              (findName(mData->mNamePtrs, opcode,
                                        NameData<Value_t>::VARIABLE))));
                      }
                      output << "push Var" << opcode-VarBegin;
                      produces = 0;
                  }
                  else
                  {
                      switch(OPCODE(opcode))
                      {
                        case cNeg: n = "neg"; params = 1; break;
                        case cAdd: n = "add"; break;
                        case cSub: n = "sub"; break;
                        case cMul: n = "mul"; break;
                        case cDiv: n = "div"; break;
                        case cMod: n = "mod"; break;
                        case cPow: n = "pow"; break;
                        case cEqual: n = "eq"; break;
                        case cNEqual: n = "neq"; break;
                        case cLess: n = "lt"; break;
                        case cLessOrEq: n = "le"; break;
                        case cGreater: n = "gt"; break;
                        case cGreaterOrEq: n = "ge"; break;
                        case cAnd: n = "and"; break;
                        case cOr: n = "or"; break;
                        case cNot: n = "not"; params = 1; break;
                        case cNotNot: n = "notnot"; params = 1; break;
                        case cDeg: n = "deg"; params = 1; break;
                        case cRad: n = "rad"; params = 1; break;

                        case cFetch:
                        {
                            unsigned index = ByteCode[++IP];
                            if(showExpression && index < stack.size())
                                stack.push_back(stack[index]);
                            output << "cFetch(" << index << ")";
                            produces = 0;
                            break;
                        }
    #ifdef FP_SUPPORT_OPTIMIZER
                        case cLog2by: n = "log2by"; params = 2; out_params = 1; break;
                        case cPopNMov:
                        {
                            std::size_t a = ByteCode[++IP];
                            std::size_t b = ByteCode[++IP];
                            if(showExpression && b < stack.size())
                            {
                                std::pair<int, std::string> stacktop(0, "?");
                                if(b < stack.size()) stacktop = stack[b];
                                stack.resize(a);
                                stack.push_back(stacktop);
                            }
                            output << "cPopNMov(" << a << ", " << b << ")";
                            produces = 0;
                            break;
                        }
                        case cNop:
                            output << "nop"; params = 0; produces = 0;
                            break;
    #endif
                        case cSinCos:
                        {
                            if(showExpression)
                            {
                                std::pair<int, std::string> sin = stack.back();
                                std::pair<int, std::string> cos(
                                    0, "cos(" + sin.second + ")");
                                sin.first = 0;
                                sin.second = "sin(" + sin.second + ")";
                                stack.back() = sin;
                                stack.push_back(cos);
                            }
                            output << "sincos";
                            produces = 0;
                            break;
                        }
                        case cSinhCosh:
                        {
                            if(showExpression)
                            {
                                std::pair<int, std::string> sinh = stack.back();
                                std::pair<int, std::string> cosh(
                                    0, "cosh(" + sinh.second + ")");
                                sinh.first = 0;
                                sinh.second = "sinh(" + sinh.second + ")";
                                stack.back() = sinh;
                                stack.push_back(cosh);
                            }
                            output << "sinhcosh";
                            produces = 0;
                            break;
                        }
                        case cAbsAnd: n = "abs_and"; break;
                        case cAbsOr:  n = "abs_or"; break;
                        case cAbsNot: n = "abs_not"; params = 1; break;
                        case cAbsNotNot: n = "abs_notnot"; params = 1; break;
                        case cDup:
                        {
                            if(showExpression)
                                stack.push_back(stack.back());
                            output << "dup";
                            produces = 0;
                            break;
                        }
                        case cInv: n = "inv"; params = 1; break;
                        case cSqr: n = "sqr"; params = 1; break;
                        case cRDiv: n = "rdiv"; break;
                        case cRSub: n = "rsub"; break;
                        case cRSqrt: n = "rsqrt"; params = 1; break;

                        default:
                            n = Functions[opcode-cAbs].name;
                            params = Functions[opcode-cAbs].params;
                            out_params = params != 1;
                      }
                  }
            }
        }
        if(produces) output << n;
        if(out_params) output << " (" << params << ")";
        if(showExpression)
        {
            padLine(outputBuffer, 20);

            if(produces > 0)
            {
                std::ostringstream buf;
                const char *paramsep = ",", *suff = "";
                int prio = 0; bool commutative = false;
                switch(opcode)
                {
                  case cIf: buf << "if("; suff = ")";
                      break;
                  case cAbsIf: buf << "if("; suff = ")";
                      break;
                  case cOr:  prio = 6; paramsep = "|"; commutative = true;
                      break;
                  case cAnd: prio = 5; paramsep = "&"; commutative = true;
                      break;
                  case cAdd: prio = 4; paramsep = "+"; commutative = true;
                      break;
                  case cSub: prio = 4; paramsep = "-";
                      break;
                  case cMul: prio = 3; paramsep = "*"; commutative = true;
                      break;
                  case cDiv: prio = 3; paramsep = "/";
                      break;
                  case cPow: prio = 2; paramsep = "^";
                      break;
                  case cAbsOr:  prio = 6; paramsep = "|"; commutative = true;
                      break;
                  case cAbsAnd: prio = 5; paramsep = "&"; commutative = true;
                      break;
                  case cSqr: prio = 2; suff = "^2";
                      break;
                  case cNeg: buf << "(-("; suff = "))";
                      break;
                  case cNot: buf << "(!("; suff = "))";
                      break;
                  default: buf << n << '('; suff = ")";
                }

                const char* sep = "";
                for(unsigned a=0; a<params; ++a)
                {
                    buf << sep;
                    if(stack.size() + a < params)
                        buf << "?";
                    else
                    {
                        const std::pair<int,std::string>& prev =
                            stack[stack.size() - params + a];
                        if(prio > 0 && (prev.first > prio ||
                                        (prev.first==prio && !commutative)))
                            buf << '(' << prev.second << ')';
                        else
                            buf << prev.second;
                    }
                    sep = paramsep;
                }
                if(stack.size() >= params)
                    stack.resize(stack.size() - params);
                else
                    stack.clear();
                buf << suff;
                stack.push_back(std::make_pair(prio, buf.str()));
                //if(n.size() <= 4 && !out_params) padLine(outputBuffer, 20);
            }
            //padLine(outputBuffer, 20);
            output << "= ";
            if(((opcode == cIf || opcode == cAbsIf) && params != 3)
              || opcode == cJump
    #ifdef FP_SUPPORT_OPTIMIZER
              || opcode == cNop
    #endif
                )
                output << "(void)";
            else if(stack.empty())
                output << "[?] ?";
            else
                output << '[' << (stack.size()-1) << ']'
                       << stack.back().second;
        }

        if(showExpression)
        {
            dest << outputBuffer.str() << std::endl;
            outputBuffer.str("");
        }
        else
            output << std::endl;
    }
    dest << std::flush;
}
#endif


#ifndef FP_SUPPORT_OPTIMIZER
template<typename Value_t>
void FunctionParserBase<Value_t>::Optimize()
{
    // Do nothing if no optimizations are supported.
}
#endif


#define FUNCTIONPARSER_INSTANTIATE_CLASS(type) \
    template class FunctionParserBase< type >;

#ifndef FP_DISABLE_DOUBLE_TYPE
FUNCTIONPARSER_INSTANTIATE_CLASS(double)
#endif

#ifdef FP_SUPPORT_FLOAT_TYPE
FUNCTIONPARSER_INSTANTIATE_CLASS(float)
#endif

#ifdef FP_SUPPORT_LONG_DOUBLE_TYPE
FUNCTIONPARSER_INSTANTIATE_CLASS(long double)
#endif

#ifdef FP_SUPPORT_LONG_INT_TYPE
FUNCTIONPARSER_INSTANTIATE_CLASS(long)
#endif

#ifdef FP_SUPPORT_MPFR_FLOAT_TYPE
FUNCTIONPARSER_INSTANTIATE_CLASS(MpfrFloat)
#endif

#ifdef FP_SUPPORT_GMP_INT_TYPE
FUNCTIONPARSER_INSTANTIATE_CLASS(GmpInt)
#endif

#ifdef FP_SUPPORT_COMPLEX_DOUBLE_TYPE
FUNCTIONPARSER_INSTANTIATE_CLASS(std::complex<double>)
#endif

#ifdef FP_SUPPORT_COMPLEX_FLOAT_TYPE
FUNCTIONPARSER_INSTANTIATE_CLASS(std::complex<float>)
#endif

#ifdef FP_SUPPORT_COMPLEX_LONG_DOUBLE_TYPE
FUNCTIONPARSER_INSTANTIATE_CLASS(std::complex<long double>)
#endif
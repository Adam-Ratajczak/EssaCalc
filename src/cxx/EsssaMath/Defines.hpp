/*
 ******************************************************************
 *           C++ Mathematical Expression Toolkit Library          *
 *                                                                *
 * Author: Arash Partow (1999-2023)                               *
 * URL: https://www.partow.net/programming/exprtk/index.html      *
 *                                                                *
 * Copyright notice:                                              *
 * Free use of the C++ Mathematical Expression Toolkit Library is *
 * permitted under the guidelines and in accordance with the most *
 * current version of the MIT License.                            *
 * https://www.opensource.org/licenses/MIT                        *
 *                                                                *
 * Example expressions:                                           *
 * (00) (y + x / y) * (x - y / x)                                 *
 * (01) (x^2 / sin(2 * pi / y)) - x / 2                           *
 * (02) sqrt(1 - (x^2))                                           *
 * (03) 1 - sin(2 * x) + cos(pi / y)                              *
 * (04) a * exp(2 * t) + c                                        *
 * (05) if(((x + 2) == 3) and ((y + 5) <= 9),1 + w, 2 / z)        *
 * (06) (avg(x,y) <= x + y ? x - y : x * y) + 2 * pi / x          *
 * (07) z := x + sin(2 * pi / y)                                  *
 * (08) u := 2 * (pi * z) / (w := x + cos(y / pi))                *
 * (09) clamp(-1,sin(2 * pi * x) + cos(y / 2 * pi),+1)            *
 * (10) inrange(-2,m,+2) == if(({-2 <= m} and [m <= +2]),1,0)     *
 * (11) (2sin(x)cos(2y)7 + 1) == (2 * sin(x) * cos(2*y) * 7 + 1)  *
 * (12) (x ilike 's*ri?g') and [y < (3 z^7 + w)]                  *
 *                                                                *
 ******************************************************************
*/

#pragma once

#include <algorithm>
#include <cassert>
#include <cctype>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <deque>
#include <functional>
#include <iterator>
#include <limits>
#include <list>
#include <map>
#include <set>
#include <stack>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>


namespace Essa::Math
{
   #ifdef exprtk_enable_debugging
     #define exprtk_debug(params) printf params
   #else
     #define exprtk_debug(params) (void)0
   #endif

   #define exprtk_error_location             \
   "exprtk.hpp:" + details::to_str(__LINE__) \

   #if defined(__GNUC__) && (__GNUC__  >= 7)

      #define exprtk_disable_fallthrough_begin                      \
      _Pragma ("GCC diagnostic push")                               \
      _Pragma ("GCC diagnostic ignored \"-Wimplicit-fallthrough\"") \

      #define exprtk_disable_fallthrough_end                        \
      _Pragma ("GCC diagnostic pop")                                \

   #else
      #define exprtk_disable_fallthrough_begin (void)0;
      #define exprtk_disable_fallthrough_end   (void)0;
   #endif

   #if __cplusplus >= 201103L
      #define exprtk_override override
      #define exprtk_final    final
      #define exprtk_delete   = delete
   #else
      #define exprtk_override
      #define exprtk_final
      #define exprtk_delete
   #endif

   namespace details
   {
      typedef char                   char_t;
      typedef char_t*                char_ptr;
      typedef char_t const*          char_cptr;
      typedef unsigned char          uchar_t;
      typedef uchar_t*               uchar_ptr;
      typedef uchar_t const*         uchar_cptr;
      typedef unsigned long long int _uint64_t;
      typedef long long int          _int64_t;

      inline bool is_whitespace(const char_t c)
      {
         return (' '  == c) || ('\n' == c) ||
                ('\r' == c) || ('\t' == c) ||
                ('\b' == c) || ('\v' == c) ||
                ('\f' == c) ;
      }

      inline bool is_operator_char(const char_t c)
      {
         return ('+' == c) || ('-' == c) ||
                ('*' == c) || ('/' == c) ||
                ('^' == c) || ('<' == c) ||
                ('>' == c) || ('=' == c) ||
                (',' == c) || ('!' == c) ||
                ('(' == c) || (')' == c) ||
                ('[' == c) || (']' == c) ||
                ('{' == c) || ('}' == c) ||
                ('%' == c) || (':' == c) ||
                ('?' == c) || ('&' == c) ||
                ('|' == c) || (';' == c) ;
      }

      inline bool is_letter(const char_t c)
      {
         return (('a' <= c) && (c <= 'z')) ||
                (('A' <= c) && (c <= 'Z')) ;
      }

      inline bool is_digit(const char_t c)
      {
         return ('0' <= c) && (c <= '9');
      }

      inline bool is_letter_or_digit(const char_t c)
      {
         return is_letter(c) || is_digit(c);
      }

      inline bool is_left_bracket(const char_t c)
      {
         return ('(' == c) || ('[' == c) || ('{' == c);
      }

      inline bool is_right_bracket(const char_t c)
      {
         return (')' == c) || (']' == c) || ('}' == c);
      }

      inline bool is_bracket(const char_t c)
      {
         return is_left_bracket(c) || is_right_bracket(c);
      }

      inline bool is_sign(const char_t c)
      {
         return ('+' == c) || ('-' == c);
      }

      inline bool is_invalid(const char_t c)
      {
         return !is_whitespace   (c) &&
                !is_operator_char(c) &&
                !is_letter       (c) &&
                !is_digit        (c) &&
                ('.'  != c)          &&
                ('_'  != c)          &&
                ('$'  != c)          &&
                ('~'  != c)          &&
                ('\'' != c);
      }

      inline bool is_valid_string_char(const char_t c)
      {
         return std::isprint(static_cast<uchar_t>(c)) ||
                is_whitespace(c);
      }

      #ifndef exprtk_disable_caseinsensitivity
      inline void case_normalise(std::string& s)
      {
         for (std::size_t i = 0; i < s.size(); ++i)
         {
            s[i] = static_cast<std::string::value_type>(std::tolower(s[i]));
         }
      }

      inline bool imatch(const char_t c1, const char_t c2)
      {
         return std::tolower(c1) == std::tolower(c2);
      }

      inline bool imatch(const std::string& s1, const std::string& s2)
      {
         if (s1.size() == s2.size())
         {
            for (std::size_t i = 0; i < s1.size(); ++i)
            {
               if (std::tolower(s1[i]) != std::tolower(s2[i]))
               {
                  return false;
               }
            }

            return true;
         }

         return false;
      }

      struct ilesscompare
      {
         inline bool operator() (const std::string& s1, const std::string& s2) const
         {
            const std::size_t length = std::min(s1.size(),s2.size());

            for (std::size_t i = 0; i < length;  ++i)
            {
               const char_t c1 = static_cast<char_t>(std::tolower(s1[i]));
               const char_t c2 = static_cast<char_t>(std::tolower(s2[i]));

               if (c1 > c2)
                  return false;
               else if (c1 < c2)
                  return true;
            }

            return s1.size() < s2.size();
         }
      };

      #else
      inline void case_normalise(std::string&)
      {}

      inline bool imatch(const char_t c1, const char_t c2)
      {
         return c1 == c2;
      }

      inline bool imatch(const std::string& s1, const std::string& s2)
      {
         return s1 == s2;
      }

      struct ilesscompare
      {
         inline bool operator() (const std::string& s1, const std::string& s2) const
         {
            return s1 < s2;
         }
      };
      #endif

      inline bool is_valid_sf_symbol(const std::string& symbol)
      {
         // Special function: $f12 or $F34
         return (4 == symbol.size())  &&
                ('$' == symbol[0])    &&
                imatch('f',symbol[1]) &&
                is_digit(symbol[2])   &&
                is_digit(symbol[3]);
      }

      inline const char_t& front(const std::string& s)
      {
         return s[0];
      }

      inline const char_t& back(const std::string& s)
      {
         return s[s.size() - 1];
      }

      inline std::string to_str(int i)
      {
         if (0 == i)
            return std::string("0");

         std::string result;

         const int sign = (i < 0) ? -1 : 1;

         for ( ; i; i /= 10)
         {
            result += '0' + static_cast<char_t>(sign * (i % 10));
         }

         if (sign < 0)
         {
            result += '-';
         }

         std::reverse(result.begin(), result.end());

         return result;
      }

      inline std::string to_str(std::size_t i)
      {
         return to_str(static_cast<int>(i));
      }

      inline bool is_hex_digit(const uchar_t digit)
      {
         return (('0' <= digit) && (digit <= '9')) ||
                (('A' <= digit) && (digit <= 'F')) ||
                (('a' <= digit) && (digit <= 'f')) ;
      }

      inline uchar_t hex_to_bin(uchar_t h)
      {
         if (('0' <= h) && (h <= '9'))
            return (h - '0');
         else
            return static_cast<uchar_t>(std::toupper(h) - 'A');
      }

      template <typename Iterator>
      inline bool parse_hex(Iterator& itr, Iterator end,
                            char_t& result)
      {
         if (
              (end ==  (itr    ))               ||
              (end ==  (itr + 1))               ||
              (end ==  (itr + 2))               ||
              (end ==  (itr + 3))               ||
              ('0' != *(itr    ))               ||
              ('X' != std::toupper(*(itr + 1))) ||
              (!is_hex_digit(*(itr + 2)))       ||
              (!is_hex_digit(*(itr + 3)))
            )
         {
            return false;
         }

         result = hex_to_bin(static_cast<uchar_t>(*(itr + 2))) << 4 |
                  hex_to_bin(static_cast<uchar_t>(*(itr + 3))) ;

         return true;
      }

      inline bool cleanup_escapes(std::string& s)
      {
         typedef std::string::iterator str_itr_t;

         str_itr_t itr1 = s.begin();
         str_itr_t itr2 = s.begin();
         str_itr_t end  = s.end  ();

         std::size_t removal_count  = 0;

         while (end != itr1)
         {
            if ('\\' == (*itr1))
            {
               if (end == ++itr1)
               {
                  return false;
               }
               else if (parse_hex(itr1, end, *itr2))
               {
                  itr1+= 4;
                  itr2+= 1;
                  removal_count +=4;
               }
               else if ('a' == (*itr1)) { (*itr2++) = '\a'; ++itr1; ++removal_count; }
               else if ('b' == (*itr1)) { (*itr2++) = '\b'; ++itr1; ++removal_count; }
               else if ('f' == (*itr1)) { (*itr2++) = '\f'; ++itr1; ++removal_count; }
               else if ('n' == (*itr1)) { (*itr2++) = '\n'; ++itr1; ++removal_count; }
               else if ('r' == (*itr1)) { (*itr2++) = '\r'; ++itr1; ++removal_count; }
               else if ('t' == (*itr1)) { (*itr2++) = '\t'; ++itr1; ++removal_count; }
               else if ('v' == (*itr1)) { (*itr2++) = '\v'; ++itr1; ++removal_count; }
               else if ('0' == (*itr1)) { (*itr2++) = '\0'; ++itr1; ++removal_count; }
               else
               {
                  (*itr2++) = (*itr1++);
                  ++removal_count;
               }
               continue;
            }
            else
               (*itr2++) = (*itr1++);
         }

         if ((removal_count > s.size()) || (0 == removal_count))
            return false;

         s.resize(s.size() - removal_count);

         return true;
      }

      class build_string
      {
      public:

         explicit build_string(const std::size_t& initial_size = 64)
         {
            data_.reserve(initial_size);
         }

         inline build_string& operator << (const std::string& s)
         {
            data_ += s;
            return (*this);
         }

         inline build_string& operator << (char_cptr s)
         {
            data_ += std::string(s);
            return (*this);
         }

         inline operator std::string () const
         {
            return data_;
         }

         inline std::string as_string() const
         {
            return data_;
         }

      private:

         std::string data_;
      };

      static const std::string reserved_words[] =
                                  {
                                    "break",  "case",  "continue",  "default",  "false",  "for",
                                    "if", "else", "ilike",  "in", "like", "and",  "nand", "nor",
                                    "not",  "null",  "or",   "repeat", "return",  "shl",  "shr",
                                    "swap", "switch", "true",  "until", "var",  "while", "xnor",
                                    "xor", "&", "|"
                                  };

      static const std::size_t reserved_words_size = sizeof(reserved_words) / sizeof(std::string);

      static const std::string reserved_symbols[] =
                                  {
                                    "abs",  "acos",  "acosh",  "and",  "asin",  "asinh", "atan",
                                    "atanh", "atan2", "avg",  "break", "case", "ceil",  "clamp",
                                    "continue",   "cos",   "cosh",   "cot",   "csc",  "default",
                                    "deg2grad",  "deg2rad",   "equal",  "erf",   "erfc",  "exp",
                                    "expm1",  "false",   "floor",  "for",   "frac",  "grad2deg",
                                    "hypot", "iclamp", "if",  "else", "ilike", "in",  "inrange",
                                    "like",  "log",  "log10", "log2",  "logn",  "log1p", "mand",
                                    "max", "min",  "mod", "mor",  "mul", "ncdf",  "nand", "nor",
                                    "not",   "not_equal",   "null",   "or",   "pow",  "rad2deg",
                                    "repeat", "return", "root", "round", "roundn", "sec", "sgn",
                                    "shl", "shr", "sin", "sinc", "sinh", "sqrt",  "sum", "swap",
                                    "switch", "tan",  "tanh", "true",  "trunc", "until",  "var",
                                    "while", "xnor", "xor", "&", "|"
                                  };

      static const std::size_t reserved_symbols_size = sizeof(reserved_symbols) / sizeof(std::string);

      static const std::string base_function_list[] =
                                  {
                                    "abs",  "acos",  "acosh",  "asin",  "asinh", "atan", "atan2", "cos", 
                                    "cosh",   "cot",   "csc",  "default","erf",  "exp", "log",  "log10", 
                                    "log2",  "logn",  "pow", "root", "round", "roundn", "sec","sin", 
                                    "sinh", "sqrt",  "tan",  "tanh"
                                  };

      static const std::size_t base_function_list_size = sizeof(base_function_list) / sizeof(std::string);

      static const std::string logic_ops_list[] =
                                  {
                                    "and", "nand", "nor", "not", "or",  "xnor", "xor", "&", "|"
                                  };

      static const std::size_t logic_ops_list_size = sizeof(logic_ops_list) / sizeof(std::string);

      static const std::string cntrl_struct_list[] =
                                  {
                                     "if", "switch", "for", "while", "repeat", "return"
                                  };

      static const std::size_t cntrl_struct_list_size = sizeof(cntrl_struct_list) / sizeof(std::string);

      static const std::string arithmetic_ops_list[] =
                                  {
                                    "+", "-", "*", "/", "%", "^"
                                  };

      static const std::size_t arithmetic_ops_list_size = sizeof(arithmetic_ops_list) / sizeof(std::string);

      static const std::string assignment_ops_list[] =
                                  {
                                    ":=", "+=", "-=",
                                    "*=", "/=", "%="
                                  };

      static const std::size_t assignment_ops_list_size = sizeof(assignment_ops_list) / sizeof(std::string);

      static const std::string inequality_ops_list[] =
                                  {
                                     "<",  "<=", "==",
                                     "=",  "!=", "<>",
                                    ">=",  ">"
                                  };

      static const std::size_t inequality_ops_list_size = sizeof(inequality_ops_list) / sizeof(std::string);

      inline bool is_reserved_word(const std::string& symbol)
      {
         for (std::size_t i = 0; i < reserved_words_size; ++i)
         {
            if (imatch(symbol, reserved_words[i]))
            {
               return true;
            }
         }

         return false;
      }

      inline bool is_reserved_symbol(const std::string& symbol)
      {
         for (std::size_t i = 0; i < reserved_symbols_size; ++i)
         {
            if (imatch(symbol, reserved_symbols[i]))
            {
               return true;
            }
         }

         return false;
      }

      inline bool is_base_function(const std::string& function_name)
      {
         for (std::size_t i = 0; i < base_function_list_size; ++i)
         {
            if (imatch(function_name, base_function_list[i]))
            {
               return true;
            }
         }

         return false;
      }

      inline bool is_control_struct(const std::string& cntrl_strct)
      {
         for (std::size_t i = 0; i < cntrl_struct_list_size; ++i)
         {
            if (imatch(cntrl_strct, cntrl_struct_list[i]))
            {
               return true;
            }
         }

         return false;
      }

      inline bool is_logic_opr(const std::string& lgc_opr)
      {
         for (std::size_t i = 0; i < logic_ops_list_size; ++i)
         {
            if (imatch(lgc_opr, logic_ops_list[i]))
            {
               return true;
            }
         }

         return false;
      }

      struct cs_match
      {
         static inline bool cmp(const char_t c0, const char_t c1)
         {
            return (c0 == c1);
         }
      };

      struct cis_match
      {
         static inline bool cmp(const char_t c0, const char_t c1)
         {
            return (std::tolower(c0) == std::tolower(c1));
         }
      };

      template <typename Iterator, typename Compare>
      inline bool match_impl(const Iterator pattern_begin,
                             const Iterator pattern_end  ,
                             const Iterator data_begin   ,
                             const Iterator data_end     ,
                             const typename std::iterator_traits<Iterator>::value_type& zero_or_more,
                             const typename std::iterator_traits<Iterator>::value_type& exactly_one )
      {
         typedef typename std::iterator_traits<Iterator>::value_type type;

         const Iterator null_itr(0);

         Iterator p_itr  = pattern_begin;
         Iterator d_itr  = data_begin;
         Iterator np_itr = null_itr;
         Iterator nd_itr = null_itr;

         for ( ; ; )
         {
            if (p_itr != pattern_end)
            {
               const type c = *(p_itr);

               if ((data_end != d_itr) && (Compare::cmp(c,*(d_itr)) || (exactly_one == c)))
               {
                  ++d_itr;
                  ++p_itr;
                  continue;
               }
               else if (zero_or_more == c)
               {
                  while ((pattern_end != p_itr) && (zero_or_more == *(p_itr)))
                  {
                     ++p_itr;
                  }

                  const type d = *(p_itr);

                  while ((data_end != d_itr) && !(Compare::cmp(d,*(d_itr)) || (exactly_one == d)))
                  {
                     ++d_itr;
                  }

                  // set backtrack iterators
                  np_itr = p_itr - 1;
                  nd_itr = d_itr + 1;

                  continue;
               }
            }
            else if (data_end == d_itr)
               return true;

            if ((data_end == d_itr) || (null_itr == nd_itr))
                return false;

            p_itr = np_itr;
            d_itr = nd_itr;
         }

         return true;
      }

      inline bool wc_match(const std::string& wild_card,
                           const std::string& str)
      {
         return match_impl<char_cptr,cs_match>(
                   wild_card.data(),
                   wild_card.data() + wild_card.size(),
                   str.data(),
                   str.data() + str.size(),
                   '*', '?');
      }

      inline bool wc_imatch(const std::string& wild_card,
                            const std::string& str)
      {
         return match_impl<char_cptr,cis_match>(
                   wild_card.data(),
                   wild_card.data() + wild_card.size(),
                   str.data(),
                   str.data() + str.size(),
                   '*', '?');
      }

      inline bool sequence_match(const std::string& pattern,
                                 const std::string& str,
                                 std::size_t&       diff_index,
                                 char_t&            diff_value)
      {
         if (str.empty())
         {
            return ("Z" == pattern);
         }
         else if ('*' == pattern[0])
            return false;

         typedef std::string::const_iterator itr_t;

         itr_t p_itr = pattern.begin();
         itr_t s_itr = str    .begin();

         const itr_t p_end = pattern.end();
         const itr_t s_end = str    .end();

         while ((s_end != s_itr) && (p_end != p_itr))
         {
            if ('*' == (*p_itr))
            {
               const char_t target = static_cast<char_t>(std::toupper(*(p_itr - 1)));

               if ('*' == target)
               {
                  diff_index = static_cast<std::size_t>(std::distance(str.begin(),s_itr));
                  diff_value = static_cast<char_t>(std::toupper(*p_itr));

                  return false;
               }
               else
                  ++p_itr;

               while (s_itr != s_end)
               {
                  if (target != std::toupper(*s_itr))
                     break;
                  else
                     ++s_itr;
               }

               continue;
            }
            else if (
                      ('?' != *p_itr) &&
                      std::toupper(*p_itr) != std::toupper(*s_itr)
                    )
            {
               diff_index = static_cast<std::size_t>(std::distance(str.begin(),s_itr));
               diff_value = static_cast<char_t>(std::toupper(*p_itr));

               return false;
            }

            ++p_itr;
            ++s_itr;
         }

         return (
                  (s_end == s_itr) &&
                  (
                    (p_end ==  p_itr) ||
                    ('*'   == *p_itr)
                  )
                );
      }

      static const double pow10[] = {
                                      1.0,
                                      1.0E+001, 1.0E+002, 1.0E+003, 1.0E+004,
                                      1.0E+005, 1.0E+006, 1.0E+007, 1.0E+008,
                                      1.0E+009, 1.0E+010, 1.0E+011, 1.0E+012,
                                      1.0E+013, 1.0E+014, 1.0E+015, 1.0E+016
                                    };

      static const std::size_t pow10_size = sizeof(pow10) / sizeof(double);

      namespace numeric
      {
         namespace constant
         {
            static const double e       =  2.71828182845904523536028747135266249775724709369996;
            static const double pi      =  3.14159265358979323846264338327950288419716939937510;
            static const double pi_2    =  1.57079632679489661923132169163975144209858469968755;
            static const double pi_4    =  0.78539816339744830961566084581987572104929234984378;
            static const double pi_180  =  0.01745329251994329576923690768488612713442871888542;
            static const double _1_pi   =  0.31830988618379067153776752674502872406891929148091;
            static const double _2_pi   =  0.63661977236758134307553505349005744813783858296183;
            static const double _180_pi = 57.29577951308232087679815481410517033240547246656443;
            static const double log2    =  0.69314718055994530941723212145817656807550013436026;
            static const double sqrt2   =  1.41421356237309504880168872420969807856967187537695;
         }

         namespace details
         {
            struct unknown_type_tag { unknown_type_tag() {} };
            struct real_type_tag    { real_type_tag   () {} };
            struct int_type_tag     { int_type_tag    () {} };

            template <typename T>
            struct number_type
            {
               typedef unknown_type_tag type;
               number_type() {}
            };

            #define exprtk_register_real_type_tag(T)             \
            template <> struct number_type<T>                    \
            { typedef real_type_tag type; number_type() {} };    \

            #define exprtk_register_int_type_tag(T)              \
            template <> struct number_type<T>                    \
            { typedef int_type_tag type; number_type() {} };     \

            exprtk_register_real_type_tag(double     )
            exprtk_register_real_type_tag(long double)
            exprtk_register_real_type_tag(float      )

            exprtk_register_int_type_tag(short         )
            exprtk_register_int_type_tag(int           )
            exprtk_register_int_type_tag(_int64_t      )
            exprtk_register_int_type_tag(unsigned short)
            exprtk_register_int_type_tag(unsigned int  )
            exprtk_register_int_type_tag(_uint64_t     )

            #undef exprtk_register_real_type_tag
            #undef exprtk_register_int_type_tag

            template <typename T>
            struct epsilon_type {};

            #define exprtk_define_epsilon_type(Type, Epsilon)      \
            template <> struct epsilon_type<Type>                  \
            {                                                      \
               static inline Type value()                          \
               {                                                   \
                  const Type epsilon = static_cast<Type>(Epsilon); \
                  return epsilon;                                  \
               }                                                   \
            };                                                     \

            exprtk_define_epsilon_type(float      , 0.00000100000f)
            exprtk_define_epsilon_type(double     , 0.000000000100)
            exprtk_define_epsilon_type(long double, 0.000000000001)

            #undef exprtk_define_epsilon_type
         }
      }

      template <typename T> struct is_const                { enum {result = 0}; };
      template <typename T> struct is_const <const T>      { enum {result = 1}; };
      template <typename T> struct is_const_ref            { enum {result = 0}; };
      template <typename T> struct is_const_ref <const T&> { enum {result = 1}; };
      template <typename T> struct is_ref                  { enum {result = 0}; };
      template <typename T> struct is_ref<T&>              { enum {result = 1}; };
      template <typename T> struct is_ref<const T&>        { enum {result = 0}; };

      template <std::size_t State>
      struct param_to_str { static std::string result() { static const std::string r("v"); return r; } };

      template <>
      struct param_to_str<0> { static std::string result() { static const std::string r("c"); return r; } };
   }
}
#include "include/Defines.hpp"
#include <algorithm>

namespace Essa::Math
{
   namespace details
   {
      bool disable_caseinsensitivity = false;
      bool disable_string_capabilities = true;
      bool disable_break_continue = true;
      bool enable_range_runtime_checks = true;
      bool disable_superscalar_unroll = false;
      bool disable_comments = true;
      bool disable_return_statement = true;
      bool disable_enhanced_features = false;
      bool disable_sc_andor = true;
      bool disable_cardinal_pow_optimisation = false;

      bool is_whitespace(const char_t c)
      {
         return (' '  == c) || ('\n' == c) ||
                ('\r' == c) || ('\t' == c) ||
                ('\b' == c) || ('\v' == c) ||
                ('\f' == c) ;
      }

      bool is_operator_char(const char_t c)
      {
         return ('+' == c) || ('-' == c) ||
                ('*' == c) || ('/' == c) ||
                ('^' == c) || ('<' == c) ||
                ('>' == c) || ('=' == c) ||
                (',' == c) || ('!' == c) ||
                ('(' == c) || (')' == c) ||
                ('[' == c) || (']' == c) ||
                ('{' == c) || ('}' == c) ||
                (':' == c) || ('?' == c) || 
                ('&' == c) || ('|' == c) || (';' == c) ;
      }

      bool is_letter(const char_t c)
      {
         return (('a' <= c) && (c <= 'z')) ||
                (('A' <= c) && (c <= 'Z')) || c == '%';
      }

      bool is_digit(const char_t c)
      {
         return ('0' <= c) && (c <= '9');
      }

      bool is_letter_or_digit(const char_t c)
      {
         return is_letter(c) || is_digit(c) || c == '%';
      }

      bool is_left_bracket(const char_t c)
      {
         return ('(' == c) || ('[' == c) || ('{' == c);
      }

      bool is_right_bracket(const char_t c)
      {
         return (')' == c) || (']' == c) || ('}' == c);
      }

      bool is_bracket(const char_t c)
      {
         return is_left_bracket(c) || is_right_bracket(c);
      }

      bool is_sign(const char_t c)
      {
         return ('+' == c) || ('-' == c);
      }

      bool is_invalid(const char_t c)
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

      bool is_valid_string_char(const char_t c)
      {
         return std::isprint(static_cast<uchar_t>(c)) ||
                is_whitespace(c);
      }

      void case_normalise(std::string& s)
      {
         if(!disable_caseinsensitivity){
            for (std::size_t i = 0; i < s.size(); ++i)
            {
               s[i] = static_cast<std::string::value_type>(std::tolower(s[i]));
            }
         }else{

         }
      }

      bool imatch(const char_t c1, const char_t c2)
      {
         if(!disable_caseinsensitivity){
            return std::tolower(c1) == std::tolower(c2);
         }else{
            return c1 == c2;
         }
      }

      bool imatch(const std::string& s1, const std::string& s2)
      {
         if(!disable_caseinsensitivity){
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
         }else{
            return s1 == s2;
         }
      }

    bool ilesscompare::operator() (const std::string& s1, const std::string& s2) const
    {
        if(!disable_caseinsensitivity){
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
        }else{
            return s1 < s2;
        }
    }

    bool is_valid_sf_symbol(const std::string& symbol)
    {
        // Special function: $f12 or $F34
        return (4 == symbol.size())  &&
            ('$' == symbol[0])    &&
            imatch('f',symbol[1]) &&
            is_digit(symbol[2])   &&
            is_digit(symbol[3]);
    }

    const char_t& front(const std::string& s)
    {
        return s[0];
    }

    const char_t& back(const std::string& s)
    {
        return s[s.size() - 1];
    }

    std::string to_str(int i)
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

    std::string to_str(std::size_t i)
    {
        return to_str(static_cast<int>(i));
    }

    bool is_hex_digit(const uchar_t digit)
    {
       return (('0' <= digit) && (digit <= '9')) ||
              (('A' <= digit) && (digit <= 'F')) ||
              (('a' <= digit) && (digit <= 'f')) ;
    }

    uchar_t hex_to_bin(uchar_t h)
    {
        if (('0' <= h) && (h <= '9'))
            return (h - '0');
        else
            return static_cast<uchar_t>(std::toupper(h) - 'A');
    }

      bool parse_hex(str_itr_t& itr, str_itr_t end, char_t& result)
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

      bool cleanup_escapes(std::string& s)
      {

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

    build_string::build_string(const std::size_t& initial_size)
    {
        data_.reserve(initial_size);
    }

    build_string& build_string::operator << (const std::string& s)
    {
        data_ += s;
        return (*this);
    }

    build_string& build_string::operator << (char_cptr s)
    {
        data_ += std::string(s);
        return (*this);
    }

    build_string::operator std::string () const
    {
        return data_;
    }

    std::string build_string::as_string() const
    {
        return data_;
    }

    const std::string reserved_words[] =
                                  {
                                    "break",  "case",  "continue",  "default",  "false",  "for",
                                    "if", "else", "ilike",  "in", "like", "and",  "nand", "nor",
                                    "not",  "null",  "or",   "repeat", "return",  "shl",  "shr",
                                    "swap", "switch", "true",  "until", "var",  "while", "xnor",
                                    "xor", "&", "|"
                                  };

    const std::size_t reserved_words_size = sizeof(reserved_words) / sizeof(std::string);

    const std::string reserved_symbols[] =
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

    const std::size_t reserved_symbols_size = sizeof(reserved_symbols) / sizeof(std::string);

    const std::string base_function_list[] =
                                  {
                                    "abs",  "acos",  "acosh",  "and",  "asin",  "asinh", "atan",
                                    "atan2", "atanh", "avg",  "break", "case", "ceil",  "clamp",
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

    const std::size_t base_function_list_size = sizeof(base_function_list) / sizeof(std::string);

    const std::string logic_ops_list[] =
                                  {
                                    "and", "nand", "nor", "not", "or",  "xnor", "xor", "&", "|"
                                  };

    const std::size_t logic_ops_list_size = sizeof(logic_ops_list) / sizeof(std::string);

    const std::string cntrl_struct_list[] =
                                  {
                                     "if", "switch", "for", "while", "repeat", "return"
                                  };

    const std::size_t cntrl_struct_list_size = sizeof(cntrl_struct_list) / sizeof(std::string);

    const std::string arithmetic_ops_list[] =
                                  {
                                    "+", "-", "*", "/", "mod", "^"
                                  };

    const std::size_t arithmetic_ops_list_size = sizeof(arithmetic_ops_list) / sizeof(std::string);

    const std::string assignment_ops_list[] =
                                  {
                                    ":=", "+=", "-=",
                                    "*=", "/=", "%="
                                  };

    const std::size_t assignment_ops_list_size = sizeof(assignment_ops_list) / sizeof(std::string);

    const std::string inequality_ops_list[] =
                                  {
                                     "<",  "<=", "==",
                                     "=",  "!=", "<>",
                                    ">=",  ">"
                                  };

    const std::size_t inequality_ops_list_size = sizeof(inequality_ops_list) / sizeof(std::string);

      bool is_reserved_word(const std::string& symbol)
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

      bool is_reserved_symbol(const std::string& symbol)
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

      bool is_base_function(const std::string& function_name)
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

      bool is_control_struct(const std::string& cntrl_strct)
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

      bool is_logic_opr(const std::string& lgc_opr)
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

    bool cs_match::cmp(const char_t c0, const char_t c1)
    {
        return (c0 == c1);
    }
    
    bool cis_match::cmp(const char_t c0, const char_t c1)
    {
        return (std::tolower(c0) == std::tolower(c1));
    }

      bool match_impl(  const char* pattern_begin,
                        const char* pattern_end  ,
                        const char* data_begin   ,
                        const char* data_end     ,
                        const char& zero_or_more,
                        const char& exactly_one,
                        std::function<bool(char_t, char_t)> _foo)
      {
         typedef char type;

         const char* null_itr(0);

         const char* p_itr  = pattern_begin;
         const char* d_itr  = data_begin;
         const char* np_itr = null_itr;
         const char* nd_itr = null_itr;

         for ( ; ; )
         {
            if (p_itr != pattern_end)
            {
               const type c = *(p_itr);

               if ((data_end != d_itr) && (_foo(c,*(d_itr)) || (exactly_one == c)))
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

                  while ((data_end != d_itr) && !(_foo(d,*(d_itr)) || (exactly_one == d)))
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

      bool wc_match(const std::string& wild_card,
                           const std::string& str)
      {
         return match_impl(
                   wild_card.data(),
                   wild_card.data() + wild_card.size(),
                   str.data(),
                   str.data() + str.size(),
                   '*', '?', cs_match::cmp);
      }

      bool wc_imatch(const std::string& wild_card,
                            const std::string& str)
      {
         return match_impl(
                   wild_card.data(),
                   wild_card.data() + wild_card.size(),
                   str.data(),
                   str.data() + str.size(),
                   '*', '?', cis_match::cmp);
      }

      bool sequence_match(const std::string& pattern,
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

    const double pow10[] = {
                                      1.0,
                                      1.0E+001, 1.0E+002, 1.0E+003, 1.0E+004,
                                      1.0E+005, 1.0E+006, 1.0E+007, 1.0E+008,
                                      1.0E+009, 1.0E+010, 1.0E+011, 1.0E+012,
                                      1.0E+013, 1.0E+014, 1.0E+015, 1.0E+016
                                    };

    const std::size_t pow10_size = sizeof(pow10) / sizeof(double);

      namespace numeric
      {
         namespace constant
         {
            const double e       =  2.71828182845904523536028747135266249775724709369996;
            const double pi      =  3.14159265358979323846264338327950288419716939937510;
            const double pi_2    =  1.57079632679489661923132169163975144209858469968755;
            const double pi_4    =  0.78539816339744830961566084581987572104929234984378;
            const double pi_180  =  0.01745329251994329576923690768488612713442871888542;
            const double _1_pi   =  0.31830988618379067153776752674502872406891929148091;
            const double _2_pi   =  0.63661977236758134307553505349005744813783858296183;
            const double _180_pi = 57.29577951308232087679815481410517033240547246656443;
            const double log2    =  0.69314718055994530941723212145817656807550013436026;
            const double sqrt2   =  1.41421356237309504880168872420969807856967187537695;
         }
      }
   }
}
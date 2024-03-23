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

#include "Defines.hpp"
#include "Numeric.hpp"

namespace Essa::Math{
   namespace details{
      template <typename Iterator, typename T>
      inline bool string_to_type_converter_impl_ref(Iterator& itr, const Iterator end, T& result)
      {
         if (itr == end)
            return false;

         const bool negative = ('-' == (*itr));

         if (negative || ('+' == (*itr)))
         {
            if (end == ++itr)
               return false;
         }

         static const uchar_t zero = static_cast<uchar_t>('0');

         while ((end != itr) && (zero == (*itr))) ++itr;

         bool return_result = true;
         unsigned int digit = 0;
         const std::size_t length = static_cast<std::size_t>(std::distance(itr,end));

         if (length <= 4)
         {
            exprtk_disable_fallthrough_begin
            switch (length)
            {
               #ifdef exprtk_use_lut

               #define exprtk_process_digit                          \
               if ((digit = details::digit_table[(int)*itr++]) < 10) \
                  result = result * 10 + (digit);                    \
               else                                                  \
               {                                                     \
                  return_result = false;                             \
                  break;                                             \
               }                                                     \

               #else

               #define exprtk_process_digit         \
               if ((digit = (*itr++ - zero)) < 10)  \
                  result = result * T(10) + digit;  \
               else                                 \
               {                                    \
                  return_result = false;            \
                  break;                            \
               }                                    \

               #endif

               case 4 : exprtk_process_digit
               case 3 : exprtk_process_digit
               case 2 : exprtk_process_digit
               case 1 : if ((digit = (*itr - zero))>= 10)
                        {
                           digit = 0;
                           return_result = false;
                        }

               #undef exprtk_process_digit
            }
            exprtk_disable_fallthrough_end
         }
         else
            return_result = false;

         if (length && return_result)
         {
            result = result * 10 + static_cast<T>(digit);
            ++itr;
         }

         result = negative ? -result : result;
         return return_result;
      }

      template <typename Iterator, typename T>
      static inline bool parse_nan(Iterator& itr, const Iterator end, T& t)
      {
         typedef typename std::iterator_traits<Iterator>::value_type type;

         static const std::size_t nan_length = 3;

         if (std::distance(itr,end) != static_cast<int>(nan_length))
            return false;

         if (static_cast<type>('n') == (*itr))
         {
            if (
                 (static_cast<type>('a') != *(itr + 1)) ||
                 (static_cast<type>('n') != *(itr + 2))
               )
            {
               return false;
            }
         }
         else if (
                   (static_cast<type>('A') != *(itr + 1)) ||
                   (static_cast<type>('N') != *(itr + 2))
                 )
         {
            return false;
         }

         t = std::numeric_limits<T>::quiet_NaN();

         return true;
      }

      template <typename Iterator, typename T>
      static inline bool parse_inf(Iterator& itr, const Iterator end, T& t, const bool negative)
      {
         static const char_t inf_uc[] = "INFINITY";
         static const char_t inf_lc[] = "infinity";
         static const std::size_t inf_length = 8;

         const std::size_t length = static_cast<std::size_t>(std::distance(itr,end));

         if ((3 != length) && (inf_length != length))
            return false;

         char_cptr inf_itr = ('i' == (*itr)) ? inf_lc : inf_uc;

         while (end != itr)
         {
            if (*inf_itr == static_cast<char_t>(*itr))
            {
               ++itr;
               ++inf_itr;
               continue;
            }
            else
               return false;
         }

         if (negative)
            t = -std::numeric_limits<T>::infinity();
         else
            t =  std::numeric_limits<T>::infinity();

         return true;
      }

      template <typename T>
      inline bool valid_exponent(const int exponent, numeric::details::real_type_tag)
      {
         using namespace details::numeric;
         return (numeric_info<T>::min_exp <= exponent) && (exponent <= numeric_info<T>::max_exp);
      }

      template <typename Iterator, typename T>
      inline bool string_to_real(Iterator& itr_external, const Iterator end, T& t, numeric::details::real_type_tag)
      {
         if (end == itr_external) return false;

         Iterator itr = itr_external;

         T d = T(0);

         const bool negative = ('-' == (*itr));

         if (negative || '+' == (*itr))
         {
            if (end == ++itr)
               return false;
         }

         bool instate = false;

         static const char_t zero = static_cast<uchar_t>('0');

         #define parse_digit_1(d)          \
         if ((digit = (*itr - zero)) < 10) \
            { d = d * T(10) + digit; }     \
         else                              \
            { break; }                     \
         if (end == ++itr) break;          \

         #define parse_digit_2(d)          \
         if ((digit = (*itr - zero)) < 10) \
            { d = d * T(10) + digit; }     \
         else                              \
            { break; }                     \
            ++itr;                         \

         if ('.' != (*itr))
         {
            const Iterator curr = itr;

            while ((end != itr) && (zero == (*itr))) ++itr;

            while (end != itr)
            {
               unsigned int digit;
               parse_digit_1(d)
               parse_digit_1(d)
               parse_digit_2(d)
            }

            if (curr != itr) instate = true;
         }

         int exponent = 0;

         if (end != itr)
         {
            if ('.' == (*itr))
            {
               const Iterator curr = ++itr;
               T tmp_d = T(0);

               while (end != itr)
               {
                  unsigned int digit;
                  parse_digit_1(tmp_d)
                  parse_digit_1(tmp_d)
                  parse_digit_2(tmp_d)
               }

               if (curr != itr)
               {
                  instate = true;

                  const int frac_exponent = static_cast<int>(-std::distance(curr, itr));

                  if (!valid_exponent<T>(frac_exponent, numeric::details::real_type_tag()))
                     return false;

                  d += compute_pow10(tmp_d, frac_exponent);
               }

               #undef parse_digit_1
               #undef parse_digit_2
            }

            if (end != itr)
            {
               typename std::iterator_traits<Iterator>::value_type c = (*itr);

               if (('e' == c) || ('E' == c))
               {
                  int exp = 0;

                  if (!details::string_to_type_converter_impl_ref(++itr, end, exp))
                  {
                     if (end == itr)
                        return false;
                     else
                        c = (*itr);
                  }

                  exponent += exp;
               }

               if (end != itr)
               {
                  if (('f' == c) || ('F' == c) || ('l' == c) || ('L' == c))
                     ++itr;
                  else if ('#' == c)
                  {
                     if (end == ++itr)
                        return false;
                     else if (('I' <= (*itr)) && ((*itr) <= 'n'))
                     {
                        if (('i' == (*itr)) || ('I' == (*itr)))
                        {
                           return parse_inf(itr, end, t, negative);
                        }
                        else if (('n' == (*itr)) || ('N' == (*itr)))
                        {
                           return parse_nan(itr, end, t);
                        }
                        else
                           return false;
                     }
                     else
                        return false;
                  }
                  else if (('I' <= (*itr)) && ((*itr) <= 'n'))
                  {
                     if (('i' == (*itr)) || ('I' == (*itr)))
                     {
                        return parse_inf(itr, end, t, negative);
                     }
                     else if (('n' == (*itr)) || ('N' == (*itr)))
                     {
                        return parse_nan(itr, end, t);
                     }
                     else
                        return false;
                  }
                  else
                     return false;
               }
            }
         }

         if ((end != itr) || (!instate))
            return false;
         else if (!valid_exponent<T>(exponent, numeric::details::real_type_tag()))
            return false;
         else if (exponent)
            d = compute_pow10(d,exponent);

         t = static_cast<T>((negative) ? -d : d);
         return true;
      }

      template <typename Iterator, typename T>
      inline bool string_to_real(Iterator& itr_external, const Iterator end, T& t, numeric::details::complex_type_tag){
         return string_to_real(itr_external, end, t.real(), numeric::details::real_type_tag());
      }

      template <typename T>
      inline bool string_to_real(const std::string& s, T& t)
      {
         const typename numeric::details::number_type<T>::type num_type;

         char_cptr begin = s.data();
         char_cptr end   = s.data() + s.size();

         return string_to_real(begin, end, t, num_type);
      }

      template <typename T>
      struct functor_t
      {
         /*
            Note: The following definitions for Type, may require tweaking
                  based on the compiler and target architecture. The benchmark
                  should provide enough information to make the right choice.
         */
         //typedef T Type;
         //typedef const T Type;
         typedef const T& Type;
         typedef       T& RefType;
         typedef T (*qfunc_t)(Type t0, Type t1, Type t2, Type t3);
         typedef T (*tfunc_t)(Type t0, Type t1, Type t2);
         typedef T (*bfunc_t)(Type t0, Type t1);
         typedef T (*ufunc_t)(Type t0);
      };

   } // namespace details

   struct loop_runtime_check
   {
      enum loop_types
      {
         e_invalid           = 0,
         e_for_loop          = 1,
         e_while_loop        = 2,
         e_repeat_until_loop = 4,
         e_all_loops         = 7
      };

      enum violation_type
      {
          e_unknown         = 0,
          e_iteration_count = 1,
          e_timeout         = 2
      };

      loop_types loop_set;

      loop_runtime_check()
      : loop_set(e_invalid)
      , max_loop_iterations(0)
      {}

      details::_uint64_t max_loop_iterations;

      struct violation_context
      {
         loop_types loop;
         violation_type violation;
         details::_uint64_t iteration_count;
      };

      virtual bool check()
      {
         return true;
      }

      virtual void handle_runtime_violation(const violation_context&)
      {
         throw std::runtime_error("ExprTk Loop run-time violation.");
      }

      virtual ~loop_runtime_check() {}
   };

   typedef loop_runtime_check* loop_runtime_check_ptr;

   namespace lexer
   {
      struct token
      {
         enum token_type
         {
            e_none        =   0, e_error       =   1, e_err_symbol  =   2,
            e_err_number  =   3, e_err_string  =   4, e_err_sfunc   =   5,
            e_eof         =   6, e_number      =   7, e_symbol      =   8,
            e_string      =   9, e_assign      =  10, e_addass      =  11,
            e_subass      =  12, e_mulass      =  13, e_divass      =  14,
            e_modass      =  15, e_shr         =  16, e_shl         =  17,
            e_lte         =  18, e_ne          =  19, e_gte         =  20,
            e_swap        =  21, e_lt          = '<', e_gt          = '>',
            e_eq          = '=', e_rbracket    = ')', e_lbracket    = '(',
            e_rsqrbracket = ']', e_lsqrbracket = '[', e_rcrlbracket = '}',
            e_lcrlbracket = '{', e_comma       = ',', e_add         = '+',
            e_sub         = '-', e_div         = '/', e_mul         = '*',
            e_pow         = '^', e_colon       = ':', e_ternary     = '?'
         };

         token()
         : type(e_none)
         , value("")
         , position(std::numeric_limits<std::size_t>::max())
         {}

         void clear()
         {
            type     = e_none;
            value    = "";
            position = std::numeric_limits<std::size_t>::max();
         }

         template <typename Iterator>
         inline token& set_operator(const token_type tt,
                                    const Iterator begin, const Iterator end,
                                    const Iterator base_begin = Iterator(0))
         {
            type = tt;
            value.assign(begin,end);
            if (base_begin)
               position = static_cast<std::size_t>(std::distance(base_begin,begin));
            return (*this);
         }

         template <typename Iterator>
         inline token& set_symbol(const Iterator begin, const Iterator end, const Iterator base_begin = Iterator(0))
         {
            type = e_symbol;
            value.assign(begin,end);
            if (base_begin)
               position = static_cast<std::size_t>(std::distance(base_begin,begin));
            return (*this);
         }

         template <typename Iterator>
         inline token& set_numeric(const Iterator begin, const Iterator end, const Iterator base_begin = Iterator(0))
         {
            type = e_number;
            value.assign(begin,end);
            if (base_begin)
               position = static_cast<std::size_t>(std::distance(base_begin,begin));
            return (*this);
         }

         template <typename Iterator>
         inline token& set_string(const Iterator begin, const Iterator end, const Iterator base_begin = Iterator(0))
         {
            type = e_string;
            value.assign(begin,end);
            if (base_begin)
               position = static_cast<std::size_t>(std::distance(base_begin,begin));
            return (*this);
         }

         inline token& set_string(const std::string& s, const std::size_t p)
         {
            type     = e_string;
            value    = s;
            position = p;
            return (*this);
         }

         template <typename Iterator>
         inline token& set_error(const token_type et,
                                 const Iterator begin, const Iterator end,
                                 const Iterator base_begin = Iterator(0))
         {
            if (
                 (e_error      == et) ||
                 (e_err_symbol == et) ||
                 (e_err_number == et) ||
                 (e_err_string == et) ||
                 (e_err_sfunc  == et)
               )
            {
               type = et;
            }
            else
               type = e_error;

            value.assign(begin,end);

            if (base_begin)
               position = static_cast<std::size_t>(std::distance(base_begin,begin));

            return (*this);
         }

         static inline std::string to_str(token_type t)
         {
            switch (t)
            {
               case e_none        : return "NONE";
               case e_error       : return "ERROR";
               case e_err_symbol  : return "ERROR_SYMBOL";
               case e_err_number  : return "ERROR_NUMBER";
               case e_err_string  : return "ERROR_STRING";
               case e_eof         : return "EOF";
               case e_number      : return "NUMBER";
               case e_symbol      : return "SYMBOL";
               case e_string      : return "STRING";
               case e_assign      : return ":=";
               case e_addass      : return "+=";
               case e_subass      : return "-=";
               case e_mulass      : return "*=";
               case e_divass      : return "/=";
               case e_modass      : return "%=";
               case e_shr         : return ">>";
               case e_shl         : return "<<";
               case e_lte         : return "<=";
               case e_ne          : return "!=";
               case e_gte         : return ">=";
               case e_lt          : return "<";
               case e_gt          : return ">";
               case e_eq          : return "=";
               case e_rbracket    : return ")";
               case e_lbracket    : return "(";
               case e_rsqrbracket : return "]";
               case e_lsqrbracket : return "[";
               case e_rcrlbracket : return "}";
               case e_lcrlbracket : return "{";
               case e_comma       : return ",";
               case e_add         : return "+";
               case e_sub         : return "-";
               case e_div         : return "/";
               case e_mul         : return "*";
               case e_pow         : return "^";
               case e_colon       : return ":";
               case e_ternary     : return "?";
               case e_swap        : return "<=>";
               default            : return "UNKNOWN";
            }
         }

         inline bool is_error() const
         {
            return (
                     (e_error      == type) ||
                     (e_err_symbol == type) ||
                     (e_err_number == type) ||
                     (e_err_string == type) ||
                     (e_err_sfunc  == type)
                   );
         }

         token_type type;
         std::string value;
         std::size_t position;
      };
   }
}

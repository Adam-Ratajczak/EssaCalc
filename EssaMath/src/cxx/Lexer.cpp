#include "include/Lexer.hpp"
#include "include/Numeric.hpp"

namespace Essa::Math{
   namespace details{
    
      template <typename T>
      bool string_to_type_converter_impl_ref(details::char_cptr& itr, const details::char_cptr end, T& result)
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

      template <typename T>
      static bool parse_nan(details::char_cptr& itr, const details::char_cptr end, T& t)
      {
         typedef char type;

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

      template <typename T>
      static bool parse_inf(details::char_cptr& itr, const details::char_cptr end, T& t, const bool negative)
      {
         static const char_t inf_uc[] = "INF";
         static const char_t inf_lc[] = "inf";
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
      bool valid_exponent(const int exponent, numeric::details::real_type_tag)
      {
         using namespace details::numeric;
         return (numeric_info<T>::min_exp <= exponent) && (exponent <= numeric_info<T>::max_exp);
      }


      template <typename T>
      bool string_to_real(details::char_cptr& itr_external, const details::char_cptr end, T& t, numeric::details::complex_type_tag){
         if (end == itr_external) return false;

         details::char_cptr itr = itr_external;

         T d = T(0);

         const bool negative = ('-' == (*itr));

         if (negative || '+' == (*itr))
         {
            if (end == ++itr)
               return false;
         }

         bool instate = false;

         static const char_t zero = static_cast<uchar_t>('0');

         #define parse_digit_1(d)                     \
         if ((digit = (*itr - zero)) < 10)            \
            { d = T(d.real() * 10 + digit); }     \
         else                                         \
            { break; }                                \
         if (end == ++itr) break;                     \

         #define parse_digit_2(d)                     \
         if ((digit = (*itr - zero)) < 10)            \
            { d = T(d.real() * 10 + digit); }     \
         else                                         \
            { break; }                                \
            ++itr;                                    \

         if ('.' != (*itr))
         {
            const details::char_cptr curr = itr;

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
               const details::char_cptr curr = ++itr;
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
               typename std::iterator_traits<details::char_cptr>::value_type c = (*itr);

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

      template <typename T>
      bool string_to_real(details::char_cptr& itr_external, const details::char_cptr end, T& t, numeric::details::real_type_tag)
      {
         if (end == itr_external) return false;

         details::char_cptr itr = itr_external;

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
            const details::char_cptr curr = itr;

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
               const details::char_cptr curr = ++itr;
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
               typename std::iterator_traits<details::char_cptr>::value_type c = (*itr);

               if (('e' == c) || ('E' == c) || ('b' == c) || ('B' == c))
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

      template <typename T>
      bool string_to_real(details::char_cptr& itr_external, const details::char_cptr end, T& t, numeric::details::int_type_tag)
      {
         if (end == itr_external) return false;

         details::char_cptr itr = itr_external;

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
            const details::char_cptr curr = itr;

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
               const details::char_cptr curr = ++itr;
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
               typename std::iterator_traits<details::char_cptr>::value_type c = (*itr);

               if (('e' == c) || ('E' == c) || ('b' == c) || ('B' == c))
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

      template <typename T>
      bool string_to_real(const std::string& s, T& t)
      {
         const typename numeric::details::number_type<T>::type num_type;

         char_cptr begin = s.data();
         char_cptr end   = s.data() + s.size();

         return string_to_real(begin, end, t, num_type);
      }
      template bool string_to_real(const std::string&, int16_t&);
      template bool string_to_real(const std::string&, int32_t&);
      template bool string_to_real(const std::string&, int64_t&);
      template bool string_to_real(const std::string&, float&);
      template bool string_to_real(const std::string&, double&);
      template bool string_to_real(const std::string&, long double&);
      template bool string_to_real(const std::string&, std::complex<float>&);
      template bool string_to_real(const std::string&, std::complex<double>&);
      template bool string_to_real(const std::string&, std::complex<long double>&);

   }
      loop_runtime_check::loop_runtime_check()
      : loop_set(e_invalid)
      , max_loop_iterations(0)
      {}

      bool loop_runtime_check::check()
      {
         return true;
      }

      void loop_runtime_check::handle_runtime_violation(const violation_context&)
      {
         throw std::runtime_error("ExprTk Loop run-time violation.");
      }

   namespace lexer
   {
         token::token()
         : type(e_none)
         , value("")
         , position(std::numeric_limits<std::size_t>::max())
         {}

         void token::clear()
         {
            type     = e_none;
            value    = "";
            position = std::numeric_limits<std::size_t>::max();
         }

         token& token::set_operator(const token_type tt,
                                    const details::char_cptr begin, const details::char_cptr end,
                                    const details::char_cptr base_begin)
         {
            type = tt;
            value.assign(begin,end);
            if (base_begin)
               position = static_cast<std::size_t>(std::distance(base_begin,begin));
            return (*this);
         }

         token& token::set_symbol(const details::char_cptr begin, const details::char_cptr end, const details::char_cptr base_begin)
         {
            type = e_symbol;
            value.assign(begin,end);
            if (base_begin)
               position = static_cast<std::size_t>(std::distance(base_begin,begin));
            return (*this);
         }

         token& token::set_numeric(const details::char_cptr begin, const details::char_cptr end, const details::char_cptr base_begin)
         {
            type = e_number;
            value.assign(begin,end);
            if (base_begin)
               position = static_cast<std::size_t>(std::distance(base_begin,begin));
            return (*this);
         }

         token& token::set_string(const details::char_cptr begin, const details::char_cptr end, const details::char_cptr base_begin)
         {
            type = e_string;
            value.assign(begin,end);
            if (base_begin)
               position = static_cast<std::size_t>(std::distance(base_begin,begin));
            return (*this);
         }

         token& token::set_string(const std::string& s, const std::size_t p)
         {
            type     = e_string;
            value    = s;
            position = p;
            return (*this);
         }

         token& token::set_error(const token_type et,
                                 const details::char_cptr begin, const details::char_cptr end,
                                 const details::char_cptr base_begin)
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

         std::string token::to_str(token_type t)
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

         bool token::is_error() const
         {
            return (
                     (e_error      == type) ||
                     (e_err_symbol == type) ||
                     (e_err_number == type) ||
                     (e_err_string == type) ||
                     (e_err_sfunc  == type)
                   );
         }
   }
}

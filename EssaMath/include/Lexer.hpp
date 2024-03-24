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

#include "include/Defines.hpp"

namespace Essa::Math{
   namespace details{
      template <typename T>
      bool string_to_real(const std::string& s, T& t);

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

      loop_runtime_check();

      details::_uint64_t max_loop_iterations;

      struct violation_context
      {
         loop_types loop;
         violation_type violation;
         details::_uint64_t iteration_count;
      };

      virtual bool check();

      virtual void handle_runtime_violation(const violation_context&);

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

         token();

         void clear();

         token& set_operator(const token_type tt,
                                    const details::char_cptr begin, const details::char_cptr end,
                                    const details::char_cptr base_begin = details::char_cptr(0));

         token& set_symbol(const details::char_cptr begin, const details::char_cptr end, const details::char_cptr base_begin = details::char_cptr(0));

         token& set_numeric(const details::char_cptr begin, const details::char_cptr end, const details::char_cptr base_begin = details::char_cptr(0));

         token& set_string(const details::char_cptr begin, const details::char_cptr end, const details::char_cptr base_begin = details::char_cptr(0));

         token& set_string(const std::string& s, const std::size_t p);

         token& set_error(const token_type et,
                                 const details::char_cptr begin, const details::char_cptr end,
                                 const details::char_cptr base_begin = details::char_cptr(0));
         
         static std::string to_str(token_type t);

         bool is_error() const;

         token_type type;
         std::string value;
         std::size_t position;
      };
   }
}

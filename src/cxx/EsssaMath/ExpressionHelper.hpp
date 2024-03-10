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

#include "Expression.hpp"

namespace Essa::Math{
    template <typename T>
   class expression_helper
   {
   public:

      static inline bool is_constant(const expression<T>& expr)
      {
         return details::is_constant_node(expr.control_block_->expr);
      }

      static inline bool is_variable(const expression<T>& expr)
      {
         return details::is_variable_node(expr.control_block_->expr);
      }

      static inline bool is_unary(const expression<T>& expr)
      {
         return details::is_unary_node(expr.control_block_->expr);
      }

      static inline bool is_binary(const expression<T>& expr)
      {
         return details::is_binary_node(expr.control_block_->expr);
      }

      static inline bool is_function(const expression<T>& expr)
      {
         return details::is_function(expr.control_block_->expr);
      }

      static inline bool is_null(const expression<T>& expr)
      {
         return details::is_null_node(expr.control_block_->expr);
      }
   };

   template <typename T>
   inline bool is_valid(const expression<T>& expr)
   {
      return !expression_helper<T>::is_null(expr);
   }
}

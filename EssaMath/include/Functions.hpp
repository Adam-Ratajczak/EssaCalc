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

#include "ParserHelpers.hpp"


namespace Essa::Math{
   class function_traits
   {
   public:

      function_traits()
      : allow_zero_parameters_(false)
      , has_side_effects_(true)
      , min_num_args_(0)
      , max_num_args_(std::numeric_limits<std::size_t>::max())
      {}

      inline bool& allow_zero_parameters()
      {
         return allow_zero_parameters_;
      }

      inline bool& has_side_effects()
      {
         return has_side_effects_;
      }

      std::size_t& min_num_args()
      {
         return min_num_args_;
      }

      std::size_t& max_num_args()
      {
         return max_num_args_;
      }

   private:

      bool allow_zero_parameters_;
      bool has_side_effects_;
      std::size_t min_num_args_;
      std::size_t max_num_args_;
   };

   template <typename FunctionType>
   void enable_zero_parameters(FunctionType& func)
   {
      func.allow_zero_parameters() = true;

      if (0 != func.min_num_args())
      {
         func.min_num_args() = 0;
      }
   }

   template <typename FunctionType>
   void disable_zero_parameters(FunctionType& func)
   {
      func.allow_zero_parameters() = false;
   }

   template <typename FunctionType>
   void enable_has_side_effects(FunctionType& func)
   {
      func.has_side_effects() = true;
   }

   template <typename FunctionType>
   void disable_has_side_effects(FunctionType& func)
   {
      func.has_side_effects() = false;
   }

   template <typename FunctionType>
   void set_min_num_args(FunctionType& func, const std::size_t& num_args)
   {
      func.min_num_args() = num_args;

      if ((0 != func.min_num_args()) && func.allow_zero_parameters())
         func.allow_zero_parameters() = false;
   }

   template <typename FunctionType>
   void set_max_num_args(FunctionType& func, const std::size_t& num_args)
   {
      func.max_num_args() = num_args;
   }

   template <typename T>
   class ifunction : public function_traits
   {
   public:

      explicit ifunction(const std::size_t& pc)
      : param_count(pc)
      {}

      virtual ~ifunction() {}

      #define empty_method_body(N)                   \
      {                                              \
         exprtk_debug(("ifunction::operator() - Operator(" #N ") has not been overridden\n")); \
         return std::numeric_limits<T>::quiet_NaN(); \
      }                                              \

      inline virtual T operator() ()
      empty_method_body(0)

      inline virtual T operator() (const T&)
      empty_method_body(1)

      inline virtual T operator() (const T&,const T&)
      empty_method_body(2)

      inline virtual T operator() (const T&, const T&, const T&)
      empty_method_body(3)

      inline virtual T operator() (const T&, const T&, const T&, const T&)
      empty_method_body(4)

      inline virtual T operator() (const T&, const T&, const T&, const T&, const T&)
      empty_method_body(5)

      inline virtual T operator() (const T&, const T&, const T&, const T&, const T&, const T&)
      empty_method_body(6)

      inline virtual T operator() (const T&, const T&, const T&, const T&, const T&, const T&, const T&)
      empty_method_body(7)

      inline virtual T operator() (const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&)
      empty_method_body(8)

      inline virtual T operator() (const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&)
      empty_method_body(9)

      inline virtual T operator() (const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&)
      empty_method_body(10)

      inline virtual T operator() (const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&,
                                   const T&)
      empty_method_body(11)

      inline virtual T operator() (const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&,
                                   const T&, const T&)
      empty_method_body(12)

      inline virtual T operator() (const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&,
                                   const T&, const T&, const T&)
      empty_method_body(13)

      inline virtual T operator() (const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&,
                                   const T&, const T&, const T&, const T&)
      empty_method_body(14)

      inline virtual T operator() (const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&,
                                   const T&, const T&, const T&, const T&, const T&)
      empty_method_body(15)

      inline virtual T operator() (const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&,
                                   const T&, const T&, const T&, const T&, const T&, const T&)
      empty_method_body(16)

      inline virtual T operator() (const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&,
                                   const T&, const T&, const T&, const T&, const T&, const T&, const T&)
      empty_method_body(17)

      inline virtual T operator() (const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&,
                                   const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&)
      empty_method_body(18)

      inline virtual T operator() (const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&,
                                   const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&)
      empty_method_body(19)

      inline virtual T operator() (const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&,
                                   const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&, const T&)
      empty_method_body(20)

      #undef empty_method_body

      std::size_t param_count;
   };

   template <typename T>
   class ivararg_function : public function_traits
   {
   public:

      virtual ~ivararg_function() {}

      inline virtual T operator() (const std::vector<T>&)
      {
         exprtk_debug(("ivararg_function::operator() - Operator has not been overridden\n"));
         return std::numeric_limits<T>::quiet_NaN();
      }
   };

   template <typename T>
   class igeneric_function : public function_traits
   {
   public:

      enum return_type
      {
         e_rtrn_scalar   = 0,
         e_rtrn_string   = 1,
         e_rtrn_overload = 2
      };

      typedef T type;
      typedef type_store<T> generic_type;
      typedef typename generic_type::parameter_list parameter_list_t;

      igeneric_function(const std::string& param_seq = "", const return_type rtr_type = e_rtrn_scalar)
      : parameter_sequence(param_seq)
      , rtrn_type(rtr_type)
      {}

      virtual ~igeneric_function() {}

      #define igeneric_function_empty_body(N)        \
      {                                              \
         exprtk_debug(("igeneric_function::operator() - Operator(" #N ") has not been overridden\n")); \
         return std::numeric_limits<T>::quiet_NaN(); \
      }                                              \

      // f(i_0,i_1,....,i_N) --> Scalar
      inline virtual T operator() (parameter_list_t)
      igeneric_function_empty_body(1)

      // f(i_0,i_1,....,i_N) --> String
      inline virtual T operator() (std::string&, parameter_list_t)
      igeneric_function_empty_body(2)

      // f(psi,i_0,i_1,....,i_N) --> Scalar
      inline virtual T operator() (const std::size_t&, parameter_list_t)
      igeneric_function_empty_body(3)

      // f(psi,i_0,i_1,....,i_N) --> String
      inline virtual T operator() (const std::size_t&, std::string&, parameter_list_t)
      igeneric_function_empty_body(4)

      std::string parameter_sequence;
      return_type rtrn_type;
   };
}
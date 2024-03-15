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

#include "ExpressionNodes.hpp"

namespace Essa::Math{
   namespace details
   {
      exprtk_define_unary_op(abs  )
      exprtk_define_unary_op(acos )
      exprtk_define_unary_op(acosh)
      exprtk_define_unary_op(asin )
      exprtk_define_unary_op(asinh)
      exprtk_define_unary_op(atan )
      exprtk_define_unary_op(atanh)
      exprtk_define_unary_op(ceil )
      exprtk_define_unary_op(cos  )
      exprtk_define_unary_op(cosh )
      exprtk_define_unary_op(cot  )
      exprtk_define_unary_op(csc  )
      exprtk_define_unary_op(d2g  )
      exprtk_define_unary_op(d2r  )
      exprtk_define_unary_op(erf  )
      exprtk_define_unary_op(erfc )
      exprtk_define_unary_op(exp  )
      exprtk_define_unary_op(expm1)
      exprtk_define_unary_op(floor)
      exprtk_define_unary_op(frac )
      exprtk_define_unary_op(g2d  )
      exprtk_define_unary_op(log  )
      exprtk_define_unary_op(log10)
      exprtk_define_unary_op(log2 )
      exprtk_define_unary_op(log1p)
      exprtk_define_unary_op(ncdf )
      exprtk_define_unary_op(neg  )
      exprtk_define_unary_op(notl )
      exprtk_define_unary_op(pos  )
      exprtk_define_unary_op(r2d  )
      exprtk_define_unary_op(round)
      exprtk_define_unary_op(sec  )
      exprtk_define_unary_op(sgn  )
      exprtk_define_unary_op(sin  )
      exprtk_define_unary_op(sinc )
      exprtk_define_unary_op(sinh )
      exprtk_define_unary_op(sqrt )
      exprtk_define_unary_op(tan  )
      exprtk_define_unary_op(tanh )
      exprtk_define_unary_op(trunc)
      #undef exprtk_define_unary_op

      template <typename T>
      struct opr_base
      {
         typedef typename details::functor_t<T>::Type    Type;
         typedef typename details::functor_t<T>::RefType RefType;
         typedef typename details::functor_t<T> functor_t;
         typedef typename functor_t::qfunc_t    quaternary_functor_t;
         typedef typename functor_t::tfunc_t    trinary_functor_t;
         typedef typename functor_t::bfunc_t    binary_functor_t;
         typedef typename functor_t::ufunc_t    unary_functor_t;
      };

      template <typename T>
      struct add_op : public opr_base<T>
      {
         typedef typename opr_base<T>::Type    Type;
         typedef typename opr_base<T>::RefType RefType;

         static inline T process(Type t1, Type t2) { return t1 + t2; }
         static inline T process(Type t1, Type t2, Type t3) { return t1 + t2 + t3; }
         static inline void assign(RefType t1, Type t2) { t1 += t2; }
         static inline typename expression_node<T>::node_type type() { return expression_node<T>::e_add; }
         static inline details::operator_type operation() { return details::e_add; }
      };

      template <typename T>
      struct mul_op : public opr_base<T>
      {
         typedef typename opr_base<T>::Type    Type;
         typedef typename opr_base<T>::RefType RefType;

         static inline T process(Type t1, Type t2) { return t1 * t2; }
         static inline T process(Type t1, Type t2, Type t3) { return t1 * t2 * t3; }
         static inline void assign(RefType t1, Type t2) { t1 *= t2; }
         static inline typename expression_node<T>::node_type type() { return expression_node<T>::e_mul; }
         static inline details::operator_type operation() { return details::e_mul; }
      };

      template <typename T>
      struct sub_op : public opr_base<T>
      {
         typedef typename opr_base<T>::Type    Type;
         typedef typename opr_base<T>::RefType RefType;

         static inline T process(Type t1, Type t2) { return t1 - t2; }
         static inline T process(Type t1, Type t2, Type t3) { return t1 - t2 - t3; }
         static inline void assign(RefType t1, Type t2) { t1 -= t2; }
         static inline typename expression_node<T>::node_type type() { return expression_node<T>::e_sub; }
         static inline details::operator_type operation() { return details::e_sub; }
      };

      template <typename T>
      struct div_op : public opr_base<T>
      {
         typedef typename opr_base<T>::Type    Type;
         typedef typename opr_base<T>::RefType RefType;

         static inline T process(Type t1, Type t2) { return t1 / t2; }
         static inline T process(Type t1, Type t2, Type t3) { return t1 / t2 / t3; }
         static inline void assign(RefType t1, Type t2) { t1 /= t2; }
         static inline typename expression_node<T>::node_type type() { return expression_node<T>::e_div; }
         static inline details::operator_type operation() { return details::e_div; }
      };

      template <typename T>
      struct mod_op : public opr_base<T>
      {
         typedef typename opr_base<T>::Type    Type;
         typedef typename opr_base<T>::RefType RefType;

         static inline T process(Type t1, Type t2) { return numeric::modulus<T>(t1,t2); }
         static inline void assign(RefType t1, Type t2) { t1 = numeric::modulus<T>(t1,t2); }
         static inline typename expression_node<T>::node_type type() { return expression_node<T>::e_mod; }
         static inline details::operator_type operation() { return details::e_mod; }
      };

      template <typename T>
      struct pow_op : public opr_base<T>
      {
         typedef typename opr_base<T>::Type    Type;
         typedef typename opr_base<T>::RefType RefType;

         static inline T process(Type t1, Type t2) { return numeric::pow<T>(t1,t2); }
         static inline void assign(RefType t1, Type t2) { t1 = numeric::pow<T>(t1,t2); }
         static inline typename expression_node<T>::node_type type() { return expression_node<T>::e_pow; }
         static inline details::operator_type operation() { return details::e_pow; }
      };

      template <typename T>
      struct lt_op : public opr_base<T>
      {
         typedef typename opr_base<T>::Type Type;

         static inline T process(Type t1, Type t2) { return ((t1 < t2) ? T(1) : T(0)); }
         static inline T process(const std::string& t1, const std::string& t2) { return ((t1 < t2) ? T(1) : T(0)); }
         static inline typename expression_node<T>::node_type type() { return expression_node<T>::e_lt; }
         static inline details::operator_type operation() { return details::e_lt; }
      };

      template <typename T>
      struct lte_op : public opr_base<T>
      {
         typedef typename opr_base<T>::Type Type;

         static inline T process(Type t1, Type t2) { return ((t1 <= t2) ? T(1) : T(0)); }
         static inline T process(const std::string& t1, const std::string& t2) { return ((t1 <= t2) ? T(1) : T(0)); }
         static inline typename expression_node<T>::node_type type() { return expression_node<T>::e_lte; }
         static inline details::operator_type operation() { return details::e_lte; }
      };

      template <typename T>
      struct gt_op : public opr_base<T>
      {
         typedef typename opr_base<T>::Type Type;

         static inline T process(Type t1, Type t2) { return ((t1 > t2) ? T(1) : T(0)); }
         static inline T process(const std::string& t1, const std::string& t2) { return ((t1 > t2) ? T(1) : T(0)); }
         static inline typename expression_node<T>::node_type type() { return expression_node<T>::e_gt; }
         static inline details::operator_type operation() { return details::e_gt; }
      };

      template <typename T>
      struct gte_op : public opr_base<T>
      {
         typedef typename opr_base<T>::Type Type;

         static inline T process(Type t1, Type t2) { return ((t1 >= t2) ? T(1) : T(0)); }
         static inline T process(const std::string& t1, const std::string& t2) { return ((t1 >= t2) ? T(1) : T(0)); }
         static inline typename expression_node<T>::node_type type() { return expression_node<T>::e_gte; }
         static inline details::operator_type operation() { return details::e_gte; }
      };

      template <typename T>
      struct eq_op : public opr_base<T>
      {
         typedef typename opr_base<T>::Type Type;
         static inline T process(Type t1, Type t2) { return (std::equal_to<T>()(t1,t2) ? T(1) : T(0)); }
         static inline T process(const std::string& t1, const std::string& t2) { return ((t1 == t2) ? T(1) : T(0)); }
         static inline typename expression_node<T>::node_type type() { return expression_node<T>::e_eq; }
         static inline details::operator_type operation() { return details::e_eq; }
      };

      template <typename T>
      struct equal_op : public opr_base<T>
      {
         typedef typename opr_base<T>::Type Type;

         static inline T process(Type t1, Type t2) { return numeric::equal(t1,t2); }
         static inline T process(const std::string& t1, const std::string& t2) { return ((t1 == t2) ? T(1) : T(0)); }
         static inline typename expression_node<T>::node_type type() { return expression_node<T>::e_eq; }
         static inline details::operator_type operation() { return details::e_equal; }
      };

      template <typename T>
      struct ne_op : public opr_base<T>
      {
         typedef typename opr_base<T>::Type Type;

         static inline T process(Type t1, Type t2) { return (std::not_equal_to<T>()(t1,t2) ? T(1) : T(0)); }
         static inline T process(const std::string& t1, const std::string& t2) { return ((t1 != t2) ? T(1) : T(0)); }
         static inline typename expression_node<T>::node_type type() { return expression_node<T>::e_ne; }
         static inline details::operator_type operation() { return details::e_ne; }
      };

      template <typename T>
      struct and_op : public opr_base<T>
      {
         typedef typename opr_base<T>::Type Type;

         static inline T process(Type t1, Type t2) { return (details::is_true(t1) && details::is_true(t2)) ? T(1) : T(0); }
         static inline typename expression_node<T>::node_type type() { return expression_node<T>::e_and; }
         static inline details::operator_type operation() { return details::e_and; }
      };

      template <typename T>
      struct nand_op : public opr_base<T>
      {
         typedef typename opr_base<T>::Type Type;

         static inline T process(Type t1, Type t2) { return (details::is_true(t1) && details::is_true(t2)) ? T(0) : T(1); }
         static inline typename expression_node<T>::node_type type() { return expression_node<T>::e_nand; }
         static inline details::operator_type operation() { return details::e_nand; }
      };

      template <typename T>
      struct or_op : public opr_base<T>
      {
         typedef typename opr_base<T>::Type Type;

         static inline T process(Type t1, Type t2) { return (details::is_true(t1) || details::is_true(t2)) ? T(1) : T(0); }
         static inline typename expression_node<T>::node_type type() { return expression_node<T>::e_or; }
         static inline details::operator_type operation() { return details::e_or; }
      };

      template <typename T>
      struct nor_op : public opr_base<T>
      {
         typedef typename opr_base<T>::Type Type;

         static inline T process(Type t1, Type t2) { return (details::is_true(t1) || details::is_true(t2)) ? T(0) : T(1); }
         static inline typename expression_node<T>::node_type type() { return expression_node<T>::e_nor; }
         static inline details::operator_type operation() { return details::e_nor; }
      };

      template <typename T>
      struct xor_op : public opr_base<T>
      {
         typedef typename opr_base<T>::Type Type;

         static inline T process(Type t1, Type t2) { return numeric::xor_opr<T>(t1,t2); }
         static inline typename expression_node<T>::node_type type() { return expression_node<T>::e_nor; }
         static inline details::operator_type operation() { return details::e_xor; }
      };

      template <typename T>
      struct xnor_op : public opr_base<T>
      {
         typedef typename opr_base<T>::Type Type;

         static inline T process(Type t1, Type t2) { return numeric::xnor_opr<T>(t1,t2); }
         static inline typename expression_node<T>::node_type type() { return expression_node<T>::e_nor; }
         static inline details::operator_type operation() { return details::e_xnor; }
      };

      template <typename T>
      struct in_op : public opr_base<T>
      {
         typedef typename opr_base<T>::Type Type;

         static inline T process(const T&, const T&) { return std::numeric_limits<T>::quiet_NaN(); }
         static inline T process(const std::string& t1, const std::string& t2) { return ((std::string::npos != t2.find(t1)) ? T(1) : T(0)); }
         static inline typename expression_node<T>::node_type type() { return expression_node<T>::e_in; }
         static inline details::operator_type operation() { return details::e_in; }
      };

      template <typename T>
      struct like_op : public opr_base<T>
      {
         typedef typename opr_base<T>::Type Type;

         static inline T process(const T&, const T&) { return std::numeric_limits<T>::quiet_NaN(); }
         static inline T process(const std::string& t1, const std::string& t2) { return (details::wc_match(t2,t1) ? T(1) : T(0)); }
         static inline typename expression_node<T>::node_type type() { return expression_node<T>::e_like; }
         static inline details::operator_type operation() { return details::e_like; }
      };

      template <typename T>
      struct ilike_op : public opr_base<T>
      {
         typedef typename opr_base<T>::Type Type;

         static inline T process(const T&, const T&) { return std::numeric_limits<T>::quiet_NaN(); }
         static inline T process(const std::string& t1, const std::string& t2) { return (details::wc_imatch(t2,t1) ? T(1) : T(0)); }
         static inline typename expression_node<T>::node_type type() { return expression_node<T>::e_ilike; }
         static inline details::operator_type operation() { return details::e_ilike; }
      };

      template <typename T>
      struct inrange_op : public opr_base<T>
      {
         typedef typename opr_base<T>::Type Type;

         static inline T process(const T& t0, const T& t1, const T& t2) { return ((t0 <= t1) && (t1 <= t2)) ? T(1) : T(0); }
         static inline T process(const std::string& t0, const std::string& t1, const std::string& t2)
         {
            return ((t0 <= t1) && (t1 <= t2)) ? T(1) : T(0);
         }
         static inline typename expression_node<T>::node_type type() { return expression_node<T>::e_inranges; }
         static inline details::operator_type operation() { return details::e_inrange; }
      };

      template <typename T>
      inline T value(details::expression_node<T>* n)
      {
         return n->value();
      }

      template <typename T>
      inline T value(std::pair<details::expression_node<T>*,bool> n)
      {
         return n.first->value();
      }

      template <typename T>
      inline T value(const T* t)
      {
         return (*t);
      }

      template <typename T>
      inline T value(const T& t)
      {
         return t;
      }

      template <typename T>
      struct vararg_add_op : public opr_base<T>
      {
         typedef typename opr_base<T>::Type Type;

         template <typename Type,
                   typename Allocator,
                   template <typename, typename> class Sequence>
         static inline T process(const Sequence<Type,Allocator>& arg_list)
         {
            switch (arg_list.size())
            {
               case 0  : return T(0);
               case 1  : return process_1(arg_list);
               case 2  : return process_2(arg_list);
               case 3  : return process_3(arg_list);
               case 4  : return process_4(arg_list);
               case 5  : return process_5(arg_list);
               default :
                         {
                            T result = T(0);

                            for (std::size_t i = 0; i < arg_list.size(); ++i)
                            {
                              result += value(arg_list[i]);
                            }

                            return result;
                         }
            }
         }

         template <typename Sequence>
         static inline T process_1(const Sequence& arg_list)
         {
            return value(arg_list[0]);
         }

         template <typename Sequence>
         static inline T process_2(const Sequence& arg_list)
         {
            return value(arg_list[0]) + value(arg_list[1]);
         }

         template <typename Sequence>
         static inline T process_3(const Sequence& arg_list)
         {
            return value(arg_list[0]) + value(arg_list[1]) +
                   value(arg_list[2]) ;
         }

         template <typename Sequence>
         static inline T process_4(const Sequence& arg_list)
         {
            return value(arg_list[0]) + value(arg_list[1]) +
                   value(arg_list[2]) + value(arg_list[3]) ;
         }

         template <typename Sequence>
         static inline T process_5(const Sequence& arg_list)
         {
            return value(arg_list[0]) + value(arg_list[1]) +
                   value(arg_list[2]) + value(arg_list[3]) +
                   value(arg_list[4]) ;
         }
      };

      template <typename T>
      struct vararg_mul_op : public opr_base<T>
      {
         typedef typename opr_base<T>::Type Type;

         template <typename Type,
                   typename Allocator,
                   template <typename, typename> class Sequence>
         static inline T process(const Sequence<Type,Allocator>& arg_list)
         {
            switch (arg_list.size())
            {
               case 0  : return T(0);
               case 1  : return process_1(arg_list);
               case 2  : return process_2(arg_list);
               case 3  : return process_3(arg_list);
               case 4  : return process_4(arg_list);
               case 5  : return process_5(arg_list);
               default :
                         {
                            T result = T(value(arg_list[0]));

                            for (std::size_t i = 1; i < arg_list.size(); ++i)
                            {
                               result *= value(arg_list[i]);
                            }

                            return result;
                         }
            }
         }

         template <typename Sequence>
         static inline T process_1(const Sequence& arg_list)
         {
            return value(arg_list[0]);
         }

         template <typename Sequence>
         static inline T process_2(const Sequence& arg_list)
         {
            return value(arg_list[0]) * value(arg_list[1]);
         }

         template <typename Sequence>
         static inline T process_3(const Sequence& arg_list)
         {
            return value(arg_list[0]) * value(arg_list[1]) *
                   value(arg_list[2]) ;
         }

         template <typename Sequence>
         static inline T process_4(const Sequence& arg_list)
         {
            return value(arg_list[0]) * value(arg_list[1]) *
                   value(arg_list[2]) * value(arg_list[3]) ;
         }

         template <typename Sequence>
         static inline T process_5(const Sequence& arg_list)
         {
            return value(arg_list[0]) * value(arg_list[1]) *
                   value(arg_list[2]) * value(arg_list[3]) *
                   value(arg_list[4]) ;
         }
      };

      template <typename T>
      struct vararg_avg_op : public opr_base<T>
      {
         typedef typename opr_base<T>::Type Type;

         template <typename Type,
                   typename Allocator,
                   template <typename, typename> class Sequence>
         static inline T process(const Sequence<Type,Allocator>& arg_list)
         {
            switch (arg_list.size())
            {
               case 0  : return T(0);
               case 1  : return process_1(arg_list);
               case 2  : return process_2(arg_list);
               case 3  : return process_3(arg_list);
               case 4  : return process_4(arg_list);
               case 5  : return process_5(arg_list);
               default : return vararg_add_op<T>::process(arg_list) / T(arg_list.size());
            }
         }

         template <typename Sequence>
         static inline T process_1(const Sequence& arg_list)
         {
            return value(arg_list[0]);
         }

         template <typename Sequence>
         static inline T process_2(const Sequence& arg_list)
         {
            return (value(arg_list[0]) + value(arg_list[1])) / T(2);
         }

         template <typename Sequence>
         static inline T process_3(const Sequence& arg_list)
         {
            return (value(arg_list[0]) + value(arg_list[1]) + value(arg_list[2])) / T(3);
         }

         template <typename Sequence>
         static inline T process_4(const Sequence& arg_list)
         {
            return (value(arg_list[0]) + value(arg_list[1]) +
                    value(arg_list[2]) + value(arg_list[3])) / T(4);
         }

         template <typename Sequence>
         static inline T process_5(const Sequence& arg_list)
         {
            return (value(arg_list[0]) + value(arg_list[1]) +
                    value(arg_list[2]) + value(arg_list[3]) +
                    value(arg_list[4])) / T(5);
         }
      };

      template <typename T>
      struct vararg_min_op : public opr_base<T>
      {
         typedef typename opr_base<T>::Type Type;

         template <typename Type,
                   typename Allocator,
                   template <typename, typename> class Sequence>
         static inline T process(const Sequence<Type,Allocator>& arg_list)
         {
            switch (arg_list.size())
            {
               case 0  : return T(0);
               case 1  : return process_1(arg_list);
               case 2  : return process_2(arg_list);
               case 3  : return process_3(arg_list);
               case 4  : return process_4(arg_list);
               case 5  : return process_5(arg_list);
               default :
                         {
                            T result = T(value(arg_list[0]));

                            for (std::size_t i = 1; i < arg_list.size(); ++i)
                            {
                               const T v = value(arg_list[i]);

                               if (v < result)
                                  result = v;
                            }

                            return result;
                         }
            }
         }

         template <typename Sequence>
         static inline T process_1(const Sequence& arg_list)
         {
            return value(arg_list[0]);
         }

         template <typename Sequence>
         static inline T process_2(const Sequence& arg_list)
         {
            return std::min<T>(value(arg_list[0]),value(arg_list[1]));
         }

         template <typename Sequence>
         static inline T process_3(const Sequence& arg_list)
         {
            return std::min<T>(std::min<T>(value(arg_list[0]),value(arg_list[1])),value(arg_list[2]));
         }

         template <typename Sequence>
         static inline T process_4(const Sequence& arg_list)
         {
            return std::min<T>(
                        std::min<T>(value(arg_list[0]), value(arg_list[1])),
                        std::min<T>(value(arg_list[2]), value(arg_list[3])));
         }

         template <typename Sequence>
         static inline T process_5(const Sequence& arg_list)
         {
            return std::min<T>(
                   std::min<T>(std::min<T>(value(arg_list[0]), value(arg_list[1])),
                               std::min<T>(value(arg_list[2]), value(arg_list[3]))),
                               value(arg_list[4]));
         }
      };

      template <typename T>
      struct vararg_max_op : public opr_base<T>
      {
         typedef typename opr_base<T>::Type Type;

         template <typename Type,
                   typename Allocator,
                   template <typename, typename> class Sequence>
         static inline T process(const Sequence<Type,Allocator>& arg_list)
         {
            switch (arg_list.size())
            {
               case 0  : return T(0);
               case 1  : return process_1(arg_list);
               case 2  : return process_2(arg_list);
               case 3  : return process_3(arg_list);
               case 4  : return process_4(arg_list);
               case 5  : return process_5(arg_list);
               default :
                         {
                            T result = T(value(arg_list[0]));

                            for (std::size_t i = 1; i < arg_list.size(); ++i)
                            {
                               const T v = value(arg_list[i]);

                               if (v > result)
                                  result = v;
                            }

                            return result;
                         }
            }
         }

         template <typename Sequence>
         static inline T process_1(const Sequence& arg_list)
         {
            return value(arg_list[0]);
         }

         template <typename Sequence>
         static inline T process_2(const Sequence& arg_list)
         {
            return std::max<T>(value(arg_list[0]),value(arg_list[1]));
         }

         template <typename Sequence>
         static inline T process_3(const Sequence& arg_list)
         {
            return std::max<T>(std::max<T>(value(arg_list[0]),value(arg_list[1])),value(arg_list[2]));
         }

         template <typename Sequence>
         static inline T process_4(const Sequence& arg_list)
         {
            return std::max<T>(
                        std::max<T>(value(arg_list[0]), value(arg_list[1])),
                        std::max<T>(value(arg_list[2]), value(arg_list[3])));
         }

         template <typename Sequence>
         static inline T process_5(const Sequence& arg_list)
         {
            return std::max<T>(
                   std::max<T>(std::max<T>(value(arg_list[0]), value(arg_list[1])),
                               std::max<T>(value(arg_list[2]), value(arg_list[3]))),
                               value(arg_list[4]));
         }
      };

      template <typename T>
      struct vararg_mand_op : public opr_base<T>
      {
         typedef typename opr_base<T>::Type Type;

         template <typename Type,
                   typename Allocator,
                   template <typename, typename> class Sequence>
         static inline T process(const Sequence<Type,Allocator>& arg_list)
         {
            switch (arg_list.size())
            {
               case 1  : return process_1(arg_list);
               case 2  : return process_2(arg_list);
               case 3  : return process_3(arg_list);
               case 4  : return process_4(arg_list);
               case 5  : return process_5(arg_list);
               default :
                         {
                            for (std::size_t i = 0; i < arg_list.size(); ++i)
                            {
                               if (std::equal_to<T>()(T(0), value(arg_list[i])))
                                  return T(0);
                            }

                            return T(1);
                         }
            }
         }

         template <typename Sequence>
         static inline T process_1(const Sequence& arg_list)
         {
            return std::not_equal_to<T>()
                      (T(0), value(arg_list[0])) ? T(1) : T(0);
         }

         template <typename Sequence>
         static inline T process_2(const Sequence& arg_list)
         {
            return (
                     std::not_equal_to<T>()(T(0), value(arg_list[0])) &&
                     std::not_equal_to<T>()(T(0), value(arg_list[1]))
                   ) ? T(1) : T(0);
         }

         template <typename Sequence>
         static inline T process_3(const Sequence& arg_list)
         {
            return (
                     std::not_equal_to<T>()(T(0), value(arg_list[0])) &&
                     std::not_equal_to<T>()(T(0), value(arg_list[1])) &&
                     std::not_equal_to<T>()(T(0), value(arg_list[2]))
                   ) ? T(1) : T(0);
         }

         template <typename Sequence>
         static inline T process_4(const Sequence& arg_list)
         {
            return (
                     std::not_equal_to<T>()(T(0), value(arg_list[0])) &&
                     std::not_equal_to<T>()(T(0), value(arg_list[1])) &&
                     std::not_equal_to<T>()(T(0), value(arg_list[2])) &&
                     std::not_equal_to<T>()(T(0), value(arg_list[3]))
                   ) ? T(1) : T(0);
         }

         template <typename Sequence>
         static inline T process_5(const Sequence& arg_list)
         {
            return (
                     std::not_equal_to<T>()(T(0), value(arg_list[0])) &&
                     std::not_equal_to<T>()(T(0), value(arg_list[1])) &&
                     std::not_equal_to<T>()(T(0), value(arg_list[2])) &&
                     std::not_equal_to<T>()(T(0), value(arg_list[3])) &&
                     std::not_equal_to<T>()(T(0), value(arg_list[4]))
                   ) ? T(1) : T(0);
         }
      };

      template <typename T>
      struct vararg_mor_op : public opr_base<T>
      {
         typedef typename opr_base<T>::Type Type;

         template <typename Type,
                   typename Allocator,
                   template <typename, typename> class Sequence>
         static inline T process(const Sequence<Type,Allocator>& arg_list)
         {
            switch (arg_list.size())
            {
               case 1  : return process_1(arg_list);
               case 2  : return process_2(arg_list);
               case 3  : return process_3(arg_list);
               case 4  : return process_4(arg_list);
               case 5  : return process_5(arg_list);
               default :
                         {
                            for (std::size_t i = 0; i < arg_list.size(); ++i)
                            {
                               if (std::not_equal_to<T>()(T(0), value(arg_list[i])))
                                  return T(1);
                            }

                            return T(0);
                         }
            }
         }

         template <typename Sequence>
         static inline T process_1(const Sequence& arg_list)
         {
            return std::not_equal_to<T>()
                      (T(0), value(arg_list[0])) ? T(1) : T(0);
         }

         template <typename Sequence>
         static inline T process_2(const Sequence& arg_list)
         {
            return (
                     std::not_equal_to<T>()(T(0), value(arg_list[0])) ||
                     std::not_equal_to<T>()(T(0), value(arg_list[1]))
                   ) ? T(1) : T(0);
         }

         template <typename Sequence>
         static inline T process_3(const Sequence& arg_list)
         {
            return (
                     std::not_equal_to<T>()(T(0), value(arg_list[0])) ||
                     std::not_equal_to<T>()(T(0), value(arg_list[1])) ||
                     std::not_equal_to<T>()(T(0), value(arg_list[2]))
                   ) ? T(1) : T(0);
         }

         template <typename Sequence>
         static inline T process_4(const Sequence& arg_list)
         {
            return (
                     std::not_equal_to<T>()(T(0), value(arg_list[0])) ||
                     std::not_equal_to<T>()(T(0), value(arg_list[1])) ||
                     std::not_equal_to<T>()(T(0), value(arg_list[2])) ||
                     std::not_equal_to<T>()(T(0), value(arg_list[3]))
                   ) ? T(1) : T(0);
         }

         template <typename Sequence>
         static inline T process_5(const Sequence& arg_list)
         {
            return (
                     std::not_equal_to<T>()(T(0), value(arg_list[0])) ||
                     std::not_equal_to<T>()(T(0), value(arg_list[1])) ||
                     std::not_equal_to<T>()(T(0), value(arg_list[2])) ||
                     std::not_equal_to<T>()(T(0), value(arg_list[3])) ||
                     std::not_equal_to<T>()(T(0), value(arg_list[4]))
                   ) ? T(1) : T(0);
         }
      };

      template <typename T>
      struct vararg_multi_op : public opr_base<T>
      {
         typedef typename opr_base<T>::Type Type;

         template <typename Type,
                   typename Allocator,
                   template <typename, typename> class Sequence>
         static inline T process(const Sequence<Type,Allocator>& arg_list)
         {
            switch (arg_list.size())
            {
               case 0  : return std::numeric_limits<T>::quiet_NaN();
               case 1  : return process_1(arg_list);
               case 2  : return process_2(arg_list);
               case 3  : return process_3(arg_list);
               case 4  : return process_4(arg_list);
               case 5  : return process_5(arg_list);
               case 6  : return process_6(arg_list);
               case 7  : return process_7(arg_list);
               case 8  : return process_8(arg_list);
               default :
                         {
                            for (std::size_t i = 0; i < (arg_list.size() - 1); ++i)
                            {
                               value(arg_list[i]);
                            }

                            return value(arg_list.back());
                         }
            }
         }

         template <typename Sequence>
         static inline T process_1(const Sequence& arg_list)
         {
            return value(arg_list[0]);
         }

         template <typename Sequence>
         static inline T process_2(const Sequence& arg_list)
         {
                   value(arg_list[0]);
            return value(arg_list[1]);
         }

         template <typename Sequence>
         static inline T process_3(const Sequence& arg_list)
         {
                   value(arg_list[0]);
                   value(arg_list[1]);
            return value(arg_list[2]);
         }

         template <typename Sequence>
         static inline T process_4(const Sequence& arg_list)
         {
                   value(arg_list[0]);
                   value(arg_list[1]);
                   value(arg_list[2]);
            return value(arg_list[3]);
         }

         template <typename Sequence>
         static inline T process_5(const Sequence& arg_list)
         {
                   value(arg_list[0]);
                   value(arg_list[1]);
                   value(arg_list[2]);
                   value(arg_list[3]);
            return value(arg_list[4]);
         }

         template <typename Sequence>
         static inline T process_6(const Sequence& arg_list)
         {
                   value(arg_list[0]);
                   value(arg_list[1]);
                   value(arg_list[2]);
                   value(arg_list[3]);
                   value(arg_list[4]);
            return value(arg_list[5]);
         }

         template <typename Sequence>
         static inline T process_7(const Sequence& arg_list)
         {
                   value(arg_list[0]);
                   value(arg_list[1]);
                   value(arg_list[2]);
                   value(arg_list[3]);
                   value(arg_list[4]);
                   value(arg_list[5]);
            return value(arg_list[6]);
         }

         template <typename Sequence>
         static inline T process_8(const Sequence& arg_list)
         {
                   value(arg_list[0]);
                   value(arg_list[1]);
                   value(arg_list[2]);
                   value(arg_list[3]);
                   value(arg_list[4]);
                   value(arg_list[5]);
                   value(arg_list[6]);
            return value(arg_list[7]);
         }
      };

      template <typename T>
      struct vec_add_op
      {
         typedef vector_interface<T>* ivector_ptr;

         static inline T process(const ivector_ptr v)
         {
            const T* vec = v->vec()->vds().data();
            const std::size_t vec_size = v->vec()->vds().size();

            loop_unroll::details lud(vec_size);

            if (vec_size <= static_cast<std::size_t>(lud.batch_size))
            {
               T result = T(0);
               int i    = 0;

               exprtk_disable_fallthrough_begin
               switch (vec_size)
               {
                  #define case_stmt(N)         \
                  case N : result += vec[i++]; \

                  case_stmt(16) case_stmt(15)
                  case_stmt(14) case_stmt(13)
                  case_stmt(12) case_stmt(11)
                  case_stmt(10) case_stmt( 9)
                  case_stmt( 8) case_stmt( 7)
                  case_stmt( 6) case_stmt( 5)
                  case_stmt( 4) case_stmt( 3)
                  case_stmt( 2) case_stmt( 1)
               }
               exprtk_disable_fallthrough_end

               #undef case_stmt

               return result;
            }

            T r[] = {
                      T(0), T(0), T(0), T(0), T(0), T(0), T(0), T(0),
                      T(0), T(0), T(0), T(0), T(0), T(0), T(0), T(0)
                    };

            const T* upper_bound = vec + lud.upper_bound;

            while (vec < upper_bound)
            {
               #define exprtk_loop(N) \
               r[N] += vec[N];        \

               exprtk_loop( 0) exprtk_loop( 1)
               exprtk_loop( 2) exprtk_loop( 3)
               exprtk_loop( 4) exprtk_loop( 5)
               exprtk_loop( 6) exprtk_loop( 7)
               exprtk_loop( 8) exprtk_loop( 9)
               exprtk_loop(10) exprtk_loop(11)
               exprtk_loop(12) exprtk_loop(13)
               exprtk_loop(14) exprtk_loop(15)

               vec += lud.batch_size;
            }

            int i = 0;

            exprtk_disable_fallthrough_begin
            switch (lud.remainder)
            {
               #define case_stmt(N)       \
               case N : r[0] += vec[i++]; \

               case_stmt(15) case_stmt(14)
               case_stmt(13) case_stmt(12)
               case_stmt(11) case_stmt(10)
               case_stmt( 9) case_stmt( 8)
               case_stmt( 7) case_stmt( 6)
               case_stmt( 5) case_stmt( 4)
               case_stmt( 3) case_stmt( 2)
               case_stmt( 1)
            }
            exprtk_disable_fallthrough_end

            #undef exprtk_loop
            #undef case_stmt


            return r[ 0] + r[ 1] + r[ 2] + r[ 3] +
                  ((!disable_superscalar_unroll) ? (
                   (r[ 4] + r[ 5] + r[ 6] + r[ 7])
                 + (r[ 8] + r[ 9] + r[10] + r[11])
                 + (r[12] + r[13] + r[14] + r[15])) : T(0));
         }
      };

      template <typename T>
      struct vec_mul_op
      {
         typedef vector_interface<T>* ivector_ptr;

         static inline T process(const ivector_ptr v)
         {
            const T* vec = v->vec()->vds().data();
            const std::size_t vec_size = v->vec()->vds().size();

            loop_unroll::details lud(vec_size);

            if (vec_size <= static_cast<std::size_t>(lud.batch_size))
            {
               T result = T(1);
               int i    = 0;

               exprtk_disable_fallthrough_begin
               switch (vec_size)
               {
                  #define case_stmt(N)         \
                  case N : result *= vec[i++]; \

                  case_stmt(16) case_stmt(15)
                  case_stmt(14) case_stmt(13)
                  case_stmt(12) case_stmt(11)
                  case_stmt(10) case_stmt( 9)
                  case_stmt( 8) case_stmt( 7)
                  case_stmt( 6) case_stmt( 5)
                  case_stmt( 4) case_stmt( 3)
                  case_stmt( 2) case_stmt( 1)
               }
               exprtk_disable_fallthrough_end

               #undef case_stmt

               return result;
            }

            T r[] = {
                      T(1), T(1), T(1), T(1), T(1), T(1), T(1), T(1),
                      T(1), T(1), T(1), T(1), T(1), T(1), T(1), T(1)
                    };

            const T* upper_bound = vec + lud.upper_bound;

            while (vec < upper_bound)
            {
               #define exprtk_loop(N) \
               r[N] *= vec[N];        \

               exprtk_loop( 0) exprtk_loop( 1)
               exprtk_loop( 2) exprtk_loop( 3)
               exprtk_loop( 4) exprtk_loop( 5)
               exprtk_loop( 6) exprtk_loop( 7)
               exprtk_loop( 8) exprtk_loop( 9)
               exprtk_loop(10) exprtk_loop(11)
               exprtk_loop(12) exprtk_loop(13)
               exprtk_loop(14) exprtk_loop(15)

               vec += lud.batch_size;
            }

            int i = 0;

            exprtk_disable_fallthrough_begin
            switch (lud.remainder)
            {
               #define case_stmt(N)       \
               case N : r[0] *= vec[i++]; \

               case_stmt(15) case_stmt(14)
               case_stmt(13) case_stmt(12)
               case_stmt(11) case_stmt(10)
               case_stmt( 9) case_stmt( 8)
               case_stmt( 7) case_stmt( 6)
               case_stmt( 5) case_stmt( 4)
               case_stmt( 3) case_stmt( 2)
               case_stmt( 1)
            }
            exprtk_disable_fallthrough_end

            #undef exprtk_loop
            #undef case_stmt

            return (r[ 0] * r[ 1] * r[ 2] * r[ 3])
                 + ((!disable_superscalar_unroll) ? (
                   (r[ 4] * r[ 5] * r[ 6] * r[ 7])
                 + (r[ 8] * r[ 9] * r[10] * r[11])
                 + (r[12] * r[13] * r[14] * r[15])) : T(0));
         }
      };

      template <typename T>
      struct vec_avg_op
      {
         typedef vector_interface<T>* ivector_ptr;

         static inline T process(const ivector_ptr v)
         {
            const T vec_size = T(v->vec()->vds().size());
            return vec_add_op<T>::process(v) / vec_size;
         }
      };

      template <typename T>
      struct vec_min_op
      {
         typedef vector_interface<T>* ivector_ptr;

         static inline T process(const ivector_ptr v)
         {
            const T* vec = v->vec()->vds().data();
            const std::size_t vec_size = v->vec()->vds().size();

            T result = vec[0];

            for (std::size_t i = 1; i < vec_size; ++i)
            {
               const T v_i = vec[i];

               if (v_i < result)
                  result = v_i;
            }

            return result;
         }
      };

      template <typename T>
      struct vec_max_op
      {
         typedef vector_interface<T>* ivector_ptr;

         static inline T process(const ivector_ptr v)
         {
            const T* vec = v->vec()->vds().data();
            const std::size_t vec_size = v->vec()->vds().size();

            T result = vec[0];

            for (std::size_t i = 1; i < vec_size; ++i)
            {
               const T v_i = vec[i];

               if (v_i > result)
                  result = v_i;
            }

            return result;
         }
      };
   }
}

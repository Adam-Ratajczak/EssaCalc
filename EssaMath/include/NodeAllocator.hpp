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
      class node_allocator
      {
      public:

         template <typename ResultNode, typename OpType, typename ExprNode>
         inline expression_node<typename ResultNode::value_type>* allocate(OpType& operation, ExprNode (&branch)[1])
         {
            expression_node<typename ResultNode::value_type>* result =
               allocate<ResultNode>(operation, branch[0]);
            result->node_depth();
            return result;
         }

         template <typename ResultNode, typename OpType, typename ExprNode>
         inline expression_node<typename ResultNode::value_type>* allocate(OpType& operation, ExprNode (&branch)[2])
         {
            expression_node<typename ResultNode::value_type>* result =
               allocate<ResultNode>(operation, branch[0], branch[1]);
            result->node_depth();
            return result;
         }

         template <typename ResultNode, typename OpType, typename ExprNode>
         inline expression_node<typename ResultNode::value_type>* allocate(OpType& operation, ExprNode (&branch)[3])
         {
            expression_node<typename ResultNode::value_type>* result =
               allocate<ResultNode>(operation, branch[0], branch[1], branch[2]);
            result->node_depth();
            return result;
         }

         template <typename ResultNode, typename OpType, typename ExprNode>
         inline expression_node<typename ResultNode::value_type>* allocate(OpType& operation, ExprNode (&branch)[4])
         {
            expression_node<typename ResultNode::value_type>* result =
               allocate<ResultNode>(operation, branch[0], branch[1], branch[2], branch[3]);
            result->node_depth();
            return result;
         }

         template <typename ResultNode, typename OpType, typename ExprNode>
         inline expression_node<typename ResultNode::value_type>* allocate(OpType& operation, ExprNode (&branch)[5])
         {
            expression_node<typename ResultNode::value_type>* result =
               allocate<ResultNode>(operation, branch[0],branch[1], branch[2], branch[3], branch[4]);
            result->node_depth();
            return result;
         }

         template <typename ResultNode, typename OpType, typename ExprNode>
         inline expression_node<typename ResultNode::value_type>* allocate(OpType& operation, ExprNode (&branch)[6])
         {
            expression_node<typename ResultNode::value_type>* result =
               allocate<ResultNode>(operation, branch[0], branch[1], branch[2], branch[3], branch[4], branch[5]);
            result->node_depth();
            return result;
         }

         template <typename node_type>
         inline expression_node<typename node_type::value_type>* allocate() const
         {
            return (new node_type());
         }

         template <typename node_type,
                   typename Type,
                   typename Allocator,
                   template <typename, typename> class Sequence>
         inline expression_node<typename node_type::value_type>* allocate(const Sequence<Type,Allocator>& seq) const
         {
            expression_node<typename node_type::value_type>*
            result = (new node_type(seq));
            result->node_depth();
            return result;
         }

         template <typename node_type, typename T1>
         inline expression_node<typename node_type::value_type>* allocate(T1& t1) const
         {
            expression_node<typename node_type::value_type>*
            result = (new node_type(t1));
            result->node_depth();
            return result;
         }

         template <typename node_type, typename T1, typename T2>
         inline expression_node<typename node_type::value_type>* allocate(T1& t1, T2 t2) const
         {
            expression_node<typename node_type::value_type>*
            result = (new node_type(t1, t2));
            result->node_depth();
            return result;
         }

         template <typename node_type, typename T1>
         inline expression_node<typename node_type::value_type>* allocate_c(const T1& t1) const
         {
            expression_node<typename node_type::value_type>*
            result = (new node_type(t1));
            result->node_depth();
            return result;
         }

         template <typename node_type,
                   typename T1, typename T2>
         inline expression_node<typename node_type::value_type>* allocate(const T1& t1, const T2& t2) const
         {
            expression_node<typename node_type::value_type>*
            result = (new node_type(t1, t2));
            result->node_depth();
            return result;
         }

         template <typename node_type,
                   typename T1, typename T2>
         inline expression_node<typename node_type::value_type>* allocate_cr(const T1& t1, T2& t2) const
         {
            expression_node<typename node_type::value_type>*
            result = (new node_type(t1, t2));
            result->node_depth();
            return result;
         }

         template <typename node_type,
                   typename T1, typename T2>
         inline expression_node<typename node_type::value_type>* allocate_rc(T1& t1, const T2& t2) const
         {
            expression_node<typename node_type::value_type>*
            result = (new node_type(t1, t2));
            result->node_depth();
            return result;
         }

         template <typename node_type,
                   typename T1, typename T2>
         inline expression_node<typename node_type::value_type>* allocate_rr(T1& t1, T2& t2) const
         {
            expression_node<typename node_type::value_type>*
            result = (new node_type(t1, t2));
            result->node_depth();
            return result;
         }

         template <typename node_type,
                   typename T1, typename T2>
         inline expression_node<typename node_type::value_type>* allocate_tt(T1 t1, T2 t2) const
         {
            expression_node<typename node_type::value_type>*
            result = (new node_type(t1, t2));
            result->node_depth();
            return result;
         }

         template <typename node_type,
                   typename T1, typename T2, typename T3>
         inline expression_node<typename node_type::value_type>* allocate_ttt(T1 t1, T2 t2, T3 t3) const
         {
            expression_node<typename node_type::value_type>*
            result = (new node_type(t1, t2, t3));
            result->node_depth();
            return result;
         }

         template <typename node_type,
                   typename T1, typename T2, typename T3, typename T4>
         inline expression_node<typename node_type::value_type>* allocate_tttt(T1 t1, T2 t2, T3 t3, T4 t4) const
         {
            expression_node<typename node_type::value_type>*
            result = (new node_type(t1, t2, t3, t4));
            result->node_depth();
            return result;
         }

         template <typename node_type,
                   typename T1, typename T2, typename T3>
         inline expression_node<typename node_type::value_type>* allocate_rrr(T1& t1, T2& t2, T3& t3) const
         {
            expression_node<typename node_type::value_type>*
            result = (new node_type(t1, t2, t3));
            result->node_depth();
            return result;
         }

         template <typename node_type,
                   typename T1, typename T2, typename T3, typename T4>
         inline expression_node<typename node_type::value_type>* allocate_rrrr(T1& t1, T2& t2, T3& t3, T4& t4) const
         {
            expression_node<typename node_type::value_type>*
            result = (new node_type(t1, t2, t3, t4));
            result->node_depth();
            return result;
         }

         template <typename node_type,
                   typename T1, typename T2, typename T3, typename T4, typename T5>
         inline expression_node<typename node_type::value_type>* allocate_rrrrr(T1& t1, T2& t2, T3& t3, T4& t4, T5& t5) const
         {
            expression_node<typename node_type::value_type>*
            result = (new node_type(t1, t2, t3, t4, t5));
            result->node_depth();
            return result;
         }

         template <typename node_type,
                   typename T1, typename T2, typename T3>
         inline expression_node<typename node_type::value_type>* allocate(const T1& t1, const T2& t2,
                                                                          const T3& t3) const
         {
            expression_node<typename node_type::value_type>*
            result = (new node_type(t1, t2, t3));
            result->node_depth();
            return result;
         }

         template <typename node_type,
                   typename T1, typename T2,
                   typename T3, typename T4>
         inline expression_node<typename node_type::value_type>* allocate(const T1& t1, const T2& t2,
                                                                          const T3& t3, const T4& t4) const
         {
            expression_node<typename node_type::value_type>*
            result = (new node_type(t1, t2, t3, t4));
            result->node_depth();
            return result;
         }

         template <typename node_type,
                   typename T1, typename T2,
                   typename T3, typename T4, typename T5>
         inline expression_node<typename node_type::value_type>* allocate(const T1& t1, const T2& t2,
                                                                          const T3& t3, const T4& t4,
                                                                          const T5& t5) const
         {
            expression_node<typename node_type::value_type>*
            result = (new node_type(t1, t2, t3, t4, t5));
            result->node_depth();
            return result;
         }

         template <typename node_type,
                   typename T1, typename T2,
                   typename T3, typename T4, typename T5, typename T6>
         inline expression_node<typename node_type::value_type>* allocate(const T1& t1, const T2& t2,
                                                                          const T3& t3, const T4& t4,
                                                                          const T5& t5, const T6& t6) const
         {
            expression_node<typename node_type::value_type>*
            result = (new node_type(t1, t2, t3, t4, t5, t6));
            result->node_depth();
            return result;
         }

         template <typename node_type,
                   typename T1, typename T2,
                   typename T3, typename T4,
                   typename T5, typename T6, typename T7>
         inline expression_node<typename node_type::value_type>* allocate(const T1& t1, const T2& t2,
                                                                          const T3& t3, const T4& t4,
                                                                          const T5& t5, const T6& t6,
                                                                          const T7& t7) const
         {
            expression_node<typename node_type::value_type>*
            result = (new node_type(t1, t2, t3, t4, t5, t6, t7));
            result->node_depth();
            return result;
         }

         template <typename node_type,
                   typename T1, typename T2,
                   typename T3, typename T4,
                   typename T5, typename T6,
                   typename T7, typename T8>
         inline expression_node<typename node_type::value_type>* allocate(const T1& t1, const T2& t2,
                                                                          const T3& t3, const T4& t4,
                                                                          const T5& t5, const T6& t6,
                                                                          const T7& t7, const T8& t8) const
         {
            expression_node<typename node_type::value_type>*
            result = (new node_type(t1, t2, t3, t4, t5, t6, t7, t8));
            result->node_depth();
            return result;
         }

         template <typename node_type,
                   typename T1, typename T2,
                   typename T3, typename T4,
                   typename T5, typename T6,
                   typename T7, typename T8, typename T9>
         inline expression_node<typename node_type::value_type>* allocate(const T1& t1, const T2& t2,
                                                                          const T3& t3, const T4& t4,
                                                                          const T5& t5, const T6& t6,
                                                                          const T7& t7, const T8& t8,
                                                                          const T9& t9) const
         {
            expression_node<typename node_type::value_type>*
            result = (new node_type(t1, t2, t3, t4, t5, t6, t7, t8, t9));
            result->node_depth();
            return result;
         }

         template <typename node_type,
                   typename T1, typename T2,
                   typename T3, typename T4,
                   typename T5, typename T6,
                   typename T7, typename T8,
                   typename T9, typename T10>
         inline expression_node<typename node_type::value_type>* allocate(const T1& t1, const  T2&  t2,
                                                                          const T3& t3, const  T4&  t4,
                                                                          const T5& t5, const  T6&  t6,
                                                                          const T7& t7, const  T8&  t8,
                                                                          const T9& t9, const T10& t10) const
         {
            expression_node<typename node_type::value_type>*
            result = (new node_type(t1, t2, t3, t4, t5, t6, t7, t8, t9, t10));
            result->node_depth();
            return result;
         }

         template <typename node_type,
                   typename T1, typename T2, typename T3>
         inline expression_node<typename node_type::value_type>* allocate_type(T1 t1, T2 t2, T3 t3) const
         {
            expression_node<typename node_type::value_type>*
            result = (new node_type(t1, t2, t3));
            result->node_depth();
            return result;
         }

         template <typename node_type,
                   typename T1, typename T2,
                   typename T3, typename T4>
         inline expression_node<typename node_type::value_type>* allocate_type(T1 t1, T2 t2,
                                                                               T3 t3, T4 t4) const
         {
            expression_node<typename node_type::value_type>*
            result = (new node_type(t1, t2, t3, t4));
            result->node_depth();
            return result;
         }

         template <typename node_type,
                   typename T1, typename T2,
                   typename T3, typename T4,
                   typename T5>
         inline expression_node<typename node_type::value_type>* allocate_type(T1 t1, T2 t2,
                                                                               T3 t3, T4 t4,
                                                                               T5 t5) const
         {
            expression_node<typename node_type::value_type>*
            result = (new node_type(t1, t2, t3, t4, t5));
            result->node_depth();
            return result;
         }

         template <typename node_type,
                   typename T1, typename T2,
                   typename T3, typename T4,
                   typename T5, typename T6>
         inline expression_node<typename node_type::value_type>* allocate_type(T1 t1, T2 t2,
                                                                               T3 t3, T4 t4,
                                                                               T5 t5, T6 t6) const
         {
            expression_node<typename node_type::value_type>*
            result = (new node_type(t1, t2, t3, t4, t5, t6));
            result->node_depth();
            return result;
         }

         template <typename node_type,
                   typename T1, typename T2,
                   typename T3, typename T4,
                   typename T5, typename T6, typename T7>
         inline expression_node<typename node_type::value_type>* allocate_type(T1 t1, T2 t2,
                                                                               T3 t3, T4 t4,
                                                                               T5 t5, T6 t6,
                                                                               T7 t7) const
         {
            expression_node<typename node_type::value_type>*
            result = (new node_type(t1, t2, t3, t4, t5, t6, t7));
            result->node_depth();
            return result;
         }

         template <typename T>
         void inline free(expression_node<T>*& e) const
         {
            exprtk_debug(("node_allocator::free() - deleting expression_node "
                          "type: %03d addr: %p\n",
                          static_cast<int>(e->type()),
                          reinterpret_cast<void*>(e)));
            delete e;
            e = 0;
         }
      };
   }
}
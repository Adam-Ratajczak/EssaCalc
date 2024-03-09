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

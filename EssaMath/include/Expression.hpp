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
#include "OperatorHelpers.hpp"
#include "SymbolTable.hpp"
#include <iostream>

namespace Essa::Math{
   template <typename T>
   class function_compositor;

   template <typename T>
   class expression
   {
   private:

      typedef details::expression_node<T>*  expression_ptr;
      typedef details::vector_holder<T>*    vector_holder_ptr;
      typedef std::vector<symbol_table<T> > symtab_list_t;

      struct control_block
      {
         enum data_type
         {
            e_unknown  ,
            e_expr     ,
            e_vecholder,
            e_data     ,
            e_vecdata  ,
            e_string
         };

         struct data_pack
         {
            data_pack()
            : pointer(0)
            , type(e_unknown)
            , size(0)
            {}

            data_pack(void* ptr, const data_type dt, const std::size_t sz = 0)
            : pointer(ptr)
            , type(dt)
            , size(sz)
            {}

            void*       pointer;
            data_type   type;
            std::size_t size;
         };

         typedef std::vector<data_pack> local_data_list_t;
         typedef results_context<T>     results_context_t;
         typedef control_block*         cntrl_blck_ptr_t;

         control_block()
         : ref_count(0)
         , expr     (0)
         , results  (0)
         , retinv_null(false)
         , return_invoked(&retinv_null)
         {}

         explicit control_block(expression_ptr e)
         : ref_count(1)
         , expr     (e)
         , results  (0)
         , retinv_null(false)
         , return_invoked(&retinv_null)
         {}

        ~control_block()
         {
            if (expr && details::branch_deletable(expr))
            {
               destroy_node(expr);
            }

            if (!local_data_list.empty())
            {
               for (std::size_t i = 0; i < local_data_list.size(); ++i)
               {
                  switch (local_data_list[i].type)
                  {
                     case e_expr      : delete reinterpret_cast<expression_ptr>(local_data_list[i].pointer);
                                        break;

                     case e_vecholder : delete reinterpret_cast<vector_holder_ptr>(local_data_list[i].pointer);
                                        break;

                     case e_data      : delete reinterpret_cast<T*>(local_data_list[i].pointer);
                                        break;

                     case e_vecdata   : delete [] reinterpret_cast<T*>(local_data_list[i].pointer);
                                        break;

                     case e_string    : delete reinterpret_cast<std::string*>(local_data_list[i].pointer);
                                        break;

                     default          : break;
                  }
               }
            }

            if (results)
            {
               delete results;
            }
         }

         static inline cntrl_blck_ptr_t create(expression_ptr e)
         {
            return new control_block(e);
         }

         static inline void destroy(cntrl_blck_ptr_t& cntrl_blck)
         {
            if (cntrl_blck)
            {
               if (
                    (0 !=   cntrl_blck->ref_count) &&
                    (0 == --cntrl_blck->ref_count)
                  )
               {
                  delete cntrl_blck;
               }

               cntrl_blck = 0;
            }
         }

         std::size_t ref_count;
         expression_ptr expr;
         expression_ptr unoptimized_expr;
         local_data_list_t local_data_list;
         results_context_t* results;
         bool  retinv_null;
         bool* return_invoked;

         friend class function_compositor<T>;
      };

   public:

      expression()
      : control_block_(0)
      {
         set_expression(new details::null_node<T>());
      }

      expression(const expression<T>& e)
      : control_block_    (e.control_block_    )
      , symbol_table_list_(e.symbol_table_list_)
      {
         control_block_->ref_count++;
      }

      explicit expression(const symbol_table<T>& symbol_table)
      : control_block_(0)
      {
         set_expression(new details::null_node<T>());
         symbol_table_list_.push_back(symbol_table);
      }

      inline expression<T>& operator=(const expression<T>& e)
      {
         if (this != &e)
         {
            if (control_block_)
            {
               if (
                    (0 !=   control_block_->ref_count) &&
                    (0 == --control_block_->ref_count)
                  )
               {
                  delete control_block_;
               }

               control_block_ = 0;
            }

            control_block_ = e.control_block_;
            control_block_->ref_count++;
            symbol_table_list_ = e.symbol_table_list_;
         }

         return *this;
      }

      inline std::string ToString() const{
         assert(control_block_      );
         assert(control_block_->unoptimized_expr);

         auto& typ = typeid(control_block_->expr);

         return control_block_->unoptimized_expr->ToString();
      }

      inline bool operator==(const expression<T>& e) const
      {
         return (this == &e);
      }

      inline bool operator!() const
      {
         return (
                  (0 == control_block_      ) ||
                  (0 == control_block_->expr)
                );
      }

      inline expression<T>& release()
      {
         Essa::Math::details::dump_ptr("expression::release", this);
         control_block::destroy(control_block_);

         return (*this);
      }

     ~expression()
      {
         control_block::destroy(control_block_);
      }

      inline T value() const
      {
         assert(control_block_      );
         assert(control_block_->expr);

         return control_block_->expr->value();
      }

      inline T operator() () const
      {
         return value();
      }

      inline operator T() const
      {
         return value();
      }

      inline operator bool() const
      {
         return details::is_true(value());
      }

      inline void register_symbol_table(symbol_table<T>& st)
      {
         for (std::size_t i = 0; i < symbol_table_list_.size(); ++i)
         {
            if (&st == &symbol_table_list_[i])
            {
               return;
            }
         }

         symbol_table_list_.push_back(st);
      }

      inline const symbol_table<T>& get_symbol_table(const std::size_t& index = 0) const
      {
         return symbol_table_list_[index];
      }

      inline symbol_table<T>& get_symbol_table(const std::size_t& index = 0)
      {
         return symbol_table_list_[index];
      }

      typedef results_context<T> results_context_t;

      inline const results_context_t& results() const
      {
         if (control_block_->results)
            return (*control_block_->results);
         else
         {
            static const results_context_t null_results;
            return null_results;
         }
      }

      inline bool return_invoked() const
      {
         return (*control_block_->return_invoked);
      }
      

   private:

      inline symtab_list_t get_symbol_table_list() const
      {
         return symbol_table_list_;
      }

      inline void set_expression(const expression_ptr expr)
      {
         if (expr)
         {
            if (control_block_)
            {
               if (0 == --control_block_->ref_count)
               {
                  delete control_block_;
               }
            }

            control_block_ = control_block::create(expr);
         }
      }

      inline void set_unoptimized_expr(const expression_ptr expr)
      {
         if (expr)
         {
            if (!control_block_)
            {
               control_block_ = control_block::create(expr);
            }

            control_block_->unoptimized_expr = expr;
         }
      }

      inline void register_local_var(expression_ptr expr)
      {
         if (expr)
         {
            if (control_block_)
            {
               control_block_->
                  local_data_list.push_back(
                     typename expression<T>::control_block::
                        data_pack(reinterpret_cast<void*>(expr),
                                  control_block::e_expr));
            }
         }
      }

      inline void register_local_var(vector_holder_ptr vec_holder)
      {
         if (vec_holder)
         {
            if (control_block_)
            {
               control_block_->
                  local_data_list.push_back(
                     typename expression<T>::control_block::
                        data_pack(reinterpret_cast<void*>(vec_holder),
                                  control_block::e_vecholder));
            }
         }
      }

      inline void register_local_data(void* data, const std::size_t& size = 0, const std::size_t data_mode = 0)
      {
         if (data)
         {
            if (control_block_)
            {
               typename control_block::data_type dt = control_block::e_data;

               switch (data_mode)
               {
                  case 0 : dt = control_block::e_data;    break;
                  case 1 : dt = control_block::e_vecdata; break;
                  case 2 : dt = control_block::e_string;  break;
               }

               control_block_->
                  local_data_list.push_back(
                     typename expression<T>::control_block::
                        data_pack(reinterpret_cast<void*>(data), dt, size));
            }
         }
      }

      inline const typename control_block::local_data_list_t& local_data_list()
      {
         if (control_block_)
         {
            return control_block_->local_data_list;
         }
         else
         {
            static typename control_block::local_data_list_t null_local_data_list;
            return null_local_data_list;
         }
      }

      inline void register_return_results(results_context_t* rc)
      {
         if (control_block_ && rc)
         {
            control_block_->results = rc;
         }
      }

      inline void set_retinvk(bool* retinvk_ptr)
      {
         if (control_block_)
         {
            control_block_->return_invoked = retinvk_ptr;
         }
      }

      control_block* control_block_;
      symtab_list_t  symbol_table_list_;

      friend class parser<T>;
      friend class expression_helper<T>;
      friend class function_compositor<T>;
   }; // class expression
}

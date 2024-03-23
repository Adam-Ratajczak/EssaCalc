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
#include "include/ParserHelpers.hpp"
#include "include/OperatorHelpers.hpp"
#include "include/Numeric.hpp"
#include <cstdio>
#include <string>
#include <cassert>

namespace Essa::Math{
   namespace details
   {
      template <typename Type>
      class vector_holder
      {
      private:

         typedef Type value_type;
         typedef value_type* value_ptr;
         typedef const value_ptr const_value_ptr;

         class vector_holder_base
         {
         public:

            virtual ~vector_holder_base() {}

            inline value_ptr operator[](const std::size_t& index) const
            {
               return value_at(index);
            }

            inline std::size_t size() const
            {
               return vector_size();
            }

            inline value_ptr data() const
            {
               return value_at(0);
            }

            virtual inline bool rebaseable() const
            {
               return false;
            }

            virtual void set_ref(value_ptr*) {}

         protected:

            virtual value_ptr value_at(const std::size_t&) const = 0;
            virtual std::size_t vector_size()              const = 0;
         };

         class array_vector_impl : public vector_holder_base
         {
         public:

            array_vector_impl(const Type* vec, const std::size_t& vec_size)
            : vec_(vec)
            , size_(vec_size)
            {}

         protected:

            value_ptr value_at(const std::size_t& index) const
            {
               if (index < size_)
                  return const_cast<const_value_ptr>(vec_ + index);
               else
                  return const_value_ptr(0);
            }

            std::size_t vector_size() const
            {
               return size_;
            }

         private:

            array_vector_impl(const array_vector_impl&) exprtk_delete;
            array_vector_impl& operator=(const array_vector_impl&) exprtk_delete;

            const Type* vec_;
            const std::size_t size_;
         };

         template <typename Allocator,
                   template <typename, typename> class Sequence>
         class sequence_vector_impl : public vector_holder_base
         {
         public:

            typedef Sequence<Type,Allocator> sequence_t;

            sequence_vector_impl(sequence_t& seq)
            : sequence_(seq)
            {}

         protected:

            value_ptr value_at(const std::size_t& index) const
            {
               return (index < sequence_.size()) ? (&sequence_[index]) : const_value_ptr(0);
            }

            std::size_t vector_size() const
            {
               return sequence_.size();
            }

         private:

            sequence_vector_impl(const sequence_vector_impl&) exprtk_delete;
            sequence_vector_impl& operator=(const sequence_vector_impl&) exprtk_delete;

            sequence_t& sequence_;
         };

         class vector_view_impl : public vector_holder_base
         {
         public:

            typedef Essa::Math::vector_view<Type> vector_view_t;

            vector_view_impl(vector_view_t& vec_view)
            : vec_view_(vec_view)
            {}

            void set_ref(value_ptr* ref)
            {
               vec_view_.set_ref(ref);
            }

            virtual inline bool rebaseable() const
            {
               return true;
            }

         protected:

            value_ptr value_at(const std::size_t& index) const
            {
               return (index < vec_view_.size()) ? (&vec_view_[index]) : const_value_ptr(0);
            }

            std::size_t vector_size() const
            {
               return vec_view_.size();
            }

         private:

            vector_view_impl(const vector_view_impl&) exprtk_delete;
            vector_view_impl& operator=(const vector_view_impl&) exprtk_delete;

            vector_view_t& vec_view_;
         };

      public:

         typedef typename details::vec_data_store<Type> vds_t;

         vector_holder(Type* vec, const std::size_t& vec_size)
         : vector_holder_base_(new(buffer)array_vector_impl(vec,vec_size))
         {}

         explicit vector_holder(const vds_t& vds)
         : vector_holder_base_(new(buffer)array_vector_impl(vds.data(),vds.size()))
         {}

         template <typename Allocator>
         explicit vector_holder(std::vector<Type,Allocator>& vec)
         : vector_holder_base_(new(buffer)sequence_vector_impl<Allocator,std::vector>(vec))
         {}

         explicit vector_holder(Essa::Math::vector_view<Type>& vec)
         : vector_holder_base_(new(buffer)vector_view_impl(vec))
         {}

         inline value_ptr operator[](const std::size_t& index) const
         {
            return (*vector_holder_base_)[index];
         }

         inline std::size_t size() const
         {
            return vector_holder_base_->size();
         }

         inline value_ptr data() const
         {
            return vector_holder_base_->data();
         }

         void set_ref(value_ptr* ref)
         {
            vector_holder_base_->set_ref(ref);
         }

         bool rebaseable() const
         {
            return vector_holder_base_->rebaseable();
         }

      private:

         mutable vector_holder_base* vector_holder_base_;
         uchar_t buffer[64];
      };

      template <typename T>
      class null_node exprtk_final : public expression_node<T>
      {
      public:

         inline T value() const exprtk_override
         {
            return std::numeric_limits<T>::quiet_NaN();
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_null;
         }

         inline std::string to_string() const exprtk_override{
            return "0";
         }
      };

      template <typename T, std::size_t N>
      inline void construct_branch_pair(std::pair<expression_node<T>*,bool> (&branch)[N],
                                        expression_node<T>* b,
                                        const std::size_t& index)
      {
         if (b && (index < N))
         {
            branch[index] = std::make_pair(b,branch_deletable(b));
         }
      }

      template <typename T>
      inline void construct_branch_pair(std::pair<expression_node<T>*,bool>& branch, expression_node<T>* b)
      {
         if (b)
         {
            branch = std::make_pair(b,branch_deletable(b));
         }
      }

      template <std::size_t N, typename T>
      inline void init_branches(std::pair<expression_node<T>*,bool> (&branch)[N],
                                expression_node<T>* b0,
                                expression_node<T>* b1 = reinterpret_cast<expression_node<T>*>(0),
                                expression_node<T>* b2 = reinterpret_cast<expression_node<T>*>(0),
                                expression_node<T>* b3 = reinterpret_cast<expression_node<T>*>(0),
                                expression_node<T>* b4 = reinterpret_cast<expression_node<T>*>(0),
                                expression_node<T>* b5 = reinterpret_cast<expression_node<T>*>(0),
                                expression_node<T>* b6 = reinterpret_cast<expression_node<T>*>(0),
                                expression_node<T>* b7 = reinterpret_cast<expression_node<T>*>(0),
                                expression_node<T>* b8 = reinterpret_cast<expression_node<T>*>(0),
                                expression_node<T>* b9 = reinterpret_cast<expression_node<T>*>(0))
      {
         construct_branch_pair(branch, b0, 0);
         construct_branch_pair(branch, b1, 1);
         construct_branch_pair(branch, b2, 2);
         construct_branch_pair(branch, b3, 3);
         construct_branch_pair(branch, b4, 4);
         construct_branch_pair(branch, b5, 5);
         construct_branch_pair(branch, b6, 6);
         construct_branch_pair(branch, b7, 7);
         construct_branch_pair(branch, b8, 8);
         construct_branch_pair(branch, b9, 9);
      }

      template <typename T>
      class null_eq_node exprtk_final : public expression_node<T>
      {
      public:
         typedef expression_node<T>* expression_ptr;
         typedef std::pair<expression_ptr,bool> branch_t;

         explicit null_eq_node(expression_ptr branch, const bool equality = true)
         : equality_(equality)
         {
            construct_branch_pair(branch_, branch);
         }

         inline T value() const exprtk_override
         {
            assert(branch_.first);

            const T v = branch_.first->value();
            const bool result = details::numeric::is_nan(v);

            if (result)
               return equality_ ? T(1) : T(0);
            else
               return equality_ ? T(0) : T(1);
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_nulleq;
         }

         inline expression_node<T>* branch(const std::size_t&) const exprtk_override
         {
            return branch_.first;
         }

         void collect_nodes(typename expression_node<T>::noderef_list_t& node_delete_list) exprtk_override
         {
            expression_node<T>::ndb_t::collect(branch_, node_delete_list);
         }

         std::size_t node_depth() const exprtk_override
         {
            return expression_node<T>::ndb_t::compute_node_depth(branch_);
         }

         inline std::string to_string() const exprtk_override{
            return branch_.first->to_string() + (equality_ ? "==" : "!=") + "0";
         }
      private:

         bool equality_;
         branch_t branch_;
      };

      template <typename T>
      class literal_node exprtk_final : public expression_node<T>
      {
      public:

         explicit literal_node(const T& v)
         : value_(v)
         {}

         inline T value() const exprtk_override
         {
            return value_;
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_constant;
         }

         inline expression_node<T>* branch(const std::size_t&) const exprtk_override
         {
            return reinterpret_cast<expression_node<T>*>(0);
         }

         inline std::string to_string() const exprtk_override{
            const typename details::numeric::details::number_type<T>::type num_type;
            static const T local_pi = details::numeric::details::const_pi_impl<T>(num_type);
            static const T local_e = details::numeric::details::const_e_impl<T>(num_type);

            if(value_ == local_pi)
               return "%pi";
            else if(value_ == local_e)
               return "%e";
            else if(numeric::is_i<T>(value_))
               return "%i";
            else{
               return numeric::num_to_string<T>(value_);
            }
         }
      private:

         literal_node(const literal_node<T>&) exprtk_delete;
         literal_node<T>& operator=(const literal_node<T>&) exprtk_delete;

         const T value_;
      };

      template <typename T>
      struct range_pack;

      template <typename T>
      struct range_data_type;

      template <typename T>
      class range_interface
      {
      public:

         typedef range_pack<T> range_t;

         virtual ~range_interface() {}

         virtual range_t& range_ref() = 0;

         virtual const range_t& range_ref() const = 0;
      };

      template <typename T>
      class string_base_node
      {
      public:

         typedef range_data_type<T> range_data_type_t;

         virtual ~string_base_node() {}

         virtual std::string str () const = 0;

         virtual char_cptr   base() const = 0;

         virtual std::size_t size() const = 0;
      };

      template <typename T>
      class string_literal_node exprtk_final
                                : public expression_node <T>,
                                  public string_base_node<T>,
                                  public range_interface <T>
      {
      public:

         typedef range_pack<T> range_t;

         explicit string_literal_node(const std::string& v)
         : value_(v)
         {
            rp_.n0_c = std::make_pair<bool,std::size_t>(true,0);
            rp_.n1_c = std::make_pair<bool,std::size_t>(true,v.size() - 1);
            rp_.cache.first  = rp_.n0_c.second;
            rp_.cache.second = rp_.n1_c.second;
         }

         inline T value() const exprtk_override
         {
            return std::numeric_limits<T>::quiet_NaN();
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_stringconst;
         }

         inline expression_node<T>* branch(const std::size_t&) const exprtk_override
         {
            return reinterpret_cast<expression_node<T>*>(0);
         }

         std::string str() const exprtk_override
         {
            return value_;
         }

         char_cptr base() const exprtk_override
         {
            return value_.data();
         }

         std::size_t size() const exprtk_override
         {
            return value_.size();
         }

         range_t& range_ref() exprtk_override
         {
            return rp_;
         }

         const range_t& range_ref() const exprtk_override
         {
            return rp_;
         }

         inline std::string to_string() const exprtk_override{
            return value_;
         }
      private:

         string_literal_node(const string_literal_node<T>&) exprtk_delete;
         string_literal_node<T>& operator=(const string_literal_node<T>&) exprtk_delete;

         const std::string value_;
         range_t rp_;
      };

      template <typename T>
      class unary_node : public expression_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef std::pair<expression_ptr,bool> branch_t;

         unary_node(const operator_type& opr, expression_ptr branch)
         : operation_(opr)
         {
            construct_branch_pair(branch_,branch);
         }

         inline T value() const exprtk_override
         {
            assert(branch_.first);
            const T arg = branch_.first->value();
            return numeric::process<T>(operation_,arg);
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_unary;
         }

         inline operator_type operation()
         {
            return operation_;
         }

         inline expression_node<T>* branch(const std::size_t&) const exprtk_override
         {
            return branch_.first;
         }

         inline void release()
         {
            branch_.second = false;
         }

         void collect_nodes(typename expression_node<T>::noderef_list_t& node_delete_list) exprtk_override
         {
            expression_node<T>::ndb_t::collect(branch_, node_delete_list);
         }

         std::size_t node_depth() const exprtk_final
         {
            return expression_node<T>::ndb_t::compute_node_depth(branch_);
         }

         inline std::string to_string() const exprtk_override{
            char _buf[2048]{0};
            std::string _name = to_str(operation_);
            std::string _arg1 = branch_.first->to_string();
            sprintf(_buf, _name.c_str(), _arg1.c_str());
            return _buf;
         }
      private:

         operator_type operation_;
         branch_t branch_;
      };


      template <typename T>
      class binary_node : public expression_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef std::pair<expression_ptr,bool> branch_t;

         binary_node(const operator_type& opr,
                     expression_ptr branch0,
                     expression_ptr branch1)
         : operation_(opr)
         {
            init_branches<2>(branch_, branch0, branch1);
         }

         inline T value() const exprtk_override
         {
            assert(branch_[0].first);
            assert(branch_[1].first);

            const T arg0 = branch_[0].first->value();
            const T arg1 = branch_[1].first->value();

            return numeric::process<T>(operation_, arg0, arg1);
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_binary;
         }

         inline operator_type operation()
         {
            return operation_;
         }

         inline expression_node<T>* branch(const std::size_t& index = 0) const exprtk_override
         {
            if (0 == index)
               return branch_[0].first;
            else if (1 == index)
               return branch_[1].first;
            else
               return reinterpret_cast<expression_ptr>(0);
         }

         void collect_nodes(typename expression_node<T>::noderef_list_t& node_delete_list) exprtk_override
         {
            expression_node<T>::ndb_t::template collect(branch_, node_delete_list);
         }

         std::size_t node_depth() const exprtk_final
         {
            return expression_node<T>::ndb_t::template compute_node_depth<2>(branch_);
         }

         inline std::string to_string() const exprtk_override{
            char _buf[2048]{0};
            std::string _name = to_str(operation_);
            bool sig = false;
            
            if(binary_node* _node = dynamic_cast<binary_node*>(branch_[0].first))
               sig = check_significance(operation_, _node->operation());
            else
               sig = false;

            std::string _arg1 = (sig ? "(" : "") + branch_[0].first->to_string() + (sig ? ")" : "");
            
            if(binary_node* _node = dynamic_cast<binary_node*>(branch_[1].first))
               sig = check_significance(operation_, _node->operation());
            else
               sig = false;

            std::string _arg2 = (sig ? "(" : "") + branch_[1].first->to_string() + (sig ? ")" : "");
            sprintf(_buf, _name.c_str(), _arg1.c_str(), _arg2.c_str());
            return _buf;
         }
      private:

         operator_type operation_;
         branch_t branch_[2];
      };

      template <typename T, typename Operation>
      class binary_ext_node exprtk_final : public expression_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef std::pair<expression_ptr,bool> branch_t;

         binary_ext_node(expression_ptr branch0, expression_ptr branch1)
         {
            init_branches<2>(branch_, branch0, branch1);
         }

         inline T value() const exprtk_override
         {
            assert(branch_[0].first);
            assert(branch_[1].first);

            const T arg0 = branch_[0].first->value();
            const T arg1 = branch_[1].first->value();

            return Operation::process(arg0,arg1);
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_binary_ext;
         }

         inline operator_type operation() const
         {
            return Operation::operation();
         }

         inline expression_node<T>* branch(const std::size_t& index = 0) const exprtk_override
         {
            if (0 == index)
               return branch_[0].first;
            else if (1 == index)
               return branch_[1].first;
            else
               return reinterpret_cast<expression_ptr>(0);
         }

         void collect_nodes(typename expression_node<T>::noderef_list_t& node_delete_list) exprtk_override
         {
            expression_node<T>::ndb_t::template collect(branch_, node_delete_list);
         }

         std::size_t node_depth() const exprtk_override
         {
            return expression_node<T>::ndb_t::template compute_node_depth<2>(branch_);
         }

         inline std::string to_string() const exprtk_override{
            
            char _buf[2048]{0};
            std::string _name = to_str(operation());
            bool sig = false;
            
            if(binary_node<T>* _node = dynamic_cast<binary_node<T>*>(branch_[0].first))
               sig = check_significance(operation(), _node->operation());
            else
               sig = false;

            std::string _arg1 = (sig ? "(" : "") + branch_[0].first->to_string() + (sig ? ")" : "");
            
            if(binary_node<T>* _node = dynamic_cast<binary_node<T>*>(branch_[1].first))
               sig = check_significance(operation(), _node->operation());
            else
               sig = false;

            std::string _arg2 = (sig ? "(" : "") + branch_[1].first->to_string() + (sig ? ")" : "");
            sprintf(_buf, _name.c_str(), _arg1.c_str(), _arg2.c_str());
            return _buf;
         }
      protected:

         branch_t branch_[2];
      };

      template <typename T>
      class trinary_node : public expression_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef std::pair<expression_ptr,bool> branch_t;

         trinary_node(const operator_type& opr,
                      expression_ptr branch0,
                      expression_ptr branch1,
                      expression_ptr branch2)
         : operation_(opr)
         {
            init_branches<3>(branch_, branch0, branch1, branch2);
         }

         inline T value() const exprtk_override
         {
            assert(branch_[0].first);
            assert(branch_[1].first);
            assert(branch_[2].first);

            const T arg0 = branch_[0].first->value();
            const T arg1 = branch_[1].first->value();
            const T arg2 = branch_[2].first->value();

            switch (operation_)
            {
               case e_inrange : return numeric::inrange<T>(arg0, arg1, arg2);

               case e_clamp   : return numeric::clamp<T>(arg0, arg1, arg2);

               case e_iclamp  : return numeric::iclamp<T>(arg0, arg1, arg2);

               default        : exprtk_debug(("trinary_node::value() - Error: Invalid operation\n"));
                                return std::numeric_limits<T>::quiet_NaN();
            }
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_trinary;
         }

         void collect_nodes(typename expression_node<T>::noderef_list_t& node_delete_list) exprtk_override
         {
            expression_node<T>::ndb_t::template collect(branch_, node_delete_list);
         }

         std::size_t node_depth() const exprtk_override exprtk_final
         {
            return expression_node<T>::ndb_t::template compute_node_depth<3>(branch_);
         }

         inline std::string to_string() const exprtk_override{
            char _buf[2048]{0};
            std::string _name = to_str(operation_);
            std::string _arg1 = branch_[0].first->to_string();
            std::string _arg2 = branch_[1].first->to_string();
            std::string _arg3 = branch_[2].first->to_string();
            sprintf(_buf, _name.c_str(), _arg1.c_str(), _arg2.c_str(), _arg3.c_str());
            return _buf;
         }
      protected:

         operator_type operation_;
         branch_t branch_[3];
      };

      template <typename T>
      class quaternary_node : public expression_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef std::pair<expression_ptr,bool> branch_t;

         quaternary_node(const operator_type& opr,
                         expression_ptr branch0,
                         expression_ptr branch1,
                         expression_ptr branch2,
                         expression_ptr branch3)
         : operation_(opr)
         {
            init_branches<4>(branch_, branch0, branch1, branch2, branch3);
         }

         inline T value() const exprtk_override
         {
            return std::numeric_limits<T>::quiet_NaN();
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_quaternary;
         }

         void collect_nodes(typename expression_node<T>::noderef_list_t& node_delete_list) exprtk_override
         {
            expression_node<T>::ndb_t::template collect(branch_, node_delete_list);
         }

         std::size_t node_depth() const exprtk_override exprtk_final
         {
            return expression_node<T>::ndb_t::template compute_node_depth<4>(branch_);
         }

         inline std::string to_string() const exprtk_override{
            char _buf[2048]{0};
            std::string _name = to_str(operation_);
            std::string _arg1 = branch_[0].first->to_string();
            std::string _arg2 = branch_[1].first->to_string();
            std::string _arg3 = branch_[2].first->to_string();
            std::string _arg4 = branch_[3].first->to_string();
            sprintf(_buf, _name.c_str(), _arg1.c_str(), _arg2.c_str(), _arg3.c_str(), _arg4.c_str());
            return _buf;
         }
      protected:

         operator_type operation_;
         branch_t branch_[4];
      };

      template <typename T>
      class conditional_node exprtk_final : public expression_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef std::pair<expression_ptr,bool> branch_t;

         conditional_node(expression_ptr condition,
                          expression_ptr consequent,
                          expression_ptr alternative)
         {
            construct_branch_pair(condition_  , condition  );
            construct_branch_pair(consequent_ , consequent );
            construct_branch_pair(alternative_, alternative);
         }

         inline T value() const exprtk_override
         {
            assert(condition_  .first);
            assert(consequent_ .first);
            assert(alternative_.first);

            if (is_true(condition_))
               return consequent_.first->value();
            else
               return alternative_.first->value();
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_conditional;
         }

         void collect_nodes(typename expression_node<T>::noderef_list_t& node_delete_list) exprtk_override
         {
            expression_node<T>::ndb_t::collect(condition_   , node_delete_list);
            expression_node<T>::ndb_t::collect(consequent_  , node_delete_list);
            expression_node<T>::ndb_t::collect(alternative_ , node_delete_list);
         }

         std::size_t node_depth() const exprtk_override
         {
            return expression_node<T>::ndb_t::compute_node_depth
               (condition_, consequent_, alternative_);
         }

         inline std::string to_string() const exprtk_override{
            return "(conditional_node)";
         }
      private:

         branch_t condition_;
         branch_t consequent_;
         branch_t alternative_;
      };

      template <typename T>
      class cons_conditional_node exprtk_final : public expression_node<T>
      {
      public:

         // Consequent only conditional statement node
         typedef expression_node<T>* expression_ptr;
         typedef std::pair<expression_ptr,bool> branch_t;

         cons_conditional_node(expression_ptr condition,
                               expression_ptr consequent)
         {
            construct_branch_pair(condition_ , condition );
            construct_branch_pair(consequent_, consequent);
         }

         inline T value() const exprtk_override
         {
            assert(condition_ .first);
            assert(consequent_.first);

            if (is_true(condition_))
               return consequent_.first->value();
            else
               return std::numeric_limits<T>::quiet_NaN();
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_conditional;
         }

         void collect_nodes(typename expression_node<T>::noderef_list_t& node_delete_list) exprtk_override
         {
            expression_node<T>::ndb_t::collect(condition_  , node_delete_list);
            expression_node<T>::ndb_t::collect(consequent_ , node_delete_list);
         }

         std::size_t node_depth() const exprtk_override
         {
            return expression_node<T>::ndb_t::
               compute_node_depth(condition_, consequent_);
         }

         inline std::string to_string() const exprtk_override{
            return "(cons_conditional_node)";
         }
      private:

         branch_t condition_;
         branch_t consequent_;
      };

      template <typename T>
      class break_exception
      {
      public:

         explicit break_exception(const T& v)
         : value(v)
         {}

         T value;
      };

      class continue_exception {};

      template <typename T>
      class break_node exprtk_final : public expression_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef std::pair<expression_ptr,bool> branch_t;

         break_node(expression_ptr ret = expression_ptr(0))
         {
            construct_branch_pair(return_, ret);
         }

         inline T value() const exprtk_override
         {
            const T result = return_.first ?
                             return_.first->value() :
                             std::numeric_limits<T>::quiet_NaN();

            throw break_exception<T>(result);

            #ifndef _MSC_VER
            return std::numeric_limits<T>::quiet_NaN();
            #endif
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_break;
         }

         void collect_nodes(typename expression_node<T>::noderef_list_t& node_delete_list) exprtk_override
         {
            expression_node<T>::ndb_t::collect(return_, node_delete_list);
         }

         std::size_t node_depth() const exprtk_override
         {
            return expression_node<T>::ndb_t::compute_node_depth(return_);
         }

         inline std::string to_string() const exprtk_override{
            return "(break_node)";
         }
      private:

         branch_t return_;
      };

      template <typename T>
      class continue_node exprtk_final : public expression_node<T>
      {
      public:

         inline T value() const exprtk_override
         {
            throw continue_exception();
            #ifndef _MSC_VER
            return std::numeric_limits<T>::quiet_NaN();
            #endif
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_break;
         }

         inline std::string to_string() const exprtk_override{
            return "(continue_node)";
         }
      };

      struct loop_runtime_checker
      {
         loop_runtime_checker(loop_runtime_check_ptr loop_runtime_check,
                              loop_runtime_check::loop_types lp_typ = loop_runtime_check::e_invalid)
         : iteration_count_(0)
         , loop_runtime_check_(loop_runtime_check)
         , max_loop_iterations_(loop_runtime_check_->max_loop_iterations)
         , loop_type_(lp_typ)
         {
            assert(loop_runtime_check_);
         }

         inline void reset(const _uint64_t initial_value = 0) const
         {
            iteration_count_ = initial_value;
         }

         inline bool check() const
         {
            if (
                 (0 == loop_runtime_check_) ||
                 ((++iteration_count_ <= max_loop_iterations_) && loop_runtime_check_->check())
               )
            {
               return true;
            }

            loop_runtime_check::violation_context ctxt;
            ctxt.loop      = loop_type_;
            ctxt.violation = loop_runtime_check::e_iteration_count;

            loop_runtime_check_->handle_runtime_violation(ctxt);

            return false;
         }

         mutable _uint64_t iteration_count_;
         mutable loop_runtime_check_ptr loop_runtime_check_;
         const details::_uint64_t& max_loop_iterations_;
         loop_runtime_check::loop_types loop_type_;
      };

      template <typename T>
      class while_loop_node : public expression_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef std::pair<expression_ptr,bool> branch_t;

         while_loop_node(expression_ptr condition,
                         expression_ptr loop_body)
         {
            construct_branch_pair(condition_, condition);
            construct_branch_pair(loop_body_, loop_body);
         }

         inline T value() const exprtk_override
         {
            assert(condition_.first);
            assert(loop_body_.first);

            T result = T(0);

            while (is_true(condition_))
            {
               result = loop_body_.first->value();
            }

            return result;
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_while;
         }

         void collect_nodes(typename expression_node<T>::noderef_list_t& node_delete_list) exprtk_override
         {
            expression_node<T>::ndb_t::collect(condition_ , node_delete_list);
            expression_node<T>::ndb_t::collect(loop_body_ , node_delete_list);
         }

         std::size_t node_depth() const exprtk_override
         {
            return expression_node<T>::ndb_t::compute_node_depth(condition_, loop_body_);
         }

         inline std::string to_string() const exprtk_override{
            return "(while_loop_node)";
         }

      protected:

         branch_t condition_;
         branch_t loop_body_;
      };

      template <typename T>
      class while_loop_rtc_node exprtk_final
                                : public while_loop_node<T>
                                , public loop_runtime_checker
      {
      public:

         typedef while_loop_node<T>  parent_t;
         typedef expression_node<T>* expression_ptr;

         while_loop_rtc_node(expression_ptr condition,
                             expression_ptr loop_body,
                             loop_runtime_check_ptr loop_rt_chk)
         : parent_t(condition, loop_body)
         , loop_runtime_checker(loop_rt_chk, loop_runtime_check::e_while_loop)
         {}

         inline T value() const exprtk_override
         {
            assert(parent_t::condition_.first);
            assert(parent_t::loop_body_.first);

            T result = T(0);

            loop_runtime_checker::reset();

            while (is_true(parent_t::condition_) && loop_runtime_checker::check())
            {
               result = parent_t::loop_body_.first->value();
            }

            return result;
         }
      };

      template <typename T>
      class repeat_until_loop_node : public expression_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef std::pair<expression_ptr,bool> branch_t;

         repeat_until_loop_node(expression_ptr condition,
                                expression_ptr loop_body)
         {
            construct_branch_pair(condition_, condition);
            construct_branch_pair(loop_body_, loop_body);
         }

         inline T value() const exprtk_override
         {
            assert(condition_.first);
            assert(loop_body_.first);

            T result = T(0);

            do
            {
               result = loop_body_.first->value();
            }
            while (is_false(condition_.first));

            return result;
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_repeat;
         }

         void collect_nodes(typename expression_node<T>::noderef_list_t& node_delete_list) exprtk_override
         {
            expression_node<T>::ndb_t::collect(condition_ , node_delete_list);
            expression_node<T>::ndb_t::collect(loop_body_ , node_delete_list);
         }

         std::size_t node_depth() const exprtk_override
         {
            return expression_node<T>::ndb_t::compute_node_depth(condition_, loop_body_);
         }

         inline std::string to_string() const exprtk_override{
            return "(repeat_until_loop_node)";
         }
      protected:

         branch_t condition_;
         branch_t loop_body_;
      };

      template <typename T>
      class repeat_until_loop_rtc_node exprtk_final
                                       : public repeat_until_loop_node<T>
                                       , public loop_runtime_checker
      {
      public:

         typedef repeat_until_loop_node<T> parent_t;
         typedef expression_node<T>*       expression_ptr;

         repeat_until_loop_rtc_node(expression_ptr condition,
                                    expression_ptr loop_body,
                                    loop_runtime_check_ptr loop_rt_chk)
         : parent_t(condition, loop_body)
         , loop_runtime_checker(loop_rt_chk, loop_runtime_check::e_repeat_until_loop)
         {}

         inline T value() const exprtk_override
         {
            assert(parent_t::condition_.first);
            assert(parent_t::loop_body_.first);

            T result = T(0);

            loop_runtime_checker::reset(1);

            do
            {
               result = parent_t::loop_body_.first->value();
            }
            while (is_false(parent_t::condition_.first) && loop_runtime_checker::check());

            return result;
         }

         inline std::string to_string() const exprtk_override{
            return "(repeat_until_loop_rtc_node)";
         }
      };

      template <typename T>
      class for_loop_node : public expression_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef std::pair<expression_ptr,bool> branch_t;

         for_loop_node(expression_ptr initialiser,
                       expression_ptr condition,
                       expression_ptr incrementor,
                       expression_ptr loop_body)
         {
            construct_branch_pair(initialiser_, initialiser);
            construct_branch_pair(condition_  , condition  );
            construct_branch_pair(incrementor_, incrementor);
            construct_branch_pair(loop_body_  , loop_body  );
         }

         inline T value() const exprtk_override
         {
            assert(condition_.first);
            assert(loop_body_.first);

            T result = T(0);

            if (initialiser_.first)
               initialiser_.first->value();

            if (incrementor_.first)
            {
               while (is_true(condition_))
               {
                  result = loop_body_.first->value();
                  incrementor_.first->value();
               }
            }
            else
            {
               while (is_true(condition_))
               {
                  result = loop_body_.first->value();
               }
            }

            return result;
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_for;
         }

         void collect_nodes(typename expression_node<T>::noderef_list_t& node_delete_list) exprtk_override
         {
            expression_node<T>::ndb_t::collect(initialiser_ , node_delete_list);
            expression_node<T>::ndb_t::collect(condition_   , node_delete_list);
            expression_node<T>::ndb_t::collect(incrementor_ , node_delete_list);
            expression_node<T>::ndb_t::collect(loop_body_   , node_delete_list);
         }

         std::size_t node_depth() const exprtk_override
         {
            return expression_node<T>::ndb_t::compute_node_depth
               (initialiser_, condition_, incrementor_, loop_body_);
         }

         inline std::string to_string() const exprtk_override{
            return "(for_loop_node)";
         }

      protected:

         branch_t initialiser_;
         branch_t condition_  ;
         branch_t incrementor_;
         branch_t loop_body_  ;
      };

      template <typename T>
      class for_loop_rtc_node exprtk_final
                              : public for_loop_node<T>
                              , public loop_runtime_checker
      {
      public:

         typedef for_loop_node<T>    parent_t;
         typedef expression_node<T>* expression_ptr;

         for_loop_rtc_node(expression_ptr initialiser,
                           expression_ptr condition,
                           expression_ptr incrementor,
                           expression_ptr loop_body,
                           loop_runtime_check_ptr loop_rt_chk)
         : parent_t(initialiser, condition, incrementor, loop_body)
         , loop_runtime_checker(loop_rt_chk, loop_runtime_check::e_for_loop)
         {}

         inline T value() const exprtk_override
         {
            assert(parent_t::condition_.first);
            assert(parent_t::loop_body_.first);

            T result = T(0);

            loop_runtime_checker::reset();

            if (parent_t::initialiser_.first)
               parent_t::initialiser_.first->value();

            if (parent_t::incrementor_.first)
            {
               while (is_true(parent_t::condition_) && loop_runtime_checker::check())
               {
                  result = parent_t::loop_body_.first->value();
                  parent_t::incrementor_.first->value();
               }
            }
            else
            {
               while (is_true(parent_t::condition_) && loop_runtime_checker::check())
               {
                  result = parent_t::loop_body_.first->value();
               }
            }

            return result;
         }

         inline std::string to_string() const exprtk_override{
            return "(for_loop_rtc_node)";
         }
      };

      template <typename T>
      class while_loop_bc_node : public while_loop_node<T>
      {
      public:

         typedef while_loop_node<T>  parent_t;
         typedef expression_node<T>* expression_ptr;

         while_loop_bc_node(expression_ptr condition,
                            expression_ptr loop_body)
         : parent_t(condition, loop_body)
         {}

         inline T value() const exprtk_override
         {
            assert(parent_t::condition_.first);
            assert(parent_t::loop_body_.first);

            T result = T(0);

            while (is_true(parent_t::condition_))
            {
               try
               {
                  result = parent_t::loop_body_.first->value();
               }
               catch(const break_exception<T>& e)
               {
                  return e.value;
               }
               catch(const continue_exception&)
               {}
            }

            return result;
         }

         inline std::string to_string() const exprtk_override{
            return "(while_loop_bc_node)";
         }
      };

      template <typename T>
      class while_loop_bc_rtc_node exprtk_final
                                   : public while_loop_bc_node<T>
                                   , public loop_runtime_checker
      {
      public:

         typedef while_loop_bc_node<T> parent_t;
         typedef expression_node<T>*   expression_ptr;

         while_loop_bc_rtc_node(expression_ptr condition,
                                expression_ptr loop_body,
                                loop_runtime_check_ptr loop_rt_chk)
         : parent_t(condition, loop_body)
         , loop_runtime_checker(loop_rt_chk, loop_runtime_check::e_while_loop)
         {}

         inline T value() const exprtk_override
         {
            assert(parent_t::condition_.first);
            assert(parent_t::loop_body_.first);

            T result = T(0);

            loop_runtime_checker::reset();

            while (is_true(parent_t::condition_) && loop_runtime_checker::check())
            {
               try
               {
                  result = parent_t::loop_body_.first->value();
               }
               catch(const break_exception<T>& e)
               {
                  return e.value;
               }
               catch(const continue_exception&)
               {}
            }

            return result;
         }

         inline std::string to_string() const exprtk_override{
            return "(while_loop_bc_rtc_node)";
         }
      };

      template <typename T>
      class repeat_until_loop_bc_node : public repeat_until_loop_node<T>
      {
      public:

         typedef repeat_until_loop_node<T> parent_t;
         typedef expression_node<T>*       expression_ptr;

         repeat_until_loop_bc_node(expression_ptr condition,
                                   expression_ptr loop_body)
         : parent_t(condition, loop_body)
         {}

         inline T value() const exprtk_override
         {
            assert(parent_t::condition_.first);
            assert(parent_t::loop_body_.first);

            T result = T(0);

            do
            {
               try
               {
                  result = parent_t::loop_body_.first->value();
               }
               catch(const break_exception<T>& e)
               {
                  return e.value;
               }
               catch(const continue_exception&)
               {}
            }
            while (is_false(parent_t::condition_.first));

            return result;
         }

         inline std::string to_string() const exprtk_override{
            return "(repeat_until_loop_bc_node)";
         }
      };

      template <typename T>
      class repeat_until_loop_bc_rtc_node exprtk_final
                                          : public repeat_until_loop_bc_node<T>,
                                            public loop_runtime_checker
      {
      public:

         typedef repeat_until_loop_bc_node<T> parent_t;
         typedef expression_node<T>*          expression_ptr;

         repeat_until_loop_bc_rtc_node(expression_ptr condition,
                                       expression_ptr loop_body,
                                       loop_runtime_check_ptr loop_rt_chk)
         : parent_t(condition, loop_body)
         , loop_runtime_checker(loop_rt_chk, loop_runtime_check::e_repeat_until_loop)
         {}

         inline T value() const exprtk_override
         {
            assert(parent_t::condition_.first);
            assert(parent_t::loop_body_.first);

            T result = T(0);

            loop_runtime_checker::reset();

            do
            {
               try
               {
                  result = parent_t::loop_body_.first->value();
               }
               catch(const break_exception<T>& e)
               {
                  return e.value;
               }
               catch(const continue_exception&)
               {}
            }
            while (is_false(parent_t::condition_.first) && loop_runtime_checker::check());

            return result;
         }

         inline std::string to_string() const exprtk_override{
            return "(repeat_until_loop_bc_rtc_node)";
         }
      };

      template <typename T>
      class for_loop_bc_node : public for_loop_node<T>
      {
      public:

         typedef for_loop_node<T>    parent_t;
         typedef expression_node<T>* expression_ptr;

         for_loop_bc_node(expression_ptr initialiser,
                          expression_ptr condition,
                          expression_ptr incrementor,
                          expression_ptr loop_body)
         : parent_t(initialiser, condition, incrementor, loop_body)
         {}

         inline T value() const exprtk_override
         {
            assert(parent_t::condition_.first);
            assert(parent_t::loop_body_.first);

            T result = T(0);

            if (parent_t::initialiser_.first)
               parent_t::initialiser_.first->value();

            if (parent_t::incrementor_.first)
            {
               while (is_true(parent_t::condition_))
               {
                  try
                  {
                     result = parent_t::loop_body_.first->value();
                  }
                  catch(const break_exception<T>& e)
                  {
                     return e.value;
                  }
                  catch(const continue_exception&)
                  {}

                  parent_t::incrementor_.first->value();
               }
            }
            else
            {
               while (is_true(parent_t::condition_))
               {
                  try
                  {
                     result = parent_t::loop_body_.first->value();
                  }
                  catch(const break_exception<T>& e)
                  {
                     return e.value;
                  }
                  catch(const continue_exception&)
                  {}
               }
            }

            return result;
         }

         inline std::string to_string() const exprtk_override{
            return "(for_loop_bc_node)";
         }
      };

      template <typename T>
      class for_loop_bc_rtc_node exprtk_final
                                 : public for_loop_bc_node<T>
                                 , public loop_runtime_checker
      {
      public:

         typedef for_loop_bc_node<T> parent_t;
         typedef expression_node<T>* expression_ptr;

         for_loop_bc_rtc_node(expression_ptr initialiser,
                              expression_ptr condition,
                              expression_ptr incrementor,
                              expression_ptr loop_body,
                              loop_runtime_check_ptr loop_rt_chk)
         : parent_t(initialiser, condition, incrementor, loop_body)
         , loop_runtime_checker(loop_rt_chk, loop_runtime_check::e_for_loop)
         {}

         inline T value() const exprtk_override
         {
            assert(parent_t::condition_.first);
            assert(parent_t::loop_body_.first);

            T result = T(0);

            loop_runtime_checker::reset();

            if (parent_t::initialiser_.first)
               parent_t::initialiser_.first->value();

            if (parent_t::incrementor_.first)
            {
               while (is_true(parent_t::condition_) && loop_runtime_checker::check())
               {
                  try
                  {
                     result = parent_t::loop_body_.first->value();
                  }
                  catch(const break_exception<T>& e)
                  {
                     return e.value;
                  }
                  catch(const continue_exception&)
                  {}

                  parent_t::incrementor_.first->value();
               }
            }
            else
            {
               while (is_true(parent_t::condition_) && loop_runtime_checker::check())
               {
                  try
                  {
                     result = parent_t::loop_body_.first->value();
                  }
                  catch(const break_exception<T>& e)
                  {
                     return e.value;
                  }
                  catch(const continue_exception&)
                  {}
               }
            }

            return result;
         }

         inline std::string to_string() const exprtk_override{
            return "(for_loop_bc_rtc_node)";
         }
      };

      template <typename T>
      class switch_node : public expression_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef std::pair<expression_ptr,bool> branch_t;

         template <typename Allocator,
                   template <typename, typename> class Sequence>
         explicit switch_node(const Sequence<expression_ptr,Allocator>& arg_list)
         {
            if (1 != (arg_list.size() & 1))
               return;

            arg_list_.resize(arg_list.size());

            for (std::size_t i = 0; i < arg_list.size(); ++i)
            {
               if (arg_list[i])
               {
                  construct_branch_pair(arg_list_[i], arg_list[i]);
               }
               else
               {
                  arg_list_.clear();
                  return;
               }
            }
         }

         inline T value() const exprtk_override
         {
            if (!arg_list_.empty())
            {
               const std::size_t upper_bound = (arg_list_.size() - 1);

               for (std::size_t i = 0; i < upper_bound; i += 2)
               {
                  expression_ptr condition  = arg_list_[i    ].first;
                  expression_ptr consequent = arg_list_[i + 1].first;

                  if (is_true(condition))
                  {
                     return consequent->value();
                  }
               }

               return arg_list_[upper_bound].first->value();
            }
            else
               return std::numeric_limits<T>::quiet_NaN();
         }

         inline typename expression_node<T>::node_type type() const exprtk_override exprtk_final
         {
            return expression_node<T>::e_switch;
         }

         void collect_nodes(typename expression_node<T>::noderef_list_t& node_delete_list) exprtk_override
         {
            expression_node<T>::ndb_t::collect(arg_list_, node_delete_list);
         }

         std::size_t node_depth() const exprtk_override exprtk_final
         {
            return expression_node<T>::ndb_t::compute_node_depth(arg_list_);
         }

         inline std::string to_string() const exprtk_override{
            return "(switch_node)";
         }
      protected:

         std::vector<branch_t> arg_list_;
      };

      template <typename T, typename Switch_N>
      class switch_n_node exprtk_final : public switch_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;

         template <typename Allocator,
                   template <typename, typename> class Sequence>
         explicit switch_n_node(const Sequence<expression_ptr,Allocator>& arg_list)
         : switch_node<T>(arg_list)
         {}

         inline T value() const exprtk_override
         {
            return Switch_N::process(switch_node<T>::arg_list_);
         }
      };

      template <typename T>
      class multi_switch_node exprtk_final : public expression_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef std::pair<expression_ptr,bool> branch_t;

         template <typename Allocator,
                   template <typename, typename> class Sequence>
         explicit multi_switch_node(const Sequence<expression_ptr,Allocator>& arg_list)
         {
            if (0 != (arg_list.size() & 1))
               return;

            arg_list_.resize(arg_list.size());

            for (std::size_t i = 0; i < arg_list.size(); ++i)
            {
               if (arg_list[i])
               {
                  construct_branch_pair(arg_list_[i], arg_list[i]);
               }
               else
               {
                  arg_list_.clear();
                  return;
               }
            }
         }

         inline T value() const exprtk_override
         {
            T result = T(0);

            if (arg_list_.empty())
            {
               return std::numeric_limits<T>::quiet_NaN();
            }

            const std::size_t upper_bound = (arg_list_.size() - 1);

            for (std::size_t i = 0; i < upper_bound; i += 2)
            {
               expression_ptr condition  = arg_list_[i    ].first;
               expression_ptr consequent = arg_list_[i + 1].first;

               if (is_true(condition))
               {
                  result = consequent->value();
               }
            }

            return result;
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_mswitch;
         }

         void collect_nodes(typename expression_node<T>::noderef_list_t& node_delete_list) exprtk_override
         {
            expression_node<T>::ndb_t::collect(arg_list_, node_delete_list);
         }

         std::size_t node_depth() const exprtk_override exprtk_final
         {
            return expression_node<T>::ndb_t::compute_node_depth(arg_list_);
         }

         inline std::string to_string() const exprtk_override{
            return "(multi_switch_node)";
         }
      private:

         std::vector<branch_t> arg_list_;
      };

      template <typename T>
      class ivariable
      {
      public:

         virtual ~ivariable() {}

         virtual T& ref() = 0;
         virtual const T& ref() const = 0;
      };

      template <typename T>
      class variable_node exprtk_final
                          : public expression_node<T>,
                            public ivariable      <T>
      {
      public:

         static T null_value;

         explicit variable_node()
         : value_(&null_value)
         {}

         explicit variable_node(T& v, std::string id)
         : value_(&v), id_(id)
         {}

         inline bool operator <(const variable_node<T>& v) const
         {
            return this < (&v);
         }

         inline T value() const exprtk_override
         {
            return (*value_);
         }

         inline T& ref() exprtk_override
         {
            return (*value_);
         }

         inline const T& ref() const exprtk_override
         {
            return (*value_);
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_variable;
         }

         inline std::string to_string() const exprtk_override{
            return id_.empty() ? numeric::num_to_string<T>(*value_) : id_;
         }
      private:

         T* value_;
         std::string id_;
      };

      template <typename T>
      T variable_node<T>::null_value = T(std::numeric_limits<T>::quiet_NaN());

      template <typename T>
      struct range_pack
      {
         typedef expression_node<T>*           expression_node_ptr;
         typedef std::pair<std::size_t,std::size_t> cached_range_t;

         range_pack()
         : n0_e (std::make_pair(false,expression_node_ptr(0)))
         , n1_e (std::make_pair(false,expression_node_ptr(0)))
         , n0_c (std::make_pair(false,0))
         , n1_c (std::make_pair(false,0))
         , cache(std::make_pair(0,0))
         {}

         void clear()
         {
            n0_e  = std::make_pair(false,expression_node_ptr(0));
            n1_e  = std::make_pair(false,expression_node_ptr(0));
            n0_c  = std::make_pair(false,0);
            n1_c  = std::make_pair(false,0);
            cache = std::make_pair(0,0);
         }

         void free()
         {
            if (n0_e.first && n0_e.second)
            {
               n0_e.first = false;

               if (
                    !is_variable_node(n0_e.second) &&
                    !is_string_node  (n0_e.second)
                  )
               {
                  destroy_node(n0_e.second);
               }
            }

            if (n1_e.first && n1_e.second)
            {
               n1_e.first = false;

               if (
                    !is_variable_node(n1_e.second) &&
                    !is_string_node  (n1_e.second)
                  )
               {
                  destroy_node(n1_e.second);
               }
            }
         }

         bool const_range() const
         {
           return ( n0_c.first &&  n1_c.first) &&
                  (!n0_e.first && !n1_e.first);
         }

         bool var_range() const
         {
           return ( n0_e.first &&  n1_e.first) &&
                  (!n0_c.first && !n1_c.first);
         }

         bool operator() (std::size_t& r0, std::size_t& r1,
                          const std::size_t& size = std::numeric_limits<std::size_t>::max()) const
         {
            if (n0_c.first)
               r0 = n0_c.second;
            else if (n0_e.first)
            {
               r0 = static_cast<std::size_t>(details::numeric::to_int64(n0_e.second->value()));
            }
            else
               return false;

            if (n1_c.first)
               r1 = n1_c.second;
            else if (n1_e.first)
            {
               r1 = static_cast<std::size_t>(details::numeric::to_int64(n1_e.second->value()));
            }
            else
               return false;

            if (
                 (std::numeric_limits<std::size_t>::max() != size) &&
                 (std::numeric_limits<std::size_t>::max() == r1  )
               )
            {
               r1 = size - 1;
            }

            cache.first  = r0;
            cache.second = r1;

            if(!enable_range_runtime_checks)
            return (r0 <= r1);
            else
               return range_runtime_check(r0, r1, size);
         }

         inline std::size_t const_size() const
         {
            return (n1_c.second - n0_c.second + 1);
         }

         inline std::size_t cache_size() const
         {
            return (cache.second - cache.first + 1);
         }

         std::pair<bool,expression_node_ptr> n0_e;
         std::pair<bool,expression_node_ptr> n1_e;
         std::pair<bool,std::size_t        > n0_c;
         std::pair<bool,std::size_t        > n1_c;
         mutable cached_range_t             cache;

         bool range_runtime_check(const std::size_t r0,
                                  const std::size_t r1,
                                  const std::size_t size) const
         {
            if (r0 >= size)
            {
               throw std::runtime_error("range error: (r0 < 0) || (r0 >= size)");
               return false;
            }

            if (r1 >= size)
            {
               throw std::runtime_error("range error: (r1 < 0) || (r1 >= size)");
               return false;
            }

            return (r0 <= r1);
         }
      };

      template <typename T>
      class string_base_node;

      template <typename T>
      struct range_data_type
      {
         typedef range_pack<T> range_t;
         typedef string_base_node<T>* strbase_ptr_t;

         range_data_type()
         : range(0)
         , data (0)
         , size (0)
         , type_size(0)
         , str_node (0)
         {}

         range_t*      range;
         void*         data;
         std::size_t   size;
         std::size_t   type_size;
         strbase_ptr_t str_node;
      };

      template <typename T> class vector_node;

      template <typename T>
      class vector_interface
      {
      public:

         typedef vector_node<T>*   vector_node_ptr;
         typedef vec_data_store<T> vds_t;

         virtual ~vector_interface() {}

         virtual std::size_t size   () const = 0;

         virtual vector_node_ptr vec() const = 0;

         virtual vector_node_ptr vec()       = 0;

         virtual       vds_t& vds   ()       = 0;

         virtual const vds_t& vds   () const = 0;

         virtual bool side_effect   () const { return false; }
      };

      template <typename T>
      class vector_node exprtk_final
                        : public expression_node <T>
                        , public vector_interface<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef vector_holder<T>    vector_holder_t;
         typedef vector_node<T>*     vector_node_ptr;
         typedef vec_data_store<T>   vds_t;

         explicit vector_node(vector_holder_t* vh)
         : vector_holder_(vh)
         , vds_((*vector_holder_).size(),(*vector_holder_)[0])
         {
            vector_holder_->set_ref(&vds_.ref());
         }

         vector_node(const vds_t& vds, vector_holder_t* vh)
         : vector_holder_(vh)
         , vds_(vds)
         {}

         inline T value() const exprtk_override
         {
            return vds().data()[0];
         }

         vector_node_ptr vec() const exprtk_override
         {
            return const_cast<vector_node_ptr>(this);
         }

         vector_node_ptr vec() exprtk_override
         {
            return this;
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_vector;
         }

         std::size_t size() const exprtk_override
         {
            return vds().size();
         }

         vds_t& vds() exprtk_override
         {
            return vds_;
         }

         const vds_t& vds() const exprtk_override
         {
            return vds_;
         }

         inline vector_holder_t& vec_holder()
         {
            return (*vector_holder_);
         }

         inline std::string to_string() const exprtk_override{
            return "(vector_node)";
         }
      private:

         vector_holder_t* vector_holder_;
         vds_t                      vds_;
      };

      template <typename T>
      class vector_elem_node exprtk_final
                             : public expression_node<T>,
                               public ivariable      <T>
      {
      public:

         typedef expression_node<T>*            expression_ptr;
         typedef vector_holder<T>               vector_holder_t;
         typedef vector_holder_t*               vector_holder_ptr;
         typedef std::pair<expression_ptr,bool> branch_t;

         vector_elem_node(expression_ptr index, vector_holder_ptr vec_holder)
         : vec_holder_(vec_holder)
         , vector_base_((*vec_holder)[0])
         {
            construct_branch_pair(index_, index);
         }

         inline T value() const exprtk_override
         {
            return *(vector_base_ + static_cast<std::size_t>(details::numeric::to_int64(index_.first->value())));
         }

         inline T& ref() exprtk_override
         {
            return *(vector_base_ + static_cast<std::size_t>(details::numeric::to_int64(index_.first->value())));
         }

         inline const T& ref() const exprtk_override
         {
            return *(vector_base_ + static_cast<std::size_t>(details::numeric::to_int64(index_.first->value())));
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_vecelem;
         }

         inline vector_holder_t& vec_holder()
         {
            return (*vec_holder_);
         }

         void collect_nodes(typename expression_node<T>::noderef_list_t& node_delete_list) exprtk_override
         {
            expression_node<T>::ndb_t::collect(index_, node_delete_list);
         }

         std::size_t node_depth() const exprtk_override
         {
            return expression_node<T>::ndb_t::compute_node_depth(index_);
         }

         inline std::string to_string() const exprtk_override{
            return "(vector_elem_node)";
         }
      private:

         vector_holder_ptr vec_holder_;
         T* vector_base_;
         branch_t index_;
      };

      template <typename T>
      class rebasevector_elem_node exprtk_final
                                   : public expression_node<T>,
                                     public ivariable      <T>
      {
      public:

         typedef expression_node<T>*            expression_ptr;
         typedef vector_holder<T>               vector_holder_t;
         typedef vector_holder_t*               vector_holder_ptr;
         typedef vec_data_store<T>              vds_t;
         typedef std::pair<expression_ptr,bool> branch_t;

         rebasevector_elem_node(expression_ptr index, vector_holder_ptr vec_holder)
         : vector_holder_(vec_holder)
         , vds_((*vector_holder_).size(),(*vector_holder_)[0])
         {
            vector_holder_->set_ref(&vds_.ref());
            construct_branch_pair(index_, index);
         }

         inline T value() const exprtk_override
         {
            return *(vds_.data() + static_cast<std::size_t>(details::numeric::to_int64(index_.first->value())));
         }

         inline T& ref() exprtk_override
         {
            return *(vds_.data() + static_cast<std::size_t>(details::numeric::to_int64(index_.first->value())));
         }

         inline const T& ref() const exprtk_override
         {
            return *(vds_.data() + static_cast<std::size_t>(details::numeric::to_int64(index_.first->value())));
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_rbvecelem;
         }

         inline vector_holder_t& vec_holder()
         {
            return (*vector_holder_);
         }

         void collect_nodes(typename expression_node<T>::noderef_list_t& node_delete_list) exprtk_override
         {
            expression_node<T>::ndb_t::template collect(index_, node_delete_list);
         }

         std::size_t node_depth() const exprtk_override
         {
            return expression_node<T>::ndb_t::compute_node_depth(index_);
         }

      private:

         vector_holder_ptr vector_holder_;
         vds_t             vds_;
         branch_t          index_;
      };

      template <typename T>
      class rebasevector_celem_node exprtk_final
                                    : public expression_node<T>,
                                      public ivariable      <T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef vector_holder<T>    vector_holder_t;
         typedef vector_holder_t*    vector_holder_ptr;
         typedef vec_data_store<T>   vds_t;

         rebasevector_celem_node(const std::size_t index, vector_holder_ptr vec_holder)
         : index_(index)
         , vector_holder_(vec_holder)
         , vds_((*vector_holder_).size(),(*vector_holder_)[0])
         {
            vector_holder_->set_ref(&vds_.ref());
         }

         inline T value() const exprtk_override
         {
            return *(vds_.data() + index_);
         }

         inline T& ref() exprtk_override
         {
            return *(vds_.data() + index_);
         }

         inline const T& ref() const exprtk_override
         {
            return *(vds_.data() + index_);
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_rbveccelem;
         }

         inline vector_holder_t& vec_holder()
         {
            return (*vector_holder_);
         }

         inline std::string to_string() const exprtk_override{
            return "(rebasevector_celem_node)";
         }
      private:

         const std::size_t index_;
         vector_holder_ptr vector_holder_;
         vds_t vds_;
      };

      template <typename T>
      class vector_assignment_node exprtk_final : public expression_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;

         vector_assignment_node(T* vector_base,
                                const std::size_t& size,
                                const std::vector<expression_ptr>& initialiser_list,
                                const bool single_value_initialse)
         : vector_base_(vector_base)
         , initialiser_list_(initialiser_list)
         , size_(size)
         , single_value_initialse_(single_value_initialse)
         {}

         inline T value() const exprtk_override
         {
            if (single_value_initialse_)
            {
               for (std::size_t i = 0; i < size_; ++i)
               {
                  *(vector_base_ + i) = initialiser_list_[0]->value();
               }
            }
            else
            {
               const std::size_t initialiser_list_size = initialiser_list_.size();

               for (std::size_t i = 0; i < initialiser_list_size; ++i)
               {
                  *(vector_base_ + i) = initialiser_list_[i]->value();
               }

               if (initialiser_list_size < size_)
               {
                  for (std::size_t i = initialiser_list_size; i < size_; ++i)
                  {
                     *(vector_base_ + i) = T(0);
                  }
               }
            }

            return *(vector_base_);
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_vecdefass;
         }

         void collect_nodes(typename expression_node<T>::noderef_list_t& node_delete_list) exprtk_override
         {
            expression_node<T>::ndb_t::collect(initialiser_list_, node_delete_list);
         }

         std::size_t node_depth() const exprtk_override
         {
            return expression_node<T>::ndb_t::compute_node_depth(initialiser_list_);
         }

         inline std::string to_string() const exprtk_override{
            return "(vector_assignment_node)";
         }
      private:

         vector_assignment_node(const vector_assignment_node<T>&) exprtk_delete;
         vector_assignment_node<T>& operator=(const vector_assignment_node<T>&) exprtk_delete;

         mutable T* vector_base_;
         std::vector<expression_ptr> initialiser_list_;
         const std::size_t size_;
         const bool single_value_initialse_;
      };

      template <typename T>
      class swap_node exprtk_final : public expression_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef variable_node<T>*   variable_node_ptr;

         swap_node(variable_node_ptr var0, variable_node_ptr var1)
         : var0_(var0)
         , var1_(var1)
         {}

         inline T value() const exprtk_override
         {
            std::swap(var0_->ref(),var1_->ref());
            return var1_->ref();
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_swap;
         }

         inline std::string to_string() const exprtk_override{
            return "(swap_node)";
         }
      private:

         variable_node_ptr var0_;
         variable_node_ptr var1_;
      };

      template <typename T>
      class swap_generic_node exprtk_final : public binary_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef ivariable<T>*       ivariable_ptr;

         swap_generic_node(expression_ptr var0, expression_ptr var1)
         : binary_node<T>(details::e_swap, var0, var1)
         , var0_(dynamic_cast<ivariable_ptr>(var0))
         , var1_(dynamic_cast<ivariable_ptr>(var1))
         {}

         inline T value() const exprtk_override
         {
            std::swap(var0_->ref(),var1_->ref());
            return var1_->ref();
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_swap;
         }

      private:

         ivariable_ptr var0_;
         ivariable_ptr var1_;
      };

      template <typename T>
      class swap_vecvec_node exprtk_final
                             : public binary_node     <T>
                             , public vector_interface<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef vector_node    <T>* vector_node_ptr;
         typedef vec_data_store <T>  vds_t;

         using binary_node<T>::branch;

         swap_vecvec_node(expression_ptr branch0,
                          expression_ptr branch1)
         : binary_node<T>(details::e_swap, branch0, branch1)
         , vec0_node_ptr_(0)
         , vec1_node_ptr_(0)
         , vec_size_     (0)
         , initialised_  (false)
         {
            if (is_ivector_node(branch(0)))
            {
               vector_interface<T>* vi = reinterpret_cast<vector_interface<T>*>(0);

               if (0 != (vi = dynamic_cast<vector_interface<T>*>(branch(0))))
               {
                  vec0_node_ptr_ = vi->vec();
                  vds()          = vi->vds();
               }
            }

            if (is_ivector_node(branch(1)))
            {
               vector_interface<T>* vi = reinterpret_cast<vector_interface<T>*>(0);

               if (0 != (vi = dynamic_cast<vector_interface<T>*>(branch(1))))
               {
                  vec1_node_ptr_ = vi->vec();
               }
            }

            if (vec0_node_ptr_ && vec1_node_ptr_)
            {
               vec_size_ = std::min(vec0_node_ptr_->vds().size(),
                                    vec1_node_ptr_->vds().size());

               initialised_ = true;
            }

            assert(initialised_);
         }

         inline T value() const exprtk_override
         {
            if (initialised_)
            {
               assert(branch(0));
               assert(branch(1));

               binary_node<T>::branch(0)->value();
               binary_node<T>::branch(1)->value();

               T* vec0 = vec0_node_ptr_->vds().data();
               T* vec1 = vec1_node_ptr_->vds().data();

               for (std::size_t i = 0; i < vec_size_; ++i)
               {
                  std::swap(vec0[i],vec1[i]);
               }

               return vec1_node_ptr_->value();
            }
            else
               return std::numeric_limits<T>::quiet_NaN();
         }

         vector_node_ptr vec() const exprtk_override
         {
            return vec0_node_ptr_;
         }

         vector_node_ptr vec() exprtk_override
         {
            return vec0_node_ptr_;
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_vecvecswap;
         }

         std::size_t size() const exprtk_override
         {
            return vec_size_;
         }

         vds_t& vds() exprtk_override
         {
            return vds_;
         }

         const vds_t& vds() const exprtk_override
         {
            return vds_;
         }

         inline std::string to_string() const exprtk_override{
            return "(swap_vecvec_node)";
         }
      private:

         vector_node<T>* vec0_node_ptr_;
         vector_node<T>* vec1_node_ptr_;
         std::size_t     vec_size_;
         bool            initialised_;
         vds_t           vds_;
      };

      template <typename T>
      class stringvar_node exprtk_final
                           : public expression_node <T>,
                             public string_base_node<T>,
                             public range_interface <T>
      {
      public:

         typedef typename range_interface<T>::range_t range_t;

         static std::string null_value;

         explicit stringvar_node()
         : value_(&null_value)
         {}

         explicit stringvar_node(std::string& v)
         : value_(&v)
         {
            rp_.n0_c = std::make_pair<bool,std::size_t>(true,0);
            rp_.n1_c = std::make_pair<bool,std::size_t>(true,v.size() - 1);
            rp_.cache.first  = rp_.n0_c.second;
            rp_.cache.second = rp_.n1_c.second;
         }

         inline bool operator <(const stringvar_node<T>& v) const
         {
            return this < (&v);
         }

         inline T value() const exprtk_override
         {
            rp_.n1_c.second  = (*value_).size() - 1;
            rp_.cache.second = rp_.n1_c.second;

            return std::numeric_limits<T>::quiet_NaN();
         }

         std::string str() const exprtk_override
         {
            return ref();
         }

         char_cptr base() const exprtk_override
         {
            return &(*value_)[0];
         }

         std::size_t size() const exprtk_override
         {
            return ref().size();
         }

         std::string& ref()
         {
            return (*value_);
         }

         const std::string& ref() const
         {
            return (*value_);
         }

         range_t& range_ref() exprtk_override
         {
            return rp_;
         }

         const range_t& range_ref() const exprtk_override
         {
            return rp_;
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_stringvar;
         }

         void rebase(std::string& s)
         {
            value_ = &s;
            rp_.n0_c = std::make_pair<bool,std::size_t>(true,0);
            rp_.n1_c = std::make_pair<bool,std::size_t>(true,value_->size() - 1);
            rp_.cache.first  = rp_.n0_c.second;
            rp_.cache.second = rp_.n1_c.second;
         }

         inline std::string to_string() const exprtk_override{
            return "(stringvar_node)";
         }
      private:

         std::string* value_;
         mutable range_t rp_;
      };

      template <typename T>
      std::string stringvar_node<T>::null_value = std::string("");

      template <typename T>
      class string_range_node exprtk_final
                              : public expression_node <T>,
                                public string_base_node<T>,
                                public range_interface <T>
      {
      public:

         typedef typename range_interface<T>::range_t range_t;

         static std::string null_value;

         explicit string_range_node(std::string& v, const range_t& rp)
         : value_(&v)
         , rp_(rp)
         {}

         virtual ~string_range_node()
         {
            rp_.free();
         }

         inline bool operator <(const string_range_node<T>& v) const
         {
            return this < (&v);
         }

         inline T value() const exprtk_override
         {
            return std::numeric_limits<T>::quiet_NaN();
         }

         inline std::string str() const exprtk_override
         {
            return (*value_);
         }

         char_cptr base() const exprtk_override
         {
            return &(*value_)[0];
         }

         std::size_t size() const exprtk_override
         {
            return ref().size();
         }

         inline range_t range() const
         {
            return rp_;
         }

         inline virtual std::string& ref()
         {
            return (*value_);
         }

         inline virtual const std::string& ref() const
         {
            return (*value_);
         }

         inline range_t& range_ref() exprtk_override
         {
            return rp_;
         }

         inline const range_t& range_ref() const exprtk_override
         {
            return rp_;
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_stringvarrng;
         }

         inline std::string to_string() const exprtk_override{
            return "(string_range_node)";
         }
      private:

         std::string* value_;
         range_t      rp_;
      };

      template <typename T>
      std::string string_range_node<T>::null_value = std::string("");

      template <typename T>
      class const_string_range_node exprtk_final
                                    : public expression_node <T>,
                                      public string_base_node<T>,
                                      public range_interface <T>
      {
      public:

         typedef typename range_interface<T>::range_t range_t;

         explicit const_string_range_node(const std::string& v, const range_t& rp)
         : value_(v)
         , rp_(rp)
         {}

        ~const_string_range_node()
         {
            rp_.free();
         }

         inline T value() const exprtk_override
         {
            return std::numeric_limits<T>::quiet_NaN();
         }

         std::string str() const exprtk_override
         {
            return value_;
         }

         char_cptr base() const exprtk_override
         {
            return value_.data();
         }

         std::size_t size() const exprtk_override
         {
            return value_.size();
         }

         range_t range() const
         {
            return rp_;
         }

         range_t& range_ref() exprtk_override
         {
            return rp_;
         }

         const range_t& range_ref() const exprtk_override
         {
            return rp_;
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_cstringvarrng;
         }

         inline std::string to_string() const exprtk_override{
            return "(const_string_range_node)";
         }
      private:

         const_string_range_node(const const_string_range_node<T>&) exprtk_delete;
         const_string_range_node<T>& operator=(const const_string_range_node<T>&) exprtk_delete;

         const std::string value_;
         range_t rp_;
      };

      template <typename T>
      class generic_string_range_node exprtk_final
                                      : public expression_node <T>,
                                        public string_base_node<T>,
                                        public range_interface <T>
      {
      public:

         typedef expression_node <T>* expression_ptr;
         typedef stringvar_node  <T>* strvar_node_ptr;
         typedef string_base_node<T>* str_base_ptr;
         typedef typename range_interface<T>::range_t range_t;
         typedef range_t*             range_ptr;
         typedef range_interface<T>   irange_t;
         typedef irange_t*            irange_ptr;
         typedef std::pair<expression_ptr,bool>  branch_t;

         generic_string_range_node(expression_ptr str_branch, const range_t& brange)
         : initialised_(false)
         , str_base_ptr_ (0)
         , str_range_ptr_(0)
         , base_range_(brange)
         {
            range_.n0_c = std::make_pair<bool,std::size_t>(true,0);
            range_.n1_c = std::make_pair<bool,std::size_t>(true,0);
            range_.cache.first  = range_.n0_c.second;
            range_.cache.second = range_.n1_c.second;

            construct_branch_pair(branch_, str_branch);

            if (is_generally_string_node(branch_.first))
            {
               str_base_ptr_ = dynamic_cast<str_base_ptr>(branch_.first);

               if (0 == str_base_ptr_)
                  return;

               str_range_ptr_ = dynamic_cast<irange_ptr>(branch_.first);

               if (0 == str_range_ptr_)
                  return;
            }

            initialised_ = (str_base_ptr_ && str_range_ptr_);

            assert(initialised_);
         }

        ~generic_string_range_node()
         {
            base_range_.free();
         }

         inline T value() const exprtk_override
         {
            if (initialised_)
            {
               assert(branch_.first);

               branch_.first->value();

               std::size_t str_r0 = 0;
               std::size_t str_r1 = 0;

               std::size_t r0 = 0;
               std::size_t r1 = 0;

               const range_t& range = str_range_ptr_->range_ref();

               const std::size_t base_str_size = str_base_ptr_->size();

               if (
                    range      (str_r0, str_r1, base_str_size) &&
                    base_range_(    r0,     r1, base_str_size - str_r0)
                  )
               {
                  const std::size_t size = (r1 - r0) + 1;

                  range_.n1_c.second  = size - 1;
                  range_.cache.second = range_.n1_c.second;

                  value_.assign(str_base_ptr_->base() + str_r0 + r0, size);
               }
            }

            return std::numeric_limits<T>::quiet_NaN();
         }

         std::string str() const exprtk_override
         {
            return value_;
         }

         char_cptr base() const exprtk_override
         {
            return &value_[0];
         }

         std::size_t size() const exprtk_override
         {
            return value_.size();
         }

         range_t& range_ref() exprtk_override
         {
            return range_;
         }

         const range_t& range_ref() const exprtk_override
         {
            return range_;
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_strgenrange;
         }

         void collect_nodes(typename expression_node<T>::noderef_list_t& node_delete_list) exprtk_override
         {
            expression_node<T>::ndb_t::collect(branch_, node_delete_list);
         }

         std::size_t node_depth() const exprtk_override
         {
            return expression_node<T>::ndb_t::compute_node_depth(branch_);
         }

         inline std::string to_string() const exprtk_override{
            return "(generic_string_range_node)";
         }
      private:

         bool                initialised_;
         branch_t            branch_;
         str_base_ptr        str_base_ptr_;
         irange_ptr          str_range_ptr_;
         mutable range_t     base_range_;
         mutable range_t     range_;
         mutable std::string value_;
      };

      template <typename T>
      class string_concat_node exprtk_final
                               : public binary_node     <T>,
                                 public string_base_node<T>,
                                 public range_interface <T>
      {
      public:

         typedef typename range_interface<T>::range_t range_t;
         typedef range_interface<T>   irange_t;
         typedef irange_t*            irange_ptr;
         typedef range_t*             range_ptr;
         typedef expression_node <T>* expression_ptr;
         typedef string_base_node<T>* str_base_ptr;

         using binary_node<T>::branch;

         string_concat_node(const operator_type& opr,
                            expression_ptr branch0,
                            expression_ptr branch1)
         : binary_node<T>(opr, branch0, branch1)
         , initialised_(false)
         , str0_base_ptr_ (0)
         , str1_base_ptr_ (0)
         , str0_range_ptr_(0)
         , str1_range_ptr_(0)
         {
            range_.n0_c = std::make_pair<bool,std::size_t>(true,0);
            range_.n1_c = std::make_pair<bool,std::size_t>(true,0);

            range_.cache.first  = range_.n0_c.second;
            range_.cache.second = range_.n1_c.second;

            if (is_generally_string_node(branch(0)))
            {
               str0_base_ptr_ = dynamic_cast<str_base_ptr>(branch(0));

               if (0 == str0_base_ptr_)
                  return;

               str0_range_ptr_ = dynamic_cast<irange_ptr>(branch(0));

               if (0 == str0_range_ptr_)
                  return;
            }

            if (is_generally_string_node(branch(1)))
            {
               str1_base_ptr_ = dynamic_cast<str_base_ptr>(branch(1));

               if (0 == str1_base_ptr_)
                  return;

               str1_range_ptr_ = dynamic_cast<irange_ptr>(branch(1));

               if (0 == str1_range_ptr_)
                  return;
            }

            initialised_ = str0_base_ptr_  &&
                           str1_base_ptr_  &&
                           str0_range_ptr_ &&
                           str1_range_ptr_ ;

            assert(initialised_);
         }

         inline T value() const exprtk_override
         {
            if (initialised_)
            {
               assert(branch(0));
               assert(branch(1));

               branch(0)->value();
               branch(1)->value();

               std::size_t str0_r0 = 0;
               std::size_t str0_r1 = 0;

               std::size_t str1_r0 = 0;
               std::size_t str1_r1 = 0;

               const range_t& range0 = str0_range_ptr_->range_ref();
               const range_t& range1 = str1_range_ptr_->range_ref();

               if (
                    range0(str0_r0, str0_r1, str0_base_ptr_->size()) &&
                    range1(str1_r0, str1_r1, str1_base_ptr_->size())
                  )
               {
                  const std::size_t size0 = (str0_r1 - str0_r0) + 1;
                  const std::size_t size1 = (str1_r1 - str1_r0) + 1;

                  value_.assign(str0_base_ptr_->base() + str0_r0, size0);
                  value_.append(str1_base_ptr_->base() + str1_r0, size1);

                  range_.n1_c.second  = value_.size() - 1;
                  range_.cache.second = range_.n1_c.second;
               }
            }

            return std::numeric_limits<T>::quiet_NaN();
         }

         std::string str() const exprtk_override
         {
            return value_;
         }

         char_cptr base() const exprtk_override
         {
            return &value_[0];
         }

         std::size_t size() const exprtk_override
         {
            return value_.size();
         }

         range_t& range_ref() exprtk_override
         {
            return range_;
         }

         const range_t& range_ref() const exprtk_override
         {
            return range_;
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_strconcat;
         }

         inline std::string to_string() const exprtk_override{
            return "(string_concat_node)";
         }
      private:

         bool                initialised_;
         str_base_ptr        str0_base_ptr_;
         str_base_ptr        str1_base_ptr_;
         irange_ptr          str0_range_ptr_;
         irange_ptr          str1_range_ptr_;
         mutable range_t     range_;
         mutable std::string value_;
      };

      template <typename T>
      class swap_string_node exprtk_final
                             : public binary_node     <T>,
                               public string_base_node<T>,
                               public range_interface <T>
      {
      public:

         typedef typename range_interface<T>::range_t range_t;
         typedef range_t*             range_ptr;
         typedef range_interface<T>   irange_t;
         typedef irange_t*            irange_ptr;
         typedef expression_node <T>* expression_ptr;
         typedef stringvar_node  <T>* strvar_node_ptr;
         typedef string_base_node<T>* str_base_ptr;

         using binary_node<T>::branch;

         swap_string_node(expression_ptr branch0, expression_ptr branch1)
         : binary_node<T>(details::e_swap, branch0, branch1),
           initialised_(false),
           str0_node_ptr_(0),
           str1_node_ptr_(0)
         {
            if (is_string_node(branch(0)))
            {
               str0_node_ptr_ = static_cast<strvar_node_ptr>(branch(0));
            }

            if (is_string_node(branch(1)))
            {
               str1_node_ptr_ = static_cast<strvar_node_ptr>(branch(1));
            }

            initialised_ = (str0_node_ptr_ && str1_node_ptr_);

            assert(initialised_);
         }

         inline T value() const exprtk_override
         {
            if (initialised_)
            {
               assert(branch(0));
               assert(branch(1));

               branch(0)->value();
               branch(1)->value();

               std::swap(str0_node_ptr_->ref(), str1_node_ptr_->ref());
            }

            return std::numeric_limits<T>::quiet_NaN();
         }

         std::string str() const exprtk_override
         {
            return str0_node_ptr_->str();
         }

         char_cptr base() const exprtk_override
         {
           return str0_node_ptr_->base();
         }

         std::size_t size() const exprtk_override
         {
            return str0_node_ptr_->size();
         }

         range_t& range_ref() exprtk_override
         {
            return str0_node_ptr_->range_ref();
         }

         const range_t& range_ref() const exprtk_override
         {
            return str0_node_ptr_->range_ref();
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_strswap;
         }

         inline std::string to_string() const exprtk_override{
            return "(swap_string_node)";
         }
      private:

         bool initialised_;
         strvar_node_ptr str0_node_ptr_;
         strvar_node_ptr str1_node_ptr_;
      };

      template <typename T>
      class swap_genstrings_node exprtk_final : public binary_node<T>
      {
      public:

         typedef typename range_interface<T>::range_t range_t;
         typedef range_t*             range_ptr;
         typedef range_interface<T>   irange_t;
         typedef irange_t*            irange_ptr;
         typedef expression_node <T>* expression_ptr;
         typedef string_base_node<T>* str_base_ptr;

         using binary_node<T>::branch;

         swap_genstrings_node(expression_ptr branch0,
                              expression_ptr branch1)
         : binary_node<T>(details::e_default, branch0, branch1)
         , str0_base_ptr_ (0)
         , str1_base_ptr_ (0)
         , str0_range_ptr_(0)
         , str1_range_ptr_(0)
         , initialised_(false)
         {
            if (is_generally_string_node(branch(0)))
            {
               str0_base_ptr_ = dynamic_cast<str_base_ptr>(branch(0));

               if (0 == str0_base_ptr_)
                  return;

               irange_ptr range = dynamic_cast<irange_ptr>(branch(0));

               if (0 == range)
                  return;

               str0_range_ptr_ = &(range->range_ref());
            }

            if (is_generally_string_node(branch(1)))
            {
               str1_base_ptr_ = dynamic_cast<str_base_ptr>(branch(1));

               if (0 == str1_base_ptr_)
                  return;

               irange_ptr range = dynamic_cast<irange_ptr>(branch(1));

               if (0 == range)
                  return;

               str1_range_ptr_ = &(range->range_ref());
            }

            initialised_ = str0_base_ptr_  &&
                           str1_base_ptr_  &&
                           str0_range_ptr_ &&
                           str1_range_ptr_ ;

            assert(initialised_);
         }

         inline T value() const exprtk_override
         {
            if (initialised_)
            {
               assert(branch(0));
               assert(branch(1));

               branch(0)->value();
               branch(1)->value();

               std::size_t str0_r0 = 0;
               std::size_t str0_r1 = 0;

               std::size_t str1_r0 = 0;
               std::size_t str1_r1 = 0;

               const range_t& range0 = (*str0_range_ptr_);
               const range_t& range1 = (*str1_range_ptr_);

               if (
                    range0(str0_r0, str0_r1, str0_base_ptr_->size()) &&
                    range1(str1_r0, str1_r1, str1_base_ptr_->size())
                  )
               {
                  const std::size_t size0    = range0.cache_size();
                  const std::size_t size1    = range1.cache_size();
                  const std::size_t max_size = std::min(size0,size1);

                  char_ptr s0 = const_cast<char_ptr>(str0_base_ptr_->base() + str0_r0);
                  char_ptr s1 = const_cast<char_ptr>(str1_base_ptr_->base() + str1_r0);

                  loop_unroll::details lud(max_size);
                  char_cptr upper_bound = s0 + lud.upper_bound;

                  while (s0 < upper_bound)
                  {
                     #define exprtk_loop(N)   \
                     std::swap(s0[N], s1[N]); \

                     exprtk_loop( 0) exprtk_loop( 1)
                     exprtk_loop( 2) exprtk_loop( 3)
                     exprtk_loop( 4) exprtk_loop( 5)
                     exprtk_loop( 6) exprtk_loop( 7)
                     exprtk_loop( 8) exprtk_loop( 9)
                     exprtk_loop(10) exprtk_loop(11)
                     exprtk_loop(12) exprtk_loop(13)
                     exprtk_loop(14) exprtk_loop(15)

                     s0 += lud.batch_size;
                     s1 += lud.batch_size;
                  }

                  int i = 0;

                  exprtk_disable_fallthrough_begin
                  switch (lud.remainder)
                  {
                     #define case_stmt(N)                       \
                     case N : { std::swap(s0[i], s1[i]); ++i; } \

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
               }
            }

            return std::numeric_limits<T>::quiet_NaN();
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_strswap;
         }

         inline std::string to_string() const exprtk_override{
            return "(swap_genstrings_node)";
         }
      private:

         swap_genstrings_node(const swap_genstrings_node<T>&) exprtk_delete;
         swap_genstrings_node<T>& operator=(const swap_genstrings_node<T>&) exprtk_delete;

         str_base_ptr str0_base_ptr_;
         str_base_ptr str1_base_ptr_;
         range_ptr    str0_range_ptr_;
         range_ptr    str1_range_ptr_;
         bool         initialised_;
      };

      template <typename T>
      class stringvar_size_node exprtk_final : public expression_node<T>
      {
      public:

         static std::string null_value;

         explicit stringvar_size_node()
         : value_(&null_value)
         {}

         explicit stringvar_size_node(std::string& v)
         : value_(&v)
         {}

         inline T value() const exprtk_override
         {
            return T((*value_).size());
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_stringvarsize;
         }

         inline std::string to_string() const exprtk_override{
            return "(stringvar_size_node)";
         }
      private:

         std::string* value_;
      };

      template <typename T>
      std::string stringvar_size_node<T>::null_value = std::string("");

      template <typename T>
      class string_size_node exprtk_final : public expression_node<T>
      {
      public:

         typedef expression_node <T>* expression_ptr;
         typedef string_base_node<T>* str_base_ptr;
         typedef std::pair<expression_ptr,bool>  branch_t;

         explicit string_size_node(expression_ptr branch)
         : str_base_ptr_(0)
         {
            construct_branch_pair(branch_, branch);

            if (is_generally_string_node(branch_.first))
            {
               str_base_ptr_ = dynamic_cast<str_base_ptr>(branch_.first);

               if (0 == str_base_ptr_)
                  return;
            }
         }

         inline T value() const exprtk_override
         {
            T result = std::numeric_limits<T>::quiet_NaN();

            if (str_base_ptr_)
            {
               branch_.first->value();
               result = T(str_base_ptr_->size());
            }

            return result;
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_stringsize;
         }

         void collect_nodes(typename expression_node<T>::noderef_list_t& node_delete_list) exprtk_override
         {
            expression_node<T>::ndb_t::collect(branch_, node_delete_list);
         }

         std::size_t node_depth() const exprtk_override
         {
            return expression_node<T>::ndb_t::compute_node_depth(branch_);
         }

         inline std::string to_string() const exprtk_override{
            return "(string_size_node)";
         }
      private:

         branch_t           branch_;
         str_base_ptr str_base_ptr_;
      };

      struct asn_assignment
      {
         static inline void execute(std::string& s, char_cptr data, const std::size_t size)
         { s.assign(data,size); }
      };

      struct asn_addassignment
      {
         static inline void execute(std::string& s, char_cptr data, const std::size_t size)
         { s.append(data,size); }
      };

      template <typename T, typename AssignmentProcess = asn_assignment>
      class assignment_string_node exprtk_final
                                   : public binary_node     <T>,
                                     public string_base_node<T>,
                                     public range_interface <T>
      {
      public:

         typedef typename range_interface<T>::range_t range_t;
         typedef range_t*             range_ptr;
         typedef range_interface <T>  irange_t;
         typedef irange_t*            irange_ptr;
         typedef expression_node <T>* expression_ptr;
         typedef stringvar_node  <T>* strvar_node_ptr;
         typedef string_base_node<T>* str_base_ptr;

         using binary_node<T>::branch;

         assignment_string_node(const operator_type& opr,
                                expression_ptr branch0,
                                expression_ptr branch1)
         : binary_node<T>(opr, branch0, branch1)
         , initialised_(false)
         , str0_base_ptr_ (0)
         , str1_base_ptr_ (0)
         , str0_node_ptr_ (0)
         , str1_range_ptr_(0)
         {
            if (is_string_node(branch(0)))
            {
               str0_node_ptr_ = static_cast<strvar_node_ptr>(branch(0));
               str0_base_ptr_ = dynamic_cast<str_base_ptr>(branch(0));
            }

            if (is_generally_string_node(branch(1)))
            {
               str1_base_ptr_ = dynamic_cast<str_base_ptr>(branch(1));

               if (0 == str1_base_ptr_)
                  return;

               irange_ptr range = dynamic_cast<irange_ptr>(branch(1));

               if (0 == range)
                  return;

               str1_range_ptr_ = &(range->range_ref());
            }

            initialised_ = str0_base_ptr_  &&
                           str1_base_ptr_  &&
                           str0_node_ptr_  &&
                           str1_range_ptr_ ;

            assert(initialised_);
         }

         inline T value() const exprtk_override
         {
            if (initialised_)
            {
               assert(branch(0));
               assert(branch(1));

               branch(1)->value();

               std::size_t r0 = 0;
               std::size_t r1 = 0;

               const range_t& range = (*str1_range_ptr_);

               if (range(r0, r1, str1_base_ptr_->size()))
               {
                  AssignmentProcess::execute(str0_node_ptr_->ref(),
                                             str1_base_ptr_->base() + r0,
                                             (r1 - r0) + 1);

                  branch(0)->value();
               }
            }

            return std::numeric_limits<T>::quiet_NaN();
         }

         std::string str() const exprtk_override
         {
            return str0_node_ptr_->str();
         }

         char_cptr base() const exprtk_override
         {
           return str0_node_ptr_->base();
         }

         std::size_t size() const exprtk_override
         {
            return str0_node_ptr_->size();
         }

         range_t& range_ref() exprtk_override
         {
            return str0_node_ptr_->range_ref();
         }

         const range_t& range_ref() const exprtk_override
         {
            return str0_node_ptr_->range_ref();
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_strass;
         }

         inline std::string to_string() const exprtk_override{
            return "(assignment_string_node)";
         }
      private:

         bool            initialised_;
         str_base_ptr    str0_base_ptr_;
         str_base_ptr    str1_base_ptr_;
         strvar_node_ptr str0_node_ptr_;
         range_ptr       str1_range_ptr_;
      };

      template <typename T, typename AssignmentProcess = asn_assignment>
      class assignment_string_range_node exprtk_final
                                         : public binary_node     <T>,
                                           public string_base_node<T>,
                                           public range_interface <T>
      {
      public:

         typedef typename range_interface<T>::range_t range_t;
         typedef range_t*              range_ptr;
         typedef range_interface  <T>  irange_t;
         typedef irange_t*             irange_ptr;
         typedef expression_node  <T>* expression_ptr;
         typedef stringvar_node   <T>* strvar_node_ptr;
         typedef string_range_node<T>* str_rng_node_ptr;
         typedef string_base_node <T>* str_base_ptr;

         using binary_node<T>::branch;

         assignment_string_range_node(const operator_type& opr,
                                      expression_ptr branch0,
                                      expression_ptr branch1)
         : binary_node<T>(opr, branch0, branch1)
         , initialised_(false)
         , str0_base_ptr_    (0)
         , str1_base_ptr_    (0)
         , str0_rng_node_ptr_(0)
         , str0_range_ptr_   (0)
         , str1_range_ptr_   (0)
         {
            if (is_string_range_node(branch(0)))
            {
               str0_rng_node_ptr_ = static_cast<str_rng_node_ptr>(branch(0));
               str0_base_ptr_     = dynamic_cast<str_base_ptr>(branch(0));
               irange_ptr range   = dynamic_cast<irange_ptr>(branch(0));

               if (0 == range)
                  return;

               str0_range_ptr_ = &(range->range_ref());
            }

            if (is_generally_string_node(branch(1)))
            {
               str1_base_ptr_ = dynamic_cast<str_base_ptr>(branch(1));

               if (0 == str1_base_ptr_)
                  return;

               irange_ptr range = dynamic_cast<irange_ptr>(branch(1));

               if (0 == range)
                  return;

               str1_range_ptr_ = &(range->range_ref());
            }

            initialised_ = str0_base_ptr_     &&
                           str1_base_ptr_     &&
                           str0_rng_node_ptr_ &&
                           str0_range_ptr_    &&
                           str1_range_ptr_    ;

            assert(initialised_);
         }

         inline T value() const exprtk_override
         {
            if (initialised_)
            {
               assert(branch(0));
               assert(branch(1));

               branch(0)->value();
               branch(1)->value();

               std::size_t s0_r0 = 0;
               std::size_t s0_r1 = 0;

               std::size_t s1_r0 = 0;
               std::size_t s1_r1 = 0;

               const range_t& range0 = (*str0_range_ptr_);
               const range_t& range1 = (*str1_range_ptr_);

               if (
                    range0(s0_r0, s0_r1, str0_base_ptr_->size()) &&
                    range1(s1_r0, s1_r1, str1_base_ptr_->size())
                  )
               {
                  const std::size_t size = std::min((s0_r1 - s0_r0), (s1_r1 - s1_r0)) + 1;

                  std::copy(str1_base_ptr_->base() + s1_r0,
                            str1_base_ptr_->base() + s1_r0 + size,
                            const_cast<char_ptr>(base() + s0_r0));
               }
            }

            return std::numeric_limits<T>::quiet_NaN();
         }

         std::string str() const exprtk_override
         {
            return str0_base_ptr_->str();
         }

         char_cptr base() const exprtk_override
         {
            return str0_base_ptr_->base();
         }

         std::size_t size() const exprtk_override
         {
            return str0_base_ptr_->size();
         }

         range_t& range_ref() exprtk_override
         {
            return str0_rng_node_ptr_->range_ref();
         }

         const range_t& range_ref() const exprtk_override
         {
            return str0_rng_node_ptr_->range_ref();
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_strass;
         }

         inline std::string to_string() const exprtk_override{
            return "(assignment_string_range_node)";
         }
      private:

         bool             initialised_;
         str_base_ptr     str0_base_ptr_;
         str_base_ptr     str1_base_ptr_;
         str_rng_node_ptr str0_rng_node_ptr_;
         range_ptr        str0_range_ptr_;
         range_ptr        str1_range_ptr_;
      };

      template <typename T>
      class conditional_string_node exprtk_final
                                    : public trinary_node    <T>,
                                      public string_base_node<T>,
                                      public range_interface <T>
      {
      public:

         typedef typename range_interface<T>::range_t range_t;
         typedef range_t*             range_ptr;
         typedef range_interface <T>  irange_t;
         typedef irange_t*            irange_ptr;
         typedef expression_node <T>* expression_ptr;
         typedef string_base_node<T>* str_base_ptr;

         conditional_string_node(expression_ptr condition,
                                 expression_ptr consequent,
                                 expression_ptr alternative)
         : trinary_node<T>(details::e_default, consequent, alternative, condition)
         , initialised_(false)
         , str0_base_ptr_ (0)
         , str1_base_ptr_ (0)
         , str0_range_ptr_(0)
         , str1_range_ptr_(0)
         , condition_  (condition  )
         , consequent_ (consequent )
         , alternative_(alternative)
         {
            range_.n0_c = std::make_pair<bool,std::size_t>(true,0);
            range_.n1_c = std::make_pair<bool,std::size_t>(true,0);

            range_.cache.first  = range_.n0_c.second;
            range_.cache.second = range_.n1_c.second;

            if (is_generally_string_node(trinary_node<T>::branch_[0].first))
            {
               str0_base_ptr_ = dynamic_cast<str_base_ptr>(trinary_node<T>::branch_[0].first);

               if (0 == str0_base_ptr_)
                  return;

               str0_range_ptr_ = dynamic_cast<irange_ptr>(trinary_node<T>::branch_[0].first);

               if (0 == str0_range_ptr_)
                  return;
            }

            if (is_generally_string_node(trinary_node<T>::branch_[1].first))
            {
               str1_base_ptr_ = dynamic_cast<str_base_ptr>(trinary_node<T>::branch_[1].first);

               if (0 == str1_base_ptr_)
                  return;

               str1_range_ptr_ = dynamic_cast<irange_ptr>(trinary_node<T>::branch_[1].first);

               if (0 == str1_range_ptr_)
                  return;
            }

            initialised_ = str0_base_ptr_  &&
                           str1_base_ptr_  &&
                           str0_range_ptr_ &&
                           str1_range_ptr_ ;

            assert(initialised_);
         }

         inline T value() const exprtk_override
         {
            if (initialised_)
            {
               assert(condition_  );
               assert(consequent_ );
               assert(alternative_);

               std::size_t r0 = 0;
               std::size_t r1 = 0;

               if (is_true(condition_))
               {
                  consequent_->value();

                  const range_t& range = str0_range_ptr_->range_ref();

                  if (range(r0, r1, str0_base_ptr_->size()))
                  {
                     const std::size_t size = (r1 - r0) + 1;

                     value_.assign(str0_base_ptr_->base() + r0, size);

                     range_.n1_c.second  = value_.size() - 1;
                     range_.cache.second = range_.n1_c.second;

                     return T(1);
                  }
               }
               else
               {
                  alternative_->value();

                  const range_t& range = str1_range_ptr_->range_ref();

                  if (range(r0, r1, str1_base_ptr_->size()))
                  {
                     const std::size_t size = (r1 - r0) + 1;

                     value_.assign(str1_base_ptr_->base() + r0, size);

                     range_.n1_c.second  = value_.size() - 1;
                     range_.cache.second = range_.n1_c.second;

                     return T(0);
                  }
               }
            }

            return std::numeric_limits<T>::quiet_NaN();
         }

         std::string str() const exprtk_override
         {
            return value_;
         }

         char_cptr base() const exprtk_override
         {
            return &value_[0];
         }

         std::size_t size() const exprtk_override
         {
            return value_.size();
         }

         range_t& range_ref() exprtk_override
         {
            return range_;
         }

         const range_t& range_ref() const exprtk_override
         {
            return range_;
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_strcondition;
         }

         inline std::string to_string() const exprtk_override{
            return "(conditional_string_node)";
         }
      private:

         bool initialised_;
         str_base_ptr str0_base_ptr_;
         str_base_ptr str1_base_ptr_;
         irange_ptr   str0_range_ptr_;
         irange_ptr   str1_range_ptr_;
         mutable range_t     range_;
         mutable std::string value_;

         expression_ptr condition_;
         expression_ptr consequent_;
         expression_ptr alternative_;
      };

      template <typename T>
      class cons_conditional_str_node exprtk_final
                                      : public binary_node     <T>,
                                        public string_base_node<T>,
                                        public range_interface <T>
      {
      public:

         typedef typename range_interface<T>::range_t range_t;
         typedef range_t*             range_ptr;
         typedef range_interface <T>  irange_t;
         typedef irange_t*            irange_ptr;
         typedef expression_node <T>* expression_ptr;
         typedef string_base_node<T>* str_base_ptr;

         using binary_node<T>::branch;

         cons_conditional_str_node(expression_ptr condition,
                                   expression_ptr consequent)
         : binary_node<T>(details::e_default, consequent, condition)
         , initialised_(false)
         , str0_base_ptr_ (0)
         , str0_range_ptr_(0)
         , condition_ (condition )
         , consequent_(consequent)
         {
            range_.n0_c = std::make_pair<bool,std::size_t>(true,0);
            range_.n1_c = std::make_pair<bool,std::size_t>(true,0);

            range_.cache.first  = range_.n0_c.second;
            range_.cache.second = range_.n1_c.second;

            if (is_generally_string_node(branch(0)))
            {
               str0_base_ptr_ = dynamic_cast<str_base_ptr>(branch(0));

               if (0 == str0_base_ptr_)
                  return;

               str0_range_ptr_ = dynamic_cast<irange_ptr>(branch(0));

               if (0 == str0_range_ptr_)
                  return;
            }

            initialised_ = str0_base_ptr_ && str0_range_ptr_ ;

            assert(initialised_);
         }

         inline T value() const exprtk_override
         {
            if (initialised_)
            {
               assert(condition_ );
               assert(consequent_);

               if (is_true(condition_))
               {
                  consequent_->value();

                  const range_t& range = str0_range_ptr_->range_ref();

                  std::size_t r0 = 0;
                  std::size_t r1 = 0;

                  if (range(r0, r1, str0_base_ptr_->size()))
                  {
                     const std::size_t size = (r1 - r0) + 1;

                     value_.assign(str0_base_ptr_->base() + r0, size);

                     range_.n1_c.second  = value_.size() - 1;
                     range_.cache.second = range_.n1_c.second;

                     return T(1);
                  }
               }
            }

            return std::numeric_limits<T>::quiet_NaN();
         }

         std::string str() const
         {
            return value_;
         }

         char_cptr base() const
         {
            return &value_[0];
         }

         std::size_t size() const
         {
            return value_.size();
         }

         range_t& range_ref()
         {
            return range_;
         }

         const range_t& range_ref() const
         {
            return range_;
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_strccondition;
         }

         inline std::string to_string() const exprtk_override{
            return "(cons_conditional_str_node)";
         }
      private:

         bool initialised_;
         str_base_ptr str0_base_ptr_;
         irange_ptr   str0_range_ptr_;
         mutable range_t     range_;
         mutable std::string value_;

         expression_ptr condition_;
         expression_ptr consequent_;
      };

      template <typename T, typename VarArgFunction>
      class str_vararg_node exprtk_final
                            : public expression_node <T>,
                              public string_base_node<T>,
                              public range_interface <T>
      {
      public:

         typedef typename range_interface<T>::range_t range_t;
         typedef range_t*             range_ptr;
         typedef range_interface <T>  irange_t;
         typedef irange_t*            irange_ptr;
         typedef expression_node <T>* expression_ptr;
         typedef string_base_node<T>* str_base_ptr;
         typedef std::pair<expression_ptr,bool> branch_t;

         template <typename Allocator,
                   template <typename, typename> class Sequence>
         explicit str_vararg_node(const Sequence<expression_ptr,Allocator>& arg_list)
         : initialised_(false)
         , str_base_ptr_ (0)
         , str_range_ptr_(0)
         {
            construct_branch_pair(final_node_, const_cast<expression_ptr>(arg_list.back()));

            if (0 == final_node_.first)
               return;
            else if (!is_generally_string_node(final_node_.first))
               return;

            str_base_ptr_ = dynamic_cast<str_base_ptr>(final_node_.first);

            if (0 == str_base_ptr_)
               return;

            str_range_ptr_ = dynamic_cast<irange_ptr>(final_node_.first);

            if (0 == str_range_ptr_)
               return;

            initialised_ = str_base_ptr_  && str_range_ptr_;

            if (arg_list.size() > 1)
            {
               const std::size_t arg_list_size = arg_list.size() - 1;

               arg_list_.resize(arg_list_size);

               for (std::size_t i = 0; i < arg_list_size; ++i)
               {
                  if (arg_list[i])
                  {
                     construct_branch_pair(arg_list_[i], arg_list[i]);
                  }
                  else
                  {
                     arg_list_.clear();
                     return;
                  }
               }
            }
         }

         inline T value() const exprtk_override
         {
            if (!arg_list_.empty())
            {
               VarArgFunction::process(arg_list_);
            }

            final_node_.first->value();

            return std::numeric_limits<T>::quiet_NaN();
         }

         std::string str() const exprtk_override
         {
            return str_base_ptr_->str();
         }

         char_cptr base() const exprtk_override
         {
            return str_base_ptr_->base();
         }

         std::size_t size() const exprtk_override
         {
            return str_base_ptr_->size();
         }

         range_t& range_ref() exprtk_override
         {
            return str_range_ptr_->range_ref();
         }

         const range_t& range_ref() const exprtk_override
         {
            return str_range_ptr_->range_ref();
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_stringvararg;
         }

         void collect_nodes(typename expression_node<T>::noderef_list_t& node_delete_list) exprtk_override
         {
            expression_node<T>::ndb_t::collect(final_node_ , node_delete_list);
            expression_node<T>::ndb_t::collect(arg_list_   , node_delete_list);
         }

         std::size_t node_depth() const exprtk_override
         {
            return std::max(
               expression_node<T>::ndb_t::compute_node_depth(final_node_),
               expression_node<T>::ndb_t::compute_node_depth(arg_list_  ));
         }

         inline std::string to_string() const exprtk_override{
            return "(str_vararg_node)";
         }
      private:

         bool                  initialised_;
         branch_t              final_node_;
         str_base_ptr          str_base_ptr_;
         irange_ptr            str_range_ptr_;
         std::vector<branch_t> arg_list_;
      };

      template <typename T, std::size_t N>
      inline T axn(const T a, const T x)
      {
         // a*x^n
         return a * Essa::Math::details::numeric::fast_exp<T,N>::result(x);
      }

      template <typename T, std::size_t N>
      inline T axnb(const T a, const T x, const T b)
      {
         // a*x^n+b
         return a * Essa::Math::details::numeric::fast_exp<T,N>::result(x) + b;
      }

      template <typename T>
      struct sf_base
      {
         typedef typename details::functor_t<T>::Type Type;
         typedef typename details::functor_t<T> functor_t;
         typedef typename functor_t::qfunc_t quaternary_functor_t;
         typedef typename functor_t::tfunc_t trinary_functor_t;
         typedef typename functor_t::bfunc_t binary_functor_t;
         typedef typename functor_t::ufunc_t unary_functor_t;
      };

      #define define_sfop3(NN, OP0, OP1)                 \
      template <typename T>                              \
      struct sf##NN##_op : public sf_base<T>             \
      {                                                  \
         typedef typename sf_base<T>::Type const Type;   \
         static inline T process(Type x, Type y, Type z) \
         {                                               \
            return (OP0);                                \
         }                                               \
         static inline std::string id()                  \
         {                                               \
            return (OP1);                                \
         }                                               \
      };                                                 \

      define_sfop3(00,(x + y) / z       ,"(t+t)/t")
      define_sfop3(01,(x + y) * z       ,"(t+t)*t")
      define_sfop3(02,(x + y) - z       ,"(t+t)-t")
      define_sfop3(03,(x + y) + z       ,"(t+t)+t")
      define_sfop3(04,(x - y) + z       ,"(t-t)+t")
      define_sfop3(05,(x - y) / z       ,"(t-t)/t")
      define_sfop3(06,(x - y) * z       ,"(t-t)*t")
      define_sfop3(07,(x * y) + z       ,"(t*t)+t")
      define_sfop3(08,(x * y) - z       ,"(t*t)-t")
      define_sfop3(09,(x * y) / z       ,"(t*t)/t")
      define_sfop3(10,(x * y) * z       ,"(t*t)*t")
      define_sfop3(11,(x / y) + z       ,"(t/t)+t")
      define_sfop3(12,(x / y) - z       ,"(t/t)-t")
      define_sfop3(13,(x / y) / z       ,"(t/t)/t")
      define_sfop3(14,(x / y) * z       ,"(t/t)*t")
      define_sfop3(15,x / (y + z)       ,"t/(t+t)")
      define_sfop3(16,x / (y - z)       ,"t/(t-t)")
      define_sfop3(17,x / (y * z)       ,"t/(t*t)")
      define_sfop3(18,x / (y / z)       ,"t/(t/t)")
      define_sfop3(19,x * (y + z)       ,"t*(t+t)")
      define_sfop3(20,x * (y - z)       ,"t*(t-t)")
      define_sfop3(21,x * (y * z)       ,"t*(t*t)")
      define_sfop3(22,x * (y / z)       ,"t*(t/t)")
      define_sfop3(23,x - (y + z)       ,"t-(t+t)")
      define_sfop3(24,x - (y - z)       ,"t-(t-t)")
      define_sfop3(25,x - (y / z)       ,"t-(t/t)")
      define_sfop3(26,x - (y * z)       ,"t-(t*t)")
      define_sfop3(27,x + (y * z)       ,"t+(t*t)")
      define_sfop3(28,x + (y / z)       ,"t+(t/t)")
      define_sfop3(29,x + (y + z)       ,"t+(t+t)")
      define_sfop3(30,x + (y - z)       ,"t+(t-t)")
      define_sfop3(31,(axnb<T,2>(x,y,z)),"       ")
      define_sfop3(32,(axnb<T,3>(x,y,z)),"       ")
      define_sfop3(33,(axnb<T,4>(x,y,z)),"       ")
      define_sfop3(34,(axnb<T,5>(x,y,z)),"       ")
      define_sfop3(35,(axnb<T,6>(x,y,z)),"       ")
      define_sfop3(36,(axnb<T,7>(x,y,z)),"       ")
      define_sfop3(37,(axnb<T,8>(x,y,z)),"       ")
      define_sfop3(38,(axnb<T,9>(x,y,z)),"       ")
      define_sfop3(39,x * numeric::log(y)   + z,"")
      define_sfop3(40,x * numeric::log(y)   - z,"")
      define_sfop3(41,x * numeric::log10(y) + z,"")
      define_sfop3(42,x * numeric::log10(y) - z,"")
      define_sfop3(43,x * numeric::sin(y) + z  ,"")
      define_sfop3(44,x * numeric::sin(y) - z  ,"")
      define_sfop3(45,x * numeric::cos(y) + z  ,"")
      define_sfop3(46,x * numeric::cos(y) - z  ,"")
      define_sfop3(47,details::is_true(x) ? y : z,"")

      #define define_sfop4(NN, OP0, OP1)                         \
      template <typename T>                                      \
      struct sf##NN##_op : public sf_base<T>                     \
      {                                                          \
         typedef typename sf_base<T>::Type const Type;           \
         static inline T process(Type x, Type y, Type z, Type w) \
         {                                                       \
            return (OP0);                                        \
         }                                                       \
         static inline std::string id()                          \
         {                                                       \
            return (OP1);                                        \
         }                                                       \
      };                                                         \

      define_sfop4(48,(x + ((y + z) / w)),"t+((t+t)/t)")
      define_sfop4(49,(x + ((y + z) * w)),"t+((t+t)*t)")
      define_sfop4(50,(x + ((y - z) / w)),"t+((t-t)/t)")
      define_sfop4(51,(x + ((y - z) * w)),"t+((t-t)*t)")
      define_sfop4(52,(x + ((y * z) / w)),"t+((t*t)/t)")
      define_sfop4(53,(x + ((y * z) * w)),"t+((t*t)*t)")
      define_sfop4(54,(x + ((y / z) + w)),"t+((t/t)+t)")
      define_sfop4(55,(x + ((y / z) / w)),"t+((t/t)/t)")
      define_sfop4(56,(x + ((y / z) * w)),"t+((t/t)*t)")
      define_sfop4(57,(x - ((y + z) / w)),"t-((t+t)/t)")
      define_sfop4(58,(x - ((y + z) * w)),"t-((t+t)*t)")
      define_sfop4(59,(x - ((y - z) / w)),"t-((t-t)/t)")
      define_sfop4(60,(x - ((y - z) * w)),"t-((t-t)*t)")
      define_sfop4(61,(x - ((y * z) / w)),"t-((t*t)/t)")
      define_sfop4(62,(x - ((y * z) * w)),"t-((t*t)*t)")
      define_sfop4(63,(x - ((y / z) / w)),"t-((t/t)/t)")
      define_sfop4(64,(x - ((y / z) * w)),"t-((t/t)*t)")
      define_sfop4(65,(((x + y) * z) - w),"((t+t)*t)-t")
      define_sfop4(66,(((x - y) * z) - w),"((t-t)*t)-t")
      define_sfop4(67,(((x * y) * z) - w),"((t*t)*t)-t")
      define_sfop4(68,(((x / y) * z) - w),"((t/t)*t)-t")
      define_sfop4(69,(((x + y) / z) - w),"((t+t)/t)-t")
      define_sfop4(70,(((x - y) / z) - w),"((t-t)/t)-t")
      define_sfop4(71,(((x * y) / z) - w),"((t*t)/t)-t")
      define_sfop4(72,(((x / y) / z) - w),"((t/t)/t)-t")
      define_sfop4(73,((x * y) + (z * w)),"(t*t)+(t*t)")
      define_sfop4(74,((x * y) - (z * w)),"(t*t)-(t*t)")
      define_sfop4(75,((x * y) + (z / w)),"(t*t)+(t/t)")
      define_sfop4(76,((x * y) - (z / w)),"(t*t)-(t/t)")
      define_sfop4(77,((x / y) + (z / w)),"(t/t)+(t/t)")
      define_sfop4(78,((x / y) - (z / w)),"(t/t)-(t/t)")
      define_sfop4(79,((x / y) - (z * w)),"(t/t)-(t*t)")
      define_sfop4(80,(x / (y + (z * w))),"t/(t+(t*t))")
      define_sfop4(81,(x / (y - (z * w))),"t/(t-(t*t))")
      define_sfop4(82,(x * (y + (z * w))),"t*(t+(t*t))")
      define_sfop4(83,(x * (y - (z * w))),"t*(t-(t*t))")

      define_sfop4(84,(axn<T,2>(x,y) + axn<T,2>(z,w)),"")
      define_sfop4(85,(axn<T,3>(x,y) + axn<T,3>(z,w)),"")
      define_sfop4(86,(axn<T,4>(x,y) + axn<T,4>(z,w)),"")
      define_sfop4(87,(axn<T,5>(x,y) + axn<T,5>(z,w)),"")
      define_sfop4(88,(axn<T,6>(x,y) + axn<T,6>(z,w)),"")
      define_sfop4(89,(axn<T,7>(x,y) + axn<T,7>(z,w)),"")
      define_sfop4(90,(axn<T,8>(x,y) + axn<T,8>(z,w)),"")
      define_sfop4(91,(axn<T,9>(x,y) + axn<T,9>(z,w)),"")
      define_sfop4(92,((details::is_true(x) && details::is_true(y)) ? z : w),"")
      define_sfop4(93,((details::is_true(x) || details::is_true(y)) ? z : w),"")
      define_sfop4(94,(details::is_true(numeric::lth<T>(x, y)) ? z : w),"")
      define_sfop4(95,(details::is_true(numeric::leq<T>(x, y)) ? z : w),"")
      define_sfop4(96,(details::is_true(numeric::gth<T>(x, y)) ? z : w),"")
      define_sfop4(97,(details::is_true(numeric::geq<T>(x, y)) ? z : w),"")
      define_sfop4(98,(details::is_true(numeric::equal(x,y)) ? z : w),"")
      define_sfop4(99,(x * numeric::sin(y) + z * numeric::cos(w)),"")

      define_sfop4(ext00,((x + y) - (z * w)),"(t+t)-(t*t)")
      define_sfop4(ext01,((x + y) - (z / w)),"(t+t)-(t/t)")
      define_sfop4(ext02,((x + y) + (z * w)),"(t+t)+(t*t)")
      define_sfop4(ext03,((x + y) + (z / w)),"(t+t)+(t/t)")
      define_sfop4(ext04,((x - y) + (z * w)),"(t-t)+(t*t)")
      define_sfop4(ext05,((x - y) + (z / w)),"(t-t)+(t/t)")
      define_sfop4(ext06,((x - y) - (z * w)),"(t-t)-(t*t)")
      define_sfop4(ext07,((x - y) - (z / w)),"(t-t)-(t/t)")
      define_sfop4(ext08,((x + y) - (z - w)),"(t+t)-(t-t)")
      define_sfop4(ext09,((x + y) + (z - w)),"(t+t)+(t-t)")
      define_sfop4(ext10,((x + y) + (z + w)),"(t+t)+(t+t)")
      define_sfop4(ext11,((x + y) * (z - w)),"(t+t)*(t-t)")
      define_sfop4(ext12,((x + y) / (z - w)),"(t+t)/(t-t)")
      define_sfop4(ext13,((x - y) - (z + w)),"(t-t)-(t+t)")
      define_sfop4(ext14,((x - y) + (z + w)),"(t-t)+(t+t)")
      define_sfop4(ext15,((x - y) * (z + w)),"(t-t)*(t+t)")
      define_sfop4(ext16,((x - y) / (z + w)),"(t-t)/(t+t)")
      define_sfop4(ext17,((x * y) - (z + w)),"(t*t)-(t+t)")
      define_sfop4(ext18,((x / y) - (z + w)),"(t/t)-(t+t)")
      define_sfop4(ext19,((x * y) + (z + w)),"(t*t)+(t+t)")
      define_sfop4(ext20,((x / y) + (z + w)),"(t/t)+(t+t)")
      define_sfop4(ext21,((x * y) + (z - w)),"(t*t)+(t-t)")
      define_sfop4(ext22,((x / y) + (z - w)),"(t/t)+(t-t)")
      define_sfop4(ext23,((x * y) - (z - w)),"(t*t)-(t-t)")
      define_sfop4(ext24,((x / y) - (z - w)),"(t/t)-(t-t)")
      define_sfop4(ext25,((x + y) * (z * w)),"(t+t)*(t*t)")
      define_sfop4(ext26,((x + y) * (z / w)),"(t+t)*(t/t)")
      define_sfop4(ext27,((x + y) / (z * w)),"(t+t)/(t*t)")
      define_sfop4(ext28,((x + y) / (z / w)),"(t+t)/(t/t)")
      define_sfop4(ext29,((x - y) / (z * w)),"(t-t)/(t*t)")
      define_sfop4(ext30,((x - y) / (z / w)),"(t-t)/(t/t)")
      define_sfop4(ext31,((x - y) * (z * w)),"(t-t)*(t*t)")
      define_sfop4(ext32,((x - y) * (z / w)),"(t-t)*(t/t)")
      define_sfop4(ext33,((x * y) * (z + w)),"(t*t)*(t+t)")
      define_sfop4(ext34,((x / y) * (z + w)),"(t/t)*(t+t)")
      define_sfop4(ext35,((x * y) / (z + w)),"(t*t)/(t+t)")
      define_sfop4(ext36,((x / y) / (z + w)),"(t/t)/(t+t)")
      define_sfop4(ext37,((x * y) / (z - w)),"(t*t)/(t-t)")
      define_sfop4(ext38,((x / y) / (z - w)),"(t/t)/(t-t)")
      define_sfop4(ext39,((x * y) * (z - w)),"(t*t)*(t-t)")
      define_sfop4(ext40,((x * y) / (z * w)),"(t*t)/(t*t)")
      define_sfop4(ext41,((x / y) * (z / w)),"(t/t)*(t/t)")
      define_sfop4(ext42,((x / y) * (z - w)),"(t/t)*(t-t)")
      define_sfop4(ext43,((x * y) * (z * w)),"(t*t)*(t*t)")
      define_sfop4(ext44,(x + (y * (z / w))),"t+(t*(t/t))")
      define_sfop4(ext45,(x - (y * (z / w))),"t-(t*(t/t))")
      define_sfop4(ext46,(x + (y / (z * w))),"t+(t/(t*t))")
      define_sfop4(ext47,(x - (y / (z * w))),"t-(t/(t*t))")
      define_sfop4(ext48,(((x - y) - z) * w),"((t-t)-t)*t")
      define_sfop4(ext49,(((x - y) - z) / w),"((t-t)-t)/t")
      define_sfop4(ext50,(((x - y) + z) * w),"((t-t)+t)*t")
      define_sfop4(ext51,(((x - y) + z) / w),"((t-t)+t)/t")
      define_sfop4(ext52,((x + (y - z)) * w),"(t+(t-t))*t")
      define_sfop4(ext53,((x + (y - z)) / w),"(t+(t-t))/t")
      define_sfop4(ext54,((x + y) / (z + w)),"(t+t)/(t+t)")
      define_sfop4(ext55,((x - y) / (z - w)),"(t-t)/(t-t)")
      define_sfop4(ext56,((x + y) * (z + w)),"(t+t)*(t+t)")
      define_sfop4(ext57,((x - y) * (z - w)),"(t-t)*(t-t)")
      define_sfop4(ext58,((x - y) + (z - w)),"(t-t)+(t-t)")
      define_sfop4(ext59,((x - y) - (z - w)),"(t-t)-(t-t)")
      define_sfop4(ext60,((x / y) + (z * w)),"(t/t)+(t*t)")
      define_sfop4(ext61,(((x * y) * z) / w),"((t*t)*t)/t")

      #undef define_sfop3
      #undef define_sfop4

      template <typename T, typename SpecialFunction>
      class sf3_node exprtk_final : public trinary_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;

         sf3_node(const operator_type& opr,
                  expression_ptr branch0,
                  expression_ptr branch1,
                  expression_ptr branch2)
         : trinary_node<T>(opr, branch0, branch1, branch2)
         {}

         inline T value() const exprtk_override
         {
            assert(trinary_node<T>::branch_[0].first);
            assert(trinary_node<T>::branch_[1].first);
            assert(trinary_node<T>::branch_[2].first);

            const T x = trinary_node<T>::branch_[0].first->value();
            const T y = trinary_node<T>::branch_[1].first->value();
            const T z = trinary_node<T>::branch_[2].first->value();

            return SpecialFunction::process(x, y, z);
         }

         inline std::string to_string() const exprtk_override{
            return "(sf3_node)";
         }
      };

      template <typename T, typename SpecialFunction>
      class sf4_node exprtk_final : public quaternary_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;

         sf4_node(const operator_type& opr,
                  expression_ptr branch0,
                  expression_ptr branch1,
                  expression_ptr branch2,
                  expression_ptr branch3)
         : quaternary_node<T>(opr, branch0, branch1, branch2, branch3)
         {}

         inline T value() const exprtk_override
         {
            assert(quaternary_node<T>::branch_[0].first);
            assert(quaternary_node<T>::branch_[1].first);
            assert(quaternary_node<T>::branch_[2].first);
            assert(quaternary_node<T>::branch_[3].first);

            const T x = quaternary_node<T>::branch_[0].first->value();
            const T y = quaternary_node<T>::branch_[1].first->value();
            const T z = quaternary_node<T>::branch_[2].first->value();
            const T w = quaternary_node<T>::branch_[3].first->value();

            return SpecialFunction::process(x, y, z, w);
         }

         inline std::string to_string() const exprtk_override{
            return "(sf4_node)";
         }
      };

      template <typename T, typename SpecialFunction>
      class sf3_var_node exprtk_final : public expression_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;

         sf3_var_node(const T& v0, const T& v1, const T& v2)
         : v0_(v0)
         , v1_(v1)
         , v2_(v2)
         {}

         inline T value() const exprtk_override
         {
            return SpecialFunction::process(v0_, v1_, v2_);
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_trinary;
         }

         inline std::string to_string() const exprtk_override{
            return "(sf3_var_node)";
         }
      private:

         sf3_var_node(const sf3_var_node<T,SpecialFunction>&) exprtk_delete;
         sf3_var_node<T,SpecialFunction>& operator=(const sf3_var_node<T,SpecialFunction>&) exprtk_delete;

         const T& v0_;
         const T& v1_;
         const T& v2_;
      };

      template <typename T, typename SpecialFunction>
      class sf4_var_node exprtk_final : public expression_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;

         sf4_var_node(const T& v0, const T& v1, const T& v2, const T& v3)
         : v0_(v0)
         , v1_(v1)
         , v2_(v2)
         , v3_(v3)
         {}

         inline T value() const exprtk_override
         {
            return SpecialFunction::process(v0_, v1_, v2_, v3_);
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_trinary;
         }

         inline std::string to_string() const exprtk_override{
            return "(sf4_var_node)";
         }
      private:

         sf4_var_node(const sf4_var_node<T,SpecialFunction>&) exprtk_delete;
         sf4_var_node<T,SpecialFunction>& operator=(const sf4_var_node<T,SpecialFunction>&) exprtk_delete;

         const T& v0_;
         const T& v1_;
         const T& v2_;
         const T& v3_;
      };

      template <typename T, typename VarArgFunction>
      class vararg_node exprtk_final : public expression_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef std::pair<expression_ptr,bool> branch_t;

         template <typename Allocator,
                   template <typename, typename> class Sequence>
         explicit vararg_node(const Sequence<expression_ptr,Allocator>& arg_list)
         {
            arg_list_.resize(arg_list.size());

            for (std::size_t i = 0; i < arg_list.size(); ++i)
            {
               if (arg_list[i])
               {
                  construct_branch_pair(arg_list_[i],arg_list[i]);
               }
               else
               {
                  arg_list_.clear();
                  return;
               }
            }
         }

         inline T value() const exprtk_override
         {
            return VarArgFunction::process(arg_list_);
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_vararg;
         }

         void collect_nodes(typename expression_node<T>::noderef_list_t& node_delete_list) exprtk_override
         {
            expression_node<T>::ndb_t::collect(arg_list_, node_delete_list);
         }

         std::size_t node_depth() const exprtk_override
         {
            return expression_node<T>::ndb_t::compute_node_depth(arg_list_);
         }

         inline std::string to_string() const exprtk_override{
            return "(vararg_node)";
         }
      private:

         std::vector<branch_t> arg_list_;
      };

      template <typename T, typename VarArgFunction>
      class vararg_varnode exprtk_final : public expression_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;

         template <typename Allocator,
                   template <typename, typename> class Sequence>
         explicit vararg_varnode(const Sequence<expression_ptr,Allocator>& arg_list)
         {
            arg_list_.resize(arg_list.size());

            for (std::size_t i = 0; i < arg_list.size(); ++i)
            {
               if (arg_list[i] && is_variable_node(arg_list[i]))
               {
                  variable_node<T>* var_node_ptr = static_cast<variable_node<T>*>(arg_list[i]);
                  arg_list_[i] = (&var_node_ptr->ref());
               }
               else
               {
                  arg_list_.clear();
                  return;
               }
            }
         }

         inline T value() const exprtk_override
         {
            if (!arg_list_.empty())
               return VarArgFunction::process(arg_list_);
            else
               return std::numeric_limits<T>::quiet_NaN();
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_vararg;
         }

         inline std::string to_string() const exprtk_override{
            return "(vararg_varnode)";
         }
      private:

         std::vector<const T*> arg_list_;
      };

      template <typename T, typename VecFunction>
      class vectorize_node exprtk_final : public expression_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef std::pair<expression_ptr,bool> branch_t;

         explicit vectorize_node(const expression_ptr v)
         : ivec_ptr_(0)
         {
            construct_branch_pair(v_, v);

            if (is_ivector_node(v_.first))
            {
               ivec_ptr_ = dynamic_cast<vector_interface<T>*>(v_.first);
            }
            else
               ivec_ptr_ = 0;
         }

         inline T value() const exprtk_override
         {
            if (ivec_ptr_)
            {
               assert(v_.first);

               v_.first->value();

               return VecFunction::process(ivec_ptr_);
            }
            else
               return std::numeric_limits<T>::quiet_NaN();
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_vecfunc;
         }

         void collect_nodes(typename expression_node<T>::noderef_list_t& node_delete_list) exprtk_override
         {
            expression_node<T>::ndb_t::collect(v_, node_delete_list);
         }

         std::size_t node_depth() const exprtk_override
         {
            return expression_node<T>::ndb_t::compute_node_depth(v_);
         }

         inline std::string to_string() const exprtk_override{
            return "(vectorize_node)";
         }
      private:

         vector_interface<T>* ivec_ptr_;
         branch_t                    v_;
      };

      template <typename T>
      class assignment_node exprtk_final : public binary_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         using binary_node<T>::branch;

         assignment_node(const operator_type& opr,
                         expression_ptr branch0,
                         expression_ptr branch1)
         : binary_node<T>(opr, branch0, branch1)
         , var_node_ptr_(0)
         {
            if (is_variable_node(branch(0)))
            {
               var_node_ptr_ = static_cast<variable_node<T>*>(branch(0));
            }
         }

         inline T value() const exprtk_override
         {
            if (var_node_ptr_)
            {
               assert(branch(1));

               T& result = var_node_ptr_->ref();
               result = branch(1)->value();

               return result;
            }
            else
               return std::numeric_limits<T>::quiet_NaN();
         }

      private:

         variable_node<T>* var_node_ptr_;
      };

      template <typename T>
      class assignment_vec_elem_node exprtk_final : public binary_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         using binary_node<T>::branch;

         assignment_vec_elem_node(const operator_type& opr,
                                  expression_ptr branch0,
                                  expression_ptr branch1)
         : binary_node<T>(opr, branch0, branch1)
         , vec_node_ptr_(0)
         {
            if (is_vector_elem_node(branch(0)))
            {
               vec_node_ptr_ = static_cast<vector_elem_node<T>*>(branch(0));
            }
         }

         inline T value() const exprtk_override
         {
            if (vec_node_ptr_)
            {
               assert(branch(1));

               T& result = vec_node_ptr_->ref();
               result = branch(1)->value();

               return result;
            }
            else
               return std::numeric_limits<T>::quiet_NaN();
         }

         inline std::string to_string() const exprtk_override{
            return "(assignment_vec_elem_node)";
         }
      private:

         vector_elem_node<T>* vec_node_ptr_;
      };

      template <typename T>
      class assignment_rebasevec_elem_node exprtk_final : public binary_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         using expression_node<T>::branch;

         assignment_rebasevec_elem_node(const operator_type& opr,
                                        expression_ptr branch0,
                                        expression_ptr branch1)
         : binary_node<T>(opr, branch0, branch1)
         , rbvec_node_ptr_(0)
         {
            if (is_rebasevector_elem_node(branch(0)))
            {
               rbvec_node_ptr_ = static_cast<rebasevector_elem_node<T>*>(branch(0));
            }
         }

         inline T value() const exprtk_override
         {
            if (rbvec_node_ptr_)
            {
               assert(branch(1));

               T& result = rbvec_node_ptr_->ref();

               result = branch(1)->value();

               return result;
            }
            else
               return std::numeric_limits<T>::quiet_NaN();
         }

         inline std::string to_string() const exprtk_override{
            return "(assignment_rebasevec_elem_node)";
         }
      private:

         rebasevector_elem_node<T>* rbvec_node_ptr_;
      };

      template <typename T>
      class assignment_rebasevec_celem_node exprtk_final : public binary_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         using binary_node<T>::branch;

         assignment_rebasevec_celem_node(const operator_type& opr,
                                         expression_ptr branch0,
                                         expression_ptr branch1)
         : binary_node<T>(opr, branch0, branch1)
         , rbvec_node_ptr_(0)
         {
            if (is_rebasevector_celem_node(branch(0)))
            {
               rbvec_node_ptr_ = static_cast<rebasevector_celem_node<T>*>(branch(0));
            }
         }

         inline T value() const exprtk_override
         {
            if (rbvec_node_ptr_)
            {
               assert(branch(1));

               T& result = rbvec_node_ptr_->ref();
               result = branch(1)->value();

               return result;
            }
            else
               return std::numeric_limits<T>::quiet_NaN();
         }

         inline std::string to_string() const exprtk_override{
            return "(assignment_rebasevec_celem_node)";
         }
      private:

         rebasevector_celem_node<T>* rbvec_node_ptr_;
      };

      template <typename T>
      class assignment_vec_node exprtk_final
                                : public binary_node     <T>
                                , public vector_interface<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef vector_node<T>*     vector_node_ptr;
         typedef vec_data_store<T>   vds_t;

         using binary_node<T>::branch;

         assignment_vec_node(const operator_type& opr,
                             expression_ptr branch0,
                             expression_ptr branch1)
         : binary_node<T>(opr, branch0, branch1)
         , vec_node_ptr_(0)
         {
            if (is_vector_node(branch(0)))
            {
               vec_node_ptr_ = static_cast<vector_node<T>*>(branch(0));
               vds()         = vec_node_ptr_->vds();
            }
         }

         inline T value() const exprtk_override
         {
            if (vec_node_ptr_)
            {
               assert(branch(1));

               const T v = branch(1)->value();

               T* vec = vds().data();

               loop_unroll::details lud(size());
               const T* upper_bound = vec + lud.upper_bound;

               while (vec < upper_bound)
               {
                  #define exprtk_loop(N) \
                  vec[N] = v;            \

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

               exprtk_disable_fallthrough_begin
               switch (lud.remainder)
               {
                  #define case_stmt(N) \
                  case N : *vec++ = v; \

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

               return vec_node_ptr_->value();
            }
            else
               return std::numeric_limits<T>::quiet_NaN();
         }

         vector_node_ptr vec() const exprtk_override
         {
            return vec_node_ptr_;
         }

         vector_node_ptr vec() exprtk_override
         {
            return vec_node_ptr_;
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_vecvalass;
         }

         std::size_t size() const exprtk_override
         {
            return vds().size();
         }

         vds_t& vds() exprtk_override
         {
            return vds_;
         }

         const vds_t& vds() const exprtk_override
         {
            return vds_;
         }

         inline std::string to_string() const exprtk_override{
            return "(assignment_vec_node)";
         }
      private:

         vector_node<T>* vec_node_ptr_;
         vds_t           vds_;
      };

      template <typename T>
      class assignment_vecvec_node exprtk_final
                                   : public binary_node     <T>
                                   , public vector_interface<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef vector_node<T>*     vector_node_ptr;
         typedef vec_data_store<T>   vds_t;

         using binary_node<T>::branch;

         assignment_vecvec_node(const operator_type& opr,
                                expression_ptr branch0,
                                expression_ptr branch1)
         : binary_node<T>(opr, branch0, branch1)
         , vec0_node_ptr_(0)
         , vec1_node_ptr_(0)
         , initialised_(false)
         , src_is_ivec_(false)
         {
            if (is_vector_node(branch(0)))
            {
               vec0_node_ptr_ = static_cast<vector_node<T>*>(branch(0));
               vds()          = vec0_node_ptr_->vds();
            }

            if (is_vector_node(branch(1)))
            {
               vec1_node_ptr_ = static_cast<vector_node<T>*>(branch(1));
               vds_t::match_sizes(vds(),vec1_node_ptr_->vds());
            }
            else if (is_ivector_node(branch(1)))
            {
               vector_interface<T>* vi = reinterpret_cast<vector_interface<T>*>(0);

               if (0 != (vi = dynamic_cast<vector_interface<T>*>(branch(1))))
               {
                  vec1_node_ptr_ = vi->vec();

                  if (!vi->side_effect())
                  {
                     vi->vds()    = vds();
                     src_is_ivec_ = true;
                  }
                  else
                     vds_t::match_sizes(vds(),vi->vds());
               }
            }

            initialised_ = (vec0_node_ptr_ && vec1_node_ptr_);

            assert(initialised_);
         }

         inline T value() const exprtk_override
         {
            if (initialised_)
            {
               assert(branch(1));

               branch(1)->value();

               if (src_is_ivec_)
                  return vec0_node_ptr_->value();

               T* vec0 = vec0_node_ptr_->vds().data();
               T* vec1 = vec1_node_ptr_->vds().data();

               loop_unroll::details lud(size());
               const T* upper_bound = vec0 + lud.upper_bound;

               while (vec0 < upper_bound)
               {
                  #define exprtk_loop(N) \
                  vec0[N] = vec1[N];     \

                  exprtk_loop( 0) exprtk_loop( 1)
                  exprtk_loop( 2) exprtk_loop( 3)
                     exprtk_loop( 4) exprtk_loop( 5)
                  exprtk_loop( 6) exprtk_loop( 7)
                  exprtk_loop( 8) exprtk_loop( 9)
                  exprtk_loop(10) exprtk_loop(11)
                  exprtk_loop(12) exprtk_loop(13)
                  exprtk_loop(14) exprtk_loop(15)

                  vec0 += lud.batch_size;
                  vec1 += lud.batch_size;
               }

               exprtk_disable_fallthrough_begin
               switch (lud.remainder)
               {
                  #define case_stmt(N)        \
                  case N : *vec0++ = *vec1++; \

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

               return vec0_node_ptr_->value();
            }
            else
               return std::numeric_limits<T>::quiet_NaN();
         }

         vector_node_ptr vec() exprtk_override
         {
            return vec0_node_ptr_;
         }

         vector_node_ptr vec() const exprtk_override
         {
            return vec0_node_ptr_;
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_vecvecass;
         }

         std::size_t size() const exprtk_override
         {
            return vds().size();
         }

         vds_t& vds() exprtk_override
         {
            return vds_;
         }

         const vds_t& vds() const exprtk_override
         {
            return vds_;
         }

         inline std::string to_string() const exprtk_override{
            return "(assignment_vecvec_node)";
         }
      private:

         vector_node<T>* vec0_node_ptr_;
         vector_node<T>* vec1_node_ptr_;
         bool            initialised_;
         bool            src_is_ivec_;
         vds_t           vds_;
      };

      template <typename T, typename Operation>
      class assignment_op_node exprtk_final : public binary_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         using binary_node<T>::branch;

         assignment_op_node(const operator_type& opr,
                            expression_ptr branch0,
                            expression_ptr branch1)
         : binary_node<T>(opr, branch0, branch1)
         , var_node_ptr_(0)
         {
            if (is_variable_node(branch(0)))
            {
               var_node_ptr_ = static_cast<variable_node<T>*>(branch(0));
            }
         }

         inline T value() const exprtk_override
         {
            if (var_node_ptr_)
            {
               assert(branch(1));

               T& v = var_node_ptr_->ref();
               v = Operation::process(v,branch(1)->value());

               return v;
            }
            else
               return std::numeric_limits<T>::quiet_NaN();
         }

         inline std::string to_string() const exprtk_override{
            return "(assignment_op_node)";
         }
      private:

         variable_node<T>* var_node_ptr_;
      };

      template <typename T, typename Operation>
      class assignment_vec_elem_op_node exprtk_final : public binary_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         using binary_node<T>::branch;

         assignment_vec_elem_op_node(const operator_type& opr,
                                     expression_ptr branch0,
                                     expression_ptr branch1)
         : binary_node<T>(opr, branch0, branch1)
         , vec_node_ptr_(0)
         {
            if (is_vector_elem_node(branch(0)))
            {
               vec_node_ptr_ = static_cast<vector_elem_node<T>*>(branch(0));
            }
         }

         inline T value() const exprtk_override
         {
            if (vec_node_ptr_)
            {
               assert(branch(1));

               T& v = vec_node_ptr_->ref();
                  v = Operation::process(v,branch(1)->value());

               return v;
            }
            else
               return std::numeric_limits<T>::quiet_NaN();
         }

         inline std::string to_string() const exprtk_override{
            return "(assignment_vec_elem_op_node)";
         }
      private:

         vector_elem_node<T>* vec_node_ptr_;
      };

      template <typename T, typename Operation>
      class assignment_rebasevec_elem_op_node exprtk_final : public binary_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         using binary_node<T>::branch;

         assignment_rebasevec_elem_op_node(const operator_type& opr,
                                           expression_ptr branch0,
                                           expression_ptr branch1)
         : binary_node<T>(opr, branch0, branch1)
         , rbvec_node_ptr_(0)
         {
            if (is_rebasevector_elem_node(branch(0)))
            {
               rbvec_node_ptr_ = static_cast<rebasevector_elem_node<T>*>(branch(0));
            }
         }

         inline T value() const exprtk_override
         {
            if (rbvec_node_ptr_)
            {
               assert(branch(1));

               T& v = rbvec_node_ptr_->ref();
                  v = Operation::process(v,branch(1)->value());

               return v;
            }
            else
               return std::numeric_limits<T>::quiet_NaN();
         }

         inline std::string to_string() const exprtk_override{
            return "(assignment_rebasevec_elem_op_node)";
         }
      private:

         rebasevector_elem_node<T>* rbvec_node_ptr_;
      };

      template <typename T, typename Operation>
      class assignment_rebasevec_celem_op_node exprtk_final : public binary_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         using binary_node<T>::branch;

         assignment_rebasevec_celem_op_node(const operator_type& opr,
                                            expression_ptr branch0,
                                            expression_ptr branch1)
         : binary_node<T>(opr, branch0, branch1)
         , rbvec_node_ptr_(0)
         {
            if (is_rebasevector_celem_node(branch(0)))
            {
               rbvec_node_ptr_ = static_cast<rebasevector_celem_node<T>*>(branch(0));
            }
         }

         inline T value() const exprtk_override
         {
            if (rbvec_node_ptr_)
            {
               assert(branch(1));

               T& v = rbvec_node_ptr_->ref();
                  v = Operation::process(v,branch(1)->value());

               return v;
            }
            else
               return std::numeric_limits<T>::quiet_NaN();
         }

         inline std::string to_string() const exprtk_override{
            return "(assignment_rebasevec_celem_op_node)";
         }
      private:

         rebasevector_celem_node<T>* rbvec_node_ptr_;
      };

      template <typename T, typename Operation>
      class assignment_vec_op_node exprtk_final
                                   : public binary_node     <T>
                                   , public vector_interface<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef vector_node<T>*     vector_node_ptr;
         typedef vec_data_store<T>   vds_t;

         using binary_node<T>::branch;

         assignment_vec_op_node(const operator_type& opr,
                                expression_ptr branch0,
                                expression_ptr branch1)
         : binary_node<T>(opr, branch0, branch1)
         , vec_node_ptr_(0)
         {
            if (is_vector_node(branch(0)))
            {
               vec_node_ptr_ = static_cast<vector_node<T>*>(branch(0));
               vds()         = vec_node_ptr_->vds();
            }
         }

         inline T value() const exprtk_override
         {
            if (vec_node_ptr_)
            {
               assert(branch(1));

               const T v = branch(1)->value();

               T* vec = vds().data();

               loop_unroll::details lud(size());
               const T* upper_bound = vec + lud.upper_bound;

               while (vec < upper_bound)
               {
                  #define exprtk_loop(N)       \
                  Operation::assign(vec[N],v); \

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

               exprtk_disable_fallthrough_begin
               switch (lud.remainder)
               {
                  #define case_stmt(N)                  \
                  case N : Operation::assign(*vec++,v); \

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

               return vec_node_ptr_->value();
            }
            else
               return std::numeric_limits<T>::quiet_NaN();
         }

         vector_node_ptr vec() const exprtk_override
         {
            return vec_node_ptr_;
         }

         vector_node_ptr vec() exprtk_override
         {
            return vec_node_ptr_;
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_vecopvalass;
         }

         std::size_t size() const exprtk_override
         {
            return vds().size();
         }

         vds_t& vds() exprtk_override
         {
            return vds_;
         }

         const vds_t& vds() const exprtk_override
         {
            return vds_;
         }

         bool side_effect() const exprtk_override
         {
            return true;
         }

         inline std::string to_string() const exprtk_override{
            return "(assignment_vec_op_node)";
         }
      private:

         vector_node<T>* vec_node_ptr_;
         vds_t           vds_;
      };

      template <typename T, typename Operation>
      class assignment_vecvec_op_node exprtk_final
                                      : public binary_node     <T>
                                      , public vector_interface<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef vector_node<T>*     vector_node_ptr;
         typedef vec_data_store<T>   vds_t;

         using binary_node<T>::branch;

         assignment_vecvec_op_node(const operator_type& opr,
                                   expression_ptr branch0,
                                   expression_ptr branch1)
         : binary_node<T>(opr, branch0, branch1)
         , vec0_node_ptr_(0)
         , vec1_node_ptr_(0)
         , initialised_(false)
         {
            if (is_vector_node(branch(0)))
            {
               vec0_node_ptr_ = static_cast<vector_node<T>*>(branch(0));
               vds()          = vec0_node_ptr_->vds();
            }

            if (is_vector_node(branch(1)))
            {
               vec1_node_ptr_ = static_cast<vector_node<T>*>(branch(1));
               vec1_node_ptr_->vds() = vds();
            }
            else if (is_ivector_node(branch(1)))
            {
               vector_interface<T>* vi = reinterpret_cast<vector_interface<T>*>(0);

               if (0 != (vi = dynamic_cast<vector_interface<T>*>(branch(1))))
               {
                  vec1_node_ptr_ = vi->vec();
                  vec1_node_ptr_->vds() = vds();
               }
               else
                  vds_t::match_sizes(vds(),vec1_node_ptr_->vds());
            }

            initialised_ = (vec0_node_ptr_ && vec1_node_ptr_);

            assert(initialised_);
         }

         inline T value() const exprtk_override
         {
            if (initialised_)
            {
               assert(branch(0));
               assert(branch(1));

               branch(0)->value();
               branch(1)->value();

                     T* vec0 = vec0_node_ptr_->vds().data();
               const T* vec1 = vec1_node_ptr_->vds().data();

               loop_unroll::details lud(size());
               const T* upper_bound = vec0 + lud.upper_bound;

               while (vec0 < upper_bound)
               {
                  #define exprtk_loop(N)                          \
                  vec0[N] = Operation::process(vec0[N], vec1[N]); \

                  exprtk_loop( 0) exprtk_loop( 1)
                  exprtk_loop( 2) exprtk_loop( 3)
                  exprtk_loop( 4) exprtk_loop( 5)
                  exprtk_loop( 6) exprtk_loop( 7)
                  exprtk_loop( 8) exprtk_loop( 9)
                  exprtk_loop(10) exprtk_loop(11)
                  exprtk_loop(12) exprtk_loop(13)
                  exprtk_loop(14) exprtk_loop(15)

                  vec0 += lud.batch_size;
                  vec1 += lud.batch_size;
               }

               int i = 0;

               exprtk_disable_fallthrough_begin
               switch (lud.remainder)
               {
                  #define case_stmt(N)                                              \
                  case N : { vec0[i] = Operation::process(vec0[i], vec1[i]); ++i; } \

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

               return vec0_node_ptr_->value();
            }
            else
               return std::numeric_limits<T>::quiet_NaN();
         }

         vector_node_ptr vec() const exprtk_override
         {
            return vec0_node_ptr_;
         }

         vector_node_ptr vec() exprtk_override
         {
            return vec0_node_ptr_;
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_vecopvecass;
         }

         std::size_t size() const exprtk_override
         {
            return vds().size();
         }

         vds_t& vds() exprtk_override
         {
            return vds_;
         }

         const vds_t& vds() const exprtk_override
         {
            return vds_;
         }

         bool side_effect() const exprtk_override
         {
            return true;
         }

         inline std::string to_string() const exprtk_override{
            return "(assignment_vecvec_op_node)";
         }
      private:

         vector_node<T>* vec0_node_ptr_;
         vector_node<T>* vec1_node_ptr_;
         bool            initialised_;
         vds_t           vds_;
      };

      template <typename T, typename Operation>
      class vec_binop_vecvec_node exprtk_final
                                  : public binary_node     <T>
                                  , public vector_interface<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef vector_node<T>*     vector_node_ptr;
         typedef vector_holder<T>*   vector_holder_ptr;
         typedef vec_data_store<T>   vds_t;

         using binary_node<T>::branch;

         vec_binop_vecvec_node(const operator_type& opr,
                               expression_ptr branch0,
                               expression_ptr branch1)
         : binary_node<T>(opr, branch0, branch1)
         , vec0_node_ptr_(0)
         , vec1_node_ptr_(0)
         , temp_         (0)
         , temp_vec_node_(0)
         , initialised_(false)
         {
            bool v0_is_ivec = false;
            bool v1_is_ivec = false;

            if (is_vector_node(branch(0)))
            {
               vec0_node_ptr_ = static_cast<vector_node_ptr>(branch(0));
            }
            else if (is_ivector_node(branch(0)))
            {
               vector_interface<T>* vi = reinterpret_cast<vector_interface<T>*>(0);

               if (0 != (vi = dynamic_cast<vector_interface<T>*>(branch(0))))
               {
                  vec0_node_ptr_ = vi->vec();
                  v0_is_ivec     = true;
               }
            }

            if (is_vector_node(branch(1)))
            {
               vec1_node_ptr_ = static_cast<vector_node_ptr>(branch(1));
            }
            else if (is_ivector_node(branch(1)))
            {
               vector_interface<T>* vi = reinterpret_cast<vector_interface<T>*>(0);

               if (0 != (vi = dynamic_cast<vector_interface<T>*>(branch(1))))
               {
                  vec1_node_ptr_ = vi->vec();
                  v1_is_ivec     = true;
               }
            }

            if (vec0_node_ptr_ && vec1_node_ptr_)
            {
               vector_holder<T>& vec0 = vec0_node_ptr_->vec_holder();
               vector_holder<T>& vec1 = vec1_node_ptr_->vec_holder();

               if (v0_is_ivec && (vec0.size() <= vec1.size()))
                  vds_ = vds_t(vec0_node_ptr_->vds());
               else if (v1_is_ivec && (vec1.size() <= vec0.size()))
                  vds_ = vds_t(vec1_node_ptr_->vds());
               else
                  vds_ = vds_t(std::min(vec0.size(),vec1.size()));

               temp_          = new vector_holder<T>(vds().data(),vds().size());
               temp_vec_node_ = new vector_node  <T>(vds(),temp_);

               initialised_ = true;
            }

            assert(initialised_);
         }

        ~vec_binop_vecvec_node()
         {
            delete temp_;
            delete temp_vec_node_;
         }

         inline T value() const exprtk_override
         {
            if (initialised_)
            {
               assert(branch(0));
               assert(branch(1));

               branch(0)->value();
               branch(1)->value();

               const T* vec0 = vec0_node_ptr_->vds().data();
               const T* vec1 = vec1_node_ptr_->vds().data();
                     T* vec2 = vds().data();

               loop_unroll::details lud(size());
               const T* upper_bound = vec2 + lud.upper_bound;

               while (vec2 < upper_bound)
               {
                  #define exprtk_loop(N)                          \
                  vec2[N] = Operation::process(vec0[N], vec1[N]); \

                  exprtk_loop( 0) exprtk_loop( 1)
                  exprtk_loop( 2) exprtk_loop( 3)
                  exprtk_loop( 4) exprtk_loop( 5)
                  exprtk_loop( 6) exprtk_loop( 7)
                  exprtk_loop( 8) exprtk_loop( 9)
                  exprtk_loop(10) exprtk_loop(11)
                  exprtk_loop(12) exprtk_loop(13)
                  exprtk_loop(14) exprtk_loop(15)

                  vec0 += lud.batch_size;
                  vec1 += lud.batch_size;
                  vec2 += lud.batch_size;
               }

               int i = 0;

               exprtk_disable_fallthrough_begin
               switch (lud.remainder)
               {
                  #define case_stmt(N)                                              \
                  case N : { vec2[i] = Operation::process(vec0[i], vec1[i]); ++i; } \

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

               return (vds().data())[0];
            }
            else
               return std::numeric_limits<T>::quiet_NaN();
         }

         vector_node_ptr vec() const exprtk_override
         {
            return temp_vec_node_;
         }

         vector_node_ptr vec() exprtk_override
         {
            return temp_vec_node_;
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_vecvecarith;
         }

         std::size_t size() const exprtk_override
         {
            return vds_.size();
         }

         vds_t& vds() exprtk_override
         {
            return vds_;
         }

         const vds_t& vds() const exprtk_override
         {
            return vds_;
         }

         inline std::string to_string() const exprtk_override{
            return "(vec_binop_vecvec_node)";
         }
      private:

         vector_node_ptr   vec0_node_ptr_;
         vector_node_ptr   vec1_node_ptr_;
         vector_holder_ptr temp_;
         vector_node_ptr   temp_vec_node_;
         bool              initialised_;
         vds_t             vds_;
      };

      template <typename T, typename Operation>
      class vec_binop_vecval_node exprtk_final
                                  : public binary_node     <T>
                                  , public vector_interface<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef vector_node<T>*     vector_node_ptr;
         typedef vector_holder<T>*   vector_holder_ptr;
         typedef vec_data_store<T>   vds_t;

         using binary_node<T>::branch;

         vec_binop_vecval_node(const operator_type& opr,
                               expression_ptr branch0,
                               expression_ptr branch1)
         : binary_node<T>(opr, branch0, branch1)
         , vec0_node_ptr_(0)
         , temp_         (0)
         , temp_vec_node_(0)
         {
            bool v0_is_ivec = false;

            if (is_vector_node(branch(0)))
            {
               vec0_node_ptr_ = static_cast<vector_node_ptr>(branch(0));
            }
            else if (is_ivector_node(branch(0)))
            {
               vector_interface<T>* vi = reinterpret_cast<vector_interface<T>*>(0);

               if (0 != (vi = dynamic_cast<vector_interface<T>*>(branch(0))))
               {
                  vec0_node_ptr_ = vi->vec();
                  v0_is_ivec     = true;
               }
            }

            if (vec0_node_ptr_)
            {
               if (v0_is_ivec)
                  vds() = vec0_node_ptr_->vds();
               else
                  vds() = vds_t(vec0_node_ptr_->size());

               temp_          = new vector_holder<T>(vds());
               temp_vec_node_ = new vector_node  <T>(vds(),temp_);
            }
         }

        ~vec_binop_vecval_node()
         {
            delete temp_;
            delete temp_vec_node_;
         }

         inline T value() const exprtk_override
         {
            if (vec0_node_ptr_)
            {
               assert(branch(0));
               assert(branch(1));

                           branch(0)->value();
               const T v = branch(1)->value();

               const T* vec0 = vec0_node_ptr_->vds().data();
                     T* vec1 = vds().data();

               loop_unroll::details lud(size());
               const T* upper_bound = vec0 + lud.upper_bound;

               while (vec0 < upper_bound)
               {
                  #define exprtk_loop(N)                    \
                  vec1[N] = Operation::process(vec0[N], v); \

                  exprtk_loop( 0) exprtk_loop( 1)
                  exprtk_loop( 2) exprtk_loop( 3)
                  exprtk_loop( 4) exprtk_loop( 5)
                  exprtk_loop( 6) exprtk_loop( 7)
                  exprtk_loop( 8) exprtk_loop( 9)
                  exprtk_loop(10) exprtk_loop(11)
                  exprtk_loop(12) exprtk_loop(13)
                  exprtk_loop(14) exprtk_loop(15)

                  vec0 += lud.batch_size;
                  vec1 += lud.batch_size;
               }

               int i = 0;

               exprtk_disable_fallthrough_begin
               switch (lud.remainder)
               {
                  #define case_stmt(N)                                        \
                  case N : { vec1[i] = Operation::process(vec0[i], v); ++i; } \

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

               return (vds().data())[0];
            }
            else
               return std::numeric_limits<T>::quiet_NaN();
         }

         vector_node_ptr vec() const exprtk_override
         {
            return temp_vec_node_;
         }

         vector_node_ptr vec() exprtk_override
         {
            return temp_vec_node_;
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_vecvalarith;
         }

         std::size_t size() const exprtk_override
         {
            return vds().size();
         }

         vds_t& vds() exprtk_override
         {
            return vds_;
         }

         const vds_t& vds() const exprtk_override
         {
            return vds_;
         }

         inline std::string to_string() const exprtk_override{
            return "(vec_binop_vecval_node)";
         }
      private:

         vector_node_ptr   vec0_node_ptr_;
         vector_holder_ptr temp_;
         vector_node_ptr   temp_vec_node_;
         vds_t             vds_;
      };

      template <typename T, typename Operation>
      class vec_binop_valvec_node exprtk_final
                                  : public binary_node     <T>
                                  , public vector_interface<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef vector_node<T>*     vector_node_ptr;
         typedef vector_holder<T>*   vector_holder_ptr;
         typedef vec_data_store<T>   vds_t;

         using binary_node<T>::branch;

         vec_binop_valvec_node(const operator_type& opr,
                               expression_ptr branch0,
                               expression_ptr branch1)
         : binary_node<T>(opr, branch0, branch1)
         , vec1_node_ptr_(0)
         , temp_         (0)
         , temp_vec_node_(0)
         {
            bool v1_is_ivec = false;

            if (is_vector_node(branch(1)))
            {
               vec1_node_ptr_ = static_cast<vector_node_ptr>(branch(1));
            }
            else if (is_ivector_node(branch(1)))
            {
               vector_interface<T>* vi = reinterpret_cast<vector_interface<T>*>(0);

               if (0 != (vi = dynamic_cast<vector_interface<T>*>(branch(1))))
               {
                  vec1_node_ptr_ = vi->vec();
                  v1_is_ivec     = true;
               }
            }

            if (vec1_node_ptr_)
            {
               if (v1_is_ivec)
                  vds() = vec1_node_ptr_->vds();
               else
                  vds() = vds_t(vec1_node_ptr_->size());

               temp_          = new vector_holder<T>(vds());
               temp_vec_node_ = new vector_node  <T>(vds(),temp_);
            }
         }

        ~vec_binop_valvec_node()
         {
            delete temp_;
            delete temp_vec_node_;
         }

         inline T value() const exprtk_override
         {
            if (vec1_node_ptr_)
            {
               assert(branch(0));
               assert(branch(1));

               const T v = branch(0)->value();
                           branch(1)->value();

                     T* vec0 = vds().data();
               const T* vec1 = vec1_node_ptr_->vds().data();

               loop_unroll::details lud(size());
               const T* upper_bound = vec0 + lud.upper_bound;

               while (vec0 < upper_bound)
               {
                  #define exprtk_loop(N)                    \
                  vec0[N] = Operation::process(v, vec1[N]); \

                  exprtk_loop( 0) exprtk_loop( 1)
                  exprtk_loop( 2) exprtk_loop( 3)
                  exprtk_loop( 4) exprtk_loop( 5)
                  exprtk_loop( 6) exprtk_loop( 7)
                  exprtk_loop( 8) exprtk_loop( 9)
                  exprtk_loop(10) exprtk_loop(11)
                  exprtk_loop(12) exprtk_loop(13)
                  exprtk_loop(14) exprtk_loop(15)

                  vec0 += lud.batch_size;
                  vec1 += lud.batch_size;
               }

               int i = 0;

               exprtk_disable_fallthrough_begin
               switch (lud.remainder)
               {
                  #define case_stmt(N)                                        \
                  case N : { vec0[i] = Operation::process(v, vec1[i]); ++i; } \

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

               return (vds().data())[0];
            }
            else
               return std::numeric_limits<T>::quiet_NaN();
         }

         vector_node_ptr vec() const exprtk_override
         {
            return temp_vec_node_;
         }

         vector_node_ptr vec() exprtk_override
         {
            return temp_vec_node_;
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_vecvalarith;
         }

         std::size_t size() const exprtk_override
         {
            return vds().size();
         }

         vds_t& vds() exprtk_override
         {
            return vds_;
         }

         const vds_t& vds() const exprtk_override
         {
            return vds_;
         }

         inline std::string to_string() const exprtk_override{
            return "(vec_binop_valvec_node)";
         }
      private:

         vector_node_ptr   vec1_node_ptr_;
         vector_holder_ptr temp_;
         vector_node_ptr   temp_vec_node_;
         vds_t             vds_;
      };

      template <typename T, typename Operation>
      class unary_vector_node exprtk_final
                              : public unary_node      <T>
                              , public vector_interface<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef vector_node<T>*     vector_node_ptr;
         typedef vector_holder<T>*   vector_holder_ptr;
         typedef vec_data_store<T>   vds_t;

         using expression_node<T>::branch;

         unary_vector_node(const operator_type& opr, expression_ptr branch0)
         : unary_node<T>(opr, branch0)
         , vec0_node_ptr_(0)
         , temp_         (0)
         , temp_vec_node_(0)
         {
            bool vec0_is_ivec = false;

            if (is_vector_node(branch()))
            {
               vec0_node_ptr_ = static_cast<vector_node_ptr>(branch());
            }
            else if (is_ivector_node(branch()))
            {
               vector_interface<T>* vi = reinterpret_cast<vector_interface<T>*>(0);

               if (0 != (vi = dynamic_cast<vector_interface<T>*>(branch())))
               {
                  vec0_node_ptr_ = vi->vec();
                  vec0_is_ivec   = true;
               }
            }

            if (vec0_node_ptr_)
            {
               if (vec0_is_ivec)
                  vds_ = vec0_node_ptr_->vds();
               else
                  vds_ = vds_t(vec0_node_ptr_->size());

               temp_          = new vector_holder<T>(vds());
               temp_vec_node_ = new vector_node  <T>(vds(),temp_);
            }
         }

        ~unary_vector_node()
         {
            delete temp_;
            delete temp_vec_node_;
         }

         inline T value() const exprtk_override
         {
            assert(branch());

            branch()->value();

            if (vec0_node_ptr_)
            {
               const T* vec0 = vec0_node_ptr_->vds().data();
                     T* vec1 = vds().data();

               loop_unroll::details lud(size());
               const T* upper_bound = vec0 + lud.upper_bound;

               while (vec0 < upper_bound)
               {
                  #define exprtk_loop(N)                 \
                  vec1[N] = Operation::process(vec0[N]); \

                  exprtk_loop( 0) exprtk_loop( 1)
                  exprtk_loop( 2) exprtk_loop( 3)
                  exprtk_loop( 4) exprtk_loop( 5)
                  exprtk_loop( 6) exprtk_loop( 7)
                  exprtk_loop( 8) exprtk_loop( 9)
                  exprtk_loop(10) exprtk_loop(11)
                  exprtk_loop(12) exprtk_loop(13)
                  exprtk_loop(14) exprtk_loop(15)

                  vec0 += lud.batch_size;
                  vec1 += lud.batch_size;
               }

               int i = 0;

               exprtk_disable_fallthrough_begin
               switch (lud.remainder)
               {
                  #define case_stmt(N)                                     \
                  case N : { vec1[i] = Operation::process(vec0[i]); ++i; } \

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

               return (vds().data())[0];
            }
            else
               return std::numeric_limits<T>::quiet_NaN();
         }

         vector_node_ptr vec() const exprtk_override
         {
            return temp_vec_node_;
         }

         vector_node_ptr vec() exprtk_override
         {
            return temp_vec_node_;
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_vecunaryop;
         }

         std::size_t size() const exprtk_override
         {
            return vds().size();
         }

         vds_t& vds() exprtk_override
         {
            return vds_;
         }

         const vds_t& vds() const exprtk_override
         {
            return vds_;
         }

         inline std::string to_string() const exprtk_override{
            return "(vec_binop_valvec_node)";
         }
      private:

         vector_node_ptr   vec0_node_ptr_;
         vector_holder_ptr temp_;
         vector_node_ptr   temp_vec_node_;
         vds_t             vds_;
      };

      template <typename T>
      class conditional_vector_node exprtk_final
                                    : public expression_node <T>
                                    , public vector_interface<T>
      {
      public:

         typedef expression_node <T>* expression_ptr;
         typedef vector_interface<T>* vec_interface_ptr;
         typedef vector_node     <T>* vector_node_ptr;
         typedef vector_holder   <T>* vector_holder_ptr;
         typedef vec_data_store  <T>  vds_t;
         typedef std::pair<expression_ptr,bool> branch_t;

         conditional_vector_node(expression_ptr condition,
                                 expression_ptr consequent,
                                 expression_ptr alternative)
         : consequent_node_ptr_ (0)
         , alternative_node_ptr_(0)
         , temp_vec_node_       (0)
         , temp_                (0)
         , vec_size_            (0)
         , initialised_         (false)
         {
            construct_branch_pair(condition_  , condition  );
            construct_branch_pair(consequent_ , consequent );
            construct_branch_pair(alternative_, alternative);

            if (details::is_ivector_node(consequent_.first))
            {
               vec_interface_ptr ivec_ptr = dynamic_cast<vec_interface_ptr>(consequent_.first);

               if (0 != ivec_ptr)
               {
                  consequent_node_ptr_ = ivec_ptr->vec();
               }
            }

            if (details::is_ivector_node(alternative_.first))
            {
               vec_interface_ptr ivec_ptr = dynamic_cast<vec_interface_ptr>(alternative_.first);

               if (0 != ivec_ptr)
               {
                  alternative_node_ptr_ = ivec_ptr->vec();
               }
            }

            if (consequent_node_ptr_ && alternative_node_ptr_)
            {
               vec_size_ = std::min(consequent_node_ptr_ ->vds().size(),
                                    alternative_node_ptr_->vds().size());

               vds_           = vds_t(vec_size_);
               temp_          = new vector_holder<T>(vds_);
               temp_vec_node_ = new vector_node  <T>(vds(),temp_);

               initialised_ = true;
            }

            assert(initialised_ && (vec_size_ > 0));
         }

        ~conditional_vector_node()
         {
            delete temp_;
            delete temp_vec_node_;
         }

         inline T value() const exprtk_override
         {
            if (initialised_)
            {
               assert(condition_  .first);
               assert(consequent_ .first);
               assert(alternative_.first);

               T result = T(0);
               T* source_vector = 0;
               T* result_vector = vds().data();

               if (is_true(condition_))
               {
                  result        = consequent_.first->value();
                  source_vector = consequent_node_ptr_->vds().data();
               }
               else
               {
                  result        = alternative_.first->value();
                  source_vector = alternative_node_ptr_->vds().data();
               }

               for (std::size_t i = 0; i < vec_size_; ++i)
               {
                  result_vector[i] = source_vector[i];
               }

               return result;
            }

            return std::numeric_limits<T>::quiet_NaN();
         }

         vector_node_ptr vec() const exprtk_override
         {
            return temp_vec_node_;
         }

         vector_node_ptr vec() exprtk_override
         {
            return temp_vec_node_;
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_vecondition;
         }

         std::size_t size() const exprtk_override
         {
            return vec_size_;
         }

         vds_t& vds() exprtk_override
         {
            return vds_;
         }

         const vds_t& vds() const exprtk_override
         {
            return vds_;
         }

         void collect_nodes(typename expression_node<T>::noderef_list_t& node_delete_list) exprtk_override
         {
            expression_node<T>::ndb_t::collect(condition_   , node_delete_list);
            expression_node<T>::ndb_t::collect(consequent_  , node_delete_list);
            expression_node<T>::ndb_t::collect(alternative_ , node_delete_list);
         }

         std::size_t node_depth() const exprtk_override
         {
            return expression_node<T>::ndb_t::compute_node_depth
               (condition_, consequent_, alternative_);
         }

         inline std::string to_string() const exprtk_override{
            return "(conditional_vector_node)";
         }
      private:

         branch_t condition_;
         branch_t consequent_;
         branch_t alternative_;
         vector_node_ptr   consequent_node_ptr_;
         vector_node_ptr   alternative_node_ptr_;
         vector_node_ptr   temp_vec_node_;
         vector_holder_ptr temp_;
         vds_t vds_;
         std::size_t vec_size_;
         bool        initialised_;
      };

      template <typename T>
      class scand_node exprtk_final : public binary_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         using binary_node<T>::branch;

         scand_node(const operator_type& opr,
                    expression_ptr branch0,
                    expression_ptr branch1)
         : binary_node<T>(opr, branch0, branch1)
         {}

         inline T value() const exprtk_override
         {
            assert(branch(0));
            assert(branch(1));

            return (
                     std::not_equal_to<T>()
                        (T(0),branch(0)->value()) &&
                     std::not_equal_to<T>()
                        (T(0),branch(1)->value())
                   ) ? T(1) : T(0);
         }

         inline std::string to_string() const exprtk_override{
            return "(scand_node)";
         }
      };

      template <typename T>
      class scor_node exprtk_final : public binary_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         using binary_node<T>::branch;

         scor_node(const operator_type& opr,
                   expression_ptr branch0,
                   expression_ptr branch1)
         : binary_node<T>(opr, branch0, branch1)
         {}

         inline T value() const exprtk_override
         {
            assert(branch(0));
            assert(branch(1));

            return (
                     std::not_equal_to<T>()
                        (T(0),branch(0)->value()) ||
                     std::not_equal_to<T>()
                        (T(0),branch(1)->value())
                   ) ? T(1) : T(0);
         }

         inline std::string to_string() const exprtk_override{
            return "(scor_node)";
         }
      };

      template <typename T, typename IFunction, std::size_t N>
      class function_N_node exprtk_final : public expression_node<T>
      {
      public:

         // Function of N paramters.
         typedef expression_node<T>* expression_ptr;
         typedef std::pair<expression_ptr,bool> branch_t;
         typedef IFunction ifunction;

         explicit function_N_node(ifunction* func)
         : function_((N == func->param_count) ? func : reinterpret_cast<ifunction*>(0))
         , parameter_count_(func->param_count)
         {}

         template <std::size_t NumBranches>
         bool init_branches(expression_ptr (&b)[NumBranches])
         {
            // Needed for incompetent and broken msvc compiler versions
            #ifdef _MSC_VER
             #pragma warning(push)
             #pragma warning(disable: 4127)
            #endif
            if (N != NumBranches)
               return false;
            else
            {
               for (std::size_t i = 0; i < NumBranches; ++i)
               {
                  if (b[i])
                     branch_[i] = std::make_pair(b[i],branch_deletable(b[i]));
                  else
                     return false;
               }
               return true;
            }
            #ifdef _MSC_VER
             #pragma warning(pop)
            #endif
         }

         inline bool operator <(const function_N_node<T,IFunction,N>& fn) const
         {
            return this < (&fn);
         }

         inline T value() const exprtk_override
         {
            // Needed for incompetent and broken msvc compiler versions
            #ifdef _MSC_VER
             #pragma warning(push)
             #pragma warning(disable: 4127)
            #endif
            if ((0 == function_) || (0 == N))
               return std::numeric_limits<T>::quiet_NaN();
            else
            {
               T v[N];
               evaluate_branches<T,N>::execute(v,branch_);
               return invoke<T,N>::execute(*function_,v);
            }
            #ifdef _MSC_VER
             #pragma warning(pop)
            #endif
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_function;
         }

         void collect_nodes(typename expression_node<T>::noderef_list_t& node_delete_list) exprtk_override
         {
            expression_node<T>::ndb_t::template collect(branch_, node_delete_list);
         }

         std::size_t node_depth() const exprtk_override
         {
            return expression_node<T>::ndb_t::template compute_node_depth<N>(branch_);
         }

         template <typename T_, std::size_t BranchCount>
         struct evaluate_branches
         {
            static inline void execute(T_ (&v)[BranchCount], const branch_t (&b)[BranchCount])
            {
               for (std::size_t i = 0; i < BranchCount; ++i)
               {
                  v[i] = b[i].first->value();
               }
            }
         };

         template <typename T_>
         struct evaluate_branches <T_,5>
         {
            static inline void execute(T_ (&v)[5], const branch_t (&b)[5])
            {
               v[0] = b[0].first->value();
               v[1] = b[1].first->value();
               v[2] = b[2].first->value();
               v[3] = b[3].first->value();
               v[4] = b[4].first->value();
            }
         };

         template <typename T_>
         struct evaluate_branches <T_,4>
         {
            static inline void execute(T_ (&v)[4], const branch_t (&b)[4])
            {
               v[0] = b[0].first->value();
               v[1] = b[1].first->value();
               v[2] = b[2].first->value();
               v[3] = b[3].first->value();
            }
         };

         template <typename T_>
         struct evaluate_branches <T_,3>
         {
            static inline void execute(T_ (&v)[3], const branch_t (&b)[3])
            {
               v[0] = b[0].first->value();
               v[1] = b[1].first->value();
               v[2] = b[2].first->value();
            }
         };

         template <typename T_>
         struct evaluate_branches <T_,2>
         {
            static inline void execute(T_ (&v)[2], const branch_t (&b)[2])
            {
               v[0] = b[0].first->value();
               v[1] = b[1].first->value();
            }
         };

         template <typename T_>
         struct evaluate_branches <T_,1>
         {
            static inline void execute(T_ (&v)[1], const branch_t (&b)[1])
            {
               v[0] = b[0].first->value();
            }
         };

         template <typename T_, std::size_t ParamCount>
         struct invoke { static inline T execute(ifunction&, branch_t (&)[ParamCount]) { return std::numeric_limits<T_>::quiet_NaN(); } };

         template <typename T_>
         struct invoke<T_,20>
         {
            static inline T_ execute(ifunction& f, T_ (&v)[20])
            { return f(v[0],v[1],v[2],v[3],v[4],v[5],v[6],v[7],v[8],v[9],v[10],v[11],v[12],v[13],v[14],v[15],v[16],v[17],v[18],v[19]); }
         };

         template <typename T_>
         struct invoke<T_,19>
         {
            static inline T_ execute(ifunction& f, T_ (&v)[19])
            { return f(v[0],v[1],v[2],v[3],v[4],v[5],v[6],v[7],v[8],v[9],v[10],v[11],v[12],v[13],v[14],v[15],v[16],v[17],v[18]); }
         };

         template <typename T_>
         struct invoke<T_,18>
         {
            static inline T_ execute(ifunction& f, T_ (&v)[18])
            { return f(v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8], v[9], v[10], v[11], v[12], v[13], v[14], v[15], v[16], v[17]); }
         };

         template <typename T_>
         struct invoke<T_,17>
         {
            static inline T_ execute(ifunction& f, T_ (&v)[17])
            { return f(v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8], v[9], v[10], v[11], v[12], v[13], v[14], v[15], v[16]); }
         };

         template <typename T_>
         struct invoke<T_,16>
         {
            static inline T_ execute(ifunction& f, T_ (&v)[16])
            { return f(v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8], v[9], v[10], v[11], v[12], v[13], v[14], v[15]); }
         };

         template <typename T_>
         struct invoke<T_,15>
         {
            static inline T_ execute(ifunction& f, T_ (&v)[15])
            { return f(v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8], v[9], v[10], v[11], v[12], v[13], v[14]); }
         };

         template <typename T_>
         struct invoke<T_,14>
         {
            static inline T_ execute(ifunction& f, T_ (&v)[14])
            { return f(v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8], v[9], v[10], v[11], v[12], v[13]); }
         };

         template <typename T_>
         struct invoke<T_,13>
         {
            static inline T_ execute(ifunction& f, T_ (&v)[13])
            { return f(v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8], v[9], v[10], v[11], v[12]); }
         };

         template <typename T_>
         struct invoke<T_,12>
         {
            static inline T_ execute(ifunction& f, T_ (&v)[12])
            { return f(v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8], v[9], v[10], v[11]); }
         };

         template <typename T_>
         struct invoke<T_,11>
         {
            static inline T_ execute(ifunction& f, T_ (&v)[11])
            { return f(v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8], v[9], v[10]); }
         };

         template <typename T_>
         struct invoke<T_,10>
         {
            static inline T_ execute(ifunction& f, T_ (&v)[10])
            { return f(v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8], v[9]); }
         };

         template <typename T_>
         struct invoke<T_,9>
         {
            static inline T_ execute(ifunction& f, T_ (&v)[9])
            { return f(v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8]); }
         };

         template <typename T_>
         struct invoke<T_,8>
         {
            static inline T_ execute(ifunction& f, T_ (&v)[8])
            { return f(v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7]); }
         };

         template <typename T_>
         struct invoke<T_,7>
         {
            static inline T_ execute(ifunction& f, T_ (&v)[7])
            { return f(v[0], v[1], v[2], v[3], v[4], v[5], v[6]); }
         };

         template <typename T_>
         struct invoke<T_,6>
         {
            static inline T_ execute(ifunction& f, T_ (&v)[6])
            { return f(v[0], v[1], v[2], v[3], v[4], v[5]); }
         };

         template <typename T_>
         struct invoke<T_,5>
         {
            static inline T_ execute(ifunction& f, T_ (&v)[5])
            { return f(v[0], v[1], v[2], v[3], v[4]); }
         };

         template <typename T_>
         struct invoke<T_,4>
         {
            static inline T_ execute(ifunction& f, T_ (&v)[4])
            { return f(v[0], v[1], v[2], v[3]); }
         };

         template <typename T_>
         struct invoke<T_,3>
         {
            static inline T_ execute(ifunction& f, T_ (&v)[3])
            { return f(v[0], v[1], v[2]); }
         };

         template <typename T_>
         struct invoke<T_,2>
         {
            static inline T_ execute(ifunction& f, T_ (&v)[2])
            { return f(v[0], v[1]); }
         };

         template <typename T_>
         struct invoke<T_,1>
         {
            static inline T_ execute(ifunction& f, T_ (&v)[1])
            { return f(v[0]); }
         };

         inline std::string to_string() const exprtk_override{
            return "(function_N_node)";
         }
      private:

         ifunction*  function_;
         std::size_t parameter_count_;
         branch_t    branch_[N];
      };

      template <typename T, typename IFunction>
      class function_N_node<T,IFunction,0> exprtk_final : public expression_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef IFunction ifunction;

         explicit function_N_node(ifunction* func)
         : function_((0 == func->param_count) ? func : reinterpret_cast<ifunction*>(0))
         {}

         inline bool operator <(const function_N_node<T,IFunction,0>& fn) const
         {
            return this < (&fn);
         }

         inline T value() const exprtk_override
         {
            if (function_)
               return (*function_)();
            else
               return std::numeric_limits<T>::quiet_NaN();
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_function;
         }

         inline std::string to_string() const exprtk_override{
            return "(function_N_node)";
         }
      private:

         ifunction* function_;
      };

      template <typename T, typename VarArgFunction>
      class vararg_function_node exprtk_final : public expression_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;

         vararg_function_node(VarArgFunction*  func,
                              const std::vector<expression_ptr>& arg_list)
         : function_(func)
         , arg_list_(arg_list)
         {
            value_list_.resize(arg_list.size(),std::numeric_limits<T>::quiet_NaN());
         }

         inline bool operator <(const vararg_function_node<T,VarArgFunction>& fn) const
         {
            return this < (&fn);
         }

         inline T value() const exprtk_override
         {
            if (function_)
            {
               populate_value_list();
               return (*function_)(value_list_);
            }
            else
               return std::numeric_limits<T>::quiet_NaN();
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_vafunction;
         }

         void collect_nodes(typename expression_node<T>::noderef_list_t& node_delete_list) exprtk_override
         {
            for (std::size_t i = 0; i < arg_list_.size(); ++i)
            {
               if (arg_list_[i] && !details::is_variable_node(arg_list_[i]))
               {
                  node_delete_list.push_back(&arg_list_[i]);
               }
            }
         }

         std::size_t node_depth() const exprtk_override
         {
            return expression_node<T>::ndb_t::compute_node_depth(arg_list_);
         }

         inline std::string to_string() const exprtk_override{
            return "(vararg_function_node)";
         }
      private:

         inline void populate_value_list() const
         {
            for (std::size_t i = 0; i < arg_list_.size(); ++i)
            {
               value_list_[i] = arg_list_[i]->value();
            }
         }

         VarArgFunction* function_;
         std::vector<expression_ptr> arg_list_;
         mutable std::vector<T> value_list_;
      };

      template <typename T, typename GenericFunction>
      class generic_function_node : public expression_node<T>
      {
      public:

         typedef type_store<T>       type_store_t;
         typedef expression_node<T>* expression_ptr;
         typedef variable_node<T>    variable_node_t;
         typedef vector_node<T>      vector_node_t;
         typedef variable_node_t*    variable_node_ptr_t;
         typedef vector_node_t*      vector_node_ptr_t;
         typedef range_interface<T>  range_interface_t;
         typedef range_data_type<T>  range_data_type_t;
         typedef typename range_interface<T>::range_t range_t;

         typedef std::pair<expression_ptr,bool> branch_t;
         typedef std::pair<void*,std::size_t>   void_t;

         typedef std::vector<T>                 tmp_vs_t;
         typedef std::vector<type_store_t>      typestore_list_t;
         typedef std::vector<range_data_type_t> range_list_t;

         explicit generic_function_node(const std::vector<expression_ptr>& arg_list,
                                        GenericFunction* func = reinterpret_cast<GenericFunction*>(0))
         : function_(func)
         , arg_list_(arg_list)
         {}

         virtual ~generic_function_node() {}

         void collect_nodes(typename expression_node<T>::noderef_list_t& node_delete_list) exprtk_override
         {
            expression_node<T>::ndb_t::collect(branch_, node_delete_list);
         }

         std::size_t node_depth() const exprtk_override exprtk_final
         {
            return expression_node<T>::ndb_t::compute_node_depth(branch_);
         }

         virtual bool init_branches()
         {
            expr_as_vec1_store_.resize(arg_list_.size(),T(0)               );
            typestore_list_    .resize(arg_list_.size(),type_store_t()     );
            range_list_        .resize(arg_list_.size(),range_data_type_t());
            branch_            .resize(arg_list_.size(),branch_t(reinterpret_cast<expression_ptr>(0),false));

            for (std::size_t i = 0; i < arg_list_.size(); ++i)
            {
               type_store_t& ts = typestore_list_[i];

               if (0 == arg_list_[i])
                  return false;
               else if (is_ivector_node(arg_list_[i]))
               {
                  vector_interface<T>* vi = reinterpret_cast<vector_interface<T>*>(0);

                  if (0 == (vi = dynamic_cast<vector_interface<T>*>(arg_list_[i])))
                     return false;

                  ts.size = vi->size();
                  ts.data = vi->vds().data();
                  ts.type = type_store_t::e_vector;
                  vi->vec()->vec_holder().set_ref(&ts.vec_data);
               }
               else if (is_generally_string_node(arg_list_[i]) && !disable_string_capabilities)
               {
                  string_base_node<T>* sbn = reinterpret_cast<string_base_node<T>*>(0);

                  if (0 == (sbn = dynamic_cast<string_base_node<T>*>(arg_list_[i])))
                     return false;

                  ts.size = sbn->size();
                  ts.data = reinterpret_cast<void*>(const_cast<char_ptr>(sbn->base()));
                  ts.type = type_store_t::e_string;

                  range_list_[i].data      = ts.data;
                  range_list_[i].size      = ts.size;
                  range_list_[i].type_size = sizeof(char);
                  range_list_[i].str_node  = sbn;

                  range_interface_t* ri = reinterpret_cast<range_interface_t*>(0);

                  if (0 == (ri = dynamic_cast<range_interface_t*>(arg_list_[i])))
                     return false;

                  const range_t& rp = ri->range_ref();

                  if (
                       rp.const_range() &&
                       is_const_string_range_node(arg_list_[i])
                     )
                  {
                     ts.size = rp.const_size();
                     ts.data = static_cast<char_ptr>(ts.data) + rp.n0_c.second;
                     range_list_[i].range = reinterpret_cast<range_t*>(0);
                  }
                  else
                     range_list_[i].range = &(ri->range_ref());
               }
               else if (is_variable_node(arg_list_[i]))
               {
                  variable_node_ptr_t var = variable_node_ptr_t(0);

                  if (0 == (var = dynamic_cast<variable_node_ptr_t>(arg_list_[i])))
                     return false;

                  ts.size = 1;
                  ts.data = &var->ref();
                  ts.type = type_store_t::e_scalar;
               }
               else
               {
                  ts.size = 1;
                  ts.data = reinterpret_cast<void*>(&expr_as_vec1_store_[i]);
                  ts.type = type_store_t::e_scalar;
               }

               branch_[i] = std::make_pair(arg_list_[i],branch_deletable(arg_list_[i]));
            }

            return true;
         }

         inline bool operator <(const generic_function_node<T,GenericFunction>& fn) const
         {
            return this < (&fn);
         }

         inline T value() const exprtk_override
         {
            if (function_)
            {
               if (populate_value_list())
               {
                  typedef typename GenericFunction::parameter_list_t parameter_list_t;

                  return (*function_)(parameter_list_t(typestore_list_));
               }
            }

            return std::numeric_limits<T>::quiet_NaN();
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_genfunction;
         }

         inline std::string to_string() const exprtk_override{
            return "(generic_function_node)";
         }
      protected:

         inline virtual bool populate_value_list() const
         {
            for (std::size_t i = 0; i < branch_.size(); ++i)
            {
               expr_as_vec1_store_[i] = branch_[i].first->value();
            }

            for (std::size_t i = 0; i < branch_.size(); ++i)
            {
               range_data_type_t& rdt = range_list_[i];

               if (rdt.range)
               {
                  const range_t& rp = (*rdt.range);
                  std::size_t r0    = 0;
                  std::size_t r1    = 0;

                  if (rp(r0, r1, rdt.size))
                  {
                     type_store_t& ts = typestore_list_[i];

                     ts.size = rp.cache_size();
                     if (ts.type == type_store_t::e_string && !disable_string_capabilities)
                        ts.data = const_cast<char_ptr>(rdt.str_node->base()) + rp.cache.first;
                     ts.data = static_cast<char_ptr>(rdt.data) + (rp.cache.first * rdt.type_size);
                  }
                  else
                     return false;
               }
            }

            return true;
         }

         GenericFunction* function_;
         mutable typestore_list_t typestore_list_;

      private:

         std::vector<expression_ptr> arg_list_;
         std::vector<branch_t>         branch_;
         mutable tmp_vs_t  expr_as_vec1_store_;
         mutable range_list_t      range_list_;
      };

      template <typename T, typename StringFunction>
      class string_function_node : public generic_function_node<T,StringFunction>,
                                   public string_base_node<T>,
                                   public range_interface <T>
      {
      public:

         typedef generic_function_node<T,StringFunction> gen_function_t;
         typedef typename range_interface<T>::range_t range_t;

         string_function_node(StringFunction* func,
                              const std::vector<typename gen_function_t::expression_ptr>& arg_list)
         : gen_function_t(arg_list,func)
         {
            range_.n0_c = std::make_pair<bool,std::size_t>(true,0);
            range_.n1_c = std::make_pair<bool,std::size_t>(true,0);
            range_.cache.first  = range_.n0_c.second;
            range_.cache.second = range_.n1_c.second;
         }

         inline bool operator <(const string_function_node<T,StringFunction>& fn) const
         {
            return this < (&fn);
         }

         inline T value() const exprtk_override
         {
            if (gen_function_t::function_)
            {
               if (gen_function_t::populate_value_list())
               {
                  typedef typename StringFunction::parameter_list_t parameter_list_t;

                  const T result = (*gen_function_t::function_)
                                      (
                                        ret_string_,
                                        parameter_list_t(gen_function_t::typestore_list_)
                                      );

                  range_.n1_c.second  = ret_string_.size() - 1;
                  range_.cache.second = range_.n1_c.second;

                  return result;
               }
            }

            return std::numeric_limits<T>::quiet_NaN();
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_strfunction;
         }

         std::string str() const exprtk_override
         {
            return ret_string_;
         }

         char_cptr base() const exprtk_override
         {
           return &ret_string_[0];
         }

         std::size_t size() const exprtk_override
         {
            return ret_string_.size();
         }

         range_t& range_ref() exprtk_override
         {
            return range_;
         }

         const range_t& range_ref() const exprtk_override
         {
            return range_;
         }

         inline std::string to_string() const exprtk_override{
            return "(string_function_node)";
         }
      protected:

         mutable range_t     range_;
         mutable std::string ret_string_;
      };

      template <typename T, typename GenericFunction>
      class multimode_genfunction_node : public generic_function_node<T,GenericFunction>
      {
      public:

         typedef generic_function_node<T,GenericFunction> gen_function_t;
         typedef typename gen_function_t::range_t         range_t;

         multimode_genfunction_node(GenericFunction* func,
                                    const std::size_t& param_seq_index,
                                    const std::vector<typename gen_function_t::expression_ptr>& arg_list)
         : gen_function_t(arg_list,func)
         , param_seq_index_(param_seq_index)
         {}

         inline T value() const exprtk_override
         {
            if (gen_function_t::function_)
            {
               if (gen_function_t::populate_value_list())
               {
                  typedef typename GenericFunction::parameter_list_t parameter_list_t;

                  return (*gen_function_t::function_)
                            (
                              param_seq_index_,
                              parameter_list_t(gen_function_t::typestore_list_)
                            );
               }
            }

            return std::numeric_limits<T>::quiet_NaN();
         }

         inline typename expression_node<T>::node_type type() const exprtk_override exprtk_final
         {
            return expression_node<T>::e_genfunction;
         }

         inline std::string to_string() const exprtk_override{
            return "(multimode_genfunction_node)";
         }
      private:

         std::size_t param_seq_index_;
      };

      template <typename T, typename StringFunction>
      class multimode_strfunction_node exprtk_final : public string_function_node<T,StringFunction>
      {
      public:

         typedef string_function_node<T,StringFunction> str_function_t;
         typedef typename str_function_t::range_t range_t;

         multimode_strfunction_node(StringFunction* func,
                                    const std::size_t& param_seq_index,
                                    const std::vector<typename str_function_t::expression_ptr>& arg_list)
         : str_function_t(func,arg_list)
         , param_seq_index_(param_seq_index)
         {}

         inline T value() const exprtk_override
         {
            if (str_function_t::function_)
            {
               if (str_function_t::populate_value_list())
               {
                  typedef typename StringFunction::parameter_list_t parameter_list_t;

                  const T result = (*str_function_t::function_)
                                      (
                                        param_seq_index_,
                                        str_function_t::ret_string_,
                                        parameter_list_t(str_function_t::typestore_list_)
                                      );

                  str_function_t::range_.n1_c.second  = str_function_t::ret_string_.size() - 1;
                  str_function_t::range_.cache.second = str_function_t::range_.n1_c.second;

                  return result;
               }
            }

            return std::numeric_limits<T>::quiet_NaN();
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_strfunction;
         }

         inline std::string to_string() const exprtk_override{
            return "(multimode_strfunction_node)";
         }
      private:

         const std::size_t param_seq_index_;
      };

      class return_exception
      {};

      template <typename T>
      class null_igenfunc
      {
      public:

         virtual ~null_igenfunc() {}

         typedef type_store<T> generic_type;
         typedef typename generic_type::parameter_list parameter_list_t;

         inline virtual T operator() (parameter_list_t)
         {
            return std::numeric_limits<T>::quiet_NaN();
         }
      };

      template <typename T>
      class return_node exprtk_final : public generic_function_node<T,null_igenfunc<T> >
      {
      public:

         typedef results_context<T>   results_context_t;
         typedef null_igenfunc<T>     igeneric_function_t;
         typedef igeneric_function_t* igeneric_function_ptr;
         typedef generic_function_node<T,igeneric_function_t> gen_function_t;

         return_node(const std::vector<typename gen_function_t::expression_ptr>& arg_list,
                     results_context_t& rc)
         : gen_function_t  (arg_list)
         , results_context_(&rc)
         {}

         inline T value() const exprtk_override
         {
            if (
                 (0 != results_context_) &&
                 gen_function_t::populate_value_list()
               )
            {
               typedef typename type_store<T>::parameter_list parameter_list_t;

               results_context_->
                  assign(parameter_list_t(gen_function_t::typestore_list_));

               throw return_exception();
            }

            return std::numeric_limits<T>::quiet_NaN();
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_return;
         }

         inline std::string to_string() const exprtk_override{
            return "(return_node)";
         }
      private:

         results_context_t* results_context_;
      };

      template <typename T>
      class return_envelope_node exprtk_final : public expression_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef results_context<T>  results_context_t;
         typedef std::pair<expression_ptr,bool> branch_t;

         return_envelope_node(expression_ptr body, results_context_t& rc)
         : results_context_(&rc  )
         , return_invoked_ (false)
         {
            construct_branch_pair(body_, body);
         }

         inline T value() const exprtk_override
         {
            assert(body_.first);

            try
            {
               return_invoked_ = false;
               results_context_->clear();

               return body_.first->value();
            }
            catch(const return_exception&)
            {
               return_invoked_ = true;
               return std::numeric_limits<T>::quiet_NaN();
            }
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_retenv;
         }

         inline bool* retinvk_ptr()
         {
            return &return_invoked_;
         }

         void collect_nodes(typename expression_node<T>::noderef_list_t& node_delete_list) exprtk_override
         {
            expression_node<T>::ndb_t::collect(body_, node_delete_list);
         }

         std::size_t node_depth() const exprtk_override
         {
            return expression_node<T>::ndb_t::compute_node_depth(body_);
         }

         inline std::string to_string() const exprtk_override{
            return "(return_envelope_node)";
         }
      private:

         results_context_t* results_context_;
         mutable bool        return_invoked_;
         branch_t                      body_;
      };

      #define exprtk_define_unary_op(OpName)                    \
      template <typename T>                                     \
      struct OpName##_op                                        \
      {                                                         \
         typedef typename functor_t<T>::Type Type;              \
         typedef typename expression_node<T>::node_type node_t; \
                                                                \
         static inline T process(Type v)                        \
         {                                                      \
            return numeric:: OpName (v);                        \
         }                                                      \
                                                                \
         static inline node_t type()                            \
         {                                                      \
            return expression_node<T>::e_##OpName;              \
         }                                                      \
                                                                \
         static inline details::operator_type operation()       \
         {                                                      \
            return details::e_##OpName;                         \
         }                                                      \
      }; 
            template <typename T>
      class vov_base_node : public expression_node<T>
      {
      public:

         virtual ~vov_base_node() {}

         inline virtual operator_type operation() const
         {
            return details::e_default;
         }

         virtual const T& v0() const = 0;

         virtual const T& v1() const = 0;
      };

      template <typename T>
      class cov_base_node : public expression_node<T>
      {
      public:

         virtual ~cov_base_node() {}

         inline virtual operator_type operation() const
         {
            return details::e_default;
         }

         virtual const T c() const = 0;

         virtual const T& v() const = 0;
      };

      template <typename T>
      class voc_base_node : public expression_node<T>
      {
      public:

         virtual ~voc_base_node() {}

         inline virtual operator_type operation() const
         {
            return details::e_default;
         }

         virtual const T c() const = 0;

         virtual const T& v() const = 0;
      };

      template <typename T>
      class vob_base_node : public expression_node<T>
      {
      public:

         virtual ~vob_base_node() {}

         virtual const T& v() const = 0;
      };

      template <typename T>
      class bov_base_node : public expression_node<T>
      {
      public:

         virtual ~bov_base_node() {}

         virtual const T& v() const = 0;
      };

      template <typename T>
      class cob_base_node : public expression_node<T>
      {
      public:

         virtual ~cob_base_node() {}

         inline virtual operator_type operation() const
         {
            return details::e_default;
         }

         virtual const T c() const = 0;

         virtual void set_c(const T) = 0;

         virtual expression_node<T>* move_branch(const std::size_t& index) = 0;
      };

      template <typename T>
      class boc_base_node : public expression_node<T>
      {
      public:

         virtual ~boc_base_node() {}

         inline virtual operator_type operation() const
         {
            return details::e_default;
         }

         virtual const T c() const = 0;

         virtual void set_c(const T) = 0;

         virtual expression_node<T>* move_branch(const std::size_t& index) = 0;
      };

      template <typename T>
      class uv_base_node : public expression_node<T>
      {
      public:

         virtual ~uv_base_node() {}

         inline virtual operator_type operation() const
         {
            return details::e_default;
         }

         virtual const T& v() const = 0;
      };

      template <typename T>
      class sos_base_node : public expression_node<T>
      {
      public:

         virtual ~sos_base_node() {}

         inline virtual operator_type operation() const
         {
            return details::e_default;
         }
      };

      template <typename T>
      class sosos_base_node : public expression_node<T>
      {
      public:

         virtual ~sosos_base_node() {}

         inline virtual operator_type operation() const
         {
            return details::e_default;
         }
      };

      template <typename T>
      class T0oT1oT2_base_node : public expression_node<T>
      {
      public:

         virtual ~T0oT1oT2_base_node() {}

         virtual std::string type_id() const = 0;
      };

      template <typename T>
      class T0oT1oT2oT3_base_node : public expression_node<T>
      {
      public:

         virtual ~T0oT1oT2oT3_base_node() {}

         virtual std::string type_id() const = 0;
      };

      template <typename T, typename Operation>
      class unary_variable_node exprtk_final : public uv_base_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef Operation operation_t;

         explicit unary_variable_node(const T& var)
         : v_(var)
         {}

         inline T value() const exprtk_override
         {
            return Operation::process(v_);
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return Operation::type();
         }

         inline operator_type operation() const exprtk_override
         {
            return Operation::operation();
         }

         inline const T& v() const exprtk_override
         {
            return v_;
         }

         inline std::string to_string() const exprtk_override{
            return "(unary_variable_node)";
         }
      private:

         unary_variable_node(const unary_variable_node<T,Operation>&) exprtk_delete;
         unary_variable_node<T,Operation>& operator=(const unary_variable_node<T,Operation>&) exprtk_delete;

         const T& v_;
      };

      template <typename T>
      class uvouv_node exprtk_final : public expression_node<T>
      {
      public:

         // UOpr1(v0) Op UOpr2(v1)
         typedef typename details::functor_t<T> functor_t;
         typedef typename functor_t::bfunc_t    bfunc_t;
         typedef typename functor_t::ufunc_t    ufunc_t;
         typedef expression_node<T>*            expression_ptr;

         explicit uvouv_node(const T& var0,const T& var1,
                             ufunc_t uf0, ufunc_t uf1, bfunc_t bf)
         : v0_(var0)
         , v1_(var1)
         , u0_(uf0 )
         , u1_(uf1 )
         , f_ (bf  )
         {}

         inline T value() const exprtk_override
         {
            return f_(u0_(v0_),u1_(v1_));
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_uvouv;
         }

         inline const T& v0()
         {
            return v0_;
         }

         inline const T& v1()
         {
            return v1_;
         }

         inline ufunc_t u0()
         {
            return u0_;
         }

         inline ufunc_t u1()
         {
            return u1_;
         }

         inline ufunc_t f()
         {
            return f_;
         }

         inline std::string to_string() const exprtk_override{
            return "(uvouv_node)";
         }
      private:

         uvouv_node(const uvouv_node<T>&) exprtk_delete;
         uvouv_node<T>& operator=(const uvouv_node<T>&) exprtk_delete;

         const T& v0_;
         const T& v1_;
         const ufunc_t u0_;
         const ufunc_t u1_;
         const bfunc_t f_;
      };

      template <typename T, typename Operation>
      class unary_branch_node exprtk_final : public expression_node<T>
      {
      public:

         typedef Operation                      operation_t;
         typedef expression_node<T>*            expression_ptr;
         typedef std::pair<expression_ptr,bool> branch_t;

         explicit unary_branch_node(expression_ptr branch)
         {
            construct_branch_pair(branch_, branch);
         }

         inline T value() const exprtk_override
         {
            return Operation::process(branch_.first->value());
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return Operation::type();
         }

         inline operator_type operation() const
         {
            return Operation::operation();
         }

         inline expression_node<T>* branch(const std::size_t&) const exprtk_override
         {
            return branch_.first;
         }

         inline void release()
         {
            branch_.second = false;
         }

         void collect_nodes(typename expression_node<T>::noderef_list_t& node_delete_list) exprtk_override
         {
            expression_node<T>::ndb_t::collect(branch_, node_delete_list);
         }

         std::size_t node_depth() const exprtk_override
         {
            return expression_node<T>::ndb_t::compute_node_depth(branch_);
         }

         inline std::string to_string() const exprtk_override{
            char _buf[2048]{0};
            std::string _name = to_str(operation());
            std::string _arg1 = branch_.first->to_string();
            sprintf(_buf, _name.c_str(), _arg1.c_str());
            return _buf;
         }
      private:

         unary_branch_node(const unary_branch_node<T,Operation>&) exprtk_delete;
         unary_branch_node<T,Operation>& operator=(const unary_branch_node<T,Operation>&) exprtk_delete;

         branch_t branch_;
      };
            #define exprtk_crtype(Type)                          \
      param_to_str<is_const_ref< Type >::result>::result() \

      template <typename T>
      struct T0oT1oT2process
      {
         typedef typename details::functor_t<T> functor_t;
         typedef typename functor_t::bfunc_t    bfunc_t;

         struct mode0
         {
            static inline T process(const T& t0, const T& t1, const T& t2, const bfunc_t bf0, const bfunc_t bf1)
            {
               // (T0 o0 T1) o1 T2
               return bf1(bf0(t0,t1),t2);
            }

            template <typename T0, typename T1, typename T2>
            static inline std::string id()
            {
               static const std::string result = "(" + exprtk_crtype(T0) + "o"   +
                                                       exprtk_crtype(T1) + ")o(" +
                                                       exprtk_crtype(T2) + ")"   ;
               return result;
            }
         };

         struct mode1
         {
            static inline T process(const T& t0, const T& t1, const T& t2, const bfunc_t bf0, const bfunc_t bf1)
            {
               // T0 o0 (T1 o1 T2)
               return bf0(t0,bf1(t1,t2));
            }

            template <typename T0, typename T1, typename T2>
            static inline std::string id()
            {
               static const std::string result = "(" + exprtk_crtype(T0) + ")o(" +
                                                       exprtk_crtype(T1) + "o"   +
                                                       exprtk_crtype(T2) + ")"   ;
               return result;
            }
         };
      };

      template <typename T>
      struct T0oT1oT20T3process
      {
         typedef typename details::functor_t<T> functor_t;
         typedef typename functor_t::bfunc_t    bfunc_t;

         struct mode0
         {
            static inline T process(const T& t0, const T& t1,
                                    const T& t2, const T& t3,
                                    const bfunc_t bf0, const bfunc_t bf1, const bfunc_t bf2)
            {
               // (T0 o0 T1) o1 (T2 o2 T3)
               return bf1(bf0(t0,t1),bf2(t2,t3));
            }

            template <typename T0, typename T1, typename T2, typename T3>
            static inline std::string id()
            {
               static const std::string result = "(" + exprtk_crtype(T0) + "o"  +
                                                       exprtk_crtype(T1) + ")o" +
                                                 "(" + exprtk_crtype(T2) + "o"  +
                                                       exprtk_crtype(T3) + ")"  ;
               return result;
            }
         };

         struct mode1
         {
            static inline T process(const T& t0, const T& t1,
                                    const T& t2, const T& t3,
                                    const bfunc_t bf0, const bfunc_t bf1, const bfunc_t bf2)
            {
               // (T0 o0 (T1 o1 (T2 o2 T3))
               return bf0(t0,bf1(t1,bf2(t2,t3)));
            }
            template <typename T0, typename T1, typename T2, typename T3>
            static inline std::string id()
            {
               static const std::string result = "(" + exprtk_crtype(T0) +  ")o((" +
                                                       exprtk_crtype(T1) +  ")o("  +
                                                       exprtk_crtype(T2) +  "o"    +
                                                       exprtk_crtype(T3) +  "))"   ;
               return result;
            }
         };

         struct mode2
         {
            static inline T process(const T& t0, const T& t1,
                                    const T& t2, const T& t3,
                                    const bfunc_t bf0, const bfunc_t bf1, const bfunc_t bf2)
            {
               // (T0 o0 ((T1 o1 T2) o2 T3)
               return bf0(t0,bf2(bf1(t1,t2),t3));
            }

            template <typename T0, typename T1, typename T2, typename T3>
            static inline std::string id()
            {
               static const std::string result = "(" + exprtk_crtype(T0) + ")o((" +
                                                       exprtk_crtype(T1) + "o"    +
                                                       exprtk_crtype(T2) + ")o("  +
                                                       exprtk_crtype(T3) + "))"   ;
               return result;
            }
         };

         struct mode3
         {
            static inline T process(const T& t0, const T& t1,
                                    const T& t2, const T& t3,
                                    const bfunc_t bf0, const bfunc_t bf1, const bfunc_t bf2)
            {
               // (((T0 o0 T1) o1 T2) o2 T3)
               return bf2(bf1(bf0(t0,t1),t2),t3);
            }

            template <typename T0, typename T1, typename T2, typename T3>
            static inline std::string id()
            {
               static const std::string result = "((" + exprtk_crtype(T0) + "o"    +
                                                        exprtk_crtype(T1) + ")o("  +
                                                        exprtk_crtype(T2) + "))o(" +
                                                        exprtk_crtype(T3) + ")";
               return result;
            }
         };

         struct mode4
         {
            static inline T process(const T& t0, const T& t1,
                                    const T& t2, const T& t3,
                                    const bfunc_t bf0, const bfunc_t bf1, const bfunc_t bf2)
            {
               // ((T0 o0 (T1 o1 T2)) o2 T3
               return bf2(bf0(t0,bf1(t1,t2)),t3);
            }

            template <typename T0, typename T1, typename T2, typename T3>
            static inline std::string id()
            {
               static const std::string result = "((" + exprtk_crtype(T0) + ")o("  +
                                                        exprtk_crtype(T1) + "o"    +
                                                        exprtk_crtype(T2) + "))o(" +
                                                        exprtk_crtype(T3) + ")"    ;
               return result;
            }
         };
      };

      #undef exprtk_crtype

      template <typename T, typename T0, typename T1>
      struct nodetype_T0oT1 { static const typename expression_node<T>::node_type result; };
      template <typename T, typename T0, typename T1>
      const typename expression_node<T>::node_type nodetype_T0oT1<T,T0,T1>::result = expression_node<T>::e_none;

      #define synthesis_node_type_define(T0_, T1_, v_)                                                          \
      template <typename T, typename T0, typename T1>                                                           \
      struct nodetype_T0oT1<T,T0_,T1_> { static const typename expression_node<T>::node_type result; };         \
      template <typename T, typename T0, typename T1>                                                           \
      const typename expression_node<T>::node_type nodetype_T0oT1<T,T0_,T1_>::result = expression_node<T>:: v_; \

      synthesis_node_type_define(const T0&, const T1&,  e_vov)
      synthesis_node_type_define(const T0&, const T1 ,  e_voc)
      synthesis_node_type_define(const T0 , const T1&,  e_cov)
      synthesis_node_type_define(      T0&,       T1&, e_none)
      synthesis_node_type_define(const T0 , const T1 , e_none)
      synthesis_node_type_define(      T0&, const T1 , e_none)
      synthesis_node_type_define(const T0 ,       T1&, e_none)
      synthesis_node_type_define(const T0&,       T1&, e_none)
      synthesis_node_type_define(      T0&, const T1&, e_none)
      #undef synthesis_node_type_define

      template <typename T, typename T0, typename T1, typename T2>
      struct nodetype_T0oT1oT2 { static const typename expression_node<T>::node_type result; };
      template <typename T, typename T0, typename T1, typename T2>
      const typename expression_node<T>::node_type nodetype_T0oT1oT2<T,T0,T1,T2>::result = expression_node<T>::e_none;

      #define synthesis_node_type_define(T0_, T1_, T2_, v_)                                                            \
      template <typename T, typename T0, typename T1, typename T2>                                                     \
      struct nodetype_T0oT1oT2<T,T0_,T1_,T2_> { static const typename expression_node<T>::node_type result; };         \
      template <typename T, typename T0, typename T1, typename T2>                                                     \
      const typename expression_node<T>::node_type nodetype_T0oT1oT2<T,T0_,T1_,T2_>::result = expression_node<T>:: v_; \

      synthesis_node_type_define(const T0&, const T1&, const T2&, e_vovov)
      synthesis_node_type_define(const T0&, const T1&, const T2 , e_vovoc)
      synthesis_node_type_define(const T0&, const T1 , const T2&, e_vocov)
      synthesis_node_type_define(const T0 , const T1&, const T2&, e_covov)
      synthesis_node_type_define(const T0 , const T1&, const T2 , e_covoc)
      synthesis_node_type_define(const T0 , const T1 , const T2 , e_none )
      synthesis_node_type_define(const T0 , const T1 , const T2&, e_none )
      synthesis_node_type_define(const T0&, const T1 , const T2 , e_none )
      synthesis_node_type_define(      T0&,       T1&,       T2&, e_none )
      #undef synthesis_node_type_define

      template <typename T, typename T0, typename T1, typename T2, typename T3>
      struct nodetype_T0oT1oT2oT3 { static const typename expression_node<T>::node_type result; };
      template <typename T, typename T0, typename T1, typename T2, typename T3>
      const typename expression_node<T>::node_type nodetype_T0oT1oT2oT3<T,T0,T1,T2,T3>::result = expression_node<T>::e_none;

      #define synthesis_node_type_define(T0_, T1_, T2_, T3_, v_)                                                              \
      template <typename T, typename T0, typename T1, typename T2, typename T3>                                               \
      struct nodetype_T0oT1oT2oT3<T,T0_,T1_,T2_,T3_> { static const typename expression_node<T>::node_type result; };         \
      template <typename T, typename T0, typename T1, typename T2, typename T3>                                               \
      const typename expression_node<T>::node_type nodetype_T0oT1oT2oT3<T,T0_,T1_,T2_,T3_>::result = expression_node<T>:: v_; \

      synthesis_node_type_define(const T0&, const T1&, const T2&, const T3&, e_vovovov)
      synthesis_node_type_define(const T0&, const T1&, const T2&, const T3 , e_vovovoc)
      synthesis_node_type_define(const T0&, const T1&, const T2 , const T3&, e_vovocov)
      synthesis_node_type_define(const T0&, const T1 , const T2&, const T3&, e_vocovov)
      synthesis_node_type_define(const T0 , const T1&, const T2&, const T3&, e_covovov)
      synthesis_node_type_define(const T0 , const T1&, const T2 , const T3&, e_covocov)
      synthesis_node_type_define(const T0&, const T1 , const T2&, const T3 , e_vocovoc)
      synthesis_node_type_define(const T0 , const T1&, const T2&, const T3 , e_covovoc)
      synthesis_node_type_define(const T0&, const T1 , const T2 , const T3&, e_vococov)
      synthesis_node_type_define(const T0 , const T1 , const T2 , const T3 , e_none   )
      synthesis_node_type_define(const T0 , const T1 , const T2 , const T3&, e_none   )
      synthesis_node_type_define(const T0 , const T1 , const T2&, const T3 , e_none   )
      synthesis_node_type_define(const T0 , const T1&, const T2 , const T3 , e_none   )
      synthesis_node_type_define(const T0&, const T1 , const T2 , const T3 , e_none   )
      synthesis_node_type_define(const T0 , const T1 , const T2&, const T3&, e_none   )
      synthesis_node_type_define(const T0&, const T1&, const T2 , const T3 , e_none   )
      #undef synthesis_node_type_define

      template <typename T, typename T0, typename T1>
      class T0oT1 exprtk_final : public expression_node<T>
      {
      public:

         typedef typename details::functor_t<T> functor_t;
         typedef typename functor_t::bfunc_t    bfunc_t;
         typedef T value_type;
         typedef T0oT1<T,T0,T1> node_type;

         T0oT1(T0 p0, T1 p1, const bfunc_t p2)
         : t0_(p0)
         , t1_(p1)
         , f_ (p2)
         {}

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            static const typename expression_node<T>::node_type result = nodetype_T0oT1<T,T0,T1>::result;
            return result;
         }

         inline operator_type operation() const exprtk_override
         {
            return e_default;
         }

         inline T value() const exprtk_override
         {
            return f_(t0_,t1_);
         }

         inline T0 t0() const
         {
            return t0_;
         }

         inline T1 t1() const
         {
            return t1_;
         }

         inline bfunc_t f() const
         {
            return f_;
         }

         template <typename Allocator>
         static inline expression_node<T>* allocate(Allocator& allocator,
                                                    T0 p0, T1 p1,
                                                    bfunc_t p2)
         {
            return allocator
                     .template allocate_type<node_type, T0, T1, bfunc_t&>
                        (p0, p1, p2);
         }

         inline std::string to_string() const exprtk_override{
            return "(T0oT1)";
         }
      private:

         T0oT1(const T0oT1<T,T0,T1>&) exprtk_delete;
         T0oT1<T,T0,T1>& operator=(const T0oT1<T,T0,T1>&) { return (*this); }

         T0 t0_;
         T1 t1_;
         const bfunc_t f_;
      };

      template <typename T, typename T0, typename T1, typename T2, typename ProcessMode>
      class T0oT1oT2 exprtk_final : public T0oT1oT2_base_node<T>
      {
      public:

         typedef typename details::functor_t<T> functor_t;
         typedef typename functor_t::bfunc_t    bfunc_t;
         typedef T value_type;
         typedef T0oT1oT2<T,T0,T1,T2,ProcessMode> node_type;
         typedef ProcessMode process_mode_t;

         T0oT1oT2(T0 p0, T1 p1, T2 p2, const bfunc_t p3, const bfunc_t p4)
         : t0_(p0)
         , t1_(p1)
         , t2_(p2)
         , f0_(p3)
         , f1_(p4)
         {}

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            static const typename expression_node<T>::node_type result = nodetype_T0oT1oT2<T,T0,T1,T2>::result;
            return result;
         }

         inline operator_type operation()
         {
            return e_default;
         }

         inline T value() const exprtk_override
         {
            return ProcessMode::process(t0_, t1_, t2_, f0_, f1_);
         }

         inline T0 t0() const
         {
            return t0_;
         }

         inline T1 t1() const
         {
            return t1_;
         }

         inline T2 t2() const
         {
            return t2_;
         }

         bfunc_t f0() const
         {
            return f0_;
         }

         bfunc_t f1() const
         {
            return f1_;
         }

         std::string type_id() const exprtk_override
         {
            return id();
         }

         static inline std::string id()
         {
            return process_mode_t::template id<T0,T1,T2>();
         }

         template <typename Allocator>
         static inline expression_node<T>* allocate(Allocator& allocator, T0 p0, T1 p1, T2 p2, bfunc_t p3, bfunc_t p4)
         {
            return allocator
                      .template allocate_type<node_type, T0, T1, T2, bfunc_t, bfunc_t>
                         (p0, p1, p2, p3, p4);
         }

         inline std::string to_string() const exprtk_override{
            return "(T0oT1oT2)";
         }
      private:

         T0oT1oT2(const node_type&) exprtk_delete;
         node_type& operator=(const node_type&) exprtk_delete;

         T0 t0_;
         T1 t1_;
         T2 t2_;
         const bfunc_t f0_;
         const bfunc_t f1_;
      };

      template <typename T, typename T0_, typename T1_, typename T2_, typename T3_, typename ProcessMode>
      class T0oT1oT2oT3 exprtk_final : public T0oT1oT2oT3_base_node<T>
      {
      public:

         typedef typename details::functor_t<T> functor_t;
         typedef typename functor_t::bfunc_t    bfunc_t;
         typedef T value_type;
         typedef T0_ T0;
         typedef T1_ T1;
         typedef T2_ T2;
         typedef T3_ T3;
         typedef T0oT1oT2oT3<T,T0,T1,T2,T3,ProcessMode> node_type;
         typedef ProcessMode process_mode_t;

         T0oT1oT2oT3(T0 p0, T1 p1, T2 p2, T3 p3, bfunc_t p4, bfunc_t p5, bfunc_t p6)
         : t0_(p0)
         , t1_(p1)
         , t2_(p2)
         , t3_(p3)
         , f0_(p4)
         , f1_(p5)
         , f2_(p6)
         {}

         inline T value() const exprtk_override
         {
            return ProcessMode::process(t0_, t1_, t2_, t3_, f0_, f1_, f2_);
         }

         inline T0 t0() const
         {
            return t0_;
         }

         inline T1 t1() const
         {
            return t1_;
         }

         inline T2 t2() const
         {
            return t2_;
         }

         inline T3 t3() const
         {
            return t3_;
         }

         inline bfunc_t f0() const
         {
            return f0_;
         }

         inline bfunc_t f1() const
         {
            return f1_;
         }

         inline bfunc_t f2() const
         {
            return f2_;
         }

         inline std::string type_id() const exprtk_override
         {
            return id();
         }

         static inline std::string id()
         {
            return process_mode_t::template id<T0, T1, T2, T3>();
         }

         template <typename Allocator>
         static inline expression_node<T>* allocate(Allocator& allocator,
                                                    T0 p0, T1 p1, T2 p2, T3 p3,
                                                    bfunc_t p4, bfunc_t p5, bfunc_t p6)
         {
            return allocator
                      .template allocate_type<node_type, T0, T1, T2, T3, bfunc_t, bfunc_t>
                         (p0, p1, p2, p3, p4, p5, p6);
         }

         inline std::string to_string() const exprtk_override{
            return "(T0oT1oT2oT3)";
         }
      private:

         T0oT1oT2oT3(const node_type&) exprtk_delete;
         node_type& operator=(const node_type&) exprtk_delete;

         T0 t0_;
         T1 t1_;
         T2 t2_;
         T3 t3_;
         const bfunc_t f0_;
         const bfunc_t f1_;
         const bfunc_t f2_;
      };

      template <typename T, typename T0, typename T1, typename T2>
      class T0oT1oT2_sf3 exprtk_final : public T0oT1oT2_base_node<T>
      {
      public:

         typedef typename details::functor_t<T> functor_t;
         typedef typename functor_t::tfunc_t    tfunc_t;
         typedef T value_type;
         typedef T0oT1oT2_sf3<T,T0,T1,T2> node_type;

         T0oT1oT2_sf3(T0 p0, T1 p1, T2 p2, const tfunc_t p3)
         : t0_(p0)
         , t1_(p1)
         , t2_(p2)
         , f_ (p3)
         {}

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            static const typename expression_node<T>::node_type result = nodetype_T0oT1oT2<T,T0,T1,T2>::result;
            return result;
         }

         inline operator_type operation() const exprtk_override
         {
            return e_default;
         }

         inline T value() const exprtk_override
         {
            return f_(t0_, t1_, t2_);
         }

         inline T0 t0() const
         {
            return t0_;
         }

         inline T1 t1() const
         {
            return t1_;
         }

         inline T2 t2() const
         {
            return t2_;
         }

         tfunc_t f() const
         {
            return f_;
         }

         std::string type_id() const
         {
            return id();
         }

         static inline std::string id()
         {
            return "sf3";
         }

         template <typename Allocator>
         static inline expression_node<T>* allocate(Allocator& allocator, T0 p0, T1 p1, T2 p2, tfunc_t p3)
         {
            return allocator
                     .template allocate_type<node_type, T0, T1, T2, tfunc_t>
                        (p0, p1, p2, p3);
         }

         inline std::string to_string() const exprtk_override{
            return "(T0oT1oT2_sf3)";
         }
      private:

         T0oT1oT2_sf3(const node_type&) exprtk_delete;
         node_type& operator=(const node_type&) exprtk_delete;

         T0 t0_;
         T1 t1_;
         T2 t2_;
         const tfunc_t f_;
      };

      template <typename T, typename T0, typename T1, typename T2>
      class sf3ext_type_node : public T0oT1oT2_base_node<T>
      {
      public:

         virtual ~sf3ext_type_node() {}

         virtual T0 t0() const = 0;

         virtual T1 t1() const = 0;

         virtual T2 t2() const = 0;
      };

      template <typename T, typename T0, typename T1, typename T2, typename SF3Operation>
      class T0oT1oT2_sf3ext exprtk_final : public sf3ext_type_node<T,T0,T1,T2>
      {
      public:

         typedef T value_type;
         typedef T0oT1oT2_sf3ext<T, T0, T1, T2, SF3Operation> node_type;

         T0oT1oT2_sf3ext(T0 p0, T1 p1, T2 p2)
         : t0_(p0)
         , t1_(p1)
         , t2_(p2)
         {}

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            static const typename expression_node<T>::node_type result = nodetype_T0oT1oT2<T,T0,T1,T2>::result;
            return result;
         }

         inline operator_type operation()
         {
            return e_default;
         }

         inline T value() const exprtk_override
         {
            return SF3Operation::process(t0_, t1_, t2_);
         }

         T0 t0() const exprtk_override
         {
            return t0_;
         }

         T1 t1() const exprtk_override
         {
            return t1_;
         }

         T2 t2() const exprtk_override
         {
            return t2_;
         }

         std::string type_id() const exprtk_override
         {
            return id();
         }

         static inline std::string id()
         {
            return SF3Operation::id();
         }

         template <typename Allocator>
         static inline expression_node<T>* allocate(Allocator& allocator, T0 p0, T1 p1, T2 p2)
         {
            return allocator
                     .template allocate_type<node_type, T0, T1, T2>
                        (p0, p1, p2);
         }

         inline std::string to_string() const exprtk_override{
            return "(T0oT1oT2_sf3ext)";
         }
      private:

         T0oT1oT2_sf3ext(const node_type&) exprtk_delete;
         node_type& operator=(const node_type&) exprtk_delete;

         T0 t0_;
         T1 t1_;
         T2 t2_;
      };

      template <typename T>
      inline bool is_sf3ext_node(const expression_node<T>* n)
      {
         switch (n->type())
         {
            case expression_node<T>::e_vovov : return true;
            case expression_node<T>::e_vovoc : return true;
            case expression_node<T>::e_vocov : return true;
            case expression_node<T>::e_covov : return true;
            case expression_node<T>::e_covoc : return true;
            default                          : return false;
         }
      }

      template <typename T, typename T0, typename T1, typename T2, typename T3>
      class T0oT1oT2oT3_sf4 exprtk_final : public T0oT1oT2_base_node<T>
      {
      public:

         typedef typename details::functor_t<T> functor_t;
         typedef typename functor_t::qfunc_t    qfunc_t;
         typedef T value_type;
         typedef T0oT1oT2oT3_sf4<T, T0, T1, T2, T3> node_type;

         T0oT1oT2oT3_sf4(T0 p0, T1 p1, T2 p2, T3 p3, const qfunc_t p4)
         : t0_(p0)
         , t1_(p1)
         , t2_(p2)
         , t3_(p3)
         , f_ (p4)
         {}

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            static const typename expression_node<T>::node_type result = nodetype_T0oT1oT2oT3<T,T0,T1,T2,T3>::result;
            return result;
         }

         inline operator_type operation() const exprtk_override
         {
            return e_default;
         }

         inline T value() const exprtk_override
         {
            return f_(t0_, t1_, t2_, t3_);
         }

         inline T0 t0() const
         {
            return t0_;
         }

         inline T1 t1() const
         {
            return t1_;
         }

         inline T2 t2() const
         {
            return t2_;
         }

         inline T3 t3() const
         {
            return t3_;
         }

         qfunc_t f() const
         {
            return f_;
         }

         std::string type_id() const
         {
            return id();
         }

         static inline std::string id()
         {
            return "sf4";
         }

         template <typename Allocator>
         static inline expression_node<T>* allocate(Allocator& allocator, T0 p0, T1 p1, T2 p2, T3 p3, qfunc_t p4)
         {
            return allocator
                     .template allocate_type<node_type, T0, T1, T2, T3, qfunc_t>
                        (p0, p1, p2, p3, p4);
         }

         inline std::string to_string() const exprtk_override{
            return "(T0oT1oT2oT3_sf4)";
         }
      private:

         T0oT1oT2oT3_sf4(const node_type&) exprtk_delete;
         node_type& operator=(const node_type&) exprtk_delete;

         T0 t0_;
         T1 t1_;
         T2 t2_;
         T3 t3_;
         const qfunc_t f_;
      };

      template <typename T, typename T0, typename T1, typename T2, typename T3, typename SF4Operation>
      class T0oT1oT2oT3_sf4ext exprtk_final : public T0oT1oT2oT3_base_node<T>
      {
      public:

         typedef T value_type;
         typedef T0oT1oT2oT3_sf4ext<T, T0, T1, T2, T3, SF4Operation> node_type;

         T0oT1oT2oT3_sf4ext(T0 p0, T1 p1, T2 p2, T3 p3)
         : t0_(p0)
         , t1_(p1)
         , t2_(p2)
         , t3_(p3)
         {}

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            static const typename expression_node<T>::node_type result = nodetype_T0oT1oT2oT3<T,T0,T1,T2,T3>::result;
            return result;
         }

         inline T value() const exprtk_override
         {
            return SF4Operation::process(t0_, t1_, t2_, t3_);
         }

         inline T0 t0() const
         {
            return t0_;
         }

         inline T1 t1() const
         {
            return t1_;
         }

         inline T2 t2() const
         {
            return t2_;
         }

         inline T3 t3() const
         {
            return t3_;
         }

         std::string type_id() const exprtk_override
         {
            return id();
         }

         static inline std::string id()
         {
            return SF4Operation::id();
         }

         template <typename Allocator>
         static inline expression_node<T>* allocate(Allocator& allocator, T0 p0, T1 p1, T2 p2, T3 p3)
         {
            return allocator
                     .template allocate_type<node_type, T0, T1, T2, T3>
                        (p0, p1, p2, p3);
         }

         inline std::string to_string() const exprtk_override{
            return "(T0oT1oT2oT3_sf4ext)";
         }
      private:

         T0oT1oT2oT3_sf4ext(const node_type&) exprtk_delete;
         node_type& operator=(const node_type&) exprtk_delete;

         T0 t0_;
         T1 t1_;
         T2 t2_;
         T3 t3_;
      };

      template <typename T>
      inline bool is_sf4ext_node(const expression_node<T>* n)
      {
         switch (n->type())
         {
            case expression_node<T>::e_vovovov : return true;
            case expression_node<T>::e_vovovoc : return true;
            case expression_node<T>::e_vovocov : return true;
            case expression_node<T>::e_vocovov : return true;
            case expression_node<T>::e_covovov : return true;
            case expression_node<T>::e_covocov : return true;
            case expression_node<T>::e_vocovoc : return true;
            case expression_node<T>::e_covovoc : return true;
            case expression_node<T>::e_vococov : return true;
            default                            : return false;
         }
      }

      template <typename T, typename T0, typename T1>
      struct T0oT1_define
      {
         typedef details::T0oT1<T, T0, T1> type0;
      };

      template <typename T, typename T0, typename T1, typename T2>
      struct T0oT1oT2_define
      {
         typedef details::T0oT1oT2<T, T0, T1, T2, typename T0oT1oT2process<T>::mode0> type0;
         typedef details::T0oT1oT2<T, T0, T1, T2, typename T0oT1oT2process<T>::mode1> type1;
         typedef details::T0oT1oT2_sf3<T, T0, T1, T2> sf3_type;
         typedef details::sf3ext_type_node<T, T0, T1, T2> sf3_type_node;
      };

      template <typename T, typename T0, typename T1, typename T2, typename T3>
      struct T0oT1oT2oT3_define
      {
         typedef details::T0oT1oT2oT3<T, T0, T1, T2, T3, typename T0oT1oT20T3process<T>::mode0> type0;
         typedef details::T0oT1oT2oT3<T, T0, T1, T2, T3, typename T0oT1oT20T3process<T>::mode1> type1;
         typedef details::T0oT1oT2oT3<T, T0, T1, T2, T3, typename T0oT1oT20T3process<T>::mode2> type2;
         typedef details::T0oT1oT2oT3<T, T0, T1, T2, T3, typename T0oT1oT20T3process<T>::mode3> type3;
         typedef details::T0oT1oT2oT3<T, T0, T1, T2, T3, typename T0oT1oT20T3process<T>::mode4> type4;
         typedef details::T0oT1oT2oT3_sf4<T, T0, T1, T2, T3> sf4_type;
      };

      template <typename T, typename Operation>
      class vov_node exprtk_final : public vov_base_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef Operation operation_t;

         // variable op variable node
         explicit vov_node(const T& var0, const T& var1)
         : v0_(var0)
         , v1_(var1)
         {}

         inline T value() const exprtk_override
         {
            return Operation::process(v0_,v1_);
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return Operation::type();
         }

         inline operator_type operation() const exprtk_override
         {
            return Operation::operation();
         }

         inline const T& v0() const exprtk_override
         {
            return v0_;
         }

         inline const T& v1() const exprtk_override
         {
            return v1_;
         }

         inline std::string to_string() const exprtk_override{
            return "(vov_node)";
         }
      protected:

         const T& v0_;
         const T& v1_;

      private:

         vov_node(const vov_node<T,Operation>&) exprtk_delete;
         vov_node<T,Operation>& operator=(const vov_node<T,Operation>&) exprtk_delete;
      };

      template <typename T, typename Operation>
      class cov_node exprtk_final : public cov_base_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef Operation operation_t;

         // constant op variable node
         explicit cov_node(const T& const_var, const T& var)
         : c_(const_var)
         , v_(var)
         {}

         inline T value() const exprtk_override
         {
            return Operation::process(c_,v_);
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return Operation::type();
         }

         inline operator_type operation() const exprtk_override
         {
            return Operation::operation();
         }

         inline const T c() const exprtk_override
         {
            return c_;
         }

         inline const T& v() const exprtk_override
         {
            return v_;
         }

         inline std::string to_string() const exprtk_override{
            return "(cov_node)";
         }
      protected:

         const T  c_;
         const T& v_;

      private:

         cov_node(const cov_node<T,Operation>&) exprtk_delete;
         cov_node<T,Operation>& operator=(const cov_node<T,Operation>&) exprtk_delete;
      };

      template <typename T, typename Operation>
      class voc_node exprtk_final : public voc_base_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef Operation operation_t;

         // variable op constant node
         explicit voc_node(const T& var, const T& const_var)
         : v_(var)
         , c_(const_var)
         {}

         inline T value() const exprtk_override
         {
            return Operation::process(v_,c_);
         }

         inline operator_type operation() const exprtk_override
         {
            return Operation::operation();
         }

         inline const T c() const exprtk_override
         {
            return c_;
         }

         inline const T& v() const exprtk_override
         {
            return v_;
         }

         inline std::string to_string() const exprtk_override{
            return "(voc_node)";
         }
      protected:

         const T& v_;
         const T  c_;

      private:

         voc_node(const voc_node<T,Operation>&) exprtk_delete;
         voc_node<T,Operation>& operator=(const voc_node<T,Operation>&) exprtk_delete;
      };

      template <typename T, typename Operation>
      class vob_node exprtk_final : public vob_base_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef std::pair<expression_ptr,bool> branch_t;
         typedef Operation operation_t;

         // variable op constant node
         explicit vob_node(const T& var, const expression_ptr branch)
         : v_(var)
         {
            construct_branch_pair(branch_, branch);
         }

         inline T value() const exprtk_override
         {
            assert(branch_.first);
            return Operation::process(v_,branch_.first->value());
         }

         inline const T& v() const exprtk_override
         {
            return v_;
         }

         inline expression_node<T>* branch(const std::size_t&) const exprtk_override
         {
            return branch_.first;
         }

         void collect_nodes(typename expression_node<T>::noderef_list_t& node_delete_list) exprtk_override
         {
            expression_node<T>::ndb_t::template collect(branch_, node_delete_list);
         }

         std::size_t node_depth() const exprtk_override
         {
            return expression_node<T>::ndb_t::compute_node_depth(branch_);
         }

         inline std::string to_string() const exprtk_override{
            return "(vob_node)";
         }
      private:

         vob_node(const vob_node<T,Operation>&) exprtk_delete;
         vob_node<T,Operation>& operator=(const vob_node<T,Operation>&) exprtk_delete;

         const T& v_;
         branch_t branch_;
      };

      template <typename T, typename Operation>
      class bov_node exprtk_final : public bov_base_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef std::pair<expression_ptr,bool> branch_t;
         typedef Operation operation_t;

         // variable op constant node
         explicit bov_node(const expression_ptr branch, const T& var)
         : v_(var)
         {
            construct_branch_pair(branch_, branch);
         }

         inline T value() const exprtk_override
         {
            assert(branch_.first);
            return Operation::process(branch_.first->value(),v_);
         }

         inline const T& v() const exprtk_override
         {
            return v_;
         }

         inline expression_node<T>* branch(const std::size_t&) const exprtk_override
         {
            return branch_.first;
         }

         void collect_nodes(typename expression_node<T>::noderef_list_t& node_delete_list) exprtk_override
         {
            expression_node<T>::ndb_t::template collect(branch_, node_delete_list);
         }

         std::size_t node_depth() const exprtk_override
         {
            return expression_node<T>::ndb_t::compute_node_depth(branch_);
         }

         inline std::string to_string() const exprtk_override{
            return "(bov_node)";
         }
      private:

         bov_node(const bov_node<T,Operation>&) exprtk_delete;
         bov_node<T,Operation>& operator=(const bov_node<T,Operation>&) exprtk_delete;

         const T& v_;
         branch_t branch_;
      };

      template <typename T, typename Operation>
      class cob_node exprtk_final : public cob_base_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef std::pair<expression_ptr,bool> branch_t;
         typedef Operation operation_t;

         // variable op constant node
         explicit cob_node(const T const_var, const expression_ptr branch)
         : c_(const_var)
         {
            construct_branch_pair(branch_, branch);
         }

         inline T value() const exprtk_override
         {
            assert(branch_.first);
            return Operation::process(c_,branch_.first->value());
         }

         inline operator_type operation() const exprtk_override
         {
            return Operation::operation();
         }

         inline const T c() const exprtk_override
         {
            return c_;
         }

         inline void set_c(const T new_c) exprtk_override
         {
            (*const_cast<T*>(&c_)) = new_c;
         }

         inline expression_node<T>* branch(const std::size_t&) const exprtk_override
         {
            return branch_.first;
         }

         inline expression_node<T>* move_branch(const std::size_t&) exprtk_override
         {
            branch_.second = false;
            return branch_.first;
         }

         void collect_nodes(typename expression_node<T>::noderef_list_t& node_delete_list) exprtk_override
         {
            expression_node<T>::ndb_t::template collect(branch_, node_delete_list);
         }

         std::size_t node_depth() const exprtk_override
         {
            return expression_node<T>::ndb_t::compute_node_depth(branch_);
         }

         inline std::string to_string() const exprtk_override{
            return "(cob_node)";
         }
      private:

         cob_node(const cob_node<T,Operation>&) exprtk_delete;
         cob_node<T,Operation>& operator=(const cob_node<T,Operation>&) exprtk_delete;

         const T  c_;
         branch_t branch_;
      };

      template <typename T, typename Operation>
      class boc_node exprtk_final : public boc_base_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef std::pair<expression_ptr,bool> branch_t;
         typedef Operation operation_t;

         // variable op constant node
         explicit boc_node(const expression_ptr branch, const T const_var)
         : c_(const_var)
         {
            construct_branch_pair(branch_, branch);
         }

         inline T value() const exprtk_override
         {
            assert(branch_.first);
            return Operation::process(branch_.first->value(),c_);
         }

         inline operator_type operation() const exprtk_override
         {
            return Operation::operation();
         }

         inline const T c() const exprtk_override
         {
            return c_;
         }

         inline void set_c(const T new_c) exprtk_override
         {
            (*const_cast<T*>(&c_)) = new_c;
         }

         inline expression_node<T>* branch(const std::size_t&) const exprtk_override
         {
            return branch_.first;
         }

         inline expression_node<T>* move_branch(const std::size_t&) exprtk_override
         {
            branch_.second = false;
            return branch_.first;
         }

         void collect_nodes(typename expression_node<T>::noderef_list_t& node_delete_list) exprtk_override
         {
            expression_node<T>::ndb_t::template collect(branch_, node_delete_list);
         }

         std::size_t node_depth() const exprtk_override
         {
            return expression_node<T>::ndb_t::compute_node_depth(branch_);
         }

         inline std::string to_string() const exprtk_override{
            return "(boc_node)";
         }
      private:

         boc_node(const boc_node<T,Operation>&) exprtk_delete;
         boc_node<T,Operation>& operator=(const boc_node<T,Operation>&) exprtk_delete;

         const T  c_;
         branch_t branch_;
      };

      template <typename T, typename SType0, typename SType1, typename Operation>
      class sos_node exprtk_final : public sos_base_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef Operation operation_t;

         // string op string node
         explicit sos_node(SType0 p0, SType1 p1)
         : s0_(p0)
         , s1_(p1)
         {}

         inline T value() const exprtk_override
         {
            return Operation::process(s0_,s1_);
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return Operation::type();
         }

         inline operator_type operation() const exprtk_override
         {
            return Operation::operation();
         }

         inline std::string& s0()
         {
            return s0_;
         }

         inline std::string& s1()
         {
            return s1_;
         }

         inline std::string to_string() const exprtk_override{
            return "(sos_node)";
         }
      protected:

         SType0 s0_;
         SType1 s1_;

      private:

         sos_node(const sos_node<T,SType0,SType1,Operation>&) exprtk_delete;
         sos_node<T,SType0,SType1,Operation>& operator=(const sos_node<T,SType0,SType1,Operation>&) exprtk_delete;
      };

      template <typename T, typename SType0, typename SType1, typename RangePack, typename Operation>
      class str_xrox_node exprtk_final : public sos_base_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef Operation operation_t;
         typedef str_xrox_node<T,SType0,SType1,RangePack,Operation> node_type;

         // string-range op string node
         explicit str_xrox_node(SType0 p0, SType1 p1, RangePack rp0)
         : s0_ (p0 )
         , s1_ (p1 )
         , rp0_(rp0)
         {}

        ~str_xrox_node()
         {
            rp0_.free();
         }

         inline T value() const exprtk_override
         {
            std::size_t r0 = 0;
            std::size_t r1 = 0;

            if (rp0_(r0, r1, s0_.size()))
               return Operation::process(s0_.substr(r0, (r1 - r0) + 1), s1_);
            else
               return T(0);
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return Operation::type();
         }

         inline operator_type operation() const exprtk_override
         {
            return Operation::operation();
         }

         inline std::string& s0()
         {
            return s0_;
         }

         inline std::string& s1()
         {
            return s1_;
         }

         inline std::string to_string() const exprtk_override{
            return "(str_xrox_node)";
         }
      protected:

         SType0    s0_;
         SType1    s1_;
         RangePack rp0_;

      private:

         str_xrox_node(const node_type&) exprtk_delete;
         node_type& operator=(const node_type&) exprtk_delete;
      };

      template <typename T, typename SType0, typename SType1, typename RangePack, typename Operation>
      class str_xoxr_node exprtk_final : public sos_base_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef Operation operation_t;
         typedef str_xoxr_node<T,SType0,SType1,RangePack,Operation> node_type;

         // string op string range node
         explicit str_xoxr_node(SType0 p0, SType1 p1, RangePack rp1)
         : s0_ (p0 )
         , s1_ (p1 )
         , rp1_(rp1)
         {}

        ~str_xoxr_node()
         {
            rp1_.free();
         }

         inline T value() const exprtk_override
         {
            std::size_t r0 = 0;
            std::size_t r1 = 0;

            if (rp1_(r0, r1, s1_.size()))
               return Operation::process(s0_, s1_.substr(r0, (r1 - r0) + 1));
            else
               return T(0);
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return Operation::type();
         }

         inline operator_type operation() const exprtk_override
         {
            return Operation::operation();
         }

         inline std::string& s0()
         {
            return s0_;
         }

         inline std::string& s1()
         {
            return s1_;
         }

         inline std::string to_string() const exprtk_override{
            return "(str_xoxr_node)";
         }
      protected:

         SType0    s0_;
         SType1    s1_;
         RangePack rp1_;

      private:

         str_xoxr_node(const node_type&) exprtk_delete;
         node_type& operator=(const node_type&) exprtk_delete;
      };

      template <typename T, typename SType0, typename SType1, typename RangePack, typename Operation>
      class str_xroxr_node exprtk_final : public sos_base_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef Operation operation_t;
         typedef str_xroxr_node<T,SType0,SType1,RangePack,Operation> node_type;

         // string-range op string-range node
         explicit str_xroxr_node(SType0 p0, SType1 p1, RangePack rp0, RangePack rp1)
         : s0_ (p0 )
         , s1_ (p1 )
         , rp0_(rp0)
         , rp1_(rp1)
         {}

        ~str_xroxr_node()
         {
            rp0_.free();
            rp1_.free();
         }

         inline T value() const exprtk_override
         {
            std::size_t r0_0 = 0;
            std::size_t r0_1 = 0;
            std::size_t r1_0 = 0;
            std::size_t r1_1 = 0;

            if (
                 rp0_(r0_0, r1_0, s0_.size()) &&
                 rp1_(r0_1, r1_1, s1_.size())
               )
            {
               return Operation::process(
                                          s0_.substr(r0_0, (r1_0 - r0_0) + 1),
                                          s1_.substr(r0_1, (r1_1 - r0_1) + 1)
                                        );
            }
            else
               return T(0);
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return Operation::type();
         }

         inline operator_type operation() const exprtk_override
         {
            return Operation::operation();
         }

         inline std::string& s0()
         {
            return s0_;
         }

         inline std::string& s1()
         {
            return s1_;
         }

         inline std::string to_string() const exprtk_override{
            return "(str_xroxr_node)";
         }
      protected:

         SType0    s0_;
         SType1    s1_;
         RangePack rp0_;
         RangePack rp1_;

      private:

         str_xroxr_node(const node_type&) exprtk_delete;
         node_type& operator=(const node_type&) exprtk_delete;
      };

      template <typename T, typename Operation>
      class str_sogens_node exprtk_final : public binary_node<T>
      {
      public:

         typedef expression_node <T>* expression_ptr;
         typedef string_base_node<T>* str_base_ptr;
         typedef range_pack      <T>  range_t;
         typedef range_t*             range_ptr;
         typedef range_interface <T>  irange_t;
         typedef irange_t*            irange_ptr;

         using binary_node<T>::branch;

         str_sogens_node(const operator_type& opr,
                         expression_ptr branch0,
                         expression_ptr branch1)
         : binary_node<T>(opr, branch0, branch1)
         , str0_base_ptr_ (0)
         , str1_base_ptr_ (0)
         , str0_range_ptr_(0)
         , str1_range_ptr_(0)
         {
            if (is_generally_string_node(branch(0)))
            {
               str0_base_ptr_ = dynamic_cast<str_base_ptr>(branch(0));

               if (0 == str0_base_ptr_)
                  return;

               irange_ptr range = dynamic_cast<irange_ptr>(branch(0));

               if (0 == range)
                  return;

               str0_range_ptr_ = &(range->range_ref());
            }

            if (is_generally_string_node(branch(1)))
            {
               str1_base_ptr_ = dynamic_cast<str_base_ptr>(branch(1));

               if (0 == str1_base_ptr_)
                  return;

               irange_ptr range = dynamic_cast<irange_ptr>(branch(1));

               if (0 == range)
                  return;

               str1_range_ptr_ = &(range->range_ref());
            }
         }

         inline T value() const exprtk_override
         {
            if (
                 str0_base_ptr_  &&
                 str1_base_ptr_  &&
                 str0_range_ptr_ &&
                 str1_range_ptr_
               )
            {
               branch(0)->value();
               branch(1)->value();

               std::size_t str0_r0 = 0;
               std::size_t str0_r1 = 0;

               std::size_t str1_r0 = 0;
               std::size_t str1_r1 = 0;

               const range_t& range0 = (*str0_range_ptr_);
               const range_t& range1 = (*str1_range_ptr_);

               if (
                    range0(str0_r0, str0_r1, str0_base_ptr_->size()) &&
                    range1(str1_r0, str1_r1, str1_base_ptr_->size())
                  )
               {
                  return Operation::process(
                                             str0_base_ptr_->str().substr(str0_r0,(str0_r1 - str0_r0) + 1),
                                             str1_base_ptr_->str().substr(str1_r0,(str1_r1 - str1_r0) + 1)
                                           );
               }
            }

            return std::numeric_limits<T>::quiet_NaN();
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return Operation::type();
         }

         inline std::string to_string() const exprtk_override{
            return "(str_sogens_node)";
         }
      private:

         str_sogens_node(const str_sogens_node<T,Operation>&) exprtk_delete;
         str_sogens_node<T,Operation>& operator=(const str_sogens_node<T,Operation>&) exprtk_delete;

         str_base_ptr str0_base_ptr_;
         str_base_ptr str1_base_ptr_;
         range_ptr    str0_range_ptr_;
         range_ptr    str1_range_ptr_;
      };

      template <typename T, typename SType0, typename SType1, typename SType2, typename Operation>
      class sosos_node exprtk_final : public sosos_base_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef Operation operation_t;
         typedef sosos_node<T, SType0, SType1, SType2, Operation> node_type;

         // variable op variable node
         explicit sosos_node(SType0 p0, SType1 p1, SType2 p2)
         : s0_(p0)
         , s1_(p1)
         , s2_(p2)
         {}

         inline T value() const exprtk_override
         {
            return Operation::process(s0_, s1_, s2_);
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return Operation::type();
         }

         inline operator_type operation() const exprtk_override
         {
            return Operation::operation();
         }

         inline std::string& s0()
         {
            return s0_;
         }

         inline std::string& s1()
         {
            return s1_;
         }

         inline std::string& s2()
         {
            return s2_;
         }

         inline std::string to_string() const exprtk_override{
            return "(sosos_node)";
         }
      protected:

         SType0 s0_;
         SType1 s1_;
         SType2 s2_;

      private:

         sosos_node(const node_type&) exprtk_delete;
         node_type& operator=(const node_type&) exprtk_delete;
      };

      template <typename T, typename PowOp>
      class ipow_node exprtk_final: public expression_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef PowOp operation_t;

         explicit ipow_node(const T& v)
         : v_(v)
         {}

         inline T value() const exprtk_override
         {
            return PowOp::result(v_);
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_ipow;
         }

         inline std::string to_string() const exprtk_override{
            return "(ipow_node)";
         }
      private:

         ipow_node(const ipow_node<T,PowOp>&) exprtk_delete;
         ipow_node<T,PowOp>& operator=(const ipow_node<T,PowOp>&) exprtk_delete;

         const T& v_;
      };

      template <typename T, typename PowOp>
      class bipow_node exprtk_final : public expression_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef std::pair<expression_ptr, bool> branch_t;
         typedef PowOp operation_t;

         explicit bipow_node(expression_ptr branch)
         {
            construct_branch_pair(branch_, branch);
         }

         inline T value() const exprtk_override
         {
            assert(branch_.first);
            return PowOp::result(branch_.first->value());
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_ipow;
         }

         void collect_nodes(typename expression_node<T>::noderef_list_t& node_delete_list) exprtk_override
         {
            expression_node<T>::ndb_t::collect(branch_, node_delete_list);
         }

         std::size_t node_depth() const exprtk_override
         {
            return expression_node<T>::ndb_t::compute_node_depth(branch_);
         }

         inline std::string to_string() const exprtk_override{
            return "(bipow_node)";
         }
      private:

         bipow_node(const bipow_node<T,PowOp>&) exprtk_delete;
         bipow_node<T,PowOp>& operator=(const bipow_node<T,PowOp>&) exprtk_delete;

         branch_t branch_;
      };

      template <typename T, typename PowOp>
      class ipowinv_node exprtk_final : public expression_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef PowOp operation_t;

         explicit ipowinv_node(const T& v)
         : v_(v)
         {}

         inline T value() const exprtk_override
         {
            return (T(1) / PowOp::result(v_));
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_ipowinv;
         }

         inline std::string to_string() const exprtk_override{
            return "(ipowinv_node)";
         }
      private:

         ipowinv_node(const ipowinv_node<T,PowOp>&) exprtk_delete;
         ipowinv_node<T,PowOp>& operator=(const ipowinv_node<T,PowOp>&) exprtk_delete;

         const T& v_;
      };

      template <typename T, typename PowOp>
      class bipowninv_node exprtk_final : public expression_node<T>
      {
      public:

         typedef expression_node<T>* expression_ptr;
         typedef std::pair<expression_ptr, bool> branch_t;
         typedef PowOp operation_t;

         explicit bipowninv_node(expression_ptr branch)
         {
            construct_branch_pair(branch_, branch);
         }

         inline T value() const exprtk_override
         {
            assert(branch_.first);
            return (T(1) / PowOp::result(branch_.first->value()));
         }

         inline typename expression_node<T>::node_type type() const exprtk_override
         {
            return expression_node<T>::e_ipowinv;
         }

         void collect_nodes(typename expression_node<T>::noderef_list_t& node_delete_list) exprtk_override
         {
            expression_node<T>::ndb_t::template collect(branch_, node_delete_list);
         }

         std::size_t node_depth() const exprtk_override
         {
            return expression_node<T>::ndb_t::compute_node_depth(branch_);
         }

         inline std::string to_string() const exprtk_override{
            return "(bipowninv_node)";
         }
      private:

         bipowninv_node(const bipowninv_node<T,PowOp>&) exprtk_delete;
         bipowninv_node<T,PowOp>& operator=(const bipowninv_node<T,PowOp>&) exprtk_delete;

         branch_t branch_;
      };

      template <typename T>
      inline bool is_vov_node(const expression_node<T>* node)
      {
         return (0 != dynamic_cast<const vov_base_node<T>*>(node));
      }

      template <typename T>
      inline bool is_cov_node(const expression_node<T>* node)
      {
         return (0 != dynamic_cast<const cov_base_node<T>*>(node));
      }

      template <typename T>
      inline bool is_voc_node(const expression_node<T>* node)
      {
         return (0 != dynamic_cast<const voc_base_node<T>*>(node));
      }

      template <typename T>
      inline bool is_cob_node(const expression_node<T>* node)
      {
         return (0 != dynamic_cast<const cob_base_node<T>*>(node));
      }

      template <typename T>
      inline bool is_boc_node(const expression_node<T>* node)
      {
         return (0 != dynamic_cast<const boc_base_node<T>*>(node));
      }

      template <typename T>
      inline bool is_t0ot1ot2_node(const expression_node<T>* node)
      {
         return (0 != dynamic_cast<const T0oT1oT2_base_node<T>*>(node));
      }

      template <typename T>
      inline bool is_t0ot1ot2ot3_node(const expression_node<T>* node)
      {
         return (0 != dynamic_cast<const T0oT1oT2oT3_base_node<T>*>(node));
      }

      template <typename T>
      inline bool is_uv_node(const expression_node<T>* node)
      {
         return (0 != dynamic_cast<const uv_base_node<T>*>(node));
      }

      template <typename T>
      inline bool is_string_node(const expression_node<T>* node)
      {
         return node && (expression_node<T>::e_stringvar == node->type());
      }

      template <typename T>
      inline bool is_string_range_node(const expression_node<T>* node)
      {
         return node && (expression_node<T>::e_stringvarrng == node->type());
      }

      template <typename T>
      inline bool is_const_string_node(const expression_node<T>* node)
      {
         return node && (expression_node<T>::e_stringconst == node->type());
      }

      template <typename T>
      inline bool is_const_string_range_node(const expression_node<T>* node)
      {
         return node && (expression_node<T>::e_cstringvarrng == node->type());
      }

      template <typename T>
      inline bool is_string_assignment_node(const expression_node<T>* node)
      {
         return node && (expression_node<T>::e_strass == node->type());
      }

      template <typename T>
      inline bool is_string_concat_node(const expression_node<T>* node)
      {
         return node && (expression_node<T>::e_strconcat == node->type());
      }

      template <typename T>
      inline bool is_string_function_node(const expression_node<T>* node)
      {
         return node && (expression_node<T>::e_strfunction == node->type());
      }

      template <typename T>
      inline bool is_string_condition_node(const expression_node<T>* node)
      {
         return node && (expression_node<T>::e_strcondition == node->type());
      }

      template <typename T>
      inline bool is_string_ccondition_node(const expression_node<T>* node)
      {
         return node && (expression_node<T>::e_strccondition == node->type());
      }

      template <typename T>
      inline bool is_string_vararg_node(const expression_node<T>* node)
      {
         return node && (expression_node<T>::e_stringvararg == node->type());
      }

      template <typename T>
      inline bool is_genricstring_range_node(const expression_node<T>* node)
      {
         return node && (expression_node<T>::e_strgenrange == node->type());
      }

      template <typename T>
      inline bool is_generally_string_node(const expression_node<T>* node)
      {
         if (node)
         {
            switch (node->type())
            {
               case expression_node<T>::e_stringvar     :
               case expression_node<T>::e_stringconst   :
               case expression_node<T>::e_stringvarrng  :
               case expression_node<T>::e_cstringvarrng :
               case expression_node<T>::e_strgenrange   :
               case expression_node<T>::e_strass        :
               case expression_node<T>::e_strconcat     :
               case expression_node<T>::e_strfunction   :
               case expression_node<T>::e_strcondition  :
               case expression_node<T>::e_strccondition :
               case expression_node<T>::e_stringvararg  : return true;
               default                                  : return false;
            }
         }

         return false;
      }
    }
}

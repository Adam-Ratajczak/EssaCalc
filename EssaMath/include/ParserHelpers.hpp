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

#include "include/Generator.hpp"

namespace Essa::Math{
   namespace lexer{
      class parser_helper
      {
      public:

         typedef token     token_t;
         typedef generator generator_t;

         inline bool init(const std::string& str)
         {
            if (!lexer_.process(str))
            {
               return false;
            }

            lexer_.begin();

            next_token();

            return true;
         }

         inline generator_t& lexer()
         {
            return lexer_;
         }

         inline const generator_t& lexer() const
         {
            return lexer_;
         }

         inline void store_token()
         {
            lexer_.store();
            store_current_token_ = current_token_;
         }

         inline void restore_token()
         {
            lexer_.restore();
            current_token_ = store_current_token_;
         }

         inline void next_token()
         {
            current_token_ = lexer_.next_token();
         }

         inline const token_t& current_token() const
         {
            return current_token_;
         }

         enum token_advance_mode
         {
            e_hold    = 0,
            e_advance = 1
         };

         inline void advance_token(const token_advance_mode mode)
         {
            if (e_advance == mode)
            {
               next_token();
            }
         }

         inline bool token_is(const token_t::token_type& ttype, const token_advance_mode mode = e_advance)
         {
            if (current_token().type != ttype)
            {
               return false;
            }

            advance_token(mode);

            return true;
         }

         inline bool token_is(const token_t::token_type& ttype,
                              const std::string& value,
                              const token_advance_mode mode = e_advance)
         {
            if (
                 (current_token().type != ttype) ||
                 !Essa::Math::details::imatch(value,current_token().value)
               )
            {
               return false;
            }

            advance_token(mode);

            return true;
         }

         inline bool peek_token_is(const token_t::token_type& ttype)
         {
            return (lexer_.peek_next_token().type == ttype);
         }

         inline bool peek_token_is(const std::string& s)
         {
            return (Essa::Math::details::imatch(lexer_.peek_next_token().value,s));
         }

      private:

         generator_t lexer_;
         token_t     current_token_;
         token_t     store_current_token_;
      };
   }

   template <typename T>
   class vector_view
   {
   public:

      typedef T* data_ptr_t;

      vector_view(data_ptr_t data, const std::size_t& size)
      : size_(size)
      , data_(data)
      , data_ref_(0)
      {}

      vector_view(const vector_view<T>& vv)
      : size_(vv.size_)
      , data_(vv.data_)
      , data_ref_(0)
      {}

      inline void rebase(data_ptr_t data)
      {
         data_ = data;

         if (!data_ref_.empty())
         {
            for (std::size_t i = 0; i < data_ref_.size(); ++i)
            {
               (*data_ref_[i]) = data;
            }
         }
      }

      inline data_ptr_t data() const
      {
         return data_;
      }

      inline std::size_t size() const
      {
         return size_;
      }

      inline const T& operator[](const std::size_t index) const
      {
         return data_[index];
      }

      inline T& operator[](const std::size_t index)
      {
         return data_[index];
      }

      void set_ref(data_ptr_t* data_ref)
      {
         data_ref_.push_back(data_ref);
      }

   private:

      const std::size_t size_;
      data_ptr_t  data_;
      std::vector<data_ptr_t*> data_ref_;
   };

   template <typename T>
   inline vector_view<T> make_vector_view(T* data,
                                          const std::size_t size, const std::size_t offset = 0)
   {
      return vector_view<T>(data + offset, size);
   }

   template <typename T>
   inline vector_view<T> make_vector_view(std::vector<T>& v,
                                          const std::size_t size, const std::size_t offset = 0)
   {
      return vector_view<T>(v.data() + offset, size);
   }

   template <typename T> class results_context;

   template <typename T>
   struct type_store
   {
      enum store_type
      {
         e_unknown,
         e_scalar ,
         e_vector ,
         e_string
      };

      type_store()
      : data(0)
      , size(0)
      , type(e_unknown)
      {}

      union
      {
         void* data;
         T*    vec_data;
      };

      std::size_t size;
      store_type  type;

      class parameter_list
      {
      public:

         explicit parameter_list(std::vector<type_store>& pl)
         : parameter_list_(pl)
         {}

         inline bool empty() const
         {
            return parameter_list_.empty();
         }

         inline std::size_t size() const
         {
            return parameter_list_.size();
         }

         inline type_store& operator[](const std::size_t& index)
         {
            return parameter_list_[index];
         }

         inline const type_store& operator[](const std::size_t& index) const
         {
            return parameter_list_[index];
         }

         inline type_store& front()
         {
            return parameter_list_[0];
         }

         inline const type_store& front() const
         {
            return parameter_list_[0];
         }

         inline type_store& back()
         {
            return parameter_list_.back();
         }

         inline const type_store& back() const
         {
            return parameter_list_.back();
         }

      private:

         std::vector<type_store>& parameter_list_;

         friend class results_context<T>;
      };

      template <typename ViewType>
      struct type_view
      {
         typedef type_store<T> type_store_t;
         typedef ViewType      value_t;

         explicit type_view(type_store_t& ts)
         : ts_(ts)
         , data_(reinterpret_cast<value_t*>(ts_.data))
         {}

         explicit type_view(const type_store_t& ts)
         : ts_(const_cast<type_store_t&>(ts))
         , data_(reinterpret_cast<value_t*>(ts_.data))
         {}

         inline std::size_t size() const
         {
            return ts_.size;
         }

         inline value_t& operator[](const std::size_t& i)
         {
            return data_[i];
         }

         inline const value_t& operator[](const std::size_t& i) const
         {
            return data_[i];
         }

         inline const value_t* begin() const { return data_; }
         inline       value_t* begin()       { return data_; }

         inline const value_t* end() const
         {
            return static_cast<value_t*>(data_ + ts_.size);
         }

         inline value_t* end()
         {
            return static_cast<value_t*>(data_ + ts_.size);
         }

         type_store_t& ts_;
         value_t* data_;
      };

      typedef type_view<T>    vector_view;
      typedef type_view<char> string_view;

      struct scalar_view
      {
         typedef type_store<T> type_store_t;
         typedef T value_t;

         explicit scalar_view(type_store_t& ts)
         : v_(*reinterpret_cast<value_t*>(ts.data))
         {}

         explicit scalar_view(const type_store_t& ts)
         : v_(*reinterpret_cast<value_t*>(const_cast<type_store_t&>(ts).data))
         {}

         inline value_t& operator() ()
         {
            return v_;
         }

         inline const value_t& operator() () const
         {
            return v_;
         }

         template <typename IntType>
         inline bool to_int(IntType& i) const
         {
            if (!Essa::Math::details::numeric::is_integer(v_))
               return false;

            i = static_cast<IntType>(v_);

            return true;
         }

         template <typename UIntType>
         inline bool to_uint(UIntType& u) const
         {
            if (v_ < T(0))
               return false;
            else if (!Essa::Math::details::numeric::is_integer(v_))
               return false;

            u = static_cast<UIntType>(v_);

            return true;
         }

         T& v_;
      };
   };

   template <typename StringView>
   inline std::string to_str(const StringView& view)
   {
      return std::string(view.begin(),view.size());
   }

   namespace details
   {
      template <typename T> class return_node;
      template <typename T> class return_envelope_node;
   }

   template <typename T>
   class results_context
   {
   public:

      typedef type_store<T> type_store_t;

      results_context()
      : results_available_(false)
      {}

      inline std::size_t count() const
      {
         if (results_available_)
            return parameter_list_.size();
         else
            return 0;
      }

      inline type_store_t& operator[](const std::size_t& index)
      {
         return parameter_list_[index];
      }

      inline const type_store_t& operator[](const std::size_t& index) const
      {
         return parameter_list_[index];
      }

   private:

      inline void clear()
      {
         results_available_ = false;
      }

      typedef std::vector<type_store_t> ts_list_t;
      typedef typename type_store_t::parameter_list parameter_list_t;

      inline void assign(const parameter_list_t& pl)
      {
         parameter_list_    = pl.parameter_list_;
         results_available_ = true;
      }

      bool results_available_;
      ts_list_t parameter_list_;

      friend class details::return_node<T>;
      friend class details::return_envelope_node<T>;
   };
}
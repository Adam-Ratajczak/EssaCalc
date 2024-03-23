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

#include "include/Functions.hpp"
#include "include/ExpressionNodes.hpp"
#include <list>
#include <set>

namespace Essa::Math{
   template <typename T>
   class stringvar_base
   {
   public:

      typedef typename details::stringvar_node<T> stringvar_node_t;

      stringvar_base(const std::string& name, stringvar_node_t* svn)
      : name_(name)
      , string_varnode_(svn)
      {}

      bool valid() const
      {
         return !name_.empty() && (0 != string_varnode_);
      }

      std::string name() const
      {
         assert(string_varnode_);
         return name_;
      }

      void rebase(std::string& s)
      {
         assert(string_varnode_);
         string_varnode_->rebase(s);
      }

   private:

      std::string name_;
      stringvar_node_t* string_varnode_;
   };

   template <typename T> class parser;
   template <typename T> class expression_helper;

   template <typename T>
   class symbol_table
   {
   public:

     enum symtab_mutability_type
     {
       e_unknown   = 0,
       e_mutable   = 1,
       e_immutable = 2
     };

     typedef T (*ff00_functor)();
     typedef T (*ff01_functor)(T);
     typedef T (*ff02_functor)(T, T);
     typedef T (*ff03_functor)(T, T, T);
     typedef T (*ff04_functor)(T, T, T, T);
     typedef T (*ff05_functor)(T, T, T, T, T);
     typedef T (*ff06_functor)(T, T, T, T, T, T);
     typedef T (*ff07_functor)(T, T, T, T, T, T, T);
     typedef T (*ff08_functor)(T, T, T, T, T, T, T, T);
     typedef T (*ff09_functor)(T, T, T, T, T, T, T, T, T);
     typedef T (*ff10_functor)(T, T, T, T, T, T, T, T, T, T);
     typedef T (*ff11_functor)(T, T, T, T, T, T, T, T, T, T, T);
     typedef T (*ff12_functor)(T, T, T, T, T, T, T, T, T, T, T, T);
     typedef T (*ff13_functor)(T, T, T, T, T, T, T, T, T, T, T, T, T);
     typedef T (*ff14_functor)(T, T, T, T, T, T, T, T, T, T, T, T, T, T);
     typedef T (*ff15_functor)(T, T, T, T, T, T, T, T, T, T, T, T, T, T, T);

   protected:

       struct freefunc00 : public Essa::Math::ifunction<T>
       {
          using Essa::Math::ifunction<T>::operator();

          explicit freefunc00(ff00_functor ff) : Essa::Math::ifunction<T>(0), f(ff) {}
          inline T operator() ()
          { return f(); }
          ff00_functor f;
       };

      struct freefunc01 : public Essa::Math::ifunction<T>
      {
         using Essa::Math::ifunction<T>::operator();

         explicit freefunc01(ff01_functor ff) : Essa::Math::ifunction<T>(1), f(ff) {}
         inline T operator() (const T& v0)
         { return f(v0); }
         ff01_functor f;
      };

      struct freefunc02 : public Essa::Math::ifunction<T>
      {
         using Essa::Math::ifunction<T>::operator();

         explicit freefunc02(ff02_functor ff) : Essa::Math::ifunction<T>(2), f(ff) {}
         inline T operator() (const T& v0, const T& v1)
         { return f(v0, v1); }
         ff02_functor f;
      };

      struct freefunc03 : public Essa::Math::ifunction<T>
      {
         using Essa::Math::ifunction<T>::operator();

         explicit freefunc03(ff03_functor ff) : Essa::Math::ifunction<T>(3), f(ff) {}
         inline T operator() (const T& v0, const T& v1, const T& v2)
         { return f(v0, v1, v2); }
         ff03_functor f;
      };

      struct freefunc04 : public Essa::Math::ifunction<T>
      {
         using Essa::Math::ifunction<T>::operator();

         explicit freefunc04(ff04_functor ff) : Essa::Math::ifunction<T>(4), f(ff) {}
         inline T operator() (const T& v0, const T& v1, const T& v2, const T& v3)
         { return f(v0, v1, v2, v3); }
         ff04_functor f;
      };

      struct freefunc05 : public Essa::Math::ifunction<T>
      {
         using Essa::Math::ifunction<T>::operator();

         explicit freefunc05(ff05_functor ff) : Essa::Math::ifunction<T>(5), f(ff) {}
         inline T operator() (const T& v0, const T& v1, const T& v2, const T& v3, const T& v4)
         { return f(v0, v1, v2, v3, v4); }
         ff05_functor f;
      };

      struct freefunc06 : public Essa::Math::ifunction<T>
      {
         using Essa::Math::ifunction<T>::operator();

         explicit freefunc06(ff06_functor ff) : Essa::Math::ifunction<T>(6), f(ff) {}
         inline T operator() (const T& v0, const T& v1, const T& v2, const T& v3, const T& v4, const T& v5)
         { return f(v0, v1, v2, v3, v4, v5); }
         ff06_functor f;
      };

      struct freefunc07 : public Essa::Math::ifunction<T>
      {
         using Essa::Math::ifunction<T>::operator();

         explicit freefunc07(ff07_functor ff) : Essa::Math::ifunction<T>(7), f(ff) {}
         inline T operator() (const T& v0, const T& v1, const T& v2, const T& v3, const T& v4,
                              const T& v5, const T& v6)
         { return f(v0, v1, v2, v3, v4, v5, v6); }
         ff07_functor f;
      };

      struct freefunc08 : public Essa::Math::ifunction<T>
      {
         using Essa::Math::ifunction<T>::operator();

         explicit freefunc08(ff08_functor ff) : Essa::Math::ifunction<T>(8), f(ff) {}
         inline T operator() (const T& v0, const T& v1, const T& v2, const T& v3, const T& v4,
                              const T& v5, const T& v6, const T& v7)
         { return f(v0, v1, v2, v3, v4, v5, v6, v7); }
         ff08_functor f;
      };

      struct freefunc09 : public Essa::Math::ifunction<T>
      {
         using Essa::Math::ifunction<T>::operator();

         explicit freefunc09(ff09_functor ff) : Essa::Math::ifunction<T>(9), f(ff) {}
         inline T operator() (const T& v0, const T& v1, const T& v2, const T& v3, const T& v4,
                              const T& v5, const T& v6, const T& v7, const T& v8)
         { return f(v0, v1, v2, v3, v4, v5, v6, v7, v8); }
         ff09_functor f;
      };

      struct freefunc10 : public Essa::Math::ifunction<T>
      {
         using Essa::Math::ifunction<T>::operator();

         explicit freefunc10(ff10_functor ff) : Essa::Math::ifunction<T>(10), f(ff) {}
         inline T operator() (const T& v0, const T& v1, const T& v2, const T& v3, const T& v4,
                              const T& v5, const T& v6, const T& v7, const T& v8, const T& v9)
         { return f(v0, v1, v2, v3, v4, v5, v6, v7, v8, v9); }
         ff10_functor f;
      };

      struct freefunc11 : public Essa::Math::ifunction<T>
      {
         using Essa::Math::ifunction<T>::operator();

         explicit freefunc11(ff11_functor ff) : Essa::Math::ifunction<T>(11), f(ff) {}
         inline T operator() (const T& v0, const T& v1, const T& v2, const T& v3, const T& v4,
                              const T& v5, const T& v6, const T& v7, const T& v8, const T& v9, const T& v10)
         { return f(v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10); }
         ff11_functor f;
      };

      struct freefunc12 : public Essa::Math::ifunction<T>
      {
         using Essa::Math::ifunction<T>::operator();

         explicit freefunc12(ff12_functor ff) : Essa::Math::ifunction<T>(12), f(ff) {}
         inline T operator() (const T& v00, const T& v01, const T& v02, const T& v03, const T& v04,
                              const T& v05, const T& v06, const T& v07, const T& v08, const T& v09,
                              const T& v10, const T& v11)
         { return f(v00, v01, v02, v03, v04, v05, v06, v07, v08, v09, v10, v11); }
         ff12_functor f;
      };

      struct freefunc13 : public Essa::Math::ifunction<T>
      {
         using Essa::Math::ifunction<T>::operator();

         explicit freefunc13(ff13_functor ff) : Essa::Math::ifunction<T>(13), f(ff) {}
         inline T operator() (const T& v00, const T& v01, const T& v02, const T& v03, const T& v04,
                              const T& v05, const T& v06, const T& v07, const T& v08, const T& v09,
                              const T& v10, const T& v11, const T& v12)
         { return f(v00, v01, v02, v03, v04, v05, v06, v07, v08, v09, v10, v11, v12); }
         ff13_functor f;
      };

      struct freefunc14 : public Essa::Math::ifunction<T>
      {
         using Essa::Math::ifunction<T>::operator();

         explicit freefunc14(ff14_functor ff) : Essa::Math::ifunction<T>(14), f(ff) {}
         inline T operator() (const T& v00, const T& v01, const T& v02, const T& v03, const T& v04,
                              const T& v05, const T& v06, const T& v07, const T& v08, const T& v09,
                              const T& v10, const T& v11, const T& v12, const T& v13)
         { return f(v00, v01, v02, v03, v04, v05, v06, v07, v08, v09, v10, v11, v12, v13); }
         ff14_functor f;
      };

      struct freefunc15 : public Essa::Math::ifunction<T>
      {
         using Essa::Math::ifunction<T>::operator();

         explicit freefunc15(ff15_functor ff) : Essa::Math::ifunction<T>(15), f(ff) {}
         inline T operator() (const T& v00, const T& v01, const T& v02, const T& v03, const T& v04,
                              const T& v05, const T& v06, const T& v07, const T& v08, const T& v09,
                              const T& v10, const T& v11, const T& v12, const T& v13, const T& v14)
         { return f(v00, v01, v02, v03, v04, v05, v06, v07, v08, v09, v10, v11, v12, v13, v14); }
         ff15_functor f;
      };

      template <typename Type, typename RawType>
      struct type_store
      {
         typedef details::expression_node<T>*        expression_ptr;
         typedef typename details::variable_node<T>  variable_node_t;
         typedef ifunction<T>                        ifunction_t;
         typedef ivararg_function<T>                 ivararg_function_t;
         typedef igeneric_function<T>                igeneric_function_t;
         typedef details::vector_holder<T>           vector_t;
         typedef typename details::stringvar_node<T> stringvar_node_t;

         typedef Type type_t;
         typedef type_t* type_ptr;
         typedef std::pair<bool,type_ptr> type_pair_t;
         typedef std::map<std::string,type_pair_t,details::ilesscompare> type_map_t;
         typedef typename type_map_t::iterator tm_itr_t;
         typedef typename type_map_t::const_iterator tm_const_itr_t;

         enum { lut_size = 256 };

         type_map_t  map;
         std::size_t size;

         type_store()
         : size(0)
         {}

         struct deleter
         {
            #define exprtk_define_process(Type)                  \
            static inline void process(std::pair<bool,Type*>& n) \
            {                                                    \
               delete n.second;                                  \
            }                                                    \

            exprtk_define_process(variable_node_t )
            exprtk_define_process(vector_t        )
            exprtk_define_process(stringvar_node_t)

            #undef exprtk_define_process

            template <typename DeleteType>
            static inline void process(std::pair<bool,DeleteType*>&)
            {}
         };

         inline bool symbol_exists(const std::string& symbol_name) const
         {
            if (symbol_name.empty())
               return false;
            else if (map.end() != map.find(symbol_name))
               return true;
            else
               return false;
         }

         template <typename PtrType>
         inline std::string entity_name(const PtrType& ptr) const
         {
            if (map.empty())
               return std::string();

            tm_const_itr_t itr = map.begin();

            while (map.end() != itr)
            {
               if (itr->second.second == ptr)
               {
                  return itr->first;
               }
               else
                  ++itr;
            }

            return std::string();
         }

         inline bool is_constant(const std::string& symbol_name) const
         {
            if (symbol_name.empty())
               return false;
            else
            {
               const tm_const_itr_t itr = map.find(symbol_name);

               if (map.end() == itr)
                  return false;
               else
                  return (*itr).second.first;
            }
         }

         template <typename Tie, typename RType>
         inline bool add_impl(const std::string& symbol_name, RType t, const bool is_const)
         {
            if (symbol_name.size() > 1)
            {
               for (std::size_t i = 0; i < details::reserved_symbols_size; ++i)
               {
                  if (details::imatch(symbol_name, details::reserved_symbols[i]))
                  {
                     return false;
                  }
               }
            }

            const tm_itr_t itr = map.find(symbol_name);

            if (map.end() == itr)
            {
               map[symbol_name] = Tie::make(t,is_const);
               ++size;
            }

            return true;
         }

         struct tie_array
         {
            static inline std::pair<bool,vector_t*> make(std::pair<T*,std::size_t> v, const bool is_const = false)
            {
               return std::make_pair(is_const, new vector_t(v.first, v.second));
            }
         };

         struct tie_stdvec
         {
            template <typename Allocator>
            static inline std::pair<bool,vector_t*> make(std::vector<T,Allocator>& v, const bool is_const = false)
            {
               return std::make_pair(is_const, new vector_t(v));
            }
         };

         struct tie_vecview
         {
            static inline std::pair<bool,vector_t*> make(Essa::Math::vector_view<T>& v, const bool is_const = false)
            {
               return std::make_pair(is_const, new vector_t(v));
            }
         };

         struct tie_stddeq
         {
            template <typename Allocator>
            static inline std::pair<bool,vector_t*> make(std::deque<T,Allocator>& v, const bool is_const = false)
            {
               return std::make_pair(is_const, new vector_t(v));
            }
         };

         template <std::size_t v_size>
         inline bool add(const std::string& symbol_name, T (&v)[v_size], const bool is_const = false)
         {
            return add_impl<tie_array,std::pair<T*,std::size_t> >
                      (symbol_name, std::make_pair(v,v_size), is_const);
         }

         inline bool add(const std::string& symbol_name, T* v, const std::size_t v_size, const bool is_const = false)
         {
            return add_impl<tie_array,std::pair<T*,std::size_t> >
                     (symbol_name, std::make_pair(v,v_size), is_const);
         }

         template <typename Allocator>
         inline bool add(const std::string& symbol_name, std::vector<T,Allocator>& v, const bool is_const = false)
         {
            return add_impl<tie_stdvec,std::vector<T,Allocator>&>
                      (symbol_name, v, is_const);
         }

         inline bool add(const std::string& symbol_name, Essa::Math::vector_view<T>& v, const bool is_const = false)
         {
            return add_impl<tie_vecview,Essa::Math::vector_view<T>&>
                      (symbol_name, v, is_const);
         }

         template <typename Allocator>
         inline bool add(const std::string& symbol_name, std::deque<T,Allocator>& v, const bool is_const = false)
         {
            return add_impl<tie_stddeq,std::deque<T,Allocator>&>
                      (symbol_name, v, is_const);
         }

         inline bool add(const std::string& symbol_name, RawType& t_, const bool is_const = false)
         {
            struct tie
            {
               static inline std::pair<bool,variable_node_t*> make(T& t, const std::string& _name, const bool is_constant = false)
               {
                  return std::make_pair(is_constant, new variable_node_t(t, _name));
               }

               static inline std::pair<bool,stringvar_node_t*> make(std::string& t, const bool is_constant = false)
               {
                  return std::make_pair(is_constant, new stringvar_node_t(t));
               }

               static inline std::pair<bool,function_t*> make(function_t& t, const bool is_constant = false)
               {
                  return std::make_pair(is_constant,&t);
               }

               static inline std::pair<bool,vararg_function_t*> make(vararg_function_t& t, const bool is_constant = false)
               {
                  return std::make_pair(is_constant,&t);
               }

               static inline std::pair<bool,generic_function_t*> make(generic_function_t& t, const bool is_constant = false)
               {
                  return std::make_pair(is_constant,&t);
               }
            };

            const tm_itr_t itr = map.find(symbol_name);

            if (map.end() == itr)
            {
               map[symbol_name] = tie::make(t_, symbol_name, is_const);
               ++size;
            }

            return true;
         }

         inline type_ptr get(const std::string& symbol_name) const
         {
            const tm_const_itr_t itr = map.find(symbol_name);

            if (map.end() == itr)
               return reinterpret_cast<type_ptr>(0);
            else
               return itr->second.second;
         }

         template <typename TType, typename TRawType, typename PtrType>
         struct ptr_match
         {
            static inline bool test(const PtrType, const void*)
            {
               return false;
            }
         };

         template <typename TType, typename TRawType>
         struct ptr_match<TType,TRawType,variable_node_t*>
         {
            static inline bool test(const variable_node_t* p, const void* ptr)
            {
               exprtk_debug(("ptr_match::test() - %p <--> %p\n",(void*)(&(p->ref())),ptr));
               return (&(p->ref()) == ptr);
            }
         };

         inline type_ptr get_from_varptr(const void* ptr) const
         {
            tm_const_itr_t itr = map.begin();

            while (map.end() != itr)
            {
               type_ptr ret_ptr = itr->second.second;

               if (ptr_match<Type,RawType,type_ptr>::test(ret_ptr,ptr))
               {
                  return ret_ptr;
               }

               ++itr;
            }

            return type_ptr(0);
         }

         inline bool remove(const std::string& symbol_name, const bool delete_node = true)
         {
            const tm_itr_t itr = map.find(symbol_name);

            if (map.end() != itr)
            {
               if (delete_node)
               {
                  deleter::process((*itr).second);
               }

               map.erase(itr);
               --size;

               return true;
            }
            else
               return false;
         }

         inline RawType& type_ref(const std::string& symbol_name)
         {
            struct init_type
            {
               static inline double set(double)           { return (0.0);           }
               static inline double set(long double)      { return (0.0);           }
               static inline float  set(float)            { return (0.0f);          }
               static inline std::string set(std::string) { return std::string(""); }
            };

            static RawType null_type = init_type::set(RawType());

            const tm_const_itr_t itr = map.find(symbol_name);

            if (map.end() == itr)
               return null_type;
            else
               return itr->second.second->ref();
         }

         inline void clear(const bool delete_node = true)
         {
            if (!map.empty())
            {
               if (delete_node)
               {
                  tm_itr_t itr = map.begin();
                  tm_itr_t end = map.end  ();

                  while (end != itr)
                  {
                     deleter::process((*itr).second);
                     ++itr;
                  }
               }

               map.clear();
            }

            size = 0;
         }

         template <typename Allocator,
                   template <typename, typename> class Sequence>
         inline std::size_t get_list(Sequence<std::pair<std::string,RawType>,Allocator>& list) const
         {
            std::size_t count = 0;

            if (!map.empty())
            {
               tm_const_itr_t itr = map.begin();
               tm_const_itr_t end = map.end  ();

               while (end != itr)
               {
                  list.push_back(std::make_pair((*itr).first,itr->second.second->ref()));
                  ++itr;
                  ++count;
               }
            }

            return count;
         }

         template <typename Allocator,
                   template <typename, typename> class Sequence>
         inline std::size_t get_list(Sequence<std::string,Allocator>& vlist) const
         {
            std::size_t count = 0;

            if (!map.empty())
            {
               tm_const_itr_t itr = map.begin();
               tm_const_itr_t end = map.end  ();

               while (end != itr)
               {
                  vlist.push_back((*itr).first);
                  ++itr;
                  ++count;
               }
            }

            return count;
         }
      };

      typedef details::expression_node<T>*        expression_ptr;
      typedef typename details::variable_node<T>  variable_t;
      typedef typename details::vector_holder<T>  vector_holder_t;
      typedef variable_t*                         variable_ptr;
      typedef typename details::stringvar_node<T> stringvar_t;
      typedef stringvar_t*                        stringvar_ptr;
      typedef ifunction        <T>                function_t;
      typedef ivararg_function <T>                vararg_function_t;
      typedef igeneric_function<T>                generic_function_t;
      typedef function_t*                         function_ptr;
      typedef vararg_function_t*                  vararg_function_ptr;
      typedef generic_function_t*                 generic_function_ptr;

      static const std::size_t lut_size = 256;

      // Symbol Table Holder
      struct control_block
      {
         struct st_data
         {
            type_store<variable_t        , T                 > variable_store;
            type_store<function_t        , function_t        > function_store;
            type_store<vararg_function_t , vararg_function_t > vararg_function_store;
            type_store<generic_function_t, generic_function_t> generic_function_store;
            type_store<generic_function_t, generic_function_t> string_function_store;
            type_store<generic_function_t, generic_function_t> overload_function_store;
            type_store<vector_holder_t   , vector_holder_t   > vector_store;
            type_store<stringvar_t       , std::string       > stringvar_store;

            st_data()
            {
               for (std::size_t i = 0; i < details::reserved_words_size; ++i)
               {
                  reserved_symbol_table_.insert(details::reserved_words[i]);
               }

               for (std::size_t i = 0; i < details::reserved_symbols_size; ++i)
               {
                  reserved_symbol_table_.insert(details::reserved_symbols[i]);
               }
            }

           ~st_data()
            {
               for (std::size_t i = 0; i < free_function_list_.size(); ++i)
               {
                  delete free_function_list_[i];
               }
            }

            inline bool is_reserved_symbol(const std::string& symbol) const
            {
               return (reserved_symbol_table_.end() != reserved_symbol_table_.find(symbol));
            }

            static inline st_data* create()
            {
               return (new st_data);
            }

            static inline void destroy(st_data*& sd)
            {
               delete sd;
               sd = reinterpret_cast<st_data*>(0);
            }

            std::list<T>               local_symbol_list_;
            std::list<std::string>     local_stringvar_list_;
            std::set<std::string>      reserved_symbol_table_;
            std::vector<ifunction<T>*> free_function_list_;
         };

         control_block()
         : ref_count(1)
         , data_(st_data::create())
         , mutability_(e_mutable)
         {}

         explicit control_block(st_data* data)
         : ref_count(1)
         , data_(data)
         , mutability_(e_mutable)
         {}

        ~control_block()
         {
            if (data_ && (0 == ref_count))
            {
               st_data::destroy(data_);
            }
         }

         static inline control_block* create()
         {
            return (new control_block);
         }

         template <typename SymTab>
         static inline void destroy(control_block*& cntrl_blck, SymTab* sym_tab)
         {
            if (cntrl_blck)
            {
               if (
                    (0 !=   cntrl_blck->ref_count) &&
                    (0 == --cntrl_blck->ref_count)
                  )
               {
                  if (sym_tab)
                     sym_tab->clear();

                  delete cntrl_blck;
               }

               cntrl_blck = 0;
            }
         }

         void set_mutability(const symtab_mutability_type mutability)
         {
            mutability_ = mutability;
         }

         std::size_t ref_count;
         st_data* data_;
         symtab_mutability_type mutability_;
      };

   public:

      symbol_table(const symtab_mutability_type mutability = e_mutable)
      : control_block_(control_block::create())
      {
         control_block_->set_mutability(mutability);
         clear();
      }

     ~symbol_table()
      {
         Essa::Math::details::dump_ptr("~symbol_table", this);
         control_block::destroy(control_block_, this);
      }

      symbol_table(const symbol_table<T>& st)
      {
         control_block_ = st.control_block_;
         control_block_->ref_count++;
      }

      inline symbol_table<T>& operator=(const symbol_table<T>& st)
      {
         if (this != &st)
         {
            control_block::destroy(control_block_,reinterpret_cast<symbol_table<T>*>(0));

            control_block_ = st.control_block_;
            control_block_->ref_count++;
         }

         return (*this);
      }

      inline bool operator==(const symbol_table<T>& st) const
      {
         return (this == &st) || (control_block_ == st.control_block_);
      }

      inline symtab_mutability_type mutability() const
      {
         return valid() ? control_block_->mutability_ : e_unknown;
      }

      inline void clear_variables(const bool delete_node = true)
      {
         local_data().variable_store.clear(delete_node);
      }

      inline void clear_functions()
      {
         local_data().function_store.clear();
      }

      inline void clear_strings()
      {
         local_data().stringvar_store.clear();
      }

      inline void clear_vectors()
      {
         local_data().vector_store.clear();
      }

      inline void clear_local_constants()
      {
         local_data().local_symbol_list_.clear();
      }

      inline void clear()
      {
         if (!valid()) return;
         clear_variables      ();
         clear_functions      ();
         clear_strings        ();
         clear_vectors        ();
         clear_local_constants();
      }

      inline std::size_t variable_count() const
      {
         if (valid())
            return local_data().variable_store.size;
         else
            return 0;
      }

      inline std::size_t stringvar_count() const
      {
         if (valid())
            return local_data().stringvar_store.size;
         else
            return 0;
      }

      inline std::size_t function_count() const
      {
         if (valid())
            return local_data().function_store.size;
         else
            return 0;
      }

      inline std::size_t vector_count() const
      {
         if (valid())
            return local_data().vector_store.size;
         else
            return 0;
      }

      inline variable_ptr get_variable(const std::string& variable_name) const
      {
         if (!valid())
            return reinterpret_cast<variable_ptr>(0);
         else if (!valid_symbol(variable_name))
            return reinterpret_cast<variable_ptr>(0);
         else
            return local_data().variable_store.get(variable_name);
      }

      inline variable_ptr get_variable(const T& var_ref) const
      {
         if (!valid())
            return reinterpret_cast<variable_ptr>(0);
         else
            return local_data().variable_store.get_from_varptr(
                                                  reinterpret_cast<const void*>(&var_ref));
      }

      inline stringvar_ptr get_stringvar(const std::string& string_name) const
      {
         if (!valid())
            return reinterpret_cast<stringvar_ptr>(0);
         else if (!valid_symbol(string_name))
            return reinterpret_cast<stringvar_ptr>(0);
         else
            return local_data().stringvar_store.get(string_name);
      }

      inline stringvar_base<T> get_stringvar_base(const std::string& string_name) const
      {
         static stringvar_base<T> null_stringvar_base("",reinterpret_cast<stringvar_ptr>(0));
         if (!valid())
            return null_stringvar_base;
         else if (!valid_symbol(string_name))
            return null_stringvar_base;

         stringvar_ptr stringvar = local_data().stringvar_store.get(string_name);

         if (0 == stringvar)
         {
            return null_stringvar_base;
         }

         return stringvar_base<T>(string_name,stringvar);
      }

      inline function_ptr get_function(const std::string& function_name) const
      {
         if (!valid())
            return reinterpret_cast<function_ptr>(0);
         else if (!valid_symbol(function_name))
            return reinterpret_cast<function_ptr>(0);
         else
            return local_data().function_store.get(function_name);
      }

      inline vararg_function_ptr get_vararg_function(const std::string& vararg_function_name) const
      {
         if (!valid())
            return reinterpret_cast<vararg_function_ptr>(0);
         else if (!valid_symbol(vararg_function_name))
            return reinterpret_cast<vararg_function_ptr>(0);
         else
            return local_data().vararg_function_store.get(vararg_function_name);
      }

      inline generic_function_ptr get_generic_function(const std::string& function_name) const
      {
         if (!valid())
            return reinterpret_cast<generic_function_ptr>(0);
         else if (!valid_symbol(function_name))
            return reinterpret_cast<generic_function_ptr>(0);
         else
            return local_data().generic_function_store.get(function_name);
      }

      inline generic_function_ptr get_string_function(const std::string& function_name) const
      {
         if (!valid())
            return reinterpret_cast<generic_function_ptr>(0);
         else if (!valid_symbol(function_name))
            return reinterpret_cast<generic_function_ptr>(0);
         else
            return local_data().string_function_store.get(function_name);
      }

      inline generic_function_ptr get_overload_function(const std::string& function_name) const
      {
         if (!valid())
            return reinterpret_cast<generic_function_ptr>(0);
         else if (!valid_symbol(function_name))
            return reinterpret_cast<generic_function_ptr>(0);
         else
            return local_data().overload_function_store.get(function_name);
      }

      typedef vector_holder_t* vector_holder_ptr;

      inline vector_holder_ptr get_vector(const std::string& vector_name) const
      {
         if (!valid())
            return reinterpret_cast<vector_holder_ptr>(0);
         else if (!valid_symbol(vector_name))
            return reinterpret_cast<vector_holder_ptr>(0);
         else
            return local_data().vector_store.get(vector_name);
      }

      inline T& variable_ref(const std::string& symbol_name)
      {
         static T null_var = T(0);
         if (!valid())
            return null_var;
         else if (!valid_symbol(symbol_name))
            return null_var;
         else
            return local_data().variable_store.type_ref(symbol_name);
      }

      inline std::string& stringvar_ref(const std::string& symbol_name)
      {
         static std::string null_stringvar;
         if (!valid())
            return null_stringvar;
         else if (!valid_symbol(symbol_name))
            return null_stringvar;
         else
            return local_data().stringvar_store.type_ref(symbol_name);
      }
      
      inline bool is_constant_node(const std::string& symbol_name) const
      {
         if (!valid())
            return false;
         else if (!valid_symbol(symbol_name))
            return false;
         else
            return local_data().variable_store.is_constant(symbol_name);
      }

      inline bool is_constant_string(const std::string& symbol_name) const
      {
         if (!valid())
            return false;
         else if (!valid_symbol(symbol_name))
            return false;
         else if (!local_data().stringvar_store.symbol_exists(symbol_name))
            return false;
         else
            return local_data().stringvar_store.is_constant(symbol_name);
      }

      inline bool create_variable(const std::string& variable_name, const T& value = T(0))
      {
         if (!valid())
            return false;
         else if (!valid_symbol(variable_name))
            return false;
         else if (symbol_exists(variable_name))
            return false;

         local_data().local_symbol_list_.push_back(value);
         T& t = local_data().local_symbol_list_.back();

         return add_variable(variable_name,t);
      }

      inline bool create_stringvar(const std::string& stringvar_name, const std::string& value = std::string(""))
      {
         if (!valid())
            return false;
         else if (!valid_symbol(stringvar_name))
            return false;
         else if (symbol_exists(stringvar_name))
            return false;

         local_data().local_stringvar_list_.push_back(value);
         std::string& s = local_data().local_stringvar_list_.back();

         return add_stringvar(stringvar_name,s);
      }

      inline bool add_variable(const std::string& variable_name, T& t, const bool is_constant = false)
      {
         if (!valid())
            return false;
         else if (!valid_symbol(variable_name))
            return false;
         else if (symbol_exists(variable_name))
            return false;
         else
            return local_data().variable_store.add(variable_name, t, is_constant);
      }

      inline bool add_constant(const std::string& constant_name, const T& value)
      {
         if (!valid())
            return false;
         else if (!valid_symbol(constant_name))
            return false;
         else if (symbol_exists(constant_name))
            return false;

         local_data().local_symbol_list_.push_back(value);
         T& t = local_data().local_symbol_list_.back();

         return add_variable(constant_name, t, true);
      }

      inline bool add_stringvar(const std::string& stringvar_name, std::string& s, const bool is_constant = false)
      {
         if (!valid())
            return false;
         else if (!valid_symbol(stringvar_name))
            return false;
         else if (symbol_exists(stringvar_name))
            return false;
         else
            return local_data().stringvar_store.add(stringvar_name, s, is_constant);
      }

      inline bool add_function(const std::string& function_name, function_t& function)
      {
         if (!valid())
            return false;
         else if (!valid_symbol(function_name))
            return false;
         else if (symbol_exists(function_name))
            return false;
         else
            return local_data().function_store.add(function_name,function);
      }

      inline bool add_function(const std::string& vararg_function_name, vararg_function_t& vararg_function)
      {
         if (!valid())
            return false;
         else if (!valid_symbol(vararg_function_name))
            return false;
         else if (symbol_exists(vararg_function_name))
            return false;
         else
            return local_data().vararg_function_store.add(vararg_function_name,vararg_function);
      }

      inline bool add_function(const std::string& function_name, generic_function_t& function)
      {
         if (!valid())
            return false;
         else if (!valid_symbol(function_name))
            return false;
         else if (symbol_exists(function_name))
            return false;
         else
         {
            switch (function.rtrn_type)
            {
               case generic_function_t::e_rtrn_scalar :
                  return (std::string::npos == function.parameter_sequence.find_first_not_of("STVZ*?|")) ?
                         local_data().generic_function_store.add(function_name,function) : false;

               case generic_function_t::e_rtrn_string :
                  return (std::string::npos == function.parameter_sequence.find_first_not_of("STVZ*?|")) ?
                         local_data().string_function_store.add(function_name,function)  : false;

               case generic_function_t::e_rtrn_overload :
                  return (std::string::npos == function.parameter_sequence.find_first_not_of("STVZ*?|:")) ?
                         local_data().overload_function_store.add(function_name,function) : false;
            }
         }

         return false;
      }

      #define exprtk_define_freefunction(NN)                                                \
      inline bool add_function(const std::string& function_name, ff##NN##_functor function) \
      {                                                                                     \
         if (!valid())                                                                      \
         { return false; }                                                                  \
         if (!valid_symbol(function_name))                                                  \
         { return false; }                                                                  \
         if (symbol_exists(function_name))                                                  \
         { return false; }                                                                  \
                                                                                            \
         Essa::Math::ifunction<T>* ifunc = new freefunc##NN(function);                          \
                                                                                            \
         local_data().free_function_list_.push_back(ifunc);                                 \
                                                                                            \
         return add_function(function_name,(*local_data().free_function_list_.back()));     \
      }                                                                                     \

      exprtk_define_freefunction(00) exprtk_define_freefunction(01)
      exprtk_define_freefunction(02) exprtk_define_freefunction(03)
      exprtk_define_freefunction(04) exprtk_define_freefunction(05)
      exprtk_define_freefunction(06) exprtk_define_freefunction(07)
      exprtk_define_freefunction(08) exprtk_define_freefunction(09)
      exprtk_define_freefunction(10) exprtk_define_freefunction(11)
      exprtk_define_freefunction(12) exprtk_define_freefunction(13)
      exprtk_define_freefunction(14) exprtk_define_freefunction(15)

      #undef exprtk_define_freefunction

      inline bool add_reserved_function(const std::string& function_name, function_t& function)
      {
         if (!valid())
            return false;
         else if (!valid_symbol(function_name,false))
            return false;
         else if (symbol_exists(function_name,false))
            return false;
         else
            return local_data().function_store.add(function_name,function);
      }

      inline bool add_reserved_function(const std::string& vararg_function_name, vararg_function_t& vararg_function)
      {
         if (!valid())
            return false;
         else if (!valid_symbol(vararg_function_name,false))
            return false;
         else if (symbol_exists(vararg_function_name,false))
            return false;
         else
            return local_data().vararg_function_store.add(vararg_function_name,vararg_function);
      }

      inline bool add_reserved_function(const std::string& function_name, generic_function_t& function)
      {
         if (!valid())
            return false;
         else if (!valid_symbol(function_name,false))
            return false;
         else if (symbol_exists(function_name,false))
            return false;
         else
         {
            switch (function.rtrn_type)
            {
               case generic_function_t::e_rtrn_scalar :
                  return (std::string::npos == function.parameter_sequence.find_first_not_of("STVZ*?|")) ?
                         local_data().generic_function_store.add(function_name,function) : false;

               case generic_function_t::e_rtrn_string :
                  return (std::string::npos == function.parameter_sequence.find_first_not_of("STVZ*?|")) ?
                         local_data().string_function_store.add(function_name,function)  : false;

               case generic_function_t::e_rtrn_overload :
                  return (std::string::npos == function.parameter_sequence.find_first_not_of("STVZ*?|:")) ?
                         local_data().overload_function_store.add(function_name,function) : false;
            }
         }

         return false;
      }

      template <std::size_t N>
      inline bool add_vector(const std::string& vector_name, T (&v)[N])
      {
         if (!valid())
            return false;
         else if (!valid_symbol(vector_name))
            return false;
         else if (symbol_exists(vector_name))
            return false;
         else
            return local_data().vector_store.add(vector_name,v);
      }

      inline bool add_vector(const std::string& vector_name, T* v, const std::size_t& v_size)
      {
         if (!valid())
            return false;
         else if (!valid_symbol(vector_name))
            return false;
         else if (symbol_exists(vector_name))
            return false;
         else if (0 == v_size)
            return false;
         else
            return local_data().vector_store.add(vector_name, v, v_size);
      }

      template <typename Allocator>
      inline bool add_vector(const std::string& vector_name, std::vector<T,Allocator>& v)
      {
         if (!valid())
            return false;
         else if (!valid_symbol(vector_name))
            return false;
         else if (symbol_exists(vector_name))
            return false;
         else if (0 == v.size())
            return false;
         else
            return local_data().vector_store.add(vector_name,v);
      }

      inline bool add_vector(const std::string& vector_name, Essa::Math::vector_view<T>& v)
      {
         if (!valid())
            return false;
         else if (!valid_symbol(vector_name))
            return false;
         else if (symbol_exists(vector_name))
            return false;
         else if (0 == v.size())
            return false;
         else
            return local_data().vector_store.add(vector_name,v);
      }

      inline bool remove_variable(const std::string& variable_name, const bool delete_node = true)
      {
         if (!valid())
            return false;
         else
            return local_data().variable_store.remove(variable_name, delete_node);
      }

      inline bool remove_stringvar(const std::string& string_name)
      {
         if (!valid())
            return false;
         else
            return local_data().stringvar_store.remove(string_name);
      }

      inline bool remove_function(const std::string& function_name)
      {
         if (!valid())
            return false;
         else
            return local_data().function_store.remove(function_name);
      }

      inline bool remove_vararg_function(const std::string& vararg_function_name)
      {
         if (!valid())
            return false;
         else
            return local_data().vararg_function_store.remove(vararg_function_name);
      }

      inline bool remove_vector(const std::string& vector_name)
      {
         if (!valid())
            return false;
         else
            return local_data().vector_store.remove(vector_name);
      }

      inline bool add_constants()
      {
         return add_pi      () &&
                add_e       () &&
                add_i       () &&
                add_epsilon () &&
                add_infinity() ;
      }

      inline bool add_pi()
      {
         const typename details::numeric::details::number_type<T>::type num_type;
         static const T local_pi = details::numeric::details::const_pi_impl<T>(num_type);
         return add_constant("%pi",local_pi);
      }

      inline bool add_e()
      {
         const typename details::numeric::details::number_type<T>::type num_type;
         static const T local_e = details::numeric::details::const_e_impl<T>(num_type);
         return add_constant("%e",local_e);
      }

      inline bool add_i()
      {
         const typename details::numeric::details::number_type<T>::type num_type;
         static const T local_i = details::numeric::details::const_i_impl<T>(num_type);
         return add_constant("%i",local_i);
      }

      inline bool add_epsilon()
      {
         static const T local_epsilon = details::numeric::details::epsilon_type<T>::value();
         return add_constant("epsilon",local_epsilon);
      }

      inline bool add_infinity()
      {
         static const T local_infinity = std::numeric_limits<T>::infinity();
         return add_constant("inf",local_infinity);
      }

      template <typename Package>
      inline bool add_package(Package& package)
      {
         return package.register_package(*this);
      }

      template <typename Allocator,
                template <typename, typename> class Sequence>
      inline std::size_t get_variable_list(Sequence<std::pair<std::string,T>,Allocator>& vlist) const
      {
         if (!valid())
            return 0;
         else
            return local_data().variable_store.get_list(vlist);
      }

      template <typename Allocator,
                template <typename, typename> class Sequence>
      inline std::size_t get_variable_list(Sequence<std::string,Allocator>& vlist) const
      {
         if (!valid())
            return 0;
         else
            return local_data().variable_store.get_list(vlist);
      }

      template <typename Allocator,
                template <typename, typename> class Sequence>
      inline std::size_t get_stringvar_list(Sequence<std::pair<std::string,std::string>,Allocator>& svlist) const
      {
         if (!valid())
            return 0;
         else
            return local_data().stringvar_store.get_list(svlist);
      }

      template <typename Allocator,
                template <typename, typename> class Sequence>
      inline std::size_t get_stringvar_list(Sequence<std::string,Allocator>& svlist) const
      {
         if (!valid())
            return 0;
         else
            return local_data().stringvar_store.get_list(svlist);
      }

      template <typename Allocator,
                template <typename, typename> class Sequence>
      inline std::size_t get_vector_list(Sequence<std::string,Allocator>& vlist) const
      {
         if (!valid())
            return 0;
         else
            return local_data().vector_store.get_list(vlist);
      }

      inline bool symbol_exists(const std::string& symbol_name, const bool check_reserved_symb = true) const
      {
         /*
            Function will return true if symbol_name exists as either a
            reserved symbol, variable, stringvar, vector or function name
            in any of the type stores.
         */
         if (!valid())
            return false;
         else if (local_data().variable_store.symbol_exists(symbol_name))
            return true;
         else if (local_data().stringvar_store.symbol_exists(symbol_name))
            return true;
         else if (local_data().vector_store.symbol_exists(symbol_name))
            return true;
         else if (local_data().function_store.symbol_exists(symbol_name))
            return true;
         else if (check_reserved_symb && local_data().is_reserved_symbol(symbol_name))
            return true;
         else
            return false;
      }

      inline bool is_variable(const std::string& variable_name) const
      {
         if (!valid())
            return false;
         else
            return local_data().variable_store.symbol_exists(variable_name);
      }

      inline bool is_stringvar(const std::string& stringvar_name) const
      {
         if (!valid())
            return false;
         else
            return local_data().stringvar_store.symbol_exists(stringvar_name);
      }

      inline bool is_conststr_stringvar(const std::string& symbol_name) const
      {
         if (!valid())
            return false;
         else if (!valid_symbol(symbol_name))
            return false;
         else if (!local_data().stringvar_store.symbol_exists(symbol_name))
            return false;

         return (
                  local_data().stringvar_store.symbol_exists(symbol_name) ||
                  local_data().stringvar_store.is_constant  (symbol_name)
                );
      }

      inline bool is_function(const std::string& function_name) const
      {
         if (!valid())
            return false;
         else
            return local_data().function_store.symbol_exists(function_name);
      }

      inline bool is_vararg_function(const std::string& vararg_function_name) const
      {
         if (!valid())
            return false;
         else
            return local_data().vararg_function_store.symbol_exists(vararg_function_name);
      }

      inline bool is_vector(const std::string& vector_name) const
      {
         if (!valid())
            return false;
         else
            return local_data().vector_store.symbol_exists(vector_name);
      }

      inline std::string get_variable_name(const expression_ptr& ptr) const
      {
         return local_data().variable_store.entity_name(ptr);
      }

      inline std::string get_vector_name(const vector_holder_ptr& ptr) const
      {
         return local_data().vector_store.entity_name(ptr);
      }

      inline std::string get_stringvar_name(const expression_ptr& ptr) const
      {
         return local_data().stringvar_store.entity_name(ptr);
      }

      inline std::string get_conststr_stringvar_name(const expression_ptr& ptr) const
      {
         return local_data().stringvar_store.entity_name(ptr);
      }

      inline bool valid() const
      {
         // Symbol table sanity check.
         return control_block_ && control_block_->data_;
      }

      inline void load_from(const symbol_table<T>& st)
      {
         {
            std::vector<std::string> name_list;

            st.local_data().function_store.get_list(name_list);

            if (!name_list.empty())
            {
               for (std::size_t i = 0; i < name_list.size(); ++i)
               {
                  Essa::Math::ifunction<T>& ifunc = *st.get_function(name_list[i]);
                  add_function(name_list[i],ifunc);
               }
            }
         }

         {
            std::vector<std::string> name_list;

            st.local_data().vararg_function_store.get_list(name_list);

            if (!name_list.empty())
            {
               for (std::size_t i = 0; i < name_list.size(); ++i)
               {
                  Essa::Math::ivararg_function<T>& ivafunc = *st.get_vararg_function(name_list[i]);
                  add_function(name_list[i],ivafunc);
               }
            }
         }

         {
            std::vector<std::string> name_list;

            st.local_data().generic_function_store.get_list(name_list);

            if (!name_list.empty())
            {
               for (std::size_t i = 0; i < name_list.size(); ++i)
               {
                  Essa::Math::igeneric_function<T>& ifunc = *st.get_generic_function(name_list[i]);
                  add_function(name_list[i],ifunc);
               }
            }
         }

         {
            std::vector<std::string> name_list;

            st.local_data().string_function_store.get_list(name_list);

            if (!name_list.empty())
            {
               for (std::size_t i = 0; i < name_list.size(); ++i)
               {
                  Essa::Math::igeneric_function<T>& ifunc = *st.get_string_function(name_list[i]);
                  add_function(name_list[i],ifunc);
               }
            }
         }

         {
            std::vector<std::string> name_list;

            st.local_data().overload_function_store.get_list(name_list);

            if (!name_list.empty())
            {
               for (std::size_t i = 0; i < name_list.size(); ++i)
               {
                  Essa::Math::igeneric_function<T>& ifunc = *st.get_overload_function(name_list[i]);
                  add_function(name_list[i],ifunc);
               }
            }
         }
      }

   private:

      inline bool valid_symbol(const std::string& symbol, const bool check_reserved_symb = true) const
      {
         if (symbol.empty())
            return false;
         else if (!details::is_letter(symbol[0]))
            return false;
         else if (symbol.size() > 1)
         {
            for (std::size_t i = 1; i < symbol.size(); ++i)
            {
               if (
                    !details::is_letter_or_digit(symbol[i]) &&
                    ('_' != symbol[i])
                  )
               {
                  if ((i < (symbol.size() - 1)) && ('.' == symbol[i]))
                     continue;
                  else
                     return false;
               }
            }
         }

         return (check_reserved_symb) ? (!local_data().is_reserved_symbol(symbol)) : true;
      }

      inline bool valid_function(const std::string& symbol) const
      {
         if (symbol.empty())
            return false;
         else if (!details::is_letter(symbol[0]))
            return false;
         else if (symbol.size() > 1)
         {
            for (std::size_t i = 1; i < symbol.size(); ++i)
            {
               if (
                    !details::is_letter_or_digit(symbol[i]) &&
                    ('_' != symbol[i])
                  )
               {
                  if ((i < (symbol.size() - 1)) && ('.' == symbol[i]))
                     continue;
                  else
                     return false;
               }
            }
         }

         return true;
      }

      typedef typename control_block::st_data local_data_t;

      inline local_data_t& local_data()
      {
         return *(control_block_->data_);
      }

      inline const local_data_t& local_data() const
      {
         return *(control_block_->data_);
      }

      control_block* control_block_;

      friend class parser<T>;
   }; // class symbol_table
}


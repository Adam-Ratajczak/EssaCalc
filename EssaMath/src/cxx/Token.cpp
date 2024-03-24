#include "include/Token.hpp"
#include <cassert>

namespace Essa::Math{
   namespace lexer{

         token_scanner::token_scanner(const std::size_t& stride)
         : stride_(stride)
         {
            if (stride > 4)
            {
               throw std::invalid_argument("token_scanner() - Invalid stride value");
            }
         }

         std::size_t token_scanner::process(generator& g)
         {
            if (g.token_list_.size() >= stride_)
            {
               for (std::size_t i = 0; i < (g.token_list_.size() - stride_ + 1); ++i)
               {
                  token t;

                  switch (stride_)
                  {
                     case 1 :
                              {
                                 const token& t0 = g.token_list_[i];

                                 if (!operator()(t0))
                                 {
                                    return i;
                                 }
                              }
                              break;

                     case 2 :
                              {
                                 const token& t0 = g.token_list_[i    ];
                                 const token& t1 = g.token_list_[i + 1];

                                 if (!operator()(t0, t1))
                                 {
                                    return i;
                                 }
                              }
                              break;

                     case 3 :
                              {
                                 const token& t0 = g.token_list_[i    ];
                                 const token& t1 = g.token_list_[i + 1];
                                 const token& t2 = g.token_list_[i + 2];

                                 if (!operator()(t0, t1, t2))
                                 {
                                    return i;
                                 }
                              }
                              break;

                     case 4 :
                              {
                                 const token& t0 = g.token_list_[i    ];
                                 const token& t1 = g.token_list_[i + 1];
                                 const token& t2 = g.token_list_[i + 2];
                                 const token& t3 = g.token_list_[i + 3];

                                 if (!operator()(t0, t1, t2, t3))
                                 {
                                    return i;
                                 }
                              }
                              break;
                  }
               }
            }

            return (g.token_list_.size() - stride_ + 1);
         }

         bool token_scanner::operator() (const token&)
         {
            return false;
         }

         bool token_scanner::operator() (const token&, const token&)
         {
            return false;
         }

         bool token_scanner::operator() (const token&, const token&, const token&)
         {
            return false;
         }

         bool token_scanner::operator() (const token&, const token&, const token&, const token&)
         {
            return false;
         }

         std::size_t token_modifier::process(generator& g)
         {
            std::size_t changes = 0;

            for (std::size_t i = 0; i < g.token_list_.size(); ++i)
            {
               if (modify(g.token_list_[i])) changes++;
            }

            return changes;
         }
         
         token_inserter::token_inserter(const std::size_t& stride)
         : stride_(stride)
         {
            if (stride > 5)
            {
               throw std::invalid_argument("token_inserter() - Invalid stride value");
            }
         }

         std::size_t token_inserter::process(generator& g)
         {
            if (g.token_list_.empty())
               return 0;
            else if (g.token_list_.size() < stride_)
               return 0;

            std::size_t changes = 0;

            typedef std::pair<std::size_t, token> insert_t;
            std::vector<insert_t> insert_list;
            insert_list.reserve(10000);

            for (std::size_t i = 0; i < (g.token_list_.size() - stride_ + 1); ++i)
            {
               int insert_index = -1;
               token t;

               switch (stride_)
               {
                  case 1 : insert_index = insert(g.token_list_[i],t);
                           break;

                  case 2 : insert_index = insert(g.token_list_[i], g.token_list_[i + 1], t);
                           break;

                  case 3 : insert_index = insert(g.token_list_[i], g.token_list_[i + 1], g.token_list_[i + 2], t);
                           break;

                  case 4 : insert_index = insert(g.token_list_[i], g.token_list_[i + 1], g.token_list_[i + 2], g.token_list_[i + 3], t);
                           break;

                  case 5 : insert_index = insert(g.token_list_[i], g.token_list_[i + 1], g.token_list_[i + 2], g.token_list_[i + 3], g.token_list_[i + 4], t);
                           break;
               }

               if ((insert_index >= 0) && (insert_index <= (static_cast<int>(stride_) + 1)))
               {
                  insert_list.push_back(insert_t(i, t));
                  changes++;
               }
            }

            if (!insert_list.empty())
            {
               generator::token_list_t token_list;

               std::size_t insert_index = 0;

               for (std::size_t i = 0; i < g.token_list_.size(); ++i)
               {
                  token_list.push_back(g.token_list_[i]);

                  if (
                       (insert_index < insert_list.size()) &&
                       (insert_list[insert_index].first == i)
                     )
                  {
                     token_list.push_back(insert_list[insert_index].second);
                     insert_index++;
                  }
               }

               std::swap(g.token_list_,token_list);
            }

            return changes;
         }

        token_joiner::token_joiner(const std::size_t& stride)
         : stride_(stride)
         {}

         std::size_t token_joiner::process(generator& g)
         {
            if (g.token_list_.empty())
               return 0;

            switch (stride_)
            {
               case 2  : return process_stride_2(g);
               case 3  : return process_stride_3(g);
               default : return 0;
            }
         }

         std::size_t token_joiner::process_stride_2(generator& g)
         {
            if (g.token_list_.size() < 2)
               return 0;

            std::size_t changes = 0;

            generator::token_list_t token_list;
            token_list.reserve(10000);

            for (int i = 0;  i < static_cast<int>(g.token_list_.size() - 1); ++i)
            {
               token t;

               for ( ; ; )
               {
                  if (!join(g[i], g[i + 1], t))
                  {
                     token_list.push_back(g[i]);
                     break;
                  }

                  token_list.push_back(t);

                  ++changes;

                  i+=2;

                  if (static_cast<std::size_t>(i) >= (g.token_list_.size() - 1))
                     break;
               }
            }

            token_list.push_back(g.token_list_.back());

            assert(token_list.size() <= g.token_list_.size());

            std::swap(token_list, g.token_list_);

            return changes;
         }

         std::size_t token_joiner::process_stride_3(generator& g)
         {
            if (g.token_list_.size() < 3)
               return 0;

            std::size_t changes = 0;

            generator::token_list_t token_list;
            token_list.reserve(10000);

            for (int i = 0;  i < static_cast<int>(g.token_list_.size() - 2); ++i)
            {
               token t;

               for ( ; ; )
               {
                  if (!join(g[i], g[i + 1], g[i + 2], t))
                  {
                     token_list.push_back(g[i]);
                     break;
                  }

                  token_list.push_back(t);

                  ++changes;

                  i+=3;

                  if (static_cast<std::size_t>(i) >= (g.token_list_.size() - 2))
                     break;
               }
            }

            token_list.push_back(*(g.token_list_.begin() + g.token_list_.size() - 2));
            token_list.push_back(*(g.token_list_.begin() + g.token_list_.size() - 1));

            assert(token_list.size() <= g.token_list_.size());

            std::swap(token_list, g.token_list_);

            return changes;
         }
         
      namespace helper
      {

         void dump(const lexer::generator& generator)
         {
            for (std::size_t i = 0; i < generator.size(); ++i)
            {
               const lexer::token& t = generator[i];
               printf("Token[%02d] @ %03d  %6s  -->  '%s'\n",
                      static_cast<int>(i),
                      static_cast<int>(t.position),
                      t.to_str(t.type).c_str(),
                      t.value.c_str());
            }
         }

            commutative_inserter::commutative_inserter()
            : lexer::token_inserter(2)
            {}

            void commutative_inserter::ignore_symbol(const std::string& symbol)
            {
               ignore_set_.insert(symbol);
            }

            int commutative_inserter::insert(const lexer::token& t0, const lexer::token& t1, lexer::token& new_token)
            {
               bool match         = false;
               new_token.type     = lexer::token::e_mul;
               new_token.value    = "*";
               new_token.position = t1.position;

               if (t0.type == lexer::token::e_symbol)
               {
                  if (ignore_set_.end() != ignore_set_.find(t0.value))
                  {
                     return -1;
                  }
                  else if (!t0.value.empty() && ('$' == t0.value[0]))
                  {
                     return -1;
                  }
               }

               if (t1.type == lexer::token::e_symbol)
               {
                  if (ignore_set_.end() != ignore_set_.find(t1.value))
                  {
                     return -1;
                  }
               }
               if      ((t0.type == lexer::token::e_number     ) && (t1.type == lexer::token::e_symbol     )) match = true;
               else if ((t0.type == lexer::token::e_number     ) && (t1.type == lexer::token::e_lbracket   )) match = true;
               else if ((t0.type == lexer::token::e_number     ) && (t1.type == lexer::token::e_lcrlbracket)) match = true;
               else if ((t0.type == lexer::token::e_number     ) && (t1.type == lexer::token::e_lsqrbracket)) match = true;
               else if ((t0.type == lexer::token::e_symbol     ) && (t1.type == lexer::token::e_number     )) match = true;
               else if ((t0.type == lexer::token::e_rbracket   ) && (t1.type == lexer::token::e_number     )) match = true;
               else if ((t0.type == lexer::token::e_rcrlbracket) && (t1.type == lexer::token::e_number     )) match = true;
               else if ((t0.type == lexer::token::e_rsqrbracket) && (t1.type == lexer::token::e_number     )) match = true;
               else if ((t0.type == lexer::token::e_rbracket   ) && (t1.type == lexer::token::e_symbol     )) match = true;
               else if ((t0.type == lexer::token::e_rcrlbracket) && (t1.type == lexer::token::e_symbol     )) match = true;
               else if ((t0.type == lexer::token::e_rsqrbracket) && (t1.type == lexer::token::e_symbol     )) match = true;
               else if ((t0.type == lexer::token::e_symbol     ) && (t1.type == lexer::token::e_symbol     )) match = true;

               return (match) ? 1 : -1;
            }

            operator_joiner::operator_joiner(const std::size_t& stride)
            : token_joiner(stride)
            {}

            bool operator_joiner::join(const lexer::token& t0, const lexer::token& t1, lexer::token& t)
            {
               // ': =' --> ':='
               if ((t0.type == lexer::token::e_colon) && (t1.type == lexer::token::e_eq))
               {
                  t.type     = lexer::token::e_assign;
                  t.value    = ":=";
                  t.position = t0.position;

                  return true;
               }
               // '+ =' --> '+='
               else if ((t0.type == lexer::token::e_add) && (t1.type == lexer::token::e_eq))
               {
                  t.type     = lexer::token::e_addass;
                  t.value    = "+=";
                  t.position = t0.position;

                  return true;
               }
               // '- =' --> '-='
               else if ((t0.type == lexer::token::e_sub) && (t1.type == lexer::token::e_eq))
               {
                  t.type     = lexer::token::e_subass;
                  t.value    = "-=";
                  t.position = t0.position;

                  return true;
               }
               // '* =' --> '*='
               else if ((t0.type == lexer::token::e_mul) && (t1.type == lexer::token::e_eq))
               {
                  t.type     = lexer::token::e_mulass;
                  t.value    = "*=";
                  t.position = t0.position;

                  return true;
               }
               // '/ =' --> '/='
               else if ((t0.type == lexer::token::e_div) && (t1.type == lexer::token::e_eq))
               {
                  t.type     = lexer::token::e_divass;
                  t.value    = "/=";
                  t.position = t0.position;

                  return true;
               }
               // '> =' --> '>='
               else if ((t0.type == lexer::token::e_gt) && (t1.type == lexer::token::e_eq))
               {
                  t.type     = lexer::token::e_gte;
                  t.value    = ">=";
                  t.position = t0.position;

                  return true;
               }
               // '< =' --> '<='
               else if ((t0.type == lexer::token::e_lt) && (t1.type == lexer::token::e_eq))
               {
                  t.type     = lexer::token::e_lte;
                  t.value    = "<=";
                  t.position = t0.position;

                  return true;
               }
               // '= =' --> '=='
               else if ((t0.type == lexer::token::e_eq) && (t1.type == lexer::token::e_eq))
               {
                  t.type     = lexer::token::e_eq;
                  t.value    = "==";
                  t.position = t0.position;

                  return true;
               }
               // '! =' --> '!='
               else if ((static_cast<details::char_t>(t0.type) == '!') && (t1.type == lexer::token::e_eq))
               {
                  t.type     = lexer::token::e_ne;
                  t.value    = "!=";
                  t.position = t0.position;

                  return true;
               }
               // '< >' --> '<>'
               else if ((t0.type == lexer::token::e_lt) && (t1.type == lexer::token::e_gt))
               {
                  t.type     = lexer::token::e_ne;
                  t.value    = "<>";
                  t.position = t0.position;

                  return true;
               }
               // '<= >' --> '<=>'
               else if ((t0.type == lexer::token::e_lte) && (t1.type == lexer::token::e_gt))
               {
                  t.type     = lexer::token::e_swap;
                  t.value    = "<=>";
                  t.position = t0.position;

                  return true;
               }
               // '+ -' --> '-'
               else if ((t0.type == lexer::token::e_add) && (t1.type == lexer::token::e_sub))
               {
                  t.type     = lexer::token::e_sub;
                  t.value    = "-";
                  t.position = t0.position;

                  return true;
               }
               // '- +' --> '-'
               else if ((t0.type == lexer::token::e_sub) && (t1.type == lexer::token::e_add))
               {
                  t.type     = lexer::token::e_sub;
                  t.value    = "-";
                  t.position = t0.position;

                  return true;
               }
               // '- -' --> '+'
               else if ((t0.type == lexer::token::e_sub) && (t1.type == lexer::token::e_sub))
               {
                  /*
                     Note: May need to reconsider this when wanting to implement
                     pre/postfix decrement operator
                  */
                  t.type     = lexer::token::e_add;
                  t.value    = "+";
                  t.position = t0.position;

                  return true;
               }
               else
                  return false;
            }

            bool operator_joiner::join(const lexer::token& t0,
                             const lexer::token& t1,
                             const lexer::token& t2,
                             lexer::token& t)
            {
               // '[ * ]' --> '[*]'
               if (
                    (t0.type == lexer::token::e_lsqrbracket) &&
                    (t1.type == lexer::token::e_mul        ) &&
                    (t2.type == lexer::token::e_rsqrbracket)
                  )
               {
                  t.type     = lexer::token::e_symbol;
                  t.value    = "[*]";
                  t.position = t0.position;

                  return true;
               }
               else
                  return false;
            }

            bracket_checker::bracket_checker()
            : token_scanner(1)
            , state_(true)
            {}

            bool bracket_checker::result()
            {
               if (!stack_.empty())
               {
                  lexer::token t;
                  t.value      = stack_.top().first;
                  t.position   = stack_.top().second;
                  error_token_ = t;
                  state_       = false;

                  return false;
               }
               else
                  return state_;
            }

            lexer::token bracket_checker::error_token()
            {
               return error_token_;
            }

            void bracket_checker::reset()
            {
               // Why? because msvc doesn't support swap properly.
               stack_ = std::stack<std::pair<char,std::size_t> >();
               state_ = true;
               error_token_.clear();
            }

            bool bracket_checker::operator() (const lexer::token& t)
            {
               if (
                    !t.value.empty()                       &&
                    (lexer::token::e_string != t.type)     &&
                    (lexer::token::e_symbol != t.type)     &&
                    Essa::Math::details::is_bracket(t.value[0])
                  )
               {
                  details::char_t c = t.value[0];

                  if      (t.type == lexer::token::e_lbracket   ) stack_.push(std::make_pair(')',t.position));
                  else if (t.type == lexer::token::e_lcrlbracket) stack_.push(std::make_pair('}',t.position));
                  else if (t.type == lexer::token::e_lsqrbracket) stack_.push(std::make_pair(']',t.position));
                  else if (Essa::Math::details::is_right_bracket(c))
                  {
                     if (stack_.empty())
                     {
                        state_       = false;
                        error_token_ = t;

                        return false;
                     }
                     else if (c != stack_.top().first)
                     {
                        state_       = false;
                        error_token_ = t;

                        return false;
                     }
                     else
                        stack_.pop();
                  }
               }

               return true;
            }
            
            template<typename T>
            numeric_checker<T>::numeric_checker()
            : token_scanner (1)
            , current_index_(0)
            {}

            template<typename T>
            bool numeric_checker<T>::result()
            {
               return error_list_.empty();
            }

            template<typename T>
            void numeric_checker<T>::reset()
            {
               error_list_.clear();
               current_index_ = 0;
            }

            template<typename T>
            bool numeric_checker<T>::operator() (const lexer::token& t)
            {
               if (token::e_number == t.type)
               {
                  T v;

                  if (!Essa::Math::details::string_to_real(t.value,v))
                  {
                     error_list_.push_back(current_index_);
                  }
               }

               ++current_index_;

               return true;
            }

            template<typename T>
            std::size_t numeric_checker<T>::error_count() const
            {
               return error_list_.size();
            }

            template<typename T>
            std::size_t numeric_checker<T>::error_index(const std::size_t& i)
            {
               if (i < error_list_.size())
                  return error_list_[i];
               else
                  return std::numeric_limits<std::size_t>::max();
            }

            template<typename T>
            void numeric_checker<T>::clear_errors()
            {
               error_list_.clear();
            }
        template class numeric_checker<int16_t>;
        template class numeric_checker<int32_t>;
        template class numeric_checker<int64_t>;
        template class numeric_checker<float>;
        template class numeric_checker<double>;
        template class numeric_checker<long double>;
        template class numeric_checker<std::complex<float>>;
        template class numeric_checker<std::complex<double>>;
        template class numeric_checker<std::complex<long double>>;

            bool symbol_replacer::remove(const std::string& target_symbol)
            {
               const replace_map_t::iterator itr = replace_map_.find(target_symbol);

               if (replace_map_.end() == itr)
                  return false;

               replace_map_.erase(itr);

               return true;
            }

            bool symbol_replacer::add_replace(const std::string& target_symbol,
                             const std::string& replace_symbol,
                             const lexer::token::token_type token_type)
            {
               const replace_map_t::iterator itr = replace_map_.find(target_symbol);

               if (replace_map_.end() != itr)
               {
                  return false;
               }

               replace_map_[target_symbol] = std::make_pair(replace_symbol,token_type);

               return true;
            }

            void symbol_replacer::clear()
            {
               replace_map_.clear();
            }

            bool symbol_replacer::modify(lexer::token& t)
            {
               if (lexer::token::e_symbol == t.type)
               {
                  if (replace_map_.empty())
                     return false;

                  const replace_map_t::iterator itr = replace_map_.find(t.value);

                  if (replace_map_.end() != itr)
                  {
                     t.value = itr->second.first;
                     t.type  = itr->second.second;

                     return true;
                  }
               }

               return false;
            }

            sequence_validator::sequence_validator()
            : lexer::token_scanner(2)
            {
               add_invalid(lexer::token::e_number, lexer::token::e_number);
               add_invalid(lexer::token::e_string, lexer::token::e_string);
               add_invalid(lexer::token::e_number, lexer::token::e_string);
               add_invalid(lexer::token::e_string, lexer::token::e_number);

               add_invalid_set1(lexer::token::e_assign );
               add_invalid_set1(lexer::token::e_shr    );
               add_invalid_set1(lexer::token::e_shl    );
               add_invalid_set1(lexer::token::e_lte    );
               add_invalid_set1(lexer::token::e_ne     );
               add_invalid_set1(lexer::token::e_gte    );
               add_invalid_set1(lexer::token::e_lt     );
               add_invalid_set1(lexer::token::e_gt     );
               add_invalid_set1(lexer::token::e_eq     );
               add_invalid_set1(lexer::token::e_comma  );
               add_invalid_set1(lexer::token::e_add    );
               add_invalid_set1(lexer::token::e_sub    );
               add_invalid_set1(lexer::token::e_div    );
               add_invalid_set1(lexer::token::e_mul    );
               add_invalid_set1(lexer::token::e_pow    );
               add_invalid_set1(lexer::token::e_colon  );
               add_invalid_set1(lexer::token::e_ternary);
            }

            bool sequence_validator::result()
            {
               return error_list_.empty();
            }

            bool sequence_validator::operator() (const lexer::token& t0, const lexer::token& t1)
            {
               const set_t::value_type p = std::make_pair(t0.type,t1.type);

               if (invalid_bracket_check(t0.type,t1.type))
               {
                  error_list_.push_back(std::make_pair(t0,t1));
               }
               else if (invalid_comb_.find(p) != invalid_comb_.end())
               {
                  error_list_.push_back(std::make_pair(t0,t1));
               }

               return true;
            }

            std::size_t sequence_validator::error_count() const
            {
               return error_list_.size();
            }

            std::pair<lexer::token,lexer::token> sequence_validator::error(const std::size_t index)
            {
               if (index < error_list_.size())
               {
                  return error_list_[index];
               }
               else
               {
                  static const lexer::token error_token;
                  return std::make_pair(error_token,error_token);
               }
            }

            void sequence_validator::clear_errors()
            {
               error_list_.clear();
            }

            void sequence_validator::add_invalid(const lexer::token::token_type base, const lexer::token::token_type t)
            {
               invalid_comb_.insert(std::make_pair(base,t));
            }

            void sequence_validator::add_invalid_set1(const lexer::token::token_type t)
            {
               add_invalid(t, lexer::token::e_assign);
               add_invalid(t, lexer::token::e_shr   );
               add_invalid(t, lexer::token::e_shl   );
               add_invalid(t, lexer::token::e_lte   );
               add_invalid(t, lexer::token::e_ne    );
               add_invalid(t, lexer::token::e_gte   );
               add_invalid(t, lexer::token::e_lt    );
               add_invalid(t, lexer::token::e_gt    );
               add_invalid(t, lexer::token::e_eq    );
               add_invalid(t, lexer::token::e_comma );
               add_invalid(t, lexer::token::e_div   );
               add_invalid(t, lexer::token::e_mul   );
               add_invalid(t, lexer::token::e_pow   );
               add_invalid(t, lexer::token::e_colon );
            }

            bool sequence_validator::invalid_bracket_check(const lexer::token::token_type base, const lexer::token::token_type t)
            {
               if (details::is_right_bracket(static_cast<details::char_t>(base)))
               {
                  switch (t)
                  {
                     case lexer::token::e_assign : return (']' != base);
                     case lexer::token::e_string : return (')' != base);
                     default                     : return false;
                  }
               }
               else if (details::is_left_bracket(static_cast<details::char_t>(base)))
               {
                  if (details::is_right_bracket(static_cast<details::char_t>(t)))
                     return false;
                  else if (details::is_left_bracket(static_cast<details::char_t>(t)))
                     return false;
                  else
                  {
                     switch (t)
                     {
                        case lexer::token::e_number  : return false;
                        case lexer::token::e_symbol  : return false;
                        case lexer::token::e_string  : return false;
                        case lexer::token::e_add     : return false;
                        case lexer::token::e_sub     : return false;
                        case lexer::token::e_colon   : return false;
                        case lexer::token::e_ternary : return false;
                        default                      : return true ;
                     }
                  }
               }
               else if (details::is_right_bracket(static_cast<details::char_t>(t)))
               {
                  switch (base)
                  {
                     case lexer::token::e_number  : return false;
                     case lexer::token::e_symbol  : return false;
                     case lexer::token::e_string  : return false;
                     case lexer::token::e_eof     : return false;
                     case lexer::token::e_colon   : return false;
                     case lexer::token::e_ternary : return false;
                     default                      : return true ;
                  }
               }
               else if (details::is_left_bracket(static_cast<details::char_t>(t)))
               {
                  switch (base)
                  {
                     case lexer::token::e_rbracket    : return true;
                     case lexer::token::e_rsqrbracket : return true;
                     case lexer::token::e_rcrlbracket : return true;
                     default                          : return false;
                  }
               }

               return false;
            }

            sequence_validator_3tokens::sequence_validator_3tokens()
            : lexer::token_scanner(3)
            {
               add_invalid(lexer::token::e_number , lexer::token::e_number , lexer::token::e_number);
               add_invalid(lexer::token::e_string , lexer::token::e_string , lexer::token::e_string);
               add_invalid(lexer::token::e_comma  , lexer::token::e_comma  , lexer::token::e_comma );

               add_invalid(lexer::token::e_add    , lexer::token::e_add    , lexer::token::e_add   );
               add_invalid(lexer::token::e_sub    , lexer::token::e_sub    , lexer::token::e_sub   );
               add_invalid(lexer::token::e_div    , lexer::token::e_div    , lexer::token::e_div   );
               add_invalid(lexer::token::e_mul    , lexer::token::e_mul    , lexer::token::e_mul   );
               add_invalid(lexer::token::e_pow    , lexer::token::e_pow    , lexer::token::e_pow   );

               add_invalid(lexer::token::e_add    , lexer::token::e_sub    , lexer::token::e_add   );
               add_invalid(lexer::token::e_sub    , lexer::token::e_add    , lexer::token::e_sub   );
               add_invalid(lexer::token::e_div    , lexer::token::e_mul    , lexer::token::e_div   );
               add_invalid(lexer::token::e_mul    , lexer::token::e_div    , lexer::token::e_mul   );
            }

            bool sequence_validator_3tokens::result()
            {
               return error_list_.empty();
            }

            bool sequence_validator_3tokens::operator() (const lexer::token& t0, const lexer::token& t1, const lexer::token& t2)
            {
               const set_t::value_type p = std::make_pair(t0.type,std::make_pair(t1.type,t2.type));

               if (invalid_comb_.find(p) != invalid_comb_.end())
               {
                  error_list_.push_back(std::make_pair(t0,t1));
               }

               return true;
            }

            std::size_t sequence_validator_3tokens::error_count() const
            {
               return error_list_.size();
            }

            std::pair<lexer::token,lexer::token> sequence_validator_3tokens::error(const std::size_t index)
            {
               if (index < error_list_.size())
               {
                  return error_list_[index];
               }
               else
               {
                  static const lexer::token error_token;
                  return std::make_pair(error_token,error_token);
               }
            }

            void sequence_validator_3tokens::clear_errors()
            {
               error_list_.clear();
            }

            void sequence_validator_3tokens::add_invalid(const token_t t0, const token_t t1, const token_t t2)
            {
               invalid_comb_.insert(std::make_pair(t0,std::make_pair(t1,t2)));
            }

            bool helper_assembly::register_scanner(lexer::token_scanner* scanner)
            {
               if (token_scanner_list.end() != std::find(token_scanner_list.begin(),
                                                         token_scanner_list.end  (),
                                                         scanner))
               {
                  return false;
               }

               token_scanner_list.push_back(scanner);

               return true;
            }

            bool helper_assembly::register_modifier(lexer::token_modifier* modifier)
            {
               if (token_modifier_list.end() != std::find(token_modifier_list.begin(),
                                                          token_modifier_list.end  (),
                                                          modifier))
               {
                  return false;
               }

               token_modifier_list.push_back(modifier);

               return true;
            }

            bool helper_assembly::register_joiner(lexer::token_joiner* joiner)
            {
               if (token_joiner_list.end() != std::find(token_joiner_list.begin(),
                                                        token_joiner_list.end  (),
                                                        joiner))
               {
                  return false;
               }

               token_joiner_list.push_back(joiner);

               return true;
            }

            bool helper_assembly::register_inserter(lexer::token_inserter* inserter)
            {
               if (token_inserter_list.end() != std::find(token_inserter_list.begin(),
                                                          token_inserter_list.end  (),
                                                          inserter))
               {
                  return false;
               }

               token_inserter_list.push_back(inserter);

               return true;
            }

            bool helper_assembly::run_modifiers(lexer::generator& g)
            {
               error_token_modifier = reinterpret_cast<lexer::token_modifier*>(0);

               for (std::size_t i = 0; i < token_modifier_list.size(); ++i)
               {
                  lexer::token_modifier& modifier = (*token_modifier_list[i]);

                  modifier.reset();
                  modifier.process(g);

                  if (!modifier.result())
                  {
                     error_token_modifier = token_modifier_list[i];

                     return false;
                  }
               }

               return true;
            }

            bool helper_assembly::run_joiners(lexer::generator& g)
            {
               error_token_joiner = reinterpret_cast<lexer::token_joiner*>(0);

               for (std::size_t i = 0; i < token_joiner_list.size(); ++i)
               {
                  lexer::token_joiner& joiner = (*token_joiner_list[i]);

                  joiner.reset();
                  joiner.process(g);

                  if (!joiner.result())
                  {
                     error_token_joiner = token_joiner_list[i];

                     return false;
                  }
               }

               return true;
            }

            bool helper_assembly::run_inserters(lexer::generator& g)
            {
               error_token_inserter = reinterpret_cast<lexer::token_inserter*>(0);

               for (std::size_t i = 0; i < token_inserter_list.size(); ++i)
               {
                  lexer::token_inserter& inserter = (*token_inserter_list[i]);

                  inserter.reset();
                  inserter.process(g);

                  if (!inserter.result())
                  {
                     error_token_inserter = token_inserter_list[i];

                     return false;
                  }
               }

               return true;
            }

            bool helper_assembly::run_scanners(lexer::generator& g)
            {
               error_token_scanner = reinterpret_cast<lexer::token_scanner*>(0);

               for (std::size_t i = 0; i < token_scanner_list.size(); ++i)
               {
                  lexer::token_scanner& scanner = (*token_scanner_list[i]);

                  scanner.reset();
                  scanner.process(g);

                  if (!scanner.result())
                  {
                     error_token_scanner = token_scanner_list[i];

                     return false;
                  }
               }

               return true;
            }
      }
   }
}


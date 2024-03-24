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
#include <cassert>
#include <set>
#include <stack>
#include <map>
#include <algorithm>

namespace Essa::Math{
   namespace lexer{
      class helper_interface
      {
      public:

         virtual void init()                     {              }
         virtual void reset()                    {              }
         virtual bool result()                   { return true; }
         virtual std::size_t process(generator&) { return 0;    }
         virtual ~helper_interface()             {              }
      };

      class token_scanner : public helper_interface
      {
      public:

         virtual ~token_scanner() {}

         explicit token_scanner(const std::size_t& stride);

         std::size_t process(generator& g) exprtk_override;

         virtual bool operator() (const token&);

         virtual bool operator() (const token&, const token&);

         virtual bool operator() (const token&, const token&, const token&);

         virtual bool operator() (const token&, const token&, const token&, const token&);

      private:

         const std::size_t stride_;
      }; // class token_scanner

      class token_modifier : public helper_interface
      {
      public:

         std::size_t process(generator& g) exprtk_override;

         virtual bool modify(token& t) = 0;
      };

      class token_inserter : public helper_interface
      {
      public:

         explicit token_inserter(const std::size_t& stride);

         std::size_t process(generator& g) exprtk_override;

         #define token_inserter_empty_body \
         {                                 \
            return -1;                     \
         }                                 \

         virtual int insert(const token&, token&)
         token_inserter_empty_body

         virtual int insert(const token&, const token&, token&)
         token_inserter_empty_body

         virtual int insert(const token&, const token&, const token&, token&)
         token_inserter_empty_body

         virtual int insert(const token&, const token&, const token&, const token&, token&)
         token_inserter_empty_body

         virtual int insert(const token&, const token&, const token&, const token&, const token&, token&)
         token_inserter_empty_body

         #undef token_inserter_empty_body

      private:

         const std::size_t stride_;
      };

      class token_joiner : public helper_interface
      {
      public:

         explicit token_joiner(const std::size_t& stride);

         std::size_t process(generator& g) exprtk_override;

         virtual bool join(const token&, const token&, token&)               { return false; }
         virtual bool join(const token&, const token&, const token&, token&) { return false; }

      private:

         std::size_t process_stride_2(generator& g);

         std::size_t process_stride_3(generator& g);

         const std::size_t stride_;
      };

      namespace helper
      {

         void dump(const lexer::generator& generator);
         class commutative_inserter : public lexer::token_inserter
         {
         public:

            using lexer::token_inserter::insert;

            commutative_inserter();

            void ignore_symbol(const std::string& symbol);

            int insert(const lexer::token& t0, const lexer::token& t1, lexer::token& new_token) exprtk_override;

         private:

            std::set<std::string,details::ilesscompare> ignore_set_;
         };

         class operator_joiner : public token_joiner
         {
         public:

            explicit operator_joiner(const std::size_t& stride);

            bool join(const lexer::token& t0, const lexer::token& t1, lexer::token& t) exprtk_override;

            bool join(const lexer::token& t0,
                             const lexer::token& t1,
                             const lexer::token& t2,
                             lexer::token& t) exprtk_override;
         };

         class bracket_checker : public lexer::token_scanner
         {
         public:

            using lexer::token_scanner::operator();

            bracket_checker();

            bool result();

            lexer::token error_token();

            void reset();

            bool operator() (const lexer::token& t);

         private:

            bool state_;
            std::stack<std::pair<char,std::size_t> > stack_;
            lexer::token error_token_;
         };

         template <typename T>
         class numeric_checker exprtk_final : public lexer::token_scanner
         {
         public:

            using lexer::token_scanner::operator();

            numeric_checker();

            bool result();

            void reset();

            bool operator() (const lexer::token& t);

            std::size_t error_count() const;

            std::size_t error_index(const std::size_t& i);

            void clear_errors();

         private:

            std::size_t current_index_;
            std::vector<std::size_t> error_list_;
         };

         class symbol_replacer : public lexer::token_modifier
         {
         private:

            typedef std::map<std::string,std::pair<std::string,token::token_type>,details::ilesscompare> replace_map_t;

         public:

            bool remove(const std::string& target_symbol);

            bool add_replace(const std::string& target_symbol,
                             const std::string& replace_symbol,
                             const lexer::token::token_type token_type = lexer::token::e_symbol);

            void clear();

         private:

            bool modify(lexer::token& t);

            replace_map_t replace_map_;
         };

         class sequence_validator exprtk_final : public lexer::token_scanner
         {
         private:

            typedef std::pair<lexer::token::token_type,lexer::token::token_type> token_pair_t;
            typedef std::set<token_pair_t> set_t;

         public:

            using lexer::token_scanner::operator();

            sequence_validator();

            bool result();

            bool operator() (const lexer::token& t0, const lexer::token& t1);

            std::size_t error_count() const;

            std::pair<lexer::token,lexer::token> error(const std::size_t index);

            void clear_errors();

         private:

            void add_invalid(const lexer::token::token_type base, const lexer::token::token_type t);

            void add_invalid_set1(const lexer::token::token_type t);

            bool invalid_bracket_check(const lexer::token::token_type base, const lexer::token::token_type t);

            set_t invalid_comb_;
            std::vector<std::pair<lexer::token,lexer::token> > error_list_;
         };

         class sequence_validator_3tokens exprtk_final : public lexer::token_scanner
         {
         private:

            typedef lexer::token::token_type token_t;
            typedef std::pair<token_t,std::pair<token_t,token_t> > token_triplet_t;
            typedef std::set<token_triplet_t> set_t;

         public:

            using lexer::token_scanner::operator();

            sequence_validator_3tokens();

            bool result();

            bool operator() (const lexer::token& t0, const lexer::token& t1, const lexer::token& t2);

            std::size_t error_count() const;

            std::pair<lexer::token,lexer::token> error(const std::size_t index);

            void clear_errors();

         private:

            void add_invalid(const token_t t0, const token_t t1, const token_t t2);

            set_t invalid_comb_;
            std::vector<std::pair<lexer::token,lexer::token> > error_list_;
         };

         struct helper_assembly
         {
            bool register_scanner(lexer::token_scanner* scanner);

            bool register_modifier(lexer::token_modifier* modifier);

            bool register_joiner(lexer::token_joiner* joiner);

            bool register_inserter(lexer::token_inserter* inserter);

            bool run_modifiers(lexer::generator& g);

            bool run_joiners(lexer::generator& g);

            bool run_inserters(lexer::generator& g);

            bool run_scanners(lexer::generator& g);

            std::vector<lexer::token_scanner*>  token_scanner_list;
            std::vector<lexer::token_modifier*> token_modifier_list;
            std::vector<lexer::token_joiner*>   token_joiner_list;
            std::vector<lexer::token_inserter*> token_inserter_list;

            lexer::token_scanner*  error_token_scanner;
            lexer::token_modifier* error_token_modifier;
            lexer::token_joiner*   error_token_joiner;
            lexer::token_inserter* error_token_inserter;
         };
      }
   }
}

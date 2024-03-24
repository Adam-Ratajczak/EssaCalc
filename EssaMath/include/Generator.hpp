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
#include "include/Lexer.hpp"
#include <vector>

namespace Essa::Math{
   namespace lexer{
      class generator
      {
      public:

         typedef token token_t;
         typedef std::vector<token_t> token_list_t;
         typedef token_list_t::iterator token_list_itr_t;
         typedef details::char_t char_t;

         generator();

         void clear();

         bool process(const std::string& str);

         bool empty() const;

         std::size_t size() const;

         void begin();

         void store();

         void restore();

         token_t& next_token();

         token_t& peek_next_token();

         token_t& operator[](const std::size_t& index);

         token_t operator[](const std::size_t& index) const;

         bool finished() const;

         void insert_front(token_t::token_type tk_type);

         std::string substr(const std::size_t& begin, const std::size_t& end) const;

         std::string remaining() const;

      private:

         bool is_end(details::char_cptr itr) const;

         bool is_comment_start(details::char_cptr itr) const;

         void skip_whitespace();

         void skip_comments();

         void scan_token();

         void scan_operator();

         void scan_symbol();

         void scan_number();

         void scan_special_function();

         void scan_string();

      private:

         token_list_t       token_list_;
         token_list_itr_t   token_itr_;
         token_list_itr_t   store_token_itr_;
         token_t            eof_token_;
         details::char_cptr base_itr_;
         details::char_cptr s_itr_;
         details::char_cptr s_end_;

         friend class token_scanner;
         friend class token_modifier;
         friend class token_inserter;
         friend class token_joiner;
      }; // class generator
   }
}

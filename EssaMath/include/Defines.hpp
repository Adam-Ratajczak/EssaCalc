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

#include <complex>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <functional>
#include <iterator>
#include <string>

namespace Essa::Math
{
   #ifdef exprtk_enable_debugging
     #define exprtk_debug(params) printf params
   #else
     #define exprtk_debug(params) (void)0
   #endif

   #define exprtk_error_location             \
   "exprtk.hpp:" + details::to_str(__LINE__) \

   #if defined(__GNUC__) && (__GNUC__  >= 7)

      #define exprtk_disable_fallthrough_begin                      \
      _Pragma ("GCC diagnostic push")                               \
      _Pragma ("GCC diagnostic ignored \"-Wimplicit-fallthrough\"") \

      #define exprtk_disable_fallthrough_end                        \
      _Pragma ("GCC diagnostic pop")                                \

   #else
      #define exprtk_disable_fallthrough_begin (void)0;
      #define exprtk_disable_fallthrough_end   (void)0;
   #endif

   #if __cplusplus >= 201103L
      #define exprtk_override override
      #define exprtk_final    final
      #define exprtk_delete   = delete
   #else
      #define exprtk_override
      #define exprtk_final
      #define exprtk_delete
   #endif

   namespace details
   {
      typedef char                   char_t;
      typedef char_t*                char_ptr;
      typedef char_t const*          char_cptr;
      typedef unsigned char          uchar_t;
      typedef uchar_t*               uchar_ptr;
      typedef uchar_t const*         uchar_cptr;
      typedef unsigned long long int _uint64_t;
      typedef long long int          _int64_t;
      typedef std::string::iterator  str_itr_t;

      extern bool disable_caseinsensitivity;
      extern bool disable_string_capabilities;
      extern bool disable_break_continue;
      extern bool enable_range_runtime_checks;
      extern bool disable_superscalar_unroll;
      extern bool disable_comments;
      extern bool disable_return_statement;
      extern bool disable_enhanced_features;
      extern bool disable_sc_andor;
      extern bool disable_cardinal_pow_optimisation;

      bool is_whitespace(const char_t c);
      bool is_operator_char(const char_t c);
      bool is_letter(const char_t c);
      bool is_digit(const char_t c);
      bool is_letter_or_digit(const char_t c);
      bool is_left_bracket(const char_t c);
      bool is_right_bracket(const char_t c);
      bool is_bracket(const char_t c);
      bool is_sign(const char_t c);
      bool is_invalid(const char_t c);
      bool is_valid_string_char(const char_t c);
      void case_normalise(std::string& s);
      bool imatch(const char_t c1, const char_t c2);
      bool imatch(const std::string& s1, const std::string& s2);

      struct ilesscompare
      {
         bool operator() (const std::string& s1, const std::string& s2) const;
      };

      bool is_valid_sf_symbol(const std::string& symbol);
      const char_t& front(const std::string& s);
      const char_t& back(const std::string& s);
      std::string to_str(int i);
      std::string to_str(std::size_t i);
      bool is_hex_digit(const uchar_t digit);
      uchar_t hex_to_bin(uchar_t h);
      bool parse_hex(str_itr_t& itr, str_itr_t end, char_t& result);
      bool cleanup_escapes(std::string& s);

      class build_string
      {
      public:

         explicit build_string(const std::size_t& initial_size = 64);

         build_string& operator << (const std::string& s);

         build_string& operator << (char_cptr s);

         operator std::string () const;

         std::string as_string() const;

      private:

         std::string data_;
      };

      extern const std::string reserved_words[];
      extern const std::size_t reserved_words_size;
      extern const std::string reserved_symbols[];
      extern const std::size_t reserved_symbols_size;
      extern const std::string base_function_list[];
      extern const std::size_t base_function_list_size;
      extern const std::string logic_ops_list[];
      extern const std::size_t logic_ops_list_size;
      extern const std::string cntrl_struct_list[];
      extern const std::size_t cntrl_struct_list_size;
      extern const std::string arithmetic_ops_list[];
      extern const std::size_t arithmetic_ops_list_size;
      extern const std::string assignment_ops_list[];
      extern const std::size_t assignment_ops_list_size;
      extern const std::string inequality_ops_list[];
      extern const std::size_t inequality_ops_list_size;

      bool is_reserved_word(const std::string& symbol);
      bool is_reserved_symbol(const std::string& symbol);
      bool is_base_function(const std::string& function_name);
      bool is_control_struct(const std::string& cntrl_strct);
      bool is_logic_opr(const std::string& lgc_opr);
      struct cs_match
      {
         static bool cmp(const char_t c0, const char_t c1);
      };

      struct cis_match
      {
         static bool cmp(const char_t c0, const char_t c1);
      };

      bool match_impl(const char* pattern_begin,
                      const char* pattern_end  ,
                      const char* data_begin   ,
                      const char* data_end     ,
                      const char& zero_or_more,
                      const char& exactly_one,
                      std::function<bool(char_t, char_t)> _foo);

      bool wc_match(const std::string& wild_card,
                           const std::string& str);

      bool wc_imatch(const std::string& wild_card,
                            const std::string& str);

      bool sequence_match(const std::string& pattern,
                                 const std::string& str,
                                 std::size_t&       diff_index,
                                 char_t&            diff_value);

      extern const double pow10[];
      extern const std::size_t pow10_size;

      namespace numeric
      {
         namespace constant
         {
            extern const double e;
            extern const double pi;
            extern const double pi_2;
            extern const double pi_4;
            extern const double pi_180;
            extern const double _1_pi;
            extern const double _2_pi;
            extern const double _180_pi;
            extern const double log2;
            extern const double sqrt2;
         }

         namespace details
         {
            struct unknown_type_tag { unknown_type_tag() {} };
            struct real_type_tag    { real_type_tag   () {} };
            struct int_type_tag     { int_type_tag    () {} };
            struct complex_type_tag     { complex_type_tag    () {} };

            template <typename T>
            struct number_type
            {
               typedef unknown_type_tag type;
               number_type() {}
            };

            #define exprtk_register_real_type_tag(T)             \
            template <> struct number_type<T>                    \
            { typedef real_type_tag type; number_type() {} };    \

            #define exprtk_register_int_type_tag(T)              \
            template <> struct number_type<T>                    \
            { typedef int_type_tag type; number_type() {} };     \

            #define exprtk_register_complex_type_tag(T)          \
            template <> struct number_type<T>                    \
            { typedef complex_type_tag type; number_type() {} }; \

            exprtk_register_real_type_tag(double      )
            exprtk_register_real_type_tag(long double )
            exprtk_register_real_type_tag(float       )

            exprtk_register_int_type_tag(int16_t      )
            exprtk_register_int_type_tag(int32_t      )
            exprtk_register_int_type_tag(int64_t      )

            exprtk_register_complex_type_tag(std::complex<float>)
            exprtk_register_complex_type_tag(std::complex<double>)
            exprtk_register_complex_type_tag(std::complex<long double>)

            #undef exprtk_register_real_type_tag
            #undef exprtk_register_int_type_tag
            #undef exprtk_register_complex_type_tag

            template <typename T>
            struct epsilon_type {};

            #define exprtk_define_epsilon_type(Type, Epsilon)      \
            template <> struct epsilon_type<Type>                  \
            {                                                      \
               static Type value()                          \
               {                                                   \
                  const Type epsilon = static_cast<Type>(Epsilon); \
                  return epsilon;                                  \
               }                                                   \
            };                                                     \

            exprtk_define_epsilon_type(int16_t                    , 0.0)
            exprtk_define_epsilon_type(int32_t                    , 0.0)
            exprtk_define_epsilon_type(int64_t                    , 0.0)
            exprtk_define_epsilon_type(float                      , 0.00000100000f)
            exprtk_define_epsilon_type(double                     , 0.000000000100)
            exprtk_define_epsilon_type(long double                , 0.000000000001)
            exprtk_define_epsilon_type(std::complex<float>        , 0.00000100000f)
            exprtk_define_epsilon_type(std::complex<double>       , 0.000000000100)
            exprtk_define_epsilon_type(std::complex<long double>  , 0.000000000001)

            #undef exprtk_define_epsilon_type
         }
      }

      template <typename T> struct is_const                { enum {result = 0}; };
      template <typename T> struct is_const <const T>      { enum {result = 1}; };
      template <typename T> struct is_const_ref            { enum {result = 0}; };
      template <typename T> struct is_const_ref <const T&> { enum {result = 1}; };
      template <typename T> struct is_ref                  { enum {result = 0}; };
      template <typename T> struct is_ref<T&>              { enum {result = 1}; };
      template <typename T> struct is_ref<const T&>        { enum {result = 0}; };

      template <std::size_t State>
      struct param_to_str { static std::string result() { static const std::string r("v"); return r; } };

      template <>
      struct param_to_str<0> { static std::string result() { static const std::string r("c"); return r; } };
   }
}

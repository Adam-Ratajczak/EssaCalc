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
#include "include/Token.hpp"
#include "include/ParserHelpers.hpp"
#include "include/OperatorHelpers.hpp"
#include "include/ExpressionNodes.hpp"
#include "include/ExpressionGenerator.hpp"
#include "include/NodeAllocator.hpp"
#include "include/Functions.hpp"
#include "include/SymbolTable.hpp"
#include "include/Expression.hpp"

namespace Essa::Math{
   namespace parser_error
   {
      enum error_mode
      {
         e_unknown = 0,
         e_syntax  = 1,
         e_token   = 2,
         e_numeric = 4,
         e_symtab  = 5,
         e_lexer   = 6,
         e_helper  = 7,
         e_parser  = 8
      };

      struct type
      {
         type();

         lexer::token token;
         error_mode mode;
         std::string diagnostic;
         std::string src_location;
         std::string error_line;
         std::size_t line_no;
         std::size_t column_no;
      };

      type make_error(const error_mode mode,
                             const std::string& diagnostic   = "",
                             const std::string& src_location = "");

      type make_error(const error_mode mode,
                             const lexer::token& tk,
                             const std::string& diagnostic   = "",
                             const std::string& src_location = "");

      std::string to_str(error_mode mode);

      bool update_error(type& error, const std::string& expression);

      void dump_error(const type& error);
   }

   namespace details
   {
      template <typename Parser>
      void disable_type_checking(Parser& p)
      {
         p.state_.type_check_enabled = false;
      }
   }

   template <typename T>
   class parser : public lexer::parser_helper
   {
      friend expression_generator<T>;
   private:

      enum precedence_level
      {
         e_level00, e_level01, e_level02, e_level03, e_level04,
         e_level05, e_level06, e_level07, e_level08, e_level09,
         e_level10, e_level11, e_level12, e_level13, e_level14
      };

      typedef const T&                                    cref_t;
      typedef const T                                     const_t;
      typedef ifunction<T>                                F;
      typedef ivararg_function<T>                         VAF;
      typedef igeneric_function<T>                        GF;
      typedef ifunction<T>                                ifunction_t;
      typedef ivararg_function<T>                         ivararg_function_t;
      typedef igeneric_function<T>                        igeneric_function_t;
      typedef details::expression_node<T>                 expression_node_t;
      typedef details::literal_node<T>                    literal_node_t;
      typedef details::unary_node<T>                      unary_node_t;
      typedef details::binary_node<T>                     binary_node_t;
      typedef details::trinary_node<T>                    trinary_node_t;
      typedef details::quaternary_node<T>                 quaternary_node_t;
      typedef details::conditional_node<T>                conditional_node_t;
      typedef details::cons_conditional_node<T>           cons_conditional_node_t;
      typedef details::while_loop_node<T>                 while_loop_node_t;
      typedef details::repeat_until_loop_node<T>          repeat_until_loop_node_t;
      typedef details::for_loop_node<T>                   for_loop_node_t;
      typedef details::while_loop_rtc_node<T>             while_loop_rtc_node_t;
      typedef details::repeat_until_loop_rtc_node<T>      repeat_until_loop_rtc_node_t;
      typedef details::for_loop_rtc_node<T>               for_loop_rtc_node_t;
      typedef details::while_loop_bc_node<T>              while_loop_bc_node_t;
      typedef details::repeat_until_loop_bc_node<T>       repeat_until_loop_bc_node_t;
      typedef details::for_loop_bc_node<T>                for_loop_bc_node_t;
      typedef details::while_loop_bc_rtc_node<T>          while_loop_bc_rtc_node_t;
      typedef details::repeat_until_loop_bc_rtc_node<T>   repeat_until_loop_bc_rtc_node_t;
      typedef details::for_loop_bc_rtc_node<T>            for_loop_bc_rtc_node_t;
      typedef details::switch_node<T>                     switch_node_t;
      typedef details::variable_node<T>                   variable_node_t;
      typedef details::vector_elem_node<T>                vector_elem_node_t;
      typedef details::rebasevector_elem_node<T>          rebasevector_elem_node_t;
      typedef details::rebasevector_celem_node<T>         rebasevector_celem_node_t;
      typedef details::vector_node<T>                     vector_node_t;
      typedef details::range_pack<T>                      range_t;
      typedef details::stringvar_node<T>                  stringvar_node_t;
      typedef details::string_literal_node<T>             string_literal_node_t;
      typedef details::string_range_node<T>               string_range_node_t;
      typedef details::const_string_range_node<T>         const_string_range_node_t;
      typedef details::generic_string_range_node<T>       generic_string_range_node_t;
      typedef details::string_concat_node<T>              string_concat_node_t;
      typedef details::assignment_string_node<T>          assignment_string_node_t;
      typedef details::assignment_string_range_node<T>    assignment_string_range_node_t;
      typedef details::conditional_string_node<T>         conditional_string_node_t;
      typedef details::cons_conditional_str_node<T>       cons_conditional_str_node_t;
      typedef details::assignment_node<T>                 assignment_node_t;
      typedef details::assignment_vec_elem_node<T>        assignment_vec_elem_node_t;
      typedef details::assignment_rebasevec_elem_node<T>  assignment_rebasevec_elem_node_t;
      typedef details::assignment_rebasevec_celem_node<T> assignment_rebasevec_celem_node_t;
      typedef details::assignment_vec_node<T>             assignment_vec_node_t;
      typedef details::assignment_vecvec_node<T>          assignment_vecvec_node_t;
      typedef details::conditional_vector_node<T>         conditional_vector_node_t;
      typedef details::scand_node<T>                      scand_node_t;
      typedef details::scor_node<T>                       scor_node_t;
      typedef lexer::token                                token_t;
      typedef expression_node_t*                          expression_node_ptr;
      typedef expression<T>                               expression_t;
      typedef symbol_table<T>                             symbol_table_t;
      typedef typename expression<T>::symtab_list_t       symbol_table_list_t;
      typedef details::vector_holder<T>*                  vector_holder_ptr;

      typedef typename details::functor_t<T> functor_t;
      typedef typename functor_t::qfunc_t    quaternary_functor_t;
      typedef typename functor_t::tfunc_t    trinary_functor_t;
      typedef typename functor_t::bfunc_t    binary_functor_t;
      typedef typename functor_t::ufunc_t    unary_functor_t;

      typedef details::operator_type operator_t;

      typedef std::map<operator_t, unary_functor_t  > unary_op_map_t;
      typedef std::map<operator_t, binary_functor_t > binary_op_map_t;
      typedef std::map<operator_t, trinary_functor_t> trinary_op_map_t;

      typedef std::map<std::string,std::pair<trinary_functor_t   ,operator_t> > sf3_map_t;
      typedef std::map<std::string,std::pair<quaternary_functor_t,operator_t> > sf4_map_t;

      typedef std::map<binary_functor_t,operator_t> inv_binary_op_map_t;
      typedef std::multimap<std::string,details::base_operation_t,details::ilesscompare> base_ops_map_t;
      typedef std::set<std::string,details::ilesscompare> disabled_func_set_t;

      typedef details::T0oT1_define<T, cref_t , cref_t > vov_t;
      typedef details::T0oT1_define<T, const_t, cref_t > cov_t;
      typedef details::T0oT1_define<T, cref_t , const_t> voc_t;

      typedef details::T0oT1oT2_define<T, cref_t , cref_t , cref_t > vovov_t;
      typedef details::T0oT1oT2_define<T, cref_t , cref_t , const_t> vovoc_t;
      typedef details::T0oT1oT2_define<T, cref_t , const_t, cref_t > vocov_t;
      typedef details::T0oT1oT2_define<T, const_t, cref_t , cref_t > covov_t;
      typedef details::T0oT1oT2_define<T, const_t, cref_t , const_t> covoc_t;
      typedef details::T0oT1oT2_define<T, const_t, const_t, cref_t > cocov_t;
      typedef details::T0oT1oT2_define<T, cref_t , const_t, const_t> vococ_t;

      typedef details::T0oT1oT2oT3_define<T, cref_t , cref_t , cref_t , cref_t > vovovov_t;
      typedef details::T0oT1oT2oT3_define<T, cref_t , cref_t , cref_t , const_t> vovovoc_t;
      typedef details::T0oT1oT2oT3_define<T, cref_t , cref_t , const_t, cref_t > vovocov_t;
      typedef details::T0oT1oT2oT3_define<T, cref_t , const_t, cref_t , cref_t > vocovov_t;
      typedef details::T0oT1oT2oT3_define<T, const_t, cref_t , cref_t , cref_t > covovov_t;

      typedef details::T0oT1oT2oT3_define<T, const_t, cref_t , const_t, cref_t > covocov_t;
      typedef details::T0oT1oT2oT3_define<T, cref_t , const_t, cref_t , const_t> vocovoc_t;
      typedef details::T0oT1oT2oT3_define<T, const_t, cref_t , cref_t , const_t> covovoc_t;
      typedef details::T0oT1oT2oT3_define<T, cref_t , const_t, const_t, cref_t > vococov_t;

      typedef results_context<T> results_context_t;

      typedef parser_helper prsrhlpr_t;

      struct scope_element
      {
         enum element_type
         {
            e_none    ,
            e_variable,
            e_vector  ,
            e_vecelem ,
            e_string
         };

         typedef details::vector_holder<T> vector_holder_t;
         typedef variable_node_t*          variable_node_ptr;
         typedef vector_holder_t*          vector_holder_ptr;
         typedef expression_node_t*        expression_node_ptr;
         typedef stringvar_node_t*         stringvar_node_ptr;

         scope_element();

         bool operator < (const scope_element& se) const;

         void clear();

         std::string  name;
         std::size_t  size;
         std::size_t  index;
         std::size_t  depth;
         std::size_t  ref_count;
         std::size_t  ip_index;
         element_type type;
         bool         active;
         void*        data;
         expression_node_ptr var_node;
         vector_holder_ptr   vec_node;
         stringvar_node_ptr str_node;
      };

      class scope_element_manager
      {
      public:

         typedef expression_node_t* expression_node_ptr;
         typedef variable_node_t*   variable_node_ptr;
         typedef parser<T>          parser_t;

         explicit scope_element_manager(parser<T>& p);

         std::size_t size() const;

         bool empty() const;

         scope_element& get_element(const std::size_t& index);

         scope_element& get_element(const std::string& var_name,
                                           const std::size_t index = std::numeric_limits<std::size_t>::max());

         scope_element& get_active_element(const std::string& var_name,
                                                  const std::size_t index = std::numeric_limits<std::size_t>::max());

         bool add_element(const scope_element& se);

         void deactivate(const std::size_t& scope_depth);

         void free_element(scope_element& se);

         void cleanup();

         std::size_t next_ip_index();

         expression_node_ptr get_variable(const T& v);

      private:

         scope_element_manager(const scope_element_manager&) exprtk_delete;
         scope_element_manager& operator=(const scope_element_manager&) exprtk_delete;

         parser_t& parser_;
         std::vector<scope_element> element_;
         scope_element null_element_;
         std::size_t input_param_cnt_;
      };

      class scope_handler
      {
      public:

         typedef parser<T> parser_t;

         explicit scope_handler(parser<T>& p);

        ~scope_handler();

      private:

         scope_handler(const scope_handler&) exprtk_delete;
         scope_handler& operator=(const scope_handler&) exprtk_delete;

         parser_t& parser_;
      };

      template <typename T_>
      struct halfopen_range_policy
      {
         static bool is_within(const T_& v, const T_& begin, const T_& end)
         {
            assert(begin <= end);
            return (begin <= v) && (v < end);
         }

         static bool is_less(const T_& v, const T_& begin)
         {
            return (v < begin);
         }

         static bool is_greater(const T_& v, const T_& end)
         {
            return (end <= v);
         }

         static bool end_inclusive()
         {
            return false;
         }
      };

      template <typename T_>
      struct closed_range_policy
      {
         static bool is_within(const T_& v, const T_& begin, const T_& end)
         {
            assert(begin <= end);
            return (begin <= v) && (v <= end);
         }

         static bool is_less(const T_& v, const T_& begin)
         {
            return (v < begin);
         }

         static bool is_greater(const T_& v, const T_& end)
         {
            return (end < v);
         }

         static bool end_inclusive()
         {
            return true;
         }
      };

      template <typename IntervalPointType,
                typename RangePolicy = halfopen_range_policy<IntervalPointType> >
      class interval_container_t
      {
      public:

         typedef IntervalPointType interval_point_t;
         typedef std::pair<interval_point_t, interval_point_t> interval_t;
         typedef std::map<interval_point_t, interval_t> interval_map_t;
         typedef typename interval_map_t::const_iterator interval_map_citr_t;

         std::size_t size() const
         {
            return interval_map_.size();
         }

         void reset()
         {
            interval_map_.clear();
         }

         bool in_interval(const interval_point_t point, interval_t& interval) const
         {
            interval_map_citr_t itr = RangePolicy::end_inclusive() ?
                                      interval_map_.lower_bound(point):
                                      interval_map_.upper_bound(point);

            for (; itr != interval_map_.end(); ++itr)
            {
               const interval_point_t& begin = itr->second.first;
               const interval_point_t& end   = itr->second.second;

               if (RangePolicy::is_within(point, begin, end))
               {
                  interval = interval_t(begin,end);
                  return true;
               }
               else if (RangePolicy::is_greater(point, end))
               {
                  break;
               }
            }

            return false;
         }

         bool in_interval(const interval_point_t point) const
         {
            interval_t interval;
            return in_interval(point,interval);
         }

         bool add_interval(const interval_point_t begin, const interval_point_t end)
         {
            if ((end <= begin) || in_interval(begin) || in_interval(end))
            {
               return false;
            }

            interval_map_[end] = std::make_pair(begin, end);

            return true;
         }

         bool add_interval(const interval_t interval)
         {
            return add_interval(interval.first, interval.second);
         }

      private:

         interval_map_t interval_map_;
      };

      class stack_limit_handler
      {
      public:

         typedef parser<T> parser_t;

         explicit stack_limit_handler(parser<T>& p);

        ~stack_limit_handler();

         bool operator!();

      private:

         stack_limit_handler(const stack_limit_handler&) exprtk_delete;
         stack_limit_handler& operator=(const stack_limit_handler&) exprtk_delete;

         parser_t& parser_;
         bool limit_exceeded_;
      };

      struct symtab_store
      {
         symbol_table_list_t symtab_list_;

         typedef typename symbol_table_t::local_data_t local_data_t;
         typedef typename symbol_table_t::variable_ptr variable_ptr;
         typedef typename symbol_table_t::function_ptr function_ptr;
         typedef typename symbol_table_t::stringvar_ptr stringvar_ptr;
         typedef typename symbol_table_t::vector_holder_ptr    vector_holder_ptr;
         typedef typename symbol_table_t::vararg_function_ptr  vararg_function_ptr;
         typedef typename symbol_table_t::generic_function_ptr generic_function_ptr;

         struct variable_context
         {
            variable_context()
            : symbol_table(0)
            , variable(0)
            {}

            const symbol_table_t* symbol_table;
            variable_ptr variable;
         };

         struct vector_context
         {
            vector_context()
            : symbol_table(0)
            , vector_holder(0)
            {}

            const symbol_table_t* symbol_table;
            vector_holder_ptr vector_holder;
         };

         struct string_context
         {
            string_context()
            : symbol_table(0)
            , str_var(0)
            {}

            const symbol_table_t* symbol_table;
            stringvar_ptr str_var;
         };

         bool empty() const;

         void clear();

         bool valid() const;

         bool valid_symbol(const std::string& symbol) const;

         bool valid_function_name(const std::string& symbol) const;

         variable_context get_variable_context(const std::string& variable_name) const;

         variable_ptr get_variable(const std::string& variable_name) const;

         variable_ptr get_variable(const T& var_ref) const;

         string_context get_string_context(const std::string& string_name) const;

         stringvar_ptr get_stringvar(const std::string& string_name) const;

         function_ptr get_function(const std::string& function_name) const;

         vararg_function_ptr get_vararg_function(const std::string& vararg_function_name) const;

         generic_function_ptr get_generic_function(const std::string& function_name) const;

         generic_function_ptr get_string_function(const std::string& function_name) const;

         generic_function_ptr get_overload_function(const std::string& function_name) const;

         vector_context get_vector_context(const std::string& vector_name) const;

         vector_holder_ptr get_vector(const std::string& vector_name) const;

         bool is_constant_node(const std::string& symbol_name) const;

         bool is_constant_string(const std::string& symbol_name) const;

         bool symbol_exists(const std::string& symbol) const;

         bool is_variable(const std::string& variable_name) const;

         bool is_stringvar(const std::string& stringvar_name) const;

         bool is_conststr_stringvar(const std::string& symbol_name) const;

         bool is_function(const std::string& function_name) const;

         bool is_vararg_function(const std::string& vararg_function_name) const;

         bool is_vector(const std::string& vector_name) const;

         std::string get_variable_name(const expression_node_ptr& ptr) const;

         std::string get_vector_name(const vector_holder_ptr& ptr) const;

         std::string get_stringvar_name(const expression_node_ptr& ptr) const;

         std::string get_conststr_stringvar_name(const expression_node_ptr& ptr) const;

         local_data_t& local_data(const std::size_t& index = 0);

         const local_data_t& local_data(const std::size_t& index = 0) const;

         symbol_table_t& get_symbol_table(const std::size_t& index = 0);
      };

      struct parser_state
      {
         parser_state();

         void reset();

         #ifndef exprtk_enable_debugging
         void activate_side_effect(const std::string&);
         #else
         void activate_side_effect(const std::string& source);
         #endif

         bool parsing_return_stmt;
         bool parsing_break_stmt;
         bool return_stmt_present;
         bool side_effect_present;
         bool type_check_enabled;
         std::size_t scope_depth;
         std::size_t stack_depth;
         std::size_t parsing_loop_stmt_count;
      };

   public:

      struct unknown_symbol_resolver
      {

         enum usr_symbol_type
         {
            e_usr_unknown_type  = 0,
            e_usr_variable_type = 1,
            e_usr_constant_type = 2
         };

         enum usr_mode
         {
            e_usrmode_default  = 0,
            e_usrmode_extended = 1
         };

         usr_mode mode;

         unknown_symbol_resolver(const usr_mode m = e_usrmode_default)
         : mode(m)
         {}

         virtual ~unknown_symbol_resolver() {}

         virtual bool process(const std::string& /*unknown_symbol*/,
                              usr_symbol_type&   st,
                              T&                 default_value,
                              std::string&       error_message);

         virtual bool process(const std::string& /* unknown_symbol */,
                              symbol_table_t&    /* symbol_table   */,
                              std::string&       /* error_message  */);
      };

      enum collect_type
      {
         e_ct_none        = 0,
         e_ct_variables   = 1,
         e_ct_functions   = 2,
         e_ct_assignments = 4
      };

      enum symbol_type
      {
         e_st_unknown        = 0,
         e_st_variable       = 1,
         e_st_vector         = 2,
         e_st_vecelem        = 3,
         e_st_string         = 4,
         e_st_function       = 5,
         e_st_local_variable = 6,
         e_st_local_vector   = 7,
         e_st_local_string   = 8
      };

      class dependent_entity_collector
      {
      public:

         typedef std::pair<std::string,symbol_type> symbol_t;
         typedef std::vector<symbol_t> symbol_list_t;

         dependent_entity_collector(const std::size_t options = e_ct_none);

         template <typename Allocator,
                   template <typename, typename> class Sequence>
         std::size_t symbols(Sequence<symbol_t,Allocator>& symbols_list)
         {
            if (!collect_variables_ && !collect_functions_)
               return 0;
            else if (symbol_name_list_.empty())
               return 0;

            for (std::size_t i = 0; i < symbol_name_list_.size(); ++i)
            {
               details::case_normalise(symbol_name_list_[i].first);
            }

            std::sort(symbol_name_list_.begin(),symbol_name_list_.end());

            std::unique_copy(symbol_name_list_.begin(),
                             symbol_name_list_.end  (),
                             std::back_inserter(symbols_list));

            return symbols_list.size();
         }

         template <typename Allocator,
                   template <typename, typename> class Sequence>
         std::size_t assignment_symbols(Sequence<symbol_t,Allocator>& assignment_list)
         {
            if (!collect_assignments_)
               return 0;
            else if (assignment_name_list_.empty())
               return 0;

            for (std::size_t i = 0; i < assignment_name_list_.size(); ++i)
            {
               details::case_normalise(assignment_name_list_[i].first);
            }

            std::sort(assignment_name_list_.begin(),assignment_name_list_.end());

            std::unique_copy(assignment_name_list_.begin(),
                             assignment_name_list_.end  (),
                             std::back_inserter(assignment_list));

            return assignment_list.size();
         }

         void clear();

         bool& collect_variables();

         bool& collect_functions();

         bool& collect_assignments();

         bool return_present() const;

         bool final_stmt_return() const;

         typedef std::vector<std::string> retparam_list_t;

         retparam_list_t return_param_type_list() const;

         void add_symbol(const std::string& symbol, const symbol_type st);

         void add_assignment(const std::string& symbol, const symbol_type st);

      private:

         std::size_t options_;
         bool collect_variables_;
         bool collect_functions_;
         bool collect_assignments_;
         bool return_present_;
         bool final_stmt_return_;
         symbol_list_t symbol_name_list_;
         symbol_list_t assignment_name_list_;
         retparam_list_t retparam_list_;

         friend class parser<T>;
      };

      class settings_store
      {
      private:

         typedef std::set<std::string,details::ilesscompare> disabled_entity_set_t;
         typedef disabled_entity_set_t::iterator des_itr_t;

      public:

         enum settings_compilation_options
         {
            e_unknown              =    0,
            e_replacer             =    1,
            e_joiner               =    2,
            e_numeric_check        =    4,
            e_bracket_check        =    8,
            e_sequence_check       =   16,
            e_commutative_check    =   32,
            e_strength_reduction   =   64,
            e_disable_vardef       =  128,
            e_collect_vars         =  256,
            e_collect_funcs        =  512,
            e_collect_assings      = 1024,
            e_disable_usr_on_rsrvd = 2048,
            e_disable_zero_return  = 4096
         };

         enum settings_base_funcs
         {
            e_bf_unknown = 0, e_bf_abs,         e_bf_acos,        e_bf_acosh,
            e_bf_and,         e_bf_asin,        e_bf_asinh,       e_bf_atan,
            e_bf_atan2,       e_bf_atanh,       e_bf_avg,         e_bf_break,
            e_bf_case,        e_bf_ceil,        e_bf_clamp,       e_bf_continue,
            e_bf_cos,         e_bf_cosh,        e_bf_cot,         e_bf_csc,
            e_bf_default,     e_bf_deg2grad,    e_bf_deg2rad,     e_bf_equal,
            e_bf_erf,         e_bf_erfc,        e_bf_exp,         e_bf_expm1,
            e_bf_false,       e_bf_floor,       e_bf_for,         e_bf_frac,
            e_bf_grad2deg,    e_bf_hypot,       e_bf_iclamp,      e_bf_if,
            e_bf_else,        e_bf_ilike,       e_bf_in,          e_bf_inrange,
            e_bf_like,        e_bf_log,         e_bf_log10,       e_bf_log2,
            e_bf_logn,        e_bf_log1p,       e_bf_mand,        e_bf_max,
            e_bf_min,         e_bf_mod,         e_bf_mor,         e_bf_mul,
            e_bf_ncdf,        e_bf_nand,        e_bf_nor,         e_bf_not,
            e_bf_not_equal,   e_bf_null,        e_bf_or,          e_bf_pow,
            e_bf_rad2deg,     e_bf_repeat,      e_bf_return,      e_bf_root,
            e_bf_round,       e_bf_roundn,      e_bf_sec,         e_bf_sgn,
            e_bf_shl,         e_bf_shr,         e_bf_sin,         e_bf_sinc,
            e_bf_sinh,        e_bf_sqrt,        e_bf_sum,         e_bf_swap,
            e_bf_switch,      e_bf_tan,         e_bf_tanh,        e_bf_true,
            e_bf_trunc,       e_bf_until,       e_bf_var,         e_bf_while,
            e_bf_xnor,        e_bf_xor,         e_bf_and2,        e_bf_or2
         };

         enum settings_control_structs
         {
            e_ctrl_unknown = 0,
            e_ctrl_ifelse,
            e_ctrl_switch,
            e_ctrl_for_loop,
            e_ctrl_while_loop,
            e_ctrl_repeat_loop,
            e_ctrl_return
         };

         enum settings_logic_opr
         {
            e_logic_unknown = 0,
            e_logic_and, e_logic_nand , e_logic_nor ,
            e_logic_not, e_logic_or   , e_logic_xnor,
            e_logic_xor, e_logic_scand, e_logic_scor
         };

         enum settings_arithmetic_opr
         {
            e_arith_unknown = 0,
            e_arith_add, e_arith_sub, e_arith_mul,
            e_arith_div, e_arith_mod, e_arith_pow
         };

         enum settings_assignment_opr
         {
            e_assign_unknown = 0,
            e_assign_assign, e_assign_addass, e_assign_subass,
            e_assign_mulass, e_assign_divass, e_assign_modass
         };

         enum settings_inequality_opr
         {
            e_ineq_unknown = 0,
            e_ineq_lt   , e_ineq_lte, e_ineq_eq    ,
            e_ineq_equal, e_ineq_ne , e_ineq_nequal,
            e_ineq_gte  , e_ineq_gt
         };

         static const std::size_t compile_all_opts;

         settings_store(const std::size_t compile_options = compile_all_opts);

         settings_store& enable_all_base_functions();

         settings_store& enable_all_control_structures();

         settings_store& enable_all_logic_ops();

         settings_store& enable_all_arithmetic_ops();

         settings_store& enable_all_assignment_ops();

         settings_store& enable_all_inequality_ops();

         settings_store& enable_local_vardef();

         settings_store& disable_all_base_functions();

         settings_store& disable_all_control_structures();

         settings_store& disable_all_logic_ops();

         settings_store& disable_all_arithmetic_ops();

         settings_store& disable_all_assignment_ops();

         settings_store& disable_all_inequality_ops();

         settings_store& disable_local_vardef();

         bool replacer_enabled           () const;
         bool commutative_check_enabled  () const;
         bool joiner_enabled             () const;
         bool numeric_check_enabled      () const;
         bool bracket_check_enabled      () const;
         bool sequence_check_enabled     () const;
         bool strength_reduction_enabled () const;
         bool collect_variables_enabled  () const;
         bool collect_functions_enabled  () const;
         bool collect_assignments_enabled() const;
         bool vardef_disabled            () const;
         bool rsrvd_sym_usr_disabled     () const;
         bool zero_return_disabled       () const;

         bool function_enabled(const std::string& function_name) const;

         bool control_struct_enabled(const std::string& control_struct) const;

         bool logic_enabled(const std::string& logic_operation) const;

         bool arithmetic_enabled(const details::operator_type& arithmetic_operation) const;

         bool assignment_enabled(const details::operator_type& assignment) const;

         bool inequality_enabled(const details::operator_type& inequality) const;

         bool function_disabled(const std::string& function_name) const;

         bool control_struct_disabled(const std::string& control_struct) const;

         bool logic_disabled(const std::string& logic_operation) const;

         bool assignment_disabled(const details::operator_type assignment_operation) const;

         bool logic_disabled(const details::operator_type logic_operation) const;

         bool arithmetic_disabled(const details::operator_type arithmetic_operation) const;

         bool inequality_disabled(const details::operator_type& inequality) const;

         settings_store& disable_base_function(settings_base_funcs bf);

         settings_store& disable_control_structure(settings_control_structs ctrl_struct);

         settings_store& disable_logic_operation(settings_logic_opr logic);

         settings_store& disable_arithmetic_operation(settings_arithmetic_opr arithmetic);

         settings_store& disable_assignment_operation(settings_assignment_opr assignment);

         settings_store& disable_inequality_operation(settings_inequality_opr inequality);

         settings_store& enable_base_function(settings_base_funcs bf);

         settings_store& enable_control_structure(settings_control_structs ctrl_struct);

         settings_store& enable_logic_operation(settings_logic_opr logic);

         settings_store& enable_arithmetic_operation(settings_arithmetic_opr arithmetic);

         settings_store& enable_assignment_operation(settings_assignment_opr assignment);

         settings_store& enable_inequality_operation(settings_inequality_opr inequality);

         void set_max_stack_depth(const std::size_t max_stack_depth);

         void set_max_node_depth(const std::size_t max_node_depth);

      private:

         void load_compile_options(const std::size_t compile_options);

         std::string assign_opr_to_string(details::operator_type opr) const;

         std::string arith_opr_to_string(details::operator_type opr) const;

         std::string inequality_opr_to_string(details::operator_type opr) const;

         std::string logic_opr_to_string(details::operator_type opr) const;

         bool enable_replacer_;
         bool enable_joiner_;
         bool enable_numeric_check_;
         bool enable_bracket_check_;
         bool enable_sequence_check_;
         bool enable_commutative_check_;
         bool enable_strength_reduction_;
         bool enable_collect_vars_;
         bool enable_collect_funcs_;
         bool enable_collect_assings_;
         bool disable_vardef_;
         bool disable_rsrvd_sym_usr_;
         bool disable_zero_return_;

         disabled_entity_set_t disabled_func_set_ ;
         disabled_entity_set_t disabled_ctrl_set_ ;
         disabled_entity_set_t disabled_logic_set_;
         disabled_entity_set_t disabled_arithmetic_set_;
         disabled_entity_set_t disabled_assignment_set_;
         disabled_entity_set_t disabled_inequality_set_;

         std::size_t max_stack_depth_;
         std::size_t max_node_depth_;

         friend class parser<T>;
      };

      typedef settings_store settings_t;

      parser(const settings_t& settings = settings_t());

     ~parser() {}

      void init_precompilation();

      bool compile(const std::string& expression_string, expression<T>& expr);

      expression_t compile(const std::string& expression_string, symbol_table_t& symtab);

      bool run_assemblies();

      settings_store& settings()
      {
         return settings_;
      }

      parser_error::type get_error(const std::size_t& index) const;

      std::string error() const;

      std::size_t error_count() const;

      dependent_entity_collector& dec();
      
      void process_lexer_errors();

      bool replace_symbol(const std::string& old_symbol, const std::string& new_symbol);

      bool remove_replace_symbol(const std::string& symbol);

      void enable_unknown_symbol_resolver(unknown_symbol_resolver* usr = reinterpret_cast<unknown_symbol_resolver*>(0));

      void enable_unknown_symbol_resolver(unknown_symbol_resolver& usr);

      void disable_unknown_symbol_resolver();

      void register_loop_runtime_check(loop_runtime_check& lrtchk);

      void clear_loop_runtime_check();

      bool simplify_unary_negation_branch(expression_node_ptr& node);

   private:

      bool valid_base_operation(const std::string& symbol) const;

      bool valid_vararg_operation(const std::string& symbol) const;

      bool is_invalid_logic_operation(const details::operator_type operation) const;

      bool is_invalid_arithmetic_operation(const details::operator_type operation) const;

      bool is_invalid_assignment_operation(const details::operator_type operation) const;

      bool is_invalid_inequality_operation(const details::operator_type operation) const;

      #ifdef exprtk_enable_debugging
      void next_token();
      #endif

      expression_node_ptr parse_corpus();

      std::string construct_subexpr(lexer::token& begin_token, lexer::token& end_token);

      static const precedence_level default_precedence;

      struct state_t
      {
         void set(const precedence_level& l,
                         const precedence_level& r,
                         const details::operator_type& o);

         void reset();

         precedence_level left;
         precedence_level right;
         details::operator_type operation;
      };

      expression_node_ptr parse_expression(precedence_level precedence = e_level00);

      static expression_node_ptr error_node();

      struct scoped_expression_delete
      {
         scoped_expression_delete(parser<T>& pr, expression_node_ptr& expression);

        ~scoped_expression_delete();

         bool delete_ptr;
         parser<T>& parser_;
         expression_node_ptr& expression_;

      private:

         scoped_expression_delete(const scoped_expression_delete&) exprtk_delete;
         scoped_expression_delete& operator=(const scoped_expression_delete&) exprtk_delete;
      };

      template <typename Type, std::size_t N>
      struct scoped_delete
      {
         typedef Type* ptr_t;

         scoped_delete(parser<T>& pr, ptr_t& p)
         : delete_ptr(true)
         , parser_(pr)
         , p_(&p)
         {}

         scoped_delete(parser<T>& pr, ptr_t (&p)[N])
         : delete_ptr(true)
         , parser_(pr)
         , p_(&p[0])
         {}

        ~scoped_delete()
         {
            if (delete_ptr)
            {
               for (std::size_t i = 0; i < N; ++i)
               {
                  free_node(parser_.node_allocator_, p_[i]);
               }
            }
         }

         bool delete_ptr;
         parser<T>& parser_;
         ptr_t* p_;

      private:

         scoped_delete(const scoped_delete<Type,N>&) exprtk_delete;
         scoped_delete<Type,N>& operator=(const scoped_delete<Type,N>&) exprtk_delete;
      };

      template <typename Type>
      struct scoped_deq_delete
      {
         typedef Type* ptr_t;

         scoped_deq_delete(parser<T>& pr, std::deque<ptr_t>& deq)
         : delete_ptr(true)
         , parser_(pr)
         , deq_(deq)
         {}

        ~scoped_deq_delete()
         {
            if (delete_ptr && !deq_.empty())
            {
               for (std::size_t i = 0; i < deq_.size(); ++i)
               {
                  free_node(parser_.node_allocator_,deq_[i]);
               }

               deq_.clear();
            }
         }

         bool delete_ptr;
         parser<T>& parser_;
         std::deque<ptr_t>& deq_;

      private:

         scoped_deq_delete(const scoped_deq_delete<Type>&) exprtk_delete;
         scoped_deq_delete<Type>& operator=(const scoped_deq_delete<Type>&) exprtk_delete;
      };

      template <typename Type>
      struct scoped_vec_delete
      {
         typedef Type* ptr_t;

         scoped_vec_delete(parser<T>& pr, std::vector<ptr_t>& vec)
         : delete_ptr(true)
         , parser_(pr)
         , vec_(vec)
         {}

        ~scoped_vec_delete()
         {
            if (delete_ptr && !vec_.empty())
            {
               for (std::size_t i = 0; i < vec_.size(); ++i)
               {
                  free_node(parser_.node_allocator_,vec_[i]);
               }

               vec_.clear();
            }
         }

         bool delete_ptr;
         parser<T>& parser_;
         std::vector<ptr_t>& vec_;

      private:

         scoped_vec_delete(const scoped_vec_delete<Type>&) exprtk_delete;
         scoped_vec_delete<Type>& operator=(const scoped_vec_delete<Type>&) exprtk_delete;
      };

      struct scoped_bool_negator
      {
         explicit scoped_bool_negator(bool& bb);

        ~scoped_bool_negator();

         bool& b;
      };

      struct scoped_bool_or_restorer
      {
         explicit scoped_bool_or_restorer(bool& bb);

        ~scoped_bool_or_restorer();

         bool& b;
         bool original_value_;
      };

      struct scoped_inc_dec
      {
         explicit scoped_inc_dec(std::size_t& v);

        ~scoped_inc_dec();

         std::size_t& v_;
      };

      expression_node_ptr parse_function_invocation(ifunction<T>* function, const std::string& function_name);

      template <std::size_t NumberofParameters>
      expression_node_ptr parse_function_call(ifunction<T>* function, const std::string& function_name)
      {
         #ifdef _MSC_VER
            #pragma warning(push)
            #pragma warning(disable: 4127)
         #endif
         if (0 == NumberofParameters)
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR020 - Expecting ifunction '" + function_name + "' to have non-zero parameter count",
                          exprtk_error_location));

            return error_node();
         }
         #ifdef _MSC_VER
            #pragma warning(pop)
         #endif

         expression_node_ptr branch[NumberofParameters];
         expression_node_ptr result  = error_node();

         std::fill_n(branch, NumberofParameters, reinterpret_cast<expression_node_ptr>(0));

         scoped_delete<expression_node_t,NumberofParameters> sd((*this),branch);

         next_token();

         if (!token_is(token_t::e_lbracket))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR021 - Expecting argument list for function: '" + function_name + "'",
                          exprtk_error_location));

            return error_node();
         }

         for (int i = 0; i < static_cast<int>(NumberofParameters); ++i)
         {
            branch[i] = parse_expression();

            if (0 == branch[i])
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR022 - Failed to parse argument " + details::to_str(i) + " for function: '" + function_name + "'",
                             exprtk_error_location));

               return error_node();
            }
            else if (i < static_cast<int>(NumberofParameters - 1))
            {
               if (!token_is(token_t::e_comma))
               {
                  set_error(
                     make_error(parser_error::e_syntax,
                                current_token(),
                                "ERR023 - Invalid number of arguments for function: '" + function_name + "'",
                                exprtk_error_location));

                  return error_node();
               }
            }
         }

         if (!token_is(token_t::e_rbracket))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR024 - Invalid number of arguments for function: '" + function_name + "'",
                          exprtk_error_location));

            return error_node();
         }
         else
            result = expression_generator_.function(function,branch);

         sd.delete_ptr = (0 == result);

         return result;
      }

      expression_node_ptr parse_function_call_0(ifunction<T>* function, const std::string& function_name);

      template <std::size_t MaxNumberofParameters>
      std::size_t parse_base_function_call(expression_node_ptr (&param_list)[MaxNumberofParameters], const std::string& function_name = "")
      {
         std::fill_n(param_list, MaxNumberofParameters, reinterpret_cast<expression_node_ptr>(0));

         scoped_delete<expression_node_t,MaxNumberofParameters> sd((*this),param_list);

         next_token();

         if (!token_is(token_t::e_lbracket))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR026 - Expected a '(' at start of function call to '" + function_name  +
                          "', instead got: '" + current_token().value + "'",
                          exprtk_error_location));

            return 0;
         }

         if (token_is(token_t::e_rbracket, e_hold))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR027 - Expected at least one input parameter for function call '" + function_name + "'",
                          exprtk_error_location));

            return 0;
         }

         std::size_t param_index = 0;

         for (; param_index < MaxNumberofParameters; ++param_index)
         {
            param_list[param_index] = parse_expression();

            if (0 == param_list[param_index])
               return 0;
            else if (token_is(token_t::e_rbracket))
            {
               sd.delete_ptr = false;
               break;
            }
            else if (token_is(token_t::e_comma))
               continue;
            else
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR028 - Expected a ',' between function input parameters, instead got: '" + current_token().value + "'",
                             exprtk_error_location));

               return 0;
            }
         }

         if (sd.delete_ptr)
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR029 - Invalid number of input parameters passed to function '" + function_name  + "'",
                          exprtk_error_location));

            return 0;
         }

         return (param_index + 1);
      }

      expression_node_ptr parse_base_operation();

      expression_node_ptr parse_conditional_statement_01(expression_node_ptr condition);

      expression_node_ptr parse_conditional_statement_02(expression_node_ptr condition);

      expression_node_ptr parse_conditional_statement();

      expression_node_ptr parse_ternary_conditional_statement(expression_node_ptr condition);

      expression_node_ptr parse_not_statement();

      void handle_brkcnt_scope_exit();

      expression_node_ptr parse_while_loop();

      expression_node_ptr parse_repeat_until_loop();

      expression_node_ptr parse_for_loop();

      expression_node_ptr parse_switch_statement();

      expression_node_ptr parse_multi_switch_statement();

      expression_node_ptr parse_vararg_function();

      expression_node_ptr parse_string_range_statement(expression_node_ptr& expression);

      void parse_pending_string_rangesize(expression_node_ptr& expression);

      template <typename Allocator1,
                typename Allocator2,
                template <typename, typename> class Sequence>
      expression_node_ptr simplify(Sequence<expression_node_ptr,Allocator1>& expression_list,
                                          Sequence<bool,Allocator2>& side_effect_list,
                                          const bool specialise_on_final_type = false)
      {
         if (expression_list.empty())
            return error_node();
         else if (1 == expression_list.size())
            return expression_list[0];

         Sequence<expression_node_ptr,Allocator1> tmp_expression_list;

         bool return_node_present = false;

         for (std::size_t i = 0; i < (expression_list.size() - 1); ++i)
         {
            if (is_variable_node(expression_list[i]))
               continue;
            else if (
                      is_return_node  (expression_list[i]) ||
                      is_break_node   (expression_list[i]) ||
                      is_continue_node(expression_list[i])
                    )
            {
               tmp_expression_list.push_back(expression_list[i]);

               // Remove all subexpressions after first short-circuit
               // node has been encountered.

               for (std::size_t j = i + 1; j < expression_list.size(); ++j)
               {
                  free_node(node_allocator_,expression_list[j]);
               }

               return_node_present = true;

               break;
            }
            else if (
                      is_constant_node(expression_list[i]) ||
                      is_null_node    (expression_list[i]) ||
                      !side_effect_list[i]
                    )
            {
               free_node(node_allocator_,expression_list[i]);
               continue;
            }
            else
               tmp_expression_list.push_back(expression_list[i]);
         }

         if (!return_node_present)
         {
            tmp_expression_list.push_back(expression_list.back());
         }

         expression_list.swap(tmp_expression_list);

         if (tmp_expression_list.size() > expression_list.size())
         {
            exprtk_debug(("simplify() - Reduced subexpressions from %d to %d\n",
                          static_cast<int>(tmp_expression_list.size()),
                          static_cast<int>(expression_list    .size())));
         }

         if (
              return_node_present     ||
              side_effect_list.back() ||
              (expression_list.size() > 1)
            )
            state_.activate_side_effect("simplify()");

         if (1 == expression_list.size())
            return expression_list[0];
         else if (specialise_on_final_type && is_generally_string_node(expression_list.back()))
            return expression_generator_.vararg_function(details::e_smulti,expression_list);
         else
            return expression_generator_.vararg_function(details::e_multi,expression_list);
      }

      expression_node_ptr parse_multi_sequence(const std::string& source = "",
                                                      const bool enforce_crlbrackets = false);

      bool parse_range(range_t& rp, const bool skip_lsqr = false);

      void lodge_symbol(const std::string& symbol, const symbol_type st);

      expression_node_ptr parse_string();

      expression_node_ptr parse_const_string();

      expression_node_ptr parse_vector();

      expression_node_ptr parse_vararg_function_call(ivararg_function<T>* vararg_function, const std::string& vararg_function_name);

      class type_checker
      {
      public:

         enum return_type_t
         {
            e_overload = ' ',
            e_numeric  = 'T',
            e_string   = 'S'
         };

         struct function_prototype_t
         {
             return_type_t return_type;
             std::string   param_seq;
         };

         typedef parser<T> parser_t;
         typedef std::vector<function_prototype_t> function_definition_list_t;

         type_checker(parser_t& p,
                      const std::string& func_name,
                      const std::string& func_prototypes,
                      const return_type_t default_return_type);

         bool verify(const std::string& param_seq, std::size_t& pseq_index);

         std::size_t paramseq_count() const;

         std::string paramseq(const std::size_t& index) const;

         return_type_t return_type(const std::size_t& index) const;

         bool invalid() const;

         bool allow_zero_parameters() const;

      private:

         std::vector<std::string> split_param_seq(const std::string& param_seq, const details::char_t delimiter = '|') const;

         bool is_valid_token(std::string param_seq,
                                    function_prototype_t& funcproto) const;

         void parse_function_prototypes(const std::string& func_prototypes);

         type_checker(const type_checker&) exprtk_delete;
         type_checker& operator=(const type_checker&) exprtk_delete;

         bool invalid_state_;
         parser_t& parser_;
         std::string function_name_;
         const return_type_t default_return_type_;
         function_definition_list_t function_definition_list_;
      };

      expression_node_ptr parse_generic_function_call(igeneric_function<T>* function, const std::string& function_name);

      bool parse_igeneric_function_params(std::string& param_type_list,
                                                 std::vector<expression_node_ptr>& arg_list,
                                                 const std::string& function_name,
                                                 igeneric_function<T>* function,
                                                 const type_checker& tc);

      expression_node_ptr parse_string_function_call(igeneric_function<T>* function, const std::string& function_name);

      expression_node_ptr parse_overload_function_call(igeneric_function<T>* function, const std::string& function_name);

      template <typename Type, std::size_t NumberOfParameters>
      struct parse_special_function_impl
      {
         static expression_node_ptr process(parser<Type>& p, const details::operator_type opt_type, const std::string& sf_name)
         {
            expression_node_ptr branch[NumberOfParameters];
            expression_node_ptr result = error_node();

            std::fill_n(branch, NumberOfParameters, reinterpret_cast<expression_node_ptr>(0));

            scoped_delete<expression_node_t,NumberOfParameters> sd(p,branch);

            p.next_token();

            if (!p.token_is(token_t::e_lbracket))
            {
               p.set_error(
                    make_error(parser_error::e_syntax,
                               p.current_token(),
                               "ERR137 - Expected '(' for special function '" + sf_name + "'",
                               exprtk_error_location));

               return error_node();
            }

            for (std::size_t i = 0; i < NumberOfParameters; ++i)
            {
               branch[i] = p.parse_expression();

               if (0 == branch[i])
               {
                  return p.error_node();
               }
               else if (i < (NumberOfParameters - 1))
               {
                  if (!p.token_is(token_t::e_comma))
                  {
                     p.set_error(
                          make_error(parser_error::e_syntax,
                                     p.current_token(),
                                     "ERR138 - Expected ',' before next parameter of special function '" + sf_name + "'",
                                     exprtk_error_location));

                     return p.error_node();
                  }
               }
            }

            if (!p.token_is(token_t::e_rbracket))
            {
               p.set_error(
                    make_error(parser_error::e_syntax,
                               p.current_token(),
                               "ERR139 - Invalid number of parameters for special function '" + sf_name + "'",
                               exprtk_error_location));

               return p.error_node();
            }
            else
               result = p.expression_generator_.special_function(opt_type,branch);

            sd.delete_ptr = (0 == result);

            return result;
         }
      };

      expression_node_ptr parse_special_function();

      expression_node_ptr parse_null_statement();

      expression_node_ptr parse_break_statement();

      expression_node_ptr parse_continue_statement();

      expression_node_ptr parse_define_vector_statement(const std::string& vec_name);

      expression_node_ptr parse_define_string_statement(const std::string& str_name, expression_node_ptr initialisation_expression);

      bool local_variable_is_shadowed(const std::string& symbol);

      expression_node_ptr parse_define_var_statement();

      expression_node_ptr parse_uninitialised_var_statement(const std::string& var_name);

      expression_node_ptr parse_swap_statement();

      expression_node_ptr parse_return_statement();

      bool post_variable_process(const std::string& symbol);

      bool post_bracket_process(const typename token_t::token_type& token, expression_node_ptr& branch);

      typedef typename interval_container_t<const void*>::interval_t interval_t;
      typedef interval_container_t<const void*> immutable_memory_map_t;
      typedef std::map<interval_t,token_t> immutable_symtok_map_t;

      interval_t make_memory_range(const T& t);

      interval_t make_memory_range(const T* begin, const std::size_t size);

      interval_t make_memory_range(details::char_cptr begin, const std::size_t size);

      void lodge_immutable_symbol(const lexer::token& token, const interval_t interval);

      expression_node_ptr parse_symtab_symbol();

      expression_node_ptr parse_symbol();

      expression_node_ptr parse_branch(precedence_level precedence = e_level00);

      void set_error(const parser_error::type& error_type);

      void remove_last_error();

      void set_synthesis_error(const std::string& synthesis_error_message);

      void register_local_vars(expression<T>& e);

      void register_return_results(expression<T>& e);

      void load_unary_operations_map(unary_op_map_t& m);

      void load_binary_operations_map(binary_op_map_t& m);

      void load_inv_binary_operations_map(inv_binary_op_map_t& m);

      void load_sf3_map(sf3_map_t& sf3_map);

      void load_sf4_map(sf4_map_t& sf4_map);

      results_context_t& results_ctx();

      void return_cleanup();

   private:

      parser(const parser<T>&) exprtk_delete;
      parser<T>& operator=(const parser<T>&) exprtk_delete;

      settings_store settings_;
      expression_generator<T> expression_generator_;
      details::node_allocator node_allocator_;
      symtab_store symtab_store_;
      dependent_entity_collector dec_;
      std::deque<parser_error::type> error_list_;
      std::deque<bool> brkcnt_list_;
      parser_state state_;
      bool resolve_unknown_symbol_;
      results_context_t* results_context_;
      unknown_symbol_resolver* unknown_symbol_resolver_;
      unknown_symbol_resolver default_usr_;
      base_ops_map_t base_ops_map_;
      unary_op_map_t unary_op_map_;
      binary_op_map_t binary_op_map_;
      inv_binary_op_map_t inv_binary_op_map_;
      sf3_map_t sf3_map_;
      sf4_map_t sf4_map_;
      std::string synthesis_error_;
      scope_element_manager sem_;

      immutable_memory_map_t immutable_memory_map_;
      immutable_symtok_map_t immutable_symtok_map_;

      lexer::helper::helper_assembly helper_assembly_;

      lexer::helper::commutative_inserter       commutative_inserter_;
      lexer::helper::operator_joiner            operator_joiner_2_;
      lexer::helper::operator_joiner            operator_joiner_3_;
      lexer::helper::symbol_replacer            symbol_replacer_;
      lexer::helper::bracket_checker            bracket_checker_;
      lexer::helper::numeric_checker<T>         numeric_checker_;
      lexer::helper::sequence_validator         sequence_validator_;
      lexer::helper::sequence_validator_3tokens sequence_validator_3tkns_;

      loop_runtime_check_ptr loop_runtime_check_;

      template <typename ParserType>
      friend void details::disable_type_checking(ParserType& p);
   }; // class parser
}

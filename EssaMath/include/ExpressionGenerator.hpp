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
#include "include/ParserHelpers.hpp"
#include "include/OperatorHelpers.hpp"
#include "include/ExpressionNodes.hpp"
#include "include/Operators.hpp"
#include "include/NodeAllocator.hpp"
#include "include/Functions.hpp"
#include "include/SymbolTable.hpp"

namespace Essa::Math{
      template <typename T>
      class expression_generator
      {
      public:
        typedef details::expression_node<T>* expression_node_ptr;
        typedef expression_node_ptr (*synthesize_functor_t)(expression_generator<T>&, const details::operator_type& operation, expression_node_ptr (&branch)[2]);
        typedef std::map<std::string,synthesize_functor_t> synthesize_map_t;
        typedef typename Essa::Math::parser<T> parser_t;
        typedef const T& vtype;
        typedef const T  ctype;

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
        typedef details::vector_holder<T>*                  vector_holder_ptr;

        typedef results_context<T> results_context_t;

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

      typedef details::T0oT1_define<T, vtype , vtype > vov_t;
      typedef details::T0oT1_define<T, ctype, vtype > cov_t;
      typedef details::T0oT1_define<T, vtype , ctype> voc_t;

      typedef details::T0oT1oT2_define<T, vtype , vtype , vtype > vovov_t;
      typedef details::T0oT1oT2_define<T, vtype , vtype , ctype> vovoc_t;
      typedef details::T0oT1oT2_define<T, vtype , ctype, vtype > vocov_t;
      typedef details::T0oT1oT2_define<T, ctype, vtype , vtype > covov_t;
      typedef details::T0oT1oT2_define<T, ctype, vtype , ctype> covoc_t;
      typedef details::T0oT1oT2_define<T, ctype, ctype, vtype > cocov_t;
      typedef details::T0oT1oT2_define<T, vtype , ctype, ctype> vococ_t;

      typedef details::T0oT1oT2oT3_define<T, vtype , vtype , vtype , vtype > vovovov_t;
      typedef details::T0oT1oT2oT3_define<T, vtype , vtype , vtype , ctype> vovovoc_t;
      typedef details::T0oT1oT2oT3_define<T, vtype , vtype , ctype, vtype > vovocov_t;
      typedef details::T0oT1oT2oT3_define<T, vtype , ctype, vtype , vtype > vocovov_t;
      typedef details::T0oT1oT2oT3_define<T, ctype, vtype , vtype , vtype > covovov_t;

      typedef details::T0oT1oT2oT3_define<T, ctype, vtype , ctype, vtype > covocov_t;
      typedef details::T0oT1oT2oT3_define<T, vtype , ctype, vtype , ctype> vocovoc_t;
      typedef details::T0oT1oT2oT3_define<T, ctype, vtype , vtype , ctype> covovoc_t;
      typedef details::T0oT1oT2oT3_define<T, vtype , ctype, ctype, vtype > vococov_t;

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

        static expression_node_ptr error_node();

         details::node_allocator* node_allocator(){return node_allocator_;};
         parser_t* parser() { return parser_;}

         void init_synthesize_map();

         void set_parser(parser_t& p);

         void set_uom(unary_op_map_t& unary_op_map);

         void set_bom(binary_op_map_t& binary_op_map);

         void set_ibom(inv_binary_op_map_t& inv_binary_op_map);

         void set_sf3m(sf3_map_t& sf3_map);

         void set_sf4m(sf4_map_t& sf4_map);

         void set_allocator(details::node_allocator& na);

         void set_strength_reduction_state(const bool enabled);

         bool strength_reduction_enabled() const;

         bool valid_operator(const details::operator_type& operation, binary_functor_t& bop);

         bool valid_operator(const details::operator_type& operation, unary_functor_t& uop);

         details::operator_type get_operator(const binary_functor_t& bop) const;

         expression_node_ptr operator() (const T& v) const;

         expression_node_ptr operator() (const std::string& s) const;

         expression_node_ptr operator() (std::string& s, range_t& rp) const;

         expression_node_ptr operator() (const std::string& s, range_t& rp) const;

         expression_node_ptr operator() (expression_node_ptr branch, range_t& rp) const;

         bool unary_optimisable(const details::operator_type& operation) const;

         bool sf3_optimisable(const std::string& sf3id, trinary_functor_t& tfunc) const;

         bool sf4_optimisable(const std::string& sf4id, quaternary_functor_t& qfunc) const;

         bool sf3_optimisable(const std::string& sf3id, details::operator_type& operation) const;

         bool sf4_optimisable(const std::string& sf4id, details::operator_type& operation) const;

         expression_node_ptr operator() (const details::operator_type& operation, expression_node_ptr (&branch)[1]);

         bool is_assignment_operation(const details::operator_type& operation) const;

         bool valid_string_operation(const details::operator_type& operation) const;

         std::string to_str(const details::operator_type& operation) const;

         bool operation_optimisable(const details::operator_type& operation) const;

         std::string branch_to_id(expression_node_ptr branch) const;

         std::string branch_to_id(expression_node_ptr (&branch)[2]) const;

         bool cov_optimisable(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const;

         bool voc_optimisable(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const;

         bool vov_optimisable(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const;

         bool cob_optimisable(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const;

         bool boc_optimisable(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const;

         bool cocob_optimisable(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const;

         bool coboc_optimisable(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const;

         bool uvouv_optimisable(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const;

         bool vob_optimisable(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const;

         bool bov_optimisable(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const;

         bool binext_optimisable(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const;

         bool is_invalid_assignment_op(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const;

         bool is_constpow_operation(const details::operator_type& operation, expression_node_ptr(&branch)[2]) const;

         bool is_invalid_break_continue_op(expression_node_ptr (&branch)[2]) const;

         bool is_invalid_string_op(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const;

         bool is_invalid_string_op(const details::operator_type& operation, expression_node_ptr (&branch)[3]) const;

         bool is_string_operation(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const;

         bool is_string_operation(const details::operator_type& operation, expression_node_ptr (&branch)[3]) const;

         bool is_shortcircuit_expression(const details::operator_type& operation) const;

         bool is_null_present(expression_node_ptr (&branch)[2]) const;

         bool is_vector_eqineq_logic_operation(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const;

         bool is_vector_arithmetic_operation(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const;

         expression_node_ptr operator() (const details::operator_type& operation, expression_node_ptr (&branch)[2]);

         expression_node_ptr operator() (const details::operator_type& operation, expression_node_ptr (&branch)[3]);

         expression_node_ptr operator() (const details::operator_type& operation, expression_node_ptr (&branch)[4]);

         expression_node_ptr operator() (const details::operator_type& operation, expression_node_ptr b0);

         expression_node_ptr operator() (const details::operator_type& operation, expression_node_ptr& b0, expression_node_ptr& b1);

         expression_node_ptr conditional(expression_node_ptr condition,
                                                expression_node_ptr consequent,
                                                expression_node_ptr alternative) const;

         expression_node_ptr conditional_string(expression_node_ptr condition,
                                                       expression_node_ptr consequent,
                                                       expression_node_ptr alternative) const;

         expression_node_ptr conditional_vector(expression_node_ptr condition,
                                                       expression_node_ptr consequent,
                                                       expression_node_ptr alternative) const;

         loop_runtime_check_ptr get_loop_runtime_check(const loop_runtime_check::loop_types loop_type) const;

         expression_node_ptr while_loop(expression_node_ptr& condition,
                                               expression_node_ptr& branch,
                                               const bool break_continue_present = false) const;

         expression_node_ptr repeat_until_loop(expression_node_ptr& condition,
                                                      expression_node_ptr& branch,
                                                      const bool break_continue_present = false) const;

         expression_node_ptr for_loop(expression_node_ptr& initialiser,
                                             expression_node_ptr& condition,
                                             expression_node_ptr& incrementor,
                                             expression_node_ptr& loop_body,
                                             bool break_continue_present = false) const;

         template <typename Allocator,
                   template <typename, typename> class Sequence>
         expression_node_ptr const_optimise_switch(Sequence<expression_node_ptr,Allocator>& arg_list)
         {
            expression_node_ptr result = error_node();

            for (std::size_t i = 0; i < (arg_list.size() / 2); ++i)
            {
               expression_node_ptr condition  = arg_list[(2 * i)    ];
               expression_node_ptr consequent = arg_list[(2 * i) + 1];

               if ((0 == result) && details::is_true(condition))
               {
                  result = consequent;
                  break;
               }
            }

            if (0 == result)
            {
               result = arg_list.back();
            }

            for (std::size_t i = 0; i < arg_list.size(); ++i)
            {
               expression_node_ptr current_expr = arg_list[i];

               if (current_expr && (current_expr != result))
               {
                  free_node(*node_allocator_,current_expr);
               }
            }

            return result;
         }

         template <typename Allocator,
                   template <typename, typename> class Sequence>
         expression_node_ptr const_optimise_mswitch(Sequence<expression_node_ptr,Allocator>& arg_list)
         {
            expression_node_ptr result = error_node();

            for (std::size_t i = 0; i < (arg_list.size() / 2); ++i)
            {
               expression_node_ptr condition  = arg_list[(2 * i)    ];
               expression_node_ptr consequent = arg_list[(2 * i) + 1];

               if (details::is_true(condition))
               {
                  result = consequent;
               }
            }

            if (0 == result)
            {
               T zero = T(0);
               result = node_allocator_->allocate<literal_node_t>(zero);
            }

            for (std::size_t i = 0; i < arg_list.size(); ++i)
            {
               expression_node_ptr& current_expr = arg_list[i];

               if (current_expr && (current_expr != result))
               {
                  details::free_node(*node_allocator_,current_expr);
               }
            }

            return result;
         }

         struct switch_nodes
         {
            typedef std::vector<std::pair<expression_node_ptr,bool> > arg_list_t;

            struct switch_impl_1
            {
               static T process(const arg_list_t& arg);
            };

            struct switch_impl_2
            {
               static T process(const arg_list_t& arg);
            };

            struct switch_impl_3
            {
               static T process(const arg_list_t& arg);
            };

            struct switch_impl_4
            {
               static T process(const arg_list_t& arg);
            };

            struct switch_impl_5
            {
               static T process(const arg_list_t& arg);
            };

            struct switch_impl_6
            {
               static T process(const arg_list_t& arg);
            };

            struct switch_impl_7
            {
               static T process(const arg_list_t& arg);
            };

            #undef case_stmt
         };

         template <typename Allocator,
                   template <typename, typename> class Sequence>
         expression_node_ptr switch_statement(Sequence<expression_node_ptr,Allocator>& arg_list, const bool default_statement_present)
         {
            if (arg_list.empty())
               return error_node();
            else if (
                      !all_nodes_valid(arg_list) ||
                      (!default_statement_present && (arg_list.size() < 2))
                    )
            {
               details::free_all_nodes(*node_allocator_,arg_list);

               return error_node();
            }
            else if (is_constant_foldable(arg_list))
               return const_optimise_switch(arg_list);

            switch ((arg_list.size() - 1) / 2)
            {
               #define case_stmt(N)                                                       \
               case N :                                                                   \
                  return node_allocator_->                                                \
                            allocate<details::switch_n_node                               \
                              <T,typename switch_nodes::switch_impl_##N > >(arg_list); \

               case_stmt(1)
               case_stmt(2)
               case_stmt(3)
               case_stmt(4)
               case_stmt(5)
               case_stmt(6)
               case_stmt(7)
               #undef case_stmt

               default : return node_allocator_->allocate<details::switch_node<T> >(arg_list);
            }
         }

         template <typename Allocator,
                   template <typename, typename> class Sequence>
         expression_node_ptr multi_switch_statement(Sequence<expression_node_ptr,Allocator>& arg_list)
         {
            if (!all_nodes_valid(arg_list))
            {
               details::free_all_nodes(*node_allocator_,arg_list);

               return error_node();
            }
            else if (is_constant_foldable(arg_list))
               return const_optimise_mswitch(arg_list);
            else
               return node_allocator_->allocate<details::multi_switch_node<T> >(arg_list);
         }

         #define unary_opr_switch_statements             \
         case_stmt(details::e_abs   , details::abs_op  ) \
         case_stmt(details::e_acos  , details::acos_op ) \
         case_stmt(details::e_acosh , details::acosh_op) \
         case_stmt(details::e_asin  , details::asin_op ) \
         case_stmt(details::e_asinh , details::asinh_op) \
         case_stmt(details::e_atan  , details::atan_op ) \
         case_stmt(details::e_atanh , details::atanh_op) \
         case_stmt(details::e_ceil  , details::ceil_op ) \
         case_stmt(details::e_cos   , details::cos_op  ) \
         case_stmt(details::e_cosh  , details::cosh_op ) \
         case_stmt(details::e_exp   , details::exp_op  ) \
         case_stmt(details::e_expm1 , details::expm1_op) \
         case_stmt(details::e_floor , details::floor_op) \
         case_stmt(details::e_log   , details::log_op  ) \
         case_stmt(details::e_log10 , details::log10_op) \
         case_stmt(details::e_log2  , details::log2_op ) \
         case_stmt(details::e_log1p , details::log1p_op) \
         case_stmt(details::e_neg   , details::neg_op  ) \
         case_stmt(details::e_pos   , details::pos_op  ) \
         case_stmt(details::e_round , details::round_op) \
         case_stmt(details::e_sin   , details::sin_op  ) \
         case_stmt(details::e_sinc  , details::sinc_op ) \
         case_stmt(details::e_sinh  , details::sinh_op ) \
         case_stmt(details::e_sqrt  , details::sqrt_op ) \
         case_stmt(details::e_tan   , details::tan_op  ) \
         case_stmt(details::e_tanh  , details::tanh_op ) \
         case_stmt(details::e_cot   , details::cot_op  ) \
         case_stmt(details::e_sec   , details::sec_op  ) \
         case_stmt(details::e_csc   , details::csc_op  ) \
         case_stmt(details::e_r2d   , details::r2d_op  ) \
         case_stmt(details::e_d2r   , details::d2r_op  ) \
         case_stmt(details::e_d2g   , details::d2g_op  ) \
         case_stmt(details::e_g2d   , details::g2d_op  ) \
         case_stmt(details::e_notl  , details::notl_op ) \
         case_stmt(details::e_sgn   , details::sgn_op  ) \
         case_stmt(details::e_erf   , details::erf_op  ) \
         case_stmt(details::e_erfc  , details::erfc_op ) \
         case_stmt(details::e_ncdf  , details::ncdf_op ) \
         case_stmt(details::e_frac  , details::frac_op ) \
         case_stmt(details::e_trunc , details::trunc_op) \

         expression_node_ptr synthesize_uv_expression(const details::operator_type& operation,
                                                             expression_node_ptr (&branch)[1]);

         expression_node_ptr synthesize_uvec_expression(const details::operator_type& operation,
                                                               expression_node_ptr (&branch)[1]);

         expression_node_ptr synthesize_unary_expression(const details::operator_type& operation,
                                                                expression_node_ptr (&branch)[1]);

         expression_node_ptr const_optimise_sf3(const details::operator_type& operation,
                                                       expression_node_ptr (&branch)[3]);

         expression_node_ptr varnode_optimise_sf3(const details::operator_type& operation, expression_node_ptr (&branch)[3]);

         expression_node_ptr special_function(const details::operator_type& operation, expression_node_ptr (&branch)[3]);

         expression_node_ptr const_optimise_sf4(const details::operator_type& operation, expression_node_ptr (&branch)[4]);

         expression_node_ptr varnode_optimise_sf4(const details::operator_type& operation, expression_node_ptr (&branch)[4]);

         expression_node_ptr special_function(const details::operator_type& operation, expression_node_ptr (&branch)[4]);

         template <typename Allocator,
                   template <typename, typename> class Sequence>
         expression_node_ptr const_optimise_varargfunc(const details::operator_type& operation, Sequence<expression_node_ptr,Allocator>& arg_list)
         {
            expression_node_ptr temp_node = error_node();

            switch (operation)
            {
               #define case_stmt(op0, op1)                                                \
               case op0 : temp_node = node_allocator_->                                   \
                                         allocate<details::vararg_node<T,op1<T> > > \
                                            (arg_list);                                   \
                          break;                                                          \

               case_stmt(details::e_sum   , details::vararg_add_op  )
               case_stmt(details::e_prod  , details::vararg_mul_op  )
               case_stmt(details::e_avg   , details::vararg_avg_op  )
               case_stmt(details::e_min   , details::vararg_min_op  )
               case_stmt(details::e_max   , details::vararg_max_op  )
               case_stmt(details::e_mand  , details::vararg_mand_op )
               case_stmt(details::e_mor   , details::vararg_mor_op  )
               case_stmt(details::e_multi , details::vararg_multi_op)
               #undef case_stmt
               default : return error_node();
            }

            const T v = temp_node->value();

            details::free_node(*node_allocator_,temp_node);

            return node_allocator_->allocate<literal_node_t>(v);
         }

         bool special_one_parameter_vararg(const details::operator_type& operation) const;

         template <typename Allocator,
                   template <typename, typename> class Sequence>
         expression_node_ptr varnode_optimise_varargfunc(const details::operator_type& operation, Sequence<expression_node_ptr,Allocator>& arg_list)
         {
            switch (operation)
            {
               #define case_stmt(op0, op1)                                                  \
               case op0 : return node_allocator_->                                          \
                             allocate<details::vararg_varnode<T,op1<T> > >(arg_list); \

               case_stmt(details::e_sum   , details::vararg_add_op  )
               case_stmt(details::e_prod  , details::vararg_mul_op  )
               case_stmt(details::e_avg   , details::vararg_avg_op  )
               case_stmt(details::e_min   , details::vararg_min_op  )
               case_stmt(details::e_max   , details::vararg_max_op  )
               case_stmt(details::e_mand  , details::vararg_mand_op )
               case_stmt(details::e_mor   , details::vararg_mor_op  )
               case_stmt(details::e_multi , details::vararg_multi_op)
               #undef case_stmt
               default : return error_node();
            }
         }

         template <typename Allocator,
                   template <typename, typename> class Sequence>
         expression_node_ptr vectorize_func(const details::operator_type& operation, Sequence<expression_node_ptr,Allocator>& arg_list)
         {
            if (1 == arg_list.size())
            {
               switch (operation)
               {
                  #define case_stmt(op0, op1)                                                     \
                  case op0 : return node_allocator_->                                             \
                                allocate<details::vectorize_node<T,op1<T> > >(arg_list[0]); \

                  case_stmt(details::e_sum  , details::vec_add_op)
                  case_stmt(details::e_prod , details::vec_mul_op)
                  case_stmt(details::e_avg  , details::vec_avg_op)
                  case_stmt(details::e_min  , details::vec_min_op)
                  case_stmt(details::e_max  , details::vec_max_op)
                  #undef case_stmt
                  default : return error_node();
               }
            }
            else
               return error_node();
         }

         template <typename Allocator,
                   template <typename, typename> class Sequence>
         expression_node_ptr vararg_function(const details::operator_type& operation, Sequence<expression_node_ptr,Allocator>& arg_list)
         {
            if (!all_nodes_valid(arg_list))
            {
               details::free_all_nodes(*node_allocator_,arg_list);

               return error_node();
            }
            else if (is_constant_foldable(arg_list))
               return const_optimise_varargfunc(operation,arg_list);
            else if ((arg_list.size() == 1) && details::is_ivector_node(arg_list[0]))
               return vectorize_func(operation,arg_list);
            else if ((arg_list.size() == 1) && special_one_parameter_vararg(operation))
               return arg_list[0];
            else if (all_nodes_variables(arg_list))
               return varnode_optimise_varargfunc(operation,arg_list);

            if (details::e_smulti == operation && !details::disable_string_capabilities)
            {
               return node_allocator_->
                 allocate<details::str_vararg_node<T,details::vararg_multi_op<T> > >(arg_list);
            }
            {
               switch (operation)
               {
                  #define case_stmt(op0, op1)                                               \
                  case op0 : return node_allocator_->                                       \
                                allocate<details::vararg_node<T,op1<T> > >(arg_list); \

                  case_stmt(details::e_sum   , details::vararg_add_op  )
                  case_stmt(details::e_prod  , details::vararg_mul_op  )
                  case_stmt(details::e_avg   , details::vararg_avg_op  )
                  case_stmt(details::e_min   , details::vararg_min_op  )
                  case_stmt(details::e_max   , details::vararg_max_op  )
                  case_stmt(details::e_mand  , details::vararg_mand_op )
                  case_stmt(details::e_mor   , details::vararg_mor_op  )
                  case_stmt(details::e_multi , details::vararg_multi_op)
                  #undef case_stmt
                  default : return error_node();
               }
            }
         }

         template <std::size_t N>
         expression_node_ptr function(ifunction_t* f, expression_node_ptr (&b)[N])
         {
            typedef typename details::function_N_node<T,ifunction_t,N> function_N_node_t;
            expression_node_ptr result = synthesize_expression<function_N_node_t,N>(f,b);

            if (0 == result)
               return error_node();
            else
            {
               // Can the function call be completely optimised?
               if (details::is_constant_node(result))
                  return result;
               else if (!all_nodes_valid(b))
               {
                  details::free_node(*node_allocator_,result);
                  std::fill_n(b, N, reinterpret_cast<expression_node_ptr>(0));

                  return error_node();
               }
               else if (N != f->param_count)
               {
                  details::free_node(*node_allocator_,result);
                  std::fill_n(b, N, reinterpret_cast<expression_node_ptr>(0));

                  return error_node();
               }

               function_N_node_t* func_node_ptr = reinterpret_cast<function_N_node_t*>(result);

               if (!func_node_ptr->init_branches(b))
               {
                  details::free_node(*node_allocator_,result);
                  std::fill_n(b, N, reinterpret_cast<expression_node_ptr>(0));

                  return error_node();
               }

               return result;
            }
         }

         bool cardinal_pow_optimisable(const details::operator_type& operation, const T& c) const;

         expression_node_ptr cardinal_pow_optimisation(const T& v, const T& c);

         expression_node_ptr cardinal_pow_optimisation(expression_node_ptr (&branch)[2]);

         expression_node_ptr function(ifunction_t* f);

         expression_node_ptr vararg_function_call(ivararg_function_t* vaf,
                                                         std::vector<expression_node_ptr>& arg_list);

         expression_node_ptr generic_function_call(igeneric_function_t* gf,
                                                          std::vector<expression_node_ptr>& arg_list,
                                                          const std::size_t& param_seq_index = std::numeric_limits<std::size_t>::max());

         expression_node_ptr string_function_call(igeneric_function_t* gf,
                                                         std::vector<expression_node_ptr>& arg_list,
                                                         const std::size_t& param_seq_index = std::numeric_limits<std::size_t>::max());

         expression_node_ptr return_call(std::vector<expression_node_ptr>& arg_list);

         expression_node_ptr return_envelope(expression_node_ptr body,
                                                    results_context_t* rc,
                                                    bool*& return_invoked);

         expression_node_ptr vector_element(const std::string& symbol,
                                                   vector_holder_ptr vector_base,
                                                   expression_node_ptr index);

      private:

         template <std::size_t N, typename NodePtr>
         bool is_constant_foldable(NodePtr (&b)[N]) const
         {
            if(details::disable_enhanced_features)
               return false;
            for (std::size_t i = 0; i < N; ++i)
            {
               if (0 == b[i])
                  return false;
               else if (!details::is_constant_node(b[i]))
                  return false;
            }

            return true;
         }

         template <typename NodePtr,
                   typename Allocator,
                   template <typename, typename> class Sequence>
         bool is_constant_foldable(const Sequence<NodePtr,Allocator>& b) const
         {
            if(details::disable_enhanced_features)
               return false;
            for (std::size_t i = 0; i < b.size(); ++i)
            {
               if (0 == b[i])
                  return false;
               else if (!details::is_constant_node(b[i]))
                  return false;
            }

            return true;
         }

         void lodge_assignment(symbol_type cst, expression_node_ptr node);

         const void* base_ptr(expression_node_ptr node);

         bool assign_immutable_symbol(expression_node_ptr node);

         expression_node_ptr synthesize_assignment_expression(const details::operator_type& operation, expression_node_ptr (&branch)[2]);

         expression_node_ptr synthesize_assignment_operation_expression(const details::operator_type& operation,
                                                                               expression_node_ptr (&branch)[2]);

         expression_node_ptr synthesize_veceqineqlogic_operation_expression(const details::operator_type& operation,
                                                                                   expression_node_ptr (&branch)[2]);

         expression_node_ptr synthesize_vecarithmetic_operation_expression(const details::operator_type& operation,
                                                                                  expression_node_ptr (&branch)[2]);

         expression_node_ptr synthesize_swap_expression(expression_node_ptr (&branch)[2]);

         expression_node_ptr synthesize_shortcircuit_expression(const details::operator_type& operation, expression_node_ptr (&branch)[2]);

         expression_node_ptr synthesize_uvouv_expression(const details::operator_type& operation, expression_node_ptr (&branch)[2]);

         #undef basic_opr_switch_statements
         #undef extended_opr_switch_statements
         #undef unary_opr_switch_statements

         #define string_opr_switch_statements            \
         case_stmt(details::e_lt    , details::lt_op   ) \
         case_stmt(details::e_lte   , details::lte_op  ) \
         case_stmt(details::e_gt    , details::gt_op   ) \
         case_stmt(details::e_gte   , details::gte_op  ) \
         case_stmt(details::e_eq    , details::eq_op   ) \
         case_stmt(details::e_ne    , details::ne_op   ) \
         case_stmt(details::e_in    , details::in_op   ) \
         case_stmt(details::e_like  , details::like_op ) \
         case_stmt(details::e_ilike , details::ilike_op) \

         expression_node_ptr synthesize_sos_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2]);

         expression_node_ptr synthesize_sros_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2]);

         expression_node_ptr synthesize_sosr_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2]);

         expression_node_ptr synthesize_socsr_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2]);

         expression_node_ptr synthesize_srosr_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2]);

         expression_node_ptr synthesize_socs_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2]);

         expression_node_ptr synthesize_csos_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2]);

         expression_node_ptr synthesize_csosr_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2]);

         expression_node_ptr synthesize_srocs_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2]);

         expression_node_ptr synthesize_srocsr_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2]);

         expression_node_ptr synthesize_csocs_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2]);

         expression_node_ptr synthesize_csocsr_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2]);

         expression_node_ptr synthesize_csros_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2]);

         expression_node_ptr synthesize_csrosr_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2]);

         expression_node_ptr synthesize_csrocs_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2]);

         expression_node_ptr synthesize_csrocsr_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2]);

         expression_node_ptr synthesize_strogen_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2]);

         expression_node_ptr synthesize_string_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2]);

         expression_node_ptr synthesize_string_expression(const details::operator_type& opr, expression_node_ptr (&branch)[3]);

         expression_node_ptr synthesize_null_expression(const details::operator_type& operation, expression_node_ptr (&branch)[2]);

         bool synthesize_expression(const details::operator_type& operation,
                                           expression_node_ptr (&branch)[2],
                                           expression_node_ptr& result);

         template <typename NodeType, std::size_t N>
         expression_node_ptr synthesize_expression(const details::operator_type& operation, expression_node_ptr (&branch)[N])
         {
            if (
                 (details::e_in    == operation) ||
                 (details::e_like  == operation) ||
                 (details::e_ilike == operation)
               )
            {
               free_all_nodes(*node_allocator_,branch);

               return error_node();
            }
            else if (!details::all_nodes_valid<N>(branch))
            {
               free_all_nodes(*node_allocator_,branch);

               return error_node();
            }
            else if ((details::e_default != operation))
            {
               // Attempt simple constant folding optimisation.
               expression_node_ptr expression_point = node_allocator_->allocate<NodeType>(operation,branch);

               if (is_constant_foldable<N>(branch))
               {
                  const T v = expression_point->value();
                  details::free_node(*node_allocator_,expression_point);

                  return node_allocator_->allocate<literal_node_t>(v);
               }
               else
                  return expression_point;
            }
            else
               return error_node();
         }

         template <typename NodeType, std::size_t N>
         expression_node_ptr synthesize_expression(F* f, expression_node_ptr (&branch)[N])
         {
            if (!details::all_nodes_valid<N>(branch))
            {
               free_all_nodes(*node_allocator_,branch);

               return error_node();
            }

            typedef typename details::function_N_node<T,ifunction_t,N> function_N_node_t;

            // Attempt simple constant folding optimisation.

            expression_node_ptr expression_point = node_allocator_->allocate<NodeType>(f);
            function_N_node_t* func_node_ptr = dynamic_cast<function_N_node_t*>(expression_point);

            if (0 == func_node_ptr)
            {
               free_all_nodes(*node_allocator_,branch);

               return error_node();
            }
            else
               func_node_ptr->init_branches(branch);

            if (is_constant_foldable<N>(branch) && !f->has_side_effects())
            {
               T v = expression_point->value();
               details::free_node(*node_allocator_,expression_point);

               return node_allocator_->allocate<literal_node_t>(v);
            }

            parser_->state_.activate_side_effect("synthesize_expression(function<NT,N>)");

            return expression_point;
         }


         template <typename TType, template <typename, typename> class IPowNode>
         expression_generator<T>::expression_node_ptr cardinal_pow_optimisation_impl(const TType& v, const unsigned int& p)
         {
            switch (p)
            {
               #define case_stmt(cp)                                                     \
               case cp : return node_allocator_->                                        \
                            allocate<IPowNode<T,details::numeric::fast_exp<T,cp> > >(v); \

               case_stmt( 1) case_stmt( 2) case_stmt( 3) case_stmt( 4)
               case_stmt( 5) case_stmt( 6) case_stmt( 7) case_stmt( 8)
               case_stmt( 9) case_stmt(10) case_stmt(11) case_stmt(12)
               case_stmt(13) case_stmt(14) case_stmt(15) case_stmt(16)
               case_stmt(17) case_stmt(18) case_stmt(19) case_stmt(20)
               case_stmt(21) case_stmt(22) case_stmt(23) case_stmt(24)
               case_stmt(25) case_stmt(26) case_stmt(27) case_stmt(28)
               case_stmt(29) case_stmt(30) case_stmt(31) case_stmt(32)
               case_stmt(33) case_stmt(34) case_stmt(35) case_stmt(36)
               case_stmt(37) case_stmt(38) case_stmt(39) case_stmt(40)
               case_stmt(41) case_stmt(42) case_stmt(43) case_stmt(44)
               case_stmt(45) case_stmt(46) case_stmt(47) case_stmt(48)
               case_stmt(49) case_stmt(50) case_stmt(51) case_stmt(52)
               case_stmt(53) case_stmt(54) case_stmt(55) case_stmt(56)
               case_stmt(57) case_stmt(58) case_stmt(59) case_stmt(60)
               #undef case_stmt
               default : return error_node();
            }
         }

         template <typename T0, typename T1>
         expression_node_ptr synthesize_str_xrox_expression_impl(const details::operator_type& opr,
                                                                        T0 s0, T1 s1,
                                                                        range_t rp0)
         {
            switch (opr)
            {
               #define case_stmt(op0, op1)                                                                      \
               case op0 : return node_allocator_->                                                              \
                             allocate_ttt<typename details::str_xrox_node<T,T0,T1,range_t,op1<T> >,T0,T1> \
                                (s0, s1, rp0);                                                                  \

               string_opr_switch_statements
               #undef case_stmt
               default : return error_node();
            }
         }

         template <typename T0, typename T1>
         expression_node_ptr synthesize_str_xoxr_expression_impl(const details::operator_type& opr,
                                                                        T0 s0, T1 s1,
                                                                        range_t rp1)
         {
            switch (opr)
            {
               #define case_stmt(op0, op1)                                                                      \
               case op0 : return node_allocator_->                                                              \
                             allocate_ttt<typename details::str_xoxr_node<T,T0,T1,range_t,op1<T> >,T0,T1> \
                                (s0, s1, rp1);                                                                  \

               string_opr_switch_statements
               #undef case_stmt
               default : return error_node();
            }
         }

         template <typename T0, typename T1>
         expression_node_ptr synthesize_str_xroxr_expression_impl(const details::operator_type& opr,
                                                                         T0 s0, T1 s1,
                                                                         range_t rp0, range_t rp1)
         {
            switch (opr)
            {
               #define case_stmt(op0, op1)                                                                        \
               case op0 : return node_allocator_->                                                                \
                             allocate_tttt<typename details::str_xroxr_node<T,T0,T1,range_t,op1<T> >,T0,T1> \
                                (s0, s1, rp0, rp1);                                                               \

               string_opr_switch_statements
               #undef case_stmt
               default : return error_node();
            }
         }

         template <typename T0, typename T1>
         expression_node_ptr synthesize_sos_expression_impl(const details::operator_type& opr, T0 s0, T1 s1)
         {
            switch (opr)
            {
               #define case_stmt(op0, op1)                                                                 \
               case op0 : return node_allocator_->                                                         \
                             allocate_tt<typename details::sos_node<T,T0,T1,op1<T> >,T0,T1>(s0, s1); \

               string_opr_switch_statements
               #undef case_stmt
               default : return error_node();
            }
         }

         bool                     strength_reduction_enabled_;
         details::node_allocator* node_allocator_;
         synthesize_map_t         synthesize_map_;
         unary_op_map_t*          unary_op_map_;
         binary_op_map_t*         binary_op_map_;
         inv_binary_op_map_t*     inv_binary_op_map_;
         sf3_map_t*               sf3_map_;
         sf4_map_t*               sf4_map_;
         parser_t*                parser_;
      }; // class expression_generator
}

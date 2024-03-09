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

#include "Defines.hpp"
#include "Numeric.hpp"
#include "Lexer.hpp"
#include "Token.hpp"
#include "ParserHelpers.hpp"
#include "OperatorHelpers.hpp"
#include "ExpressionNodes.hpp"
#include "Operators.hpp"
#include "NodeAllocator.hpp"
#include "Functions.hpp"
#include "SymbolTable.hpp"
#include "Expression.hpp"

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
         type()
         : mode(parser_error::e_unknown)
         , line_no  (0)
         , column_no(0)
         {}

         lexer::token token;
         error_mode mode;
         std::string diagnostic;
         std::string src_location;
         std::string error_line;
         std::size_t line_no;
         std::size_t column_no;
      };

      inline type make_error(const error_mode mode,
                             const std::string& diagnostic   = "",
                             const std::string& src_location = "")
      {
         type t;
         t.mode         = mode;
         t.token.type   = lexer::token::e_error;
         t.diagnostic   = diagnostic;
         t.src_location = src_location;
         exprtk_debug(("%s\n",diagnostic .c_str()));
         return t;
      }

      inline type make_error(const error_mode mode,
                             const lexer::token& tk,
                             const std::string& diagnostic   = "",
                             const std::string& src_location = "")
      {
         type t;
         t.mode         = mode;
         t.token        = tk;
         t.diagnostic   = diagnostic;
         t.src_location = src_location;
         exprtk_debug(("%s\n",diagnostic .c_str()));
         return t;
      }

      inline std::string to_str(error_mode mode)
      {
         switch (mode)
         {
            case e_unknown : return std::string("Unknown Error");
            case e_syntax  : return std::string("Syntax Error" );
            case e_token   : return std::string("Token Error"  );
            case e_numeric : return std::string("Numeric Error");
            case e_symtab  : return std::string("Symbol Error" );
            case e_lexer   : return std::string("Lexer Error"  );
            case e_helper  : return std::string("Helper Error" );
            case e_parser  : return std::string("Parser Error" );
            default        : return std::string("Unknown Error");
         }
      }

      inline bool update_error(type& error, const std::string& expression)
      {
         if (
              expression.empty()                         ||
              (error.token.position > expression.size()) ||
              (std::numeric_limits<std::size_t>::max() == error.token.position)
            )
         {
            return false;
         }

         std::size_t error_line_start = 0;

         for (std::size_t i = error.token.position; i > 0; --i)
         {
            const details::char_t c = expression[i];

            if (('\n' == c) || ('\r' == c))
            {
               error_line_start = i + 1;
               break;
            }
         }

         std::size_t next_nl_position = std::min(expression.size(),
                                                 expression.find_first_of('\n',error.token.position + 1));

         error.column_no  = error.token.position - error_line_start;
         error.error_line = expression.substr(error_line_start,
                                              next_nl_position - error_line_start);

         error.line_no = 0;

         for (std::size_t i = 0; i < next_nl_position; ++i)
         {
            if ('\n' == expression[i])
               ++error.line_no;
         }

         return true;
      }

      inline void dump_error(const type& error)
      {
         printf("Position: %02d   Type: [%s]   Msg: %s\n",
                static_cast<int>(error.token.position),
                Essa::Math::parser_error::to_str(error.mode).c_str(),
                error.diagnostic.c_str());
      }
   }

   namespace details
   {
      template <typename Parser>
      inline void disable_type_checking(Parser& p)
      {
         p.state_.type_check_enabled = false;
      }
   }

   template <typename T>
   class parser : public lexer::parser_helper
   {
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
      #ifndef exprtk_disable_break_continue
      typedef details::while_loop_bc_node<T>              while_loop_bc_node_t;
      typedef details::repeat_until_loop_bc_node<T>       repeat_until_loop_bc_node_t;
      typedef details::for_loop_bc_node<T>                for_loop_bc_node_t;
      typedef details::while_loop_bc_rtc_node<T>          while_loop_bc_rtc_node_t;
      typedef details::repeat_until_loop_bc_rtc_node<T>   repeat_until_loop_bc_rtc_node_t;
      typedef details::for_loop_bc_rtc_node<T>            for_loop_bc_rtc_node_t;
      #endif
      typedef details::switch_node<T>                     switch_node_t;
      typedef details::variable_node<T>                   variable_node_t;
      typedef details::vector_elem_node<T>                vector_elem_node_t;
      typedef details::rebasevector_elem_node<T>          rebasevector_elem_node_t;
      typedef details::rebasevector_celem_node<T>         rebasevector_celem_node_t;
      typedef details::vector_node<T>                     vector_node_t;
      typedef details::range_pack<T>                      range_t;
      #ifndef exprtk_disable_string_capabilities
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
      #endif
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
         #ifndef exprtk_disable_string_capabilities
         typedef stringvar_node_t*         stringvar_node_ptr;
         #endif

         scope_element()
         : name("???")
         , size (std::numeric_limits<std::size_t>::max())
         , index(std::numeric_limits<std::size_t>::max())
         , depth(std::numeric_limits<std::size_t>::max())
         , ref_count(0)
         , ip_index (0)
         , type (e_none)
         , active(false)
         , data     (0)
         , var_node (0)
         , vec_node (0)
         #ifndef exprtk_disable_string_capabilities
         , str_node(0)
         #endif
         {}

         bool operator < (const scope_element& se) const
         {
            if (ip_index < se.ip_index)
               return true;
            else if (ip_index > se.ip_index)
               return false;
            else if (depth < se.depth)
               return true;
            else if (depth > se.depth)
               return false;
            else if (index < se.index)
               return true;
            else if (index > se.index)
               return false;
            else
               return (name < se.name);
         }

         void clear()
         {
            name   = "???";
            size   = std::numeric_limits<std::size_t>::max();
            index  = std::numeric_limits<std::size_t>::max();
            depth  = std::numeric_limits<std::size_t>::max();
            type   = e_none;
            active = false;
            ref_count = 0;
            ip_index  = 0;
            data      = 0;
            var_node  = 0;
            vec_node  = 0;
            #ifndef exprtk_disable_string_capabilities
            str_node  = 0;
            #endif
         }

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
         #ifndef exprtk_disable_string_capabilities
         stringvar_node_ptr str_node;
         #endif
      };

      class scope_element_manager
      {
      public:

         typedef expression_node_t* expression_node_ptr;
         typedef variable_node_t*   variable_node_ptr;
         typedef parser<T>          parser_t;

         explicit scope_element_manager(parser<T>& p)
         : parser_(p)
         , input_param_cnt_(0)
         {}

         inline std::size_t size() const
         {
            return element_.size();
         }

         inline bool empty() const
         {
            return element_.empty();
         }

         inline scope_element& get_element(const std::size_t& index)
         {
            if (index < element_.size())
               return element_[index];
            else
               return null_element_;
         }

         inline scope_element& get_element(const std::string& var_name,
                                           const std::size_t index = std::numeric_limits<std::size_t>::max())
         {
            const std::size_t current_depth = parser_.state_.scope_depth;

            for (std::size_t i = 0; i < element_.size(); ++i)
            {
               scope_element& se = element_[i];

               if (se.depth > current_depth)
                  continue;
               else if (
                         details::imatch(se.name, var_name) &&
                         (se.index == index)
                       )
                  return se;
            }

            return null_element_;
         }

         inline scope_element& get_active_element(const std::string& var_name,
                                                  const std::size_t index = std::numeric_limits<std::size_t>::max())
         {
            const std::size_t current_depth = parser_.state_.scope_depth;

            for (std::size_t i = 0; i < element_.size(); ++i)
            {
               scope_element& se = element_[i];

               if (se.depth > current_depth)
                  continue;
               else if (
                         details::imatch(se.name, var_name) &&
                         (se.index == index)                &&
                         (se.active)
                       )
                  return se;
            }

            return null_element_;
         }

         inline bool add_element(const scope_element& se)
         {
            for (std::size_t i = 0; i < element_.size(); ++i)
            {
               scope_element& cse = element_[i];

               if (
                    details::imatch(cse.name, se.name) &&
                    (cse.depth <= se.depth)            &&
                    (cse.index == se.index)            &&
                    (cse.size  == se.size )            &&
                    (cse.type  == se.type )            &&
                    (cse.active)
                  )
                  return false;
            }

            element_.push_back(se);
            std::sort(element_.begin(),element_.end());

            return true;
         }

         inline void deactivate(const std::size_t& scope_depth)
         {
            exprtk_debug(("deactivate() - Scope depth: %d\n",
                          static_cast<int>(parser_.state_.scope_depth)));

            for (std::size_t i = 0; i < element_.size(); ++i)
            {
               scope_element& se = element_[i];

               if (se.active && (se.depth >= scope_depth))
               {
                  exprtk_debug(("deactivate() - element[%02d] '%s'\n",
                                static_cast<int>(i),
                                se.name.c_str()));

                  se.active = false;
               }
            }
         }

         inline void free_element(scope_element& se)
         {
            exprtk_debug(("free_element() - se[%s]\n", se.name.c_str()));

            switch (se.type)
            {
               case scope_element::e_variable   : delete reinterpret_cast<T*>(se.data);
                                                  delete se.var_node;
                                                  break;

               case scope_element::e_vector     : delete[] reinterpret_cast<T*>(se.data);
                                                  delete se.vec_node;
                                                  break;

               case scope_element::e_vecelem    : delete se.var_node;
                                                  break;

               #ifndef exprtk_disable_string_capabilities
               case scope_element::e_string     : delete reinterpret_cast<std::string*>(se.data);
                                                  delete se.str_node;
                                                  break;
               #endif

               default                          : return;
            }

            se.clear();
         }

         inline void cleanup()
         {
            for (std::size_t i = 0; i < element_.size(); ++i)
            {
               free_element(element_[i]);
            }

            element_.clear();

            input_param_cnt_ = 0;
         }

         inline std::size_t next_ip_index()
         {
            return ++input_param_cnt_;
         }

         inline expression_node_ptr get_variable(const T& v)
         {
            for (std::size_t i = 0; i < element_.size(); ++i)
            {
               scope_element& se = element_[i];

               if (
                    se.active   &&
                    se.var_node &&
                    details::is_variable_node(se.var_node)
                  )
               {
                  variable_node_ptr vn = reinterpret_cast<variable_node_ptr>(se.var_node);

                  if (&(vn->ref()) == (&v))
                  {
                     return se.var_node;
                  }
               }
            }

            return expression_node_ptr(0);
         }

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

         explicit scope_handler(parser<T>& p)
         : parser_(p)
         {
            parser_.state_.scope_depth++;
            #ifdef exprtk_enable_debugging
            const std::string depth(2 * parser_.state_.scope_depth,'-');
            exprtk_debug(("%s> Scope Depth: %02d\n",
                          depth.c_str(),
                          static_cast<int>(parser_.state_.scope_depth)));
            #endif
         }

        ~scope_handler()
         {
            parser_.sem_.deactivate(parser_.state_.scope_depth);
            parser_.state_.scope_depth--;
            #ifdef exprtk_enable_debugging
            const std::string depth(2 * parser_.state_.scope_depth,'-');
            exprtk_debug(("<%s Scope Depth: %02d\n",
                          depth.c_str(),
                          static_cast<int>(parser_.state_.scope_depth)));
            #endif
         }

      private:

         scope_handler(const scope_handler&) exprtk_delete;
         scope_handler& operator=(const scope_handler&) exprtk_delete;

         parser_t& parser_;
      };

      template <typename T_>
      struct halfopen_range_policy
      {
         static inline bool is_within(const T_& v, const T_& begin, const T_& end)
         {
            assert(begin <= end);
            return (begin <= v) && (v < end);
         }

         static inline bool is_less(const T_& v, const T_& begin)
         {
            return (v < begin);
         }

         static inline bool is_greater(const T_& v, const T_& end)
         {
            return (end <= v);
         }

         static inline bool end_inclusive()
         {
            return false;
         }
      };

      template <typename T_>
      struct closed_range_policy
      {
         static inline bool is_within(const T_& v, const T_& begin, const T_& end)
         {
            assert(begin <= end);
            return (begin <= v) && (v <= end);
         }

         static inline bool is_less(const T_& v, const T_& begin)
         {
            return (v < begin);
         }

         static inline bool is_greater(const T_& v, const T_& end)
         {
            return (end < v);
         }

         static inline bool end_inclusive()
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

         explicit stack_limit_handler(parser<T>& p)
         : parser_(p)
         , limit_exceeded_(false)
         {
            if (++parser_.state_.stack_depth > parser_.settings_.max_stack_depth_)
            {
               limit_exceeded_ = true;
               parser_.set_error(
                  make_error(parser_error::e_parser,
                     "ERR000 - Current stack depth " + details::to_str(parser_.state_.stack_depth) +
                     " exceeds maximum allowed stack depth of " + details::to_str(parser_.settings_.max_stack_depth_),
                     exprtk_error_location));
            }
         }

        ~stack_limit_handler()
         {
            parser_.state_.stack_depth--;
         }

         bool operator!()
         {
            return limit_exceeded_;
         }

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
         #ifndef exprtk_disable_string_capabilities
         typedef typename symbol_table_t::stringvar_ptr stringvar_ptr;
         #endif
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

         #ifndef exprtk_disable_string_capabilities
         struct string_context
         {
            string_context()
            : symbol_table(0)
            , str_var(0)
            {}

            const symbol_table_t* symbol_table;
            stringvar_ptr str_var;
         };
         #endif

         inline bool empty() const
         {
            return symtab_list_.empty();
         }

         inline void clear()
         {
            symtab_list_.clear();
         }

         inline bool valid() const
         {
            if (!empty())
            {
               for (std::size_t i = 0; i < symtab_list_.size(); ++i)
               {
                  if (symtab_list_[i].valid())
                     return true;
               }
            }

            return false;
         }

         inline bool valid_symbol(const std::string& symbol) const
         {
            if (!symtab_list_.empty())
               return symtab_list_[0].valid_symbol(symbol);
            else
               return false;
         }

         inline bool valid_function_name(const std::string& symbol) const
         {
            if (!symtab_list_.empty())
               return symtab_list_[0].valid_function(symbol);
            else
               return false;
         }

         inline variable_context get_variable_context(const std::string& variable_name) const
         {
            variable_context result;
            if (!valid_symbol(variable_name))
               return result;

            for (std::size_t i = 0; i < symtab_list_.size(); ++i)
            {
               if (!symtab_list_[i].valid())
               {
                  continue;
               }

               result.variable = local_data(i)
                                    .variable_store.get(variable_name);
               if (result.variable)
               {
                  result.symbol_table = &symtab_list_[i];
                  break;
               }
            }

            return result;
         }

         inline variable_ptr get_variable(const std::string& variable_name) const
         {
            if (!valid_symbol(variable_name))
               return reinterpret_cast<variable_ptr>(0);

            variable_ptr result = reinterpret_cast<variable_ptr>(0);

            for (std::size_t i = 0; i < symtab_list_.size(); ++i)
            {
               if (!symtab_list_[i].valid())
                  continue;
               else
                  result = local_data(i)
                              .variable_store.get(variable_name);

               if (result) break;
            }

            return result;
         }

         inline variable_ptr get_variable(const T& var_ref) const
         {
            variable_ptr result = reinterpret_cast<variable_ptr>(0);

            for (std::size_t i = 0; i < symtab_list_.size(); ++i)
            {
               if (!symtab_list_[i].valid())
                  continue;
               else
                  result = local_data(i).variable_store
                              .get_from_varptr(reinterpret_cast<const void*>(&var_ref));

               if (result) break;
            }

            return result;
         }

         #ifndef exprtk_disable_string_capabilities
         inline string_context get_string_context(const std::string& string_name) const
         {
            string_context result;

            if (!valid_symbol(string_name))
               return result;

            for (std::size_t i = 0; i < symtab_list_.size(); ++i)
            {
               if (!symtab_list_[i].valid())
               {
                  continue;
               }

               result.str_var = local_data(i).stringvar_store.get(string_name);

               if (result.str_var)
               {
                  result.symbol_table = &symtab_list_[i];
                  break;
               }
            }

            return result;
         }

         inline stringvar_ptr get_stringvar(const std::string& string_name) const
         {
            if (!valid_symbol(string_name))
               return reinterpret_cast<stringvar_ptr>(0);

            stringvar_ptr result = reinterpret_cast<stringvar_ptr>(0);

            for (std::size_t i = 0; i < symtab_list_.size(); ++i)
            {
               if (!symtab_list_[i].valid())
                  continue;
               else
                  result = local_data(i)
                              .stringvar_store.get(string_name);

               if (result) break;
            }

            return result;
         }
         #endif

         inline function_ptr get_function(const std::string& function_name) const
         {
            if (!valid_function_name(function_name))
               return reinterpret_cast<function_ptr>(0);

            function_ptr result = reinterpret_cast<function_ptr>(0);

            for (std::size_t i = 0; i < symtab_list_.size(); ++i)
            {
               if (!symtab_list_[i].valid())
                  continue;
               else
                  result = local_data(i)
                              .function_store.get(function_name);

               if (result) break;
            }

            return result;
         }

         inline vararg_function_ptr get_vararg_function(const std::string& vararg_function_name) const
         {
            if (!valid_function_name(vararg_function_name))
               return reinterpret_cast<vararg_function_ptr>(0);

            vararg_function_ptr result = reinterpret_cast<vararg_function_ptr>(0);

            for (std::size_t i = 0; i < symtab_list_.size(); ++i)
            {
               if (!symtab_list_[i].valid())
                  continue;
               else
                  result = local_data(i)
                              .vararg_function_store.get(vararg_function_name);

               if (result) break;
            }

            return result;
         }

         inline generic_function_ptr get_generic_function(const std::string& function_name) const
         {
            if (!valid_function_name(function_name))
               return reinterpret_cast<generic_function_ptr>(0);

            generic_function_ptr result = reinterpret_cast<generic_function_ptr>(0);

            for (std::size_t i = 0; i < symtab_list_.size(); ++i)
            {
               if (!symtab_list_[i].valid())
                  continue;
               else
                  result = local_data(i)
                              .generic_function_store.get(function_name);

               if (result) break;
            }

            return result;
         }

         inline generic_function_ptr get_string_function(const std::string& function_name) const
         {
            if (!valid_function_name(function_name))
               return reinterpret_cast<generic_function_ptr>(0);

            generic_function_ptr result = reinterpret_cast<generic_function_ptr>(0);

            for (std::size_t i = 0; i < symtab_list_.size(); ++i)
            {
               if (!symtab_list_[i].valid())
                  continue;
               else
                  result =
                     local_data(i).string_function_store.get(function_name);

               if (result) break;
            }

            return result;
         }

         inline generic_function_ptr get_overload_function(const std::string& function_name) const
         {
            if (!valid_function_name(function_name))
               return reinterpret_cast<generic_function_ptr>(0);

            generic_function_ptr result = reinterpret_cast<generic_function_ptr>(0);

            for (std::size_t i = 0; i < symtab_list_.size(); ++i)
            {
               if (!symtab_list_[i].valid())
                  continue;
               else
                  result =
                     local_data(i).overload_function_store.get(function_name);

               if (result) break;
            }

            return result;
         }

         inline vector_context get_vector_context(const std::string& vector_name) const
         {
            vector_context result;
            if (!valid_symbol(vector_name))
               return result;

            for (std::size_t i = 0; i < symtab_list_.size(); ++i)
            {
               if (!symtab_list_[i].valid())
               {
                  continue;
               }

               result.vector_holder = local_data(i).vector_store.get(vector_name);

               if (result.vector_holder)
               {
                  result.symbol_table = &symtab_list_[i];
                  break;
               }
            }

            return result;
         }

         inline vector_holder_ptr get_vector(const std::string& vector_name) const
         {
            if (!valid_symbol(vector_name))
               return reinterpret_cast<vector_holder_ptr>(0);

            vector_holder_ptr result = reinterpret_cast<vector_holder_ptr>(0);

            for (std::size_t i = 0; i < symtab_list_.size(); ++i)
            {
               if (!symtab_list_[i].valid())
                  continue;
               else
                  result =
                     local_data(i).vector_store.get(vector_name);

               if (result) break;
            }

            return result;
         }

         inline bool is_constant_node(const std::string& symbol_name) const
         {
            if (!valid_symbol(symbol_name))
               return false;

            for (std::size_t i = 0; i < symtab_list_.size(); ++i)
            {
               if (!symtab_list_[i].valid())
                  continue;
               else if (local_data(i).variable_store.is_constant(symbol_name))
                  return true;
            }

            return false;
         }

         #ifndef exprtk_disable_string_capabilities
         inline bool is_constant_string(const std::string& symbol_name) const
         {
            if (!valid_symbol(symbol_name))
               return false;

            for (std::size_t i = 0; i < symtab_list_.size(); ++i)
            {
               if (!symtab_list_[i].valid())
                  continue;
               else if (!local_data(i).stringvar_store.symbol_exists(symbol_name))
                  continue;
               else if (local_data(i).stringvar_store.is_constant(symbol_name))
                  return true;
            }

            return false;
         }
         #endif

         inline bool symbol_exists(const std::string& symbol) const
         {
            for (std::size_t i = 0; i < symtab_list_.size(); ++i)
            {
               if (!symtab_list_[i].valid())
                  continue;
               else if (symtab_list_[i].symbol_exists(symbol))
                  return true;
            }

            return false;
         }

         inline bool is_variable(const std::string& variable_name) const
         {
            for (std::size_t i = 0; i < symtab_list_.size(); ++i)
            {
               if (!symtab_list_[i].valid())
                  continue;
               else if (
                         symtab_list_[i].local_data().variable_store
                           .symbol_exists(variable_name)
                       )
                  return true;
            }

            return false;
         }

         #ifndef exprtk_disable_string_capabilities
         inline bool is_stringvar(const std::string& stringvar_name) const
         {
            for (std::size_t i = 0; i < symtab_list_.size(); ++i)
            {
               if (!symtab_list_[i].valid())
                  continue;
               else if (
                         symtab_list_[i].local_data().stringvar_store
                           .symbol_exists(stringvar_name)
                       )
                  return true;
            }

            return false;
         }

         inline bool is_conststr_stringvar(const std::string& symbol_name) const
         {
            for (std::size_t i = 0; i < symtab_list_.size(); ++i)
            {
               if (!symtab_list_[i].valid())
                  continue;
               else if (
                         symtab_list_[i].local_data().stringvar_store
                           .symbol_exists(symbol_name)
                       )
               {
                  return (
                           local_data(i).stringvar_store.symbol_exists(symbol_name) ||
                           local_data(i).stringvar_store.is_constant  (symbol_name)
                         );

               }
            }

            return false;
         }
         #endif

         inline bool is_function(const std::string& function_name) const
         {
            for (std::size_t i = 0; i < symtab_list_.size(); ++i)
            {
               if (!symtab_list_[i].valid())
                  continue;
               else if (
                         local_data(i).vararg_function_store
                           .symbol_exists(function_name)
                       )
                  return true;
            }

            return false;
         }

         inline bool is_vararg_function(const std::string& vararg_function_name) const
         {
            for (std::size_t i = 0; i < symtab_list_.size(); ++i)
            {
               if (!symtab_list_[i].valid())
                  continue;
               else if (
                         local_data(i).vararg_function_store
                           .symbol_exists(vararg_function_name)
                       )
                  return true;
            }

            return false;
         }

         inline bool is_vector(const std::string& vector_name) const
         {
            for (std::size_t i = 0; i < symtab_list_.size(); ++i)
            {
               if (!symtab_list_[i].valid())
                  continue;
               else if (
                         local_data(i).vector_store
                           .symbol_exists(vector_name)
                       )
                  return true;
            }

            return false;
         }

         inline std::string get_variable_name(const expression_node_ptr& ptr) const
         {
            return local_data().variable_store.entity_name(ptr);
         }

         inline std::string get_vector_name(const vector_holder_ptr& ptr) const
         {
            return local_data().vector_store.entity_name(ptr);
         }

         #ifndef exprtk_disable_string_capabilities
         inline std::string get_stringvar_name(const expression_node_ptr& ptr) const
         {
            return local_data().stringvar_store.entity_name(ptr);
         }

         inline std::string get_conststr_stringvar_name(const expression_node_ptr& ptr) const
         {
            return local_data().stringvar_store.entity_name(ptr);
         }
         #endif

         inline local_data_t& local_data(const std::size_t& index = 0)
         {
            return symtab_list_[index].local_data();
         }

         inline const local_data_t& local_data(const std::size_t& index = 0) const
         {
            return symtab_list_[index].local_data();
         }

         inline symbol_table_t& get_symbol_table(const std::size_t& index = 0)
         {
            return symtab_list_[index];
         }
      };

      struct parser_state
      {
         parser_state()
         : type_check_enabled(true)
         {
            reset();
         }

         void reset()
         {
            parsing_return_stmt     = false;
            parsing_break_stmt      = false;
            return_stmt_present     = false;
            side_effect_present     = false;
            scope_depth             = 0;
            stack_depth             = 0;
            parsing_loop_stmt_count = 0;
         }

         #ifndef exprtk_enable_debugging
         void activate_side_effect(const std::string&)
         #else
         void activate_side_effect(const std::string& source)
         #endif
         {
            if (!side_effect_present)
            {
               side_effect_present = true;

               exprtk_debug(("activate_side_effect() - caller: %s\n",source.c_str()));
            }
         }

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
                              std::string&       error_message)
         {
            if (e_usrmode_default != mode)
               return false;

            st = e_usr_variable_type;
            default_value = T(0);
            error_message.clear();

            return true;
         }

         virtual bool process(const std::string& /* unknown_symbol */,
                              symbol_table_t&    /* symbol_table   */,
                              std::string&       /* error_message  */)
         {
            return false;
         }
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

         dependent_entity_collector(const std::size_t options = e_ct_none)
         : options_(options)
         , collect_variables_  ((options_ & e_ct_variables  ) == e_ct_variables  )
         , collect_functions_  ((options_ & e_ct_functions  ) == e_ct_functions  )
         , collect_assignments_((options_ & e_ct_assignments) == e_ct_assignments)
         , return_present_   (false)
         , final_stmt_return_(false)
         {}

         template <typename Allocator,
                   template <typename, typename> class Sequence>
         inline std::size_t symbols(Sequence<symbol_t,Allocator>& symbols_list)
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
         inline std::size_t assignment_symbols(Sequence<symbol_t,Allocator>& assignment_list)
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

         void clear()
         {
            symbol_name_list_    .clear();
            assignment_name_list_.clear();
            retparam_list_       .clear();
            return_present_    = false;
            final_stmt_return_ = false;
         }

         bool& collect_variables()
         {
            return collect_variables_;
         }

         bool& collect_functions()
         {
            return collect_functions_;
         }

         bool& collect_assignments()
         {
            return collect_assignments_;
         }

         bool return_present() const
         {
            return return_present_;
         }

         bool final_stmt_return() const
         {
            return final_stmt_return_;
         }

         typedef std::vector<std::string> retparam_list_t;

         retparam_list_t return_param_type_list() const
         {
            return retparam_list_;
         }

      private:

         inline void add_symbol(const std::string& symbol, const symbol_type st)
         {
            switch (st)
            {
               case e_st_variable       :
               case e_st_vector         :
               case e_st_string         :
               case e_st_local_variable :
               case e_st_local_vector   :
               case e_st_local_string   : if (collect_variables_)
                                             symbol_name_list_
                                                .push_back(std::make_pair(symbol, st));
                                          break;

               case e_st_function       : if (collect_functions_)
                                             symbol_name_list_
                                                .push_back(std::make_pair(symbol, st));
                                          break;

               default                  : return;
            }
         }

         inline void add_assignment(const std::string& symbol, const symbol_type st)
         {
            switch (st)
            {
               case e_st_variable       :
               case e_st_vector         :
               case e_st_string         : if (collect_assignments_)
                                             assignment_name_list_
                                                .push_back(std::make_pair(symbol, st));
                                          break;

               default                  : return;
            }
         }

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
            e_bf_unknown = 0,
            e_bf_abs       , e_bf_acos     , e_bf_acosh    , e_bf_asin    ,
            e_bf_asinh     , e_bf_atan     , e_bf_atan2    , e_bf_atanh   ,
            e_bf_avg       , e_bf_ceil     , e_bf_clamp    , e_bf_cos     ,
            e_bf_cosh      , e_bf_cot      , e_bf_csc      , e_bf_equal   ,
            e_bf_erf       , e_bf_erfc     , e_bf_exp      , e_bf_expm1   ,
            e_bf_floor     , e_bf_frac     , e_bf_hypot    , e_bf_iclamp  ,
            e_bf_like      , e_bf_log      , e_bf_log10    , e_bf_log1p   ,
            e_bf_log2      , e_bf_logn     , e_bf_mand     , e_bf_max     ,
            e_bf_min       , e_bf_mod      , e_bf_mor      , e_bf_mul     ,
            e_bf_ncdf      , e_bf_pow      , e_bf_root     , e_bf_round   ,
            e_bf_roundn    , e_bf_sec      , e_bf_sgn      , e_bf_sin     ,
            e_bf_sinc      , e_bf_sinh     , e_bf_sqrt     , e_bf_sum     ,
            e_bf_swap      , e_bf_tan      , e_bf_tanh     , e_bf_trunc   ,
            e_bf_not_equal , e_bf_inrange  , e_bf_deg2grad , e_bf_deg2rad ,
            e_bf_rad2deg   , e_bf_grad2deg
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

         static const std::size_t compile_all_opts =
                                     e_replacer          +
                                     e_joiner            +
                                     e_numeric_check     +
                                     e_bracket_check     +
                                     e_sequence_check    +
                                     e_commutative_check +
                                     e_strength_reduction;

         settings_store(const std::size_t compile_options = compile_all_opts)
         : max_stack_depth_(400)
         , max_node_depth_(10000)
         {
           load_compile_options(compile_options);
         }

         settings_store& enable_all_base_functions()
         {
            disabled_func_set_.clear();
            return (*this);
         }

         settings_store& enable_all_control_structures()
         {
            disabled_ctrl_set_.clear();
            return (*this);
         }

         settings_store& enable_all_logic_ops()
         {
            disabled_logic_set_.clear();
            return (*this);
         }

         settings_store& enable_all_arithmetic_ops()
         {
            disabled_arithmetic_set_.clear();
            return (*this);
         }

         settings_store& enable_all_assignment_ops()
         {
            disabled_assignment_set_.clear();
            return (*this);
         }

         settings_store& enable_all_inequality_ops()
         {
            disabled_inequality_set_.clear();
            return (*this);
         }

         settings_store& enable_local_vardef()
         {
            disable_vardef_ = false;
            return (*this);
         }

         settings_store& disable_all_base_functions()
         {
            std::copy(details::base_function_list,
                      details::base_function_list + details::base_function_list_size,
                      std::insert_iterator<disabled_entity_set_t>
                        (disabled_func_set_, disabled_func_set_.begin()));
            return (*this);
         }

         settings_store& disable_all_control_structures()
         {
            std::copy(details::cntrl_struct_list,
                      details::cntrl_struct_list + details::cntrl_struct_list_size,
                      std::insert_iterator<disabled_entity_set_t>
                        (disabled_ctrl_set_, disabled_ctrl_set_.begin()));
            return (*this);
         }

         settings_store& disable_all_logic_ops()
         {
            std::copy(details::logic_ops_list,
                      details::logic_ops_list + details::logic_ops_list_size,
                      std::insert_iterator<disabled_entity_set_t>
                        (disabled_logic_set_, disabled_logic_set_.begin()));
            return (*this);
         }

         settings_store& disable_all_arithmetic_ops()
         {
            std::copy(details::arithmetic_ops_list,
                      details::arithmetic_ops_list + details::arithmetic_ops_list_size,
                      std::insert_iterator<disabled_entity_set_t>
                        (disabled_arithmetic_set_, disabled_arithmetic_set_.begin()));
            return (*this);
         }

         settings_store& disable_all_assignment_ops()
         {
            std::copy(details::assignment_ops_list,
                      details::assignment_ops_list + details::assignment_ops_list_size,
                      std::insert_iterator<disabled_entity_set_t>
                        (disabled_assignment_set_, disabled_assignment_set_.begin()));
            return (*this);
         }

         settings_store& disable_all_inequality_ops()
         {
            std::copy(details::inequality_ops_list,
                      details::inequality_ops_list + details::inequality_ops_list_size,
                      std::insert_iterator<disabled_entity_set_t>
                        (disabled_inequality_set_, disabled_inequality_set_.begin()));
            return (*this);
         }

         settings_store& disable_local_vardef()
         {
            disable_vardef_ = true;
            return (*this);
         }

         bool replacer_enabled           () const { return enable_replacer_;           }
         bool commutative_check_enabled  () const { return enable_commutative_check_;  }
         bool joiner_enabled             () const { return enable_joiner_;             }
         bool numeric_check_enabled      () const { return enable_numeric_check_;      }
         bool bracket_check_enabled      () const { return enable_bracket_check_;      }
         bool sequence_check_enabled     () const { return enable_sequence_check_;     }
         bool strength_reduction_enabled () const { return enable_strength_reduction_; }
         bool collect_variables_enabled  () const { return enable_collect_vars_;       }
         bool collect_functions_enabled  () const { return enable_collect_funcs_;      }
         bool collect_assignments_enabled() const { return enable_collect_assings_;    }
         bool vardef_disabled            () const { return disable_vardef_;            }
         bool rsrvd_sym_usr_disabled     () const { return disable_rsrvd_sym_usr_;     }
         bool zero_return_disabled       () const { return disable_zero_return_;       }

         bool function_enabled(const std::string& function_name) const
         {
            if (disabled_func_set_.empty())
               return true;
            else
               return (disabled_func_set_.end() == disabled_func_set_.find(function_name));
         }

         bool control_struct_enabled(const std::string& control_struct) const
         {
            if (disabled_ctrl_set_.empty())
               return true;
            else
               return (disabled_ctrl_set_.end() == disabled_ctrl_set_.find(control_struct));
         }

         bool logic_enabled(const std::string& logic_operation) const
         {
            if (disabled_logic_set_.empty())
               return true;
            else
               return (disabled_logic_set_.end() == disabled_logic_set_.find(logic_operation));
         }

         bool arithmetic_enabled(const details::operator_type& arithmetic_operation) const
         {
            if (disabled_logic_set_.empty())
               return true;
            else
               return disabled_arithmetic_set_.end() == disabled_arithmetic_set_
                                                            .find(arith_opr_to_string(arithmetic_operation));
         }

         bool assignment_enabled(const details::operator_type& assignment) const
         {
            if (disabled_assignment_set_.empty())
               return true;
            else
               return disabled_assignment_set_.end() == disabled_assignment_set_
                                                           .find(assign_opr_to_string(assignment));
         }

         bool inequality_enabled(const details::operator_type& inequality) const
         {
            if (disabled_inequality_set_.empty())
               return true;
            else
               return disabled_inequality_set_.end() == disabled_inequality_set_
                                                           .find(inequality_opr_to_string(inequality));
         }

         bool function_disabled(const std::string& function_name) const
         {
            if (disabled_func_set_.empty())
               return false;
            else
               return (disabled_func_set_.end() != disabled_func_set_.find(function_name));
         }

         bool control_struct_disabled(const std::string& control_struct) const
         {
            if (disabled_ctrl_set_.empty())
               return false;
            else
               return (disabled_ctrl_set_.end() != disabled_ctrl_set_.find(control_struct));
         }

         bool logic_disabled(const std::string& logic_operation) const
         {
            if (disabled_logic_set_.empty())
               return false;
            else
               return (disabled_logic_set_.end() != disabled_logic_set_.find(logic_operation));
         }

         bool assignment_disabled(const details::operator_type assignment_operation) const
         {
            if (disabled_assignment_set_.empty())
               return false;
            else
               return disabled_assignment_set_.end() != disabled_assignment_set_
                                                           .find(assign_opr_to_string(assignment_operation));
         }

         bool logic_disabled(const details::operator_type logic_operation) const
         {
            if (disabled_logic_set_.empty())
               return false;
            else
               return disabled_logic_set_.end() != disabled_logic_set_
                                                           .find(logic_opr_to_string(logic_operation));
         }

         bool arithmetic_disabled(const details::operator_type arithmetic_operation) const
         {
            if (disabled_arithmetic_set_.empty())
               return false;
            else
               return disabled_arithmetic_set_.end() != disabled_arithmetic_set_
                                                           .find(arith_opr_to_string(arithmetic_operation));
         }

         bool inequality_disabled(const details::operator_type& inequality) const
         {
            if (disabled_inequality_set_.empty())
               return false;
            else
               return disabled_inequality_set_.end() != disabled_inequality_set_
                                                           .find(inequality_opr_to_string(inequality));
         }

         settings_store& disable_base_function(settings_base_funcs bf)
         {
            if (
                 (e_bf_unknown != bf) &&
                 (static_cast<std::size_t>(bf) < (details::base_function_list_size + 1))
               )
            {
               disabled_func_set_.insert(details::base_function_list[bf - 1]);
            }

            return (*this);
         }

         settings_store& disable_control_structure(settings_control_structs ctrl_struct)
         {
            if (
                 (e_ctrl_unknown != ctrl_struct) &&
                 (static_cast<std::size_t>(ctrl_struct) < (details::cntrl_struct_list_size + 1))
               )
            {
               disabled_ctrl_set_.insert(details::cntrl_struct_list[ctrl_struct - 1]);
            }

            return (*this);
         }

         settings_store& disable_logic_operation(settings_logic_opr logic)
         {
            if (
                 (e_logic_unknown != logic) &&
                 (static_cast<std::size_t>(logic) < (details::logic_ops_list_size + 1))
               )
            {
               disabled_logic_set_.insert(details::logic_ops_list[logic - 1]);
            }

            return (*this);
         }

         settings_store& disable_arithmetic_operation(settings_arithmetic_opr arithmetic)
         {
            if (
                 (e_arith_unknown != arithmetic) &&
                 (static_cast<std::size_t>(arithmetic) < (details::arithmetic_ops_list_size + 1))
               )
            {
               disabled_arithmetic_set_.insert(details::arithmetic_ops_list[arithmetic - 1]);
            }

            return (*this);
         }

         settings_store& disable_assignment_operation(settings_assignment_opr assignment)
         {
            if (
                 (e_assign_unknown != assignment) &&
                 (static_cast<std::size_t>(assignment) < (details::assignment_ops_list_size + 1))
               )
            {
               disabled_assignment_set_.insert(details::assignment_ops_list[assignment - 1]);
            }

            return (*this);
         }

         settings_store& disable_inequality_operation(settings_inequality_opr inequality)
         {
            if (
                 (e_ineq_unknown != inequality) &&
                 (static_cast<std::size_t>(inequality) < (details::inequality_ops_list_size + 1))
               )
            {
               disabled_inequality_set_.insert(details::inequality_ops_list[inequality - 1]);
            }

            return (*this);
         }

         settings_store& enable_base_function(settings_base_funcs bf)
         {
            if (
                 (e_bf_unknown != bf) &&
                 (static_cast<std::size_t>(bf) < (details::base_function_list_size + 1))
               )
            {
               const des_itr_t itr = disabled_func_set_.find(details::base_function_list[bf - 1]);

               if (disabled_func_set_.end() != itr)
               {
                  disabled_func_set_.erase(itr);
               }
            }

            return (*this);
         }

         settings_store& enable_control_structure(settings_control_structs ctrl_struct)
         {
            if (
                 (e_ctrl_unknown != ctrl_struct) &&
                 (static_cast<std::size_t>(ctrl_struct) < (details::cntrl_struct_list_size + 1))
               )
            {
               const des_itr_t itr = disabled_ctrl_set_.find(details::cntrl_struct_list[ctrl_struct - 1]);

               if (disabled_ctrl_set_.end() != itr)
               {
                  disabled_ctrl_set_.erase(itr);
               }
            }

            return (*this);
         }

         settings_store& enable_logic_operation(settings_logic_opr logic)
         {
            if (
                 (e_logic_unknown != logic) &&
                 (static_cast<std::size_t>(logic) < (details::logic_ops_list_size + 1))
               )
            {
               const des_itr_t itr = disabled_logic_set_.find(details::logic_ops_list[logic - 1]);

               if (disabled_logic_set_.end() != itr)
               {
                  disabled_logic_set_.erase(itr);
               }
            }

            return (*this);
         }

         settings_store& enable_arithmetic_operation(settings_arithmetic_opr arithmetic)
         {
            if (
                 (e_arith_unknown != arithmetic) &&
                 (static_cast<std::size_t>(arithmetic) < (details::arithmetic_ops_list_size + 1))
               )
            {
               const des_itr_t itr = disabled_arithmetic_set_.find(details::arithmetic_ops_list[arithmetic - 1]);

               if (disabled_arithmetic_set_.end() != itr)
               {
                  disabled_arithmetic_set_.erase(itr);
               }
            }

            return (*this);
         }

         settings_store& enable_assignment_operation(settings_assignment_opr assignment)
         {
            if (
                 (e_assign_unknown != assignment) &&
                 (static_cast<std::size_t>(assignment) < (details::assignment_ops_list_size + 1))
               )
            {
               const des_itr_t itr = disabled_assignment_set_.find(details::assignment_ops_list[assignment - 1]);

               if (disabled_assignment_set_.end() != itr)
               {
                  disabled_assignment_set_.erase(itr);
               }
            }

            return (*this);
         }

         settings_store& enable_inequality_operation(settings_inequality_opr inequality)
         {
            if (
                 (e_ineq_unknown != inequality) &&
                 (static_cast<std::size_t>(inequality) < (details::inequality_ops_list_size + 1))
               )
            {
               const des_itr_t itr = disabled_inequality_set_.find(details::inequality_ops_list[inequality - 1]);

               if (disabled_inequality_set_.end() != itr)
               {
                  disabled_inequality_set_.erase(itr);
               }
            }

            return (*this);
         }

         void set_max_stack_depth(const std::size_t max_stack_depth)
         {
            max_stack_depth_ = max_stack_depth;
         }

         void set_max_node_depth(const std::size_t max_node_depth)
         {
            max_node_depth_ = max_node_depth;
         }

      private:

         void load_compile_options(const std::size_t compile_options)
         {
            enable_replacer_           = (compile_options & e_replacer            ) == e_replacer;
            enable_joiner_             = (compile_options & e_joiner              ) == e_joiner;
            enable_numeric_check_      = (compile_options & e_numeric_check       ) == e_numeric_check;
            enable_bracket_check_      = (compile_options & e_bracket_check       ) == e_bracket_check;
            enable_sequence_check_     = (compile_options & e_sequence_check      ) == e_sequence_check;
            enable_commutative_check_  = (compile_options & e_commutative_check   ) == e_commutative_check;
            enable_strength_reduction_ = (compile_options & e_strength_reduction  ) == e_strength_reduction;
            enable_collect_vars_       = (compile_options & e_collect_vars        ) == e_collect_vars;
            enable_collect_funcs_      = (compile_options & e_collect_funcs       ) == e_collect_funcs;
            enable_collect_assings_    = (compile_options & e_collect_assings     ) == e_collect_assings;
            disable_vardef_            = (compile_options & e_disable_vardef      ) == e_disable_vardef;
            disable_rsrvd_sym_usr_     = (compile_options & e_disable_usr_on_rsrvd) == e_disable_usr_on_rsrvd;
            disable_zero_return_       = (compile_options & e_disable_zero_return ) == e_disable_zero_return;
         }

         std::string assign_opr_to_string(details::operator_type opr) const
         {
            switch (opr)
            {
               case details::e_assign : return ":=";
               case details::e_addass : return "+=";
               case details::e_subass : return "-=";
               case details::e_mulass : return "*=";
               case details::e_divass : return "/=";
               case details::e_modass : return "%=";
               default                : return ""  ;
            }
         }

         std::string arith_opr_to_string(details::operator_type opr) const
         {
            switch (opr)
            {
               case details::e_add : return "+";
               case details::e_sub : return "-";
               case details::e_mul : return "*";
               case details::e_div : return "/";
               case details::e_mod : return "%";
               default             : return "" ;
            }
         }

         std::string inequality_opr_to_string(details::operator_type opr) const
         {
            switch (opr)
            {
               case details::e_lt    : return "<" ;
               case details::e_lte   : return "<=";
               case details::e_eq    : return "==";
               case details::e_equal : return "=" ;
               case details::e_ne    : return "!=";
               case details::e_nequal: return "<>";
               case details::e_gte   : return ">=";
               case details::e_gt    : return ">" ;
               default               : return ""  ;
            }
         }

         std::string logic_opr_to_string(details::operator_type opr) const
         {
            switch (opr)
            {
               case details::e_and  : return "and" ;
               case details::e_or   : return "or"  ;
               case details::e_xor  : return "xor" ;
               case details::e_nand : return "nand";
               case details::e_nor  : return "nor" ;
               case details::e_xnor : return "xnor";
               case details::e_notl : return "not" ;
               default              : return ""    ;
            }
         }

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

      parser(const settings_t& settings = settings_t())
      : settings_(settings)
      , resolve_unknown_symbol_(false)
      , results_context_(0)
      , unknown_symbol_resolver_(reinterpret_cast<unknown_symbol_resolver*>(0))
        #ifdef _MSC_VER
        #pragma warning(push)
        #pragma warning (disable:4355)
        #endif
      , sem_(*this)
        #ifdef _MSC_VER
        #pragma warning(pop)
        #endif
      , operator_joiner_2_(2)
      , operator_joiner_3_(3)
      , loop_runtime_check_(0)
      {
         init_precompilation();

         load_operations_map           (base_ops_map_     );
         load_unary_operations_map     (unary_op_map_     );
         load_binary_operations_map    (binary_op_map_    );
         load_inv_binary_operations_map(inv_binary_op_map_);
         load_sf3_map                  (sf3_map_          );
         load_sf4_map                  (sf4_map_          );

         expression_generator_.init_synthesize_map();
         expression_generator_.set_parser(*this);
         expression_generator_.set_uom(unary_op_map_);
         expression_generator_.set_bom(binary_op_map_);
         expression_generator_.set_ibom(inv_binary_op_map_);
         expression_generator_.set_sf3m(sf3_map_);
         expression_generator_.set_sf4m(sf4_map_);
         expression_generator_.set_strength_reduction_state(settings_.strength_reduction_enabled());

        settings_.disable_all_assignment_ops();
        settings_.disable_all_control_structures();
        settings_.disable_all_inequality_ops();
        settings_.disable_all_logic_ops();
      }

     ~parser() {}

      inline void init_precompilation()
      {
         dec_.collect_variables() =
            settings_.collect_variables_enabled();

         dec_.collect_functions() =
            settings_.collect_functions_enabled();

         dec_.collect_assignments() =
            settings_.collect_assignments_enabled();

         if (settings_.replacer_enabled())
         {
            symbol_replacer_.clear();
            symbol_replacer_.add_replace("true" , "1", lexer::token::e_number);
            symbol_replacer_.add_replace("false", "0", lexer::token::e_number);
            helper_assembly_.token_modifier_list.clear();
            helper_assembly_.register_modifier(&symbol_replacer_);
         }

         if (settings_.commutative_check_enabled())
         {
            for (std::size_t i = 0; i < details::reserved_words_size; ++i)
            {
               commutative_inserter_.ignore_symbol(details::reserved_words[i]);
            }

            helper_assembly_.token_inserter_list.clear();
            helper_assembly_.register_inserter(&commutative_inserter_);
         }

         if (settings_.joiner_enabled())
         {
            helper_assembly_.token_joiner_list.clear();
            helper_assembly_.register_joiner(&operator_joiner_2_);
            helper_assembly_.register_joiner(&operator_joiner_3_);
         }

         if (
              settings_.numeric_check_enabled () ||
              settings_.bracket_check_enabled () ||
              settings_.sequence_check_enabled()
            )
         {
            helper_assembly_.token_scanner_list.clear();

            if (settings_.numeric_check_enabled())
            {
               helper_assembly_.register_scanner(&numeric_checker_);
            }

            if (settings_.bracket_check_enabled())
            {
               helper_assembly_.register_scanner(&bracket_checker_);
            }

            if (settings_.sequence_check_enabled())
            {
               helper_assembly_.register_scanner(&sequence_validator_      );
               helper_assembly_.register_scanner(&sequence_validator_3tkns_);
            }
         }
      }

      inline bool compile(const std::string& expression_string, expression<T>& expr)
      {
         state_          .reset();
         error_list_     .clear();
         brkcnt_list_    .clear();
         synthesis_error_.clear();
         sem_            .cleanup();

         return_cleanup();

         expression_generator_.set_allocator(node_allocator_);

         if (expression_string.empty())
         {
            set_error(
               make_error(parser_error::e_syntax,
                          "ERR001 - Empty expression!",
                          exprtk_error_location));

            return false;
         }

         if (!init(expression_string))
         {
            process_lexer_errors();
            return false;
         }

         if (lexer().empty())
         {
            set_error(
               make_error(parser_error::e_syntax,
                          "ERR002 - Empty expression!",
                          exprtk_error_location));

            return false;
         }

         if (!run_assemblies())
         {
            return false;
         }

         symtab_store_.symtab_list_ = expr.get_symbol_table_list();
         dec_.clear();

         lexer().begin();

         next_token();

         expression_node_ptr e = parse_corpus();

         if ((0 != e) && (token_t::e_eof == current_token().type))
         {
            bool* retinvk_ptr = 0;

            if (state_.return_stmt_present)
            {
               dec_.return_present_ = true;

               e = expression_generator_
                     .return_envelope(e, results_context_, retinvk_ptr);
            }

            expr.set_expression(e);
            expr.set_retinvk(retinvk_ptr);

            register_local_vars(expr);
            register_return_results(expr);

            return !(!expr);
         }
         else
         {
            if (error_list_.empty())
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR003 - Invalid expression encountered",
                             exprtk_error_location));
            }

            if ((0 != e) && branch_deletable(e))
            {
               destroy_node(e);
            }

            dec_.clear    ();
            sem_.cleanup  ();
            return_cleanup();

            return false;
         }
      }

      inline expression_t compile(const std::string& expression_string, symbol_table_t& symtab)
      {
         expression_t expression;
         expression.register_symbol_table(symtab);
         compile(expression_string,expression);
         return expression;
      }

      void process_lexer_errors()
      {
         for (std::size_t i = 0; i < lexer().size(); ++i)
         {
            if (lexer()[i].is_error())
            {
               std::string diagnostic = "ERR004 - ";

               switch (lexer()[i].type)
               {
                  case lexer::token::e_error      : diagnostic += "General token error";
                                                    break;

                  case lexer::token::e_err_symbol : diagnostic += "Symbol error";
                                                    break;

                  case lexer::token::e_err_number : diagnostic += "Invalid numeric token";
                                                    break;

                  case lexer::token::e_err_string : diagnostic += "Invalid string token";
                                                    break;

                  case lexer::token::e_err_sfunc  : diagnostic += "Invalid special function token";
                                                    break;

                  default                         : diagnostic += "Unknown compiler error";
               }

               set_error(
                  make_error(parser_error::e_lexer,
                             lexer()[i],
                             diagnostic + ": " + lexer()[i].value,
                             exprtk_error_location));
            }
         }
      }

      inline bool run_assemblies()
      {
         if (settings_.commutative_check_enabled())
         {
            helper_assembly_.run_inserters(lexer());
         }

         if (settings_.joiner_enabled())
         {
            helper_assembly_.run_joiners(lexer());
         }

         if (settings_.replacer_enabled())
         {
            helper_assembly_.run_modifiers(lexer());
         }

         if (
              settings_.numeric_check_enabled () ||
              settings_.bracket_check_enabled () ||
              settings_.sequence_check_enabled()
            )
         {
            if (!helper_assembly_.run_scanners(lexer()))
            {
               if (helper_assembly_.error_token_scanner)
               {
                  lexer::helper::bracket_checker*            bracket_checker_ptr     = 0;
                  lexer::helper::numeric_checker<T>*         numeric_checker_ptr     = 0;
                  lexer::helper::sequence_validator*         sequence_validator_ptr  = 0;
                  lexer::helper::sequence_validator_3tokens* sequence_validator3_ptr = 0;

                  if (0 != (bracket_checker_ptr = dynamic_cast<lexer::helper::bracket_checker*>(helper_assembly_.error_token_scanner)))
                  {
                     set_error(
                        make_error(parser_error::e_token,
                                   bracket_checker_ptr->error_token(),
                                   "ERR005 - Mismatched brackets: '" + bracket_checker_ptr->error_token().value + "'",
                                   exprtk_error_location));
                  }
                  else if (0 != (numeric_checker_ptr = dynamic_cast<lexer::helper::numeric_checker<T>*>(helper_assembly_.error_token_scanner)))
                  {
                     for (std::size_t i = 0; i < numeric_checker_ptr->error_count(); ++i)
                     {
                        lexer::token error_token = lexer()[numeric_checker_ptr->error_index(i)];

                        set_error(
                           make_error(parser_error::e_token,
                                      error_token,
                                      "ERR006 - Invalid numeric token: '" + error_token.value + "'",
                                      exprtk_error_location));
                     }

                     if (numeric_checker_ptr->error_count())
                     {
                        numeric_checker_ptr->clear_errors();
                     }
                  }
                  else if (0 != (sequence_validator_ptr = dynamic_cast<lexer::helper::sequence_validator*>(helper_assembly_.error_token_scanner)))
                  {
                     for (std::size_t i = 0; i < sequence_validator_ptr->error_count(); ++i)
                     {
                        std::pair<lexer::token,lexer::token> error_token = sequence_validator_ptr->error(i);

                        set_error(
                           make_error(parser_error::e_token,
                                      error_token.first,
                                      "ERR007 - Invalid token sequence: '" +
                                      error_token.first.value  + "' and '" +
                                      error_token.second.value + "'",
                                      exprtk_error_location));
                     }

                     if (sequence_validator_ptr->error_count())
                     {
                        sequence_validator_ptr->clear_errors();
                     }
                  }
                  else if (0 != (sequence_validator3_ptr = dynamic_cast<lexer::helper::sequence_validator_3tokens*>(helper_assembly_.error_token_scanner)))
                  {
                     for (std::size_t i = 0; i < sequence_validator3_ptr->error_count(); ++i)
                     {
                        std::pair<lexer::token,lexer::token> error_token = sequence_validator3_ptr->error(i);

                        set_error(
                           make_error(parser_error::e_token,
                                      error_token.first,
                                      "ERR008 - Invalid token sequence: '" +
                                      error_token.first.value  + "' and '" +
                                      error_token.second.value + "'",
                                      exprtk_error_location));
                     }

                     if (sequence_validator3_ptr->error_count())
                     {
                        sequence_validator3_ptr->clear_errors();
                     }
                  }
               }

               return false;
            }
         }

         return true;
      }

      inline settings_store& settings()
      {
         return settings_;
      }

      inline parser_error::type get_error(const std::size_t& index) const
      {
         if (index < error_list_.size())
            return error_list_[index];
         else
            throw std::invalid_argument("parser::get_error() - Invalid error index specificed");
      }

      inline std::string error() const
      {
         if (!error_list_.empty())
         {
            return error_list_[0].diagnostic;
         }
         else
            return std::string("No Error");
      }

      inline std::size_t error_count() const
      {
         return error_list_.size();
      }

      inline dependent_entity_collector& dec()
      {
         return dec_;
      }

      inline bool replace_symbol(const std::string& old_symbol, const std::string& new_symbol)
      {
         if (!settings_.replacer_enabled())
            return false;
         else if (details::is_reserved_word(old_symbol))
            return false;
         else
            return symbol_replacer_.add_replace(old_symbol,new_symbol,lexer::token::e_symbol);
      }

      inline bool remove_replace_symbol(const std::string& symbol)
      {
         if (!settings_.replacer_enabled())
            return false;
         else if (details::is_reserved_word(symbol))
            return false;
         else
            return symbol_replacer_.remove(symbol);
      }

      inline void enable_unknown_symbol_resolver(unknown_symbol_resolver* usr = reinterpret_cast<unknown_symbol_resolver*>(0))
      {
         resolve_unknown_symbol_ = true;

         if (usr)
            unknown_symbol_resolver_ = usr;
         else
            unknown_symbol_resolver_ = &default_usr_;
      }

      inline void enable_unknown_symbol_resolver(unknown_symbol_resolver& usr)
      {
         enable_unknown_symbol_resolver(&usr);
      }

      inline void disable_unknown_symbol_resolver()
      {
         resolve_unknown_symbol_  = false;
         unknown_symbol_resolver_ = &default_usr_;
      }

      inline void register_loop_runtime_check(loop_runtime_check& lrtchk)
      {
         loop_runtime_check_ = &lrtchk;
      }

      inline void clear_loop_runtime_check()
      {
         loop_runtime_check_ = loop_runtime_check_ptr(0);
      }

   private:

      inline bool valid_base_operation(const std::string& symbol) const
      {
         const std::size_t length = symbol.size();

         if (
              (length < 3) || // Shortest base op symbol length
              (length > 9)    // Longest base op symbol length
            )
            return false;
         else
            return settings_.function_enabled(symbol) &&
                   (base_ops_map_.end() != base_ops_map_.find(symbol));
      }

      inline bool valid_vararg_operation(const std::string& symbol) const
      {
         static const std::string s_sum     = "sum" ;
         static const std::string s_mul     = "mul" ;
         static const std::string s_avg     = "avg" ;
         static const std::string s_min     = "min" ;
         static const std::string s_max     = "max" ;
         static const std::string s_mand    = "mand";
         static const std::string s_mor     = "mor" ;
         static const std::string s_multi   = "~"   ;
         static const std::string s_mswitch = "[*]" ;

         return
               (
                  details::imatch(symbol,s_sum    ) ||
                  details::imatch(symbol,s_mul    ) ||
                  details::imatch(symbol,s_avg    ) ||
                  details::imatch(symbol,s_min    ) ||
                  details::imatch(symbol,s_max    ) ||
                  details::imatch(symbol,s_mand   ) ||
                  details::imatch(symbol,s_mor    ) ||
                  details::imatch(symbol,s_multi  ) ||
                  details::imatch(symbol,s_mswitch)
               ) &&
               settings_.function_enabled(symbol);
      }

      bool is_invalid_logic_operation(const details::operator_type operation) const
      {
         return settings_.logic_disabled(operation);
      }

      bool is_invalid_arithmetic_operation(const details::operator_type operation) const
      {
         return settings_.arithmetic_disabled(operation);
      }

      bool is_invalid_assignment_operation(const details::operator_type operation) const
      {
         return settings_.assignment_disabled(operation);
      }

      bool is_invalid_inequality_operation(const details::operator_type operation) const
      {
         return settings_.inequality_disabled(operation);
      }

      #ifdef exprtk_enable_debugging
      inline void next_token()
      {
         const std::string ct_str = current_token().value;
         const std::size_t ct_pos = current_token().position;
         parser_helper::next_token();
         const std::string depth(2 * state_.scope_depth,' ');
         exprtk_debug(("%s"
                       "prev[%s | %04d] --> curr[%s | %04d]  stack_level: %3d\n",
                       depth.c_str(),
                       ct_str.c_str(),
                       static_cast<unsigned int>(ct_pos),
                       current_token().value.c_str(),
                       static_cast<unsigned int>(current_token().position),
                       static_cast<unsigned int>(state_.stack_depth)));
      }
      #endif

      inline expression_node_ptr parse_corpus()
      {
         std::vector<expression_node_ptr> arg_list;
         std::vector<bool> side_effect_list;

         scoped_vec_delete<expression_node_t> sdd((*this),arg_list);

         lexer::token begin_token;
         lexer::token end_token;

         for ( ; ; )
         {
            state_.side_effect_present = false;

            begin_token = current_token();

            expression_node_ptr arg = parse_expression();

            if (0 == arg)
            {
               if (error_list_.empty())
               {
                  set_error(
                     make_error(parser_error::e_syntax,
                                current_token(),
                                "ERR009 - Invalid expression encountered",
                                exprtk_error_location));
               }

               return error_node();
            }
            else
            {
               arg_list.push_back(arg);

               side_effect_list.push_back(state_.side_effect_present);

               end_token = current_token();

               const std::string sub_expr = construct_subexpr(begin_token, end_token);

               exprtk_debug(("parse_corpus(%02d) Subexpr: %s\n",
                             static_cast<int>(arg_list.size() - 1),
                             sub_expr.c_str()));

               exprtk_debug(("parse_corpus(%02d) - Side effect present: %s\n",
                             static_cast<int>(arg_list.size() - 1),
                             state_.side_effect_present ? "true" : "false"));

               exprtk_debug(("-------------------------------------------------\n"));
            }

            if (lexer().finished())
               break;
            else if (token_is(token_t::e_eof,prsrhlpr_t::e_hold))
            {
               if (lexer().finished())
                  break;
               else
                  next_token();
            }
         }

         if (
              !arg_list.empty() &&
              is_return_node(arg_list.back())
            )
         {
            dec_.final_stmt_return_ = true;
         }

         const expression_node_ptr result = simplify(arg_list,side_effect_list);

         sdd.delete_ptr = (0 == result);

         return result;
      }

      std::string construct_subexpr(lexer::token& begin_token, lexer::token& end_token)
      {
         std::string result = lexer().substr(begin_token.position,end_token.position);

         for (std::size_t i = 0; i < result.size(); ++i)
         {
            if (details::is_whitespace(result[i])) result[i] = ' ';
         }

         return result;
      }

      static const precedence_level default_precedence = e_level00;

      struct state_t
      {
         inline void set(const precedence_level& l,
                         const precedence_level& r,
                         const details::operator_type& o)
         {
            left  = l;
            right = r;
            operation = o;
         }

         inline void reset()
         {
            left      = e_level00;
            right     = e_level00;
            operation = details::e_default;
         }

         precedence_level left;
         precedence_level right;
         details::operator_type operation;
      };

      inline expression_node_ptr parse_expression(precedence_level precedence = e_level00)
      {
         stack_limit_handler slh(*this);

         if (!slh)
         {
            return error_node();
         }

         expression_node_ptr expression = parse_branch(precedence);

         if (0 == expression)
         {
            return error_node();
         }

         bool break_loop = false;

         state_t current_state;

         for ( ; ; )
         {
            current_state.reset();

            switch (current_token().type)
            {
               case token_t::e_assign : current_state.set(e_level00, e_level00, details::e_assign); break;
               case token_t::e_addass : current_state.set(e_level00, e_level00, details::e_addass); break;
               case token_t::e_subass : current_state.set(e_level00, e_level00, details::e_subass); break;
               case token_t::e_mulass : current_state.set(e_level00, e_level00, details::e_mulass); break;
               case token_t::e_divass : current_state.set(e_level00, e_level00, details::e_divass); break;
               case token_t::e_modass : current_state.set(e_level00, e_level00, details::e_modass); break;
               case token_t::e_swap   : current_state.set(e_level00, e_level00, details::e_swap  ); break;
               case token_t::e_lt     : current_state.set(e_level05, e_level06, details::e_lt    ); break;
               case token_t::e_lte    : current_state.set(e_level05, e_level06, details::e_lte   ); break;
               case token_t::e_eq     : current_state.set(e_level05, e_level06, details::e_eq    ); break;
               case token_t::e_ne     : current_state.set(e_level05, e_level06, details::e_ne    ); break;
               case token_t::e_gte    : current_state.set(e_level05, e_level06, details::e_gte   ); break;
               case token_t::e_gt     : current_state.set(e_level05, e_level06, details::e_gt    ); break;
               case token_t::e_add    : current_state.set(e_level07, e_level08, details::e_add   ); break;
               case token_t::e_sub    : current_state.set(e_level07, e_level08, details::e_sub   ); break;
               case token_t::e_div    : current_state.set(e_level10, e_level11, details::e_div   ); break;
               case token_t::e_mul    : current_state.set(e_level10, e_level11, details::e_mul   ); break;
               case token_t::e_mod    : current_state.set(e_level10, e_level11, details::e_mod   ); break;
               case token_t::e_pow    : current_state.set(e_level12, e_level12, details::e_pow   ); break;
               default                : if (token_t::e_symbol == current_token().type)
                                        {
                                           static const std::string s_and   = "and"  ;
                                           static const std::string s_nand  = "nand" ;
                                           static const std::string s_or    = "or"   ;
                                           static const std::string s_nor   = "nor"  ;
                                           static const std::string s_xor   = "xor"  ;
                                           static const std::string s_xnor  = "xnor" ;
                                           static const std::string s_in    = "in"   ;
                                           static const std::string s_like  = "like" ;
                                           static const std::string s_ilike = "ilike";
                                           static const std::string s_and1  = "&"    ;
                                           static const std::string s_or1   = "|"    ;
                                           static const std::string s_not   = "not"  ;

                                           if (details::imatch(current_token().value,s_and))
                                           {
                                              current_state.set(e_level03, e_level04, details::e_and);
                                              break;
                                           }
                                           else if (details::imatch(current_token().value,s_and1))
                                           {
                                              #ifndef exprtk_disable_sc_andor
                                              current_state.set(e_level03, e_level04, details::e_scand);
                                              #else
                                              current_state.set(e_level03, e_level04, details::e_and);
                                              #endif
                                              break;
                                           }
                                           else if (details::imatch(current_token().value,s_nand))
                                           {
                                              current_state.set(e_level03, e_level04, details::e_nand);
                                              break;
                                           }
                                           else if (details::imatch(current_token().value,s_or))
                                           {
                                              current_state.set(e_level01, e_level02, details::e_or);
                                              break;
                                           }
                                           else if (details::imatch(current_token().value,s_or1))
                                           {
                                              #ifndef exprtk_disable_sc_andor
                                              current_state.set(e_level01, e_level02, details::e_scor);
                                              #else
                                              current_state.set(e_level01, e_level02, details::e_or);
                                              #endif
                                              break;
                                           }
                                           else if (details::imatch(current_token().value,s_nor))
                                           {
                                              current_state.set(e_level01, e_level02, details::e_nor);
                                              break;
                                           }
                                           else if (details::imatch(current_token().value,s_xor))
                                           {
                                              current_state.set(e_level01, e_level02, details::e_xor);
                                              break;
                                           }
                                           else if (details::imatch(current_token().value,s_xnor))
                                           {
                                              current_state.set(e_level01, e_level02, details::e_xnor);
                                              break;
                                           }
                                           else if (details::imatch(current_token().value,s_in))
                                           {
                                              current_state.set(e_level04, e_level04, details::e_in);
                                              break;
                                           }
                                           else if (details::imatch(current_token().value,s_like))
                                           {
                                              current_state.set(e_level04, e_level04, details::e_like);
                                              break;
                                           }
                                           else if (details::imatch(current_token().value,s_ilike))
                                           {
                                              current_state.set(e_level04, e_level04, details::e_ilike);
                                              break;
                                           }
                                           else if (details::imatch(current_token().value,s_not))
                                           {
                                              break;
                                           }
                                        }

                                        break_loop = true;
            }

            if (break_loop)
            {
               parse_pending_string_rangesize(expression);
               break;
            }
            else if (current_state.left < precedence)
               break;

            const lexer::token prev_token = current_token();

            next_token();

            expression_node_ptr right_branch   = error_node();
            expression_node_ptr new_expression = error_node();

            if (is_invalid_logic_operation(current_state.operation))
            {
               free_node(node_allocator_,expression);

               set_error(
                  make_error(parser_error::e_syntax,
                             prev_token,
                             "ERR010 - Invalid or disabled logic operation '" + details::to_str(current_state.operation) + "'",
                             exprtk_error_location));

               return error_node();
            }
            else if (is_invalid_arithmetic_operation(current_state.operation))
            {
               free_node(node_allocator_,expression);

               set_error(
                  make_error(parser_error::e_syntax,
                             prev_token,
                             "ERR011 - Invalid or disabled arithmetic operation '" + details::to_str(current_state.operation) + "'",
                             exprtk_error_location));

               return error_node();
            }
            else if (is_invalid_inequality_operation(current_state.operation))
            {
               free_node(node_allocator_,expression);

               set_error(
                  make_error(parser_error::e_syntax,
                             prev_token,
                             "ERR012 - Invalid inequality operation '" + details::to_str(current_state.operation) + "'",
                             exprtk_error_location));

               return error_node();
            }
            else if (is_invalid_assignment_operation(current_state.operation))
            {
               free_node(node_allocator_,expression);

               set_error(
                  make_error(parser_error::e_syntax,
                             prev_token,
                             "ERR013 - Invalid or disabled assignment operation '" + details::to_str(current_state.operation) + "'",
                             exprtk_error_location));

               return error_node();
            }

            if (0 != (right_branch = parse_expression(current_state.right)))
            {
               if (
                    details::is_return_node(expression  ) ||
                    details::is_return_node(right_branch)
                  )
               {
                  free_node(node_allocator_, expression  );
                  free_node(node_allocator_, right_branch);

                  set_error(
                     make_error(parser_error::e_syntax,
                                prev_token,
                                "ERR014 - Return statements cannot be part of sub-expressions",
                                exprtk_error_location));

                  return error_node();
               }

               new_expression = expression_generator_
                                  (
                                    current_state.operation,
                                    expression,
                                    right_branch
                                  );
            }

            if (0 == new_expression)
            {
               if (error_list_.empty())
               {
                  set_error(
                     make_error(parser_error::e_syntax,
                                prev_token,
                                !synthesis_error_.empty() ?
                                synthesis_error_ :
                                "ERR015 - General parsing error at token: '" + prev_token.value + "'",
                                exprtk_error_location));
               }

               free_node(node_allocator_, expression  );
               free_node(node_allocator_, right_branch);

               return error_node();
            }
            else
            {
               if (
                    token_is(token_t::e_ternary,prsrhlpr_t::e_hold) &&
                    (e_level00 == precedence)
                  )
               {
                  expression = parse_ternary_conditional_statement(new_expression);
               }
               else
                  expression = new_expression;

               parse_pending_string_rangesize(expression);
            }
         }

         if ((0 != expression) && (expression->node_depth() > settings_.max_node_depth_))
         {
            set_error(
               make_error(parser_error::e_syntax,
                  current_token(),
                  "ERR016 - Expression depth of " + details::to_str(static_cast<int>(expression->node_depth())) +
                  " exceeds maximum allowed expression depth of " + details::to_str(static_cast<int>(settings_.max_node_depth_)),
                  exprtk_error_location));

            free_node(node_allocator_,expression);

            return error_node();
         }

         return expression;
      }

      bool simplify_unary_negation_branch(expression_node_ptr& node)
      {
         {
            typedef details::unary_branch_node<T,details::neg_op<T> > ubn_t;
            ubn_t* n = dynamic_cast<ubn_t*>(node);

            if (n)
            {
               expression_node_ptr un_r = n->branch(0);
               n->release();
               free_node(node_allocator_,node);
               node = un_r;

               return true;
            }
         }

         {
            typedef details::unary_variable_node<T,details::neg_op<T> > uvn_t;

            uvn_t* n = dynamic_cast<uvn_t*>(node);

            if (n)
            {
               const T& v = n->v();
               expression_node_ptr return_node = error_node();

               if (
                    (0 != (return_node = symtab_store_.get_variable(v))) ||
                    (0 != (return_node = sem_         .get_variable(v)))
                  )
               {
                  free_node(node_allocator_,node);
                  node = return_node;

                  return true;
               }
               else
               {
                  set_error(
                     make_error(parser_error::e_syntax,
                                current_token(),
                                "ERR017 - Failed to find variable node in symbol table",
                                exprtk_error_location));

                  free_node(node_allocator_,node);

                  return false;
               }
            }
         }

         return false;
      }

      static inline expression_node_ptr error_node()
      {
         return reinterpret_cast<expression_node_ptr>(0);
      }

      struct scoped_expression_delete
      {
         scoped_expression_delete(parser<T>& pr, expression_node_ptr& expression)
         : delete_ptr(true)
         , parser_(pr)
         , expression_(expression)
         {}

        ~scoped_expression_delete()
         {
            if (delete_ptr)
            {
               free_node(parser_.node_allocator_, expression_);
            }
         }

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
         explicit scoped_bool_negator(bool& bb)
         : b(bb)
         { b = !b; }

        ~scoped_bool_negator()
         { b = !b; }

         bool& b;
      };

      struct scoped_bool_or_restorer
      {
         explicit scoped_bool_or_restorer(bool& bb)
         : b(bb)
         , original_value_(bb)
         {}

        ~scoped_bool_or_restorer()
         {
            b = b || original_value_;
         }

         bool& b;
         bool original_value_;
      };

      struct scoped_inc_dec
      {
         explicit scoped_inc_dec(std::size_t& v)
         : v_(v)
         { ++v_; }

        ~scoped_inc_dec()
         {
           assert(v_ > 0);
           --v_;
         }

         std::size_t& v_;
      };

      inline expression_node_ptr parse_function_invocation(ifunction<T>* function, const std::string& function_name)
      {
         expression_node_ptr func_node = reinterpret_cast<expression_node_ptr>(0);

         switch (function->param_count)
         {
            case  0 : func_node = parse_function_call_0  (function,function_name); break;
            case  1 : func_node = parse_function_call< 1>(function,function_name); break;
            case  2 : func_node = parse_function_call< 2>(function,function_name); break;
            case  3 : func_node = parse_function_call< 3>(function,function_name); break;
            case  4 : func_node = parse_function_call< 4>(function,function_name); break;
            case  5 : func_node = parse_function_call< 5>(function,function_name); break;
            case  6 : func_node = parse_function_call< 6>(function,function_name); break;
            case  7 : func_node = parse_function_call< 7>(function,function_name); break;
            case  8 : func_node = parse_function_call< 8>(function,function_name); break;
            case  9 : func_node = parse_function_call< 9>(function,function_name); break;
            case 10 : func_node = parse_function_call<10>(function,function_name); break;
            case 11 : func_node = parse_function_call<11>(function,function_name); break;
            case 12 : func_node = parse_function_call<12>(function,function_name); break;
            case 13 : func_node = parse_function_call<13>(function,function_name); break;
            case 14 : func_node = parse_function_call<14>(function,function_name); break;
            case 15 : func_node = parse_function_call<15>(function,function_name); break;
            case 16 : func_node = parse_function_call<16>(function,function_name); break;
            case 17 : func_node = parse_function_call<17>(function,function_name); break;
            case 18 : func_node = parse_function_call<18>(function,function_name); break;
            case 19 : func_node = parse_function_call<19>(function,function_name); break;
            case 20 : func_node = parse_function_call<20>(function,function_name); break;
            default : {
                         set_error(
                            make_error(parser_error::e_syntax,
                                       current_token(),
                                       "ERR018 - Invalid number of parameters for function: '" + function_name + "'",
                                       exprtk_error_location));

                         return error_node();
                      }
         }

         if (func_node)
            return func_node;
         else
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR019 - Failed to generate call to function: '" + function_name + "'",
                          exprtk_error_location));

            return error_node();
         }
      }

      template <std::size_t NumberofParameters>
      inline expression_node_ptr parse_function_call(ifunction<T>* function, const std::string& function_name)
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

      inline expression_node_ptr parse_function_call_0(ifunction<T>* function, const std::string& function_name)
      {
         expression_node_ptr result = expression_generator_.function(function);

         state_.side_effect_present = function->has_side_effects();

         next_token();

         if (
               token_is(token_t::e_lbracket) &&
              !token_is(token_t::e_rbracket)
            )
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR025 - Expecting '()' to proceed call to function: '" + function_name + "'",
                          exprtk_error_location));

            free_node(node_allocator_,result);

            return error_node();
         }
         else
            return result;
      }

      template <std::size_t MaxNumberofParameters>
      inline std::size_t parse_base_function_call(expression_node_ptr (&param_list)[MaxNumberofParameters], const std::string& function_name = "")
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

      inline expression_node_ptr parse_base_operation()
      {
         typedef std::pair<base_ops_map_t::iterator,base_ops_map_t::iterator> map_range_t;

         const std::string operation_name   = current_token().value;
         const token_t     diagnostic_token = current_token();

         map_range_t itr_range = base_ops_map_.equal_range(operation_name);

         if (0 == std::distance(itr_range.first,itr_range.second))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          diagnostic_token,
                          "ERR030 - No entry found for base operation: " + operation_name,
                          exprtk_error_location));

            return error_node();
         }

         static const std::size_t MaxNumberofParameters = 4;
         expression_node_ptr param_list[MaxNumberofParameters] = {0};

         const std::size_t parameter_count = parse_base_function_call(param_list, operation_name);

         if ((parameter_count > 0) && (parameter_count <= MaxNumberofParameters))
         {
            for (base_ops_map_t::iterator itr = itr_range.first; itr != itr_range.second; ++itr)
            {
               const details::base_operation_t& operation = itr->second;

               if (operation.num_params == parameter_count)
               {
                  switch (parameter_count)
                  {
                     #define base_opr_case(N)                                         \
                     case N : {                                                       \
                                 expression_node_ptr pl##N[N] = {0};                  \
                                 std::copy(param_list, param_list + N, pl##N);        \
                                 lodge_symbol(operation_name, e_st_function);         \
                                 return expression_generator_(operation.type, pl##N); \
                              }                                                       \

                     base_opr_case(1)
                     base_opr_case(2)
                     base_opr_case(3)
                     base_opr_case(4)
                     #undef base_opr_case
                  }
               }
            }
         }

         for (std::size_t i = 0; i < MaxNumberofParameters; ++i)
         {
            free_node(node_allocator_, param_list[i]);
         }

         set_error(
            make_error(parser_error::e_syntax,
                       diagnostic_token,
                       "ERR031 - Invalid number of input parameters for call to function: '" + operation_name + "'",
                       exprtk_error_location));

         return error_node();
      }

      inline expression_node_ptr parse_conditional_statement_01(expression_node_ptr condition)
      {
         // Parse: [if][(][condition][,][consequent][,][alternative][)]

         expression_node_ptr consequent  = error_node();
         expression_node_ptr alternative = error_node();

         bool result = true;

         if (!token_is(token_t::e_comma))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR032 - Expected ',' between if-statement condition and consequent",
                          exprtk_error_location));
            result = false;
         }
         else if (0 == (consequent = parse_expression()))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR033 - Failed to parse consequent for if-statement",
                          exprtk_error_location));
            result = false;
         }
         else if (!token_is(token_t::e_comma))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR034 - Expected ',' between if-statement consequent and alternative",
                          exprtk_error_location));
            result = false;
         }
         else if (0 == (alternative = parse_expression()))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR035 - Failed to parse alternative for if-statement",
                          exprtk_error_location));
            result = false;
         }
         else if (!token_is(token_t::e_rbracket))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR036 - Expected ')' at the end of if-statement",
                          exprtk_error_location));
            result = false;
         }

         #ifndef exprtk_disable_string_capabilities
         if (result)
         {
            const bool consq_is_str = is_generally_string_node(consequent );
            const bool alter_is_str = is_generally_string_node(alternative);

            if (consq_is_str || alter_is_str)
            {
               if (consq_is_str && alter_is_str)
               {
                  return expression_generator_
                           .conditional_string(condition, consequent, alternative);
               }

               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR037 - Return types of if-statement differ: string/non-string",
                             exprtk_error_location));

               result = false;
            }
         }
         #endif

         if (result)
         {
            const bool consq_is_vec = is_ivector_node(consequent );
            const bool alter_is_vec = is_ivector_node(alternative);

            if (consq_is_vec || alter_is_vec)
            {
               if (consq_is_vec && alter_is_vec)
               {
                  return expression_generator_
                           .conditional_vector(condition, consequent, alternative);
               }

               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR038 - Return types of if-statement differ: vector/non-vector",
                             exprtk_error_location));

               result = false;
            }
         }

         if (!result)
         {
            free_node(node_allocator_, condition  );
            free_node(node_allocator_, consequent );
            free_node(node_allocator_, alternative);

            return error_node();
         }
         else
            return expression_generator_
                      .conditional(condition, consequent, alternative);
      }

      inline expression_node_ptr parse_conditional_statement_02(expression_node_ptr condition)
      {
         expression_node_ptr consequent  = error_node();
         expression_node_ptr alternative = error_node();

         bool result = true;

         if (token_is(token_t::e_lcrlbracket,prsrhlpr_t::e_hold))
         {
            if (0 == (consequent = parse_multi_sequence("if-statement-01")))
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR039 - Failed to parse body of consequent for if-statement",
                             exprtk_error_location));

               result = false;
            }
         }
         else
         {
            if (
                 settings_.commutative_check_enabled() &&
                 token_is(token_t::e_mul,prsrhlpr_t::e_hold)
               )
            {
               next_token();
            }

            if (0 != (consequent = parse_expression()))
            {
               if (!token_is(token_t::e_eof))
               {
                  set_error(
                     make_error(parser_error::e_syntax,
                                current_token(),
                                "ERR040 - Expected ';' at the end of the consequent for if-statement",
                                exprtk_error_location));

                  result = false;
               }
            }
            else
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR041 - Failed to parse body of consequent for if-statement",
                             exprtk_error_location));

               result = false;
            }
         }

         if (result)
         {
            if (details::imatch(current_token().value,"else"))
            {
               next_token();

               if (token_is(token_t::e_lcrlbracket,prsrhlpr_t::e_hold))
               {
                  if (0 == (alternative = parse_multi_sequence("else-statement-01")))
                  {
                     set_error(
                        make_error(parser_error::e_syntax,
                                   current_token(),
                                   "ERR042 - Failed to parse body of the 'else' for if-statement",
                                   exprtk_error_location));

                     result = false;
                  }
               }
               else if (details::imatch(current_token().value,"if"))
               {
                  if (0 == (alternative = parse_conditional_statement()))
                  {
                     set_error(
                        make_error(parser_error::e_syntax,
                                   current_token(),
                                   "ERR043 - Failed to parse body of if-else statement",
                                   exprtk_error_location));

                     result = false;
                  }
               }
               else if (0 != (alternative = parse_expression()))
               {
                  if (!token_is(token_t::e_eof))
                  {
                     set_error(
                        make_error(parser_error::e_syntax,
                                   current_token(),
                                   "ERR044 - Expected ';' at the end of the 'else-if' for the if-statement",
                                   exprtk_error_location));

                     result = false;
                  }
               }
               else
               {
                  set_error(
                     make_error(parser_error::e_syntax,
                                current_token(),
                                "ERR045 - Failed to parse body of the 'else' for if-statement",
                                exprtk_error_location));

                  result = false;
               }
            }
         }

         #ifndef exprtk_disable_string_capabilities
         if (result)
         {
            const bool consq_is_str = is_generally_string_node(consequent );
            const bool alter_is_str = is_generally_string_node(alternative);

            if (consq_is_str || alter_is_str)
            {
               if (consq_is_str && alter_is_str)
               {
                  return expression_generator_
                           .conditional_string(condition, consequent, alternative);
               }

               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR046 - Return types of if-statement differ: string/non-string",
                             exprtk_error_location));

               result = false;
            }
         }
         #endif

         if (result)
         {
            const bool consq_is_vec = is_ivector_node(consequent );
            const bool alter_is_vec = is_ivector_node(alternative);

            if (consq_is_vec || alter_is_vec)
            {
               if (consq_is_vec && alter_is_vec)
               {
                  return expression_generator_
                           .conditional_vector(condition, consequent, alternative);
               }

               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR047 - Return types of if-statement differ: vector/non-vector",
                             exprtk_error_location));

               result = false;
            }
         }

         if (!result)
         {
            free_node(node_allocator_, condition  );
            free_node(node_allocator_, consequent );
            free_node(node_allocator_, alternative);

            return error_node();
         }
         else
            return expression_generator_
                      .conditional(condition, consequent, alternative);
      }

      inline expression_node_ptr parse_conditional_statement()
      {
         expression_node_ptr condition = error_node();

         next_token();

         if (!token_is(token_t::e_lbracket))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR048 - Expected '(' at start of if-statement, instead got: '" + current_token().value + "'",
                          exprtk_error_location));

            return error_node();
         }
         else if (0 == (condition = parse_expression()))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR049 - Failed to parse condition for if-statement",
                          exprtk_error_location));

            return error_node();
         }
         else if (token_is(token_t::e_comma,prsrhlpr_t::e_hold))
         {
            // if (x,y,z)
            return parse_conditional_statement_01(condition);
         }
         else if (token_is(token_t::e_rbracket))
         {
            /*
               00. if (x) y;
               01. if (x) y; else z;
               02. if (x) y; else {z0; ... zn;}
               03. if (x) y; else if (z) w;
               04. if (x) y; else if (z) w; else u;
               05. if (x) y; else if (z) w; else {u0; ... un;}
               06. if (x) y; else if (z) {w0; ... wn;}
               07. if (x) {y0; ... yn;}
               08. if (x) {y0; ... yn;} else z;
               09. if (x) {y0; ... yn;} else {z0; ... zn;};
               10. if (x) {y0; ... yn;} else if (z) w;
               11. if (x) {y0; ... yn;} else if (z) w; else u;
               12. if (x) {y0; ... nex;} else if (z) w; else {u0 ... un;}
               13. if (x) {y0; ... yn;} else if (z) {w0; ... wn;}
            */
            return parse_conditional_statement_02(condition);
         }

         set_error(
            make_error(parser_error::e_syntax,
                       current_token(),
                       "ERR050 - Invalid if-statement",
                       exprtk_error_location));

         free_node(node_allocator_,condition);

         return error_node();
      }

      inline expression_node_ptr parse_ternary_conditional_statement(expression_node_ptr condition)
      {
         // Parse: [condition][?][consequent][:][alternative]
         expression_node_ptr consequent  = error_node();
         expression_node_ptr alternative = error_node();

         bool result = true;

         if (0 == condition)
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR051 - Encountered invalid condition branch for ternary if-statement",
                          exprtk_error_location));

            return error_node();
         }
         else if (!token_is(token_t::e_ternary))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR052 - Expected '?' after condition of ternary if-statement",
                          exprtk_error_location));

            result = false;
         }
         else if (0 == (consequent = parse_expression()))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR053 - Failed to parse consequent for ternary if-statement",
                          exprtk_error_location));

            result = false;
         }
         else if (!token_is(token_t::e_colon))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR054 - Expected ':' between ternary if-statement consequent and alternative",
                          exprtk_error_location));

            result = false;
         }
         else if (0 == (alternative = parse_expression()))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR055 - Failed to parse alternative for ternary if-statement",
                          exprtk_error_location));

            result = false;
         }

         #ifndef exprtk_disable_string_capabilities
         if (result)
         {
            const bool consq_is_str = is_generally_string_node(consequent );
            const bool alter_is_str = is_generally_string_node(alternative);

            if (consq_is_str || alter_is_str)
            {
               if (consq_is_str && alter_is_str)
               {
                  return expression_generator_
                           .conditional_string(condition, consequent, alternative);
               }

               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR056 - Return types of ternary differ: string/non-string",
                             exprtk_error_location));

               result = false;
            }
         }
         #endif

         if (result)
         {
            const bool consq_is_vec = is_ivector_node(consequent );
            const bool alter_is_vec = is_ivector_node(alternative);

            if (consq_is_vec || alter_is_vec)
            {
               if (consq_is_vec && alter_is_vec)
               {
                  return expression_generator_
                           .conditional_vector(condition, consequent, alternative);
               }

               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR057 - Return types of ternary differ: vector/non-vector",
                             exprtk_error_location));

               result = false;
            }
         }

         if (!result)
         {
            free_node(node_allocator_, condition  );
            free_node(node_allocator_, consequent );
            free_node(node_allocator_, alternative);

            return error_node();
         }
         else
            return expression_generator_
                      .conditional(condition, consequent, alternative);
      }

      inline expression_node_ptr parse_not_statement()
      {
         if (settings_.logic_disabled("not"))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR058 - Invalid or disabled logic operation 'not'",
                          exprtk_error_location));

            return error_node();
         }

         return parse_base_operation();
      }

      void handle_brkcnt_scope_exit()
      {
         assert(!brkcnt_list_.empty());
         brkcnt_list_.pop_front();
      }

      inline expression_node_ptr parse_while_loop()
      {
         // Parse: [while][(][test expr][)][{][expression][}]
         expression_node_ptr condition   = error_node();
         expression_node_ptr branch      = error_node();
         expression_node_ptr result_node = error_node();

         bool result = true;

         next_token();

         if (!token_is(token_t::e_lbracket))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR059 - Expected '(' at start of while-loop condition statement",
                          exprtk_error_location));

            return error_node();
         }
         else if (0 == (condition = parse_expression()))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR060 - Failed to parse condition for while-loop",
                          exprtk_error_location));

            return error_node();
         }
         else if (!token_is(token_t::e_rbracket))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR061 - Expected ')' at end of while-loop condition statement",
                          exprtk_error_location));

            result = false;
         }

         brkcnt_list_.push_front(false);

         if (result)
         {
            scoped_inc_dec sid(state_.parsing_loop_stmt_count);

            if (0 == (branch = parse_multi_sequence("while-loop", true)))
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR062 - Failed to parse body of while-loop"));
               result = false;
            }
            else if (0 == (result_node = expression_generator_.while_loop(condition,
                                                                          branch,
                                                                          brkcnt_list_.front())))
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR063 - Failed to synthesize while-loop",
                             exprtk_error_location));

               result = false;
            }
         }

         handle_brkcnt_scope_exit();

         if (!result)
         {
            free_node(node_allocator_, branch     );
            free_node(node_allocator_, condition  );
            free_node(node_allocator_, result_node);

            return error_node();
         }

         return result_node;
      }

      inline expression_node_ptr parse_repeat_until_loop()
      {
         // Parse: [repeat][{][expression][}][until][(][test expr][)]
         expression_node_ptr condition = error_node();
         expression_node_ptr branch    = error_node();
         next_token();

         std::vector<expression_node_ptr> arg_list;
         std::vector<bool> side_effect_list;

         scoped_vec_delete<expression_node_t> sdd((*this),arg_list);

         brkcnt_list_.push_front(false);

         if (details::imatch(current_token().value,"until"))
         {
            next_token();
            branch = node_allocator_.allocate<details::null_node<T> >();
         }
         else
         {
            const token_t::token_type seperator = token_t::e_eof;

            scope_handler sh(*this);

            scoped_bool_or_restorer sbr(state_.side_effect_present);

            scoped_inc_dec sid(state_.parsing_loop_stmt_count);

            for ( ; ; )
            {
               state_.side_effect_present = false;

               expression_node_ptr arg = parse_expression();

               if (0 == arg)
                  return error_node();
               else
               {
                  arg_list.push_back(arg);
                  side_effect_list.push_back(state_.side_effect_present);
               }

               if (details::imatch(current_token().value,"until"))
               {
                  next_token();
                  break;
               }

               const bool is_next_until = peek_token_is(token_t::e_symbol) &&
                                          peek_token_is("until");

               if (!token_is(seperator) && is_next_until)
               {
                  set_error(
                     make_error(parser_error::e_syntax,
                                current_token(),
                                "ERR064 - Expected '" + token_t::to_str(seperator) + "' in body of repeat until loop",
                                exprtk_error_location));

                  return error_node();
               }

               if (details::imatch(current_token().value,"until"))
               {
                  next_token();
                  break;
               }
            }

            branch = simplify(arg_list,side_effect_list);

            sdd.delete_ptr = (0 == branch);

            if (sdd.delete_ptr)
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR065 - Failed to parse body of repeat until loop",
                             exprtk_error_location));

               return error_node();
            }
         }

         if (!token_is(token_t::e_lbracket))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR066 - Expected '(' before condition statement of repeat until loop",
                          exprtk_error_location));

            free_node(node_allocator_,branch);
            return error_node();
         }
         else if (0 == (condition = parse_expression()))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR067 - Failed to parse condition for repeat until loop",
                          exprtk_error_location));

            free_node(node_allocator_,branch);
            return error_node();
         }
         else if (!token_is(token_t::e_rbracket))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR068 - Expected ')' after condition of repeat until loop",
                          exprtk_error_location));

            free_node(node_allocator_, branch   );
            free_node(node_allocator_, condition);

            return error_node();
         }

         expression_node_ptr result;

         result = expression_generator_
                     .repeat_until_loop(condition, branch, brkcnt_list_.front());

         if (0 == result)
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR069 - Failed to synthesize repeat until loop",
                          exprtk_error_location));

            free_node(node_allocator_,condition);

            return error_node();
         }

         handle_brkcnt_scope_exit();

         return result;
      }

      inline expression_node_ptr parse_for_loop()
      {
         expression_node_ptr initialiser = error_node();
         expression_node_ptr condition   = error_node();
         expression_node_ptr incrementor = error_node();
         expression_node_ptr loop_body   = error_node();

         scope_element* se = 0;
         bool result       = true;

         next_token();

         scope_handler sh(*this);

         if (!token_is(token_t::e_lbracket))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR070 - Expected '(' at start of for-loop",
                          exprtk_error_location));

            return error_node();
         }

         if (!token_is(token_t::e_eof))
         {
            if (
                 !token_is(token_t::e_symbol,prsrhlpr_t::e_hold) &&
                 details::imatch(current_token().value,"var")
               )
            {
               next_token();

               if (!token_is(token_t::e_symbol,prsrhlpr_t::e_hold))
               {
                  set_error(
                     make_error(parser_error::e_syntax,
                                current_token(),
                                "ERR071 - Expected a variable at the start of initialiser section of for-loop",
                                exprtk_error_location));

                  return error_node();
               }
               else if (!peek_token_is(token_t::e_assign))
               {
                  set_error(
                     make_error(parser_error::e_syntax,
                                current_token(),
                                "ERR072 - Expected variable assignment of initialiser section of for-loop",
                                exprtk_error_location));

                  return error_node();
               }

               const std::string loop_counter_symbol = current_token().value;

               se = &sem_.get_element(loop_counter_symbol);

               if ((se->name == loop_counter_symbol) && se->active)
               {
                  set_error(
                     make_error(parser_error::e_syntax,
                                current_token(),
                                "ERR073 - For-loop variable '" + loop_counter_symbol+ "' is being shadowed by a previous declaration",
                                exprtk_error_location));

                  return error_node();
               }
               else if (!symtab_store_.is_variable(loop_counter_symbol))
               {
                  if (
                       !se->active &&
                       (se->name == loop_counter_symbol) &&
                       (se->type == scope_element::e_variable)
                     )
                  {
                     se->active = true;
                     se->ref_count++;
                  }
                  else
                  {
                     scope_element nse;
                     nse.name      = loop_counter_symbol;
                     nse.active    = true;
                     nse.ref_count = 1;
                     nse.type      = scope_element::e_variable;
                     nse.depth     = state_.scope_depth;
                     nse.data      = new T(T(0));
                     nse.var_node  = node_allocator_.allocate<variable_node_t>(*reinterpret_cast<T*>(nse.data));

                     if (!sem_.add_element(nse))
                     {
                        set_error(
                           make_error(parser_error::e_syntax,
                                      current_token(),
                                      "ERR074 - Failed to add new local variable '" + loop_counter_symbol + "' to SEM",
                                      exprtk_error_location));

                        sem_.free_element(nse);

                        result = false;
                     }
                     else
                     {
                        exprtk_debug(("parse_for_loop() - INFO - Added new local variable: %s\n",nse.name.c_str()));

                        state_.activate_side_effect("parse_for_loop()");
                     }
                  }
               }
            }

            if (0 == (initialiser = parse_expression()))
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR075 - Failed to parse initialiser of for-loop",
                             exprtk_error_location));

               result = false;
            }
            else if (!token_is(token_t::e_eof))
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR076 - Expected ';' after initialiser of for-loop",
                             exprtk_error_location));

               result = false;
            }
         }

         if (!token_is(token_t::e_eof))
         {
            if (0 == (condition = parse_expression()))
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR077 - Failed to parse condition of for-loop",
                             exprtk_error_location));

               result = false;
            }
            else if (!token_is(token_t::e_eof))
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR078 - Expected ';' after condition section of for-loop",
                             exprtk_error_location));

               result = false;
            }
         }

         if (!token_is(token_t::e_rbracket))
         {
            if (0 == (incrementor = parse_expression()))
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR079 - Failed to parse incrementor of for-loop",
                             exprtk_error_location));

               result = false;
            }
            else if (!token_is(token_t::e_rbracket))
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR080 - Expected ')' after incrementor section of for-loop",
                             exprtk_error_location));

               result = false;
            }
         }

         if (result)
         {
            brkcnt_list_.push_front(false);

            scoped_inc_dec sid(state_.parsing_loop_stmt_count);

            if (0 == (loop_body = parse_multi_sequence("for-loop", true)))
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR081 - Failed to parse body of for-loop",
                             exprtk_error_location));

               result = false;
            }
         }

         if (!result)
         {
            if (se)
            {
               se->ref_count--;
            }

            free_node(node_allocator_, initialiser);
            free_node(node_allocator_, condition  );
            free_node(node_allocator_, incrementor);
            free_node(node_allocator_, loop_body  );
            return error_node();
         }

         expression_node_ptr result_node =
            expression_generator_.for_loop(initialiser,
                                           condition,
                                           incrementor,
                                           loop_body,
                                           brkcnt_list_.front());
         handle_brkcnt_scope_exit();

         return result_node;
      }

      inline expression_node_ptr parse_switch_statement()
      {
         std::vector<expression_node_ptr> arg_list;
         expression_node_ptr result = error_node();

         if (!details::imatch(current_token().value,"switch"))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR082 - Expected keyword 'switch'",
                          exprtk_error_location));

            return error_node();
         }

         scoped_vec_delete<expression_node_t> svd((*this),arg_list);

         next_token();

         if (!token_is(token_t::e_lcrlbracket))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR083 - Expected '{' for call to switch statement",
                          exprtk_error_location));

            return error_node();
         }

         expression_node_ptr default_statement = error_node();

         scoped_expression_delete defstmt_delete((*this), default_statement);

         for ( ; ; )
         {
            if (details::imatch("case",current_token().value))
            {
               next_token();

               expression_node_ptr condition = parse_expression();

               if (0 == condition)
                  return error_node();
               else if (!token_is(token_t::e_colon))
               {
                  set_error(
                     make_error(parser_error::e_syntax,
                                current_token(),
                                "ERR084 - Expected ':' for case of switch statement",
                                exprtk_error_location));

                  free_node(node_allocator_, condition);

                  return error_node();
               }

               expression_node_ptr consequent = parse_expression();

               if (0 == consequent)
               {
                  free_node(node_allocator_, condition);

                  return error_node();
               }
               else if (!token_is(token_t::e_eof))
               {
                  set_error(
                     make_error(parser_error::e_syntax,
                                current_token(),
                                "ERR085 - Expected ';' at end of case for switch statement",
                                exprtk_error_location));

                  free_node(node_allocator_, condition );
                  free_node(node_allocator_, consequent);

                  return error_node();
               }

               // Can we optimise away the case statement?
               if (is_constant_node(condition) && is_false(condition))
               {
                  free_node(node_allocator_, condition );
                  free_node(node_allocator_, consequent);
               }
               else
               {
                  arg_list.push_back(condition );
                  arg_list.push_back(consequent);
               }

            }
            else if (details::imatch("default",current_token().value))
            {
               if (0 != default_statement)
               {
                  set_error(
                     make_error(parser_error::e_syntax,
                                current_token(),
                                "ERR086 - Multiple default cases for switch statement",
                                exprtk_error_location));

                  return error_node();
               }

               next_token();

               if (!token_is(token_t::e_colon))
               {
                  set_error(
                     make_error(parser_error::e_syntax,
                                current_token(),
                                "ERR087 - Expected ':' for default of switch statement",
                                exprtk_error_location));

                  return error_node();
               }

               if (token_is(token_t::e_lcrlbracket,prsrhlpr_t::e_hold))
                  default_statement = parse_multi_sequence("switch-default");
               else
                  default_statement = parse_expression();

               if (0 == default_statement)
                  return error_node();
               else if (!token_is(token_t::e_eof))
               {
                  set_error(
                     make_error(parser_error::e_syntax,
                                current_token(),
                                "ERR088 - Expected ';' at end of default for switch statement",
                                exprtk_error_location));

                  return error_node();
               }
            }
            else if (token_is(token_t::e_rcrlbracket))
               break;
            else
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR089 - Expected '}' at end of switch statement",
                             exprtk_error_location));

               return error_node();
            }
         }

         const bool default_statement_present = (0 != default_statement);

         if (default_statement_present)
         {
            arg_list.push_back(default_statement);
         }

         result = expression_generator_.switch_statement(arg_list, (0 != default_statement));

         svd.delete_ptr = (0 == result);
         defstmt_delete.delete_ptr = (0 == result);

         return result;
      }

      inline expression_node_ptr parse_multi_switch_statement()
      {
         std::vector<expression_node_ptr> arg_list;

         if (!details::imatch(current_token().value,"[*]"))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR090 - Expected token '[*]'",
                          exprtk_error_location));

            return error_node();
         }

         scoped_vec_delete<expression_node_t> svd((*this),arg_list);

         next_token();

         if (!token_is(token_t::e_lcrlbracket))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR091 - Expected '{' for call to [*] statement",
                          exprtk_error_location));

            return error_node();
         }

         for ( ; ; )
         {
            if (!details::imatch("case",current_token().value))
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR092 - Expected a 'case' statement for multi-switch",
                             exprtk_error_location));

               return error_node();
            }

            next_token();

            expression_node_ptr condition = parse_expression();

            if (0 == condition)
               return error_node();

            if (!token_is(token_t::e_colon))
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR093 - Expected ':' for case of [*] statement",
                             exprtk_error_location));

               return error_node();
            }

            expression_node_ptr consequent = parse_expression();

            if (0 == consequent)
               return error_node();

            if (!token_is(token_t::e_eof))
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR094 - Expected ';' at end of case for [*] statement",
                             exprtk_error_location));

               return error_node();
            }

            // Can we optimise away the case statement?
            if (is_constant_node(condition) && is_false(condition))
            {
               free_node(node_allocator_, condition );
               free_node(node_allocator_, consequent);
            }
            else
            {
               arg_list.push_back(condition );
               arg_list.push_back(consequent);
            }

            if (token_is(token_t::e_rcrlbracket,prsrhlpr_t::e_hold))
            {
               break;
            }
         }

         if (!token_is(token_t::e_rcrlbracket))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR095 - Expected '}' at end of [*] statement",
                          exprtk_error_location));

            return error_node();
         }

         const expression_node_ptr result = expression_generator_.multi_switch_statement(arg_list);

         svd.delete_ptr = (0 == result);

         return result;
      }

      inline expression_node_ptr parse_vararg_function()
      {
         std::vector<expression_node_ptr> arg_list;

         details::operator_type opt_type = details::e_default;
         const std::string symbol = current_token().value;

         if (details::imatch(symbol,"~"))
         {
            next_token();
            return parse_multi_sequence();
         }
         else if (details::imatch(symbol,"[*]"))
         {
            return parse_multi_switch_statement();
         }
         else if (details::imatch(symbol, "avg" )) opt_type = details::e_avg ;
         else if (details::imatch(symbol, "mand")) opt_type = details::e_mand;
         else if (details::imatch(symbol, "max" )) opt_type = details::e_max ;
         else if (details::imatch(symbol, "min" )) opt_type = details::e_min ;
         else if (details::imatch(symbol, "mor" )) opt_type = details::e_mor ;
         else if (details::imatch(symbol, "mul" )) opt_type = details::e_prod;
         else if (details::imatch(symbol, "sum" )) opt_type = details::e_sum ;
         else
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR096 - Unsupported built-in vararg function: " + symbol,
                          exprtk_error_location));

            return error_node();
         }

         scoped_vec_delete<expression_node_t> sdd((*this),arg_list);

         lodge_symbol(symbol, e_st_function);

         next_token();

         if (!token_is(token_t::e_lbracket))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR097 - Expected '(' for call to vararg function: " + symbol,
                          exprtk_error_location));

            return error_node();
         }

         if (token_is(token_t::e_rbracket))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR098 - vararg function: " + symbol +
                          " requires at least one input parameter",
                          exprtk_error_location));

            return error_node();
         }

         for ( ; ; )
         {
            expression_node_ptr arg = parse_expression();

            if (0 == arg)
               return error_node();
            else
               arg_list.push_back(arg);

            if (token_is(token_t::e_rbracket))
               break;
            else if (!token_is(token_t::e_comma))
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR099 - Expected ',' for call to vararg function: " + symbol,
                             exprtk_error_location));

               return error_node();
            }
         }

         const expression_node_ptr result = expression_generator_.vararg_function(opt_type,arg_list);

         sdd.delete_ptr = (0 == result);
         return result;
      }

      #ifndef exprtk_disable_string_capabilities
      inline expression_node_ptr parse_string_range_statement(expression_node_ptr& expression)
      {
         if (!token_is(token_t::e_lsqrbracket))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR100 - Expected '[' as start of string range definition",
                          exprtk_error_location));

            free_node(node_allocator_,expression);

            return error_node();
         }
         else if (token_is(token_t::e_rsqrbracket))
         {
            return node_allocator_.allocate<details::string_size_node<T> >(expression);
         }

         range_t rp;

         if (!parse_range(rp,true))
         {
            free_node(node_allocator_,expression);

            return error_node();
         }

         expression_node_ptr result = expression_generator_(expression,rp);

         if (0 == result)
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR101 - Failed to generate string range node",
                          exprtk_error_location));

            free_node(node_allocator_,expression);
            rp.free();
         }

         rp.clear();

         return result;
      }
      #else
      inline expression_node_ptr parse_string_range_statement(expression_node_ptr&)
      {
         return error_node();
      }
      #endif

      inline void parse_pending_string_rangesize(expression_node_ptr& expression)
      {
         // Allow no more than 100 range calls, eg: s[][][]...[][]
         const std::size_t max_rangesize_parses = 100;

         std::size_t i = 0;

         while
            (
              (0 != expression)                     &&
              (i++ < max_rangesize_parses)          &&
              error_list_.empty()                   &&
              is_generally_string_node(expression)  &&
              token_is(token_t::e_lsqrbracket,prsrhlpr_t::e_hold)
            )
         {
            expression = parse_string_range_statement(expression);
         }
      }

      template <typename Allocator1,
                typename Allocator2,
                template <typename, typename> class Sequence>
      inline expression_node_ptr simplify(Sequence<expression_node_ptr,Allocator1>& expression_list,
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

      inline expression_node_ptr parse_multi_sequence(const std::string& source = "",
                                                      const bool enforce_crlbrackets = false)
      {
         token_t::token_type open_bracket  = token_t::e_lcrlbracket;
         token_t::token_type close_bracket = token_t::e_rcrlbracket;
         token_t::token_type seperator     = token_t::e_eof;

         if (!token_is(open_bracket))
         {
            if (!enforce_crlbrackets && token_is(token_t::e_lbracket))
            {
               open_bracket  = token_t::e_lbracket;
               close_bracket = token_t::e_rbracket;
               seperator     = token_t::e_comma;
            }
            else
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR102 - Expected '" + token_t::to_str(open_bracket) + "' for call to multi-sequence" +
                             ((!source.empty()) ? std::string(" section of " + source): ""),
                             exprtk_error_location));

               return error_node();
            }
         }
         else if (token_is(close_bracket))
         {
            return node_allocator_.allocate<details::null_node<T> >();
         }

         std::vector<expression_node_ptr> arg_list;
         std::vector<bool> side_effect_list;

         expression_node_ptr result = error_node();

         scoped_vec_delete<expression_node_t> sdd((*this),arg_list);

         scope_handler sh(*this);

         scoped_bool_or_restorer sbr(state_.side_effect_present);

         for ( ; ; )
         {
            state_.side_effect_present = false;

            expression_node_ptr arg = parse_expression();

            if (0 == arg)
               return error_node();
            else
            {
               arg_list.push_back(arg);
               side_effect_list.push_back(state_.side_effect_present);
            }

            if (token_is(close_bracket))
               break;

            const bool is_next_close = peek_token_is(close_bracket);

            if (!token_is(seperator) && is_next_close)
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR103 - Expected '" + details::to_str(seperator) + "' for call to multi-sequence section of " + source,
                             exprtk_error_location));

               return error_node();
            }

            if (token_is(close_bracket))
               break;
         }

         result = simplify(arg_list, side_effect_list, source.empty());

         sdd.delete_ptr = (0 == result);
         return result;
      }

      inline bool parse_range(range_t& rp, const bool skip_lsqr = false)
      {
         // Examples of valid ranges:
         // 1. [1:5]     -> 1..5
         // 2. [ :5]     -> 0..5
         // 3. [1: ]     -> 1..end
         // 4. [x:y]     -> x..y where x <= y
         // 5. [x+1:y/2] -> x+1..y/2 where x+1 <= y/2
         // 6. [ :y]     -> 0..y where 0 <= y
         // 7. [x: ]     -> x..end where x <= end

         rp.clear();

         if (!skip_lsqr && !token_is(token_t::e_lsqrbracket))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR104 - Expected '[' for start of range",
                          exprtk_error_location));

            return false;
         }

         if (token_is(token_t::e_colon))
         {
            rp.n0_c.first  = true;
            rp.n0_c.second = 0;
            rp.cache.first = 0;
         }
         else
         {
            expression_node_ptr r0 = parse_expression();

            if (0 == r0)
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR105 - Failed parse begin section of range",
                             exprtk_error_location));

               return false;
            }
            else if (is_constant_node(r0))
            {
               const T r0_value = r0->value();

               if (r0_value >= T(0))
               {
                  rp.n0_c.first  = true;
                  rp.n0_c.second = static_cast<std::size_t>(details::numeric::to_int64(r0_value));
                  rp.cache.first = rp.n0_c.second;
               }

               free_node(node_allocator_,r0);

               if (r0_value < T(0))
               {
                  set_error(
                     make_error(parser_error::e_syntax,
                                current_token(),
                                "ERR106 - Range lower bound less than zero! Constraint: r0 >= 0",
                                exprtk_error_location));

                  return false;
               }
            }
            else
            {
               rp.n0_e.first  = true;
               rp.n0_e.second = r0;
            }

            if (!token_is(token_t::e_colon))
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR107 - Expected ':' for break  in range",
                             exprtk_error_location));

               rp.free();

               return false;
            }
         }

         if (token_is(token_t::e_rsqrbracket))
         {
            rp.n1_c.first  = true;
            rp.n1_c.second = std::numeric_limits<std::size_t>::max();
         }
         else
         {
            expression_node_ptr r1 = parse_expression();

            if (0 == r1)
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR108 - Failed parse end section of range",
                             exprtk_error_location));

               rp.free();

               return false;
            }
            else if (is_constant_node(r1))
            {
               const T r1_value = r1->value();

               if (r1_value >= T(0))
               {
                  rp.n1_c.first   = true;
                  rp.n1_c.second  = static_cast<std::size_t>(details::numeric::to_int64(r1_value));
                  rp.cache.second = rp.n1_c.second;
               }

               free_node(node_allocator_,r1);

               if (r1_value < T(0))
               {
                  set_error(
                     make_error(parser_error::e_syntax,
                                current_token(),
                                "ERR109 - Range upper bound less than zero! Constraint: r1 >= 0",
                                exprtk_error_location));

                  rp.free();

                  return false;
               }
            }
            else
            {
               rp.n1_e.first  = true;
               rp.n1_e.second = r1;
            }

            if (!token_is(token_t::e_rsqrbracket))
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR110 - Expected ']' for start of range",
                             exprtk_error_location));

               rp.free();

               return false;
            }
         }

         if (rp.const_range())
         {
            std::size_t r0 = 0;
            std::size_t r1 = 0;

            bool rp_result = false;

            try
            {
               rp_result = rp(r0, r1);
            }
            catch (std::runtime_error&)
            {}

            if (!rp_result || (r0 > r1))
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR111 - Invalid range, Constraint: r0 <= r1",
                             exprtk_error_location));

               return false;
            }
         }

         return true;
      }

      inline void lodge_symbol(const std::string& symbol,
                               const symbol_type st)
      {
         dec_.add_symbol(symbol,st);
      }

      #ifndef exprtk_disable_string_capabilities
      inline expression_node_ptr parse_string()
      {
         const std::string symbol = current_token().value;

         typedef details::stringvar_node<T>* strvar_node_t;

         expression_node_ptr result   = error_node();
         strvar_node_t const_str_node = static_cast<strvar_node_t>(0);

         scope_element& se = sem_.get_active_element(symbol);

         if (scope_element::e_string == se.type)
         {
            se.active = true;
            result    = se.str_node;
            lodge_symbol(symbol, e_st_local_string);
         }
         else
         {
            typedef typename symtab_store::string_context str_ctxt_t;
            str_ctxt_t str_ctx = symtab_store_.get_string_context(symbol);

            if ((0 == str_ctx.str_var) || !symtab_store_.is_conststr_stringvar(symbol))
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR112 - Unknown string symbol",
                             exprtk_error_location));

               return error_node();
            }

            assert(str_ctx.str_var != 0);
            assert(str_ctx.symbol_table != 0);

            result = str_ctx.str_var;

            if (symtab_store_.is_constant_string(symbol))
            {
               const_str_node = static_cast<strvar_node_t>(result);
               result = expression_generator_(const_str_node->str());
            }
            else if (symbol_table_t::e_immutable == str_ctx.symbol_table->mutability())
            {
               lodge_immutable_symbol(
                  current_token(),
                  make_memory_range(str_ctx.str_var->base(), str_ctx.str_var->size()));
            }

            lodge_symbol(symbol, e_st_string);
         }

         if (peek_token_is(token_t::e_lsqrbracket))
         {
            next_token();

            if (peek_token_is(token_t::e_rsqrbracket))
            {
               next_token();
               next_token();

               if (const_str_node)
               {
                  free_node(node_allocator_,result);

                  return expression_generator_(T(const_str_node->size()));
               }
               else
                  return node_allocator_.allocate<details::stringvar_size_node<T> >
                            (static_cast<details::stringvar_node<T>*>(result)->ref());
            }

            range_t rp;

            if (!parse_range(rp))
            {
               free_node(node_allocator_,result);

               return error_node();
            }
            else if (const_str_node)
            {
               free_node(node_allocator_,result);
               result = expression_generator_(const_str_node->ref(),rp);
            }
            else
               result = expression_generator_(static_cast<details::stringvar_node<T>*>
                           (result)->ref(), rp);

            if (result)
               rp.clear();
         }
         else
            next_token();

         return result;
      }
      #else
      inline expression_node_ptr parse_string()
      {
         return error_node();
      }
      #endif

      #ifndef exprtk_disable_string_capabilities
      inline expression_node_ptr parse_const_string()
      {
         const std::string   const_str = current_token().value;
         expression_node_ptr result    = expression_generator_(const_str);

         if (peek_token_is(token_t::e_lsqrbracket))
         {
            next_token();

            if (peek_token_is(token_t::e_rsqrbracket))
            {
               next_token();
               next_token();

               free_node(node_allocator_,result);

               return expression_generator_(T(const_str.size()));
            }

            range_t rp;

            if (!parse_range(rp))
            {
               free_node(node_allocator_,result);
               rp.free();

               return error_node();
            }

            free_node(node_allocator_,result);

            if (rp.n1_c.first && (rp.n1_c.second == std::numeric_limits<std::size_t>::max()))
            {
               rp.n1_c.second  = const_str.size() - 1;
               rp.cache.second = rp.n1_c.second;
            }

            if (
                 (rp.n0_c.first && (rp.n0_c.second >= const_str.size())) ||
                 (rp.n1_c.first && (rp.n1_c.second >= const_str.size()))
               )
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR113 - Overflow in range for string: '" + const_str + "'[" +
                             (rp.n0_c.first ? details::to_str(static_cast<int>(rp.n0_c.second)) : "?") + ":" +
                             (rp.n1_c.first ? details::to_str(static_cast<int>(rp.n1_c.second)) : "?") + "]",
                             exprtk_error_location));

               rp.free();

               return error_node();
            }

            result = expression_generator_(const_str,rp);

            if (result)
               rp.clear();
         }
         else
            next_token();

         return result;
      }
      #else
      inline expression_node_ptr parse_const_string()
      {
         return error_node();
      }
      #endif

      inline expression_node_ptr parse_vector()
      {
         const std::string symbol = current_token().value;

         vector_holder_ptr vec = vector_holder_ptr(0);

         const scope_element& se = sem_.get_active_element(symbol);

         if (
              !details::imatch(se.name, symbol) ||
              (se.depth > state_.scope_depth)   ||
              (scope_element::e_vector != se.type)
            )
         {
            typedef typename symtab_store::vector_context vec_ctxt_t;
            vec_ctxt_t vec_ctx = symtab_store_.get_vector_context(symbol);

            if (0 == vec_ctx.vector_holder)
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR114 - Symbol '" + symbol+ " not a vector",
                             exprtk_error_location));

               return error_node();
            }

            assert(0 != vec_ctx.vector_holder);
            assert(0 != vec_ctx.symbol_table );

            vec = vec_ctx.vector_holder;

            if (symbol_table_t::e_immutable == vec_ctx.symbol_table->mutability())
            {
               lodge_immutable_symbol(
                  current_token(),
                  make_memory_range(vec->data(), vec->size()));
            }
         }
         else
            vec = se.vec_node;

         assert(0 != vec);

         expression_node_ptr index_expr = error_node();

         next_token();

         if (!token_is(token_t::e_lsqrbracket))
         {
            return node_allocator_.allocate<vector_node_t>(vec);
         }
         else if (token_is(token_t::e_rsqrbracket))
         {
            return expression_generator_(T(vec->size()));
         }
         else if (0 == (index_expr = parse_expression()))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR115 - Failed to parse index for vector: '" + symbol + "'",
                          exprtk_error_location));

            return error_node();
         }
         else if (!token_is(token_t::e_rsqrbracket))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR116 - Expected ']' for index of vector: '" + symbol + "'",
                          exprtk_error_location));

            free_node(node_allocator_,index_expr);

            return error_node();
         }

         // Perform compile-time range check
         if (details::is_constant_node(index_expr))
         {
            const std::size_t index    = static_cast<std::size_t>(details::numeric::to_int32(index_expr->value()));
            const std::size_t vec_size = vec->size();

            if (index >= vec_size)
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR117 - Index of " + details::to_str(index) + " out of range for "
                             "vector '" + symbol + "' of size " + details::to_str(vec_size),
                             exprtk_error_location));

               free_node(node_allocator_,index_expr);

               return error_node();
            }
         }

         return expression_generator_.vector_element(symbol, vec, index_expr);
      }

      inline expression_node_ptr parse_vararg_function_call(ivararg_function<T>* vararg_function, const std::string& vararg_function_name)
      {
         std::vector<expression_node_ptr> arg_list;

         expression_node_ptr result = error_node();

         scoped_vec_delete<expression_node_t> sdd((*this),arg_list);

         next_token();

         if (token_is(token_t::e_lbracket))
         {
            if (token_is(token_t::e_rbracket))
            {
               if (!vararg_function->allow_zero_parameters())
               {
                  set_error(
                     make_error(parser_error::e_syntax,
                                current_token(),
                                "ERR118 - Zero parameter call to vararg function: "
                                + vararg_function_name + " not allowed",
                                exprtk_error_location));

                  return error_node();
               }
            }
            else
            {
               for ( ; ; )
               {
                  expression_node_ptr arg = parse_expression();

                  if (0 == arg)
                     return error_node();
                  else
                     arg_list.push_back(arg);

                  if (token_is(token_t::e_rbracket))
                     break;
                  else if (!token_is(token_t::e_comma))
                  {
                     set_error(
                        make_error(parser_error::e_syntax,
                                   current_token(),
                                   "ERR119 - Expected ',' for call to vararg function: "
                                   + vararg_function_name,
                                   exprtk_error_location));

                     return error_node();
                  }
               }
            }
         }
         else if (!vararg_function->allow_zero_parameters())
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR120 - Zero parameter call to vararg function: "
                          + vararg_function_name + " not allowed",
                          exprtk_error_location));

            return error_node();
         }

         if (arg_list.size() < vararg_function->min_num_args())
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR121 - Invalid number of parameters to call to vararg function: "
                          + vararg_function_name + ", require at least "
                          + details::to_str(static_cast<int>(vararg_function->min_num_args())) + " parameters",
                          exprtk_error_location));

            return error_node();
         }
         else if (arg_list.size() > vararg_function->max_num_args())
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR122 - Invalid number of parameters to call to vararg function: "
                          + vararg_function_name + ", require no more than "
                          + details::to_str(static_cast<int>(vararg_function->max_num_args())) + " parameters",
                          exprtk_error_location));

            return error_node();
         }

         result = expression_generator_.vararg_function_call(vararg_function,arg_list);

         sdd.delete_ptr = (0 == result);

         return result;
      }

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
                      const return_type_t default_return_type)
         : invalid_state_(true)
         , parser_(p)
         , function_name_(func_name)
         , default_return_type_(default_return_type)
         {
            parse_function_prototypes(func_prototypes);
         }

         bool verify(const std::string& param_seq, std::size_t& pseq_index)
         {
            if (function_definition_list_.empty())
               return true;

            std::vector<std::pair<std::size_t,char> > error_list;

            for (std::size_t i = 0; i < function_definition_list_.size(); ++i)
            {
               details::char_t diff_value = 0;
               std::size_t     diff_index = 0;

               const bool result = details::sequence_match(function_definition_list_[i].param_seq,
                                                           param_seq,
                                                           diff_index, diff_value);

              if (result)
              {
                 pseq_index = i;
                 return true;
              }
              else
                 error_list.push_back(std::make_pair(diff_index, diff_value));
            }

            if (1 == error_list.size())
            {
               parser_.
                  set_error(
                     make_error(parser_error::e_syntax,
                                parser_.current_token(),
                                "ERR123 - Failed parameter type check for function '" + function_name_ + "', "
                                "Expected '" + function_definition_list_[0].param_seq +
                                "' call set: '" + param_seq + "'",
                                exprtk_error_location));
            }
            else
            {
               // find first with largest diff_index;
               std::size_t max_diff_index = 0;

               for (std::size_t i = 1; i < error_list.size(); ++i)
               {
                  if (error_list[i].first > error_list[max_diff_index].first)
                  {
                     max_diff_index = i;
                  }
               }

               parser_.
                  set_error(
                     make_error(parser_error::e_syntax,
                                parser_.current_token(),
                                "ERR124 - Failed parameter type check for function '" + function_name_ + "', "
                                "Best match: '" + function_definition_list_[max_diff_index].param_seq +
                                "' call set: '" + param_seq + "'",
                                exprtk_error_location));
            }

            return false;
         }

         std::size_t paramseq_count() const
         {
            return function_definition_list_.size();
         }

         std::string paramseq(const std::size_t& index) const
         {
            return function_definition_list_[index].param_seq;
         }

         return_type_t return_type(const std::size_t& index) const
         {
            return function_definition_list_[index].return_type;
         }

         bool invalid() const
         {
            return !invalid_state_;
         }

         bool allow_zero_parameters() const
         {

            for (std::size_t i = 0; i < function_definition_list_.size(); ++i)
            {
               if (std::string::npos != function_definition_list_[i].param_seq.find("Z"))
               {
                  return true;
               }
            }

            return false;
         }

      private:

         std::vector<std::string> split_param_seq(const std::string& param_seq, const details::char_t delimiter = '|') const
         {
             std::string::const_iterator current_begin = param_seq.begin();
             std::string::const_iterator iter          = param_seq.begin();

             std::vector<std::string> result;

             while (iter != param_seq.end())
             {
                 if (*iter == delimiter)
                 {
                     result.push_back(std::string(current_begin, iter));
                     current_begin = ++iter;
                 }
                 else
                     ++iter;
             }

             if (current_begin != iter)
             {
                 result.push_back(std::string(current_begin, iter));
             }

             return result;
         }

         inline bool is_valid_token(std::string param_seq,
                                    function_prototype_t& funcproto) const
         {
            // Determine return type
            funcproto.return_type = default_return_type_;

            if (param_seq.size() > 2)
            {
               if (':' == param_seq[1])
               {
                  // Note: Only overloaded igeneric functions can have return
                  // type definitions.
                  if (type_checker::e_overload != default_return_type_)
                     return false;

                  switch (param_seq[0])
                  {
                     case 'T' : funcproto.return_type = type_checker::e_numeric;
                                break;

                     case 'S' : funcproto.return_type = type_checker::e_string;
                                break;

                     default  : return false;
                  }

                  param_seq.erase(0,2);
               }
            }

            if (
                 (std::string::npos != param_seq.find("?*")) ||
                 (std::string::npos != param_seq.find("**"))
               )
            {
               return false;
            }
            else if (
                      (std::string::npos == param_seq.find_first_not_of("STV*?|")) ||
                      ("Z" == param_seq)
                    )
            {
               funcproto.param_seq = param_seq;
               return true;
            }

            return false;
         }

         void parse_function_prototypes(const std::string& func_prototypes)
         {
            if (func_prototypes.empty())
               return;

            std::vector<std::string> param_seq_list = split_param_seq(func_prototypes);

            typedef std::map<std::string,std::size_t> param_seq_map_t;
            param_seq_map_t param_seq_map;

            for (std::size_t i = 0; i < param_seq_list.size(); ++i)
            {
               function_prototype_t func_proto;

               if (!is_valid_token(param_seq_list[i], func_proto))
               {
                  invalid_state_ = false;

                  parser_.
                     set_error(
                        make_error(parser_error::e_syntax,
                                   parser_.current_token(),
                                   "ERR125 - Invalid parameter sequence of '" + param_seq_list[i] +
                                   "' for function: " + function_name_,
                                   exprtk_error_location));
                  return;
               }

               param_seq_map_t::const_iterator seq_itr = param_seq_map.find(param_seq_list[i]);

               if (param_seq_map.end() != seq_itr)
               {
                  invalid_state_ = false;

                  parser_.
                     set_error(
                        make_error(parser_error::e_syntax,
                                   parser_.current_token(),
                                   "ERR126 - Function '" + function_name_ + "' has a parameter sequence conflict between " +
                                   "pseq_idx[" + details::to_str(seq_itr->second) + "] and" +
                                   "pseq_idx[" + details::to_str(i) + "] " +
                                   "param seq: " + param_seq_list[i],
                                   exprtk_error_location));
                  return;
               }

               function_definition_list_.push_back(func_proto);
            }
         }

         type_checker(const type_checker&) exprtk_delete;
         type_checker& operator=(const type_checker&) exprtk_delete;

         bool invalid_state_;
         parser_t& parser_;
         std::string function_name_;
         const return_type_t default_return_type_;
         function_definition_list_t function_definition_list_;
      };

      inline expression_node_ptr parse_generic_function_call(igeneric_function<T>* function, const std::string& function_name)
      {
         std::vector<expression_node_ptr> arg_list;

         scoped_vec_delete<expression_node_t> sdd((*this),arg_list);

         next_token();

         std::string param_type_list;

         type_checker tc(
            (*this),
            function_name,
            function->parameter_sequence,
            type_checker::e_string);

         if (tc.invalid())
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR127 - Type checker instantiation failure for generic function: " + function_name,
                          exprtk_error_location));

            return error_node();
         }

         if (token_is(token_t::e_lbracket))
         {
            if (token_is(token_t::e_rbracket))
            {
               if (
                    !function->allow_zero_parameters() &&
                    !tc       .allow_zero_parameters()
                  )
               {
                  set_error(
                     make_error(parser_error::e_syntax,
                                current_token(),
                                "ERR128 - Zero parameter call to generic function: "
                                + function_name + " not allowed",
                                exprtk_error_location));

                  return error_node();
               }
            }
            else
            {
               for ( ; ; )
               {
                  expression_node_ptr arg = parse_expression();

                  if (0 == arg)
                     return error_node();

                  if (is_ivector_node(arg))
                     param_type_list += 'V';
                  else if (is_generally_string_node(arg))
                     param_type_list += 'S';
                  else // Everything else is assumed to be a scalar returning expression
                     param_type_list += 'T';

                  arg_list.push_back(arg);

                  if (token_is(token_t::e_rbracket))
                     break;
                  else if (!token_is(token_t::e_comma))
                  {
                     set_error(
                        make_error(parser_error::e_syntax,
                                   current_token(),
                                   "ERR129 - Expected ',' for call to generic function: " + function_name,
                                   exprtk_error_location));

                     return error_node();
                  }
               }
            }
         }
         else if (
                   !function->parameter_sequence.empty() &&
                   function->allow_zero_parameters    () &&
                   !tc      .allow_zero_parameters    ()
                 )
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR130 - Zero parameter call to generic function: "
                          + function_name + " not allowed",
                          exprtk_error_location));

            return error_node();
         }

         std::size_t param_seq_index = 0;

         if (
              state_.type_check_enabled &&
              !tc.verify(param_type_list, param_seq_index)
            )
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR131 - Invalid input parameter sequence for call to generic function: " + function_name,
                          exprtk_error_location));

            return error_node();
         }

         expression_node_ptr result = error_node();

         if (tc.paramseq_count() <= 1)
            result = expression_generator_
                       .generic_function_call(function, arg_list);
         else
            result = expression_generator_
                       .generic_function_call(function, arg_list, param_seq_index);

         sdd.delete_ptr = (0 == result);

         return result;
      }

      inline bool parse_igeneric_function_params(std::string& param_type_list,
                                                 std::vector<expression_node_ptr>& arg_list,
                                                 const std::string& function_name,
                                                 igeneric_function<T>* function,
                                                 const type_checker& tc)
      {
         if (token_is(token_t::e_lbracket))
         {
            if (token_is(token_t::e_rbracket))
            {
               if (
                    !function->allow_zero_parameters() &&
                    !tc       .allow_zero_parameters()
                  )
               {
                  set_error(
                     make_error(parser_error::e_syntax,
                                current_token(),
                                "ERR132 - Zero parameter call to generic function: "
                                + function_name + " not allowed",
                                exprtk_error_location));

                  return false;
               }
            }
            else
            {
               for ( ; ; )
               {
                  expression_node_ptr arg = parse_expression();

                  if (0 == arg)
                     return false;

                  if (is_ivector_node(arg))
                     param_type_list += 'V';
                  else if (is_generally_string_node(arg))
                     param_type_list += 'S';
                  else // Everything else is a scalar returning expression
                     param_type_list += 'T';

                  arg_list.push_back(arg);

                  if (token_is(token_t::e_rbracket))
                     break;
                  else if (!token_is(token_t::e_comma))
                  {
                     set_error(
                        make_error(parser_error::e_syntax,
                                   current_token(),
                                   "ERR133 - Expected ',' for call to string function: " + function_name,
                                   exprtk_error_location));

                     return false;
                  }
               }
            }

            return true;
         }
         else
            return false;
      }

      #ifndef exprtk_disable_string_capabilities
      inline expression_node_ptr parse_string_function_call(igeneric_function<T>* function, const std::string& function_name)
      {
         // Move pass the function name
         next_token();

         std::string param_type_list;

         type_checker tc((*this), function_name, function->parameter_sequence, type_checker::e_string);

         if (
              (!function->parameter_sequence.empty()) &&
              (0 == tc.paramseq_count())
            )
         {
            return error_node();
         }

         std::vector<expression_node_ptr> arg_list;
         scoped_vec_delete<expression_node_t> sdd((*this),arg_list);

         if (!parse_igeneric_function_params(param_type_list, arg_list, function_name, function, tc))
         {
            return error_node();
         }

         std::size_t param_seq_index = 0;

         if (!tc.verify(param_type_list, param_seq_index))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR134 - Invalid input parameter sequence for call to string function: " + function_name,
                          exprtk_error_location));

            return error_node();
         }

         expression_node_ptr result = error_node();

         if (tc.paramseq_count() <= 1)
            result = expression_generator_
                       .string_function_call(function, arg_list);
         else
            result = expression_generator_
                       .string_function_call(function, arg_list, param_seq_index);

         sdd.delete_ptr = (0 == result);

         return result;
      }

      inline expression_node_ptr parse_overload_function_call(igeneric_function<T>* function, const std::string& function_name)
      {
         // Move pass the function name
         next_token();

         std::string param_type_list;

         type_checker tc((*this), function_name, function->parameter_sequence, type_checker::e_overload);

         if (
              (!function->parameter_sequence.empty()) &&
              (0 == tc.paramseq_count())
            )
         {
            return error_node();
         }

         std::vector<expression_node_ptr> arg_list;
         scoped_vec_delete<expression_node_t> sdd((*this),arg_list);

         if (!parse_igeneric_function_params(param_type_list, arg_list, function_name, function, tc))
         {
            return error_node();
         }

         std::size_t param_seq_index = 0;

         if (!tc.verify(param_type_list, param_seq_index))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR135 - Invalid input parameter sequence for call to overloaded function: " + function_name,
                          exprtk_error_location));

            return error_node();
         }

         expression_node_ptr result = error_node();

         if (type_checker::e_numeric == tc.return_type(param_seq_index))
         {
            if (tc.paramseq_count() <= 1)
               result = expression_generator_
                          .generic_function_call(function, arg_list);
            else
               result = expression_generator_
                          .generic_function_call(function, arg_list, param_seq_index);
         }
         else if (type_checker::e_string == tc.return_type(param_seq_index))
         {
            if (tc.paramseq_count() <= 1)
               result = expression_generator_
                          .string_function_call(function, arg_list);
            else
               result = expression_generator_
                          .string_function_call(function, arg_list, param_seq_index);
         }
         else
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR136 - Invalid return type for call to overloaded function: " + function_name,
                          exprtk_error_location));
         }

         sdd.delete_ptr = (0 == result);
         return result;
      }
      #endif

      template <typename Type, std::size_t NumberOfParameters>
      struct parse_special_function_impl
      {
         static inline expression_node_ptr process(parser<Type>& p, const details::operator_type opt_type, const std::string& sf_name)
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

      inline expression_node_ptr parse_special_function()
      {
         const std::string sf_name = current_token().value;

         // Expect: $fDD(expr0,expr1,expr2) or $fDD(expr0,expr1,expr2,expr3)
         if (
              !details::is_digit(sf_name[2]) ||
              !details::is_digit(sf_name[3])
            )
         {
            set_error(
               make_error(parser_error::e_token,
                          current_token(),
                          "ERR140 - Invalid special function[1]: " + sf_name,
                          exprtk_error_location));

            return error_node();
         }

         const int id = (sf_name[2] - '0') * 10 +
                        (sf_name[3] - '0');

         if (id >= details::e_sffinal)
         {
            set_error(
               make_error(parser_error::e_token,
                          current_token(),
                          "ERR141 - Invalid special function[2]: " + sf_name,
                          exprtk_error_location));

            return error_node();
         }

         const int sf_3_to_4                   = details::e_sf48;
         const details::operator_type opt_type = details::operator_type(id + 1000);
         const std::size_t NumberOfParameters  = (id < (sf_3_to_4 - 1000)) ? 3U : 4U;

         switch (NumberOfParameters)
         {
            case 3  : return parse_special_function_impl<T,3>::process((*this), opt_type, sf_name);
            case 4  : return parse_special_function_impl<T,4>::process((*this), opt_type, sf_name);
            default : return error_node();
         }
      }

      inline expression_node_ptr parse_null_statement()
      {
         next_token();
         return node_allocator_.allocate<details::null_node<T> >();
      }

      #ifndef exprtk_disable_break_continue
      inline expression_node_ptr parse_break_statement()
      {
         if (state_.parsing_break_stmt)
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR142 - Invoking 'break' within a break call is not allowed",
                          exprtk_error_location));

            return error_node();
         }
         else if (0 == state_.parsing_loop_stmt_count)
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR143 - Invalid use of 'break', allowed only in the scope of a loop",
                          exprtk_error_location));

            return error_node();
         }

         scoped_bool_negator sbn(state_.parsing_break_stmt);

         if (!brkcnt_list_.empty())
         {
            next_token();

            brkcnt_list_.front() = true;

            expression_node_ptr return_expr = error_node();

            if (token_is(token_t::e_lsqrbracket))
            {
               if (0 == (return_expr = parse_expression()))
               {
                  set_error(
                     make_error(parser_error::e_syntax,
                                current_token(),
                                "ERR144 - Failed to parse return expression for 'break' statement",
                                exprtk_error_location));

                  return error_node();
               }
               else if (!token_is(token_t::e_rsqrbracket))
               {
                  set_error(
                     make_error(parser_error::e_syntax,
                                current_token(),
                                "ERR145 - Expected ']' at the completion of break's return expression",
                                exprtk_error_location));

                  free_node(node_allocator_,return_expr);

                  return error_node();
               }
            }

            state_.activate_side_effect("parse_break_statement()");

            return node_allocator_.allocate<details::break_node<T> >(return_expr);
         }
         else
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR146 - Invalid use of 'break', allowed only in the scope of a loop",
                          exprtk_error_location));
         }

         return error_node();
      }

      inline expression_node_ptr parse_continue_statement()
      {
         if (0 == state_.parsing_loop_stmt_count)
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR147 - Invalid use of 'continue', allowed only in the scope of a loop",
                          exprtk_error_location));

            return error_node();
         }
         else
         {
            next_token();

            brkcnt_list_.front() = true;
            state_.activate_side_effect("parse_continue_statement()");

            return node_allocator_.allocate<details::continue_node<T> >();
         }
      }
      #endif

      inline expression_node_ptr parse_define_vector_statement(const std::string& vec_name)
      {
         expression_node_ptr size_expr = error_node();

         if (!token_is(token_t::e_lsqrbracket))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR148 - Expected '[' as part of vector size definition",
                          exprtk_error_location));

            return error_node();
         }
         else if (0 == (size_expr = parse_expression()))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR149 - Failed to determine size of vector '" + vec_name + "'",
                          exprtk_error_location));

            return error_node();
         }
         else if (!is_constant_node(size_expr))
         {
            free_node(node_allocator_,size_expr);

            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR150 - Expected a literal number as size of vector '" + vec_name + "'",
                          exprtk_error_location));

            return error_node();
         }

         const T vector_size = size_expr->value();

         free_node(node_allocator_,size_expr);

         const T max_vector_size = T(2000000000.0);

         if (
              (vector_size <= T(0)) ||
              std::not_equal_to<T>()
              (T(0),vector_size - details::numeric::trunc(vector_size)) ||
              (vector_size > max_vector_size)
            )
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR151 - Invalid vector size. Must be an integer in the range [0,2e9], size: " +
                          details::to_str(details::numeric::to_int32(vector_size)),
                          exprtk_error_location));

            return error_node();
         }

         std::vector<expression_node_ptr> vec_initilizer_list;

         scoped_vec_delete<expression_node_t> svd((*this),vec_initilizer_list);

         bool single_value_initialiser = false;
         bool vec_to_vec_initialiser   = false;
         bool null_initialisation      = false;

         if (!token_is(token_t::e_rsqrbracket))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR152 - Expected ']' as part of vector size definition",
                          exprtk_error_location));

            return error_node();
         }
         else if (!token_is(token_t::e_eof))
         {
            if (!token_is(token_t::e_assign))
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR153 - Expected ':=' as part of vector definition",
                             exprtk_error_location));

               return error_node();
            }
            else if (token_is(token_t::e_lsqrbracket))
            {
               expression_node_ptr initialiser = parse_expression();

               if (0 == initialiser)
               {
                  set_error(
                     make_error(parser_error::e_syntax,
                                current_token(),
                                "ERR154 - Failed to parse single vector initialiser",
                                exprtk_error_location));

                  return error_node();
               }

               vec_initilizer_list.push_back(initialiser);

               if (!token_is(token_t::e_rsqrbracket))
               {
                  set_error(
                     make_error(parser_error::e_syntax,
                                current_token(),
                                "ERR155 - Expected ']' to close single value vector initialiser",
                                exprtk_error_location));

                  return error_node();
               }

               single_value_initialiser = true;
            }
            else if (!token_is(token_t::e_lcrlbracket))
            {
               expression_node_ptr initialiser = error_node();

               // Is this a vector to vector assignment and initialisation?
               if (token_t::e_symbol == current_token().type)
               {
                  // Is it a locally defined vector?
                  const scope_element& se = sem_.get_active_element(current_token().value);

                  if (scope_element::e_vector == se.type)
                  {
                     if (0 != (initialiser = parse_expression()))
                        vec_initilizer_list.push_back(initialiser);
                     else
                        return error_node();
                  }
                  // Are we dealing with a user defined vector?
                  else if (symtab_store_.is_vector(current_token().value))
                  {
                     lodge_symbol(current_token().value, e_st_vector);

                     if (0 != (initialiser = parse_expression()))
                        vec_initilizer_list.push_back(initialiser);
                     else
                        return error_node();
                  }
                  // Are we dealing with a null initialisation vector definition?
                  else if (token_is(token_t::e_symbol,"null"))
                     null_initialisation = true;
               }

               if (!null_initialisation)
               {
                  if (0 == initialiser)
                  {
                     set_error(
                        make_error(parser_error::e_syntax,
                                   current_token(),
                                   "ERR156 - Expected '{' as part of vector initialiser list",
                                   exprtk_error_location));

                     return error_node();
                  }
                  else
                     vec_to_vec_initialiser = true;
               }
            }
            else if (!token_is(token_t::e_rcrlbracket))
            {
               for ( ; ; )
               {
                  expression_node_ptr initialiser = parse_expression();

                  if (0 == initialiser)
                  {
                     set_error(
                        make_error(parser_error::e_syntax,
                                   current_token(),
                                   "ERR157 - Expected '{' as part of vector initialiser list",
                                   exprtk_error_location));

                     return error_node();
                  }
                  else
                     vec_initilizer_list.push_back(initialiser);

                  if (token_is(token_t::e_rcrlbracket))
                     break;

                  const bool is_next_close = peek_token_is(token_t::e_rcrlbracket);

                  if (!token_is(token_t::e_comma) && is_next_close)
                  {
                     set_error(
                        make_error(parser_error::e_syntax,
                                   current_token(),
                                   "ERR158 - Expected ',' between vector initialisers",
                                   exprtk_error_location));

                     return error_node();
                  }

                  if (token_is(token_t::e_rcrlbracket))
                     break;
               }
            }

            if (
                 !token_is(token_t::e_rbracket   , prsrhlpr_t::e_hold) &&
                 !token_is(token_t::e_rcrlbracket, prsrhlpr_t::e_hold) &&
                 !token_is(token_t::e_rsqrbracket, prsrhlpr_t::e_hold)
               )
            {
               if (!token_is(token_t::e_eof))
               {
                  set_error(
                     make_error(parser_error::e_syntax,
                                current_token(),
                                "ERR159 - Expected ';' at end of vector definition",
                                exprtk_error_location));

                  return error_node();
               }
            }

            if (T(vec_initilizer_list.size()) > vector_size)
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR160 - Initialiser list larger than the number of elements in the vector: '" + vec_name + "'",
                             exprtk_error_location));

               return error_node();
            }
         }

         typename symbol_table_t::vector_holder_ptr vec_holder = typename symbol_table_t::vector_holder_ptr(0);

         const std::size_t vec_size = static_cast<std::size_t>(details::numeric::to_int32(vector_size));

         scope_element& se = sem_.get_element(vec_name);

         if (se.name == vec_name)
         {
            if (se.active)
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR161 - Illegal redefinition of local vector: '" + vec_name + "'",
                             exprtk_error_location));

               return error_node();
            }
            else if (
                      (se.size == vec_size) &&
                      (scope_element::e_vector == se.type)
                    )
            {
               vec_holder = se.vec_node;
               se.active  = true;
               se.depth   = state_.scope_depth;
               se.ref_count++;
            }
         }

         if (0 == vec_holder)
         {
            scope_element nse;
            nse.name      = vec_name;
            nse.active    = true;
            nse.ref_count = 1;
            nse.type      = scope_element::e_vector;
            nse.depth     = state_.scope_depth;
            nse.size      = vec_size;
            nse.data      = new T[vec_size];
            nse.vec_node  = new typename scope_element::vector_holder_t(reinterpret_cast<T*>(nse.data),nse.size);

            if (!sem_.add_element(nse))
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR162 - Failed to add new local vector '" + vec_name + "' to SEM",
                             exprtk_error_location));

               sem_.free_element(nse);

               return error_node();
            }

            vec_holder = nse.vec_node;

            exprtk_debug(("parse_define_vector_statement() - INFO - Added new local vector: %s[%d]\n",
                          nse.name.c_str(),
                          static_cast<int>(nse.size)));
         }

         state_.activate_side_effect("parse_define_vector_statement()");

         lodge_symbol(vec_name, e_st_local_vector);

         expression_node_ptr result = error_node();

         if (null_initialisation)
            result = expression_generator_(T(0.0));
         else if (vec_to_vec_initialiser)
         {
            expression_node_ptr vec_node = node_allocator_.allocate<vector_node_t>(vec_holder);

            result = expression_generator_(
                        details::e_assign,
                        vec_node,
                        vec_initilizer_list[0]);
         }
         else
            result = node_allocator_
                        .allocate<details::vector_assignment_node<T> >(
                           (*vec_holder)[0],
                           vec_size,
                           vec_initilizer_list,
                           single_value_initialiser);

         svd.delete_ptr = (0 == result);

         return result;
      }

      #ifndef exprtk_disable_string_capabilities
      inline expression_node_ptr parse_define_string_statement(const std::string& str_name, expression_node_ptr initialisation_expression)
      {
         stringvar_node_t* str_node = reinterpret_cast<stringvar_node_t*>(0);

         scope_element& se = sem_.get_element(str_name);

         if (se.name == str_name)
         {
            if (se.active)
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR163 - Illegal redefinition of local variable: '" + str_name + "'",
                             exprtk_error_location));

               free_node(node_allocator_,initialisation_expression);

               return error_node();
            }
            else if (scope_element::e_string == se.type)
            {
               str_node  = se.str_node;
               se.active = true;
               se.depth  = state_.scope_depth;
               se.ref_count++;
            }
         }

         if (0 == str_node)
         {
            scope_element nse;
            nse.name      = str_name;
            nse.active    = true;
            nse.ref_count = 1;
            nse.type      = scope_element::e_string;
            nse.depth     = state_.scope_depth;
            nse.data      = new std::string;
            nse.str_node  = new stringvar_node_t(*reinterpret_cast<std::string*>(nse.data));

            if (!sem_.add_element(nse))
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR164 - Failed to add new local string variable '" + str_name + "' to SEM",
                             exprtk_error_location));

               free_node(node_allocator_,initialisation_expression);

               sem_.free_element(nse);

               return error_node();
            }

            str_node = nse.str_node;

            exprtk_debug(("parse_define_string_statement() - INFO - Added new local string variable: %s\n",nse.name.c_str()));
         }

         lodge_symbol(str_name, e_st_local_string);

         state_.activate_side_effect("parse_define_string_statement()");

         expression_node_ptr branch[2] = {0};

         branch[0] = str_node;
         branch[1] = initialisation_expression;

         return expression_generator_(details::e_assign,branch);
      }
      #else
      inline expression_node_ptr parse_define_string_statement(const std::string&, expression_node_ptr)
      {
         return error_node();
      }
      #endif

      inline bool local_variable_is_shadowed(const std::string& symbol)
      {
         const scope_element& se = sem_.get_element(symbol);
         return (se.name == symbol) && se.active;
      }

      inline expression_node_ptr parse_define_var_statement()
      {
         if (settings_.vardef_disabled())
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR165 - Illegal variable definition",
                          exprtk_error_location));

            return error_node();
         }
         else if (!details::imatch(current_token().value,"var"))
         {
            return error_node();
         }
         else
            next_token();

         const std::string var_name = current_token().value;

         expression_node_ptr initialisation_expression = error_node();

         if (!token_is(token_t::e_symbol))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR166 - Expected a symbol for variable definition",
                          exprtk_error_location));

            return error_node();
         }
         else if (details::is_reserved_symbol(var_name))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR167 - Illegal redefinition of reserved keyword: '" + var_name + "'",
                          exprtk_error_location));

            return error_node();
         }
         else if (symtab_store_.symbol_exists(var_name))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR168 - Illegal redefinition of variable '" + var_name + "'",
                          exprtk_error_location));

            return error_node();
         }
         else if (local_variable_is_shadowed(var_name))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR169 - Illegal redefinition of local variable: '" + var_name + "'",
                          exprtk_error_location));

            return error_node();
         }
         else if (token_is(token_t::e_lsqrbracket,prsrhlpr_t::e_hold))
         {
            return parse_define_vector_statement(var_name);
         }
         else if (token_is(token_t::e_lcrlbracket,prsrhlpr_t::e_hold))
         {
            return parse_uninitialised_var_statement(var_name);
         }
         else if (token_is(token_t::e_assign))
         {
            if (0 == (initialisation_expression = parse_expression()))
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR170 - Failed to parse initialisation expression",
                             exprtk_error_location));

               return error_node();
            }
         }

         if (
              !token_is(token_t::e_rbracket   , prsrhlpr_t::e_hold) &&
              !token_is(token_t::e_rcrlbracket, prsrhlpr_t::e_hold) &&
              !token_is(token_t::e_rsqrbracket, prsrhlpr_t::e_hold)
            )
         {
            if (!token_is(token_t::e_eof,prsrhlpr_t::e_hold))
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR171 - Expected ';' after variable definition",
                             exprtk_error_location));

               free_node(node_allocator_,initialisation_expression);

               return error_node();
            }
         }

         if (
              (0 != initialisation_expression) &&
              details::is_generally_string_node(initialisation_expression)
            )
         {
            return parse_define_string_statement(var_name,initialisation_expression);
         }

         expression_node_ptr var_node = reinterpret_cast<expression_node_ptr>(0);

         scope_element& se = sem_.get_element(var_name);

         if (se.name == var_name)
         {
            if (se.active)
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR172 - Illegal redefinition of local variable: '" + var_name + "'",
                             exprtk_error_location));

               free_node(node_allocator_, initialisation_expression);

               return error_node();
            }
            else if (scope_element::e_variable == se.type)
            {
               var_node  = se.var_node;
               se.active = true;
               se.depth  = state_.scope_depth;
               se.ref_count++;
            }
         }

         if (0 == var_node)
         {
            scope_element nse;
            nse.name      = var_name;
            nse.active    = true;
            nse.ref_count = 1;
            nse.type      = scope_element::e_variable;
            nse.depth     = state_.scope_depth;
            nse.data      = new T(T(0));
            nse.var_node  = node_allocator_.allocate<variable_node_t>(*reinterpret_cast<T*>(nse.data));

            if (!sem_.add_element(nse))
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR173 - Failed to add new local variable '" + var_name + "' to SEM",
                             exprtk_error_location));

               free_node(node_allocator_, initialisation_expression);

               sem_.free_element(nse);

               return error_node();
            }

            var_node = nse.var_node;

            exprtk_debug(("parse_define_var_statement() - INFO - Added new local variable: %s\n",nse.name.c_str()));
         }

         state_.activate_side_effect("parse_define_var_statement()");

         lodge_symbol(var_name, e_st_local_variable);

         expression_node_ptr branch[2] = {0};

         branch[0] = var_node;
         branch[1] = initialisation_expression ? initialisation_expression : expression_generator_(T(0));

         return expression_generator_(details::e_assign,branch);
      }

      inline expression_node_ptr parse_uninitialised_var_statement(const std::string& var_name)
      {
         if (
              !token_is(token_t::e_lcrlbracket) ||
              !token_is(token_t::e_rcrlbracket)
            )
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR174 - Expected a '{}' for uninitialised var definition",
                          exprtk_error_location));

            return error_node();
         }
         else if (!token_is(token_t::e_eof,prsrhlpr_t::e_hold))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR175 - Expected ';' after uninitialised variable definition",
                          exprtk_error_location));

            return error_node();
         }

         expression_node_ptr var_node = reinterpret_cast<expression_node_ptr>(0);

         scope_element& se = sem_.get_element(var_name);

         if (se.name == var_name)
         {
            if (se.active)
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR176 - Illegal redefinition of local variable: '" + var_name + "'",
                             exprtk_error_location));

               return error_node();
            }
            else if (scope_element::e_variable == se.type)
            {
               var_node  = se.var_node;
               se.active = true;
               se.ref_count++;
            }
         }

         if (0 == var_node)
         {
            scope_element nse;
            nse.name      = var_name;
            nse.active    = true;
            nse.ref_count = 1;
            nse.type      = scope_element::e_variable;
            nse.depth     = state_.scope_depth;
            nse.ip_index  = sem_.next_ip_index();
            nse.data      = new T(T(0));
            nse.var_node  = node_allocator_.allocate<variable_node_t>(*reinterpret_cast<T*>(nse.data));

            if (!sem_.add_element(nse))
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR177 - Failed to add new local variable '" + var_name + "' to SEM",
                             exprtk_error_location));

               sem_.free_element(nse);

               return error_node();
            }

            exprtk_debug(("parse_uninitialised_var_statement() - INFO - Added new local variable: %s\n",
                          nse.name.c_str()));
         }

         lodge_symbol(var_name, e_st_local_variable);

         state_.activate_side_effect("parse_uninitialised_var_statement()");

         return expression_generator_(T(0));
      }

      inline expression_node_ptr parse_swap_statement()
      {
         if (!details::imatch(current_token().value,"swap"))
         {
            return error_node();
         }
         else
            next_token();

         if (!token_is(token_t::e_lbracket))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR178 - Expected '(' at start of swap statement",
                          exprtk_error_location));

            return error_node();
         }

         expression_node_ptr variable0 = error_node();
         expression_node_ptr variable1 = error_node();

         bool variable0_generated = false;
         bool variable1_generated = false;

         const std::string var0_name = current_token().value;

         if (!token_is(token_t::e_symbol,prsrhlpr_t::e_hold))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR179 - Expected a symbol for variable or vector element definition",
                          exprtk_error_location));

            return error_node();
         }
         else if (peek_token_is(token_t::e_lsqrbracket))
         {
            if (0 == (variable0 = parse_vector()))
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR180 - First parameter to swap is an invalid vector element: '" + var0_name + "'",
                             exprtk_error_location));

               return error_node();
            }

            variable0_generated = true;
         }
         else
         {
            if (symtab_store_.is_variable(var0_name))
            {
               variable0 = symtab_store_.get_variable(var0_name);
            }

            const scope_element& se = sem_.get_element(var0_name);

            if (
                 (se.active)            &&
                 (se.name == var0_name) &&
                 (scope_element::e_variable == se.type)
               )
            {
               variable0 = se.var_node;
            }

            lodge_symbol(var0_name, e_st_variable);

            if (0 == variable0)
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR181 - First parameter to swap is an invalid variable: '" + var0_name + "'",
                             exprtk_error_location));

               return error_node();
            }
            else
               next_token();
         }

         if (!token_is(token_t::e_comma))
         {
            set_error(
                make_error(parser_error::e_syntax,
                           current_token(),
                           "ERR182 - Expected ',' between parameters to swap",
                           exprtk_error_location));

            if (variable0_generated)
            {
               free_node(node_allocator_,variable0);
            }

            return error_node();
         }

         const std::string var1_name = current_token().value;

         if (!token_is(token_t::e_symbol,prsrhlpr_t::e_hold))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR183 - Expected a symbol for variable or vector element definition",
                          exprtk_error_location));

            if (variable0_generated)
            {
               free_node(node_allocator_,variable0);
            }

            return error_node();
         }
         else if (peek_token_is(token_t::e_lsqrbracket))
         {
            if (0 == (variable1 = parse_vector()))
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR184 - Second parameter to swap is an invalid vector element: '" + var1_name + "'",
                             exprtk_error_location));

               if (variable0_generated)
               {
                  free_node(node_allocator_,variable0);
               }

               return error_node();
            }

            variable1_generated = true;
         }
         else
         {
            if (symtab_store_.is_variable(var1_name))
            {
               variable1 = symtab_store_.get_variable(var1_name);
            }

            const scope_element& se = sem_.get_element(var1_name);

            if (
                 (se.active) &&
                 (se.name == var1_name) &&
                 (scope_element::e_variable == se.type)
               )
            {
               variable1 = se.var_node;
            }

            lodge_symbol(var1_name, e_st_variable);

            if (0 == variable1)
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR185 - Second parameter to swap is an invalid variable: '" + var1_name + "'",
                             exprtk_error_location));

               if (variable0_generated)
               {
                  free_node(node_allocator_,variable0);
               }

               return error_node();
            }
            else
               next_token();
         }

         if (!token_is(token_t::e_rbracket))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR186 - Expected ')' at end of swap statement",
                          exprtk_error_location));

            if (variable0_generated)
            {
               free_node(node_allocator_,variable0);
            }

            if (variable1_generated)
            {
               free_node(node_allocator_,variable1);
            }

            return error_node();
         }

         typedef details::variable_node<T>* variable_node_ptr;

         variable_node_ptr v0 = variable_node_ptr(0);
         variable_node_ptr v1 = variable_node_ptr(0);

         expression_node_ptr result = error_node();

         if (
              (0 != (v0 = dynamic_cast<variable_node_ptr>(variable0))) &&
              (0 != (v1 = dynamic_cast<variable_node_ptr>(variable1)))
            )
         {
            result = node_allocator_.allocate<details::swap_node<T> >(v0, v1);

            if (variable0_generated)
            {
               free_node(node_allocator_,variable0);
            }

            if (variable1_generated)
            {
               free_node(node_allocator_,variable1);
            }
         }
         else
            result = node_allocator_.allocate<details::swap_generic_node<T> >
                        (variable0, variable1);

         state_.activate_side_effect("parse_swap_statement()");

         return result;
      }

      #ifndef exprtk_disable_return_statement
      inline expression_node_ptr parse_return_statement()
      {
         if (state_.parsing_return_stmt)
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR187 - Return call within a return call is not allowed",
                          exprtk_error_location));

            return error_node();
         }

         scoped_bool_negator sbn(state_.parsing_return_stmt);

         std::vector<expression_node_ptr> arg_list;

         scoped_vec_delete<expression_node_t> sdd((*this),arg_list);

         if (!details::imatch(current_token().value,"return"))
         {
            return error_node();
         }
         else
            next_token();

         if (!token_is(token_t::e_lsqrbracket))
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR188 - Expected '[' at start of return statement",
                          exprtk_error_location));

            return error_node();
         }
         else if (!token_is(token_t::e_rsqrbracket))
         {
            for ( ; ; )
            {
               expression_node_ptr arg = parse_expression();

               if (0 == arg)
                  return error_node();

               arg_list.push_back(arg);

               if (token_is(token_t::e_rsqrbracket))
                  break;
               else if (!token_is(token_t::e_comma))
               {
                  set_error(
                     make_error(parser_error::e_syntax,
                                current_token(),
                                "ERR189 - Expected ',' between values during call to return",
                                exprtk_error_location));

                  return error_node();
               }
            }
         }
         else if (settings_.zero_return_disabled())
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR190 - Zero parameter return statement not allowed",
                          exprtk_error_location));

            return error_node();
         }

         const lexer::token prev_token = current_token();

         if (token_is(token_t::e_rsqrbracket))
         {
            if (!arg_list.empty())
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             prev_token,
                             "ERR191 - Invalid ']' found during return call",
                             exprtk_error_location));

               return error_node();
            }
         }

         std::string ret_param_type_list;

         for (std::size_t i = 0; i < arg_list.size(); ++i)
         {
            if (0 == arg_list[i])
               return error_node();
            else if (is_ivector_node(arg_list[i]))
               ret_param_type_list += 'V';
            else if (is_generally_string_node(arg_list[i]))
               ret_param_type_list += 'S';
            else
               ret_param_type_list += 'T';
         }

         dec_.retparam_list_.push_back(ret_param_type_list);

         expression_node_ptr result = expression_generator_.return_call(arg_list);

         sdd.delete_ptr = (0 == result);

         state_.return_stmt_present = true;

         state_.activate_side_effect("parse_return_statement()");

         return result;
      }
      #else
      inline expression_node_ptr parse_return_statement()
      {
         return error_node();
      }
      #endif

      inline bool post_variable_process(const std::string& symbol)
      {
         if (
              peek_token_is(token_t::e_lbracket   ) ||
              peek_token_is(token_t::e_lcrlbracket) ||
              peek_token_is(token_t::e_lsqrbracket)
            )
         {
            if (!settings_.commutative_check_enabled())
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR192 - Invalid sequence of variable '" + symbol + "' and bracket",
                             exprtk_error_location));

               return false;
            }

            lexer().insert_front(token_t::e_mul);
         }

         return true;
      }

      inline bool post_bracket_process(const typename token_t::token_type& token, expression_node_ptr& branch)
      {
         bool implied_mul = false;

         if (details::is_generally_string_node(branch))
            return true;

         const lexer::parser_helper::token_advance_mode hold = prsrhlpr_t::e_hold;

         switch (token)
         {
            case token_t::e_lcrlbracket : implied_mul = token_is(token_t::e_lbracket   ,hold) ||
                                                        token_is(token_t::e_lcrlbracket,hold) ||
                                                        token_is(token_t::e_lsqrbracket,hold) ;
                                          break;

            case token_t::e_lbracket    : implied_mul = token_is(token_t::e_lbracket   ,hold) ||
                                                        token_is(token_t::e_lcrlbracket,hold) ||
                                                        token_is(token_t::e_lsqrbracket,hold) ;
                                          break;

            case token_t::e_lsqrbracket : implied_mul = token_is(token_t::e_lbracket   ,hold) ||
                                                        token_is(token_t::e_lcrlbracket,hold) ||
                                                        token_is(token_t::e_lsqrbracket,hold) ;
                                          break;

            default                     : return true;
         }

         if (implied_mul)
         {
            if (!settings_.commutative_check_enabled())
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR193 - Invalid sequence of brackets",
                             exprtk_error_location));

               return false;
            }
            else if (token_t::e_eof != current_token().type)
            {
               lexer().insert_front(current_token().type);
               lexer().insert_front(token_t::e_mul);
               next_token();
            }
         }

         return true;
      }

      typedef typename interval_container_t<const void*>::interval_t interval_t;
      typedef interval_container_t<const void*> immutable_memory_map_t;
      typedef std::map<interval_t,token_t> immutable_symtok_map_t;

      inline interval_t make_memory_range(const T& t)
      {
         const T* begin = reinterpret_cast<const T*>(&t);
         const T* end   = begin + 1;
         return interval_t(begin, end);
      }

      inline interval_t make_memory_range(const T* begin, const std::size_t size)
      {
         return interval_t(begin, begin + size);
      }

      inline interval_t make_memory_range(details::char_cptr begin, const std::size_t size)
      {
         return interval_t(begin, begin + size);
      }

      void lodge_immutable_symbol(const lexer::token& token, const interval_t interval)
      {
         immutable_memory_map_.add_interval(interval);
         immutable_symtok_map_[interval] = token;
      }

      inline expression_node_ptr parse_symtab_symbol()
      {
         const std::string symbol = current_token().value;

         // Are we dealing with a variable or a special constant?
         typedef typename symtab_store::variable_context var_ctxt_t;
         var_ctxt_t var_ctx = symtab_store_.get_variable_context(symbol);

         if (var_ctx.variable)
         {
            assert(var_ctx.symbol_table);

            expression_node_ptr result_variable = var_ctx.variable;

            if (symtab_store_.is_constant_node(symbol))
            {
               result_variable = expression_generator_(var_ctx.variable->value());
            }
            else if (symbol_table_t::e_immutable == var_ctx.symbol_table->mutability())
            {
               lodge_immutable_symbol(current_token(), make_memory_range(var_ctx.variable->ref()));
               result_variable = var_ctx.variable;
            }

            if (!post_variable_process(symbol))
               return error_node();

            lodge_symbol(symbol, e_st_variable);

            next_token();

            return result_variable;
         }

         // Are we dealing with a locally defined variable, vector or string?
         if (!sem_.empty())
         {
            scope_element& se = sem_.get_active_element(symbol);

            if (se.active && details::imatch(se.name, symbol))
            {
               if (scope_element::e_variable == se.type)
               {
                  se.active = true;
                  lodge_symbol(symbol, e_st_local_variable);

                  if (!post_variable_process(symbol))
                     return error_node();

                  next_token();

                  return se.var_node;
               }
               else if (scope_element::e_vector == se.type)
               {
                  return parse_vector();
               }
               #ifndef exprtk_disable_string_capabilities
               else if (scope_element::e_string == se.type)
               {
                  return parse_string();
               }
               #endif
            }
         }

         #ifndef exprtk_disable_string_capabilities
         // Are we dealing with a string variable?
         if (symtab_store_.is_stringvar(symbol))
         {
            return parse_string();
         }
         #endif

         {
            // Are we dealing with a function?
            ifunction<T>* function = symtab_store_.get_function(symbol);

            if (function)
            {
               lodge_symbol(symbol, e_st_function);

               expression_node_ptr func_node =
                                      parse_function_invocation(function,symbol);

               if (func_node)
                  return func_node;
               else
               {
                  set_error(
                     make_error(parser_error::e_syntax,
                                current_token(),
                                "ERR194 - Failed to generate node for function: '" + symbol + "'",
                                exprtk_error_location));

                  return error_node();
               }
            }
         }

         {
            // Are we dealing with a vararg function?
            ivararg_function<T>* vararg_function = symtab_store_.get_vararg_function(symbol);

            if (vararg_function)
            {
               lodge_symbol(symbol, e_st_function);

               expression_node_ptr vararg_func_node =
                                      parse_vararg_function_call(vararg_function, symbol);

               if (vararg_func_node)
                  return vararg_func_node;
               else
               {
                  set_error(
                     make_error(parser_error::e_syntax,
                                current_token(),
                                "ERR195 - Failed to generate node for vararg function: '" + symbol + "'",
                                exprtk_error_location));

                  return error_node();
               }
            }
         }

         {
            // Are we dealing with a vararg generic function?
            igeneric_function<T>* generic_function = symtab_store_.get_generic_function(symbol);

            if (generic_function)
            {
               lodge_symbol(symbol, e_st_function);

               expression_node_ptr genericfunc_node =
                                      parse_generic_function_call(generic_function, symbol);

               if (genericfunc_node)
                  return genericfunc_node;
               else
               {
                  set_error(
                     make_error(parser_error::e_syntax,
                                current_token(),
                                "ERR196 - Failed to generate node for generic function: '" + symbol + "'",
                                exprtk_error_location));

                  return error_node();
               }
            }
         }

         #ifndef exprtk_disable_string_capabilities
         {
            // Are we dealing with a vararg string returning function?
            igeneric_function<T>* string_function = symtab_store_.get_string_function(symbol);

            if (string_function)
            {
               lodge_symbol(symbol, e_st_function);

               expression_node_ptr stringfunc_node =
                                      parse_string_function_call(string_function, symbol);

               if (stringfunc_node)
                  return stringfunc_node;
               else
               {
                  set_error(
                     make_error(parser_error::e_syntax,
                                current_token(),
                                "ERR197 - Failed to generate node for string function: '" + symbol + "'",
                                exprtk_error_location));

                  return error_node();
               }
            }
         }

         {
            // Are we dealing with a vararg overloaded scalar/string returning function?
            igeneric_function<T>* overload_function = symtab_store_.get_overload_function(symbol);

            if (overload_function)
            {
               lodge_symbol(symbol, e_st_function);

               expression_node_ptr overloadfunc_node =
                                      parse_overload_function_call(overload_function, symbol);

               if (overloadfunc_node)
                  return overloadfunc_node;
               else
               {
                  set_error(
                     make_error(parser_error::e_syntax,
                                current_token(),
                                "ERR198 - Failed to generate node for overload function: '" + symbol + "'",
                                exprtk_error_location));

                  return error_node();
               }
            }
         }
         #endif

         // Are we dealing with a vector?
         if (symtab_store_.is_vector(symbol))
         {
            lodge_symbol(symbol, e_st_vector);
            return parse_vector();
         }

         if (details::is_reserved_symbol(symbol))
         {
               if (
                    settings_.function_enabled(symbol) ||
                    !details::is_base_function(symbol)
                  )
               {
                  set_error(
                     make_error(parser_error::e_syntax,
                                current_token(),
                                "ERR199 - Invalid use of reserved symbol '" + symbol + "'",
                                exprtk_error_location));

                  return error_node();
               }
         }

         // Should we handle unknown symbols?
         if (resolve_unknown_symbol_ && unknown_symbol_resolver_)
         {
            if (!(settings_.rsrvd_sym_usr_disabled() && details::is_reserved_symbol(symbol)))
            {
               symbol_table_t& symtab = symtab_store_.get_symbol_table();

               std::string error_message;

               if (unknown_symbol_resolver::e_usrmode_default == unknown_symbol_resolver_->mode)
               {
                  T default_value = T(0);

                  typename unknown_symbol_resolver::usr_symbol_type usr_symbol_type = unknown_symbol_resolver::e_usr_unknown_type;

                  if (unknown_symbol_resolver_->process(symbol, usr_symbol_type, default_value, error_message))
                  {
                     bool create_result = false;

                     switch (usr_symbol_type)
                     {
                        case unknown_symbol_resolver::e_usr_variable_type : create_result = symtab.create_variable(symbol, default_value);
                                                                            break;

                        case unknown_symbol_resolver::e_usr_constant_type : create_result = symtab.add_constant(symbol, default_value);
                                                                            break;

                        default                                           : create_result = false;
                     }

                     if (create_result)
                     {
                        expression_node_ptr var = symtab_store_.get_variable(symbol);

                        if (var)
                        {
                           if (symtab_store_.is_constant_node(symbol))
                           {
                              var = expression_generator_(var->value());
                           }

                           lodge_symbol(symbol, e_st_variable);

                           if (!post_variable_process(symbol))
                              return error_node();

                           next_token();

                           return var;
                        }
                     }
                  }

                  set_error(
                     make_error(parser_error::e_symtab,
                                current_token(),
                                "ERR200 - Failed to create variable: '" + symbol + "'" +
                                (error_message.empty() ? "" : " - " + error_message),
                                exprtk_error_location));

               }
               else if (unknown_symbol_resolver::e_usrmode_extended == unknown_symbol_resolver_->mode)
               {
                  if (unknown_symbol_resolver_->process(symbol, symtab, error_message))
                  {
                     expression_node_ptr result = parse_symtab_symbol();

                     if (result)
                     {
                        return result;
                     }
                  }

                  set_error(
                     make_error(parser_error::e_symtab,
                                current_token(),
                                "ERR201 - Failed to resolve symbol: '" + symbol + "'" +
                                (error_message.empty() ? "" : " - " + error_message),
                                exprtk_error_location));
               }

               return error_node();
            }
         }

         set_error(
            make_error(parser_error::e_syntax,
                       current_token(),
                       "ERR202 - Undefined symbol: '" + symbol + "'",
                       exprtk_error_location));

         return error_node();
      }

      inline expression_node_ptr parse_symbol()
      {
         static const std::string symbol_if       = "if"      ;
         static const std::string symbol_while    = "while"   ;
         static const std::string symbol_repeat   = "repeat"  ;
         static const std::string symbol_for      = "for"     ;
         static const std::string symbol_switch   = "switch"  ;
         static const std::string symbol_null     = "null"    ;
         static const std::string symbol_break    = "break"   ;
         static const std::string symbol_continue = "continue";
         static const std::string symbol_var      = "var"     ;
         static const std::string symbol_swap     = "swap"    ;
         static const std::string symbol_return   = "return"  ;
         static const std::string symbol_not      = "not"     ;

         const std::string symbol = current_token().value;

         if (valid_vararg_operation(symbol))
         {
            return parse_vararg_function();
         }
         else if (details::imatch(symbol, symbol_not))
         {
            return parse_not_statement();
         }
         else if (valid_base_operation(symbol))
         {
            return parse_base_operation();
         }
         else if (
                   details::imatch(symbol, symbol_if) &&
                   settings_.control_struct_enabled(symbol)
                 )
         {
            return parse_conditional_statement();
         }
         else if (
                   details::imatch(symbol, symbol_while) &&
                   settings_.control_struct_enabled(symbol)
                 )
         {
            return parse_while_loop();
         }
         else if (
                   details::imatch(symbol, symbol_repeat) &&
                   settings_.control_struct_enabled(symbol)
                 )
         {
            return parse_repeat_until_loop();
         }
         else if (
                   details::imatch(symbol, symbol_for) &&
                   settings_.control_struct_enabled(symbol)
                 )
         {
            return parse_for_loop();
         }
         else if (
                   details::imatch(symbol, symbol_switch) &&
                   settings_.control_struct_enabled(symbol)
                 )
         {
            return parse_switch_statement();
         }
         else if (details::is_valid_sf_symbol(symbol))
         {
            return parse_special_function();
         }
         else if (details::imatch(symbol, symbol_null))
         {
            return parse_null_statement();
         }
         #ifndef exprtk_disable_break_continue
         else if (details::imatch(symbol, symbol_break))
         {
            return parse_break_statement();
         }
         else if (details::imatch(symbol, symbol_continue))
         {
            return parse_continue_statement();
         }
         #endif
         else if (details::imatch(symbol, symbol_var))
         {
            return parse_define_var_statement();
         }
         else if (details::imatch(symbol, symbol_swap))
         {
            return parse_swap_statement();
         }
         #ifndef exprtk_disable_return_statement
         else if (
                   details::imatch(symbol, symbol_return) &&
                   settings_.control_struct_enabled(symbol)
                 )
         {
            return parse_return_statement();
         }
         #endif
         else if (symtab_store_.valid() || !sem_.empty())
         {
            return parse_symtab_symbol();
         }
         else
         {
            set_error(
               make_error(parser_error::e_symtab,
                          current_token(),
                          "ERR203 - Variable or function detected, yet symbol-table is invalid, Symbol: " + symbol,
                          exprtk_error_location));

            return error_node();
         }
      }

      inline expression_node_ptr parse_branch(precedence_level precedence = e_level00)
      {
         stack_limit_handler slh(*this);

         if (!slh)
         {
            return error_node();
         }

         expression_node_ptr branch = error_node();

         if (token_t::e_number == current_token().type)
         {
            T numeric_value = T(0);

            if (details::string_to_real(current_token().value, numeric_value))
            {
               expression_node_ptr literal_exp = expression_generator_(numeric_value);

               if (0 == literal_exp)
               {
                  set_error(
                     make_error(parser_error::e_numeric,
                                current_token(),
                                "ERR204 - Failed generate node for scalar: '" + current_token().value + "'",
                                exprtk_error_location));

                  return error_node();
               }

               next_token();
               branch = literal_exp;
            }
            else
            {
               set_error(
                  make_error(parser_error::e_numeric,
                             current_token(),
                             "ERR205 - Failed to convert '" + current_token().value + "' to a number",
                             exprtk_error_location));

               return error_node();
            }
         }
         else if (token_t::e_symbol == current_token().type)
         {
            branch = parse_symbol();
         }
         #ifndef exprtk_disable_string_capabilities
         else if (token_t::e_string == current_token().type)
         {
            branch = parse_const_string();
         }
         #endif
         else if (token_t::e_lbracket == current_token().type)
         {
            next_token();

            if (0 == (branch = parse_expression()))
               return error_node();
            else if (!token_is(token_t::e_rbracket))
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR206 - Expected ')' instead of: '" + current_token().value + "'",
                             exprtk_error_location));

               details::free_node(node_allocator_,branch);

               return error_node();
            }
            else if (!post_bracket_process(token_t::e_lbracket,branch))
            {
               details::free_node(node_allocator_,branch);

               return error_node();
            }
         }
         else if (token_t::e_lsqrbracket == current_token().type)
         {
            next_token();

            if (0 == (branch = parse_expression()))
               return error_node();
            else if (!token_is(token_t::e_rsqrbracket))
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR207 - Expected ']' instead of: '" + current_token().value + "'",
                             exprtk_error_location));

               details::free_node(node_allocator_,branch);

               return error_node();
            }
            else if (!post_bracket_process(token_t::e_lsqrbracket,branch))
            {
               details::free_node(node_allocator_,branch);

               return error_node();
            }
         }
         else if (token_t::e_lcrlbracket == current_token().type)
         {
            next_token();

            if (0 == (branch = parse_expression()))
               return error_node();
            else if (!token_is(token_t::e_rcrlbracket))
            {
               set_error(
                  make_error(parser_error::e_syntax,
                             current_token(),
                             "ERR208 - Expected '}' instead of: '" + current_token().value + "'",
                             exprtk_error_location));

               details::free_node(node_allocator_,branch);

               return error_node();
            }
            else if (!post_bracket_process(token_t::e_lcrlbracket,branch))
            {
               details::free_node(node_allocator_,branch);

               return error_node();
            }
         }
         else if (token_t::e_sub == current_token().type)
         {
            next_token();
            branch = parse_expression(e_level11);

            if (
                 branch &&
                 !(
                    details::is_neg_unary_node    (branch) &&
                    simplify_unary_negation_branch(branch)
                  )
               )
            {
               expression_node_ptr result = expression_generator_(details::e_neg,branch);

               if (0 == result)
               {
                  details::free_node(node_allocator_,branch);

                  return error_node();
               }
               else
                  branch = result;
            }
         }
         else if (token_t::e_add == current_token().type)
         {
            next_token();
            branch = parse_expression(e_level13);
         }
         else if (token_t::e_eof == current_token().type)
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR209 - Premature end of expression[1]",
                          exprtk_error_location));

            return error_node();
         }
         else
         {
            set_error(
               make_error(parser_error::e_syntax,
                          current_token(),
                          "ERR210 - Premature end of expression[2]",
                          exprtk_error_location));

            return error_node();
         }

         if (
              branch                    &&
              (e_level00 == precedence) &&
              token_is(token_t::e_ternary,prsrhlpr_t::e_hold)
            )
         {
            branch = parse_ternary_conditional_statement(branch);
         }

         parse_pending_string_rangesize(branch);

         return branch;
      }

      template <typename Type>
      class expression_generator
      {
      public:

         typedef details::expression_node<Type>* expression_node_ptr;
         typedef expression_node_ptr (*synthesize_functor_t)(expression_generator<T>&, const details::operator_type& operation, expression_node_ptr (&branch)[2]);
         typedef std::map<std::string,synthesize_functor_t> synthesize_map_t;
         typedef typename Essa::Math::parser<Type> parser_t;
         typedef const Type& vtype;
         typedef const Type  ctype;

         inline void init_synthesize_map()
         {
            #ifndef exprtk_disable_enhanced_features
            synthesize_map_["(v)o(v)"] = synthesize_vov_expression::process;
            synthesize_map_["(c)o(v)"] = synthesize_cov_expression::process;
            synthesize_map_["(v)o(c)"] = synthesize_voc_expression::process;

            #define register_synthezier(S)                      \
            synthesize_map_[S ::node_type::id()] = S ::process; \

            register_synthezier(synthesize_vovov_expression0)
            register_synthezier(synthesize_vovov_expression1)
            register_synthezier(synthesize_vovoc_expression0)
            register_synthezier(synthesize_vovoc_expression1)
            register_synthezier(synthesize_vocov_expression0)
            register_synthezier(synthesize_vocov_expression1)
            register_synthezier(synthesize_covov_expression0)
            register_synthezier(synthesize_covov_expression1)
            register_synthezier(synthesize_covoc_expression0)
            register_synthezier(synthesize_covoc_expression1)
            register_synthezier(synthesize_cocov_expression1)
            register_synthezier(synthesize_vococ_expression0)

            register_synthezier(synthesize_vovovov_expression0)
            register_synthezier(synthesize_vovovoc_expression0)
            register_synthezier(synthesize_vovocov_expression0)
            register_synthezier(synthesize_vocovov_expression0)
            register_synthezier(synthesize_covovov_expression0)
            register_synthezier(synthesize_covocov_expression0)
            register_synthezier(synthesize_vocovoc_expression0)
            register_synthezier(synthesize_covovoc_expression0)
            register_synthezier(synthesize_vococov_expression0)

            register_synthezier(synthesize_vovovov_expression1)
            register_synthezier(synthesize_vovovoc_expression1)
            register_synthezier(synthesize_vovocov_expression1)
            register_synthezier(synthesize_vocovov_expression1)
            register_synthezier(synthesize_covovov_expression1)
            register_synthezier(synthesize_covocov_expression1)
            register_synthezier(synthesize_vocovoc_expression1)
            register_synthezier(synthesize_covovoc_expression1)
            register_synthezier(synthesize_vococov_expression1)

            register_synthezier(synthesize_vovovov_expression2)
            register_synthezier(synthesize_vovovoc_expression2)
            register_synthezier(synthesize_vovocov_expression2)
            register_synthezier(synthesize_vocovov_expression2)
            register_synthezier(synthesize_covovov_expression2)
            register_synthezier(synthesize_covocov_expression2)
            register_synthezier(synthesize_vocovoc_expression2)
            register_synthezier(synthesize_covovoc_expression2)

            register_synthezier(synthesize_vovovov_expression3)
            register_synthezier(synthesize_vovovoc_expression3)
            register_synthezier(synthesize_vovocov_expression3)
            register_synthezier(synthesize_vocovov_expression3)
            register_synthezier(synthesize_covovov_expression3)
            register_synthezier(synthesize_covocov_expression3)
            register_synthezier(synthesize_vocovoc_expression3)
            register_synthezier(synthesize_covovoc_expression3)
            register_synthezier(synthesize_vococov_expression3)

            register_synthezier(synthesize_vovovov_expression4)
            register_synthezier(synthesize_vovovoc_expression4)
            register_synthezier(synthesize_vovocov_expression4)
            register_synthezier(synthesize_vocovov_expression4)
            register_synthezier(synthesize_covovov_expression4)
            register_synthezier(synthesize_covocov_expression4)
            register_synthezier(synthesize_vocovoc_expression4)
            register_synthezier(synthesize_covovoc_expression4)
            #endif
         }

         inline void set_parser(parser_t& p)
         {
            parser_ = &p;
         }

         inline void set_uom(unary_op_map_t& unary_op_map)
         {
            unary_op_map_ = &unary_op_map;
         }

         inline void set_bom(binary_op_map_t& binary_op_map)
         {
            binary_op_map_ = &binary_op_map;
         }

         inline void set_ibom(inv_binary_op_map_t& inv_binary_op_map)
         {
            inv_binary_op_map_ = &inv_binary_op_map;
         }

         inline void set_sf3m(sf3_map_t& sf3_map)
         {
            sf3_map_ = &sf3_map;
         }

         inline void set_sf4m(sf4_map_t& sf4_map)
         {
            sf4_map_ = &sf4_map;
         }

         inline void set_allocator(details::node_allocator& na)
         {
            node_allocator_ = &na;
         }

         inline void set_strength_reduction_state(const bool enabled)
         {
            strength_reduction_enabled_ = enabled;
         }

         inline bool strength_reduction_enabled() const
         {
            return strength_reduction_enabled_;
         }

         inline bool valid_operator(const details::operator_type& operation, binary_functor_t& bop)
         {
            typename binary_op_map_t::iterator bop_itr = binary_op_map_->find(operation);

            if ((*binary_op_map_).end() == bop_itr)
               return false;

            bop = bop_itr->second;

            return true;
         }

         inline bool valid_operator(const details::operator_type& operation, unary_functor_t& uop)
         {
            typename unary_op_map_t::iterator uop_itr = unary_op_map_->find(operation);

            if ((*unary_op_map_).end() == uop_itr)
               return false;

            uop = uop_itr->second;

            return true;
         }

         inline details::operator_type get_operator(const binary_functor_t& bop) const
         {
            return (*inv_binary_op_map_).find(bop)->second;
         }

         inline expression_node_ptr operator() (const Type& v) const
         {
            return node_allocator_->allocate<literal_node_t>(v);
         }

         #ifndef exprtk_disable_string_capabilities
         inline expression_node_ptr operator() (const std::string& s) const
         {
            return node_allocator_->allocate<string_literal_node_t>(s);
         }

         inline expression_node_ptr operator() (std::string& s, range_t& rp) const
         {
            return node_allocator_->allocate_rr<string_range_node_t>(s,rp);
         }

         inline expression_node_ptr operator() (const std::string& s, range_t& rp) const
         {
            return node_allocator_->allocate_tt<const_string_range_node_t>(s,rp);
         }

         inline expression_node_ptr operator() (expression_node_ptr branch, range_t& rp) const
         {
            if (is_generally_string_node(branch))
               return node_allocator_->allocate_tt<generic_string_range_node_t>(branch,rp);
            else
               return error_node();
         }
         #endif

         inline bool unary_optimisable(const details::operator_type& operation) const
         {
            return (details::e_abs   == operation) || (details::e_acos  == operation) ||
                   (details::e_acosh == operation) || (details::e_asin  == operation) ||
                   (details::e_asinh == operation) || (details::e_atan  == operation) ||
                   (details::e_atanh == operation) || (details::e_ceil  == operation) ||
                   (details::e_cos   == operation) || (details::e_cosh  == operation) ||
                   (details::e_exp   == operation) || (details::e_expm1 == operation) ||
                   (details::e_floor == operation) || (details::e_log   == operation) ||
                   (details::e_log10 == operation) || (details::e_log2  == operation) ||
                   (details::e_log1p == operation) || (details::e_neg   == operation) ||
                   (details::e_pos   == operation) || (details::e_round == operation) ||
                   (details::e_sin   == operation) || (details::e_sinc  == operation) ||
                   (details::e_sinh  == operation) || (details::e_sqrt  == operation) ||
                   (details::e_tan   == operation) || (details::e_tanh  == operation) ||
                   (details::e_cot   == operation) || (details::e_sec   == operation) ||
                   (details::e_csc   == operation) || (details::e_r2d   == operation) ||
                   (details::e_d2r   == operation) || (details::e_d2g   == operation) ||
                   (details::e_g2d   == operation) || (details::e_notl  == operation) ||
                   (details::e_sgn   == operation) || (details::e_erf   == operation) ||
                   (details::e_erfc  == operation) || (details::e_ncdf  == operation) ||
                   (details::e_frac  == operation) || (details::e_trunc == operation) ;
         }

         inline bool sf3_optimisable(const std::string& sf3id, trinary_functor_t& tfunc) const
         {
            typename sf3_map_t::const_iterator itr = sf3_map_->find(sf3id);

            if (sf3_map_->end() == itr)
               return false;
            else
               tfunc = itr->second.first;

            return true;
         }

         inline bool sf4_optimisable(const std::string& sf4id, quaternary_functor_t& qfunc) const
         {
            typename sf4_map_t::const_iterator itr = sf4_map_->find(sf4id);

            if (sf4_map_->end() == itr)
               return false;
            else
               qfunc = itr->second.first;

            return true;
         }

         inline bool sf3_optimisable(const std::string& sf3id, details::operator_type& operation) const
         {
            typename sf3_map_t::const_iterator itr = sf3_map_->find(sf3id);

            if (sf3_map_->end() == itr)
               return false;
            else
               operation = itr->second.second;

            return true;
         }

         inline bool sf4_optimisable(const std::string& sf4id, details::operator_type& operation) const
         {
            typename sf4_map_t::const_iterator itr = sf4_map_->find(sf4id);

            if (sf4_map_->end() == itr)
               return false;
            else
               operation = itr->second.second;

            return true;
         }

         inline expression_node_ptr operator() (const details::operator_type& operation, expression_node_ptr (&branch)[1])
         {
            if (0 == branch[0])
            {
               return error_node();
            }
            else if (details::is_null_node(branch[0]))
            {
               return branch[0];
            }
            else if (details::is_break_node(branch[0]))
            {
               return error_node();
            }
            else if (details::is_continue_node(branch[0]))
            {
               return error_node();
            }
            else if (details::is_constant_node(branch[0]))
            {
               return synthesize_expression<unary_node_t,1>(operation,branch);
            }
            else if (unary_optimisable(operation) && details::is_variable_node(branch[0]))
            {
               return synthesize_uv_expression(operation,branch);
            }
            else if (unary_optimisable(operation) && details::is_ivector_node(branch[0]))
            {
               return synthesize_uvec_expression(operation,branch);
            }
            else
               return synthesize_unary_expression(operation,branch);
         }

         inline bool is_assignment_operation(const details::operator_type& operation) const
         {
            return (
                     (details::e_addass == operation) ||
                     (details::e_subass == operation) ||
                     (details::e_mulass == operation) ||
                     (details::e_divass == operation) ||
                     (details::e_modass == operation)
                   ) &&
                   parser_->settings_.assignment_enabled(operation);
         }

         #ifndef exprtk_disable_string_capabilities
         inline bool valid_string_operation(const details::operator_type& operation) const
         {
            return (details::e_add    == operation) ||
                   (details::e_lt     == operation) ||
                   (details::e_lte    == operation) ||
                   (details::e_gt     == operation) ||
                   (details::e_gte    == operation) ||
                   (details::e_eq     == operation) ||
                   (details::e_ne     == operation) ||
                   (details::e_in     == operation) ||
                   (details::e_like   == operation) ||
                   (details::e_ilike  == operation) ||
                   (details::e_assign == operation) ||
                   (details::e_addass == operation) ||
                   (details::e_swap   == operation) ;
         }
         #else
         inline bool valid_string_operation(const details::operator_type&) const
         {
            return false;
         }
         #endif

         inline std::string to_str(const details::operator_type& operation) const
         {
            switch (operation)
            {
               case details::e_add  : return "+"      ;
               case details::e_sub  : return "-"      ;
               case details::e_mul  : return "*"      ;
               case details::e_div  : return "/"      ;
               case details::e_mod  : return "%"      ;
               case details::e_pow  : return "^"      ;
               case details::e_lt   : return "<"      ;
               case details::e_lte  : return "<="     ;
               case details::e_gt   : return ">"      ;
               case details::e_gte  : return ">="     ;
               case details::e_eq   : return "=="     ;
               case details::e_ne   : return "!="     ;
               case details::e_and  : return "and"    ;
               case details::e_nand : return "nand"   ;
               case details::e_or   : return "or"     ;
               case details::e_nor  : return "nor"    ;
               case details::e_xor  : return "xor"    ;
               case details::e_xnor : return "xnor"   ;
               default              : return "UNKNOWN";
            }
         }

         inline bool operation_optimisable(const details::operator_type& operation) const
         {
            return (details::e_add  == operation) ||
                   (details::e_sub  == operation) ||
                   (details::e_mul  == operation) ||
                   (details::e_div  == operation) ||
                   (details::e_mod  == operation) ||
                   (details::e_pow  == operation) ||
                   (details::e_lt   == operation) ||
                   (details::e_lte  == operation) ||
                   (details::e_gt   == operation) ||
                   (details::e_gte  == operation) ||
                   (details::e_eq   == operation) ||
                   (details::e_ne   == operation) ||
                   (details::e_and  == operation) ||
                   (details::e_nand == operation) ||
                   (details::e_or   == operation) ||
                   (details::e_nor  == operation) ||
                   (details::e_xor  == operation) ||
                   (details::e_xnor == operation) ;
         }

         inline std::string branch_to_id(expression_node_ptr branch) const
         {
            static const std::string null_str   ("(null)" );
            static const std::string const_str  ("(c)"    );
            static const std::string var_str    ("(v)"    );
            static const std::string vov_str    ("(vov)"  );
            static const std::string cov_str    ("(cov)"  );
            static const std::string voc_str    ("(voc)"  );
            static const std::string str_str    ("(s)"    );
            static const std::string strrng_str ("(rngs)" );
            static const std::string cs_str     ("(cs)"   );
            static const std::string cstrrng_str("(crngs)");

            if (details::is_null_node(branch))
               return null_str;
            else if (details::is_constant_node(branch))
               return const_str;
            else if (details::is_variable_node(branch))
               return var_str;
            else if (details::is_vov_node(branch))
               return vov_str;
            else if (details::is_cov_node(branch))
               return cov_str;
            else if (details::is_voc_node(branch))
               return voc_str;
            else if (details::is_string_node(branch))
               return str_str;
            else if (details::is_const_string_node(branch))
               return cs_str;
            else if (details::is_string_range_node(branch))
               return strrng_str;
            else if (details::is_const_string_range_node(branch))
               return cstrrng_str;
            else if (details::is_t0ot1ot2_node(branch))
               return "(" + dynamic_cast<details::T0oT1oT2_base_node<T>*>(branch)->type_id() + ")";
            else if (details::is_t0ot1ot2ot3_node(branch))
               return "(" + dynamic_cast<details::T0oT1oT2oT3_base_node<T>*>(branch)->type_id() + ")";
            else
               return "ERROR";
         }

         inline std::string branch_to_id(expression_node_ptr (&branch)[2]) const
         {
            return branch_to_id(branch[0]) + std::string("o") + branch_to_id(branch[1]);
         }

         inline bool cov_optimisable(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const
         {
            if (!operation_optimisable(operation))
               return false;
            else
               return details::is_constant_node(branch[0]) &&
                      details::is_variable_node(branch[1]) ;
         }

         inline bool voc_optimisable(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const
         {
            if (!operation_optimisable(operation))
               return false;
            else
               return details::is_variable_node(branch[0]) &&
                      details::is_constant_node(branch[1]) ;
         }

         inline bool vov_optimisable(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const
         {
            if (!operation_optimisable(operation))
               return false;
            else
               return details::is_variable_node(branch[0]) &&
                      details::is_variable_node(branch[1]) ;
         }

         inline bool cob_optimisable(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const
         {
            if (!operation_optimisable(operation))
               return false;
            else
               return details::is_constant_node(branch[0]) &&
                     !details::is_constant_node(branch[1]) ;
         }

         inline bool boc_optimisable(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const
         {
            if (!operation_optimisable(operation))
               return false;
            else
               return !details::is_constant_node(branch[0]) &&
                       details::is_constant_node(branch[1]) ;
         }

         inline bool cocob_optimisable(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const
         {
            if (
                 (details::e_add == operation) ||
                 (details::e_sub == operation) ||
                 (details::e_mul == operation) ||
                 (details::e_div == operation)
               )
            {
               return (details::is_constant_node(branch[0]) && details::is_cob_node(branch[1])) ||
                      (details::is_constant_node(branch[1]) && details::is_cob_node(branch[0])) ;
            }
            else
               return false;
         }

         inline bool coboc_optimisable(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const
         {
            if (
                 (details::e_add == operation) ||
                 (details::e_sub == operation) ||
                 (details::e_mul == operation) ||
                 (details::e_div == operation)
               )
            {
               return (details::is_constant_node(branch[0]) && details::is_boc_node(branch[1])) ||
                      (details::is_constant_node(branch[1]) && details::is_boc_node(branch[0])) ;
            }
            else
               return false;
         }

         inline bool uvouv_optimisable(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const
         {
            if (!operation_optimisable(operation))
               return false;
            else
               return details::is_uv_node(branch[0]) &&
                      details::is_uv_node(branch[1]) ;
         }

         inline bool vob_optimisable(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const
         {
            if (!operation_optimisable(operation))
               return false;
            else
               return details::is_variable_node(branch[0]) &&
                     !details::is_variable_node(branch[1]) ;
         }

         inline bool bov_optimisable(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const
         {
            if (!operation_optimisable(operation))
               return false;
            else
               return !details::is_variable_node(branch[0]) &&
                       details::is_variable_node(branch[1]) ;
         }

         inline bool binext_optimisable(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const
         {
            if (!operation_optimisable(operation))
               return false;
            else
               return !details::is_constant_node(branch[0]) ||
                      !details::is_constant_node(branch[1]) ;
         }

         inline bool is_invalid_assignment_op(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const
         {
            if (is_assignment_operation(operation))
            {
               const bool b1_is_genstring = details::is_generally_string_node(branch[1]);

               if (details::is_string_node(branch[0]))
                  return !b1_is_genstring;
               else
                  return (
                           !details::is_variable_node          (branch[0]) &&
                           !details::is_vector_elem_node       (branch[0]) &&
                           !details::is_rebasevector_elem_node (branch[0]) &&
                           !details::is_rebasevector_celem_node(branch[0]) &&
                           !details::is_vector_node            (branch[0])
                         )
                         || b1_is_genstring;
            }
            else
               return false;
         }

         inline bool is_constpow_operation(const details::operator_type& operation, expression_node_ptr(&branch)[2]) const
         {
            if (
                 !details::is_constant_node(branch[1]) ||
                  details::is_constant_node(branch[0]) ||
                  details::is_variable_node(branch[0]) ||
                  details::is_vector_node  (branch[0]) ||
                  details::is_generally_string_node(branch[0])
               )
               return false;

            const Type c = static_cast<details::literal_node<Type>*>(branch[1])->value();

            return cardinal_pow_optimisable(operation, c);
         }

         inline bool is_invalid_break_continue_op(expression_node_ptr (&branch)[2]) const
         {
            return (
                     details::is_break_node   (branch[0]) ||
                     details::is_break_node   (branch[1]) ||
                     details::is_continue_node(branch[0]) ||
                     details::is_continue_node(branch[1])
                   );
         }

         inline bool is_invalid_string_op(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const
         {
            const bool b0_string = is_generally_string_node(branch[0]);
            const bool b1_string = is_generally_string_node(branch[1]);

            bool result = false;

            if (b0_string != b1_string)
               result = true;
            else if (!valid_string_operation(operation) && b0_string && b1_string)
               result = true;

            if (result)
            {
               parser_->set_synthesis_error("Invalid string operation");
            }

            return result;
         }

         inline bool is_invalid_string_op(const details::operator_type& operation, expression_node_ptr (&branch)[3]) const
         {
            const bool b0_string = is_generally_string_node(branch[0]);
            const bool b1_string = is_generally_string_node(branch[1]);
            const bool b2_string = is_generally_string_node(branch[2]);

            bool result = false;

            if ((b0_string != b1_string) || (b1_string != b2_string))
               result = true;
            else if ((details::e_inrange != operation) && b0_string && b1_string && b2_string)
               result = true;

            if (result)
            {
               parser_->set_synthesis_error("Invalid string operation");
            }

            return result;
         }

         inline bool is_string_operation(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const
         {
            const bool b0_string = is_generally_string_node(branch[0]);
            const bool b1_string = is_generally_string_node(branch[1]);

            return (b0_string && b1_string && valid_string_operation(operation));
         }

         inline bool is_string_operation(const details::operator_type& operation, expression_node_ptr (&branch)[3]) const
         {
            const bool b0_string = is_generally_string_node(branch[0]);
            const bool b1_string = is_generally_string_node(branch[1]);
            const bool b2_string = is_generally_string_node(branch[2]);

            return (b0_string && b1_string && b2_string && (details::e_inrange == operation));
         }

         #ifndef exprtk_disable_sc_andor
         inline bool is_shortcircuit_expression(const details::operator_type& operation) const
         {
            return (
                     (details::e_scand == operation) ||
                     (details::e_scor  == operation)
                   );
         }
         #else
         inline bool is_shortcircuit_expression(const details::operator_type&) const
         {
            return false;
         }
         #endif

         inline bool is_null_present(expression_node_ptr (&branch)[2]) const
         {
            return (
                     details::is_null_node(branch[0]) ||
                     details::is_null_node(branch[1])
                   );
         }

         inline bool is_vector_eqineq_logic_operation(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const
         {
            if (!is_ivector_node(branch[0]) && !is_ivector_node(branch[1]))
               return false;
            else
               return (
                        (details::e_lt    == operation) ||
                        (details::e_lte   == operation) ||
                        (details::e_gt    == operation) ||
                        (details::e_gte   == operation) ||
                        (details::e_eq    == operation) ||
                        (details::e_ne    == operation) ||
                        (details::e_equal == operation) ||
                        (details::e_and   == operation) ||
                        (details::e_nand  == operation) ||
                        (details::e_or    == operation) ||
                        (details::e_nor   == operation) ||
                        (details::e_xor   == operation) ||
                        (details::e_xnor  == operation)
                      );
         }

         inline bool is_vector_arithmetic_operation(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const
         {
            if (!is_ivector_node(branch[0]) && !is_ivector_node(branch[1]))
               return false;
            else
               return (
                        (details::e_add == operation) ||
                        (details::e_sub == operation) ||
                        (details::e_mul == operation) ||
                        (details::e_div == operation) ||
                        (details::e_pow == operation)
                      );
         }

         inline expression_node_ptr operator() (const details::operator_type& operation, expression_node_ptr (&branch)[2])
         {
            if ((0 == branch[0]) || (0 == branch[1]))
            {
               return error_node();
            }
            else if (is_invalid_string_op(operation,branch))
            {
               return error_node();
            }
            else if (is_invalid_assignment_op(operation,branch))
            {
               return error_node();
            }
            else if (is_invalid_break_continue_op(branch))
            {
               return error_node();
            }
            else if (details::e_assign == operation)
            {
               return synthesize_assignment_expression(operation, branch);
            }
            else if (details::e_swap == operation)
            {
               return synthesize_swap_expression(branch);
            }
            else if (is_assignment_operation(operation))
            {
               return synthesize_assignment_operation_expression(operation, branch);
            }
            else if (is_vector_eqineq_logic_operation(operation, branch))
            {
               return synthesize_veceqineqlogic_operation_expression(operation, branch);
            }
            else if (is_vector_arithmetic_operation(operation, branch))
            {
               return synthesize_vecarithmetic_operation_expression(operation, branch);
            }
            else if (is_shortcircuit_expression(operation))
            {
               return synthesize_shortcircuit_expression(operation, branch);
            }
            else if (is_string_operation(operation, branch))
            {
               return synthesize_string_expression(operation, branch);
            }
            else if (is_null_present(branch))
            {
               return synthesize_null_expression(operation, branch);
            }
            #ifndef exprtk_disable_cardinal_pow_optimisation
            else if (is_constpow_operation(operation, branch))
            {
               return cardinal_pow_optimisation(branch);
            }
            #endif

            expression_node_ptr result = error_node();

            #ifndef exprtk_disable_enhanced_features
            if (synthesize_expression(operation, branch, result))
            {
               return result;
            }
            else
            #endif

            {
               /*
                  Possible reductions:
                  1. c o cob -> cob
                  2. cob o c -> cob
                  3. c o boc -> boc
                  4. boc o c -> boc
               */
               result = error_node();

               if (cocob_optimisable(operation, branch))
               {
                  result = synthesize_cocob_expression::process((*this), operation, branch);
               }
               else if (coboc_optimisable(operation, branch) && (0 == result))
               {
                  result = synthesize_coboc_expression::process((*this), operation, branch);
               }

               if (result)
                  return result;
            }

            if (uvouv_optimisable(operation, branch))
            {
               return synthesize_uvouv_expression(operation, branch);
            }
            else if (vob_optimisable(operation, branch))
            {
               return synthesize_vob_expression::process((*this), operation, branch);
            }
            else if (bov_optimisable(operation, branch))
            {
               return synthesize_bov_expression::process((*this), operation, branch);
            }
            else if (cob_optimisable(operation, branch))
            {
               return synthesize_cob_expression::process((*this), operation, branch);
            }
            else if (boc_optimisable(operation, branch))
            {
               return synthesize_boc_expression::process((*this), operation, branch);
            }
            #ifndef exprtk_disable_enhanced_features
            else if (cov_optimisable(operation, branch))
            {
               return synthesize_cov_expression::process((*this), operation, branch);
            }
            #endif
            else if (binext_optimisable(operation, branch))
            {
               return synthesize_binary_ext_expression::process((*this), operation, branch);
            }
            else
               return synthesize_expression<binary_node_t,2>(operation, branch);
         }

         inline expression_node_ptr operator() (const details::operator_type& operation, expression_node_ptr (&branch)[3])
         {
            if (
                 (0 == branch[0]) ||
                 (0 == branch[1]) ||
                 (0 == branch[2])
               )
            {
               details::free_all_nodes(*node_allocator_,branch);

               return error_node();
            }
            else if (is_invalid_string_op(operation, branch))
            {
               return error_node();
            }
            else if (is_string_operation(operation, branch))
            {
               return synthesize_string_expression(operation, branch);
            }
            else
               return synthesize_expression<trinary_node_t,3>(operation, branch);
         }

         inline expression_node_ptr operator() (const details::operator_type& operation, expression_node_ptr (&branch)[4])
         {
            return synthesize_expression<quaternary_node_t,4>(operation,branch);
         }

         inline expression_node_ptr operator() (const details::operator_type& operation, expression_node_ptr b0)
         {
            expression_node_ptr branch[1] = { b0 };
            return (*this)(operation,branch);
         }

         inline expression_node_ptr operator() (const details::operator_type& operation, expression_node_ptr& b0, expression_node_ptr& b1)
         {
            expression_node_ptr result = error_node();

            if ((0 != b0) && (0 != b1))
            {
               expression_node_ptr branch[2] = { b0, b1 };
               result = expression_generator<Type>::operator()(operation, branch);
               b0 = branch[0];
               b1 = branch[1];
            }

            return result;
         }

         inline expression_node_ptr conditional(expression_node_ptr condition,
                                                expression_node_ptr consequent,
                                                expression_node_ptr alternative) const
         {
            if ((0 == condition) || (0 == consequent))
            {
               details::free_node(*node_allocator_, condition  );
               details::free_node(*node_allocator_, consequent );
               details::free_node(*node_allocator_, alternative);

               return error_node();
            }
            // Can the condition be immediately evaluated? if so optimise.
            else if (details::is_constant_node(condition))
            {
               // True branch
               if (details::is_true(condition))
               {
                  details::free_node(*node_allocator_, condition  );
                  details::free_node(*node_allocator_, alternative);

                  return consequent;
               }
               // False branch
               else
               {
                  details::free_node(*node_allocator_, condition );
                  details::free_node(*node_allocator_, consequent);

                  if (alternative)
                     return alternative;
                  else
                     return node_allocator_->allocate<details::null_node<T> >();
               }
            }
            else if ((0 != consequent) && (0 != alternative))
            {
               return node_allocator_->
                        allocate<conditional_node_t>(condition, consequent, alternative);
            }
            else
               return node_allocator_->
                        allocate<cons_conditional_node_t>(condition, consequent);
         }

         #ifndef exprtk_disable_string_capabilities
         inline expression_node_ptr conditional_string(expression_node_ptr condition,
                                                       expression_node_ptr consequent,
                                                       expression_node_ptr alternative) const
         {
            if ((0 == condition) || (0 == consequent))
            {
               details::free_node(*node_allocator_, condition  );
               details::free_node(*node_allocator_, consequent );
               details::free_node(*node_allocator_, alternative);

               return error_node();
            }
            // Can the condition be immediately evaluated? if so optimise.
            else if (details::is_constant_node(condition))
            {
               // True branch
               if (details::is_true(condition))
               {
                  details::free_node(*node_allocator_, condition  );
                  details::free_node(*node_allocator_, alternative);

                  return consequent;
               }
               // False branch
               else
               {
                  details::free_node(*node_allocator_, condition );
                  details::free_node(*node_allocator_, consequent);

                  if (alternative)
                     return alternative;
                  else
                     return node_allocator_->
                              allocate_c<details::string_literal_node<Type> >("");
               }
            }
            else if ((0 != consequent) && (0 != alternative))
               return node_allocator_->
                        allocate<conditional_string_node_t>(condition, consequent, alternative);
            else
               return error_node();
         }
         #else
         inline expression_node_ptr conditional_string(expression_node_ptr,
                                                       expression_node_ptr,
                                                       expression_node_ptr) const
         {
            return error_node();
         }
         #endif

         inline expression_node_ptr conditional_vector(expression_node_ptr condition,
                                                       expression_node_ptr consequent,
                                                       expression_node_ptr alternative) const
         {
            if ((0 == condition) || (0 == consequent))
            {
               details::free_node(*node_allocator_, condition  );
               details::free_node(*node_allocator_, consequent );
               details::free_node(*node_allocator_, alternative);

               return error_node();
            }
            // Can the condition be immediately evaluated? if so optimise.
            else if (details::is_constant_node(condition))
            {
               // True branch
               if (details::is_true(condition))
               {
                  details::free_node(*node_allocator_, condition  );
                  details::free_node(*node_allocator_, alternative);

                  return consequent;
               }
               // False branch
               else
               {
                  details::free_node(*node_allocator_, condition );
                  details::free_node(*node_allocator_, consequent);

                  if (alternative)
                     return alternative;
                  else
                     return node_allocator_->allocate<details::null_node<T> >();

               }
            }
            else if ((0 != consequent) && (0 != alternative))
            {
               return node_allocator_->
                        allocate<conditional_vector_node_t>(condition, consequent, alternative);
            }
            else
               return error_node();
         }

         inline loop_runtime_check_ptr get_loop_runtime_check(const loop_runtime_check::loop_types loop_type) const
         {
            if (
                 parser_->loop_runtime_check_ &&
                 (loop_type == (parser_->loop_runtime_check_->loop_set & loop_type))
               )
            {
               return parser_->loop_runtime_check_;
            }

            return loop_runtime_check_ptr(0);
         }

         inline expression_node_ptr while_loop(expression_node_ptr& condition,
                                               expression_node_ptr& branch,
                                               const bool break_continue_present = false) const
         {
            if (!break_continue_present && details::is_constant_node(condition))
            {
               expression_node_ptr result = error_node();
               if (details::is_true(condition))
                  // Infinite loops are not allowed.
                  result = error_node();
               else
                  result = node_allocator_->allocate<details::null_node<Type> >();

               details::free_node(*node_allocator_, condition);
               details::free_node(*node_allocator_, branch   );

               return result;
            }
            else if (details::is_null_node(condition))
            {
               details::free_node(*node_allocator_,condition);

               return branch;
            }

            loop_runtime_check_ptr rtc = get_loop_runtime_check(loop_runtime_check::e_while_loop);

            if (!break_continue_present)
            {
               if (rtc)
                  return node_allocator_->allocate<while_loop_rtc_node_t>
                           (condition, branch,  rtc);
               else
                  return node_allocator_->allocate<while_loop_node_t>
                           (condition, branch);
            }
            #ifndef exprtk_disable_break_continue
            else
            {
               if (rtc)
                  return node_allocator_->allocate<while_loop_bc_rtc_node_t>
                           (condition, branch, rtc);
               else
                  return node_allocator_->allocate<while_loop_bc_node_t>
                           (condition, branch);
            }
            #else
               return error_node();
            #endif
         }

         inline expression_node_ptr repeat_until_loop(expression_node_ptr& condition,
                                                      expression_node_ptr& branch,
                                                      const bool break_continue_present = false) const
         {
            if (!break_continue_present && details::is_constant_node(condition))
            {
               if (
                    details::is_true(condition) &&
                    details::is_constant_node(branch)
                  )
               {
                  free_node(*node_allocator_,condition);

                  return branch;
               }

               details::free_node(*node_allocator_, condition);
               details::free_node(*node_allocator_, branch   );

               return error_node();
            }
            else if (details::is_null_node(condition))
            {
               details::free_node(*node_allocator_,condition);

               return branch;
            }

            loop_runtime_check_ptr rtc = get_loop_runtime_check(loop_runtime_check::e_repeat_until_loop);

            if (!break_continue_present)
            {
               if (rtc)
                  return node_allocator_->allocate<repeat_until_loop_rtc_node_t>
                           (condition, branch,  rtc);
               else
                  return node_allocator_->allocate<repeat_until_loop_node_t>
                           (condition, branch);
            }
            #ifndef exprtk_disable_break_continue
            else
            {
               if (rtc)
                  return node_allocator_->allocate<repeat_until_loop_bc_rtc_node_t>
                           (condition, branch, rtc);
               else
                  return node_allocator_->allocate<repeat_until_loop_bc_node_t>
                           (condition, branch);
            }
            #else
               return error_node();
            #endif
         }

         inline expression_node_ptr for_loop(expression_node_ptr& initialiser,
                                             expression_node_ptr& condition,
                                             expression_node_ptr& incrementor,
                                             expression_node_ptr& loop_body,
                                             bool break_continue_present = false) const
         {
            if (!break_continue_present && details::is_constant_node(condition))
            {
               expression_node_ptr result = error_node();

               if (details::is_true(condition))
                  // Infinite loops are not allowed.
                  result = error_node();
               else
                  result = node_allocator_->allocate<details::null_node<Type> >();

               details::free_node(*node_allocator_, initialiser);
               details::free_node(*node_allocator_, condition  );
               details::free_node(*node_allocator_, incrementor);
               details::free_node(*node_allocator_, loop_body  );

               return result;
            }
            else if (details::is_null_node(condition) || (0 == condition))
            {
               details::free_node(*node_allocator_, initialiser);
               details::free_node(*node_allocator_, condition  );
               details::free_node(*node_allocator_, incrementor);

               return loop_body;
            }

            loop_runtime_check_ptr rtc = get_loop_runtime_check(loop_runtime_check::e_for_loop);

            if (!break_continue_present)
            {
               if (rtc)
                  return node_allocator_->allocate<for_loop_rtc_node_t>
                                          (
                                            initialiser,
                                            condition,
                                            incrementor,
                                            loop_body,
                                            rtc
                                          );
               else
                  return node_allocator_->allocate<for_loop_node_t>
                                          (
                                            initialiser,
                                            condition,
                                            incrementor,
                                            loop_body
                                          );
            }
            #ifndef exprtk_disable_break_continue
            else
            {
               if (rtc)
                  return node_allocator_->allocate<for_loop_bc_rtc_node_t>
                                          (
                                            initialiser,
                                            condition,
                                            incrementor,
                                            loop_body,
                                            rtc
                                          );
               else
                  return node_allocator_->allocate<for_loop_bc_node_t>
                                          (
                                            initialiser,
                                            condition,
                                            incrementor,
                                            loop_body
                                          );
            }
            #else
               return error_node();
            #endif
         }

         template <typename Allocator,
                   template <typename, typename> class Sequence>
         inline expression_node_ptr const_optimise_switch(Sequence<expression_node_ptr,Allocator>& arg_list)
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
         inline expression_node_ptr const_optimise_mswitch(Sequence<expression_node_ptr,Allocator>& arg_list)
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

            #define case_stmt(N)                                                         \
            if (is_true(arg[(2 * N)].first)) { return arg[(2 * N) + 1].first->value(); } \

            struct switch_impl_1
            {
               static inline T process(const arg_list_t& arg)
               {
                  case_stmt(0)

                  assert(arg.size() == ((2 * 1) + 1));

                  return arg.back().first->value();
               }
            };

            struct switch_impl_2
            {
               static inline T process(const arg_list_t& arg)
               {
                  case_stmt(0) case_stmt(1)

                  assert(arg.size() == ((2 * 2) + 1));

                  return arg.back().first->value();
               }
            };

            struct switch_impl_3
            {
               static inline T process(const arg_list_t& arg)
               {
                  case_stmt(0) case_stmt(1)
                  case_stmt(2)

                  assert(arg.size() == ((2 * 3) + 1));

                  return arg.back().first->value();
               }
            };

            struct switch_impl_4
            {
               static inline T process(const arg_list_t& arg)
               {
                  case_stmt(0) case_stmt(1)
                  case_stmt(2) case_stmt(3)

                  assert(arg.size() == ((2 * 4) + 1));

                  return arg.back().first->value();
               }
            };

            struct switch_impl_5
            {
               static inline T process(const arg_list_t& arg)
               {
                  case_stmt(0) case_stmt(1)
                  case_stmt(2) case_stmt(3)
                  case_stmt(4)

                  assert(arg.size() == ((2 * 5) + 1));

                  return arg.back().first->value();
               }
            };

            struct switch_impl_6
            {
               static inline T process(const arg_list_t& arg)
               {
                  case_stmt(0) case_stmt(1)
                  case_stmt(2) case_stmt(3)
                  case_stmt(4) case_stmt(5)

                  assert(arg.size() == ((2 * 6) + 1));

                  return arg.back().first->value();
               }
            };

            struct switch_impl_7
            {
               static inline T process(const arg_list_t& arg)
               {
                  case_stmt(0) case_stmt(1)
                  case_stmt(2) case_stmt(3)
                  case_stmt(4) case_stmt(5)
                  case_stmt(6)

                  assert(arg.size() == ((2 * 7) + 1));

                  return arg.back().first->value();
               }
            };

            #undef case_stmt
         };

         template <typename Allocator,
                   template <typename, typename> class Sequence>
         inline expression_node_ptr switch_statement(Sequence<expression_node_ptr,Allocator>& arg_list, const bool default_statement_present)
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
                              <Type,typename switch_nodes::switch_impl_##N > >(arg_list); \

               case_stmt(1)
               case_stmt(2)
               case_stmt(3)
               case_stmt(4)
               case_stmt(5)
               case_stmt(6)
               case_stmt(7)
               #undef case_stmt

               default : return node_allocator_->allocate<details::switch_node<Type> >(arg_list);
            }
         }

         template <typename Allocator,
                   template <typename, typename> class Sequence>
         inline expression_node_ptr multi_switch_statement(Sequence<expression_node_ptr,Allocator>& arg_list)
         {
            if (!all_nodes_valid(arg_list))
            {
               details::free_all_nodes(*node_allocator_,arg_list);

               return error_node();
            }
            else if (is_constant_foldable(arg_list))
               return const_optimise_mswitch(arg_list);
            else
               return node_allocator_->allocate<details::multi_switch_node<Type> >(arg_list);
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

         inline expression_node_ptr synthesize_uv_expression(const details::operator_type& operation,
                                                             expression_node_ptr (&branch)[1])
         {
            T& v = static_cast<details::variable_node<T>*>(branch[0])->ref();

            switch (operation)
            {
               #define case_stmt(op0, op1)                                                         \
               case op0 : return node_allocator_->                                                 \
                             allocate<typename details::unary_variable_node<Type,op1<Type> > >(v); \

               unary_opr_switch_statements
               #undef case_stmt
               default : return error_node();
            }
         }

         inline expression_node_ptr synthesize_uvec_expression(const details::operator_type& operation,
                                                               expression_node_ptr (&branch)[1])
         {
            switch (operation)
            {
               #define case_stmt(op0, op1)                                                   \
               case op0 : return node_allocator_->                                           \
                             allocate<typename details::unary_vector_node<Type,op1<Type> > > \
                                (operation, branch[0]);                                      \

               unary_opr_switch_statements
               #undef case_stmt
               default : return error_node();
            }
         }

         inline expression_node_ptr synthesize_unary_expression(const details::operator_type& operation,
                                                                expression_node_ptr (&branch)[1])
         {
            switch (operation)
            {
               #define case_stmt(op0, op1)                                                               \
               case op0 : return node_allocator_->                                                       \
                             allocate<typename details::unary_branch_node<Type,op1<Type> > >(branch[0]); \

               unary_opr_switch_statements
               #undef case_stmt
               default : return error_node();
            }
         }

         inline expression_node_ptr const_optimise_sf3(const details::operator_type& operation,
                                                       expression_node_ptr (&branch)[3])
         {
            expression_node_ptr temp_node = error_node();

            switch (operation)
            {
               #define case_stmt(op)                                                        \
               case details::e_sf##op : temp_node = node_allocator_->                       \
                             allocate<details::sf3_node<Type,details::sf##op##_op<Type> > > \
                                (operation, branch);                                        \
                             break;                                                         \

               case_stmt(00) case_stmt(01) case_stmt(02) case_stmt(03)
               case_stmt(04) case_stmt(05) case_stmt(06) case_stmt(07)
               case_stmt(08) case_stmt(09) case_stmt(10) case_stmt(11)
               case_stmt(12) case_stmt(13) case_stmt(14) case_stmt(15)
               case_stmt(16) case_stmt(17) case_stmt(18) case_stmt(19)
               case_stmt(20) case_stmt(21) case_stmt(22) case_stmt(23)
               case_stmt(24) case_stmt(25) case_stmt(26) case_stmt(27)
               case_stmt(28) case_stmt(29) case_stmt(30) case_stmt(31)
               case_stmt(32) case_stmt(33) case_stmt(34) case_stmt(35)
               case_stmt(36) case_stmt(37) case_stmt(38) case_stmt(39)
               case_stmt(40) case_stmt(41) case_stmt(42) case_stmt(43)
               case_stmt(44) case_stmt(45) case_stmt(46) case_stmt(47)
               #undef case_stmt
               default : return error_node();
            }

            const T v = temp_node->value();

            details::free_node(*node_allocator_,temp_node);

            return node_allocator_->allocate<literal_node_t>(v);
         }

         inline expression_node_ptr varnode_optimise_sf3(const details::operator_type& operation, expression_node_ptr (&branch)[3])
         {
            typedef details::variable_node<Type>* variable_ptr;

            const Type& v0 = static_cast<variable_ptr>(branch[0])->ref();
            const Type& v1 = static_cast<variable_ptr>(branch[1])->ref();
            const Type& v2 = static_cast<variable_ptr>(branch[2])->ref();

            switch (operation)
            {
               #define case_stmt(op)                                                                \
               case details::e_sf##op : return node_allocator_->                                    \
                             allocate_rrr<details::sf3_var_node<Type,details::sf##op##_op<Type> > > \
                                (v0, v1, v2);                                                       \

               case_stmt(00) case_stmt(01) case_stmt(02) case_stmt(03)
               case_stmt(04) case_stmt(05) case_stmt(06) case_stmt(07)
               case_stmt(08) case_stmt(09) case_stmt(10) case_stmt(11)
               case_stmt(12) case_stmt(13) case_stmt(14) case_stmt(15)
               case_stmt(16) case_stmt(17) case_stmt(18) case_stmt(19)
               case_stmt(20) case_stmt(21) case_stmt(22) case_stmt(23)
               case_stmt(24) case_stmt(25) case_stmt(26) case_stmt(27)
               case_stmt(28) case_stmt(29) case_stmt(30) case_stmt(31)
               case_stmt(32) case_stmt(33) case_stmt(34) case_stmt(35)
               case_stmt(36) case_stmt(37) case_stmt(38) case_stmt(39)
               case_stmt(40) case_stmt(41) case_stmt(42) case_stmt(43)
               case_stmt(44) case_stmt(45) case_stmt(46) case_stmt(47)
               #undef case_stmt
               default : return error_node();
            }
         }

         inline expression_node_ptr special_function(const details::operator_type& operation, expression_node_ptr (&branch)[3])
         {
            if (!all_nodes_valid(branch))
               return error_node();
            else if (is_constant_foldable(branch))
               return const_optimise_sf3(operation,branch);
            else if (all_nodes_variables(branch))
               return varnode_optimise_sf3(operation,branch);
            else
            {
               switch (operation)
               {
                  #define case_stmt(op)                                                        \
                  case details::e_sf##op : return node_allocator_->                            \
                                allocate<details::sf3_node<Type,details::sf##op##_op<Type> > > \
                                   (operation, branch);                                        \

                  case_stmt(00) case_stmt(01) case_stmt(02) case_stmt(03)
                  case_stmt(04) case_stmt(05) case_stmt(06) case_stmt(07)
                  case_stmt(08) case_stmt(09) case_stmt(10) case_stmt(11)
                  case_stmt(12) case_stmt(13) case_stmt(14) case_stmt(15)
                  case_stmt(16) case_stmt(17) case_stmt(18) case_stmt(19)
                  case_stmt(20) case_stmt(21) case_stmt(22) case_stmt(23)
                  case_stmt(24) case_stmt(25) case_stmt(26) case_stmt(27)
                  case_stmt(28) case_stmt(29) case_stmt(30) case_stmt(31)
                  case_stmt(32) case_stmt(33) case_stmt(34) case_stmt(35)
                  case_stmt(36) case_stmt(37) case_stmt(38) case_stmt(39)
                  case_stmt(40) case_stmt(41) case_stmt(42) case_stmt(43)
                  case_stmt(44) case_stmt(45) case_stmt(46) case_stmt(47)
                  #undef case_stmt
                  default : return error_node();
               }
            }
         }

         inline expression_node_ptr const_optimise_sf4(const details::operator_type& operation, expression_node_ptr (&branch)[4])
         {
            expression_node_ptr temp_node = error_node();

            switch (operation)
            {
               #define case_stmt(op)                                                                    \
               case details::e_sf##op : temp_node = node_allocator_->                                   \
                                         allocate<details::sf4_node<Type,details::sf##op##_op<Type> > > \
                                            (operation, branch);                                        \
                                        break;                                                          \

               case_stmt(48) case_stmt(49) case_stmt(50) case_stmt(51)
               case_stmt(52) case_stmt(53) case_stmt(54) case_stmt(55)
               case_stmt(56) case_stmt(57) case_stmt(58) case_stmt(59)
               case_stmt(60) case_stmt(61) case_stmt(62) case_stmt(63)
               case_stmt(64) case_stmt(65) case_stmt(66) case_stmt(67)
               case_stmt(68) case_stmt(69) case_stmt(70) case_stmt(71)
               case_stmt(72) case_stmt(73) case_stmt(74) case_stmt(75)
               case_stmt(76) case_stmt(77) case_stmt(78) case_stmt(79)
               case_stmt(80) case_stmt(81) case_stmt(82) case_stmt(83)
               case_stmt(84) case_stmt(85) case_stmt(86) case_stmt(87)
               case_stmt(88) case_stmt(89) case_stmt(90) case_stmt(91)
               case_stmt(92) case_stmt(93) case_stmt(94) case_stmt(95)
               case_stmt(96) case_stmt(97) case_stmt(98) case_stmt(99)
               #undef case_stmt
               default : return error_node();
            }

            const T v = temp_node->value();

            details::free_node(*node_allocator_,temp_node);

            return node_allocator_->allocate<literal_node_t>(v);
         }

         inline expression_node_ptr varnode_optimise_sf4(const details::operator_type& operation, expression_node_ptr (&branch)[4])
         {
            typedef details::variable_node<Type>* variable_ptr;

            const Type& v0 = static_cast<variable_ptr>(branch[0])->ref();
            const Type& v1 = static_cast<variable_ptr>(branch[1])->ref();
            const Type& v2 = static_cast<variable_ptr>(branch[2])->ref();
            const Type& v3 = static_cast<variable_ptr>(branch[3])->ref();

            switch (operation)
            {
               #define case_stmt(op)                                                                 \
               case details::e_sf##op : return node_allocator_->                                     \
                             allocate_rrrr<details::sf4_var_node<Type,details::sf##op##_op<Type> > > \
                                (v0, v1, v2, v3);                                                    \

               case_stmt(48) case_stmt(49) case_stmt(50) case_stmt(51)
               case_stmt(52) case_stmt(53) case_stmt(54) case_stmt(55)
               case_stmt(56) case_stmt(57) case_stmt(58) case_stmt(59)
               case_stmt(60) case_stmt(61) case_stmt(62) case_stmt(63)
               case_stmt(64) case_stmt(65) case_stmt(66) case_stmt(67)
               case_stmt(68) case_stmt(69) case_stmt(70) case_stmt(71)
               case_stmt(72) case_stmt(73) case_stmt(74) case_stmt(75)
               case_stmt(76) case_stmt(77) case_stmt(78) case_stmt(79)
               case_stmt(80) case_stmt(81) case_stmt(82) case_stmt(83)
               case_stmt(84) case_stmt(85) case_stmt(86) case_stmt(87)
               case_stmt(88) case_stmt(89) case_stmt(90) case_stmt(91)
               case_stmt(92) case_stmt(93) case_stmt(94) case_stmt(95)
               case_stmt(96) case_stmt(97) case_stmt(98) case_stmt(99)
               #undef case_stmt
               default : return error_node();
            }
         }

         inline expression_node_ptr special_function(const details::operator_type& operation, expression_node_ptr (&branch)[4])
         {
            if (!all_nodes_valid(branch))
               return error_node();
            else if (is_constant_foldable(branch))
               return const_optimise_sf4(operation,branch);
            else if (all_nodes_variables(branch))
               return varnode_optimise_sf4(operation,branch);
            switch (operation)
            {
               #define case_stmt(op)                                                        \
               case details::e_sf##op : return node_allocator_->                            \
                             allocate<details::sf4_node<Type,details::sf##op##_op<Type> > > \
                                (operation, branch);                                        \

               case_stmt(48) case_stmt(49) case_stmt(50) case_stmt(51)
               case_stmt(52) case_stmt(53) case_stmt(54) case_stmt(55)
               case_stmt(56) case_stmt(57) case_stmt(58) case_stmt(59)
               case_stmt(60) case_stmt(61) case_stmt(62) case_stmt(63)
               case_stmt(64) case_stmt(65) case_stmt(66) case_stmt(67)
               case_stmt(68) case_stmt(69) case_stmt(70) case_stmt(71)
               case_stmt(72) case_stmt(73) case_stmt(74) case_stmt(75)
               case_stmt(76) case_stmt(77) case_stmt(78) case_stmt(79)
               case_stmt(80) case_stmt(81) case_stmt(82) case_stmt(83)
               case_stmt(84) case_stmt(85) case_stmt(86) case_stmt(87)
               case_stmt(88) case_stmt(89) case_stmt(90) case_stmt(91)
               case_stmt(92) case_stmt(93) case_stmt(94) case_stmt(95)
               case_stmt(96) case_stmt(97) case_stmt(98) case_stmt(99)
               #undef case_stmt
               default : return error_node();
            }
         }

         template <typename Allocator,
                   template <typename, typename> class Sequence>
         inline expression_node_ptr const_optimise_varargfunc(const details::operator_type& operation, Sequence<expression_node_ptr,Allocator>& arg_list)
         {
            expression_node_ptr temp_node = error_node();

            switch (operation)
            {
               #define case_stmt(op0, op1)                                                \
               case op0 : temp_node = node_allocator_->                                   \
                                         allocate<details::vararg_node<Type,op1<Type> > > \
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

         inline bool special_one_parameter_vararg(const details::operator_type& operation) const
         {
            return (
                     (details::e_sum  == operation) ||
                     (details::e_prod == operation) ||
                     (details::e_avg  == operation) ||
                     (details::e_min  == operation) ||
                     (details::e_max  == operation)
                   );
         }

         template <typename Allocator,
                   template <typename, typename> class Sequence>
         inline expression_node_ptr varnode_optimise_varargfunc(const details::operator_type& operation, Sequence<expression_node_ptr,Allocator>& arg_list)
         {
            switch (operation)
            {
               #define case_stmt(op0, op1)                                                  \
               case op0 : return node_allocator_->                                          \
                             allocate<details::vararg_varnode<Type,op1<Type> > >(arg_list); \

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
         inline expression_node_ptr vectorize_func(const details::operator_type& operation, Sequence<expression_node_ptr,Allocator>& arg_list)
         {
            if (1 == arg_list.size())
            {
               switch (operation)
               {
                  #define case_stmt(op0, op1)                                                     \
                  case op0 : return node_allocator_->                                             \
                                allocate<details::vectorize_node<Type,op1<Type> > >(arg_list[0]); \

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
         inline expression_node_ptr vararg_function(const details::operator_type& operation, Sequence<expression_node_ptr,Allocator>& arg_list)
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

            #ifndef exprtk_disable_string_capabilities
            if (details::e_smulti == operation)
            {
               return node_allocator_->
                 allocate<details::str_vararg_node<Type,details::vararg_multi_op<Type> > >(arg_list);
            }
            else
            #endif
            {
               switch (operation)
               {
                  #define case_stmt(op0, op1)                                               \
                  case op0 : return node_allocator_->                                       \
                                allocate<details::vararg_node<Type,op1<Type> > >(arg_list); \

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
         inline expression_node_ptr function(ifunction_t* f, expression_node_ptr (&b)[N])
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

         inline expression_node_ptr function(ifunction_t* f)
         {
            typedef typename details::function_N_node<Type,ifunction_t,0> function_N_node_t;
            return node_allocator_->allocate<function_N_node_t>(f);
         }

         inline expression_node_ptr vararg_function_call(ivararg_function_t* vaf,
                                                         std::vector<expression_node_ptr>& arg_list)
         {
            if (!all_nodes_valid(arg_list))
            {
               details::free_all_nodes(*node_allocator_,arg_list);

               return error_node();
            }

            typedef details::vararg_function_node<Type,ivararg_function_t> alloc_type;

            expression_node_ptr result = node_allocator_->allocate<alloc_type>(vaf,arg_list);

            if (
                 !arg_list.empty()        &&
                 !vaf->has_side_effects() &&
                 is_constant_foldable(arg_list)
               )
            {
               const Type v = result->value();
               details::free_node(*node_allocator_,result);
               result = node_allocator_->allocate<literal_node_t>(v);
            }

            parser_->state_.activate_side_effect("vararg_function_call()");

            return result;
         }

         inline expression_node_ptr generic_function_call(igeneric_function_t* gf,
                                                          std::vector<expression_node_ptr>& arg_list,
                                                          const std::size_t& param_seq_index = std::numeric_limits<std::size_t>::max())
         {
            if (!all_nodes_valid(arg_list))
            {
               details::free_all_nodes(*node_allocator_,arg_list);
               return error_node();
            }

            typedef details::generic_function_node     <Type,igeneric_function_t> alloc_type1;
            typedef details::multimode_genfunction_node<Type,igeneric_function_t> alloc_type2;

            const std::size_t no_psi = std::numeric_limits<std::size_t>::max();

            expression_node_ptr result = error_node();

            if (no_psi == param_seq_index)
               result = node_allocator_->allocate<alloc_type1>(arg_list,gf);
            else
               result = node_allocator_->allocate<alloc_type2>(gf, param_seq_index, arg_list);

            alloc_type1* genfunc_node_ptr = static_cast<alloc_type1*>(result);

            if (
                 !arg_list.empty()                  &&
                 !gf->has_side_effects()            &&
                 parser_->state_.type_check_enabled &&
                 is_constant_foldable(arg_list)
               )
            {
               genfunc_node_ptr->init_branches();

               const Type v = result->value();

               details::free_node(*node_allocator_,result);

               return node_allocator_->allocate<literal_node_t>(v);
            }
            else if (genfunc_node_ptr->init_branches())
            {
               parser_->state_.activate_side_effect("generic_function_call()");

               return result;
            }
            else
            {
               details::free_node(*node_allocator_, result);
               details::free_all_nodes(*node_allocator_, arg_list);

               return error_node();
            }
         }

         #ifndef exprtk_disable_string_capabilities
         inline expression_node_ptr string_function_call(igeneric_function_t* gf,
                                                         std::vector<expression_node_ptr>& arg_list,
                                                         const std::size_t& param_seq_index = std::numeric_limits<std::size_t>::max())
         {
            if (!all_nodes_valid(arg_list))
            {
               details::free_all_nodes(*node_allocator_,arg_list);
               return error_node();
            }

            typedef details::string_function_node      <Type,igeneric_function_t> alloc_type1;
            typedef details::multimode_strfunction_node<Type,igeneric_function_t> alloc_type2;

            const std::size_t no_psi = std::numeric_limits<std::size_t>::max();

            expression_node_ptr result = error_node();

            if (no_psi == param_seq_index)
               result = node_allocator_->allocate<alloc_type1>(gf,arg_list);
            else
               result = node_allocator_->allocate<alloc_type2>(gf, param_seq_index, arg_list);

            alloc_type1* strfunc_node_ptr = static_cast<alloc_type1*>(result);

            if (
                 !arg_list.empty()       &&
                 !gf->has_side_effects() &&
                 is_constant_foldable(arg_list)
               )
            {
               strfunc_node_ptr->init_branches();

               const Type v = result->value();

               details::free_node(*node_allocator_,result);

               return node_allocator_->allocate<literal_node_t>(v);
            }
            else if (strfunc_node_ptr->init_branches())
            {
               parser_->state_.activate_side_effect("string_function_call()");

               return result;
            }
            else
            {
               details::free_node     (*node_allocator_,result  );
               details::free_all_nodes(*node_allocator_,arg_list);

               return error_node();
            }
         }
         #endif

         #ifndef exprtk_disable_return_statement
         inline expression_node_ptr return_call(std::vector<expression_node_ptr>& arg_list)
         {
            if (!all_nodes_valid(arg_list))
            {
               details::free_all_nodes(*node_allocator_,arg_list);
               return error_node();
            }

            typedef details::return_node<Type> alloc_type;

            expression_node_ptr result = node_allocator_->
                                            allocate_rr<alloc_type>(arg_list,parser_->results_ctx());

            alloc_type* return_node_ptr = static_cast<alloc_type*>(result);

            if (return_node_ptr->init_branches())
            {
               parser_->state_.activate_side_effect("return_call()");

               return result;
            }
            else
            {
               details::free_node     (*node_allocator_, result  );
               details::free_all_nodes(*node_allocator_, arg_list);

               return error_node();
            }
         }

         inline expression_node_ptr return_envelope(expression_node_ptr body,
                                                    results_context_t* rc,
                                                    bool*& return_invoked)
         {
            typedef details::return_envelope_node<Type> alloc_type;

            expression_node_ptr result = node_allocator_->
                                            allocate_cr<alloc_type>(body,(*rc));

            return_invoked = static_cast<alloc_type*>(result)->retinvk_ptr();

            return result;
         }
         #else
         inline expression_node_ptr return_call(std::vector<expression_node_ptr>&)
         {
            return error_node();
         }

         inline expression_node_ptr return_envelope(expression_node_ptr,
                                                    results_context_t*,
                                                    bool*&)
         {
            return error_node();
         }
         #endif

         inline expression_node_ptr vector_element(const std::string& symbol,
                                                   vector_holder_ptr vector_base,
                                                   expression_node_ptr index)
         {
            expression_node_ptr result = error_node();

            if (details::is_constant_node(index))
            {
               std::size_t i = static_cast<std::size_t>(details::numeric::to_int64(index->value()));

               details::free_node(*node_allocator_,index);

               if (vector_base->rebaseable())
               {
                  return node_allocator_->allocate<rebasevector_celem_node_t>(i,vector_base);
               }

               const scope_element& se = parser_->sem_.get_element(symbol,i);

               if (se.index == i)
               {
                  result = se.var_node;
               }
               else
               {
                  scope_element nse;
                  nse.name      = symbol;
                  nse.active    = true;
                  nse.ref_count = 1;
                  nse.type      = scope_element::e_vecelem;
                  nse.index     = i;
                  nse.depth     = parser_->state_.scope_depth;
                  nse.data      = 0;
                  nse.var_node  = node_allocator_->allocate<variable_node_t>((*(*vector_base)[i]));

                  if (!parser_->sem_.add_element(nse))
                  {
                     parser_->set_synthesis_error("Failed to add new local vector element to SEM [1]");

                     parser_->sem_.free_element(nse);

                     result = error_node();
                  }

                  exprtk_debug(("vector_element() - INFO - Added new local vector element: %s\n",nse.name.c_str()));

                  parser_->state_.activate_side_effect("vector_element()");

                  result = nse.var_node;
               }
            }
            else if (vector_base->rebaseable())
               result = node_allocator_->allocate<rebasevector_elem_node_t>(index,vector_base);
            else
               result = node_allocator_->allocate<vector_elem_node_t>(index,vector_base);

            return result;
         }

      private:

         template <std::size_t N, typename NodePtr>
         inline bool is_constant_foldable(NodePtr (&b)[N]) const
         {
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
         inline bool is_constant_foldable(const Sequence<NodePtr,Allocator>& b) const
         {
            for (std::size_t i = 0; i < b.size(); ++i)
            {
               if (0 == b[i])
                  return false;
               else if (!details::is_constant_node(b[i]))
                  return false;
            }

            return true;
         }

         void lodge_assignment(symbol_type cst, expression_node_ptr node)
         {
            parser_->state_.activate_side_effect("lodge_assignment()");

            if (!parser_->dec_.collect_assignments())
               return;

            std::string symbol_name;

            switch (cst)
            {
               case e_st_variable : symbol_name = parser_->symtab_store_
                                                     .get_variable_name(node);
                                    break;

               #ifndef exprtk_disable_string_capabilities
               case e_st_string   : symbol_name = parser_->symtab_store_
                                                     .get_stringvar_name(node);
                                    break;
               #endif

               case e_st_vector   : {
                                       typedef details::vector_holder<T> vector_holder_t;

                                       vector_holder_t& vh = static_cast<vector_node_t*>(node)->vec_holder();

                                       symbol_name = parser_->symtab_store_.get_vector_name(&vh);
                                    }
                                    break;

               case e_st_vecelem  : {
                                       typedef details::vector_holder<T> vector_holder_t;

                                       vector_holder_t& vh = static_cast<vector_elem_node_t*>(node)->vec_holder();

                                       symbol_name = parser_->symtab_store_.get_vector_name(&vh);

                                       cst = e_st_vector;
                                    }
                                    break;

               default            : return;
            }

            if (!symbol_name.empty())
            {
               parser_->dec_.add_assignment(symbol_name,cst);
            }
         }

         const void* base_ptr(expression_node_ptr node)
         {
            if (node)
            {
               switch(node->type())
               {
                  case details::expression_node<T>::e_variable:
                     return reinterpret_cast<const void*>(&static_cast<variable_node_t*>(node)->ref());

                  case details::expression_node<T>::e_vecelem:
                     return reinterpret_cast<const void*>(&static_cast<vector_elem_node_t*>(node)->ref());

                  case details::expression_node<T>::e_rbvecelem:
                     return reinterpret_cast<const void*>(&static_cast<rebasevector_elem_node_t*>(node)->ref());

                  case details::expression_node<T>::e_rbveccelem:
                     return reinterpret_cast<const void*>(&static_cast<rebasevector_celem_node_t*>(node)->ref());

                  case details::expression_node<T>::e_vector:
                     return reinterpret_cast<const void*>(static_cast<vector_node_t*>(node)->vec_holder().data());

                  #ifndef exprtk_disable_string_capabilities
                  case details::expression_node<T>::e_stringvar:
                     return reinterpret_cast<const void*>((static_cast<stringvar_node_t*>(node)->base()));

                  case details::expression_node<T>::e_stringvarrng:
                     return reinterpret_cast<const void*>((static_cast<string_range_node_t*>(node)->base()));
                  #endif
                  default : return reinterpret_cast<const void*>(0);
               }
            }

            return reinterpret_cast<const void*>(0);
         }

         bool assign_immutable_symbol(expression_node_ptr node)
         {
            interval_t interval;
            const void* baseptr_addr = base_ptr(node);

            exprtk_debug(("assign_immutable_symbol - base ptr addr: %p\n", baseptr_addr));

            if (parser_->immutable_memory_map_.in_interval(baseptr_addr,interval))
            {
               typename immutable_symtok_map_t::iterator itr = parser_->immutable_symtok_map_.find(interval);

               if (parser_->immutable_symtok_map_.end() != itr)
               {
                  token_t& token = itr->second;
                  parser_->set_error(
                     parser_error::make_error(parser_error::e_parser,
                        token,
                        "ERR211 - Symbol '" + token.value + "' cannot be assigned-to as it is immutable.",
                        exprtk_error_location));
               }
               else
                  parser_->set_synthesis_error("Unable to assign symbol is immutable.");

               return true;
            }

            return false;
         }

         inline expression_node_ptr synthesize_assignment_expression(const details::operator_type& operation, expression_node_ptr (&branch)[2])
         {
            if (assign_immutable_symbol(branch[0]))
            {
               return error_node();
            }
            else if (details::is_variable_node(branch[0]))
            {
               lodge_assignment(e_st_variable,branch[0]);
               return synthesize_expression<assignment_node_t,2>(operation,branch);
            }
            else if (details::is_vector_elem_node(branch[0]))
            {
               lodge_assignment(e_st_vecelem,branch[0]);
               return synthesize_expression<assignment_vec_elem_node_t, 2>(operation, branch);
            }
            else if (details::is_rebasevector_elem_node(branch[0]))
            {
               lodge_assignment(e_st_vecelem,branch[0]);
               return synthesize_expression<assignment_rebasevec_elem_node_t, 2>(operation, branch);
            }
            else if (details::is_rebasevector_celem_node(branch[0]))
            {
               lodge_assignment(e_st_vecelem,branch[0]);
               return synthesize_expression<assignment_rebasevec_celem_node_t, 2>(operation, branch);
            }
            #ifndef exprtk_disable_string_capabilities
            else if (details::is_string_node(branch[0]))
            {
               lodge_assignment(e_st_string,branch[0]);
               return synthesize_expression<assignment_string_node_t,2>(operation, branch);
            }
            else if (details::is_string_range_node(branch[0]))
            {
               lodge_assignment(e_st_string,branch[0]);
               return synthesize_expression<assignment_string_range_node_t,2>(operation, branch);
            }
            #endif
            else if (details::is_vector_node(branch[0]))
            {
               lodge_assignment(e_st_vector,branch[0]);

               if (details::is_ivector_node(branch[1]))
                  return synthesize_expression<assignment_vecvec_node_t,2>(operation, branch);
               else
                  return synthesize_expression<assignment_vec_node_t,2>(operation, branch);
            }
            else
            {
               parser_->set_synthesis_error("Invalid assignment operation.[1]");

               return error_node();
            }
         }

         inline expression_node_ptr synthesize_assignment_operation_expression(const details::operator_type& operation,
                                                                               expression_node_ptr (&branch)[2])
         {
            if (assign_immutable_symbol(branch[0]))
            {
               return error_node();
            }

            if (details::is_variable_node(branch[0]))
            {
               lodge_assignment(e_st_variable,branch[0]);

               switch (operation)
               {
                  #define case_stmt(op0, op1)                                                                 \
                  case op0 : return node_allocator_->                                                         \
                                template allocate_rrr<typename details::assignment_op_node<Type,op1<Type> > > \
                                   (operation, branch[0], branch[1]);                                         \

                  case_stmt(details::e_addass , details::add_op)
                  case_stmt(details::e_subass , details::sub_op)
                  case_stmt(details::e_mulass , details::mul_op)
                  case_stmt(details::e_divass , details::div_op)
                  case_stmt(details::e_modass , details::mod_op)
                  #undef case_stmt
                  default : return error_node();
               }
            }
            else if (details::is_vector_elem_node(branch[0]))
            {
               lodge_assignment(e_st_vecelem,branch[0]);

               switch (operation)
               {
                  #define case_stmt(op0, op1)                                                                           \
                  case op0 : return node_allocator_->                                                                   \
                                 template allocate_rrr<typename details::assignment_vec_elem_op_node<Type,op1<Type> > > \
                                    (operation, branch[0], branch[1]);                                                  \

                  case_stmt(details::e_addass , details::add_op)
                  case_stmt(details::e_subass , details::sub_op)
                  case_stmt(details::e_mulass , details::mul_op)
                  case_stmt(details::e_divass , details::div_op)
                  case_stmt(details::e_modass , details::mod_op)
                  #undef case_stmt
                  default : return error_node();
               }
            }
            else if (details::is_rebasevector_elem_node(branch[0]))
            {
               lodge_assignment(e_st_vecelem,branch[0]);

               switch (operation)
               {
                  #define case_stmt(op0, op1)                                                                                 \
                  case op0 : return node_allocator_->                                                                         \
                                 template allocate_rrr<typename details::assignment_rebasevec_elem_op_node<Type,op1<Type> > > \
                                    (operation, branch[0], branch[1]);                                                        \

                  case_stmt(details::e_addass , details::add_op)
                  case_stmt(details::e_subass , details::sub_op)
                  case_stmt(details::e_mulass , details::mul_op)
                  case_stmt(details::e_divass , details::div_op)
                  case_stmt(details::e_modass , details::mod_op)
                  #undef case_stmt
                  default : return error_node();
               }
            }
            else if (details::is_rebasevector_celem_node(branch[0]))
            {
               lodge_assignment(e_st_vecelem,branch[0]);

               switch (operation)
               {
                  #define case_stmt(op0, op1)                                                                                  \
                  case op0 : return node_allocator_->                                                                          \
                                 template allocate_rrr<typename details::assignment_rebasevec_celem_op_node<Type,op1<Type> > > \
                                    (operation, branch[0], branch[1]);                                                         \

                  case_stmt(details::e_addass , details::add_op)
                  case_stmt(details::e_subass , details::sub_op)
                  case_stmt(details::e_mulass , details::mul_op)
                  case_stmt(details::e_divass , details::div_op)
                  case_stmt(details::e_modass , details::mod_op)
                  #undef case_stmt
                  default : return error_node();
               }
            }
            else if (details::is_vector_node(branch[0]))
            {
               lodge_assignment(e_st_vector,branch[0]);

               if (details::is_ivector_node(branch[1]))
               {
                  switch (operation)
                  {
                     #define case_stmt(op0, op1)                                                                        \
                     case op0 : return node_allocator_->                                                                \
                                   template allocate_rrr<typename details::assignment_vecvec_op_node<Type,op1<Type> > > \
                                      (operation, branch[0], branch[1]);                                                \

                     case_stmt(details::e_addass , details::add_op)
                     case_stmt(details::e_subass , details::sub_op)
                     case_stmt(details::e_mulass , details::mul_op)
                     case_stmt(details::e_divass , details::div_op)
                     case_stmt(details::e_modass , details::mod_op)
                     #undef case_stmt
                     default : return error_node();
                  }
               }
               else
               {
                  switch (operation)
                  {
                     #define case_stmt(op0, op1)                                                                     \
                     case op0 : return node_allocator_->                                                             \
                                   template allocate_rrr<typename details::assignment_vec_op_node<Type,op1<Type> > > \
                                      (operation, branch[0], branch[1]);                                             \

                     case_stmt(details::e_addass , details::add_op)
                     case_stmt(details::e_subass , details::sub_op)
                     case_stmt(details::e_mulass , details::mul_op)
                     case_stmt(details::e_divass , details::div_op)
                     case_stmt(details::e_modass , details::mod_op)
                     #undef case_stmt
                     default : return error_node();
                  }
               }
            }
            #ifndef exprtk_disable_string_capabilities
            else if (
                      (details::e_addass == operation) &&
                      details::is_string_node(branch[0])
                    )
            {
               typedef details::assignment_string_node<T,details::asn_addassignment> addass_t;

               lodge_assignment(e_st_string,branch[0]);

               return synthesize_expression<addass_t,2>(operation,branch);
            }
            #endif
            else
            {
               parser_->set_synthesis_error("Invalid assignment operation[2]");

               return error_node();
            }
         }

         inline expression_node_ptr synthesize_veceqineqlogic_operation_expression(const details::operator_type& operation,
                                                                                   expression_node_ptr (&branch)[2])
         {
            const bool is_b0_ivec = details::is_ivector_node(branch[0]);
            const bool is_b1_ivec = details::is_ivector_node(branch[1]);

            #define batch_eqineq_logic_case                 \
            case_stmt(details::e_lt    , details::lt_op   ) \
            case_stmt(details::e_lte   , details::lte_op  ) \
            case_stmt(details::e_gt    , details::gt_op   ) \
            case_stmt(details::e_gte   , details::gte_op  ) \
            case_stmt(details::e_eq    , details::eq_op   ) \
            case_stmt(details::e_ne    , details::ne_op   ) \
            case_stmt(details::e_equal , details::equal_op) \
            case_stmt(details::e_and   , details::and_op  ) \
            case_stmt(details::e_nand  , details::nand_op ) \
            case_stmt(details::e_or    , details::or_op   ) \
            case_stmt(details::e_nor   , details::nor_op  ) \
            case_stmt(details::e_xor   , details::xor_op  ) \
            case_stmt(details::e_xnor  , details::xnor_op ) \

            if (is_b0_ivec && is_b1_ivec)
            {
               switch (operation)
               {
                  #define case_stmt(op0, op1)                                                                    \
                  case op0 : return node_allocator_->                                                            \
                                template allocate_rrr<typename details::vec_binop_vecvec_node<Type,op1<Type> > > \
                                   (operation, branch[0], branch[1]);                                            \

                  batch_eqineq_logic_case
                  #undef case_stmt
                  default : return error_node();
               }
            }
            else if (is_b0_ivec && !is_b1_ivec)
            {
               switch (operation)
               {
                  #define case_stmt(op0, op1)                                                                    \
                  case op0 : return node_allocator_->                                                            \
                                template allocate_rrr<typename details::vec_binop_vecval_node<Type,op1<Type> > > \
                                   (operation, branch[0], branch[1]);                                            \

                  batch_eqineq_logic_case
                  #undef case_stmt
                  default : return error_node();
               }
            }
            else if (!is_b0_ivec && is_b1_ivec)
            {
               switch (operation)
               {
                  #define case_stmt(op0, op1)                                                                    \
                  case op0 : return node_allocator_->                                                            \
                                template allocate_rrr<typename details::vec_binop_valvec_node<Type,op1<Type> > > \
                                   (operation, branch[0], branch[1]);                                            \

                  batch_eqineq_logic_case
                  #undef case_stmt
                  default : return error_node();
               }
            }
            else
               return error_node();

            #undef batch_eqineq_logic_case
         }

         inline expression_node_ptr synthesize_vecarithmetic_operation_expression(const details::operator_type& operation,
                                                                                  expression_node_ptr (&branch)[2])
         {
            const bool is_b0_ivec = details::is_ivector_node(branch[0]);
            const bool is_b1_ivec = details::is_ivector_node(branch[1]);

            #define vector_ops                          \
            case_stmt(details::e_add , details::add_op) \
            case_stmt(details::e_sub , details::sub_op) \
            case_stmt(details::e_mul , details::mul_op) \
            case_stmt(details::e_div , details::div_op) \
            case_stmt(details::e_mod , details::mod_op) \

            if (is_b0_ivec && is_b1_ivec)
            {
               switch (operation)
               {
                  #define case_stmt(op0, op1)                                                                    \
                  case op0 : return node_allocator_->                                                            \
                                template allocate_rrr<typename details::vec_binop_vecvec_node<Type,op1<Type> > > \
                                   (operation, branch[0], branch[1]);                                            \

                  vector_ops
                  case_stmt(details::e_pow,details:: pow_op)
                  #undef case_stmt
                  default : return error_node();
               }
            }
            else if (is_b0_ivec && !is_b1_ivec)
            {
               switch (operation)
               {
                  #define case_stmt(op0, op1)                                                                    \
                  case op0 : return node_allocator_->                                                            \
                                template allocate_rrr<typename details::vec_binop_vecval_node<Type,op1<Type> > > \
                                   (operation, branch[0], branch[1]);                                            \

                  vector_ops
                  case_stmt(details::e_pow,details:: pow_op)
                  #undef case_stmt
                  default : return error_node();
               }
            }
            else if (!is_b0_ivec && is_b1_ivec)
            {
               switch (operation)
               {
                  #define case_stmt(op0, op1)                                                                    \
                  case op0 : return node_allocator_->                                                            \
                                template allocate_rrr<typename details::vec_binop_valvec_node<Type,op1<Type> > > \
                                   (operation, branch[0], branch[1]);                                            \

                  vector_ops
                  #undef case_stmt
                  default : return error_node();
               }
            }
            else
               return error_node();

            #undef vector_ops
         }

         inline expression_node_ptr synthesize_swap_expression(expression_node_ptr (&branch)[2])
         {
            const bool v0_is_ivar = details::is_ivariable_node(branch[0]);
            const bool v1_is_ivar = details::is_ivariable_node(branch[1]);

            const bool v0_is_ivec = details::is_ivector_node  (branch[0]);
            const bool v1_is_ivec = details::is_ivector_node  (branch[1]);

            #ifndef exprtk_disable_string_capabilities
            const bool v0_is_str = details::is_generally_string_node(branch[0]);
            const bool v1_is_str = details::is_generally_string_node(branch[1]);
            #endif

            expression_node_ptr result = error_node();

            if (v0_is_ivar && v1_is_ivar)
            {
               typedef details::variable_node<T>* variable_node_ptr;

               variable_node_ptr v0 = variable_node_ptr(0);
               variable_node_ptr v1 = variable_node_ptr(0);

               if (
                    (0 != (v0 = dynamic_cast<variable_node_ptr>(branch[0]))) &&
                    (0 != (v1 = dynamic_cast<variable_node_ptr>(branch[1])))
                  )
               {
                  result = node_allocator_->allocate<details::swap_node<T> >(v0,v1);
               }
               else
                  result = node_allocator_->allocate<details::swap_generic_node<T> >(branch[0],branch[1]);
            }
            else if (v0_is_ivec && v1_is_ivec)
            {
               result = node_allocator_->allocate<details::swap_vecvec_node<T> >(branch[0],branch[1]);
            }
            #ifndef exprtk_disable_string_capabilities
            else if (v0_is_str && v1_is_str)
            {
               if (is_string_node(branch[0]) && is_string_node(branch[1]))
                  result = node_allocator_->allocate<details::swap_string_node<T> >
                                               (branch[0], branch[1]);
               else
                  result = node_allocator_->allocate<details::swap_genstrings_node<T> >
                                               (branch[0], branch[1]);
            }
            #endif
            else
            {
               parser_->set_synthesis_error("Only variables, strings, vectors or vector elements can be swapped");

               return error_node();
            }

            parser_->state_.activate_side_effect("synthesize_swap_expression()");

            return result;
         }

         #ifndef exprtk_disable_sc_andor
         inline expression_node_ptr synthesize_shortcircuit_expression(const details::operator_type& operation, expression_node_ptr (&branch)[2])
         {
            expression_node_ptr result = error_node();

            if (details::is_constant_node(branch[0]))
            {
               if (
                    (details::e_scand == operation) &&
                    std::equal_to<T>()(T(0),branch[0]->value())
                  )
                  result = node_allocator_->allocate_c<literal_node_t>(T(0));
               else if (
                         (details::e_scor == operation) &&
                         std::not_equal_to<T>()(T(0),branch[0]->value())
                       )
                  result = node_allocator_->allocate_c<literal_node_t>(T(1));
            }

            if (details::is_constant_node(branch[1]) && (0 == result))
            {
               if (
                    (details::e_scand == operation) &&
                    std::equal_to<T>()(T(0),branch[1]->value())
                  )
                  result = node_allocator_->allocate_c<literal_node_t>(T(0));
               else if (
                         (details::e_scor == operation) &&
                         std::not_equal_to<T>()(T(0),branch[1]->value())
                       )
                  result = node_allocator_->allocate_c<literal_node_t>(T(1));
            }

            if (result)
            {
               details::free_node(*node_allocator_, branch[0]);
               details::free_node(*node_allocator_, branch[1]);

               return result;
            }
            else if (details::e_scand == operation)
            {
               return synthesize_expression<scand_node_t,2>(operation, branch);
            }
            else if (details::e_scor == operation)
            {
               return synthesize_expression<scor_node_t,2>(operation, branch);
            }
            else
               return error_node();
         }
         #else
         inline expression_node_ptr synthesize_shortcircuit_expression(const details::operator_type&, expression_node_ptr (&)[2])
         {
            return error_node();
         }
         #endif

         #define basic_opr_switch_statements         \
         case_stmt(details::e_add , details::add_op) \
         case_stmt(details::e_sub , details::sub_op) \
         case_stmt(details::e_mul , details::mul_op) \
         case_stmt(details::e_div , details::div_op) \
         case_stmt(details::e_mod , details::mod_op) \
         case_stmt(details::e_pow , details::pow_op) \

         #define extended_opr_switch_statements        \
         case_stmt(details::e_lt   , details::lt_op  ) \
         case_stmt(details::e_lte  , details::lte_op ) \
         case_stmt(details::e_gt   , details::gt_op  ) \
         case_stmt(details::e_gte  , details::gte_op ) \
         case_stmt(details::e_eq   , details::eq_op  ) \
         case_stmt(details::e_ne   , details::ne_op  ) \
         case_stmt(details::e_and  , details::and_op ) \
         case_stmt(details::e_nand , details::nand_op) \
         case_stmt(details::e_or   , details::or_op  ) \
         case_stmt(details::e_nor  , details::nor_op ) \
         case_stmt(details::e_xor  , details::xor_op ) \
         case_stmt(details::e_xnor , details::xnor_op) \

         #ifndef exprtk_disable_cardinal_pow_optimisation
         template <typename TType, template <typename, typename> class IPowNode>
         inline expression_node_ptr cardinal_pow_optimisation_impl(const TType& v, const unsigned int& p)
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

         inline expression_node_ptr cardinal_pow_optimisation(const T& v, const T& c)
         {
            const bool not_recipricol = (c >= T(0));
            const unsigned int p = static_cast<unsigned int>(details::numeric::to_int32(details::numeric::abs(c)));

            if (0 == p)
               return node_allocator_->allocate_c<literal_node_t>(T(1));
            else if (std::equal_to<T>()(T(2),c))
            {
               return node_allocator_->
                  template allocate_rr<typename details::vov_node<Type,details::mul_op<Type> > >(v,v);
            }
            else
            {
               if (not_recipricol)
                  return cardinal_pow_optimisation_impl<T,details::ipow_node>(v,p);
               else
                  return cardinal_pow_optimisation_impl<T,details::ipowinv_node>(v,p);
            }
         }

         inline bool cardinal_pow_optimisable(const details::operator_type& operation, const T& c) const
         {
            return (details::e_pow == operation) && (details::numeric::abs(c) <= T(60)) && details::numeric::is_integer(c);
         }

         inline expression_node_ptr cardinal_pow_optimisation(expression_node_ptr (&branch)[2])
         {
            const Type c = static_cast<details::literal_node<Type>*>(branch[1])->value();
            const bool not_recipricol = (c >= T(0));
            const unsigned int p = static_cast<unsigned int>(details::numeric::to_int32(details::numeric::abs(c)));

            node_allocator_->free(branch[1]);

            if (0 == p)
            {
               details::free_all_nodes(*node_allocator_, branch);

               return node_allocator_->allocate_c<literal_node_t>(T(1));
            }
            else if (not_recipricol)
               return cardinal_pow_optimisation_impl<expression_node_ptr,details::bipow_node>(branch[0],p);
            else
               return cardinal_pow_optimisation_impl<expression_node_ptr,details::bipowninv_node>(branch[0],p);
         }
         #else
         inline expression_node_ptr cardinal_pow_optimisation(T&, const T&)
         {
            return error_node();
         }

         inline bool cardinal_pow_optimisable(const details::operator_type&, const T&)
         {
            return false;
         }

         inline expression_node_ptr cardinal_pow_optimisation(expression_node_ptr(&)[2])
         {
            return error_node();
         }
         #endif

         struct synthesize_binary_ext_expression
         {
            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               const bool left_neg  = is_neg_unary_node(branch[0]);
               const bool right_neg = is_neg_unary_node(branch[1]);

               if (left_neg && right_neg)
               {
                  if (
                       (details::e_add == operation) ||
                       (details::e_sub == operation) ||
                       (details::e_mul == operation) ||
                       (details::e_div == operation)
                     )
                  {
                     if (
                          !expr_gen.parser_->simplify_unary_negation_branch(branch[0]) ||
                          !expr_gen.parser_->simplify_unary_negation_branch(branch[1])
                        )
                     {
                        details::free_all_nodes(*expr_gen.node_allocator_,branch);

                        return error_node();
                     }
                  }

                  switch (operation)
                  {
                                           // -f(x + 1) + -g(y + 1) --> -(f(x + 1) + g(y + 1))
                     case details::e_add : return expr_gen(details::e_neg,
                                              expr_gen.node_allocator_->
                                                 template allocate<typename details::binary_ext_node<Type,details::add_op<Type> > >
                                                    (branch[0],branch[1]));

                                           // -f(x + 1) - -g(y + 1) --> g(y + 1) - f(x + 1)
                     case details::e_sub : return expr_gen.node_allocator_->
                                              template allocate<typename details::binary_ext_node<Type,details::sub_op<Type> > >
                                                 (branch[1],branch[0]);

                     default             : break;
                  }
               }
               else if (left_neg && !right_neg)
               {
                  if (
                       (details::e_add == operation) ||
                       (details::e_sub == operation) ||
                       (details::e_mul == operation) ||
                       (details::e_div == operation)
                     )
                  {
                     if (!expr_gen.parser_->simplify_unary_negation_branch(branch[0]))
                     {
                        details::free_all_nodes(*expr_gen.node_allocator_,branch);

                        return error_node();
                     }

                     switch (operation)
                     {
                                              // -f(x + 1) + g(y + 1) --> g(y + 1) - f(x + 1)
                        case details::e_add : return expr_gen.node_allocator_->
                                                 template allocate<typename details::binary_ext_node<Type,details::sub_op<Type> > >
                                                   (branch[1], branch[0]);

                                              // -f(x + 1) - g(y + 1) --> -(f(x + 1) + g(y + 1))
                        case details::e_sub : return expr_gen(details::e_neg,
                                                 expr_gen.node_allocator_->
                                                    template allocate<typename details::binary_ext_node<Type,details::add_op<Type> > >
                                                       (branch[0], branch[1]));

                                              // -f(x + 1) * g(y + 1) --> -(f(x + 1) * g(y + 1))
                        case details::e_mul : return expr_gen(details::e_neg,
                                                 expr_gen.node_allocator_->
                                                    template allocate<typename details::binary_ext_node<Type,details::mul_op<Type> > >
                                                       (branch[0], branch[1]));

                                              // -f(x + 1) / g(y + 1) --> -(f(x + 1) / g(y + 1))
                        case details::e_div : return expr_gen(details::e_neg,
                                                 expr_gen.node_allocator_->
                                                    template allocate<typename details::binary_ext_node<Type,details::div_op<Type> > >
                                                       (branch[0], branch[1]));

                        default             : return error_node();
                     }
                  }
               }
               else if (!left_neg && right_neg)
               {
                  if (
                       (details::e_add == operation) ||
                       (details::e_sub == operation) ||
                       (details::e_mul == operation) ||
                       (details::e_div == operation)
                     )
                  {
                     if (!expr_gen.parser_->simplify_unary_negation_branch(branch[1]))
                     {
                        details::free_all_nodes(*expr_gen.node_allocator_,branch);

                        return error_node();
                     }

                     switch (operation)
                     {
                                              // f(x + 1) + -g(y + 1) --> f(x + 1) - g(y + 1)
                        case details::e_add : return expr_gen.node_allocator_->
                                                 template allocate<typename details::binary_ext_node<Type,details::sub_op<Type> > >
                                                   (branch[0], branch[1]);

                                              // f(x + 1) - - g(y + 1) --> f(x + 1) + g(y + 1)
                        case details::e_sub : return expr_gen.node_allocator_->
                                                 template allocate<typename details::binary_ext_node<Type,details::add_op<Type> > >
                                                   (branch[0], branch[1]);

                                              // f(x + 1) * -g(y + 1) --> -(f(x + 1) * g(y + 1))
                        case details::e_mul : return expr_gen(details::e_neg,
                                                 expr_gen.node_allocator_->
                                                    template allocate<typename details::binary_ext_node<Type,details::mul_op<Type> > >
                                                       (branch[0], branch[1]));

                                              // f(x + 1) / -g(y + 1) --> -(f(x + 1) / g(y + 1))
                        case details::e_div : return expr_gen(details::e_neg,
                                                 expr_gen.node_allocator_->
                                                    template allocate<typename details::binary_ext_node<Type,details::div_op<Type> > >
                                                       (branch[0], branch[1]));

                        default             : return error_node();
                     }
                  }
               }

               switch (operation)
               {
                  #define case_stmt(op0, op1)                                                          \
                  case op0 : return expr_gen.node_allocator_->                                         \
                                template allocate<typename details::binary_ext_node<Type,op1<Type> > > \
                                   (branch[0], branch[1]);                                             \

                  basic_opr_switch_statements
                  extended_opr_switch_statements
                  #undef case_stmt
                  default : return error_node();
               }
            }
         };

         struct synthesize_vob_expression
         {
            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               const Type& v = static_cast<details::variable_node<Type>*>(branch[0])->ref();

               #ifndef exprtk_disable_enhanced_features
               if (details::is_sf3ext_node(branch[1]))
               {
                  expression_node_ptr result = error_node();

                  const bool synthesis_result =
                     synthesize_sf4ext_expression::template compile_right<vtype>
                        (expr_gen, v, operation, branch[1], result);

                  if (synthesis_result)
                  {
                     details::free_node(*expr_gen.node_allocator_,branch[1]);
                     return result;
                  }
               }
               #endif

               if (
                    (details::e_mul == operation) ||
                    (details::e_div == operation)
                  )
               {
                  if (details::is_uv_node(branch[1]))
                  {
                     typedef details::uv_base_node<Type>* uvbn_ptr_t;

                     details::operator_type o = static_cast<uvbn_ptr_t>(branch[1])->operation();

                     if (details::e_neg == o)
                     {
                        const Type& v1 = static_cast<uvbn_ptr_t>(branch[1])->v();

                        details::free_node(*expr_gen.node_allocator_,branch[1]);

                        switch (operation)
                        {
                           case details::e_mul : return expr_gen(details::e_neg,
                                                    expr_gen.node_allocator_->
                                                       template allocate_rr<typename details::
                                                          vov_node<Type,details::mul_op<Type> > >(v,v1));

                           case details::e_div : return expr_gen(details::e_neg,
                                                    expr_gen.node_allocator_->
                                                       template allocate_rr<typename details::
                                                          vov_node<Type,details::div_op<Type> > >(v,v1));

                           default             : break;
                        }
                     }
                  }
               }

               switch (operation)
               {
                  #define case_stmt(op0, op1)                                                      \
                  case op0 : return expr_gen.node_allocator_->                                     \
                                template allocate_rc<typename details::vob_node<Type,op1<Type> > > \
                                   (v, branch[1]);                                                 \

                  basic_opr_switch_statements
                  extended_opr_switch_statements
                  #undef case_stmt
                  default : return error_node();
               }
            }
         };

         struct synthesize_bov_expression
         {
            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               const Type& v = static_cast<details::variable_node<Type>*>(branch[1])->ref();

               #ifndef exprtk_disable_enhanced_features
               if (details::is_sf3ext_node(branch[0]))
               {
                  expression_node_ptr result = error_node();

                  const bool synthesis_result =
                     synthesize_sf4ext_expression::template compile_left<vtype>
                        (expr_gen, v, operation, branch[0], result);

                  if (synthesis_result)
                  {
                     details::free_node(*expr_gen.node_allocator_, branch[0]);

                     return result;
                  }
               }
               #endif

               if (
                    (details::e_add == operation) ||
                    (details::e_sub == operation) ||
                    (details::e_mul == operation) ||
                    (details::e_div == operation)
                  )
               {
                  if (details::is_uv_node(branch[0]))
                  {
                     typedef details::uv_base_node<Type>* uvbn_ptr_t;

                     details::operator_type o = static_cast<uvbn_ptr_t>(branch[0])->operation();

                     if (details::e_neg == o)
                     {
                        const Type& v0 = static_cast<uvbn_ptr_t>(branch[0])->v();

                        details::free_node(*expr_gen.node_allocator_,branch[0]);

                        switch (operation)
                        {
                           case details::e_add : return expr_gen.node_allocator_->
                                                    template allocate_rr<typename details::
                                                       vov_node<Type,details::sub_op<Type> > >(v,v0);

                           case details::e_sub : return expr_gen(details::e_neg,
                                                    expr_gen.node_allocator_->
                                                       template allocate_rr<typename details::
                                                          vov_node<Type,details::add_op<Type> > >(v0,v));

                           case details::e_mul : return expr_gen(details::e_neg,
                                                    expr_gen.node_allocator_->
                                                       template allocate_rr<typename details::
                                                          vov_node<Type,details::mul_op<Type> > >(v0,v));

                           case details::e_div : return expr_gen(details::e_neg,
                                                    expr_gen.node_allocator_->
                                                       template allocate_rr<typename details::
                                                          vov_node<Type,details::div_op<Type> > >(v0,v));
                           default : break;
                        }
                     }
                  }
               }

               switch (operation)
               {
                  #define case_stmt(op0, op1)                                                      \
                  case op0 : return expr_gen.node_allocator_->                                     \
                                template allocate_cr<typename details::bov_node<Type,op1<Type> > > \
                                   (branch[0], v);                                                 \

                  basic_opr_switch_statements
                  extended_opr_switch_statements
                  #undef case_stmt
                  default : return error_node();
               }
            }
         };

         struct synthesize_cob_expression
         {
            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               const Type c = static_cast<details::literal_node<Type>*>(branch[0])->value();

               details::free_node(*expr_gen.node_allocator_,branch[0]);

               if (std::equal_to<T>()(T(0),c) && (details::e_mul == operation))
               {
                  details::free_node(*expr_gen.node_allocator_,branch[1]);

                  return expr_gen(T(0));
               }
               else if (std::equal_to<T>()(T(0),c) && (details::e_div == operation))
               {
                  details::free_node(*expr_gen.node_allocator_, branch[1]);

                  return expr_gen(T(0));
               }
               else if (std::equal_to<T>()(T(0),c) && (details::e_add == operation))
                  return branch[1];
               else if (std::equal_to<T>()(T(1),c) && (details::e_mul == operation))
                  return branch[1];

               if (details::is_cob_node(branch[1]))
               {
                  // Simplify expressions of the form:
                  // 1. (1 * (2 * (3 * (4 * (5 * (6 * (7 * (8 * (9 + x))))))))) --> 40320 * (9 + x)
                  // 2. (1 + (2 + (3 + (4 + (5 + (6 + (7 + (8 + (9 + x))))))))) --> 45 + x
                  if (
                       (details::e_mul == operation) ||
                       (details::e_add == operation)
                     )
                  {
                     details::cob_base_node<Type>* cobnode = static_cast<details::cob_base_node<Type>*>(branch[1]);

                     if (operation == cobnode->operation())
                     {
                        switch (operation)
                        {
                           case details::e_add : cobnode->set_c(c + cobnode->c()); break;
                           case details::e_mul : cobnode->set_c(c * cobnode->c()); break;
                           default             : return error_node();
                        }

                        return cobnode;
                     }
                  }

                  if (operation == details::e_mul)
                  {
                     details::cob_base_node<Type>* cobnode = static_cast<details::cob_base_node<Type>*>(branch[1]);
                     details::operator_type cob_opr = cobnode->operation();

                     if (
                          (details::e_div == cob_opr) ||
                          (details::e_mul == cob_opr)
                        )
                     {
                        switch (cob_opr)
                        {
                           case details::e_div : cobnode->set_c(c * cobnode->c()); break;
                           case details::e_mul : cobnode->set_c(cobnode->c() / c); break;
                           default             : return error_node();
                        }

                        return cobnode;
                     }
                  }
                  else if (operation == details::e_div)
                  {
                     details::cob_base_node<Type>* cobnode = static_cast<details::cob_base_node<Type>*>(branch[1]);
                     details::operator_type cob_opr = cobnode->operation();

                     if (
                          (details::e_div == cob_opr) ||
                          (details::e_mul == cob_opr)
                        )
                     {
                        details::expression_node<Type>* new_cobnode = error_node();

                        switch (cob_opr)
                        {
                           case details::e_div : new_cobnode = expr_gen.node_allocator_->
                                                    template allocate_tt<typename details::cob_node<Type,details::mul_op<Type> > >
                                                       (c / cobnode->c(), cobnode->move_branch(0));
                                                 break;

                           case details::e_mul : new_cobnode = expr_gen.node_allocator_->
                                                    template allocate_tt<typename details::cob_node<Type,details::div_op<Type> > >
                                                       (c / cobnode->c(), cobnode->move_branch(0));
                                                 break;

                           default             : return error_node();
                        }

                        details::free_node(*expr_gen.node_allocator_,branch[1]);

                        return new_cobnode;
                     }
                  }
               }
               #ifndef exprtk_disable_enhanced_features
               else if (details::is_sf3ext_node(branch[1]))
               {
                  expression_node_ptr result = error_node();

                  const bool synthesis_result =
                     synthesize_sf4ext_expression::template compile_right<ctype>
                        (expr_gen, c, operation, branch[1], result);

                  if (synthesis_result)
                  {
                     details::free_node(*expr_gen.node_allocator_,branch[1]);

                     return result;
                  }
               }
               #endif

               switch (operation)
               {
                  #define case_stmt(op0, op1)                                                      \
                  case op0 : return expr_gen.node_allocator_->                                     \
                                template allocate_tt<typename details::cob_node<Type,op1<Type> > > \
                                   (c,  branch[1]);                                                \

                  basic_opr_switch_statements
                  extended_opr_switch_statements
                  #undef case_stmt
                  default : return error_node();
               }
            }
         };

         struct synthesize_boc_expression
         {
            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               const Type c = static_cast<details::literal_node<Type>*>(branch[1])->value();

               details::free_node(*(expr_gen.node_allocator_), branch[1]);

               if (std::equal_to<T>()(T(0),c) && (details::e_mul == operation))
               {
                  details::free_node(*expr_gen.node_allocator_, branch[0]);

                  return expr_gen(T(0));
               }
               else if (std::equal_to<T>()(T(0),c) && (details::e_div == operation))
               {
                  details::free_node(*expr_gen.node_allocator_, branch[0]);

                  return expr_gen(std::numeric_limits<T>::quiet_NaN());
               }
               else if (std::equal_to<T>()(T(0),c) && (details::e_add == operation))
                  return branch[0];
               else if (std::equal_to<T>()(T(1),c) && (details::e_mul == operation))
                  return branch[0];

               if (details::is_boc_node(branch[0]))
               {
                  // Simplify expressions of the form:
                  // 1. (((((((((x + 9) * 8) * 7) * 6) * 5) * 4) * 3) * 2) * 1) --> (x + 9) * 40320
                  // 2. (((((((((x + 9) + 8) + 7) + 6) + 5) + 4) + 3) + 2) + 1) --> x + 45
                  if (
                       (details::e_mul == operation) ||
                       (details::e_add == operation)
                     )
                  {
                     details::boc_base_node<Type>* bocnode = static_cast<details::boc_base_node<Type>*>(branch[0]);

                     if (operation == bocnode->operation())
                     {
                        switch (operation)
                        {
                           case details::e_add : bocnode->set_c(c + bocnode->c()); break;
                           case details::e_mul : bocnode->set_c(c * bocnode->c()); break;
                           default             : return error_node();
                        }

                        return bocnode;
                     }
                  }
                  else if (operation == details::e_div)
                  {
                     details::boc_base_node<Type>* bocnode = static_cast<details::boc_base_node<Type>*>(branch[0]);
                     details::operator_type        boc_opr = bocnode->operation();

                     if (
                          (details::e_div == boc_opr) ||
                          (details::e_mul == boc_opr)
                        )
                     {
                        switch (boc_opr)
                        {
                           case details::e_div : bocnode->set_c(c * bocnode->c()); break;
                           case details::e_mul : bocnode->set_c(bocnode->c() / c); break;
                           default             : return error_node();
                        }

                        return bocnode;
                     }
                  }
                  else if (operation == details::e_pow)
                  {
                     // (v ^ c0) ^ c1 --> v ^(c0 * c1)
                     details::boc_base_node<Type>* bocnode = static_cast<details::boc_base_node<Type>*>(branch[0]);
                     details::operator_type        boc_opr = bocnode->operation();

                     if (details::e_pow == boc_opr)
                     {
                        bocnode->set_c(bocnode->c() * c);

                        return bocnode;
                     }
                  }
               }

               #ifndef exprtk_disable_enhanced_features
               if (details::is_sf3ext_node(branch[0]))
               {
                  expression_node_ptr result = error_node();

                  const bool synthesis_result =
                     synthesize_sf4ext_expression::template compile_left<ctype>
                        (expr_gen, c, operation, branch[0], result);

                  if (synthesis_result)
                  {
                     free_node(*expr_gen.node_allocator_, branch[0]);

                     return result;
                  }
               }
               #endif

               switch (operation)
               {
                  #define case_stmt(op0, op1)                                                      \
                  case op0 : return expr_gen.node_allocator_->                                     \
                                template allocate_cr<typename details::boc_node<Type,op1<Type> > > \
                                   (branch[0], c);                                                 \

                  basic_opr_switch_statements
                  extended_opr_switch_statements
                  #undef case_stmt
                  default : return error_node();
               }
            }
         };

         struct synthesize_cocob_expression
         {
            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               expression_node_ptr result = error_node();

               // (cob) o c --> cob
               if (details::is_cob_node(branch[0]))
               {
                  details::cob_base_node<Type>* cobnode = static_cast<details::cob_base_node<Type>*>(branch[0]);

                  const Type c = static_cast<details::literal_node<Type>*>(branch[1])->value();

                  if (std::equal_to<T>()(T(0),c) && (details::e_mul == operation))
                  {
                     details::free_node(*expr_gen.node_allocator_, branch[0]);
                     details::free_node(*expr_gen.node_allocator_, branch[1]);

                     return expr_gen(T(0));
                  }
                  else if (std::equal_to<T>()(T(0),c) && (details::e_div == operation))
                  {
                     details::free_node(*expr_gen.node_allocator_, branch[0]);
                     details::free_node(*expr_gen.node_allocator_, branch[1]);

                     return expr_gen(T(std::numeric_limits<T>::quiet_NaN()));
                  }
                  else if (std::equal_to<T>()(T(0),c) && (details::e_add == operation))
                  {
                     details::free_node(*expr_gen.node_allocator_, branch[1]);

                     return branch[0];
                  }
                  else if (std::equal_to<T>()(T(1),c) && (details::e_mul == operation))
                  {
                     details::free_node(*expr_gen.node_allocator_, branch[1]);

                     return branch[0];
                  }
                  else if (std::equal_to<T>()(T(1),c) && (details::e_div == operation))
                  {
                     details::free_node(*expr_gen.node_allocator_, branch[1]);

                     return branch[0];
                  }

                  const bool op_addsub = (details::e_add == cobnode->operation()) ||
                                         (details::e_sub == cobnode->operation()) ;

                  if (op_addsub)
                  {
                     switch (operation)
                     {
                        case details::e_add : cobnode->set_c(cobnode->c() + c); break;
                        case details::e_sub : cobnode->set_c(cobnode->c() - c); break;
                        default             : return error_node();
                     }

                     result = cobnode;
                  }
                  else if (details::e_mul == cobnode->operation())
                  {
                     switch (operation)
                     {
                        case details::e_mul : cobnode->set_c(cobnode->c() * c); break;
                        case details::e_div : cobnode->set_c(cobnode->c() / c); break;
                        default             : return error_node();
                     }

                     result = cobnode;
                  }
                  else if (details::e_div == cobnode->operation())
                  {
                     if (details::e_mul == operation)
                     {
                        cobnode->set_c(cobnode->c() * c);
                        result = cobnode;
                     }
                     else if (details::e_div == operation)
                     {
                        result = expr_gen.node_allocator_->
                                    template allocate_tt<typename details::cob_node<Type,details::div_op<Type> > >
                                       (cobnode->c() / c, cobnode->move_branch(0));

                        details::free_node(*expr_gen.node_allocator_, branch[0]);
                     }
                  }

                  if (result)
                  {
                     details::free_node(*expr_gen.node_allocator_,branch[1]);
                  }
               }

               // c o (cob) --> cob
               else if (details::is_cob_node(branch[1]))
               {
                  details::cob_base_node<Type>* cobnode = static_cast<details::cob_base_node<Type>*>(branch[1]);

                  const Type c = static_cast<details::literal_node<Type>*>(branch[0])->value();

                  if (std::equal_to<T>()(T(0),c) && (details::e_mul == operation))
                  {
                     details::free_node(*expr_gen.node_allocator_, branch[0]);
                     details::free_node(*expr_gen.node_allocator_, branch[1]);

                     return expr_gen(T(0));
                  }
                  else if (std::equal_to<T>()(T(0),c) && (details::e_div == operation))
                  {
                     details::free_node(*expr_gen.node_allocator_, branch[0]);
                     details::free_node(*expr_gen.node_allocator_, branch[1]);

                     return expr_gen(T(0));
                  }
                  else if (std::equal_to<T>()(T(0),c) && (details::e_add == operation))
                  {
                     details::free_node(*expr_gen.node_allocator_, branch[0]);

                     return branch[1];
                  }
                  else if (std::equal_to<T>()(T(1),c) && (details::e_mul == operation))
                  {
                     details::free_node(*expr_gen.node_allocator_, branch[0]);

                     return branch[1];
                  }

                  if (details::e_add == cobnode->operation())
                  {
                     if (details::e_add == operation)
                     {
                        cobnode->set_c(c + cobnode->c());
                        result = cobnode;
                     }
                     else if (details::e_sub == operation)
                     {
                        result = expr_gen.node_allocator_->
                                    template allocate_tt<typename details::cob_node<Type,details::sub_op<Type> > >
                                       (c - cobnode->c(), cobnode->move_branch(0));

                        details::free_node(*expr_gen.node_allocator_,branch[1]);
                     }
                  }
                  else if (details::e_sub == cobnode->operation())
                  {
                     if (details::e_add == operation)
                     {
                        cobnode->set_c(c + cobnode->c());
                        result = cobnode;
                     }
                     else if (details::e_sub == operation)
                     {
                        result = expr_gen.node_allocator_->
                                    template allocate_tt<typename details::cob_node<Type,details::add_op<Type> > >
                                       (c - cobnode->c(), cobnode->move_branch(0));

                        details::free_node(*expr_gen.node_allocator_,branch[1]);
                     }
                  }
                  else if (details::e_mul == cobnode->operation())
                  {
                     if (details::e_mul == operation)
                     {
                        cobnode->set_c(c * cobnode->c());
                        result = cobnode;
                     }
                     else if (details::e_div == operation)
                     {
                        result = expr_gen.node_allocator_->
                                    template allocate_tt<typename details::cob_node<Type,details::div_op<Type> > >
                                       (c / cobnode->c(), cobnode->move_branch(0));

                        details::free_node(*expr_gen.node_allocator_,branch[1]);
                     }
                  }
                  else if (details::e_div == cobnode->operation())
                  {
                     if (details::e_mul == operation)
                     {
                        cobnode->set_c(c * cobnode->c());
                        result = cobnode;
                     }
                     else if (details::e_div == operation)
                     {
                        result = expr_gen.node_allocator_->
                                    template allocate_tt<typename details::cob_node<Type,details::mul_op<Type> > >
                                       (c / cobnode->c(), cobnode->move_branch(0));

                        details::free_node(*expr_gen.node_allocator_,branch[1]);
                     }
                  }

                  if (result)
                  {
                     details::free_node(*expr_gen.node_allocator_,branch[0]);
                  }
               }

               return result;
            }
         };

         struct synthesize_coboc_expression
         {
            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               expression_node_ptr result = error_node();

               // (boc) o c --> boc
               if (details::is_boc_node(branch[0]))
               {
                  details::boc_base_node<Type>* bocnode = static_cast<details::boc_base_node<Type>*>(branch[0]);

                  const Type c = static_cast<details::literal_node<Type>*>(branch[1])->value();

                  if (details::e_add == bocnode->operation())
                  {
                     switch (operation)
                     {
                        case details::e_add : bocnode->set_c(bocnode->c() + c); break;
                        case details::e_sub : bocnode->set_c(bocnode->c() - c); break;
                        default             : return error_node();
                     }

                     result = bocnode;
                  }
                  else if (details::e_mul == bocnode->operation())
                  {
                     switch (operation)
                     {
                        case details::e_mul : bocnode->set_c(bocnode->c() * c); break;
                        case details::e_div : bocnode->set_c(bocnode->c() / c); break;
                        default             : return error_node();
                     }

                     result = bocnode;
                  }
                  else if (details::e_sub == bocnode->operation())
                  {
                     if (details::e_add == operation)
                     {
                        result = expr_gen.node_allocator_->
                                    template allocate_tt<typename details::boc_node<Type,details::add_op<Type> > >
                                       (bocnode->move_branch(0), c - bocnode->c());

                        details::free_node(*expr_gen.node_allocator_,branch[0]);
                     }
                     else if (details::e_sub == operation)
                     {
                        bocnode->set_c(bocnode->c() + c);
                        result = bocnode;
                     }
                  }
                  else if (details::e_div == bocnode->operation())
                  {
                     switch (operation)
                     {
                        case details::e_div : bocnode->set_c(bocnode->c() * c); break;
                        case details::e_mul : bocnode->set_c(bocnode->c() / c); break;
                        default             : return error_node();
                     }

                     result = bocnode;
                  }

                  if (result)
                  {
                     details::free_node(*expr_gen.node_allocator_, branch[1]);
                  }
               }

               // c o (boc) --> boc
               else if (details::is_boc_node(branch[1]))
               {
                  details::boc_base_node<Type>* bocnode = static_cast<details::boc_base_node<Type>*>(branch[1]);

                  const Type c = static_cast<details::literal_node<Type>*>(branch[0])->value();

                  if (details::e_add == bocnode->operation())
                  {
                     if (details::e_add == operation)
                     {
                        bocnode->set_c(c + bocnode->c());
                        result = bocnode;
                     }
                     else if (details::e_sub == operation)
                     {
                        result = expr_gen.node_allocator_->
                                    template allocate_tt<typename details::cob_node<Type,details::sub_op<Type> > >
                                       (c - bocnode->c(), bocnode->move_branch(0));

                        details::free_node(*expr_gen.node_allocator_,branch[1]);
                     }
                  }
                  else if (details::e_sub == bocnode->operation())
                  {
                     if (details::e_add == operation)
                     {
                        result = expr_gen.node_allocator_->
                                    template allocate_tt<typename details::boc_node<Type,details::add_op<Type> > >
                                       (bocnode->move_branch(0), c - bocnode->c());

                        details::free_node(*expr_gen.node_allocator_,branch[1]);
                     }
                     else if (details::e_sub == operation)
                     {
                        result = expr_gen.node_allocator_->
                                    template allocate_tt<typename details::cob_node<Type,details::sub_op<Type> > >
                                       (c + bocnode->c(), bocnode->move_branch(0));

                        details::free_node(*expr_gen.node_allocator_,branch[1]);
                     }
                  }
                  else if (details::e_mul == bocnode->operation())
                  {
                     if (details::e_mul == operation)
                     {
                        bocnode->set_c(c * bocnode->c());
                        result = bocnode;
                     }
                     else if (details::e_div == operation)
                     {
                        result = expr_gen.node_allocator_->
                                    template allocate_tt<typename details::cob_node<Type,details::div_op<Type> > >
                                       (c / bocnode->c(), bocnode->move_branch(0));

                        details::free_node(*expr_gen.node_allocator_,branch[1]);
                     }
                  }
                  else if (details::e_div == bocnode->operation())
                  {
                     if (details::e_mul == operation)
                     {
                        bocnode->set_c(bocnode->c() / c);
                        result = bocnode;
                     }
                     else if (details::e_div == operation)
                     {
                        result = expr_gen.node_allocator_->
                                    template allocate_tt<typename details::cob_node<Type,details::div_op<Type> > >
                                       (c * bocnode->c(), bocnode->move_branch(0));

                        details::free_node(*expr_gen.node_allocator_,branch[1]);
                     }
                  }

                  if (result)
                  {
                     details::free_node(*expr_gen.node_allocator_,branch[0]);
                  }
               }

               return result;
            }
         };

         #ifndef exprtk_disable_enhanced_features
         inline bool synthesize_expression(const details::operator_type& operation,
                                           expression_node_ptr (&branch)[2],
                                           expression_node_ptr& result)
         {
            result = error_node();

            if (!operation_optimisable(operation))
               return false;

            const std::string node_id = branch_to_id(branch);

            const typename synthesize_map_t::iterator itr = synthesize_map_.find(node_id);

            if (synthesize_map_.end() != itr)
            {
               result = itr->second((*this), operation, branch);

               return true;
            }
            else
               return false;
         }

         struct synthesize_vov_expression
         {
            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               const Type& v1 = static_cast<details::variable_node<Type>*>(branch[0])->ref();
               const Type& v2 = static_cast<details::variable_node<Type>*>(branch[1])->ref();

               switch (operation)
               {
                  #define case_stmt(op0, op1)                                                      \
                  case op0 : return expr_gen.node_allocator_->                                     \
                                template allocate_rr<typename details::vov_node<Type,op1<Type> > > \
                                   (v1, v2);                                                       \

                  basic_opr_switch_statements
                  extended_opr_switch_statements
                  #undef case_stmt
                  default : return error_node();
               }
            }
         };

         struct synthesize_cov_expression
         {
            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               const Type  c = static_cast<details::literal_node<Type>*> (branch[0])->value();
               const Type& v = static_cast<details::variable_node<Type>*>(branch[1])->ref  ();

               details::free_node(*(expr_gen.node_allocator_),branch[0]);

               if (std::equal_to<T>()(T(0),c) && (details::e_mul == operation))
                  return expr_gen(T(0));
               else if (std::equal_to<T>()(T(0),c) && (details::e_div == operation))
                  return expr_gen(T(0));
               else if (std::equal_to<T>()(T(0),c) && (details::e_add == operation))
                  return static_cast<details::variable_node<Type>*>(branch[1]);
               else if (std::equal_to<T>()(T(1),c) && (details::e_mul == operation))
                  return static_cast<details::variable_node<Type>*>(branch[1]);

               switch (operation)
               {
                  #define case_stmt(op0, op1)                                                      \
                  case op0 : return expr_gen.node_allocator_->                                     \
                                template allocate_cr<typename details::cov_node<Type,op1<Type> > > \
                                   (c, v);                                                         \

                  basic_opr_switch_statements
                  extended_opr_switch_statements
                  #undef case_stmt
                  default : return error_node();
               }
            }
         };

         struct synthesize_voc_expression
         {
            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               const Type& v = static_cast<details::variable_node<Type>*>(branch[0])->ref  ();
               const Type  c = static_cast<details::literal_node<Type>*> (branch[1])->value();

               details::free_node(*(expr_gen.node_allocator_), branch[1]);

               if (expr_gen.cardinal_pow_optimisable(operation,c))
               {
                  if (std::equal_to<T>()(T(1),c))
                     return branch[0];
                  else
                     return expr_gen.cardinal_pow_optimisation(v,c);
               }
               else if (std::equal_to<T>()(T(0),c) && (details::e_mul == operation))
                  return expr_gen(T(0));
               else if (std::equal_to<T>()(T(0),c) && (details::e_div == operation))
                  return expr_gen(std::numeric_limits<T>::quiet_NaN());
               else if (std::equal_to<T>()(T(0),c) && (details::e_add == operation))
                  return static_cast<details::variable_node<Type>*>(branch[0]);
               else if (std::equal_to<T>()(T(1),c) && (details::e_mul == operation))
                  return static_cast<details::variable_node<Type>*>(branch[0]);
               else if (std::equal_to<T>()(T(1),c) && (details::e_div == operation))
                  return static_cast<details::variable_node<Type>*>(branch[0]);

               switch (operation)
               {
                  #define case_stmt(op0, op1)                                                      \
                  case op0 : return expr_gen.node_allocator_->                                     \
                                template allocate_rc<typename details::voc_node<Type,op1<Type> > > \
                                   (v, c);                                                         \

                  basic_opr_switch_statements
                  extended_opr_switch_statements
                  #undef case_stmt
                  default : return error_node();
               }
            }
         };

         struct synthesize_sf3ext_expression
         {
            template <typename T0, typename T1, typename T2>
            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& sf3opr,
                                                      T0 t0, T1 t1, T2 t2)
            {
               switch (sf3opr)
               {
                  #define case_stmt(op)                                                                              \
                  case details::e_sf##op : return details::T0oT1oT2_sf3ext<T,T0,T1,T2,details::sf##op##_op<Type> >:: \
                                allocate(*(expr_gen.node_allocator_), t0, t1, t2);                                   \

                  case_stmt(00) case_stmt(01) case_stmt(02) case_stmt(03)
                  case_stmt(04) case_stmt(05) case_stmt(06) case_stmt(07)
                  case_stmt(08) case_stmt(09) case_stmt(10) case_stmt(11)
                  case_stmt(12) case_stmt(13) case_stmt(14) case_stmt(15)
                  case_stmt(16) case_stmt(17) case_stmt(18) case_stmt(19)
                  case_stmt(20) case_stmt(21) case_stmt(22) case_stmt(23)
                  case_stmt(24) case_stmt(25) case_stmt(26) case_stmt(27)
                  case_stmt(28) case_stmt(29) case_stmt(30)
                  #undef case_stmt
                  default : return error_node();
               }
            }

            template <typename T0, typename T1, typename T2>
            static inline bool compile(expression_generator<Type>& expr_gen, const std::string& id,
                                       T0 t0, T1 t1, T2 t2,
                                       expression_node_ptr& result)
            {
               details::operator_type sf3opr;

               if (!expr_gen.sf3_optimisable(id,sf3opr))
                  return false;
               else
                  result = synthesize_sf3ext_expression::template process<T0, T1, T2>
                              (expr_gen, sf3opr, t0, t1, t2);

               return true;
            }
         };

         struct synthesize_sf4ext_expression
         {
            template <typename T0, typename T1, typename T2, typename T3>
            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& sf4opr,
                                                      T0 t0, T1 t1, T2 t2, T3 t3)
            {
               switch (sf4opr)
               {
                  #define case_stmt0(op)                                                                                      \
                  case details::e_sf##op : return details::T0oT1oT2oT3_sf4ext<Type,T0,T1,T2,T3,details::sf##op##_op<Type> >:: \
                                allocate(*(expr_gen.node_allocator_), t0, t1, t2, t3);                                        \

                  #define case_stmt1(op)                                                                                             \
                  case details::e_sf4ext##op : return details::T0oT1oT2oT3_sf4ext<Type,T0,T1,T2,T3,details::sfext##op##_op<Type> >:: \
                                allocate(*(expr_gen.node_allocator_), t0, t1, t2, t3);                                               \

                  case_stmt0(48) case_stmt0(49) case_stmt0(50) case_stmt0(51)
                  case_stmt0(52) case_stmt0(53) case_stmt0(54) case_stmt0(55)
                  case_stmt0(56) case_stmt0(57) case_stmt0(58) case_stmt0(59)
                  case_stmt0(60) case_stmt0(61) case_stmt0(62) case_stmt0(63)
                  case_stmt0(64) case_stmt0(65) case_stmt0(66) case_stmt0(67)
                  case_stmt0(68) case_stmt0(69) case_stmt0(70) case_stmt0(71)
                  case_stmt0(72) case_stmt0(73) case_stmt0(74) case_stmt0(75)
                  case_stmt0(76) case_stmt0(77) case_stmt0(78) case_stmt0(79)
                  case_stmt0(80) case_stmt0(81) case_stmt0(82) case_stmt0(83)

                  case_stmt1(00) case_stmt1(01) case_stmt1(02) case_stmt1(03)
                  case_stmt1(04) case_stmt1(05) case_stmt1(06) case_stmt1(07)
                  case_stmt1(08) case_stmt1(09) case_stmt1(10) case_stmt1(11)
                  case_stmt1(12) case_stmt1(13) case_stmt1(14) case_stmt1(15)
                  case_stmt1(16) case_stmt1(17) case_stmt1(18) case_stmt1(19)
                  case_stmt1(20) case_stmt1(21) case_stmt1(22) case_stmt1(23)
                  case_stmt1(24) case_stmt1(25) case_stmt1(26) case_stmt1(27)
                  case_stmt1(28) case_stmt1(29) case_stmt1(30) case_stmt1(31)
                  case_stmt1(32) case_stmt1(33) case_stmt1(34) case_stmt1(35)
                  case_stmt1(36) case_stmt1(37) case_stmt1(38) case_stmt1(39)
                  case_stmt1(40) case_stmt1(41) case_stmt1(42) case_stmt1(43)
                  case_stmt1(44) case_stmt1(45) case_stmt1(46) case_stmt1(47)
                  case_stmt1(48) case_stmt1(49) case_stmt1(50) case_stmt1(51)
                  case_stmt1(52) case_stmt1(53) case_stmt1(54) case_stmt1(55)
                  case_stmt1(56) case_stmt1(57) case_stmt1(58) case_stmt1(59)
                  case_stmt1(60) case_stmt1(61)

                  #undef case_stmt0
                  #undef case_stmt1
                  default : return error_node();
               }
            }

            template <typename T0, typename T1, typename T2, typename T3>
            static inline bool compile(expression_generator<Type>& expr_gen, const std::string& id,
                                       T0 t0, T1 t1, T2 t2, T3 t3,
                                       expression_node_ptr& result)
            {
               details::operator_type sf4opr;

               if (!expr_gen.sf4_optimisable(id,sf4opr))
                  return false;
               else
                  result = synthesize_sf4ext_expression::template process<T0, T1, T2, T3>
                              (expr_gen, sf4opr, t0, t1, t2, t3);

               return true;
            }

            // T o (sf3ext)
            template <typename ExternalType>
            static inline bool compile_right(expression_generator<Type>& expr_gen,
                                             ExternalType t,
                                             const details::operator_type& operation,
                                             expression_node_ptr& sf3node,
                                             expression_node_ptr& result)
            {
               if (!details::is_sf3ext_node(sf3node))
                  return false;

               typedef details::T0oT1oT2_base_node<Type>* sf3ext_base_ptr;

               sf3ext_base_ptr n = static_cast<sf3ext_base_ptr>(sf3node);
               const std::string id = "t" + expr_gen.to_str(operation) + "(" + n->type_id() + ")";

               switch (n->type())
               {
                  case details::expression_node<Type>::e_covoc : return compile_right_impl
                                                                    <typename covoc_t::sf3_type_node,ExternalType, ctype, vtype, ctype>
                                                                       (expr_gen, id, t, sf3node, result);

                  case details::expression_node<Type>::e_covov : return compile_right_impl
                                                                    <typename covov_t::sf3_type_node,ExternalType, ctype, vtype, vtype>
                                                                       (expr_gen, id, t, sf3node, result);

                  case details::expression_node<Type>::e_vocov : return compile_right_impl
                                                                    <typename vocov_t::sf3_type_node,ExternalType, vtype, ctype, vtype>
                                                                       (expr_gen, id, t, sf3node, result);

                  case details::expression_node<Type>::e_vovoc : return compile_right_impl
                                                                    <typename vovoc_t::sf3_type_node,ExternalType, vtype, vtype, ctype>
                                                                       (expr_gen, id, t, sf3node, result);

                  case details::expression_node<Type>::e_vovov : return compile_right_impl
                                                                    <typename vovov_t::sf3_type_node,ExternalType, vtype, vtype, vtype>
                                                                       (expr_gen, id, t, sf3node, result);

                  default                                      : return false;
               }
            }

            // (sf3ext) o T
            template <typename ExternalType>
            static inline bool compile_left(expression_generator<Type>& expr_gen,
                                            ExternalType t,
                                            const details::operator_type& operation,
                                            expression_node_ptr& sf3node,
                                            expression_node_ptr& result)
            {
               if (!details::is_sf3ext_node(sf3node))
                  return false;

               typedef details::T0oT1oT2_base_node<Type>* sf3ext_base_ptr;

               sf3ext_base_ptr n = static_cast<sf3ext_base_ptr>(sf3node);

               const std::string id = "(" + n->type_id() + ")" + expr_gen.to_str(operation) + "t";

               switch (n->type())
               {
                  case details::expression_node<Type>::e_covoc : return compile_left_impl
                                                                    <typename covoc_t::sf3_type_node,ExternalType, ctype, vtype, ctype>
                                                                       (expr_gen, id, t, sf3node, result);

                  case details::expression_node<Type>::e_covov : return compile_left_impl
                                                                    <typename covov_t::sf3_type_node,ExternalType, ctype, vtype, vtype>
                                                                       (expr_gen, id, t, sf3node, result);

                  case details::expression_node<Type>::e_vocov : return compile_left_impl
                                                                    <typename vocov_t::sf3_type_node,ExternalType, vtype, ctype, vtype>
                                                                       (expr_gen, id, t, sf3node, result);

                  case details::expression_node<Type>::e_vovoc : return compile_left_impl
                                                                    <typename vovoc_t::sf3_type_node,ExternalType, vtype, vtype, ctype>
                                                                       (expr_gen, id, t, sf3node, result);

                  case details::expression_node<Type>::e_vovov : return compile_left_impl
                                                                    <typename vovov_t::sf3_type_node,ExternalType, vtype, vtype, vtype>
                                                                       (expr_gen, id, t, sf3node, result);

                  default                                      : return false;
               }
            }

            template <typename SF3TypeNode, typename ExternalType, typename T0, typename T1, typename T2>
            static inline bool compile_right_impl(expression_generator<Type>& expr_gen,
                                                  const std::string& id,
                                                  ExternalType t,
                                                  expression_node_ptr& node,
                                                  expression_node_ptr& result)
            {
               SF3TypeNode* n = dynamic_cast<SF3TypeNode*>(node);

               if (n)
               {
                  T0 t0 = n->t0();
                  T1 t1 = n->t1();
                  T2 t2 = n->t2();

                  return synthesize_sf4ext_expression::template compile<ExternalType, T0, T1, T2>
                            (expr_gen, id, t, t0, t1, t2, result);
               }
               else
                  return false;
            }

            template <typename SF3TypeNode, typename ExternalType, typename T0, typename T1, typename T2>
            static inline bool compile_left_impl(expression_generator<Type>& expr_gen,
                                                 const std::string& id,
                                                 ExternalType t,
                                                 expression_node_ptr& node,
                                                 expression_node_ptr& result)
            {
               SF3TypeNode* n = dynamic_cast<SF3TypeNode*>(node);

               if (n)
               {
                  T0 t0 = n->t0();
                  T1 t1 = n->t1();
                  T2 t2 = n->t2();

                  return synthesize_sf4ext_expression::template compile<T0, T1, T2, ExternalType>
                            (expr_gen, id, t0, t1, t2, t, result);
               }
               else
                  return false;
            }
         };

         struct synthesize_vovov_expression0
         {
            typedef typename vovov_t::type0 node_type;
            typedef typename vovov_t::sf3_type sf3_type;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // (v0 o0 v1) o1 (v2)
               const details::vov_base_node<Type>* vov = static_cast<details::vov_base_node<Type>*>(branch[0]);
               const Type& v0 = vov->v0();
               const Type& v1 = vov->v1();
               const Type& v2 = static_cast<details::variable_node<Type>*>(branch[1])->ref();
               const details::operator_type o0 = vov->operation();
               const details::operator_type o1 = operation;

               details::free_node(*(expr_gen.node_allocator_),branch[0]);

               expression_node_ptr result = error_node();

               if (expr_gen.parser_->settings_.strength_reduction_enabled())
               {
                  // (v0 / v1) / v2 --> (vovov) v0 / (v1 * v2)
                  if ((details::e_div == o0) && (details::e_div == o1))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<vtype, vtype, vtype>(expr_gen, "t/(t*t)", v0, v1, v2, result);

                     exprtk_debug(("(v0 / v1) / v2 --> (vovov) v0 / (v1 * v2)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
               }

               const bool synthesis_result =
                  synthesize_sf3ext_expression::template compile<vtype, vtype, vtype>
                     (expr_gen, id(expr_gen, o0, o1), v0, v1, v2, result);

               if (synthesis_result)
                  return result;

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = reinterpret_cast<binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator_), v0, v1, v2, f0, f1);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1)
            {
               return details::build_string()
                         << "(t" << expr_gen.to_str(o0)
                         << "t)" << expr_gen.to_str(o1)
                         << "t";
            }
         };

         struct synthesize_vovov_expression1
         {
            typedef typename vovov_t::type1 node_type;
            typedef typename vovov_t::sf3_type sf3_type;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // (v0) o0 (v1 o1 v2)
               const details::vov_base_node<Type>* vov = static_cast<details::vov_base_node<Type>*>(branch[1]);
               const Type& v0 = static_cast<details::variable_node<Type>*>(branch[0])->ref();
               const Type& v1 = vov->v0();
               const Type& v2 = vov->v1();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = vov->operation();

               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               if (expr_gen.parser_->settings_.strength_reduction_enabled())
               {
                  // v0 / (v1 / v2) --> (vovov) (v0 * v2) / v1
                  if ((details::e_div == o0) && (details::e_div == o1))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<vtype, vtype, vtype>(expr_gen, "(t*t)/t", v0, v2, v1, result);

                     exprtk_debug(("v0 / (v1 / v2) --> (vovov) (v0 * v2) / v1\n"));

                     return (synthesis_result) ? result : error_node();
                  }
               }

               const bool synthesis_result =
                  synthesize_sf3ext_expression::template compile<vtype, vtype, vtype>
                     (expr_gen, id(expr_gen, o0, o1), v0, v1, v2, result);

               if (synthesis_result)
                  return result;

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = reinterpret_cast<binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator_), v0, v1, v2, f0, f1);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1)
            {
               return details::build_string()
                         << "t"  << expr_gen.to_str(o0)
                         << "(t" << expr_gen.to_str(o1)
                         << "t)";
            }
         };

         struct synthesize_vovoc_expression0
         {
            typedef typename vovoc_t::type0 node_type;
            typedef typename vovoc_t::sf3_type sf3_type;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // (v0 o0 v1) o1 (c)
               const details::vov_base_node<Type>* vov = static_cast<details::vov_base_node<Type>*>(branch[0]);
               const Type& v0 = vov->v0();
               const Type& v1 = vov->v1();
               const Type   c = static_cast<details::literal_node<Type>*>(branch[1])->value();
               const details::operator_type o0 = vov->operation();
               const details::operator_type o1 = operation;

               details::free_node(*(expr_gen.node_allocator_),branch[0]);
               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               if (expr_gen.parser_->settings_.strength_reduction_enabled())
               {
                  // (v0 / v1) / c --> (vovoc) v0 / (v1 * c)
                  if ((details::e_div == o0) && (details::e_div == o1))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<vtype, vtype, ctype>(expr_gen, "t/(t*t)", v0, v1, c, result);

                     exprtk_debug(("(v0 / v1) / c --> (vovoc) v0 / (v1 * c)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
               }

               const bool synthesis_result =
                  synthesize_sf3ext_expression::template compile<vtype, vtype, ctype>
                     (expr_gen, id(expr_gen, o0, o1), v0, v1, c, result);

               if (synthesis_result)
                  return result;

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = reinterpret_cast<binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator_), v0, v1, c, f0, f1);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1)
            {
               return details::build_string()
                         << "(t" << expr_gen.to_str(o0)
                         << "t)" << expr_gen.to_str(o1)
                         << "t";
            }
         };

         struct synthesize_vovoc_expression1
         {
            typedef typename vovoc_t::type1 node_type;
            typedef typename vovoc_t::sf3_type sf3_type;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // (v0) o0 (v1 o1 c)
               const details::voc_base_node<Type>* voc = static_cast<const details::voc_base_node<Type>*>(branch[1]);
               const Type& v0 = static_cast<details::variable_node<Type>*>(branch[0])->ref();
               const Type& v1 = voc->v();
               const Type   c = voc->c();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = voc->operation();

               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               if (expr_gen.parser_->settings_.strength_reduction_enabled())
               {
                  // v0 / (v1 / c) --> (vocov) (v0 * c) / v1
                  if ((details::e_div == o0) && (details::e_div == o1))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<vtype, ctype, vtype>(expr_gen, "(t*t)/t", v0, c, v1, result);

                     exprtk_debug(("v0 / (v1 / c) --> (vocov) (v0 * c) / v1\n"));

                     return (synthesis_result) ? result : error_node();
                  }
               }

               const bool synthesis_result =
                  synthesize_sf3ext_expression::template compile<vtype, vtype, ctype>
                     (expr_gen, id(expr_gen, o0, o1), v0, v1, c, result);

               if (synthesis_result)
                  return result;

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = reinterpret_cast<binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator_), v0, v1, c, f0, f1);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1)
            {
               return details::build_string()
                         << "t"  << expr_gen.to_str(o0)
                         << "(t" << expr_gen.to_str(o1)
                         << "t)";
            }
         };

         struct synthesize_vocov_expression0
         {
            typedef typename vocov_t::type0 node_type;
            typedef typename vocov_t::sf3_type sf3_type;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // (v0 o0 c) o1 (v1)
               const details::voc_base_node<Type>* voc = static_cast<details::voc_base_node<Type>*>(branch[0]);
               const Type& v0 = voc->v();
               const Type   c = voc->c();
               const Type& v1 = static_cast<details::variable_node<Type>*>(branch[1])->ref();
               const details::operator_type o0 = voc->operation();
               const details::operator_type o1 = operation;

               details::free_node(*(expr_gen.node_allocator_),branch[0]);

               expression_node_ptr result = error_node();

               if (expr_gen.parser_->settings_.strength_reduction_enabled())
               {
                  // (v0 / c) / v1 --> (vovoc) v0 / (v1 * c)
                  if ((details::e_div == o0) && (details::e_div == o1))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<vtype, vtype, ctype>(expr_gen, "t/(t*t)", v0, v1, c, result);

                     exprtk_debug(("(v0 / c) / v1 --> (vovoc) v0 / (v1 * c)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
               }

               const bool synthesis_result =
                  synthesize_sf3ext_expression::template compile<vtype, ctype, vtype>
                     (expr_gen, id(expr_gen, o0, o1), v0, c, v1, result);

               if (synthesis_result)
                  return result;

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = reinterpret_cast<binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator_), v0, c, v1, f0, f1);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1)
            {
               return details::build_string()
                         << "(t" << expr_gen.to_str(o0)
                         << "t)" << expr_gen.to_str(o1)
                         << "t";
            }
         };

         struct synthesize_vocov_expression1
         {
            typedef typename vocov_t::type1 node_type;
            typedef typename vocov_t::sf3_type sf3_type;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // (v0) o0 (c o1 v1)
               const details::cov_base_node<Type>* cov = static_cast<details::cov_base_node<Type>*>(branch[1]);
               const Type& v0 = static_cast<details::variable_node<Type>*>(branch[0])->ref();
               const Type   c = cov->c();
               const Type& v1 = cov->v();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = cov->operation();

               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               if (expr_gen.parser_->settings_.strength_reduction_enabled())
               {
                  // v0 / (c / v1) --> (vovoc) (v0 * v1) / c
                  if ((details::e_div == o0) && (details::e_div == o1))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<vtype, vtype, ctype>(expr_gen, "(t*t)/t", v0, v1, c, result);

                     exprtk_debug(("v0 / (c / v1) --> (vovoc) (v0 * v1) / c\n"));

                     return (synthesis_result) ? result : error_node();
                  }
               }

               const bool synthesis_result =
                  synthesize_sf3ext_expression::template compile<vtype, ctype, vtype>
                     (expr_gen, id(expr_gen, o0, o1), v0, c, v1, result);

               if (synthesis_result)
                  return result;

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = reinterpret_cast<binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator_), v0, c, v1, f0, f1);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1)
            {
               return details::build_string()
                         << "t"  << expr_gen.to_str(o0)
                         << "(t" << expr_gen.to_str(o1)
                         << "t)";
            }
         };

         struct synthesize_covov_expression0
         {
            typedef typename covov_t::type0 node_type;
            typedef typename covov_t::sf3_type sf3_type;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // (c o0 v0) o1 (v1)
               const details::cov_base_node<Type>* cov = static_cast<details::cov_base_node<Type>*>(branch[0]);
               const Type   c = cov->c();
               const Type& v0 = cov->v();
               const Type& v1 = static_cast<details::variable_node<Type>*>(branch[1])->ref();
               const details::operator_type o0 = cov->operation();
               const details::operator_type o1 = operation;

               details::free_node(*(expr_gen.node_allocator_),branch[0]);

               expression_node_ptr result = error_node();

               if (expr_gen.parser_->settings_.strength_reduction_enabled())
               {
                  // (c / v0) / v1 --> (covov) c / (v0 * v1)
                  if ((details::e_div == o0) && (details::e_div == o1))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, "t/(t*t)", c, v0, v1, result);

                     exprtk_debug(("(c / v0) / v1 --> (covov) c / (v0 * v1)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
               }

               const bool synthesis_result =
                  synthesize_sf3ext_expression::template compile<ctype, vtype, vtype>
                     (expr_gen, id(expr_gen, o0, o1), c, v0, v1, result);

               if (synthesis_result)
                  return result;

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = reinterpret_cast<binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator_), c, v0, v1, f0, f1);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1)
            {
               return details::build_string()
                         << "(t" << expr_gen.to_str(o0)
                         << "t)" << expr_gen.to_str(o1)
                         << "t";
            }
         };

         struct synthesize_covov_expression1
         {
            typedef typename covov_t::type1 node_type;
            typedef typename covov_t::sf3_type sf3_type;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // (c) o0 (v0 o1 v1)
               const details::vov_base_node<Type>* vov = static_cast<details::vov_base_node<Type>*>(branch[1]);
               const Type   c = static_cast<details::literal_node<Type>*>(branch[0])->value();
               const Type& v0 = vov->v0();
               const Type& v1 = vov->v1();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = vov->operation();

               details::free_node(*(expr_gen.node_allocator_),branch[0]);
               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               if (expr_gen.parser_->settings_.strength_reduction_enabled())
               {
                  // c / (v0 / v1) --> (covov) (c * v1) / v0
                  if ((details::e_div == o0) && (details::e_div == o1))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, "(t*t)/t", c, v1, v0, result);

                     exprtk_debug(("c / (v0 / v1) --> (covov) (c * v1) / v0\n"));

                     return (synthesis_result) ? result : error_node();
                  }
               }

               const bool synthesis_result =
                  synthesize_sf3ext_expression::template compile<ctype, vtype, vtype>
                     (expr_gen, id(expr_gen, o0, o1), c, v0, v1, result);

               if (synthesis_result)
                  return result;

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = reinterpret_cast<binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator_), c, v0, v1, f0, f1);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1)
            {
               return details::build_string()
                         << "t"  << expr_gen.to_str(o0)
                         << "(t" << expr_gen.to_str(o1)
                         << "t)";
            }
         };

         struct synthesize_covoc_expression0
         {
            typedef typename covoc_t::type0 node_type;
            typedef typename covoc_t::sf3_type sf3_type;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // (c0 o0 v) o1 (c1)
               const details::cov_base_node<Type>* cov = static_cast<details::cov_base_node<Type>*>(branch[0]);
               const Type  c0 = cov->c();
               const Type&  v = cov->v();
               const Type  c1 = static_cast<details::literal_node<Type>*>(branch[1])->value();
               const details::operator_type o0 = cov->operation();
               const details::operator_type o1 = operation;

               details::free_node(*(expr_gen.node_allocator_),branch[0]);
               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               if (expr_gen.parser_->settings_.strength_reduction_enabled())
               {
                  // (c0 + v) + c1 --> (cov) (c0 + c1) + v
                  if ((details::e_add == o0) && (details::e_add == o1))
                  {
                     exprtk_debug(("(c0 + v) + c1 --> (cov) (c0 + c1) + v\n"));

                     return expr_gen.node_allocator_->
                               template allocate_cr<typename details::cov_node<Type,details::add_op<Type> > >(c0 + c1, v);
                  }
                  // (c0 + v) - c1 --> (cov) (c0 - c1) + v
                  else if ((details::e_add == o0) && (details::e_sub == o1))
                  {
                     exprtk_debug(("(c0 + v) - c1 --> (cov) (c0 - c1) + v\n"));

                     return expr_gen.node_allocator_->
                               template allocate_cr<typename details::cov_node<Type,details::add_op<Type> > >(c0 - c1, v);
                  }
                  // (c0 - v) + c1 --> (cov) (c0 + c1) - v
                  else if ((details::e_sub == o0) && (details::e_add == o1))
                  {
                     exprtk_debug(("(c0 - v) + c1 --> (cov) (c0 + c1) - v\n"));

                     return expr_gen.node_allocator_->
                               template allocate_cr<typename details::cov_node<Type,details::sub_op<Type> > >(c0 + c1, v);
                  }
                  // (c0 - v) - c1 --> (cov) (c0 - c1) - v
                  else if ((details::e_sub == o0) && (details::e_sub == o1))
                  {
                     exprtk_debug(("(c0 - v) - c1 --> (cov) (c0 - c1) - v\n"));

                     return expr_gen.node_allocator_->
                               template allocate_cr<typename details::cov_node<Type,details::sub_op<Type> > >(c0 - c1, v);
                  }
                  // (c0 * v) * c1 --> (cov) (c0 * c1) * v
                  else if ((details::e_mul == o0) && (details::e_mul == o1))
                  {
                     exprtk_debug(("(c0 * v) * c1 --> (cov) (c0 * c1) * v\n"));

                     return expr_gen.node_allocator_->
                               template allocate_cr<typename details::cov_node<Type,details::mul_op<Type> > >(c0 * c1, v);
                  }
                  // (c0 * v) / c1 --> (cov) (c0 / c1) * v
                  else if ((details::e_mul == o0) && (details::e_div == o1))
                  {
                     exprtk_debug(("(c0 * v) / c1 --> (cov) (c0 / c1) * v\n"));

                     return expr_gen.node_allocator_->
                               template allocate_cr<typename details::cov_node<Type,details::mul_op<Type> > >(c0 / c1, v);
                  }
                  // (c0 / v) * c1 --> (cov) (c0 * c1) / v
                  else if ((details::e_div == o0) && (details::e_mul == o1))
                  {
                     exprtk_debug(("(c0 / v) * c1 --> (cov) (c0 * c1) / v\n"));

                     return expr_gen.node_allocator_->
                               template allocate_cr<typename details::cov_node<Type,details::div_op<Type> > >(c0 * c1, v);
                  }
                  // (c0 / v) / c1 --> (cov) (c0 / c1) / v
                  else if ((details::e_div == o0) && (details::e_div == o1))
                  {
                     exprtk_debug(("(c0 / v) / c1 --> (cov) (c0 / c1) / v\n"));

                     return expr_gen.node_allocator_->
                               template allocate_cr<typename details::cov_node<Type,details::div_op<Type> > >(c0 / c1, v);
                  }
               }

               const bool synthesis_result =
                  synthesize_sf3ext_expression::template compile<ctype, vtype, ctype>
                     (expr_gen, id(expr_gen, o0, o1), c0, v, c1, result);

               if (synthesis_result)
                  return result;

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = reinterpret_cast<binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator_), c0, v, c1, f0, f1);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1)
            {
               return details::build_string()
                         << "(t" << expr_gen.to_str(o0)
                         << "t)" << expr_gen.to_str(o1)
                         << "t";
            }
         };

         struct synthesize_covoc_expression1
         {
            typedef typename covoc_t::type1 node_type;
            typedef typename covoc_t::sf3_type sf3_type;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // (c0) o0 (v o1 c1)
               const details::voc_base_node<Type>* voc = static_cast<details::voc_base_node<Type>*>(branch[1]);
               const Type  c0 = static_cast<details::literal_node<Type>*>(branch[0])->value();
               const Type&  v = voc->v();
               const Type  c1 = voc->c();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = voc->operation();

               details::free_node(*(expr_gen.node_allocator_),branch[0]);
               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               if (expr_gen.parser_->settings_.strength_reduction_enabled())
               {
                  // (c0) + (v + c1) --> (cov) (c0 + c1) + v
                  if ((details::e_add == o0) && (details::e_add == o1))
                  {
                     exprtk_debug(("(c0) + (v + c1) --> (cov) (c0 + c1) + v\n"));

                     return expr_gen.node_allocator_->
                               template allocate_cr<typename details::cov_node<Type,details::add_op<Type> > >(c0 + c1, v);
                  }
                  // (c0) + (v - c1) --> (cov) (c0 - c1) + v
                  else if ((details::e_add == o0) && (details::e_sub == o1))
                  {
                     exprtk_debug(("(c0) + (v - c1) --> (cov) (c0 - c1) + v\n"));

                     return expr_gen.node_allocator_->
                               template allocate_cr<typename details::cov_node<Type,details::add_op<Type> > >(c0 - c1, v);
                  }
                  // (c0) - (v + c1) --> (cov) (c0 - c1) - v
                  else if ((details::e_sub == o0) && (details::e_add == o1))
                  {
                     exprtk_debug(("(c0) - (v + c1) --> (cov) (c0 - c1) - v\n"));

                     return expr_gen.node_allocator_->
                               template allocate_cr<typename details::cov_node<Type,details::sub_op<Type> > >(c0 - c1, v);
                  }
                  // (c0) - (v - c1) --> (cov) (c0 + c1) - v
                  else if ((details::e_sub == o0) && (details::e_sub == o1))
                  {
                     exprtk_debug(("(c0) - (v - c1) --> (cov) (c0 + c1) - v\n"));

                     return expr_gen.node_allocator_->
                               template allocate_cr<typename details::cov_node<Type,details::sub_op<Type> > >(c0 + c1, v);
                  }
                  // (c0) * (v * c1) --> (voc) v * (c0 * c1)
                  else if ((details::e_mul == o0) && (details::e_mul == o1))
                  {
                     exprtk_debug(("(c0) * (v * c1) --> (voc) v * (c0 * c1)\n"));

                     return expr_gen.node_allocator_->
                               template allocate_cr<typename details::cov_node<Type,details::mul_op<Type> > >(c0 * c1, v);
                  }
                  // (c0) * (v / c1) --> (cov) (c0 / c1) * v
                  else if ((details::e_mul == o0) && (details::e_div == o1))
                  {
                     exprtk_debug(("(c0) * (v / c1) --> (cov) (c0 / c1) * v\n"));

                     return expr_gen.node_allocator_->
                               template allocate_cr<typename details::cov_node<Type,details::mul_op<Type> > >(c0 / c1, v);
                  }
                  // (c0) / (v * c1) --> (cov) (c0 / c1) / v
                  else if ((details::e_div == o0) && (details::e_mul == o1))
                  {
                     exprtk_debug(("(c0) / (v * c1) --> (cov) (c0 / c1) / v\n"));

                     return expr_gen.node_allocator_->
                               template allocate_cr<typename details::cov_node<Type,details::div_op<Type> > >(c0 / c1, v);
                  }
                  // (c0) / (v / c1) --> (cov) (c0 * c1) / v
                  else if ((details::e_div == o0) && (details::e_div == o1))
                  {
                     exprtk_debug(("(c0) / (v / c1) --> (cov) (c0 * c1) / v\n"));

                     return expr_gen.node_allocator_->
                               template allocate_cr<typename details::cov_node<Type,details::div_op<Type> > >(c0 * c1, v);
                  }
               }

               const bool synthesis_result =
                  synthesize_sf3ext_expression::template compile<ctype, vtype, ctype>
                     (expr_gen, id(expr_gen, o0, o1), c0, v, c1, result);

               if (synthesis_result)
                  return result;

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = reinterpret_cast<binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator_), c0, v, c1, f0, f1);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1)
            {
               return details::build_string()
                         << "t"  << expr_gen.to_str(o0)
                         << "(t" << expr_gen.to_str(o1)
                         << "t)";
            }
         };

         struct synthesize_cocov_expression0
         {
            typedef typename cocov_t::type0 node_type;
            static inline expression_node_ptr process(expression_generator<Type>&,
                                                      const details::operator_type&,
                                                      expression_node_ptr (&)[2])
            {
               // (c0 o0 c1) o1 (v) - Not possible.
               return error_node();
            }
         };

         struct synthesize_cocov_expression1
         {
            typedef typename cocov_t::type1 node_type;
            typedef typename cocov_t::sf3_type sf3_type;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // (c0) o0 (c1 o1 v)
               const details::cov_base_node<Type>* cov = static_cast<details::cov_base_node<Type>*>(branch[1]);
               const Type  c0 = static_cast<details::literal_node<Type>*>(branch[0])->value();
               const Type  c1 = cov->c();
               const Type&  v = cov->v();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = cov->operation();

               details::free_node(*(expr_gen.node_allocator_),branch[0]);
               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               if (expr_gen.parser_->settings_.strength_reduction_enabled())
               {
                  // (c0) + (c1 + v) --> (cov) (c0 + c1) + v
                  if ((details::e_add == o0) && (details::e_add == o1))
                  {
                     exprtk_debug(("(c0) + (c1 + v) --> (cov) (c0 + c1) + v\n"));

                     return expr_gen.node_allocator_->
                               template allocate_cr<typename details::cov_node<Type,details::add_op<Type> > >(c0 + c1, v);
                  }
                  // (c0) + (c1 - v) --> (cov) (c0 + c1) - v
                  else if ((details::e_add == o0) && (details::e_sub == o1))
                  {
                     exprtk_debug(("(c0) + (c1 - v) --> (cov) (c0 + c1) - v\n"));

                     return expr_gen.node_allocator_->
                               template allocate_cr<typename details::cov_node<Type,details::sub_op<Type> > >(c0 + c1, v);
                  }
                  // (c0) - (c1 + v) --> (cov) (c0 - c1) - v
                  else if ((details::e_sub == o0) && (details::e_add == o1))
                  {
                     exprtk_debug(("(c0) - (c1 + v) --> (cov) (c0 - c1) - v\n"));

                     return expr_gen.node_allocator_->
                               template allocate_cr<typename details::cov_node<Type,details::sub_op<Type> > >(c0 - c1, v);
                  }
                  // (c0) - (c1 - v) --> (cov) (c0 - c1) + v
                  else if ((details::e_sub == o0) && (details::e_sub == o1))
                  {
                     exprtk_debug(("(c0) - (c1 - v) --> (cov) (c0 - c1) + v\n"));

                     return expr_gen.node_allocator_->
                               template allocate_cr<typename details::cov_node<Type,details::add_op<Type> > >(c0 - c1, v);
                  }
                  // (c0) * (c1 * v) --> (cov) (c0 * c1) * v
                  else if ((details::e_mul == o0) && (details::e_mul == o1))
                  {
                     exprtk_debug(("(c0) * (c1 * v) --> (cov) (c0 * c1) * v\n"));

                     return expr_gen.node_allocator_->
                               template allocate_cr<typename details::cov_node<Type,details::mul_op<Type> > >(c0 * c1, v);
                  }
                  // (c0) * (c1 / v) --> (cov) (c0 * c1) / v
                  else if ((details::e_mul == o0) && (details::e_div == o1))
                  {
                     exprtk_debug(("(c0) * (c1 / v) --> (cov) (c0 * c1) / v\n"));

                     return expr_gen.node_allocator_->
                               template allocate_cr<typename details::cov_node<Type,details::div_op<Type> > >(c0 * c1, v);
                  }
                  // (c0) / (c1 * v) --> (cov) (c0 / c1) / v
                  else if ((details::e_div == o0) && (details::e_mul == o1))
                  {
                     exprtk_debug(("(c0) / (c1 * v) --> (cov) (c0 / c1) / v\n"));

                     return expr_gen.node_allocator_->
                               template allocate_cr<typename details::cov_node<Type,details::div_op<Type> > >(c0 / c1, v);
                  }
                  // (c0) / (c1 / v) --> (cov) (c0 / c1) * v
                  else if ((details::e_div == o0) && (details::e_div == o1))
                  {
                     exprtk_debug(("(c0) / (c1 / v) --> (cov) (c0 / c1) * v\n"));

                     return expr_gen.node_allocator_->
                               template allocate_cr<typename details::cov_node<Type,details::mul_op<Type> > >(c0 / c1, v);
                  }
               }

               const bool synthesis_result =
                  synthesize_sf3ext_expression::template compile<ctype, ctype, vtype>
                     (expr_gen, id(expr_gen, o0, o1), c0, c1, v, result);

               if (synthesis_result)
                  return result;

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = reinterpret_cast<binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator_), c0, c1, v, f0, f1);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1)
            {
               return details::build_string()
                         << "t"  << expr_gen.to_str(o0)
                         << "(t" << expr_gen.to_str(o1)
                         << "t)";
            }
         };

         struct synthesize_vococ_expression0
         {
            typedef typename vococ_t::type0 node_type;
            typedef typename vococ_t::sf3_type sf3_type;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // (v o0 c0) o1 (c1)
               const details::voc_base_node<Type>* voc = static_cast<details::voc_base_node<Type>*>(branch[0]);
               const Type&  v = voc->v();
               const Type& c0 = voc->c();
               const Type& c1 = static_cast<details::literal_node<Type>*>(branch[1])->value();
               const details::operator_type o0 = voc->operation();
               const details::operator_type o1 = operation;

               details::free_node(*(expr_gen.node_allocator_),branch[0]);
               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               if (expr_gen.parser_->settings_.strength_reduction_enabled())
               {
                  // (v + c0) + c1 --> (voc) v + (c0 + c1)
                  if ((details::e_add == o0) && (details::e_add == o1))
                  {
                     exprtk_debug(("(v + c0) + c1 --> (voc) v + (c0 + c1)\n"));

                     return expr_gen.node_allocator_->
                               template allocate_rc<typename details::voc_node<Type,details::add_op<Type> > >(v, c0 + c1);
                  }
                  // (v + c0) - c1 --> (voc) v + (c0 - c1)
                  else if ((details::e_add == o0) && (details::e_sub == o1))
                  {
                     exprtk_debug(("(v + c0) - c1 --> (voc) v + (c0 - c1)\n"));

                     return expr_gen.node_allocator_->
                               template allocate_rc<typename details::voc_node<Type,details::add_op<Type> > >(v, c0 - c1);
                  }
                  // (v - c0) + c1 --> (voc) v - (c0 + c1)
                  else if ((details::e_sub == o0) && (details::e_add == o1))
                  {
                     exprtk_debug(("(v - c0) + c1 --> (voc) v - (c0 + c1)\n"));

                     return expr_gen.node_allocator_->
                               template allocate_rc<typename details::voc_node<Type,details::add_op<Type> > >(v, c1 - c0);
                  }
                  // (v - c0) - c1 --> (voc) v - (c0 + c1)
                  else if ((details::e_sub == o0) && (details::e_sub == o1))
                  {
                     exprtk_debug(("(v - c0) - c1 --> (voc) v - (c0 + c1)\n"));

                     return expr_gen.node_allocator_->
                               template allocate_rc<typename details::voc_node<Type,details::sub_op<Type> > >(v, c0 + c1);
                  }
                  // (v * c0) * c1 --> (voc) v * (c0 * c1)
                  else if ((details::e_mul == o0) && (details::e_mul == o1))
                  {
                     exprtk_debug(("(v * c0) * c1 --> (voc) v * (c0 * c1)\n"));

                     return expr_gen.node_allocator_->
                               template allocate_rc<typename details::voc_node<Type,details::mul_op<Type> > >(v, c0 * c1);
                  }
                  // (v * c0) / c1 --> (voc) v * (c0 / c1)
                  else if ((details::e_mul == o0) && (details::e_div == o1))
                  {
                     exprtk_debug(("(v * c0) / c1 --> (voc) v * (c0 / c1)\n"));

                     return expr_gen.node_allocator_->
                               template allocate_rc<typename details::voc_node<Type,details::mul_op<Type> > >(v, c0 / c1);
                  }
                  // (v / c0) * c1 --> (voc) v * (c1 / c0)
                  else if ((details::e_div == o0) && (details::e_mul == o1))
                  {
                     exprtk_debug(("(v / c0) * c1 --> (voc) v * (c1 / c0)\n"));

                     return expr_gen.node_allocator_->
                               template allocate_rc<typename details::voc_node<Type,details::mul_op<Type> > >(v, c1 / c0);
                  }
                  // (v / c0) / c1 --> (voc) v / (c0 * c1)
                  else if ((details::e_div == o0) && (details::e_div == o1))
                  {
                     exprtk_debug(("(v / c0) / c1 --> (voc) v / (c0 * c1)\n"));

                     return expr_gen.node_allocator_->
                               template allocate_rc<typename details::voc_node<Type,details::div_op<Type> > >(v, c0 * c1);
                  }
                  // (v ^ c0) ^ c1 --> (voc) v ^ (c0 * c1)
                  else if ((details::e_pow == o0) && (details::e_pow == o1))
                  {
                     exprtk_debug(("(v ^ c0) ^ c1 --> (voc) v ^ (c0 * c1)\n"));

                     return expr_gen.node_allocator_->
                               template allocate_rc<typename details::voc_node<Type,details::pow_op<Type> > >(v, c0 * c1);
                  }
               }

               const bool synthesis_result =
                  synthesize_sf3ext_expression::template compile<vtype, ctype, ctype>
                     (expr_gen, id(expr_gen, o0, o1), v, c0, c1, result);

               if (synthesis_result)
                  return result;

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = reinterpret_cast<binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator_), v, c0, c1, f0, f1);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1)
            {
               return details::build_string()
                         << "(t" << expr_gen.to_str(o0)
                         << "t)" << expr_gen.to_str(o1)
                         << "t";
            }
         };

         struct synthesize_vococ_expression1
         {
            typedef typename vococ_t::type0 node_type;

            static inline expression_node_ptr process(expression_generator<Type>&,
                                                      const details::operator_type&,
                                                      expression_node_ptr (&)[2])
            {
               // (v) o0 (c0 o1 c1) - Not possible.
               exprtk_debug(("(v) o0 (c0 o1 c1) - Not possible.\n"));
               return error_node();
            }
         };

         struct synthesize_vovovov_expression0
         {
            typedef typename vovovov_t::type0 node_type;
            typedef typename vovovov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // (v0 o0 v1) o1 (v2 o2 v3)
               const details::vov_base_node<Type>* vov0 = static_cast<details::vov_base_node<Type>*>(branch[0]);
               const details::vov_base_node<Type>* vov1 = static_cast<details::vov_base_node<Type>*>(branch[1]);
               const Type& v0 = vov0->v0();
               const Type& v1 = vov0->v1();
               const Type& v2 = vov1->v0();
               const Type& v3 = vov1->v1();
               const details::operator_type o0 = vov0->operation();
               const details::operator_type o1 = operation;
               const details::operator_type o2 = vov1->operation();

               details::free_node(*(expr_gen.node_allocator_),branch[0]);
               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               if (expr_gen.parser_->settings_.strength_reduction_enabled())
               {
                  // (v0 / v1) * (v2 / v3) --> (vovovov) (v0 * v2) / (v1 * v3)
                  if ((details::e_div == o0) && (details::e_mul == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf4ext_expression::
                           template compile<vtype, vtype, vtype, vtype>(expr_gen, "(t*t)/(t*t)", v0, v2, v1, v3, result);

                     exprtk_debug(("(v0 / v1) * (v2 / v3) --> (vovovov) (v0 * v2) / (v1 * v3)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (v0 / v1) / (v2 / v3) --> (vovovov) (v0 * v3) / (v1 * v2)
                  else if ((details::e_div == o0) && (details::e_div == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf4ext_expression::
                           template compile<vtype, vtype, vtype, vtype>(expr_gen, "(t*t)/(t*t)", v0, v3, v1, v2, result);

                     exprtk_debug(("(v0 / v1) / (v2 / v3) --> (vovovov) (v0 * v3) / (v1 * v2)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (v0 + v1) / (v2 / v3) --> (vovovov) (v0 + v1) * (v3 / v2)
                  else if ((details::e_add == o0) && (details::e_div == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf4ext_expression::
                           template compile<vtype, vtype, vtype, vtype>(expr_gen, "(t+t)*(t/t)", v0, v1, v3, v2, result);

                     exprtk_debug(("(v0 + v1) / (v2 / v3) --> (vovovov) (v0 + v1) * (v3 / v2)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (v0 - v1) / (v2 / v3) --> (vovovov) (v0 + v1) * (v3 / v2)
                  else if ((details::e_sub == o0) && (details::e_div == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf4ext_expression::
                           template compile<vtype, vtype, vtype, vtype>(expr_gen, "(t-t)*(t/t)", v0, v1, v3, v2, result);

                     exprtk_debug(("(v0 - v1) / (v2 / v3) --> (vovovov) (v0 - v1) * (v3 / v2)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (v0 * v1) / (v2 / v3) --> (vovovov) ((v0 * v1) * v3) / v2
                  else if ((details::e_mul == o0) && (details::e_div == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf4ext_expression::
                           template compile<vtype, vtype, vtype, vtype>(expr_gen, "((t*t)*t)/t", v0, v1, v3, v2, result);

                     exprtk_debug(("(v0 * v1) / (v2 / v3) --> (vovovov) ((v0 * v1) * v3) / v2\n"));

                     return (synthesis_result) ? result : error_node();
                  }
               }

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, v1, v2, v3, result);

               if (synthesis_result)
                  return result;

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f2 = reinterpret_cast<binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return error_node();
               else if (!expr_gen.valid_operator(o2,f2))
                  return error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator_), v0, v1, v2, v3, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "(t" << expr_gen.to_str(o0)
                         << "t)" << expr_gen.to_str(o1)
                         << "(t" << expr_gen.to_str(o2)
                         << "t)";
            }
         };

         struct synthesize_vovovoc_expression0
         {
            typedef typename vovovoc_t::type0 node_type;
            typedef typename vovovoc_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // (v0 o0 v1) o1 (v2 o2 c)
               const details::vov_base_node<Type>* vov = static_cast<details::vov_base_node<Type>*>(branch[0]);
               const details::voc_base_node<Type>* voc = static_cast<details::voc_base_node<Type>*>(branch[1]);
               const Type& v0 = vov->v0();
               const Type& v1 = vov->v1();
               const Type& v2 = voc->v ();
               const Type   c = voc->c ();
               const details::operator_type o0 = vov->operation();
               const details::operator_type o1 = operation;
               const details::operator_type o2 = voc->operation();

               details::free_node(*(expr_gen.node_allocator_),branch[0]);
               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               if (expr_gen.parser_->settings_.strength_reduction_enabled())
               {
                  // (v0 / v1) * (v2 / c) --> (vovovoc) (v0 * v2) / (v1 * c)
                  if ((details::e_div == o0) && (details::e_mul == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf4ext_expression::
                           template compile<vtype, vtype, vtype, ctype>(expr_gen, "(t*t)/(t*t)", v0, v2, v1, c, result);

                     exprtk_debug(("(v0 / v1) * (v2 / c) --> (vovovoc) (v0 * v2) / (v1 * c)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (v0 / v1) / (v2 / c) --> (vocovov) (v0 * c) / (v1 * v2)
                  if ((details::e_div == o0) && (details::e_div == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf4ext_expression::
                           template compile<vtype, ctype, vtype, vtype>(expr_gen, "(t*t)/(t*t)", v0, c, v1, v2, result);

                     exprtk_debug(("(v0 / v1) / (v2 / c) --> (vocovov) (v0 * c) / (v1 * v2)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
               }

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, v1, v2, c, result);

               if (synthesis_result)
                  return result;

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f2 = reinterpret_cast<binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return error_node();
               else if (!expr_gen.valid_operator(o2,f2))
                  return error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator_), v0, v1, v2, c, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "(t" << expr_gen.to_str(o0)
                         << "t)" << expr_gen.to_str(o1)
                         << "(t" << expr_gen.to_str(o2)
                         << "t)";
            }
         };

         struct synthesize_vovocov_expression0
         {
            typedef typename vovocov_t::type0 node_type;
            typedef typename vovocov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // (v0 o0 v1) o1 (c o2 v2)
               const details::vov_base_node<Type>* vov = static_cast<details::vov_base_node<Type>*>(branch[0]);
               const details::cov_base_node<Type>* cov = static_cast<details::cov_base_node<Type>*>(branch[1]);
               const Type& v0 = vov->v0();
               const Type& v1 = vov->v1();
               const Type& v2 = cov->v ();
               const Type   c = cov->c ();
               const details::operator_type o0 = vov->operation();
               const details::operator_type o1 = operation;
               const details::operator_type o2 = cov->operation();

               details::free_node(*(expr_gen.node_allocator_),branch[0]);
               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               if (expr_gen.parser_->settings_.strength_reduction_enabled())
               {
                  // (v0 / v1) * (c / v2) --> (vocovov) (v0 * c) / (v1 * v2)
                  if ((details::e_div == o0) && (details::e_mul == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf4ext_expression::
                           template compile<vtype, ctype, vtype, vtype>(expr_gen, "(t*t)/(t*t)", v0, c, v1, v2, result);

                     exprtk_debug(("(v0 / v1) * (c / v2) --> (vocovov) (v0 * c) / (v1 * v2)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (v0 / v1) / (c / v2) --> (vovovoc) (v0 * v2) / (v1 * c)
                  if ((details::e_div == o0) && (details::e_div == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf4ext_expression::
                           template compile<vtype, vtype, vtype, ctype>(expr_gen, "(t*t)/(t*t)", v0, v2, v1, c, result);

                     exprtk_debug(("(v0 / v1) / (c / v2) --> (vovovoc) (v0 * v2) / (v1 * c)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
               }

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, v1, c, v2, result);

               if (synthesis_result)
                  return result;

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f2 = reinterpret_cast<binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return error_node();
               else if (!expr_gen.valid_operator(o2,f2))
                  return error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator_), v0, v1, c, v2, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "(t" << expr_gen.to_str(o0)
                         << "t)" << expr_gen.to_str(o1)
                         << "(t" << expr_gen.to_str(o2)
                         << "t)";
            }
         };

         struct synthesize_vocovov_expression0
         {
            typedef typename vocovov_t::type0 node_type;
            typedef typename vocovov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // (v0 o0 c) o1 (v1 o2 v2)
               const details::voc_base_node<Type>* voc = static_cast<details::voc_base_node<Type>*>(branch[0]);
               const details::vov_base_node<Type>* vov = static_cast<details::vov_base_node<Type>*>(branch[1]);
               const Type   c = voc->c ();
               const Type& v0 = voc->v ();
               const Type& v1 = vov->v0();
               const Type& v2 = vov->v1();
               const details::operator_type o0 = voc->operation();
               const details::operator_type o1 = operation;
               const details::operator_type o2 = vov->operation();

               details::free_node(*(expr_gen.node_allocator_),branch[0]);
               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               if (expr_gen.parser_->settings_.strength_reduction_enabled())
               {
                  // (v0 / c) * (v1 / v2) --> (vovocov) (v0 * v1) / (c * v2)
                  if ((details::e_div == o0) && (details::e_mul == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf4ext_expression::
                           template compile<vtype, vtype, ctype, vtype>(expr_gen, "(t*t)/(t*t)", v0, v1, c, v2, result);

                     exprtk_debug(("(v0 / c) * (v1 / v2) --> (vovocov) (v0 * v1) / (c * v2)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (v0 / c) / (v1 / v2) --> (vovocov) (v0 * v2) / (c * v1)
                  if ((details::e_div == o0) && (details::e_div == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf4ext_expression::
                           template compile<vtype, vtype, ctype, vtype>(expr_gen, "(t*t)/(t*t)", v0, v2, c, v1, result);

                     exprtk_debug(("(v0 / c) / (v1 / v2) --> (vovocov) (v0 * v2) / (c * v1)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
               }

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, c, v1, v2, result);

               if (synthesis_result)
                  return result;

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f2 = reinterpret_cast<binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return error_node();
               else if (!expr_gen.valid_operator(o2,f2))
                  return error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator_), v0, c, v1, v2, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "(t" << expr_gen.to_str(o0)
                         << "t)" << expr_gen.to_str(o1)
                         << "(t" << expr_gen.to_str(o2)
                         << "t)";
            }
         };

         struct synthesize_covovov_expression0
         {
            typedef typename covovov_t::type0 node_type;
            typedef typename covovov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // (c o0 v0) o1 (v1 o2 v2)
               const details::cov_base_node<Type>* cov = static_cast<details::cov_base_node<Type>*>(branch[0]);
               const details::vov_base_node<Type>* vov = static_cast<details::vov_base_node<Type>*>(branch[1]);
               const Type   c = cov->c ();
               const Type& v0 = cov->v ();
               const Type& v1 = vov->v0();
               const Type& v2 = vov->v1();
               const details::operator_type o0 = cov->operation();
               const details::operator_type o1 = operation;
               const details::operator_type o2 = vov->operation();

               details::free_node(*(expr_gen.node_allocator_),branch[0]);
               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               if (expr_gen.parser_->settings_.strength_reduction_enabled())
               {
                  // (c / v0) * (v1 / v2) --> (covovov) (c * v1) / (v0 * v2)
                  if ((details::e_div == o0) && (details::e_mul == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf4ext_expression::
                           template compile<ctype, vtype, vtype, vtype>(expr_gen, "(t*t)/(t*t)", c, v1, v0, v2, result);

                     exprtk_debug(("(c / v0) * (v1 / v2) --> (covovov) (c * v1) / (v0 * v2)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (c / v0) / (v1 / v2) --> (covovov) (c * v2) / (v0 * v1)
                  if ((details::e_div == o0) && (details::e_div == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf4ext_expression::
                           template compile<ctype, vtype, vtype, vtype>(expr_gen, "(t*t)/(t*t)", c, v2, v0, v1, result);

                     exprtk_debug(("(c / v0) / (v1 / v2) --> (covovov) (c * v2) / (v0 * v1)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
               }

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), c, v0, v1, v2, result);

               if (synthesis_result)
                  return result;

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f2 = reinterpret_cast<binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return error_node();
               else if (!expr_gen.valid_operator(o2,f2))
                  return error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator_), c, v0, v1, v2, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "(t" << expr_gen.to_str(o0)
                         << "t)" << expr_gen.to_str(o1)
                         << "(t" << expr_gen.to_str(o2)
                         << "t)";
            }
         };

         struct synthesize_covocov_expression0
         {
            typedef typename covocov_t::type0 node_type;
            typedef typename covocov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // (c0 o0 v0) o1 (c1 o2 v1)
               const details::cov_base_node<Type>* cov0 = static_cast<details::cov_base_node<Type>*>(branch[0]);
               const details::cov_base_node<Type>* cov1 = static_cast<details::cov_base_node<Type>*>(branch[1]);
               const Type  c0 = cov0->c();
               const Type& v0 = cov0->v();
               const Type  c1 = cov1->c();
               const Type& v1 = cov1->v();
               const details::operator_type o0 = cov0->operation();
               const details::operator_type o1 = operation;
               const details::operator_type o2 = cov1->operation();

               details::free_node(*(expr_gen.node_allocator_),branch[0]);
               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               if (expr_gen.parser_->settings_.strength_reduction_enabled())
               {
                  // (c0 + v0) + (c1 + v1) --> (covov) (c0 + c1) + v0 + v1
                  if ((details::e_add == o0) && (details::e_add == o1) && (details::e_add == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, "(t+t)+t", (c0 + c1), v0, v1, result);

                     exprtk_debug(("(c0 + v0) + (c1 + v1) --> (covov) (c0 + c1) + v0 + v1\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (c0 + v0) - (c1 + v1) --> (covov) (c0 - c1) + v0 - v1
                  else if ((details::e_add == o0) && (details::e_sub == o1) && (details::e_add == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, "(t+t)-t", (c0 - c1), v0, v1, result);

                     exprtk_debug(("(c0 + v0) - (c1 + v1) --> (covov) (c0 - c1) + v0 - v1\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (c0 - v0) - (c1 - v1) --> (covov) (c0 - c1) - v0 + v1
                  else if ((details::e_sub == o0) && (details::e_sub == o1) && (details::e_sub == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, "(t-t)+t", (c0 - c1), v0, v1, result);

                     exprtk_debug(("(c0 - v0) - (c1 - v1) --> (covov) (c0 - c1) - v0 + v1\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (c0 * v0) * (c1 * v1) --> (covov) (c0 * c1) * v0 * v1
                  else if ((details::e_mul == o0) && (details::e_mul == o1) && (details::e_mul == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, "(t*t)*t", (c0 * c1), v0, v1, result);

                     exprtk_debug(("(c0 * v0) * (c1 * v1) --> (covov) (c0 * c1) * v0 * v1\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (c0 * v0) / (c1 * v1) --> (covov) (c0 / c1) * (v0 / v1)
                  else if ((details::e_mul == o0) && (details::e_div == o1) && (details::e_mul == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, "(t*t)/t", (c0 / c1), v0, v1, result);

                     exprtk_debug(("(c0 * v0) / (c1 * v1) --> (covov) (c0 / c1) * (v0 / v1)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (c0 / v0) * (c1 / v1) --> (covov) (c0 * c1) / (v0 * v1)
                  else if ((details::e_div == o0) && (details::e_mul == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, "t/(t*t)", (c0 * c1), v0, v1, result);

                     exprtk_debug(("(c0 / v0) * (c1 / v1) --> (covov) (c0 * c1) / (v0 * v1)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (c0 / v0) / (c1 / v1) --> (covov) ((c0 / c1) * v1) / v0
                  else if ((details::e_div == o0) && (details::e_div == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, "(t*t)/t", (c0 / c1), v1, v0, result);

                     exprtk_debug(("(c0 / v0) / (c1 / v1) --> (covov) ((c0 / c1) * v1) / v0\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (c0 * v0) / (c1 / v1) --> (covov) (c0 / c1) * (v0 * v1)
                  else if ((details::e_mul == o0) && (details::e_div == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, "t*(t*t)", (c0 / c1), v0, v1, result);

                     exprtk_debug(("(c0 * v0) / (c1 / v1) --> (covov) (c0 / c1) * (v0 * v1)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (c0 / v0) / (c1 * v1) --> (covov) (c0 / c1) / (v0 * v1)
                  else if ((details::e_div == o0) && (details::e_div == o1) && (details::e_mul == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, "t/(t*t)", (c0 / c1), v0, v1, result);

                     exprtk_debug(("(c0 / v0) / (c1 * v1) --> (covov) (c0 / c1) / (v0 * v1)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (c * v0) +/- (c * v1) --> (covov) c * (v0 +/- v1)
                  else if (
                            (std::equal_to<T>()(c0,c1)) &&
                            (details::e_mul == o0)      &&
                            (details::e_mul == o2)      &&
                            (
                              (details::e_add == o1) ||
                              (details::e_sub == o1)
                            )
                          )
                  {
                     std::string specfunc;

                     switch (o1)
                     {
                        case details::e_add : specfunc = "t*(t+t)"; break;
                        case details::e_sub : specfunc = "t*(t-t)"; break;
                        default             : return error_node();
                     }

                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, specfunc, c0, v0, v1, result);

                     exprtk_debug(("(c * v0) +/- (c * v1) --> (covov) c * (v0 +/- v1)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
               }

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), c0, v0, c1, v1, result);

               if (synthesis_result)
                  return result;

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f2 = reinterpret_cast<binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return error_node();
               else if (!expr_gen.valid_operator(o2,f2))
                  return error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator_), c0, v0, c1, v1, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "(t" << expr_gen.to_str(o0)
                         << "t)" << expr_gen.to_str(o1)
                         << "(t" << expr_gen.to_str(o2)
                         << "t)";
            }
         };

         struct synthesize_vocovoc_expression0
         {
            typedef typename vocovoc_t::type0 node_type;
            typedef typename vocovoc_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // (v0 o0 c0) o1 (v1 o2 c1)
               const details::voc_base_node<Type>* voc0 = static_cast<details::voc_base_node<Type>*>(branch[0]);
               const details::voc_base_node<Type>* voc1 = static_cast<details::voc_base_node<Type>*>(branch[1]);
               const Type  c0 = voc0->c();
               const Type& v0 = voc0->v();
               const Type  c1 = voc1->c();
               const Type& v1 = voc1->v();
               const details::operator_type o0 = voc0->operation();
               const details::operator_type o1 = operation;
               const details::operator_type o2 = voc1->operation();

               details::free_node(*(expr_gen.node_allocator_),branch[0]);
               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               if (expr_gen.parser_->settings_.strength_reduction_enabled())
               {
                  // (v0 + c0) + (v1 + c1) --> (covov) (c0 + c1) + v0 + v1
                  if ((details::e_add == o0) && (details::e_add == o1) && (details::e_add == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, "(t+t)+t", (c0 + c1), v0, v1, result);

                     exprtk_debug(("(v0 + c0) + (v1 + c1) --> (covov) (c0 + c1) + v0 + v1\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (v0 + c0) - (v1 + c1) --> (covov) (c0 - c1) + v0 - v1
                  else if ((details::e_add == o0) && (details::e_sub == o1) && (details::e_add == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, "(t+t)-t", (c0 - c1), v0, v1, result);

                     exprtk_debug(("(v0 + c0) - (v1 + c1) --> (covov) (c0 - c1) + v0 - v1\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (v0 - c0) - (v1 - c1) --> (covov) (c1 - c0) + v0 - v1
                  else if ((details::e_sub == o0) && (details::e_sub == o1) && (details::e_sub == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, "(t+t)-t", (c1 - c0), v0, v1, result);

                     exprtk_debug(("(v0 - c0) - (v1 - c1) --> (covov) (c1 - c0) + v0 - v1\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (v0 * c0) * (v1 * c1) --> (covov) (c0 * c1) * v0 * v1
                  else if ((details::e_mul == o0) && (details::e_mul == o1) && (details::e_mul == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, "(t*t)*t", (c0 * c1), v0, v1, result);

                     exprtk_debug(("(v0 * c0) * (v1 * c1) --> (covov) (c0 * c1) * v0 * v1\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (v0 * c0) / (v1 * c1) --> (covov) (c0 / c1) * (v0 / v1)
                  else if ((details::e_mul == o0) && (details::e_div == o1) && (details::e_mul == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, "(t*t)/t", (c0 / c1), v0, v1, result);

                     exprtk_debug(("(v0 * c0) / (v1 * c1) --> (covov) (c0 / c1) * (v0 / v1)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (v0 / c0) * (v1 / c1) --> (covov) (1 / (c0 * c1)) * v0 * v1
                  else if ((details::e_div == o0) && (details::e_mul == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, "(t*t)*t", Type(1) / (c0 * c1), v0, v1, result);

                     exprtk_debug(("(v0 / c0) * (v1 / c1) --> (covov) (1 / (c0 * c1)) * v0 * v1\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (v0 / c0) / (v1 / c1) --> (covov) ((c1 / c0) * v0) / v1
                  else if ((details::e_div == o0) && (details::e_div == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, "(t*t)/t", (c1 / c0), v0, v1, result);

                     exprtk_debug(("(v0 / c0) / (v1 / c1) --> (covov) ((c1 / c0) * v0) / v1\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (v0 * c0) / (v1 / c1) --> (covov) (c0 * c1) * (v0 / v1)
                  else if ((details::e_mul == o0) && (details::e_div == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, "t*(t/t)", (c0 * c1), v0, v1, result);

                     exprtk_debug(("(v0 * c0) / (v1 / c1) --> (covov) (c0 * c1) * (v0 / v1)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (v0 / c0) / (v1 * c1) --> (covov) (1 / (c0 * c1)) * v0 / v1
                  else if ((details::e_div == o0) && (details::e_div == o1) && (details::e_mul == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, "t*(t/t)", Type(1) / (c0 * c1), v0, v1, result);

                     exprtk_debug(("(v0 / c0) / (v1 * c1) --> (covov) (1 / (c0 * c1)) * v0 / v1\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (v0 / c0) * (v1 + c1) --> (vocovoc) (v0 * (1 / c0)) * (v1 + c1)
                  else if ((details::e_div == o0) && (details::e_mul == o1) && (details::e_add == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf4ext_expression::
                           template compile<vtype, ctype, vtype, ctype>(expr_gen, "(t*t)*(t+t)", v0, T(1) / c0, v1, c1, result);

                     exprtk_debug(("(v0 / c0) * (v1 + c1) --> (vocovoc) (v0 * (1 / c0)) * (v1 + c1)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (v0 / c0) * (v1 - c1) --> (vocovoc) (v0 * (1 / c0)) * (v1 - c1)
                  else if ((details::e_div == o0) && (details::e_mul == o1) && (details::e_sub == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf4ext_expression::
                           template compile<vtype, ctype, vtype, ctype>(expr_gen, "(t*t)*(t-t)", v0, T(1) / c0, v1, c1, result);

                     exprtk_debug(("(v0 / c0) * (v1 - c1) --> (vocovoc) (v0 * (1 / c0)) * (v1 - c1)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (v0 * c) +/- (v1 * c) --> (covov) c * (v0 +/- v1)
                  else if (
                            (std::equal_to<T>()(c0,c1)) &&
                            (details::e_mul == o0)      &&
                            (details::e_mul == o2)      &&
                            (
                              (details::e_add == o1) ||
                              (details::e_sub == o1)
                            )
                          )
                  {
                     std::string specfunc;

                     switch (o1)
                     {
                        case details::e_add : specfunc = "t*(t+t)"; break;
                        case details::e_sub : specfunc = "t*(t-t)"; break;
                        default             : return error_node();
                     }

                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, specfunc, c0, v0, v1, result);

                     exprtk_debug(("(v0 * c) +/- (v1 * c) --> (covov) c * (v0 +/- v1)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (v0 / c) +/- (v1 / c) --> (vovoc) (v0 +/- v1) / c
                  else if (
                            (std::equal_to<T>()(c0,c1)) &&
                            (details::e_div == o0)      &&
                            (details::e_div == o2)      &&
                            (
                              (details::e_add == o1) ||
                              (details::e_sub == o1)
                            )
                          )
                  {
                     std::string specfunc;

                     switch (o1)
                     {
                        case details::e_add : specfunc = "(t+t)/t"; break;
                        case details::e_sub : specfunc = "(t-t)/t"; break;
                        default             : return error_node();
                     }

                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<vtype, vtype, ctype>(expr_gen, specfunc, v0, v1, c0, result);

                     exprtk_debug(("(v0 / c) +/- (v1 / c) --> (vovoc) (v0 +/- v1) / c\n"));

                     return (synthesis_result) ? result : error_node();
                  }
               }

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, c0, v1, c1, result);

               if (synthesis_result)
                  return result;

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f2 = reinterpret_cast<binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return error_node();
               else if (!expr_gen.valid_operator(o2,f2))
                  return error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator_), v0, c0, v1, c1, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "(t" << expr_gen.to_str(o0)
                         << "t)" << expr_gen.to_str(o1)
                         << "(t" << expr_gen.to_str(o2)
                         << "t)";
            }
         };

         struct synthesize_covovoc_expression0
         {
            typedef typename covovoc_t::type0 node_type;
            typedef typename covovoc_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // (c0 o0 v0) o1 (v1 o2 c1)
               const details::cov_base_node<Type>* cov = static_cast<details::cov_base_node<Type>*>(branch[0]);
               const details::voc_base_node<Type>* voc = static_cast<details::voc_base_node<Type>*>(branch[1]);
               const Type  c0 = cov->c();
               const Type& v0 = cov->v();
               const Type  c1 = voc->c();
               const Type& v1 = voc->v();
               const details::operator_type o0 = cov->operation();
               const details::operator_type o1 = operation;
               const details::operator_type o2 = voc->operation();

               details::free_node(*(expr_gen.node_allocator_),branch[0]);
               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               if (expr_gen.parser_->settings_.strength_reduction_enabled())
               {
                  // (c0 + v0) + (v1 + c1) --> (covov) (c0 + c1) + v0 + v1
                  if ((details::e_add == o0) && (details::e_add == o1) && (details::e_add == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, "(t+t)+t", (c0 + c1), v0, v1, result);

                     exprtk_debug(("(c0 + v0) + (v1 + c1) --> (covov) (c0 + c1) + v0 + v1\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (c0 + v0) - (v1 + c1) --> (covov) (c0 - c1) + v0 - v1
                  else if ((details::e_add == o0) && (details::e_sub == o1) && (details::e_add == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, "(t+t)-t", (c0 - c1), v0, v1, result);

                     exprtk_debug(("(c0 + v0) - (v1 + c1) --> (covov) (c0 - c1) + v0 - v1\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (c0 - v0) - (v1 - c1) --> (covov) (c0 + c1) - v0 - v1
                  else if ((details::e_sub == o0) && (details::e_sub == o1) && (details::e_sub == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, "t-(t+t)", (c0 + c1), v0, v1, result);

                     exprtk_debug(("(c0 - v0) - (v1 - c1) --> (covov) (c0 + c1) - v0 - v1\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (c0 * v0) * (v1 * c1) --> (covov) (c0 * c1) * v0 * v1
                  else if ((details::e_mul == o0) && (details::e_mul == o1) && (details::e_mul == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, "(t*t)*t", (c0 * c1), v0, v1, result);

                     exprtk_debug(("(c0 * v0) * (v1 * c1) --> (covov) (c0 * c1) * v0 * v1\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (c0 * v0) / (v1 * c1) --> (covov) (c0 / c1) * (v0 / v1)
                  else if ((details::e_mul == o0) && (details::e_div == o1) && (details::e_mul == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, "(t*t)/t", (c0 / c1), v0, v1, result);

                     exprtk_debug(("(c0 * v0) / (v1 * c1) --> (covov) (c0 / c1) * (v0 / v1)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (c0 / v0) * (v1 / c1) --> (covov) (c0 / c1) * (v1 / v0)
                  else if ((details::e_div == o0) && (details::e_mul == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, "t*(t/t)", (c0 / c1), v1, v0, result);

                     exprtk_debug(("(c0 / v0) * (v1 / c1) --> (covov) (c0 / c1) * (v1 / v0)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (c0 / v0) / (v1 / c1) --> (covov) (c0 * c1) / (v0 * v1)
                  else if ((details::e_div == o0) && (details::e_div == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, "t/(t*t)", (c0 * c1), v0, v1, result);

                     exprtk_debug(("(c0 / v0) / (v1 / c1) --> (covov) (c0 * c1) / (v0 * v1)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (c0 * v0) / (v1 / c1) --> (covov) (c0 * c1) * (v0 / v1)
                  else if ((details::e_mul == o0) && (details::e_div == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, "(t*t)/t", (c0 * c1), v0, v1, result);

                     exprtk_debug(("(c0 * v0) / (v1 / c1) --> (covov) (c0 * c1) * (v0 / v1)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (c0 / v0) / (v1 * c1) --> (covov) (c0 / c1) / (v0 * v1)
                  else if ((details::e_div == o0) && (details::e_div == o1) && (details::e_mul == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, "t/(t*t)", (c0 / c1), v0, v1, result);

                     exprtk_debug(("(c0 / v0) / (v1 * c1) --> (covov) (c0 / c1) / (v0 * v1)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (c * v0) +/- (v1 * c) --> (covov) c * (v0 +/- v1)
                  else if (
                            (std::equal_to<T>()(c0,c1)) &&
                            (details::e_mul == o0)      &&
                            (details::e_mul == o2)      &&
                            (
                              (details::e_add == o1) ||
                              (details::e_sub == o1)
                            )
                          )
                  {
                     std::string specfunc;

                     switch (o1)
                     {
                        case details::e_add : specfunc = "t*(t+t)"; break;
                        case details::e_sub : specfunc = "t*(t-t)"; break;
                        default             : return error_node();
                     }

                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, specfunc, c0, v0, v1, result);

                     exprtk_debug(("(c * v0) +/- (v1 * c) --> (covov) c * (v0 +/- v1)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
               }

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), c0, v0, v1, c1, result);

               if (synthesis_result)
                  return result;

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f2 = reinterpret_cast<binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return error_node();
               else if (!expr_gen.valid_operator(o2,f2))
                  return error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator_), c0, v0, v1, c1, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "(t" << expr_gen.to_str(o0)
                         << "t)" << expr_gen.to_str(o1)
                         << "(t" << expr_gen.to_str(o2)
                         << "t)";
            }
         };

         struct synthesize_vococov_expression0
         {
            typedef typename vococov_t::type0 node_type;
            typedef typename vococov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // (v0 o0 c0) o1 (c1 o2 v1)
               const details::voc_base_node<Type>* voc = static_cast<details::voc_base_node<Type>*>(branch[0]);
               const details::cov_base_node<Type>* cov = static_cast<details::cov_base_node<Type>*>(branch[1]);
               const Type  c0 = voc->c();
               const Type& v0 = voc->v();
               const Type  c1 = cov->c();
               const Type& v1 = cov->v();
               const details::operator_type o0 = voc->operation();
               const details::operator_type o1 = operation;
               const details::operator_type o2 = cov->operation();

               details::free_node(*(expr_gen.node_allocator_),branch[0]);
               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               if (expr_gen.parser_->settings_.strength_reduction_enabled())
               {
                  // (v0 + c0) + (c1 + v1) --> (covov) (c0 + c1) + v0 + v1
                  if ((details::e_add == o0) && (details::e_add == o1) && (details::e_add == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, "(t+t)+t", (c0 + c1), v0, v1, result);

                     exprtk_debug(("(v0 + c0) + (c1 + v1) --> (covov) (c0 + c1) + v0 + v1\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (v0 + c0) - (c1 + v1) --> (covov) (c0 - c1) + v0 - v1
                  else if ((details::e_add == o0) && (details::e_sub == o1) && (details::e_add == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, "(t+t)-t", (c0 - c1), v0, v1, result);

                     exprtk_debug(("(v0 + c0) - (c1 + v1) --> (covov) (c0 - c1) + v0 - v1\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (v0 - c0) - (c1 - v1) --> (vovoc) v0 + v1 - (c1 + c0)
                  else if ((details::e_sub == o0) && (details::e_sub == o1) && (details::e_sub == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<vtype, vtype, ctype>(expr_gen, "(t+t)-t", v0, v1, (c1 + c0), result);

                     exprtk_debug(("(v0 - c0) - (c1 - v1) --> (vovoc) v0 + v1 - (c1 + c0)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (v0 * c0) * (c1 * v1) --> (covov) (c0 * c1) * v0 * v1
                  else if ((details::e_mul == o0) && (details::e_mul == o1) && (details::e_mul == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, "(t*t)*t", (c0 * c1), v0, v1, result);

                     exprtk_debug(("(v0 * c0) * (c1 * v1) --> (covov) (c0 * c1) * v0 * v1\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (v0 * c0) / (c1 * v1) --> (covov) (c0 / c1) * (v0 * v1)
                  else if ((details::e_mul == o0) && (details::e_div == o1) && (details::e_mul == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, "(t*t)/t", (c0 / c1), v0, v1, result);

                     exprtk_debug(("(v0 * c0) / (c1 * v1) --> (covov) (c0 / c1) * (v0 * v1)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (v0 / c0) * (c1 / v1) --> (covov) (c1 / c0) * (v0 / v1)
                  else if ((details::e_div == o0) && (details::e_mul == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, "(t*t)/t", (c1 / c0), v0, v1, result);

                     exprtk_debug(("(v0 / c0) * (c1 / v1) --> (covov) (c1 / c0) * (v0 / v1)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (v0 * c0) / (c1 / v1) --> (covov) (c0 / c1) * (v0 * v1)
                  else if ((details::e_mul == o0) && (details::e_div == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, "(t*t)*t", (c0 / c1), v0, v1, result);

                     exprtk_debug(("(v0 * c0) / (c1 / v1) --> (covov) (c0 / c1) * (v0 * v1)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (v0 / c0) / (c1 * v1) --> (covov) (1 / (c0 * c1)) * (v0 / v1)
                  else if ((details::e_div == o0) && (details::e_div == o1) && (details::e_mul == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, "(t*t)/t", Type(1) / (c0 * c1), v0, v1, result);

                     exprtk_debug(("(v0 / c0) / (c1 * v1) --> (covov) (1 / (c0 * c1)) * (v0 / v1)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (v0 / c0) / (c1 / v1) --> (vovoc) (v0 * v1) * (1 / (c0 * c1))
                  else if ((details::e_div == o0) && (details::e_div == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<vtype, vtype, ctype>(expr_gen, "(t*t)*t", v0, v1, Type(1) / (c0 * c1), result);

                     exprtk_debug(("(v0 / c0) / (c1 / v1) --> (vovoc) (v0 * v1) * (1 / (c0 * c1))\n"));

                     return (synthesis_result) ? result : error_node();
                  }
                  // (v0 * c) +/- (c * v1) --> (covov) c * (v0 +/- v1)
                  else if (
                            (std::equal_to<T>()(c0,c1)) &&
                            (details::e_mul == o0)      &&
                            (details::e_mul == o2)      &&
                            (
                              (details::e_add == o1) || (details::e_sub == o1)
                            )
                          )
                  {
                     std::string specfunc;

                     switch (o1)
                     {
                        case details::e_add : specfunc = "t*(t+t)"; break;
                        case details::e_sub : specfunc = "t*(t-t)"; break;
                        default             : return error_node();
                     }

                     const bool synthesis_result =
                        synthesize_sf3ext_expression::
                           template compile<ctype, vtype, vtype>(expr_gen, specfunc, c0, v0, v1, result);

                     exprtk_debug(("(v0 * c) +/- (c * v1) --> (covov) c * (v0 +/- v1)\n"));

                     return (synthesis_result) ? result : error_node();
                  }
               }

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, c0, c1, v1, result);

               if (synthesis_result)
                  return result;

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f2 = reinterpret_cast<binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return error_node();
               else if (!expr_gen.valid_operator(o2,f2))
                  return error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator_), v0, c0, c1, v1, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "(t" << expr_gen.to_str(o0)
                         << "t)" << expr_gen.to_str(o1)
                         << "(t" << expr_gen.to_str(o2)
                         << "t)";
            }
         };

         struct synthesize_vovovov_expression1
         {
            typedef typename vovovov_t::type1 node_type;
            typedef typename vovovov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // v0 o0 (v1 o1 (v2 o2 v3))
               typedef typename synthesize_vovov_expression1::node_type lcl_vovov_t;

               const lcl_vovov_t* vovov = static_cast<const lcl_vovov_t*>(branch[1]);
               const Type& v0 = static_cast<details::variable_node<Type>*>(branch[0])->ref();
               const Type& v1 = vovov->t0();
               const Type& v2 = vovov->t1();
               const Type& v3 = vovov->t2();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = expr_gen.get_operator(vovov->f0());
               const details::operator_type o2 = expr_gen.get_operator(vovov->f1());

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = vovov->f0();
               binary_functor_t f2 = vovov->f1();

               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen,id(expr_gen, o0, o1, o2), v0, v1, v2, v3, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o0,f0))
                  return error_node();

               exprtk_debug(("v0 o0 (v1 o1 (v2 o2 v3))\n"));

               return node_type::allocate(*(expr_gen.node_allocator_), v0, v1, v2, v3, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "t"  << expr_gen.to_str(o0)
                         << "(t" << expr_gen.to_str(o1)
                         << "(t" << expr_gen.to_str(o2)
                         << "t))";
            }
         };

         struct synthesize_vovovoc_expression1
         {
            typedef typename vovovoc_t::type1 node_type;
            typedef typename vovovoc_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // v0 o0 (v1 o1 (v2 o2 c))
               typedef typename synthesize_vovoc_expression1::node_type lcl_vovoc_t;

               const lcl_vovoc_t* vovoc = static_cast<const lcl_vovoc_t*>(branch[1]);
               const Type& v0 = static_cast<details::variable_node<Type>*>(branch[0])->ref();
               const Type& v1 = vovoc->t0();
               const Type& v2 = vovoc->t1();
               const Type   c = vovoc->t2();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = expr_gen.get_operator(vovoc->f0());
               const details::operator_type o2 = expr_gen.get_operator(vovoc->f1());

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = vovoc->f0();
               binary_functor_t f2 = vovoc->f1();

               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, v1, v2, c, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o0,f0))
                  return error_node();

               exprtk_debug(("v0 o0 (v1 o1 (v2 o2 c))\n"));

               return node_type::allocate(*(expr_gen.node_allocator_), v0, v1, v2, c, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "t"  << expr_gen.to_str(o0)
                         << "(t" << expr_gen.to_str(o1)
                         << "(t" << expr_gen.to_str(o2)
                         << "t))";
            }
         };

         struct synthesize_vovocov_expression1
         {
            typedef typename vovocov_t::type1 node_type;
            typedef typename vovocov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // v0 o0 (v1 o1 (c o2 v2))
               typedef typename synthesize_vocov_expression1::node_type lcl_vocov_t;

               const lcl_vocov_t* vocov = static_cast<const lcl_vocov_t*>(branch[1]);
               const Type& v0 = static_cast<details::variable_node<Type>*>(branch[0])->ref();
               const Type& v1 = vocov->t0();
               const Type   c = vocov->t1();
               const Type& v2 = vocov->t2();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = expr_gen.get_operator(vocov->f0());
               const details::operator_type o2 = expr_gen.get_operator(vocov->f1());

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = vocov->f0();
               binary_functor_t f2 = vocov->f1();

               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, v1, c, v2, result);

               if (synthesis_result)
                  return result;
               if (!expr_gen.valid_operator(o0,f0))
                  return error_node();

               exprtk_debug(("v0 o0 (v1 o1 (c o2 v2))\n"));

               return node_type::allocate(*(expr_gen.node_allocator_), v0, v1, c, v2, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "t"  << expr_gen.to_str(o0)
                         << "(t" << expr_gen.to_str(o1)
                         << "(t" << expr_gen.to_str(o2)
                         << "t))";
            }
         };

         struct synthesize_vocovov_expression1
         {
            typedef typename vocovov_t::type1 node_type;
            typedef typename vocovov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // v0 o0 (c o1 (v1 o2 v2))
               typedef typename synthesize_covov_expression1::node_type lcl_covov_t;

               const lcl_covov_t* covov = static_cast<const lcl_covov_t*>(branch[1]);
               const Type& v0 = static_cast<details::variable_node<Type>*>(branch[0])->ref();
               const Type   c = covov->t0();
               const Type& v1 = covov->t1();
               const Type& v2 = covov->t2();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = expr_gen.get_operator(covov->f0());
               const details::operator_type o2 = expr_gen.get_operator(covov->f1());

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = covov->f0();
               binary_functor_t f2 = covov->f1();

               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, c, v1, v2, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o0,f0))
                  return error_node();

               exprtk_debug(("v0 o0 (c o1 (v1 o2 v2))\n"));

               return node_type::allocate(*(expr_gen.node_allocator_), v0, c, v1, v2, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "t"  << expr_gen.to_str(o0)
                         << "(t" << expr_gen.to_str(o1)
                         << "(t" << expr_gen.to_str(o2)
                         << "t))";
            }
         };

         struct synthesize_covovov_expression1
         {
            typedef typename covovov_t::type1 node_type;
            typedef typename covovov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // c o0 (v0 o1 (v1 o2 v2))
               typedef typename synthesize_vovov_expression1::node_type lcl_vovov_t;

               const lcl_vovov_t* vovov = static_cast<const lcl_vovov_t*>(branch[1]);
               const Type   c = static_cast<details::literal_node<Type>*>(branch[0])->value();
               const Type& v0 = vovov->t0();
               const Type& v1 = vovov->t1();
               const Type& v2 = vovov->t2();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = expr_gen.get_operator(vovov->f0());
               const details::operator_type o2 = expr_gen.get_operator(vovov->f1());

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = vovov->f0();
               binary_functor_t f2 = vovov->f1();

               details::free_node(*(expr_gen.node_allocator_),branch[0]);
               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), c, v0, v1, v2, result);

               if (synthesis_result)
                  return result;
               if (!expr_gen.valid_operator(o0,f0))
                  return error_node();

               exprtk_debug(("c o0 (v0 o1 (v1 o2 v2))\n"));

               return node_type::allocate(*(expr_gen.node_allocator_), c, v0, v1, v2, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "t"  << expr_gen.to_str(o0)
                         << "(t" << expr_gen.to_str(o1)
                         << "(t" << expr_gen.to_str(o2)
                         << "t))";
            }
         };

         struct synthesize_covocov_expression1
         {
            typedef typename covocov_t::type1 node_type;
            typedef typename covocov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // c0 o0 (v0 o1 (c1 o2 v1))
               typedef typename synthesize_vocov_expression1::node_type lcl_vocov_t;

               const lcl_vocov_t* vocov = static_cast<const lcl_vocov_t*>(branch[1]);
               const Type  c0 = static_cast<details::literal_node<Type>*>(branch[0])->value();
               const Type& v0 = vocov->t0();
               const Type  c1 = vocov->t1();
               const Type& v1 = vocov->t2();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = expr_gen.get_operator(vocov->f0());
               const details::operator_type o2 = expr_gen.get_operator(vocov->f1());

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = vocov->f0();
               binary_functor_t f2 = vocov->f1();

               details::free_node(*(expr_gen.node_allocator_),branch[0]);
               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), c0, v0, c1, v1, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o0,f0))
                  return error_node();

               exprtk_debug(("c0 o0 (v0 o1 (c1 o2 v1))\n"));

               return node_type::allocate(*(expr_gen.node_allocator_), c0, v0, c1, v1, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "t"  << expr_gen.to_str(o0)
                         << "(t" << expr_gen.to_str(o1)
                         << "(t" << expr_gen.to_str(o2)
                         << "t))";
            }
         };

         struct synthesize_vocovoc_expression1
         {
            typedef typename vocovoc_t::type1 node_type;
            typedef typename vocovoc_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // v0 o0 (c0 o1 (v1 o2 c2))
               typedef typename synthesize_covoc_expression1::node_type lcl_covoc_t;

               const lcl_covoc_t* covoc = static_cast<const lcl_covoc_t*>(branch[1]);
               const Type& v0 = static_cast<details::variable_node<Type>*>(branch[0])->ref();
               const Type  c0 = covoc->t0();
               const Type& v1 = covoc->t1();
               const Type  c1 = covoc->t2();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = expr_gen.get_operator(covoc->f0());
               const details::operator_type o2 = expr_gen.get_operator(covoc->f1());

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = covoc->f0();
               binary_functor_t f2 = covoc->f1();

               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, c0, v1, c1, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o0,f0))
                  return error_node();

               exprtk_debug(("v0 o0 (c0 o1 (v1 o2 c2))\n"));

               return node_type::allocate(*(expr_gen.node_allocator_), v0, c0, v1, c1, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "t"  << expr_gen.to_str(o0)
                         << "(t" << expr_gen.to_str(o1)
                         << "(t" << expr_gen.to_str(o2)
                         << "t))";
            }
         };

         struct synthesize_covovoc_expression1
         {
            typedef typename covovoc_t::type1 node_type;
            typedef typename covovoc_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;
            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // c0 o0 (v0 o1 (v1 o2 c1))
               typedef typename synthesize_vovoc_expression1::node_type lcl_vovoc_t;

               const lcl_vovoc_t* vovoc = static_cast<const lcl_vovoc_t*>(branch[1]);
               const Type  c0 = static_cast<details::literal_node<Type>*>(branch[0])->value();
               const Type& v0 = vovoc->t0();
               const Type& v1 = vovoc->t1();
               const Type  c1 = vovoc->t2();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = expr_gen.get_operator(vovoc->f0());
               const details::operator_type o2 = expr_gen.get_operator(vovoc->f1());

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = vovoc->f0();
               binary_functor_t f2 = vovoc->f1();

               details::free_node(*(expr_gen.node_allocator_),branch[0]);
               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), c0, v0, v1, c1, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o0,f0))
                  return error_node();

               exprtk_debug(("c0 o0 (v0 o1 (v1 o2 c1))\n"));

               return node_type::allocate(*(expr_gen.node_allocator_), c0, v0, v1, c1, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "t"  << expr_gen.to_str(o0)
                         << "(t" << expr_gen.to_str(o1)
                         << "(t" << expr_gen.to_str(o2)
                         << "t))";
            }
         };

         struct synthesize_vococov_expression1
         {
            typedef typename vococov_t::type1 node_type;
            typedef typename vococov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // v0 o0 (c0 o1 (c1 o2 v1))
               typedef typename synthesize_cocov_expression1::node_type lcl_cocov_t;

               const lcl_cocov_t* cocov = static_cast<const lcl_cocov_t*>(branch[1]);
               const Type& v0 = static_cast<details::variable_node<Type>*>(branch[0])->ref();
               const Type  c0 = cocov->t0();
               const Type  c1 = cocov->t1();
               const Type& v1 = cocov->t2();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = expr_gen.get_operator(cocov->f0());
               const details::operator_type o2 = expr_gen.get_operator(cocov->f1());

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = cocov->f0();
               binary_functor_t f2 = cocov->f1();

               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, c0, c1, v1, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o0,f0))
                  return error_node();

               exprtk_debug(("v0 o0 (c0 o1 (c1 o2 v1))\n"));

               return node_type::allocate(*(expr_gen.node_allocator_), v0, c0, c1, v1, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "t"  << expr_gen.to_str(o0)
                         << "(t" << expr_gen.to_str(o1)
                         << "(t" << expr_gen.to_str(o2)
                         << "t))";
            }
         };

         struct synthesize_vovovov_expression2
         {
            typedef typename vovovov_t::type2 node_type;
            typedef typename vovovov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // v0 o0 ((v1 o1 v2) o2 v3)
               typedef typename synthesize_vovov_expression0::node_type lcl_vovov_t;

               const lcl_vovov_t* vovov = static_cast<const lcl_vovov_t*>(branch[1]);
               const Type& v0 = static_cast<details::variable_node<Type>*>(branch[0])->ref();
               const Type& v1 = vovov->t0();
               const Type& v2 = vovov->t1();
               const Type& v3 = vovov->t2();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = expr_gen.get_operator(vovov->f0());
               const details::operator_type o2 = expr_gen.get_operator(vovov->f1());

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = vovov->f0();
               binary_functor_t f2 = vovov->f1();

               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, v1, v2, v3, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o0,f0))
                  return error_node();

               exprtk_debug(("v0 o0 ((v1 o1 v2) o2 v3)\n"));

               return node_type::allocate(*(expr_gen.node_allocator_), v0, v1, v2, v3, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "t"   << expr_gen.to_str(o0)
                         << "((t" << expr_gen.to_str(o1)
                         << "t)"  << expr_gen.to_str(o2)
                         << "t)";
            }
         };

         struct synthesize_vovovoc_expression2
         {
            typedef typename vovovoc_t::type2 node_type;
            typedef typename vovovoc_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // v0 o0 ((v1 o1 v2) o2 c)
               typedef typename synthesize_vovoc_expression0::node_type lcl_vovoc_t;

               const lcl_vovoc_t* vovoc = static_cast<const lcl_vovoc_t*>(branch[1]);
               const Type& v0 = static_cast<details::variable_node<Type>*>(branch[0])->ref();
               const Type& v1 = vovoc->t0();
               const Type& v2 = vovoc->t1();
               const Type   c = vovoc->t2();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = expr_gen.get_operator(vovoc->f0());
               const details::operator_type o2 = expr_gen.get_operator(vovoc->f1());

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = vovoc->f0();
               binary_functor_t f2 = vovoc->f1();

               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, v1, v2, c, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o0,f0))
                  return error_node();

               exprtk_debug(("v0 o0 ((v1 o1 v2) o2 c)\n"));

               return node_type::allocate(*(expr_gen.node_allocator_), v0, v1, v2, c, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "t"   << expr_gen.to_str(o0)
                         << "((t" << expr_gen.to_str(o1)
                         << "t)"  << expr_gen.to_str(o2)
                         << "t)";
            }
         };

         struct synthesize_vovocov_expression2
         {
            typedef typename vovocov_t::type2 node_type;
            typedef typename vovocov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // v0 o0 ((v1 o1 c) o2 v2)
               typedef typename synthesize_vocov_expression0::node_type lcl_vocov_t;

               const lcl_vocov_t* vocov = static_cast<const lcl_vocov_t*>(branch[1]);
               const Type& v0 = static_cast<details::variable_node<Type>*>(branch[0])->ref();
               const Type& v1 = vocov->t0();
               const Type   c = vocov->t1();
               const Type& v2 = vocov->t2();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = expr_gen.get_operator(vocov->f0());
               const details::operator_type o2 = expr_gen.get_operator(vocov->f1());

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = vocov->f0();
               binary_functor_t f2 = vocov->f1();

               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, v1, c, v2, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o0,f0))
                  return error_node();

               exprtk_debug(("v0 o0 ((v1 o1 c) o2 v2)\n"));

               return node_type::allocate(*(expr_gen.node_allocator_), v0, v1, c, v2, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "t"   << expr_gen.to_str(o0)
                         << "((t" << expr_gen.to_str(o1)
                         << "t)"  << expr_gen.to_str(o2)
                         << "t)";
            }
         };

         struct synthesize_vocovov_expression2
         {
            typedef typename vocovov_t::type2 node_type;
            typedef typename vocovov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // v0 o0 ((c o1 v1) o2 v2)
               typedef typename synthesize_covov_expression0::node_type lcl_covov_t;

               const lcl_covov_t* covov = static_cast<const lcl_covov_t*>(branch[1]);
               const Type& v0 = static_cast<details::variable_node<Type>*>(branch[0])->ref();
               const Type   c = covov->t0();
               const Type& v1 = covov->t1();
               const Type& v2 = covov->t2();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = expr_gen.get_operator(covov->f0());
               const details::operator_type o2 = expr_gen.get_operator(covov->f1());

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = covov->f0();
               binary_functor_t f2 = covov->f1();

               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, c, v1, v2, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o0,f0))
                  return error_node();

               exprtk_debug(("v0 o0 ((c o1 v1) o2 v2)\n"));

               return node_type::allocate(*(expr_gen.node_allocator_), v0, c, v1, v2, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "t"   << expr_gen.to_str(o0)
                         << "((t" << expr_gen.to_str(o1)
                         << "t)"  << expr_gen.to_str(o2)
                         << "t)";
            }
         };

         struct synthesize_covovov_expression2
         {
            typedef typename covovov_t::type2 node_type;
            typedef typename covovov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // c o0 ((v1 o1 v2) o2 v3)
               typedef typename synthesize_vovov_expression0::node_type lcl_vovov_t;

               const lcl_vovov_t* vovov = static_cast<const lcl_vovov_t*>(branch[1]);
               const Type   c = static_cast<details::literal_node<Type>*>(branch[0])->value();
               const Type& v0 = vovov->t0();
               const Type& v1 = vovov->t1();
               const Type& v2 = vovov->t2();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = expr_gen.get_operator(vovov->f0());
               const details::operator_type o2 = expr_gen.get_operator(vovov->f1());

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = vovov->f0();
               binary_functor_t f2 = vovov->f1();

               details::free_node(*(expr_gen.node_allocator_),branch[0]);
               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), c, v0, v1, v2, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o0,f0))
                  return error_node();

               exprtk_debug(("c o0 ((v1 o1 v2) o2 v3)\n"));

               return node_type::allocate(*(expr_gen.node_allocator_), c, v0, v1, v2, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "t"   << expr_gen.to_str(o0)
                         << "((t" << expr_gen.to_str(o1)
                         << "t)"  << expr_gen.to_str(o2)
                         << "t)";
            }
        };

         struct synthesize_covocov_expression2
         {
            typedef typename covocov_t::type2 node_type;
            typedef typename covocov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // c0 o0 ((v0 o1 c1) o2 v1)
               typedef typename synthesize_vocov_expression0::node_type lcl_vocov_t;

               const lcl_vocov_t* vocov = static_cast<const lcl_vocov_t*>(branch[1]);
               const Type  c0 = static_cast<details::literal_node<Type>*>(branch[0])->value();
               const Type& v0 = vocov->t0();
               const Type  c1 = vocov->t1();
               const Type& v1 = vocov->t2();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = expr_gen.get_operator(vocov->f0());
               const details::operator_type o2 = expr_gen.get_operator(vocov->f1());

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = vocov->f0();
               binary_functor_t f2 = vocov->f1();

               details::free_node(*(expr_gen.node_allocator_),branch[0]);
               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), c0, v0, c1, v1, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o0,f0))
                  return error_node();

               exprtk_debug(("c0 o0 ((v0 o1 c1) o2 v1)\n"));

               return node_type::allocate(*(expr_gen.node_allocator_), c0, v0, c1, v1, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "t"   << expr_gen.to_str(o0)
                         << "((t" << expr_gen.to_str(o1)
                         << "t)"  << expr_gen.to_str(o2)
                         << "t)";
            }
         };

         struct synthesize_vocovoc_expression2
         {
            typedef typename vocovoc_t::type2 node_type;
            typedef typename vocovoc_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // v0 o0 ((c0 o1 v1) o2 c1)
               typedef typename synthesize_covoc_expression0::node_type lcl_covoc_t;

               const lcl_covoc_t* covoc = static_cast<const lcl_covoc_t*>(branch[1]);
               const Type& v0 = static_cast<details::variable_node<Type>*>(branch[0])->ref();
               const Type  c0 = covoc->t0();
               const Type& v1 = covoc->t1();
               const Type  c1 = covoc->t2();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = expr_gen.get_operator(covoc->f0());
               const details::operator_type o2 = expr_gen.get_operator(covoc->f1());

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = covoc->f0();
               binary_functor_t f2 = covoc->f1();

               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, c0, v1, c1, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o0,f0))
                  return error_node();

               exprtk_debug(("v0 o0 ((c0 o1 v1) o2 c1)\n"));

               return node_type::allocate(*(expr_gen.node_allocator_), v0, c0, v1, c1, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "t"   << expr_gen.to_str(o0)
                         << "((t" << expr_gen.to_str(o1)
                         << "t)"  << expr_gen.to_str(o2)
                         << "t)";
            }
         };

         struct synthesize_covovoc_expression2
         {
            typedef typename covovoc_t::type2 node_type;
            typedef typename covovoc_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // c0 o0 ((v0 o1 v1) o2 c1)
               typedef typename synthesize_vovoc_expression0::node_type lcl_vovoc_t;

               const lcl_vovoc_t* vovoc = static_cast<const lcl_vovoc_t*>(branch[1]);
               const Type  c0 = static_cast<details::literal_node<Type>*>(branch[0])->value();
               const Type& v0 = vovoc->t0();
               const Type& v1 = vovoc->t1();
               const Type  c1 = vovoc->t2();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = expr_gen.get_operator(vovoc->f0());
               const details::operator_type o2 = expr_gen.get_operator(vovoc->f1());

               binary_functor_t f0 = reinterpret_cast<binary_functor_t>(0);
               binary_functor_t f1 = vovoc->f0();
               binary_functor_t f2 = vovoc->f1();

               details::free_node(*(expr_gen.node_allocator_),branch[0]);
               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), c0, v0, v1, c1, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o0,f0))
                  return error_node();

               exprtk_debug(("c0 o0 ((v0 o1 v1) o2 c1)\n"));

               return node_type::allocate(*(expr_gen.node_allocator_), c0, v0, v1, c1, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "t"   << expr_gen.to_str(o0)
                         << "((t" << expr_gen.to_str(o1)
                         << "t)"  << expr_gen.to_str(o2)
                         << "t)";
            }
         };

         struct synthesize_vococov_expression2
         {
            typedef typename vococov_t::type2 node_type;
            static inline expression_node_ptr process(expression_generator<Type>&,
                                                      const details::operator_type&,
                                                      expression_node_ptr (&)[2])
            {
               // v0 o0 ((c0 o1 c1) o2 v1) - Not possible
               exprtk_debug(("v0 o0 ((c0 o1 c1) o2 v1) - Not possible\n"));
               return error_node();
            }

            static inline std::string id(expression_generator<Type>&,
                                         const details::operator_type,
                                         const details::operator_type,
                                         const details::operator_type)
            {
               return "INVALID";
            }
         };

         struct synthesize_vovovov_expression3
         {
            typedef typename vovovov_t::type3 node_type;
            typedef typename vovovov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // ((v0 o0 v1) o1 v2) o2 v3
               typedef typename synthesize_vovov_expression0::node_type lcl_vovov_t;

               const lcl_vovov_t* vovov = static_cast<const lcl_vovov_t*>(branch[0]);
               const Type& v0 = vovov->t0();
               const Type& v1 = vovov->t1();
               const Type& v2 = vovov->t2();
               const Type& v3 = static_cast<details::variable_node<Type>*>(branch[1])->ref();
               const details::operator_type o0 = expr_gen.get_operator(vovov->f0());
               const details::operator_type o1 = expr_gen.get_operator(vovov->f1());
               const details::operator_type o2 = operation;

               binary_functor_t f0 = vovov->f0();
               binary_functor_t f1 = vovov->f1();
               binary_functor_t f2 = reinterpret_cast<binary_functor_t>(0);

               details::free_node(*(expr_gen.node_allocator_),branch[0]);

               expression_node_ptr result = error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, v1, v2, v3, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o2,f2))
                  return error_node();

               exprtk_debug(("((v0 o0 v1) o1 v2) o2 v3\n"));

               return node_type::allocate(*(expr_gen.node_allocator_), v0, v1, v2, v3, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "((t" << expr_gen.to_str(o0)
                         << "t)"  << expr_gen.to_str(o1)
                         << "t)"  << expr_gen.to_str(o2)
                         << "t";
            }
         };

         struct synthesize_vovovoc_expression3
         {
            typedef typename vovovoc_t::type3 node_type;
            typedef typename vovovoc_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // ((v0 o0 v1) o1 v2) o2 c
               typedef typename synthesize_vovov_expression0::node_type lcl_vovov_t;

               const lcl_vovov_t* vovov = static_cast<const lcl_vovov_t*>(branch[0]);
               const Type& v0 = vovov->t0();
               const Type& v1 = vovov->t1();
               const Type& v2 = vovov->t2();
               const Type   c = static_cast<details::literal_node<Type>*>(branch[1])->value();
               const details::operator_type o0 = expr_gen.get_operator(vovov->f0());
               const details::operator_type o1 = expr_gen.get_operator(vovov->f1());
               const details::operator_type o2 = operation;

               binary_functor_t f0 = vovov->f0();
               binary_functor_t f1 = vovov->f1();
               binary_functor_t f2 = reinterpret_cast<binary_functor_t>(0);

               details::free_node(*(expr_gen.node_allocator_),branch[0]);
               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, v1, v2, c, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o2,f2))
                  return error_node();

               exprtk_debug(("((v0 o0 v1) o1 v2) o2 c\n"));

               return node_type::allocate(*(expr_gen.node_allocator_), v0, v1, v2, c, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "((t" << expr_gen.to_str(o0)
                         << "t)"  << expr_gen.to_str(o1)
                         << "t)"  << expr_gen.to_str(o2)
                         << "t";
            }
         };

         struct synthesize_vovocov_expression3
         {
            typedef typename vovocov_t::type3 node_type;
            typedef typename vovocov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // ((v0 o0 v1) o1 c) o2 v2
               typedef typename synthesize_vovoc_expression0::node_type lcl_vovoc_t;

               const lcl_vovoc_t* vovoc = static_cast<const lcl_vovoc_t*>(branch[0]);
               const Type& v0 = vovoc->t0();
               const Type& v1 = vovoc->t1();
               const Type   c = vovoc->t2();
               const Type& v2 = static_cast<details::variable_node<Type>*>(branch[1])->ref();
               const details::operator_type o0 = expr_gen.get_operator(vovoc->f0());
               const details::operator_type o1 = expr_gen.get_operator(vovoc->f1());
               const details::operator_type o2 = operation;

               binary_functor_t f0 = vovoc->f0();
               binary_functor_t f1 = vovoc->f1();
               binary_functor_t f2 = reinterpret_cast<binary_functor_t>(0);

               details::free_node(*(expr_gen.node_allocator_),branch[0]);

               expression_node_ptr result = error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, v1, c, v2, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o2,f2))
                  return error_node();

               exprtk_debug(("((v0 o0 v1) o1 c) o2 v2\n"));

               return node_type::allocate(*(expr_gen.node_allocator_), v0, v1, c, v2, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "((t" << expr_gen.to_str(o0)
                         << "t)"  << expr_gen.to_str(o1)
                         << "t)"  << expr_gen.to_str(o2)
                         << "t";
            }
         };

         struct synthesize_vocovov_expression3
         {
            typedef typename vocovov_t::type3 node_type;
            typedef typename vocovov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // ((v0 o0 c) o1 v1) o2 v2
               typedef typename synthesize_vocov_expression0::node_type lcl_vocov_t;

               const lcl_vocov_t* vocov = static_cast<const lcl_vocov_t*>(branch[0]);
               const Type& v0 = vocov->t0();
               const Type   c = vocov->t1();
               const Type& v1 = vocov->t2();
               const Type& v2 = static_cast<details::variable_node<Type>*>(branch[1])->ref();
               const details::operator_type o0 = expr_gen.get_operator(vocov->f0());
               const details::operator_type o1 = expr_gen.get_operator(vocov->f1());
               const details::operator_type o2 = operation;

               binary_functor_t f0 = vocov->f0();
               binary_functor_t f1 = vocov->f1();
               binary_functor_t f2 = reinterpret_cast<binary_functor_t>(0);

               details::free_node(*(expr_gen.node_allocator_),branch[0]);

               expression_node_ptr result = error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, c, v1, v2, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o2,f2))
                  return error_node();

               exprtk_debug(("((v0 o0 c) o1 v1) o2 v2\n"));

               return node_type::allocate(*(expr_gen.node_allocator_), v0, c, v1, v2, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "((t" << expr_gen.to_str(o0)
                         << "t)"  << expr_gen.to_str(o1)
                         << "t)"  << expr_gen.to_str(o2)
                         << "t";
            }
         };

         struct synthesize_covovov_expression3
         {
            typedef typename covovov_t::type3 node_type;
            typedef typename covovov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // ((c o0 v0) o1 v1) o2 v2
               typedef typename synthesize_covov_expression0::node_type lcl_covov_t;

               const lcl_covov_t* covov = static_cast<const lcl_covov_t*>(branch[0]);
               const Type   c = covov->t0();
               const Type& v0 = covov->t1();
               const Type& v1 = covov->t2();
               const Type& v2 = static_cast<details::variable_node<Type>*>(branch[1])->ref();
               const details::operator_type o0 = expr_gen.get_operator(covov->f0());
               const details::operator_type o1 = expr_gen.get_operator(covov->f1());
               const details::operator_type o2 = operation;

               binary_functor_t f0 = covov->f0();
               binary_functor_t f1 = covov->f1();
               binary_functor_t f2 = reinterpret_cast<binary_functor_t>(0);

               details::free_node(*(expr_gen.node_allocator_),branch[0]);

               expression_node_ptr result = error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), c, v0, v1, v2, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o2,f2))
                  return error_node();

               exprtk_debug(("((c o0 v0) o1 v1) o2 v2\n"));

               return node_type::allocate(*(expr_gen.node_allocator_), c, v0, v1, v2, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "((t" << expr_gen.to_str(o0)
                         << "t)"  << expr_gen.to_str(o1)
                         << "t)"  << expr_gen.to_str(o2)
                         << "t";
            }
         };

         struct synthesize_covocov_expression3
         {
            typedef typename covocov_t::type3 node_type;
            typedef typename covocov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // ((c0 o0 v0) o1 c1) o2 v1
               typedef typename synthesize_covoc_expression0::node_type lcl_covoc_t;

               const lcl_covoc_t* covoc = static_cast<const lcl_covoc_t*>(branch[0]);
               const Type  c0 = covoc->t0();
               const Type& v0 = covoc->t1();
               const Type  c1 = covoc->t2();
               const Type& v1 = static_cast<details::variable_node<Type>*>(branch[1])->ref();
               const details::operator_type o0 = expr_gen.get_operator(covoc->f0());
               const details::operator_type o1 = expr_gen.get_operator(covoc->f1());
               const details::operator_type o2 = operation;

               binary_functor_t f0 = covoc->f0();
               binary_functor_t f1 = covoc->f1();
               binary_functor_t f2 = reinterpret_cast<binary_functor_t>(0);

               details::free_node(*(expr_gen.node_allocator_),branch[0]);

               expression_node_ptr result = error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), c0, v0, c1, v1, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o2,f2))
                  return error_node();

               exprtk_debug(("((c0 o0 v0) o1 c1) o2 v1\n"));

               return node_type::allocate(*(expr_gen.node_allocator_), c0, v0, c1, v1, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "((t" << expr_gen.to_str(o0)
                         << "t)"  << expr_gen.to_str(o1)
                         << "t)"  << expr_gen.to_str(o2)
                         << "t";
            }
         };

         struct synthesize_vocovoc_expression3
         {
            typedef typename vocovoc_t::type3 node_type;
            typedef typename vocovoc_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // ((v0 o0 c0) o1 v1) o2 c1
               typedef typename synthesize_vocov_expression0::node_type lcl_vocov_t;

               const lcl_vocov_t* vocov = static_cast<const lcl_vocov_t*>(branch[0]);
               const Type& v0 = vocov->t0();
               const Type  c0 = vocov->t1();
               const Type& v1 = vocov->t2();
               const Type  c1 = static_cast<details::literal_node<Type>*>(branch[1])->value();
               const details::operator_type o0 = expr_gen.get_operator(vocov->f0());
               const details::operator_type o1 = expr_gen.get_operator(vocov->f1());
               const details::operator_type o2 = operation;

               binary_functor_t f0 = vocov->f0();
               binary_functor_t f1 = vocov->f1();
               binary_functor_t f2 = reinterpret_cast<binary_functor_t>(0);

               details::free_node(*(expr_gen.node_allocator_),branch[0]);
               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, c0, v1, c1, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o2,f2))
                  return error_node();

               exprtk_debug(("((v0 o0 c0) o1 v1) o2 c1\n"));

               return node_type::allocate(*(expr_gen.node_allocator_), v0, c0, v1, c1, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "((t" << expr_gen.to_str(o0)
                         << "t)"  << expr_gen.to_str(o1)
                         << "t)"  << expr_gen.to_str(o2)
                         << "t";
            }
         };

         struct synthesize_covovoc_expression3
         {
            typedef typename covovoc_t::type3 node_type;
            typedef typename covovoc_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // ((c0 o0 v0) o1 v1) o2 c1
               typedef typename synthesize_covov_expression0::node_type lcl_covov_t;

               const lcl_covov_t* covov = static_cast<const lcl_covov_t*>(branch[0]);
               const Type  c0 = covov->t0();
               const Type& v0 = covov->t1();
               const Type& v1 = covov->t2();
               const Type  c1 = static_cast<details::literal_node<Type>*>(branch[1])->value();
               const details::operator_type o0 = expr_gen.get_operator(covov->f0());
               const details::operator_type o1 = expr_gen.get_operator(covov->f1());
               const details::operator_type o2 = operation;

               binary_functor_t f0 = covov->f0();
               binary_functor_t f1 = covov->f1();
               binary_functor_t f2 = reinterpret_cast<binary_functor_t>(0);

               details::free_node(*(expr_gen.node_allocator_),branch[0]);
               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), c0, v0, v1, c1, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o2,f2))
                  return error_node();

               exprtk_debug(("((c0 o0 v0) o1 v1) o2 c1\n"));

               return node_type::allocate(*(expr_gen.node_allocator_), c0, v0, v1, c1, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "((t" << expr_gen.to_str(o0)
                         << "t)"  << expr_gen.to_str(o1)
                         << "t)"  << expr_gen.to_str(o2)
                         << "t";
            }
         };

         struct synthesize_vococov_expression3
         {
            typedef typename vococov_t::type3 node_type;
            typedef typename vococov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // ((v0 o0 c0) o1 c1) o2 v1
               typedef typename synthesize_vococ_expression0::node_type lcl_vococ_t;

               const lcl_vococ_t* vococ = static_cast<const lcl_vococ_t*>(branch[0]);
               const Type& v0 = vococ->t0();
               const Type  c0 = vococ->t1();
               const Type  c1 = vococ->t2();
               const Type& v1 = static_cast<details::variable_node<Type>*>(branch[1])->ref();
               const details::operator_type o0 = expr_gen.get_operator(vococ->f0());
               const details::operator_type o1 = expr_gen.get_operator(vococ->f1());
               const details::operator_type o2 = operation;

               binary_functor_t f0 = vococ->f0();
               binary_functor_t f1 = vococ->f1();
               binary_functor_t f2 = reinterpret_cast<binary_functor_t>(0);

               details::free_node(*(expr_gen.node_allocator_),branch[0]);

               expression_node_ptr result = error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, c0, c1, v1, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o2,f2))
                  return error_node();

               exprtk_debug(("((v0 o0 c0) o1 c1) o2 v1\n"));

               return node_type::allocate(*(expr_gen.node_allocator_), v0, c0, c1, v1, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "((t" << expr_gen.to_str(o0)
                         << "t)"  << expr_gen.to_str(o1)
                         << "t)"  << expr_gen.to_str(o2)
                         << "t";
            }
         };

         struct synthesize_vovovov_expression4
         {
            typedef typename vovovov_t::type4 node_type;
            typedef typename vovovov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // (v0 o0 (v1 o1 v2)) o2 v3
               typedef typename synthesize_vovov_expression1::node_type lcl_vovov_t;

               const lcl_vovov_t* vovov = static_cast<const lcl_vovov_t*>(branch[0]);
               const Type& v0 = vovov->t0();
               const Type& v1 = vovov->t1();
               const Type& v2 = vovov->t2();
               const Type& v3 = static_cast<details::variable_node<Type>*>(branch[1])->ref();
               const details::operator_type o0 = expr_gen.get_operator(vovov->f0());
               const details::operator_type o1 = expr_gen.get_operator(vovov->f1());
               const details::operator_type o2 = operation;

               binary_functor_t f0 = vovov->f0();
               binary_functor_t f1 = vovov->f1();
               binary_functor_t f2 = reinterpret_cast<binary_functor_t>(0);

               details::free_node(*(expr_gen.node_allocator_),branch[0]);

               expression_node_ptr result = error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, v1, v2, v3, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o2,f2))
                  return error_node();

               exprtk_debug(("(v0 o0 (v1 o1 v2)) o2 v3\n"));

               return node_type::allocate(*(expr_gen.node_allocator_), v0, v1, v2, v3, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "(t" << expr_gen.to_str(o0)
                         << "(t" << expr_gen.to_str(o1)
                         << "t)" << expr_gen.to_str(o2)
                         << "t";
            }
         };

         struct synthesize_vovovoc_expression4
         {
            typedef typename vovovoc_t::type4 node_type;
            typedef typename vovovoc_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // ((v0 o0 (v1 o1 v2)) o2 c)
               typedef typename synthesize_vovov_expression1::node_type lcl_vovov_t;

               const lcl_vovov_t* vovov = static_cast<const lcl_vovov_t*>(branch[0]);
               const Type& v0 = vovov->t0();
               const Type& v1 = vovov->t1();
               const Type& v2 = vovov->t2();
               const Type   c = static_cast<details::literal_node<Type>*>(branch[1])->value();
               const details::operator_type o0 = expr_gen.get_operator(vovov->f0());
               const details::operator_type o1 = expr_gen.get_operator(vovov->f1());
               const details::operator_type o2 = operation;

               binary_functor_t f0 = vovov->f0();
               binary_functor_t f1 = vovov->f1();
               binary_functor_t f2 = reinterpret_cast<binary_functor_t>(0);

               details::free_node(*(expr_gen.node_allocator_),branch[0]);
               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, v1, v2, c, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o2,f2))
                  return error_node();

               exprtk_debug(("((v0 o0 (v1 o1 v2)) o2 c)\n"));

               return node_type::allocate(*(expr_gen.node_allocator_), v0, v1, v2, c, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "(t" << expr_gen.to_str(o0)
                         << "(t" << expr_gen.to_str(o1)
                         << "t)" << expr_gen.to_str(o2)
                         << "t";
            }
         };

         struct synthesize_vovocov_expression4
         {
            typedef typename vovocov_t::type4 node_type;
            typedef typename vovocov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // ((v0 o0 (v1 o1 c)) o2 v1)
               typedef typename synthesize_vovoc_expression1::node_type lcl_vovoc_t;

               const lcl_vovoc_t* vovoc = static_cast<const lcl_vovoc_t*>(branch[0]);
               const Type& v0 = vovoc->t0();
               const Type& v1 = vovoc->t1();
               const Type   c = vovoc->t2();
               const Type& v2 = static_cast<details::variable_node<Type>*>(branch[1])->ref();
               const details::operator_type o0 = expr_gen.get_operator(vovoc->f0());
               const details::operator_type o1 = expr_gen.get_operator(vovoc->f1());
               const details::operator_type o2 = operation;

               binary_functor_t f0 = vovoc->f0();
               binary_functor_t f1 = vovoc->f1();
               binary_functor_t f2 = reinterpret_cast<binary_functor_t>(0);

               details::free_node(*(expr_gen.node_allocator_),branch[0]);

               expression_node_ptr result = error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, v1, c, v2, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o2,f2))
                  return error_node();

               exprtk_debug(("((v0 o0 (v1 o1 c)) o2 v1)\n"));

               return node_type::allocate(*(expr_gen.node_allocator_), v0, v1, c, v2, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "(t" << expr_gen.to_str(o0)
                         << "(t" << expr_gen.to_str(o1)
                         << "t)" << expr_gen.to_str(o2)
                         << "t";
            }
         };

         struct synthesize_vocovov_expression4
         {
            typedef typename vocovov_t::type4 node_type;
            typedef typename vocovov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // ((v0 o0 (c o1 v1)) o2 v2)
               typedef typename synthesize_vocov_expression1::node_type lcl_vocov_t;

               const lcl_vocov_t* vocov = static_cast<const lcl_vocov_t*>(branch[0]);
               const Type& v0 = vocov->t0();
               const Type   c = vocov->t1();
               const Type& v1 = vocov->t2();
               const Type& v2 = static_cast<details::variable_node<Type>*>(branch[1])->ref();
               const details::operator_type o0 = expr_gen.get_operator(vocov->f0());
               const details::operator_type o1 = expr_gen.get_operator(vocov->f1());
               const details::operator_type o2 = operation;

               binary_functor_t f0 = vocov->f0();
               binary_functor_t f1 = vocov->f1();
               binary_functor_t f2 = reinterpret_cast<binary_functor_t>(0);

               details::free_node(*(expr_gen.node_allocator_),branch[0]);
               expression_node_ptr result = error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, c, v1, v2, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o2,f2))
                  return error_node();

               exprtk_debug(("((v0 o0 (c o1 v1)) o2 v2)\n"));

               return node_type::allocate(*(expr_gen.node_allocator_), v0, c, v1, v2, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "(t" << expr_gen.to_str(o0)
                         << "(t" << expr_gen.to_str(o1)
                         << "t)" << expr_gen.to_str(o2)
                         << "t";
            }
         };

         struct synthesize_covovov_expression4
         {
            typedef typename covovov_t::type4 node_type;
            typedef typename covovov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // ((c o0 (v0 o1 v1)) o2 v2)
               typedef typename synthesize_covov_expression1::node_type lcl_covov_t;

               const lcl_covov_t* covov = static_cast<const lcl_covov_t*>(branch[0]);
               const Type   c = covov->t0();
               const Type& v0 = covov->t1();
               const Type& v1 = covov->t2();
               const Type& v2 = static_cast<details::variable_node<Type>*>(branch[1])->ref();
               const details::operator_type o0 = expr_gen.get_operator(covov->f0());
               const details::operator_type o1 = expr_gen.get_operator(covov->f1());
               const details::operator_type o2 = operation;

               binary_functor_t f0 = covov->f0();
               binary_functor_t f1 = covov->f1();
               binary_functor_t f2 = reinterpret_cast<binary_functor_t>(0);

               details::free_node(*(expr_gen.node_allocator_),branch[0]);

               expression_node_ptr result = error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), c, v0, v1, v2, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o2,f2))
                  return error_node();

               exprtk_debug(("((c o0 (v0 o1 v1)) o2 v2)\n"));

               return node_type::allocate(*(expr_gen.node_allocator_), c, v0, v1, v2, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "(t" << expr_gen.to_str(o0)
                         << "(t" << expr_gen.to_str(o1)
                         << "t)" << expr_gen.to_str(o2)
                         << "t";
            }
         };

         struct synthesize_covocov_expression4
         {
            typedef typename covocov_t::type4 node_type;
            typedef typename covocov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // ((c0 o0 (v0 o1 c1)) o2 v1)
               typedef typename synthesize_covoc_expression1::node_type lcl_covoc_t;

               const lcl_covoc_t* covoc = static_cast<const lcl_covoc_t*>(branch[0]);
               const Type  c0 = covoc->t0();
               const Type& v0 = covoc->t1();
               const Type  c1 = covoc->t2();
               const Type& v1 = static_cast<details::variable_node<Type>*>(branch[1])->ref();
               const details::operator_type o0 = expr_gen.get_operator(covoc->f0());
               const details::operator_type o1 = expr_gen.get_operator(covoc->f1());
               const details::operator_type o2 = operation;

               binary_functor_t f0 = covoc->f0();
               binary_functor_t f1 = covoc->f1();
               binary_functor_t f2 = reinterpret_cast<binary_functor_t>(0);

               details::free_node(*(expr_gen.node_allocator_),branch[0]);

               expression_node_ptr result = error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), c0, v0, c1, v1, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o2,f2))
                  return error_node();

               exprtk_debug(("((c0 o0 (v0 o1 c1)) o2 v1)\n"));

               return node_type::allocate(*(expr_gen.node_allocator_), c0, v0, c1, v1, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "(t" << expr_gen.to_str(o0)
                         << "(t" << expr_gen.to_str(o1)
                         << "t)" << expr_gen.to_str(o2)
                         << "t";
            }
         };

         struct synthesize_vocovoc_expression4
         {
            typedef typename vocovoc_t::type4 node_type;
            typedef typename vocovoc_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // ((v0 o0 (c0 o1 v1)) o2 c1)
               typedef typename synthesize_vocov_expression1::node_type lcl_vocov_t;

               const lcl_vocov_t* vocov = static_cast<const lcl_vocov_t*>(branch[0]);
               const Type& v0 = vocov->t0();
               const Type  c0 = vocov->t1();
               const Type& v1 = vocov->t2();
               const Type  c1 = static_cast<details::literal_node<Type>*>(branch[1])->value();
               const details::operator_type o0 = expr_gen.get_operator(vocov->f0());
               const details::operator_type o1 = expr_gen.get_operator(vocov->f1());
               const details::operator_type o2 = operation;

               binary_functor_t f0 = vocov->f0();
               binary_functor_t f1 = vocov->f1();
               binary_functor_t f2 = reinterpret_cast<binary_functor_t>(0);

               details::free_node(*(expr_gen.node_allocator_),branch[0]);
               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, c0, v1, c1, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o2,f2))
                  return error_node();

               exprtk_debug(("((v0 o0 (c0 o1 v1)) o2 c1)\n"));

               return node_type::allocate(*(expr_gen.node_allocator_), v0, c0, v1, c1, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "(t" << expr_gen.to_str(o0)
                         << "(t" << expr_gen.to_str(o1)
                         << "t)" << expr_gen.to_str(o2)
                         << "t";
            }
         };

         struct synthesize_covovoc_expression4
         {
            typedef typename covovoc_t::type4 node_type;
            typedef typename covovoc_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static inline expression_node_ptr process(expression_generator<Type>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_node_ptr (&branch)[2])
            {
               // ((c0 o0 (v0 o1 v1)) o2 c1)
               typedef typename synthesize_covov_expression1::node_type lcl_covov_t;

               const lcl_covov_t* covov = static_cast<const lcl_covov_t*>(branch[0]);
               const Type  c0 = covov->t0();
               const Type& v0 = covov->t1();
               const Type& v1 = covov->t2();
               const Type  c1 = static_cast<details::literal_node<Type>*>(branch[1])->value();
               const details::operator_type o0 = expr_gen.get_operator(covov->f0());
               const details::operator_type o1 = expr_gen.get_operator(covov->f1());
               const details::operator_type o2 = operation;

               binary_functor_t f0 = covov->f0();
               binary_functor_t f1 = covov->f1();
               binary_functor_t f2 = reinterpret_cast<binary_functor_t>(0);

               details::free_node(*(expr_gen.node_allocator_),branch[0]);
               details::free_node(*(expr_gen.node_allocator_),branch[1]);

               expression_node_ptr result = error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), c0, v0, v1, c1, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o2,f2))
                  return error_node();

               exprtk_debug(("((c0 o0 (v0 o1 v1)) o2 c1)\n"));

               return node_type::allocate(*(expr_gen.node_allocator_), c0, v0, v1, c1, f0, f1, f2);
            }

            static inline std::string id(expression_generator<Type>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1,
                                         const details::operator_type o2)
            {
               return details::build_string()
                         << "(t" << expr_gen.to_str(o0)
                         << "(t" << expr_gen.to_str(o1)
                         << "t)" << expr_gen.to_str(o2)
                         << "t";
            }
         };

         struct synthesize_vococov_expression4
         {
            typedef typename vococov_t::type4 node_type;
            static inline expression_node_ptr process(expression_generator<Type>&,
                                                      const details::operator_type&,
                                                      expression_node_ptr (&)[2])
            {
               // ((v0 o0 (c0 o1 c1)) o2 v1) - Not possible
               exprtk_debug(("((v0 o0 (c0 o1 c1)) o2 v1) - Not possible\n"));
               return error_node();
            }

            static inline std::string id(expression_generator<Type>&,
                                         const details::operator_type,
                                         const details::operator_type,
                                         const details::operator_type)
            {
               return "INVALID";
            }
         };
         #endif

         inline expression_node_ptr synthesize_uvouv_expression(const details::operator_type& operation, expression_node_ptr (&branch)[2])
         {
            // Definition: uv o uv
            details::operator_type o0 = static_cast<details::uv_base_node<Type>*>(branch[0])->operation();
            details::operator_type o1 = static_cast<details::uv_base_node<Type>*>(branch[1])->operation();
            const Type& v0 = static_cast<details::uv_base_node<Type>*>(branch[0])->v();
            const Type& v1 = static_cast<details::uv_base_node<Type>*>(branch[1])->v();
            unary_functor_t u0 = reinterpret_cast<unary_functor_t> (0);
            unary_functor_t u1 = reinterpret_cast<unary_functor_t> (0);
            binary_functor_t f = reinterpret_cast<binary_functor_t>(0);

            if (!valid_operator(o0,u0))
               return error_node();
            else if (!valid_operator(o1,u1))
               return error_node();
            else if (!valid_operator(operation,f))
               return error_node();

            expression_node_ptr result = error_node();

            if (
                 (details::e_neg == o0) &&
                 (details::e_neg == o1)
               )
            {
               switch (operation)
               {
                  // (-v0 + -v1) --> -(v0 + v1)
                  case details::e_add : result = (*this)(details::e_neg,
                                                    node_allocator_->
                                                       allocate_rr<typename details::
                                                          vov_node<Type,details::add_op<Type> > >(v0, v1));
                                        exprtk_debug(("(-v0 + -v1) --> -(v0 + v1)\n"));
                                        break;

                  // (-v0 - -v1) --> (v1 - v0)
                  case details::e_sub : result = node_allocator_->
                                                    allocate_rr<typename details::
                                                       vov_node<Type,details::sub_op<Type> > >(v1, v0);
                                        exprtk_debug(("(-v0 - -v1) --> (v1 - v0)\n"));
                                        break;

                  // (-v0 * -v1) --> (v0 * v1)
                  case details::e_mul : result = node_allocator_->
                                                    allocate_rr<typename details::
                                                       vov_node<Type,details::mul_op<Type> > >(v0, v1);
                                        exprtk_debug(("(-v0 * -v1) --> (v0 * v1)\n"));
                                        break;

                  // (-v0 / -v1) --> (v0 / v1)
                  case details::e_div : result = node_allocator_->
                                                    allocate_rr<typename details::
                                                       vov_node<Type,details::div_op<Type> > >(v0, v1);
                                        exprtk_debug(("(-v0 / -v1) --> (v0 / v1)\n"));
                                        break;

                  default             : break;
               }
            }

            if (0 == result)
            {
               result = node_allocator_->
                            allocate_rrrrr<typename details::uvouv_node<Type> >(v0, v1, u0, u1, f);
            }

            details::free_all_nodes(*node_allocator_,branch);
            return result;
         }

         #undef basic_opr_switch_statements
         #undef extended_opr_switch_statements
         #undef unary_opr_switch_statements

         #ifndef exprtk_disable_string_capabilities

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

         template <typename T0, typename T1>
         inline expression_node_ptr synthesize_str_xrox_expression_impl(const details::operator_type& opr,
                                                                        T0 s0, T1 s1,
                                                                        range_t rp0)
         {
            switch (opr)
            {
               #define case_stmt(op0, op1)                                                                      \
               case op0 : return node_allocator_->                                                              \
                             allocate_ttt<typename details::str_xrox_node<Type,T0,T1,range_t,op1<Type> >,T0,T1> \
                                (s0, s1, rp0);                                                                  \

               string_opr_switch_statements
               #undef case_stmt
               default : return error_node();
            }
         }

         template <typename T0, typename T1>
         inline expression_node_ptr synthesize_str_xoxr_expression_impl(const details::operator_type& opr,
                                                                        T0 s0, T1 s1,
                                                                        range_t rp1)
         {
            switch (opr)
            {
               #define case_stmt(op0, op1)                                                                      \
               case op0 : return node_allocator_->                                                              \
                             allocate_ttt<typename details::str_xoxr_node<Type,T0,T1,range_t,op1<Type> >,T0,T1> \
                                (s0, s1, rp1);                                                                  \

               string_opr_switch_statements
               #undef case_stmt
               default : return error_node();
            }
         }

         template <typename T0, typename T1>
         inline expression_node_ptr synthesize_str_xroxr_expression_impl(const details::operator_type& opr,
                                                                         T0 s0, T1 s1,
                                                                         range_t rp0, range_t rp1)
         {
            switch (opr)
            {
               #define case_stmt(op0, op1)                                                                        \
               case op0 : return node_allocator_->                                                                \
                             allocate_tttt<typename details::str_xroxr_node<Type,T0,T1,range_t,op1<Type> >,T0,T1> \
                                (s0, s1, rp0, rp1);                                                               \

               string_opr_switch_statements
               #undef case_stmt
               default : return error_node();
            }
         }

         template <typename T0, typename T1>
         inline expression_node_ptr synthesize_sos_expression_impl(const details::operator_type& opr, T0 s0, T1 s1)
         {
            switch (opr)
            {
               #define case_stmt(op0, op1)                                                                 \
               case op0 : return node_allocator_->                                                         \
                             allocate_tt<typename details::sos_node<Type,T0,T1,op1<Type> >,T0,T1>(s0, s1); \

               string_opr_switch_statements
               #undef case_stmt
               default : return error_node();
            }
         }

         inline expression_node_ptr synthesize_sos_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2])
         {
            std::string& s0 = static_cast<details::stringvar_node<Type>*>(branch[0])->ref();
            std::string& s1 = static_cast<details::stringvar_node<Type>*>(branch[1])->ref();

            return synthesize_sos_expression_impl<std::string&,std::string&>(opr, s0, s1);
         }

         inline expression_node_ptr synthesize_sros_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2])
         {
            std::string&  s0 = static_cast<details::string_range_node<Type>*>(branch[0])->ref  ();
            std::string&  s1 = static_cast<details::stringvar_node<Type>*>   (branch[1])->ref  ();
            range_t      rp0 = static_cast<details::string_range_node<Type>*>(branch[0])->range();

            static_cast<details::string_range_node<Type>*>(branch[0])->range_ref().clear();

            details::free_node(*node_allocator_,branch[0]);

            return synthesize_str_xrox_expression_impl<std::string&,std::string&>(opr, s0, s1, rp0);
         }

         inline expression_node_ptr synthesize_sosr_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2])
         {
            std::string&  s0 = static_cast<details::stringvar_node<Type>*>   (branch[0])->ref  ();
            std::string&  s1 = static_cast<details::string_range_node<Type>*>(branch[1])->ref  ();
            range_t      rp1 = static_cast<details::string_range_node<Type>*>(branch[1])->range();

            static_cast<details::string_range_node<Type>*>(branch[1])->range_ref().clear();

            details::free_node(*node_allocator_,branch[1]);

            return synthesize_str_xoxr_expression_impl<std::string&,std::string&>(opr, s0, s1, rp1);
         }

         inline expression_node_ptr synthesize_socsr_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2])
         {
            std::string&  s0 = static_cast<details::stringvar_node<Type>*>         (branch[0])->ref  ();
            std::string   s1 = static_cast<details::const_string_range_node<Type>*>(branch[1])->str  ();
            range_t      rp1 = static_cast<details::const_string_range_node<Type>*>(branch[1])->range();

            static_cast<details::const_string_range_node<Type>*>(branch[1])->range_ref().clear();

            details::free_node(*node_allocator_,branch[1]);

            return synthesize_str_xoxr_expression_impl<std::string&, const std::string>(opr, s0, s1, rp1);
         }

         inline expression_node_ptr synthesize_srosr_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2])
         {
            std::string&  s0 = static_cast<details::string_range_node<Type>*>(branch[0])->ref  ();
            std::string&  s1 = static_cast<details::string_range_node<Type>*>(branch[1])->ref  ();
            range_t      rp0 = static_cast<details::string_range_node<Type>*>(branch[0])->range();
            range_t      rp1 = static_cast<details::string_range_node<Type>*>(branch[1])->range();

            static_cast<details::string_range_node<Type>*>(branch[0])->range_ref().clear();
            static_cast<details::string_range_node<Type>*>(branch[1])->range_ref().clear();

            details::free_node(*node_allocator_,branch[0]);
            details::free_node(*node_allocator_,branch[1]);

            return synthesize_str_xroxr_expression_impl<std::string&,std::string&>(opr, s0, s1, rp0, rp1);
         }

         inline expression_node_ptr synthesize_socs_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2])
         {
            std::string& s0 = static_cast<     details::stringvar_node<Type>*>(branch[0])->ref();
            std::string  s1 = static_cast<details::string_literal_node<Type>*>(branch[1])->str();

            details::free_node(*node_allocator_,branch[1]);

            return synthesize_sos_expression_impl<std::string&, const std::string>(opr, s0, s1);
         }

         inline expression_node_ptr synthesize_csos_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2])
         {
            std::string  s0 = static_cast<details::string_literal_node<Type>*>(branch[0])->str();
            std::string& s1 = static_cast<details::stringvar_node<Type>*     >(branch[1])->ref();

            details::free_node(*node_allocator_,branch[0]);

            return synthesize_sos_expression_impl<const std::string,std::string&>(opr, s0, s1);
         }

         inline expression_node_ptr synthesize_csosr_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2])
         {
            std::string  s0  = static_cast<details::string_literal_node<Type>*>(branch[0])->str  ();
            std::string& s1  = static_cast<details::string_range_node<Type>*  >(branch[1])->ref  ();
            range_t      rp1 = static_cast<details::string_range_node<Type>*  >(branch[1])->range();

            static_cast<details::string_range_node<Type>*>(branch[1])->range_ref().clear();

            details::free_node(*node_allocator_,branch[0]);
            details::free_node(*node_allocator_,branch[1]);

            return synthesize_str_xoxr_expression_impl<const std::string,std::string&>(opr, s0, s1, rp1);
         }

         inline expression_node_ptr synthesize_srocs_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2])
         {
            std::string&  s0 = static_cast<details::string_range_node<Type>*  >(branch[0])->ref  ();
            std::string   s1 = static_cast<details::string_literal_node<Type>*>(branch[1])->str  ();
            range_t      rp0 = static_cast<details::string_range_node<Type>*  >(branch[0])->range();

            static_cast<details::string_range_node<Type>*>(branch[0])->range_ref().clear();

            details::free_node(*node_allocator_,branch[0]);
            details::free_node(*node_allocator_,branch[1]);

            return synthesize_str_xrox_expression_impl<std::string&, const std::string>(opr, s0, s1, rp0);
         }

         inline expression_node_ptr synthesize_srocsr_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2])
         {
            std::string&  s0 = static_cast<details::string_range_node<Type>*      >(branch[0])->ref  ();
            std::string   s1 = static_cast<details::const_string_range_node<Type>*>(branch[1])->str  ();
            range_t      rp0 = static_cast<details::string_range_node<Type>*      >(branch[0])->range();
            range_t      rp1 = static_cast<details::const_string_range_node<Type>*>(branch[1])->range();

            static_cast<details::string_range_node<Type>*>      (branch[0])->range_ref().clear();
            static_cast<details::const_string_range_node<Type>*>(branch[1])->range_ref().clear();

            details::free_node(*node_allocator_,branch[0]);
            details::free_node(*node_allocator_,branch[1]);

            return synthesize_str_xroxr_expression_impl<std::string&, const std::string>(opr, s0, s1, rp0, rp1);
         }

         inline expression_node_ptr synthesize_csocs_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2])
         {
            const std::string s0 = static_cast<details::string_literal_node<Type>*>(branch[0])->str();
            const std::string s1 = static_cast<details::string_literal_node<Type>*>(branch[1])->str();

            expression_node_ptr result = error_node();

            if (details::e_add == opr)
               result = node_allocator_->allocate_c<details::string_literal_node<Type> >(s0 + s1);
            else if (details::e_in == opr)
               result = node_allocator_->allocate_c<details::literal_node<Type> >(details::in_op   <Type>::process(s0,s1));
            else if (details::e_like == opr)
               result = node_allocator_->allocate_c<details::literal_node<Type> >(details::like_op <Type>::process(s0,s1));
            else if (details::e_ilike == opr)
               result = node_allocator_->allocate_c<details::literal_node<Type> >(details::ilike_op<Type>::process(s0,s1));
            else
            {
               expression_node_ptr temp = synthesize_sos_expression_impl<const std::string, const std::string>(opr, s0, s1);

               const Type v = temp->value();

               details::free_node(*node_allocator_,temp);

               result = node_allocator_->allocate<literal_node_t>(v);
            }

            details::free_all_nodes(*node_allocator_,branch);

            return result;
         }

         inline expression_node_ptr synthesize_csocsr_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2])
         {
            const std::string s0 = static_cast<details::string_literal_node<Type>*    >(branch[0])->str  ();
                  std::string s1 = static_cast<details::const_string_range_node<Type>*>(branch[1])->str  ();
            range_t          rp1 = static_cast<details::const_string_range_node<Type>*>(branch[1])->range();

            static_cast<details::const_string_range_node<Type>*>(branch[1])->range_ref().clear();

            details::free_node(*node_allocator_,branch[0]);
            details::free_node(*node_allocator_,branch[1]);

            return synthesize_str_xoxr_expression_impl<const std::string, const std::string>(opr, s0, s1, rp1);
         }

         inline expression_node_ptr synthesize_csros_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2])
         {
            std::string   s0 = static_cast<details::const_string_range_node<Type>*>(branch[0])->str  ();
            std::string&  s1 = static_cast<details::stringvar_node<Type>*         >(branch[1])->ref  ();
            range_t      rp0 = static_cast<details::const_string_range_node<Type>*>(branch[0])->range();

            static_cast<details::const_string_range_node<Type>*>(branch[0])->range_ref().clear();

            details::free_node(*node_allocator_,branch[0]);

            return synthesize_str_xrox_expression_impl<const std::string,std::string&>(opr, s0, s1, rp0);
         }

         inline expression_node_ptr synthesize_csrosr_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2])
         {
            const std::string  s0 = static_cast<details::const_string_range_node<Type>*>(branch[0])->str  ();
                  std::string& s1 = static_cast<details::string_range_node<Type>*      >(branch[1])->ref  ();
            const range_t     rp0 = static_cast<details::const_string_range_node<Type>*>(branch[0])->range();
            const range_t     rp1 = static_cast<details::string_range_node<Type>*      >(branch[1])->range();

            static_cast<details::const_string_range_node<Type>*>(branch[0])->range_ref().clear();
            static_cast<details::string_range_node<Type>*>      (branch[1])->range_ref().clear();

            details::free_node(*node_allocator_,branch[0]);
            details::free_node(*node_allocator_,branch[1]);

            return synthesize_str_xroxr_expression_impl<const std::string,std::string&>(opr, s0, s1, rp0, rp1);
         }

         inline expression_node_ptr synthesize_csrocs_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2])
         {
            const std::string s0 = static_cast<details::const_string_range_node<Type>*>(branch[0])->str  ();
            const std::string s1 = static_cast<details::string_literal_node<Type>*    >(branch[1])->str  ();
            const range_t    rp0 = static_cast<details::const_string_range_node<Type>*>(branch[0])->range();

            static_cast<details::const_string_range_node<Type>*>(branch[0])->range_ref().clear();

            details::free_all_nodes(*node_allocator_,branch);

            return synthesize_str_xrox_expression_impl<const std::string,std::string>(opr, s0, s1, rp0);
         }

         inline expression_node_ptr synthesize_csrocsr_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2])
         {
            const std::string s0 = static_cast<details::const_string_range_node<Type>*>(branch[0])->str  ();
            const std::string s1 = static_cast<details::const_string_range_node<Type>*>(branch[1])->str  ();
            const range_t    rp0 = static_cast<details::const_string_range_node<Type>*>(branch[0])->range();
            const range_t    rp1 = static_cast<details::const_string_range_node<Type>*>(branch[1])->range();

            static_cast<details::const_string_range_node<Type>*>(branch[0])->range_ref().clear();
            static_cast<details::const_string_range_node<Type>*>(branch[1])->range_ref().clear();

            details::free_all_nodes(*node_allocator_,branch);

            return synthesize_str_xroxr_expression_impl<const std::string, const std::string>(opr, s0, s1, rp0, rp1);
         }

         inline expression_node_ptr synthesize_strogen_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2])
         {
            switch (opr)
            {
               #define case_stmt(op0, op1)                                                      \
               case op0 : return node_allocator_->                                              \
                             allocate_ttt<typename details::str_sogens_node<Type,op1<Type> > >  \
                                (opr, branch[0], branch[1]);                                    \

               string_opr_switch_statements
               #undef case_stmt
               default : return error_node();
            }
         }
         #endif

         #ifndef exprtk_disable_string_capabilities
         inline expression_node_ptr synthesize_string_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2])
         {
            if ((0 == branch[0]) || (0 == branch[1]))
            {
               details::free_all_nodes(*node_allocator_,branch);

               return error_node();
            }

            const bool b0_is_s   = details::is_string_node            (branch[0]);
            const bool b0_is_cs  = details::is_const_string_node      (branch[0]);
            const bool b0_is_sr  = details::is_string_range_node      (branch[0]);
            const bool b0_is_csr = details::is_const_string_range_node(branch[0]);

            const bool b1_is_s   = details::is_string_node            (branch[1]);
            const bool b1_is_cs  = details::is_const_string_node      (branch[1]);
            const bool b1_is_sr  = details::is_string_range_node      (branch[1]);
            const bool b1_is_csr = details::is_const_string_range_node(branch[1]);

            const bool b0_is_gen = details::is_string_assignment_node (branch[0]) ||
                                   details::is_genricstring_range_node(branch[0]) ||
                                   details::is_string_concat_node     (branch[0]) ||
                                   details::is_string_function_node   (branch[0]) ||
                                   details::is_string_condition_node  (branch[0]) ||
                                   details::is_string_ccondition_node (branch[0]) ||
                                   details::is_string_vararg_node     (branch[0]) ;

            const bool b1_is_gen = details::is_string_assignment_node (branch[1]) ||
                                   details::is_genricstring_range_node(branch[1]) ||
                                   details::is_string_concat_node     (branch[1]) ||
                                   details::is_string_function_node   (branch[1]) ||
                                   details::is_string_condition_node  (branch[1]) ||
                                   details::is_string_ccondition_node (branch[1]) ||
                                   details::is_string_vararg_node     (branch[1]) ;

            if (details::e_add == opr)
            {
               if (!b0_is_cs || !b1_is_cs)
               {
                  return synthesize_expression<string_concat_node_t,2>(opr,branch);
               }
            }

            if (b0_is_gen || b1_is_gen)
            {
               return synthesize_strogen_expression(opr,branch);
            }
            else if (b0_is_s)
            {
               if      (b1_is_s  ) return synthesize_sos_expression   (opr,branch);
               else if (b1_is_cs ) return synthesize_socs_expression  (opr,branch);
               else if (b1_is_sr ) return synthesize_sosr_expression  (opr,branch);
               else if (b1_is_csr) return synthesize_socsr_expression (opr,branch);
            }
            else if (b0_is_cs)
            {
               if      (b1_is_s  ) return synthesize_csos_expression  (opr,branch);
               else if (b1_is_cs ) return synthesize_csocs_expression (opr,branch);
               else if (b1_is_sr ) return synthesize_csosr_expression (opr,branch);
               else if (b1_is_csr) return synthesize_csocsr_expression(opr,branch);
            }
            else if (b0_is_sr)
            {
               if      (b1_is_s  ) return synthesize_sros_expression  (opr,branch);
               else if (b1_is_sr ) return synthesize_srosr_expression (opr,branch);
               else if (b1_is_cs ) return synthesize_srocs_expression (opr,branch);
               else if (b1_is_csr) return synthesize_srocsr_expression(opr,branch);
            }
            else if (b0_is_csr)
            {
               if      (b1_is_s  ) return synthesize_csros_expression  (opr,branch);
               else if (b1_is_sr ) return synthesize_csrosr_expression (opr,branch);
               else if (b1_is_cs ) return synthesize_csrocs_expression (opr,branch);
               else if (b1_is_csr) return synthesize_csrocsr_expression(opr,branch);
            }

            return error_node();
         }
         #else
         inline expression_node_ptr synthesize_string_expression(const details::operator_type&, expression_node_ptr (&branch)[2])
         {
            details::free_all_nodes(*node_allocator_,branch);
            return error_node();
         }
         #endif

         #ifndef exprtk_disable_string_capabilities
         inline expression_node_ptr synthesize_string_expression(const details::operator_type& opr, expression_node_ptr (&branch)[3])
         {
            if (details::e_inrange != opr)
               return error_node();
            else if ((0 == branch[0]) || (0 == branch[1]) || (0 == branch[2]))
            {
               details::free_all_nodes(*node_allocator_,branch);

               return error_node();
            }
            else if (
                      details::is_const_string_node(branch[0]) &&
                      details::is_const_string_node(branch[1]) &&
                      details::is_const_string_node(branch[2])
                    )
            {
               const std::string s0 = static_cast<details::string_literal_node<Type>*>(branch[0])->str();
               const std::string s1 = static_cast<details::string_literal_node<Type>*>(branch[1])->str();
               const std::string s2 = static_cast<details::string_literal_node<Type>*>(branch[2])->str();

               const Type v = (((s0 <= s1) && (s1 <= s2)) ? Type(1) : Type(0));

               details::free_all_nodes(*node_allocator_,branch);

               return node_allocator_->allocate_c<details::literal_node<Type> >(v);
            }
            else if (
                      details::is_string_node(branch[0]) &&
                      details::is_string_node(branch[1]) &&
                      details::is_string_node(branch[2])
                    )
            {
               std::string& s0 = static_cast<details::stringvar_node<Type>*>(branch[0])->ref();
               std::string& s1 = static_cast<details::stringvar_node<Type>*>(branch[1])->ref();
               std::string& s2 = static_cast<details::stringvar_node<Type>*>(branch[2])->ref();

               typedef typename details::sosos_node<Type, std::string&, std::string&, std::string&, details::inrange_op<Type> > inrange_t;

               return node_allocator_->allocate_type<inrange_t, std::string&, std::string&, std::string&>(s0, s1, s2);
            }
            else if (
                      details::is_const_string_node(branch[0]) &&
                            details::is_string_node(branch[1]) &&
                      details::is_const_string_node(branch[2])
                    )
            {
               std::string  s0 = static_cast<details::string_literal_node<Type>*>(branch[0])->str();
               std::string& s1 = static_cast<details::stringvar_node<Type>*     >(branch[1])->ref();
               std::string  s2 = static_cast<details::string_literal_node<Type>*>(branch[2])->str();

               typedef typename details::sosos_node<Type, std::string, std::string&, std::string, details::inrange_op<Type> > inrange_t;

               details::free_node(*node_allocator_,branch[0]);
               details::free_node(*node_allocator_,branch[2]);

               return node_allocator_->allocate_type<inrange_t, std::string, std::string&, std::string>(s0, s1, s2);
            }
            else if (
                            details::is_string_node(branch[0]) &&
                      details::is_const_string_node(branch[1]) &&
                            details::is_string_node(branch[2])
                    )
            {
               std::string&  s0 = static_cast<details::stringvar_node<Type>*     >(branch[0])->ref();
               std::string   s1 = static_cast<details::string_literal_node<Type>*>(branch[1])->str();
               std::string&  s2 = static_cast<details::stringvar_node<Type>*     >(branch[2])->ref();

               typedef typename details::sosos_node<Type, std::string&, std::string, std::string&, details::inrange_op<Type> > inrange_t;

               details::free_node(*node_allocator_,branch[1]);

               return node_allocator_->allocate_type<inrange_t, std::string&, std::string, std::string&>(s0, s1, s2);
            }
            else if (
                      details::is_string_node(branch[0]) &&
                      details::is_string_node(branch[1]) &&
                      details::is_const_string_node(branch[2])
                    )
            {
               std::string& s0 = static_cast<details::stringvar_node<Type>*     >(branch[0])->ref();
               std::string& s1 = static_cast<details::stringvar_node<Type>*     >(branch[1])->ref();
               std::string  s2 = static_cast<details::string_literal_node<Type>*>(branch[2])->str();

               typedef typename details::sosos_node<Type, std::string&, std::string&, std::string, details::inrange_op<Type> > inrange_t;

               details::free_node(*node_allocator_,branch[2]);

               return node_allocator_->allocate_type<inrange_t, std::string&, std::string&, std::string>(s0, s1, s2);
            }
            else if (
                      details::is_const_string_node(branch[0]) &&
                      details::      is_string_node(branch[1]) &&
                      details::      is_string_node(branch[2])
                    )
            {
               std::string  s0 = static_cast<details::string_literal_node<Type>*>(branch[0])->str();
               std::string& s1 = static_cast<details::stringvar_node<Type>*     >(branch[1])->ref();
               std::string& s2 = static_cast<details::stringvar_node<Type>*     >(branch[2])->ref();

               typedef typename details::sosos_node<Type, std::string, std::string&, std::string&, details::inrange_op<Type> > inrange_t;

               details::free_node(*node_allocator_,branch[0]);

               return node_allocator_->allocate_type<inrange_t, std::string, std::string&, std::string&>(s0, s1, s2);
            }
            else
               return error_node();
         }
         #else
         inline expression_node_ptr synthesize_string_expression(const details::operator_type&, expression_node_ptr (&branch)[3])
         {
            details::free_all_nodes(*node_allocator_,branch);
            return error_node();
         }
         #endif

         inline expression_node_ptr synthesize_null_expression(const details::operator_type& operation, expression_node_ptr (&branch)[2])
         {
            /*
             Note: The following are the type promotion rules
             that relate to operations that include 'null':
             0. null ==/!=     null --> true false
             1. null operation null --> null
             2. x    ==/!=     null --> true/false
             3. null ==/!=     x    --> true/false
             4. x   operation  null --> x
             5. null operation x    --> x
            */

            typedef typename details::null_eq_node<T> nulleq_node_t;

            const bool b0_null = details::is_null_node(branch[0]);
            const bool b1_null = details::is_null_node(branch[1]);

            if (b0_null && b1_null)
            {
               expression_node_ptr result = error_node();

               if (details::e_eq == operation)
                  result = node_allocator_->allocate_c<literal_node_t>(T(1));
               else if (details::e_ne == operation)
                  result = node_allocator_->allocate_c<literal_node_t>(T(0));

               if (result)
               {
                  details::free_node(*node_allocator_,branch[0]);
                  details::free_node(*node_allocator_,branch[1]);

                  return result;
               }

               details::free_node(*node_allocator_,branch[1]);

               return branch[0];
            }
            else if (details::e_eq == operation)
            {
               expression_node_ptr result = node_allocator_->
                                                allocate_rc<nulleq_node_t>(branch[b0_null ? 0 : 1],true);

               details::free_node(*node_allocator_,branch[b0_null ? 1 : 0]);

               return result;
            }
            else if (details::e_ne == operation)
            {
               expression_node_ptr result = node_allocator_->
                                                allocate_rc<nulleq_node_t>(branch[b0_null ? 0 : 1],false);

               details::free_node(*node_allocator_,branch[b0_null ? 1 : 0]);

               return result;
            }
            else if (b0_null)
            {
               details::free_node(*node_allocator_,branch[0]);
               branch[0] = branch[1];
               branch[1] = error_node();
            }
            else if (b1_null)
            {
               details::free_node(*node_allocator_,branch[1]);
               branch[1] = error_node();
            }

            if (
                 (details::e_add == operation) || (details::e_sub == operation) ||
                 (details::e_mul == operation) || (details::e_div == operation) ||
                 (details::e_mod == operation) || (details::e_pow == operation)
               )
            {
               return branch[0];
            }

            details::free_node(*node_allocator_, branch[0]);

            if (
                 (details::e_lt    == operation) || (details::e_lte  == operation) ||
                 (details::e_gt    == operation) || (details::e_gte  == operation) ||
                 (details::e_and   == operation) || (details::e_nand == operation) ||
                 (details::e_or    == operation) || (details::e_nor  == operation) ||
                 (details::e_xor   == operation) || (details::e_xnor == operation) ||
                 (details::e_in    == operation) || (details::e_like == operation) ||
                 (details::e_ilike == operation)
               )
            {
               return node_allocator_->allocate_c<literal_node_t>(T(0));
            }

            return node_allocator_->allocate<details::null_node<Type> >();
         }

         template <typename NodeType, std::size_t N>
         inline expression_node_ptr synthesize_expression(const details::operator_type& operation, expression_node_ptr (&branch)[N])
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
                  const Type v = expression_point->value();
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
         inline expression_node_ptr synthesize_expression(F* f, expression_node_ptr (&branch)[N])
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
               Type v = expression_point->value();
               details::free_node(*node_allocator_,expression_point);

               return node_allocator_->allocate<literal_node_t>(v);
            }

            parser_->state_.activate_side_effect("synthesize_expression(function<NT,N>)");

            return expression_point;
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

      inline void set_error(const parser_error::type& error_type)
      {
         error_list_.push_back(error_type);
      }

      inline void remove_last_error()
      {
         if (!error_list_.empty())
         {
            error_list_.pop_back();
         }
      }

      inline void set_synthesis_error(const std::string& synthesis_error_message)
      {
         if (synthesis_error_.empty())
         {
            synthesis_error_ = synthesis_error_message;
         }
      }

      inline void register_local_vars(expression<T>& e)
      {
         for (std::size_t i = 0; i < sem_.size(); ++i)
         {
            scope_element& se = sem_.get_element(i);

            if (
                 (scope_element::e_variable == se.type) ||
                 (scope_element::e_vecelem  == se.type)
               )
            {
               if (se.var_node)
               {
                  e.register_local_var(se.var_node);
               }

               if (se.data)
               {
                  e.register_local_data(se.data, 1, 0);
               }
            }
            else if (scope_element::e_vector == se.type)
            {
               if (se.vec_node)
               {
                  e.register_local_var(se.vec_node);
               }

               if (se.data)
               {
                  e.register_local_data(se.data, se.size, 1);
               }
            }
            #ifndef exprtk_disable_string_capabilities
            else if (scope_element::e_string == se.type)
            {
               if (se.str_node)
               {
                  e.register_local_var(se.str_node);
               }

               if (se.data)
               {
                  e.register_local_data(se.data, se.size, 2);
               }
            }
            #endif

            se.var_node  = 0;
            se.vec_node  = 0;
            #ifndef exprtk_disable_string_capabilities
            se.str_node  = 0;
            #endif
            se.data      = 0;
            se.ref_count = 0;
            se.active    = false;
         }
      }

      inline void register_return_results(expression<T>& e)
      {
         e.register_return_results(results_context_);
         results_context_ = 0;
      }

      inline void load_unary_operations_map(unary_op_map_t& m)
      {
         #define register_unary_op(Op, UnaryFunctor)            \
         m.insert(std::make_pair(Op,UnaryFunctor<T>::process)); \

         register_unary_op(details::e_abs   , details::abs_op  )
         register_unary_op(details::e_acos  , details::acos_op )
         register_unary_op(details::e_acosh , details::acosh_op)
         register_unary_op(details::e_asin  , details::asin_op )
         register_unary_op(details::e_asinh , details::asinh_op)
         register_unary_op(details::e_atanh , details::atanh_op)
         register_unary_op(details::e_ceil  , details::ceil_op )
         register_unary_op(details::e_cos   , details::cos_op  )
         register_unary_op(details::e_cosh  , details::cosh_op )
         register_unary_op(details::e_exp   , details::exp_op  )
         register_unary_op(details::e_expm1 , details::expm1_op)
         register_unary_op(details::e_floor , details::floor_op)
         register_unary_op(details::e_log   , details::log_op  )
         register_unary_op(details::e_log10 , details::log10_op)
         register_unary_op(details::e_log2  , details::log2_op )
         register_unary_op(details::e_log1p , details::log1p_op)
         register_unary_op(details::e_neg   , details::neg_op  )
         register_unary_op(details::e_pos   , details::pos_op  )
         register_unary_op(details::e_round , details::round_op)
         register_unary_op(details::e_sin   , details::sin_op  )
         register_unary_op(details::e_sinc  , details::sinc_op )
         register_unary_op(details::e_sinh  , details::sinh_op )
         register_unary_op(details::e_sqrt  , details::sqrt_op )
         register_unary_op(details::e_tan   , details::tan_op  )
         register_unary_op(details::e_tanh  , details::tanh_op )
         register_unary_op(details::e_cot   , details::cot_op  )
         register_unary_op(details::e_sec   , details::sec_op  )
         register_unary_op(details::e_csc   , details::csc_op  )
         register_unary_op(details::e_r2d   , details::r2d_op  )
         register_unary_op(details::e_d2r   , details::d2r_op  )
         register_unary_op(details::e_d2g   , details::d2g_op  )
         register_unary_op(details::e_g2d   , details::g2d_op  )
         register_unary_op(details::e_notl  , details::notl_op )
         register_unary_op(details::e_sgn   , details::sgn_op  )
         register_unary_op(details::e_erf   , details::erf_op  )
         register_unary_op(details::e_erfc  , details::erfc_op )
         register_unary_op(details::e_ncdf  , details::ncdf_op )
         register_unary_op(details::e_frac  , details::frac_op )
         register_unary_op(details::e_trunc , details::trunc_op)
         #undef register_unary_op
      }

      inline void load_binary_operations_map(binary_op_map_t& m)
      {
         typedef typename binary_op_map_t::value_type value_type;

         #define register_binary_op(Op, BinaryFunctor)       \
         m.insert(value_type(Op,BinaryFunctor<T>::process)); \

         register_binary_op(details::e_add  , details::add_op )
         register_binary_op(details::e_sub  , details::sub_op )
         register_binary_op(details::e_mul  , details::mul_op )
         register_binary_op(details::e_div  , details::div_op )
         register_binary_op(details::e_mod  , details::mod_op )
         register_binary_op(details::e_pow  , details::pow_op )
         register_binary_op(details::e_lt   , details::lt_op  )
         register_binary_op(details::e_lte  , details::lte_op )
         register_binary_op(details::e_gt   , details::gt_op  )
         register_binary_op(details::e_gte  , details::gte_op )
         register_binary_op(details::e_eq   , details::eq_op  )
         register_binary_op(details::e_ne   , details::ne_op  )
         register_binary_op(details::e_and  , details::and_op )
         register_binary_op(details::e_nand , details::nand_op)
         register_binary_op(details::e_or   , details::or_op  )
         register_binary_op(details::e_nor  , details::nor_op )
         register_binary_op(details::e_xor  , details::xor_op )
         register_binary_op(details::e_xnor , details::xnor_op)
         #undef register_binary_op
      }

      inline void load_inv_binary_operations_map(inv_binary_op_map_t& m)
      {
         typedef typename inv_binary_op_map_t::value_type value_type;

         #define register_binary_op(Op, BinaryFunctor)       \
         m.insert(value_type(BinaryFunctor<T>::process,Op)); \

         register_binary_op(details::e_add  , details::add_op )
         register_binary_op(details::e_sub  , details::sub_op )
         register_binary_op(details::e_mul  , details::mul_op )
         register_binary_op(details::e_div  , details::div_op )
         register_binary_op(details::e_mod  , details::mod_op )
         register_binary_op(details::e_pow  , details::pow_op )
         register_binary_op(details::e_lt   , details::lt_op  )
         register_binary_op(details::e_lte  , details::lte_op )
         register_binary_op(details::e_gt   , details::gt_op  )
         register_binary_op(details::e_gte  , details::gte_op )
         register_binary_op(details::e_eq   , details::eq_op  )
         register_binary_op(details::e_ne   , details::ne_op  )
         register_binary_op(details::e_and  , details::and_op )
         register_binary_op(details::e_nand , details::nand_op)
         register_binary_op(details::e_or   , details::or_op  )
         register_binary_op(details::e_nor  , details::nor_op )
         register_binary_op(details::e_xor  , details::xor_op )
         register_binary_op(details::e_xnor , details::xnor_op)
         #undef register_binary_op
      }

      inline void load_sf3_map(sf3_map_t& sf3_map)
      {
         typedef std::pair<trinary_functor_t,details::operator_type> pair_t;

         #define register_sf3(Op)                                                                             \
         sf3_map[details::sf##Op##_op<T>::id()] = pair_t(details::sf##Op##_op<T>::process,details::e_sf##Op); \

         register_sf3(00) register_sf3(01) register_sf3(02) register_sf3(03)
         register_sf3(04) register_sf3(05) register_sf3(06) register_sf3(07)
         register_sf3(08) register_sf3(09) register_sf3(10) register_sf3(11)
         register_sf3(12) register_sf3(13) register_sf3(14) register_sf3(15)
         register_sf3(16) register_sf3(17) register_sf3(18) register_sf3(19)
         register_sf3(20) register_sf3(21) register_sf3(22) register_sf3(23)
         register_sf3(24) register_sf3(25) register_sf3(26) register_sf3(27)
         register_sf3(28) register_sf3(29) register_sf3(30)
         #undef register_sf3

         #define register_sf3_extid(Id, Op)                                        \
         sf3_map[Id] = pair_t(details::sf##Op##_op<T>::process,details::e_sf##Op); \

         register_sf3_extid("(t-t)-t",23)  // (t-t)-t --> t-(t+t)
         #undef register_sf3_extid
      }

      inline void load_sf4_map(sf4_map_t& sf4_map)
      {
         typedef std::pair<quaternary_functor_t,details::operator_type> pair_t;

         #define register_sf4(Op)                                                                             \
         sf4_map[details::sf##Op##_op<T>::id()] = pair_t(details::sf##Op##_op<T>::process,details::e_sf##Op); \

         register_sf4(48) register_sf4(49) register_sf4(50) register_sf4(51)
         register_sf4(52) register_sf4(53) register_sf4(54) register_sf4(55)
         register_sf4(56) register_sf4(57) register_sf4(58) register_sf4(59)
         register_sf4(60) register_sf4(61) register_sf4(62) register_sf4(63)
         register_sf4(64) register_sf4(65) register_sf4(66) register_sf4(67)
         register_sf4(68) register_sf4(69) register_sf4(70) register_sf4(71)
         register_sf4(72) register_sf4(73) register_sf4(74) register_sf4(75)
         register_sf4(76) register_sf4(77) register_sf4(78) register_sf4(79)
         register_sf4(80) register_sf4(81) register_sf4(82) register_sf4(83)
         #undef register_sf4

         #define register_sf4ext(Op)                                                                                    \
         sf4_map[details::sfext##Op##_op<T>::id()] = pair_t(details::sfext##Op##_op<T>::process,details::e_sf4ext##Op); \

         register_sf4ext(00) register_sf4ext(01) register_sf4ext(02) register_sf4ext(03)
         register_sf4ext(04) register_sf4ext(05) register_sf4ext(06) register_sf4ext(07)
         register_sf4ext(08) register_sf4ext(09) register_sf4ext(10) register_sf4ext(11)
         register_sf4ext(12) register_sf4ext(13) register_sf4ext(14) register_sf4ext(15)
         register_sf4ext(16) register_sf4ext(17) register_sf4ext(18) register_sf4ext(19)
         register_sf4ext(20) register_sf4ext(21) register_sf4ext(22) register_sf4ext(23)
         register_sf4ext(24) register_sf4ext(25) register_sf4ext(26) register_sf4ext(27)
         register_sf4ext(28) register_sf4ext(29) register_sf4ext(30) register_sf4ext(31)
         register_sf4ext(32) register_sf4ext(33) register_sf4ext(34) register_sf4ext(35)
         register_sf4ext(36) register_sf4ext(36) register_sf4ext(38) register_sf4ext(39)
         register_sf4ext(40) register_sf4ext(41) register_sf4ext(42) register_sf4ext(43)
         register_sf4ext(44) register_sf4ext(45) register_sf4ext(46) register_sf4ext(47)
         register_sf4ext(48) register_sf4ext(49) register_sf4ext(50) register_sf4ext(51)
         register_sf4ext(52) register_sf4ext(53) register_sf4ext(54) register_sf4ext(55)
         register_sf4ext(56) register_sf4ext(57) register_sf4ext(58) register_sf4ext(59)
         register_sf4ext(60) register_sf4ext(61)
         #undef register_sf4ext
      }

      inline results_context_t& results_ctx()
      {
         if (0 == results_context_)
         {
            results_context_ = new results_context_t();
         }

         return (*results_context_);
      }

      inline void return_cleanup()
      {
         #ifndef exprtk_disable_return_statement
         if (results_context_)
         {
            delete results_context_;
            results_context_ = 0;
         }

         state_.return_stmt_present = false;
         #endif
      }

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

   namespace details
   {
      template <typename T>
      struct collector_helper
      {
         typedef Essa::Math::symbol_table<T> symbol_table_t;
         typedef Essa::Math::expression<T>   expression_t;
         typedef Essa::Math::parser<T>       parser_t;
         typedef typename parser_t::dependent_entity_collector::symbol_t symbol_t;
         typedef typename parser_t::unknown_symbol_resolver usr_t;

         struct resolve_as_vector : public parser_t::unknown_symbol_resolver
         {
            typedef Essa::Math::parser<T> parser_t;

            resolve_as_vector()
            : usr_t(usr_t::e_usrmode_extended)
            {}

            virtual bool process(const std::string& unknown_symbol,
                                 symbol_table_t& symbol_table,
                                 std::string&)
            {
               static T v[1];
               symbol_table.add_vector(unknown_symbol,v);
               return true;
            }
         };

         static inline bool collection_pass(const std::string& expression_string,
                                            std::set<std::string>& symbol_set,
                                            const bool collect_variables,
                                            const bool collect_functions,
                                            const bool vector_pass,
                                            symbol_table_t& ext_symbol_table)
         {
            symbol_table_t symbol_table;
            expression_t   expression;
            parser_t       parser;

            resolve_as_vector vect_resolver;

            expression.register_symbol_table(symbol_table    );
            expression.register_symbol_table(ext_symbol_table);

            if (vector_pass)
               parser.enable_unknown_symbol_resolver(&vect_resolver);
            else
               parser.enable_unknown_symbol_resolver();

            if (collect_variables)
               parser.dec().collect_variables() = true;

            if (collect_functions)
               parser.dec().collect_functions() = true;

            bool pass_result = false;

            details::disable_type_checking(parser);

            if (parser.compile(expression_string, expression))
            {
               pass_result = true;

               std::deque<symbol_t> symb_list;
               parser.dec().symbols(symb_list);

               for (std::size_t i = 0; i < symb_list.size(); ++i)
               {
                  symbol_set.insert(symb_list[i].first);
               }
            }

            return pass_result;
         }
      };
   }

   template <typename Allocator,
             template <typename, typename> class Sequence>
   inline bool collect_variables(const std::string& expression,
                                 Sequence<std::string, Allocator>& symbol_list)
   {
      typedef double T;
      typedef details::collector_helper<T> collect_t;

      collect_t::symbol_table_t null_symbol_table;

      std::set<std::string> symbol_set;

      const bool variable_pass = collect_t::collection_pass
                                    (expression, symbol_set, true, false, false, null_symbol_table);
      const bool vector_pass   = collect_t::collection_pass
                                    (expression, symbol_set, true, false,  true, null_symbol_table);

      if (!variable_pass && !vector_pass)
         return false;

      std::set<std::string>::iterator itr = symbol_set.begin();

      while (symbol_set.end() != itr)
      {
         symbol_list.push_back(*itr);
         ++itr;
      }

      return true;
   }

   template <typename T,
             typename Allocator,
             template <typename, typename> class Sequence>
   inline bool collect_variables(const std::string& expression,
                                 Essa::Math::symbol_table<T>& extrnl_symbol_table,
                                 Sequence<std::string, Allocator>& symbol_list)
   {
      typedef details::collector_helper<T> collect_t;

      std::set<std::string> symbol_set;

      const bool variable_pass = collect_t::collection_pass
                                    (expression, symbol_set, true, false, false, extrnl_symbol_table);
      const bool vector_pass   = collect_t::collection_pass
                                    (expression, symbol_set, true, false,  true, extrnl_symbol_table);

      if (!variable_pass && !vector_pass)
         return false;

      std::set<std::string>::iterator itr = symbol_set.begin();

      while (symbol_set.end() != itr)
      {
         symbol_list.push_back(*itr);
         ++itr;
      }

      return true;
   }

   template <typename Allocator,
             template <typename, typename> class Sequence>
   inline bool collect_functions(const std::string& expression,
                                 Sequence<std::string, Allocator>& symbol_list)
   {
      typedef double T;
      typedef details::collector_helper<T> collect_t;

      collect_t::symbol_table_t null_symbol_table;

      std::set<std::string> symbol_set;

      const bool variable_pass = collect_t::collection_pass
                                    (expression, symbol_set, false, true, false, null_symbol_table);
      const bool vector_pass   = collect_t::collection_pass
                                    (expression, symbol_set, false, true,  true, null_symbol_table);

      if (!variable_pass && !vector_pass)
         return false;

      std::set<std::string>::iterator itr = symbol_set.begin();

      while (symbol_set.end() != itr)
      {
         symbol_list.push_back(*itr);
         ++itr;
      }

      return true;
   }

   template <typename T,
             typename Allocator,
             template <typename, typename> class Sequence>
   inline bool collect_functions(const std::string& expression,
                                 Essa::Math::symbol_table<T>& extrnl_symbol_table,
                                 Sequence<std::string, Allocator>& symbol_list)
   {
      typedef details::collector_helper<T> collect_t;

      std::set<std::string> symbol_set;

      const bool variable_pass = collect_t::collection_pass
                                    (expression, symbol_set, false, true, false, extrnl_symbol_table);
      const bool vector_pass   = collect_t::collection_pass
                                    (expression, symbol_set, false, true,  true, extrnl_symbol_table);

      if (!variable_pass && !vector_pass)
         return false;

      std::set<std::string>::iterator itr = symbol_set.begin();

      while (symbol_set.end() != itr)
      {
         symbol_list.push_back(*itr);
         ++itr;
      }

      return true;
   }

   template <typename T>
   inline T integrate(const expression<T>& e,
                      T& x,
                      const T& r0, const T& r1,
                      const std::size_t number_of_intervals = 1000000)
   {
      if (r0 > r1)
         return T(0);

      const T h = (r1 - r0) / (T(2) * number_of_intervals);
      T total_area = T(0);

      for (std::size_t i = 0; i < number_of_intervals; ++i)
      {
         x = r0 + T(2) * i * h;
         const T y0 = e.value(); x += h;
         const T y1 = e.value(); x += h;
         const T y2 = e.value(); x += h;
         total_area += h * (y0 + T(4) * y1 + y2) / T(3);
      }

      return total_area;
   }

   template <typename T>
   inline T integrate(const expression<T>& e,
                      const std::string& variable_name,
                      const T& r0, const T& r1,
                      const std::size_t number_of_intervals = 1000000)
   {
      const symbol_table<T>& sym_table = e.get_symbol_table();

      if (!sym_table.valid())
         return std::numeric_limits<T>::quiet_NaN();

      details::variable_node<T>* var = sym_table.get_variable(variable_name);

      if (var)
      {
         T& x = var->ref();
         const T x_original = x;
         const T result = integrate(e, x, r0, r1, number_of_intervals);
         x = x_original;

         return result;
      }
      else
         return std::numeric_limits<T>::quiet_NaN();
   }

   template <typename T>
   inline T derivative(const expression<T>& e,
                       T& x,
                       const T& h = T(0.00000001))
   {
      const T x_init = x;
      const T _2h    = T(2) * h;

      x = x_init + _2h;
      const T y0 = e.value();
      x = x_init + h;
      const T y1 = e.value();
      x = x_init - h;
      const T y2 = e.value();
      x = x_init - _2h;
      const T y3 = e.value();
      x = x_init;

      return (-y0 + T(8) * (y1 - y2) + y3) / (T(12) * h);
   }

   template <typename T>
   inline T second_derivative(const expression<T>& e,
                              T& x,
                              const T& h = T(0.00001))
   {
      const T x_init = x;
      const T _2h    = T(2) * h;

      const T y = e.value();
      x = x_init + _2h;
      const T y0 = e.value();
      x = x_init + h;
      const T y1 = e.value();
      x = x_init - h;
      const T y2 = e.value();
      x = x_init - _2h;
      const T y3 = e.value();
      x = x_init;

      return (-y0 + T(16) * (y1 + y2) - T(30) * y - y3) / (T(12) * h * h);
   }

   template <typename T>
   inline T third_derivative(const expression<T>& e,
                             T& x,
                             const T& h = T(0.0001))
   {
      const T x_init = x;
      const T _2h    = T(2) * h;

      x = x_init + _2h;
      const T y0 = e.value();
      x = x_init + h;
      const T y1 = e.value();
      x = x_init - h;
      const T y2 = e.value();
      x = x_init - _2h;
      const T y3 = e.value();
      x = x_init;

      return (y0 + T(2) * (y2 - y1) - y3) / (T(2) * h * h * h);
   }

   template <typename T>
   inline T derivative(const expression<T>& e,
                       const std::string& variable_name,
                       const T& h = T(0.00000001))
   {
      const symbol_table<T>& sym_table = e.get_symbol_table();

      if (!sym_table.valid())
      {
         return std::numeric_limits<T>::quiet_NaN();
      }

      details::variable_node<T>* var = sym_table.get_variable(variable_name);

      if (var)
      {
         T& x = var->ref();
         const T x_original = x;
         const T result = derivative(e, x, h);
         x = x_original;

         return result;
      }
      else
         return std::numeric_limits<T>::quiet_NaN();
   }

   template <typename T>
   inline T second_derivative(const expression<T>& e,
                              const std::string& variable_name,
                              const T& h = T(0.00001))
   {
      const symbol_table<T>& sym_table = e.get_symbol_table();

      if (!sym_table.valid())
      {
         return std::numeric_limits<T>::quiet_NaN();
      }

      details::variable_node<T>* var = sym_table.get_variable(variable_name);

      if (var)
      {
         T& x = var->ref();
         const T x_original = x;
         const T result = second_derivative(e, x, h);
         x = x_original;

         return result;
      }
      else
         return std::numeric_limits<T>::quiet_NaN();
   }

   template <typename T>
   inline T third_derivative(const expression<T>& e,
                             const std::string& variable_name,
                             const T& h = T(0.0001))
   {
      const symbol_table<T>& sym_table = e.get_symbol_table();

      if (!sym_table.valid())
      {
         return std::numeric_limits<T>::quiet_NaN();
      }

      details::variable_node<T>* var = sym_table.get_variable(variable_name);

      if (var)
      {
         T& x = var->ref();
         const T x_original = x;
         const T result = third_derivative(e, x, h);
         x = x_original;

         return result;
      }
      else
         return std::numeric_limits<T>::quiet_NaN();
   }

   /*
      Note: The following 'compute' routines are simple helpers,
      for quickly setting up the required pieces of code in order
      to evaluate an expression. By virtue of how they operate
      there will be an overhead with regards to their setup and
      teardown and hence should not be used in time critical
      sections of code.
      Furthermore they only assume a small sub set of variables,
      no string variables or user defined functions.
   */
   template <typename T>
   inline bool compute(const std::string& expression_string, T& result)
   {
      // No variables
      symbol_table<T> symbol_table;
      symbol_table.add_constants();

      expression<T> expression;
      expression.register_symbol_table(symbol_table);

      parser<T> parser;

      if (parser.compile(expression_string,expression))
      {
         result = expression.value();

         return true;
      }
      else
         return false;
   }

   template <typename T>
   inline bool compute(const std::string& expression_string,
                       const T& x,
                       T& result)
   {
      // Only 'x'
      static const std::string x_var("x");

      symbol_table<T> symbol_table;
      symbol_table.add_constants();
      symbol_table.add_constant(x_var,x);

      expression<T> expression;
      expression.register_symbol_table(symbol_table);

      parser<T> parser;

      if (parser.compile(expression_string,expression))
      {
         result = expression.value();

         return true;
      }
      else
         return false;
   }

   template <typename T>
   inline bool compute(const std::string& expression_string,
                       const T&x, const T& y,
                       T& result)
   {
      // Only 'x' and 'y'
      static const std::string x_var("x");
      static const std::string y_var("y");

      symbol_table<T> symbol_table;
      symbol_table.add_constants();
      symbol_table.add_constant(x_var,x);
      symbol_table.add_constant(y_var,y);

      expression<T> expression;
      expression.register_symbol_table(symbol_table);

      parser<T> parser;

      if (parser.compile(expression_string,expression))
      {
         result = expression.value();

         return true;
      }
      else
         return false;
   }

   template <typename T>
   inline bool compute(const std::string& expression_string,
                       const T& x, const T& y, const T& z,
                       T& result)
   {
      // Only 'x', 'y' or 'z'
      static const std::string x_var("x");
      static const std::string y_var("y");
      static const std::string z_var("z");

      symbol_table<T> symbol_table;
      symbol_table.add_constants();
      symbol_table.add_constant(x_var,x);
      symbol_table.add_constant(y_var,y);
      symbol_table.add_constant(z_var,z);

      expression<T> expression;
      expression.register_symbol_table(symbol_table);

      parser<T> parser;

      if (parser.compile(expression_string,expression))
      {
         result = expression.value();

         return true;
      }
      else
         return false;
   }

   template <typename T, std::size_t N>
   class polynomial : public ifunction<T>
   {
   private:

      template <typename Type, std::size_t NumberOfCoefficients>
      struct poly_impl { };

      template <typename Type>
      struct poly_impl <Type,12>
      {
         static inline T evaluate(const Type x,
                                  const Type c12, const Type c11, const Type c10, const Type c9, const Type c8,
                                  const Type  c7, const Type  c6, const Type  c5, const Type c4, const Type c3,
                                  const Type  c2, const Type  c1, const Type  c0)
         {
            // p(x) = c_12x^12 + c_11x^11 + c_10x^10 + c_9x^9 + c_8x^8 + c_7x^7 + c_6x^6 + c_5x^5 + c_4x^4 + c_3x^3 + c_2x^2 + c_1x^1 + c_0x^0
            return ((((((((((((c12 * x + c11) * x + c10) * x + c9) * x + c8) * x + c7) * x + c6) * x + c5) * x + c4) * x + c3) * x + c2) * x + c1) * x + c0);
         }
      };

      template <typename Type>
      struct poly_impl <Type,11>
      {
         static inline T evaluate(const Type x,
                                  const Type c11, const Type c10, const Type c9, const Type c8, const Type c7,
                                  const Type c6,  const Type  c5, const Type c4, const Type c3, const Type c2,
                                  const Type c1,  const Type  c0)
         {
            // p(x) = c_11x^11 + c_10x^10 + c_9x^9 + c_8x^8 + c_7x^7 + c_6x^6 + c_5x^5 + c_4x^4 + c_3x^3 + c_2x^2 + c_1x^1 + c_0x^0
            return (((((((((((c11 * x + c10) * x + c9) * x + c8) * x + c7) * x + c6) * x + c5) * x + c4) * x + c3) * x + c2) * x + c1) * x + c0);
         }
      };

      template <typename Type>
      struct poly_impl <Type,10>
      {
         static inline T evaluate(const Type x,
                                  const Type c10, const Type c9, const Type c8, const Type c7, const Type c6,
                                  const Type c5,  const Type c4, const Type c3, const Type c2, const Type c1,
                                  const Type c0)
         {
            // p(x) = c_10x^10 + c_9x^9 + c_8x^8 + c_7x^7 + c_6x^6 + c_5x^5 + c_4x^4 + c_3x^3 + c_2x^2 + c_1x^1 + c_0x^0
            return ((((((((((c10 * x + c9) * x + c8) * x + c7) * x + c6) * x + c5) * x + c4) * x + c3) * x + c2) * x + c1) * x + c0);
         }
      };

      template <typename Type>
      struct poly_impl <Type,9>
      {
         static inline T evaluate(const Type x,
                                  const Type c9, const Type c8, const Type c7, const Type c6, const Type c5,
                                  const Type c4, const Type c3, const Type c2, const Type c1, const Type c0)
         {
            // p(x) = c_9x^9 + c_8x^8 + c_7x^7 + c_6x^6 + c_5x^5 + c_4x^4 + c_3x^3 + c_2x^2 + c_1x^1 + c_0x^0
            return (((((((((c9 * x + c8) * x + c7) * x + c6) * x + c5) * x + c4) * x + c3) * x + c2) * x + c1) * x + c0);
         }
      };

      template <typename Type>
      struct poly_impl <Type,8>
      {
         static inline T evaluate(const Type x,
                                  const Type c8, const Type c7, const Type c6, const Type c5, const Type c4,
                                  const Type c3, const Type c2, const Type c1, const Type c0)
         {
            // p(x) = c_8x^8 + c_7x^7 + c_6x^6 + c_5x^5 + c_4x^4 + c_3x^3 + c_2x^2 + c_1x^1 + c_0x^0
            return ((((((((c8 * x + c7) * x + c6) * x + c5) * x + c4) * x + c3) * x + c2) * x + c1) * x + c0);
         }
      };

      template <typename Type>
      struct poly_impl <Type,7>
      {
         static inline T evaluate(const Type x,
                                  const Type c7, const Type c6, const Type c5, const Type c4, const Type c3,
                                  const Type c2, const Type c1, const Type c0)
         {
            // p(x) = c_7x^7 + c_6x^6 + c_5x^5 + c_4x^4 + c_3x^3 + c_2x^2 + c_1x^1 + c_0x^0
            return (((((((c7 * x + c6) * x + c5) * x + c4) * x + c3) * x + c2) * x + c1) * x + c0);
         }
      };

      template <typename Type>
      struct poly_impl <Type,6>
      {
         static inline T evaluate(const Type x,
                                  const Type c6, const Type c5, const Type c4, const Type c3, const Type c2,
                                  const Type c1, const Type c0)
         {
            // p(x) = c_6x^6 + c_5x^5 + c_4x^4 + c_3x^3 + c_2x^2 + c_1x^1 + c_0x^0
            return ((((((c6 * x + c5) * x + c4) * x + c3) * x + c2) * x + c1) * x + c0);
         }
      };

      template <typename Type>
      struct poly_impl <Type,5>
      {
         static inline T evaluate(const Type x,
                                  const Type c5, const Type c4, const Type c3, const Type c2,
                                  const Type c1, const Type c0)
         {
            // p(x) = c_5x^5 + c_4x^4 + c_3x^3 + c_2x^2 + c_1x^1 + c_0x^0
            return (((((c5 * x + c4) * x + c3) * x + c2) * x + c1) * x + c0);
         }
      };

      template <typename Type>
      struct poly_impl <Type,4>
      {
         static inline T evaluate(const Type x, const Type c4, const Type c3, const Type c2, const Type c1, const Type c0)
         {
            // p(x) = c_4x^4 + c_3x^3 + c_2x^2 + c_1x^1 + c_0x^0
            return ((((c4 * x + c3) * x + c2) * x + c1) * x + c0);
         }
      };

      template <typename Type>
      struct poly_impl <Type,3>
      {
         static inline T evaluate(const Type x, const Type c3, const Type c2, const Type c1, const Type c0)
         {
            // p(x) = c_3x^3 + c_2x^2 + c_1x^1 + c_0x^0
            return (((c3 * x + c2) * x + c1) * x + c0);
         }
      };

      template <typename Type>
      struct poly_impl <Type,2>
      {
         static inline T evaluate(const Type x, const Type c2, const Type c1, const Type c0)
         {
            // p(x) = c_2x^2 + c_1x^1 + c_0x^0
            return ((c2 * x + c1) * x + c0);
         }
      };

      template <typename Type>
      struct poly_impl <Type,1>
      {
         static inline T evaluate(const Type x, const Type c1, const Type c0)
         {
            // p(x) = c_1x^1 + c_0x^0
            return (c1 * x + c0);
         }
      };

   public:

      using ifunction<T>::operator();

      polynomial()
      : ifunction<T>((N+2 <= 20) ? (N + 2) : std::numeric_limits<std::size_t>::max())
      {
         disable_has_side_effects(*this);
      }

      virtual ~polynomial() {}

      #define poly_rtrn(NN) \
      return (NN != N) ? std::numeric_limits<T>::quiet_NaN() :

      inline virtual T operator() (const T& x, const T& c1, const T& c0)
      {
         poly_rtrn(1) (poly_impl<T,1>::evaluate(x, c1, c0));
      }

      inline virtual T operator() (const T& x, const T& c2, const T& c1, const T& c0)
      {
         poly_rtrn(2) (poly_impl<T,2>::evaluate(x, c2, c1, c0));
      }

      inline virtual T operator() (const T& x, const T& c3, const T& c2, const T& c1, const T& c0)
      {
         poly_rtrn(3) (poly_impl<T,3>::evaluate(x, c3, c2, c1, c0));
      }

      inline virtual T operator() (const T& x, const T& c4, const T& c3, const T& c2, const T& c1,
                                   const T& c0)
      {
         poly_rtrn(4) (poly_impl<T,4>::evaluate(x, c4, c3, c2, c1, c0));
      }

      inline virtual T operator() (const T& x, const T& c5, const T& c4, const T& c3, const T& c2,
                                   const T& c1, const T& c0)
      {
         poly_rtrn(5) (poly_impl<T,5>::evaluate(x, c5, c4, c3, c2, c1, c0));
      }

      inline virtual T operator() (const T& x, const T& c6, const T& c5, const T& c4, const T& c3,
                                   const T& c2, const T& c1, const T& c0)
      {
         poly_rtrn(6) (poly_impl<T,6>::evaluate(x, c6, c5, c4, c3, c2, c1, c0));
      }

      inline virtual T operator() (const T& x, const T& c7, const T& c6, const T& c5, const T& c4,
                                   const T& c3, const T& c2, const T& c1, const T& c0)
      {
         poly_rtrn(7) (poly_impl<T,7>::evaluate(x, c7, c6, c5, c4, c3, c2, c1, c0));
      }

      inline virtual T operator() (const T& x, const T& c8, const T& c7, const T& c6, const T& c5,
                                   const T& c4, const T& c3, const T& c2, const T& c1, const T& c0)
      {
         poly_rtrn(8) (poly_impl<T,8>::evaluate(x, c8, c7, c6, c5, c4, c3, c2, c1, c0));
      }

      inline virtual T operator() (const T& x, const T& c9, const T& c8, const T& c7, const T& c6,
                                   const T& c5, const T& c4, const T& c3, const T& c2, const T& c1,
                                   const T& c0)
      {
         poly_rtrn(9) (poly_impl<T,9>::evaluate(x, c9, c8, c7, c6, c5, c4, c3, c2, c1, c0));
      }

      inline virtual T operator() (const T& x, const T& c10, const T& c9, const T& c8, const T& c7,
                                   const T& c6, const T& c5, const T& c4, const T& c3, const T& c2,
                                   const T& c1, const T& c0)
      {
         poly_rtrn(10) (poly_impl<T,10>::evaluate(x, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, c0));
      }

      inline virtual T operator() (const T& x, const T& c11, const T& c10, const T& c9, const T& c8,
                                   const T& c7, const T& c6, const T& c5, const T& c4, const T& c3,
                                   const T& c2, const T& c1, const T& c0)
      {
         poly_rtrn(11) (poly_impl<T,11>::evaluate(x, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, c0));
      }

      inline virtual T operator() (const T& x, const T& c12, const T& c11, const T& c10, const T& c9,
                                   const T& c8, const T& c7, const T& c6, const T& c5, const T& c4,
                                   const T& c3, const T& c2, const T& c1, const T& c0)
      {
         poly_rtrn(12) (poly_impl<T,12>::evaluate(x, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, c0));
      }

      #undef poly_rtrn

      inline virtual T operator() ()
      {
         return std::numeric_limits<T>::quiet_NaN();
      }

      inline virtual T operator() (const T&)
      {
         return std::numeric_limits<T>::quiet_NaN();
      }

      inline virtual T operator() (const T&, const T&)
      {
         return std::numeric_limits<T>::quiet_NaN();
      }
   };

   template <typename T>
   class function_compositor
   {
   public:

      typedef Essa::Math::expression<T>             expression_t;
      typedef Essa::Math::symbol_table<T>           symbol_table_t;
      typedef Essa::Math::parser<T>                 parser_t;
      typedef typename parser_t::settings_store settings_t;

      struct function
      {
         function()
         {}

         function(const std::string& n)
         : name_(n)
         {}

         function(const std::string& name,
                  const std::string& expression)
         : name_(name)
         , expression_(expression)
         {}

         function(const std::string& name,
                  const std::string& expression,
                  const std::string& v0)
         : name_(name)
         , expression_(expression)
         {
            v_.push_back(v0);
         }

         function(const std::string& name,
                  const std::string& expression,
                  const std::string& v0, const std::string& v1)
         : name_(name)
         , expression_(expression)
         {
            v_.push_back(v0); v_.push_back(v1);
         }

         function(const std::string& name,
                  const std::string& expression,
                  const std::string& v0, const std::string& v1,
                  const std::string& v2)
         : name_(name)
         , expression_(expression)
         {
            v_.push_back(v0); v_.push_back(v1);
            v_.push_back(v2);
         }

         function(const std::string& name,
                  const std::string& expression,
                  const std::string& v0, const std::string& v1,
                  const std::string& v2, const std::string& v3)
         : name_(name)
         , expression_(expression)
         {
            v_.push_back(v0); v_.push_back(v1);
            v_.push_back(v2); v_.push_back(v3);
         }

         function(const std::string& name,
                  const std::string& expression,
                  const std::string& v0, const std::string& v1,
                  const std::string& v2, const std::string& v3,
                  const std::string& v4)
         : name_(name)
         , expression_(expression)
         {
            v_.push_back(v0); v_.push_back(v1);
            v_.push_back(v2); v_.push_back(v3);
            v_.push_back(v4);
         }

         inline function& name(const std::string& n)
         {
            name_ = n;
            return (*this);
         }

         inline function& expression(const std::string& e)
         {
            expression_ = e;
            return (*this);
         }

         inline function& var(const std::string& v)
         {
            v_.push_back(v);
            return (*this);
         }

         std::string name_;
         std::string expression_;
         std::deque<std::string> v_;
      };

   private:

      struct base_func : public Essa::Math::ifunction<T>
      {
         typedef const T&                       type;
         typedef Essa::Math::ifunction<T>     function_t;
         typedef std::vector<T*>            varref_t;
         typedef std::vector<T>                var_t;
         typedef std::pair<T*,std::size_t> lvarref_t;
         typedef std::vector<lvarref_t>    lvr_vec_t;

         using Essa::Math::ifunction<T>::operator();

         base_func(const std::size_t& pc = 0)
         : Essa::Math::ifunction<T>(pc)
         , local_var_stack_size(0)
         , stack_depth(0)
         {
            v.resize(pc);
         }

         virtual ~base_func() {}

         #define exprtk_assign(Index)   \
         (*v[Index]) = v##Index; \

         inline void update(const T& v0)
         {
            exprtk_assign(0)
         }

         inline void update(const T& v0, const T& v1)
         {
            exprtk_assign(0) exprtk_assign(1)
         }

         inline void update(const T& v0, const T& v1, const T& v2)
         {
            exprtk_assign(0) exprtk_assign(1)
            exprtk_assign(2)
         }

         inline void update(const T& v0, const T& v1, const T& v2, const T& v3)
         {
            exprtk_assign(0) exprtk_assign(1)
            exprtk_assign(2) exprtk_assign(3)
         }

         inline void update(const T& v0, const T& v1, const T& v2, const T& v3, const T& v4)
         {
            exprtk_assign(0) exprtk_assign(1)
            exprtk_assign(2) exprtk_assign(3)
            exprtk_assign(4)
         }

         inline void update(const T& v0, const T& v1, const T& v2, const T& v3, const T& v4, const T& v5)
         {
            exprtk_assign(0) exprtk_assign(1)
            exprtk_assign(2) exprtk_assign(3)
            exprtk_assign(4) exprtk_assign(5)
         }

         #ifdef exprtk_assign
         #undef exprtk_assign
         #endif

         inline function_t& setup(expression_t& expr)
         {
            expression = expr;

            typedef typename expression_t::control_block::local_data_list_t ldl_t;

            const ldl_t ldl = expr.local_data_list();

            std::vector<std::size_t> index_list;

            for (std::size_t i = 0; i < ldl.size(); ++i)
            {
               if (ldl[i].size)
               {
                  index_list.push_back(i);
               }
            }

            std::size_t input_param_count = 0;

            for (std::size_t i = 0; i < index_list.size(); ++i)
            {
               const std::size_t index = index_list[i];

               if (i < (index_list.size() - v.size()))
               {
                  lv.push_back(
                        std::make_pair(
                           reinterpret_cast<T*>(ldl[index].pointer),
                           ldl[index].size));

                  local_var_stack_size += ldl[index].size;
               }
               else
                  v[input_param_count++] = reinterpret_cast<T*>(ldl[index].pointer);
            }

            clear_stack();

            return (*this);
         }

         inline void pre()
         {
            if (stack_depth++)
            {
               if (!v.empty())
               {
                  var_t var_stack(v.size(),T(0));
                  copy(v,var_stack);
                  param_stack.push_back(var_stack);
               }

               if (!lv.empty())
               {
                  var_t local_var_stack(local_var_stack_size,T(0));
                  copy(lv,local_var_stack);
                  local_stack.push_back(local_var_stack);
               }
            }
         }

         inline void post()
         {
            if (--stack_depth)
            {
               if (!v.empty())
               {
                  copy(param_stack.back(),v);
                  param_stack.pop_back();
               }

               if (!lv.empty())
               {
                  copy(local_stack.back(),lv);
                  local_stack.pop_back();
               }
            }
         }

         void copy(const varref_t& src_v, var_t& dest_v)
         {
            for (std::size_t i = 0; i < src_v.size(); ++i)
            {
               dest_v[i] = (*src_v[i]);
            }
         }

         void copy(const var_t& src_v, varref_t& dest_v)
         {
            for (std::size_t i = 0; i < src_v.size(); ++i)
            {
               (*dest_v[i]) = src_v[i];
            }
         }

         void copy(const lvr_vec_t& src_v, var_t& dest_v)
         {
            typename var_t::iterator itr = dest_v.begin();
            typedef  typename std::iterator_traits<typename var_t::iterator>::difference_type diff_t;

            for (std::size_t i = 0; i < src_v.size(); ++i)
            {
               lvarref_t vr = src_v[i];

               if (1 == vr.second)
                  *itr++ = (*vr.first);
               else
               {
                  std::copy(vr.first, vr.first + vr.second, itr);
                  itr += static_cast<diff_t>(vr.second);
               }
            }
         }

         void copy(const var_t& src_v, lvr_vec_t& dest_v)
         {
            typename var_t::const_iterator itr = src_v.begin();
            typedef  typename std::iterator_traits<typename var_t::iterator>::difference_type diff_t;

            for (std::size_t i = 0; i < src_v.size(); ++i)
            {
               lvarref_t vr = dest_v[i];

               if (1 == vr.second)
                  (*vr.first) = *itr++;
               else
               {
                  std::copy(itr, itr + static_cast<diff_t>(vr.second), vr.first);
                  itr += static_cast<diff_t>(vr.second);
               }
            }
         }

         inline void clear_stack()
         {
            for (std::size_t i = 0; i < v.size(); ++i)
            {
               (*v[i]) = 0;
            }
         }

         inline virtual T value(expression_t& e)
         {
            return e.value();
         }

         expression_t expression;
         varref_t v;
         lvr_vec_t lv;
         std::size_t local_var_stack_size;
         std::size_t stack_depth;
         std::deque<var_t> param_stack;
         std::deque<var_t> local_stack;
      };

      typedef std::map<std::string,base_func*> funcparam_t;

      struct func_0param : public base_func
      {
         using Essa::Math::ifunction<T>::operator();

         func_0param() : base_func(0) {}

         inline T operator() ()
         {
            return this->value(base_func::expression);
         }
      };

      typedef const T& type;

      template <typename BaseFuncType>
      struct scoped_bft
      {
         explicit scoped_bft(BaseFuncType& bft)
         : bft_(bft)
         {
            bft_.pre ();
         }

        ~scoped_bft()
         {
            bft_.post();
         }

         BaseFuncType& bft_;

      private:

         scoped_bft(const scoped_bft&) exprtk_delete;
         scoped_bft& operator=(const scoped_bft&) exprtk_delete;
      };

      struct func_1param : public base_func
      {
         using Essa::Math::ifunction<T>::operator();

         func_1param() : base_func(1) {}

         inline T operator() (type v0)
         {
            scoped_bft<func_1param> sb(*this);
            base_func::update(v0);
            return this->value(base_func::expression);
         }
      };

      struct func_2param : public base_func
      {
         using Essa::Math::ifunction<T>::operator();

         func_2param() : base_func(2) {}

         inline T operator() (type v0, type v1)
         {
            scoped_bft<func_2param> sb(*this);
            base_func::update(v0, v1);
            return this->value(base_func::expression);
         }
      };

      struct func_3param : public base_func
      {
         using Essa::Math::ifunction<T>::operator();

         func_3param() : base_func(3) {}

         inline T operator() (type v0, type v1, type v2)
         {
            scoped_bft<func_3param> sb(*this);
            base_func::update(v0, v1, v2);
            return this->value(base_func::expression);
         }
      };

      struct func_4param : public base_func
      {
         using Essa::Math::ifunction<T>::operator();

         func_4param() : base_func(4) {}

         inline T operator() (type v0, type v1, type v2, type v3)
         {
            scoped_bft<func_4param> sb(*this);
            base_func::update(v0, v1, v2, v3);
            return this->value(base_func::expression);
         }
      };

      struct func_5param : public base_func
      {
         using Essa::Math::ifunction<T>::operator();

         func_5param() : base_func(5) {}

         inline T operator() (type v0, type v1, type v2, type v3, type v4)
         {
            scoped_bft<func_5param> sb(*this);
            base_func::update(v0, v1, v2, v3, v4);
            return this->value(base_func::expression);
         }
      };

      struct func_6param : public base_func
      {
         using Essa::Math::ifunction<T>::operator();

         func_6param() : base_func(6) {}

         inline T operator() (type v0, type v1, type v2, type v3, type v4, type v5)
         {
            scoped_bft<func_6param> sb(*this);
            base_func::update(v0, v1, v2, v3, v4, v5);
            return this->value(base_func::expression);
         }
      };

      static T return_value(expression_t& e)
      {
         typedef Essa::Math::results_context<T> results_context_t;
         typedef typename results_context_t::type_store_t type_t;
         typedef typename type_t::scalar_view scalar_t;

         const T result = e.value();

         if (e.return_invoked())
         {
            // Due to the post compilation checks, it can be safely
            // assumed that there will be at least one parameter
            // and that the first parameter will always be scalar.
            return scalar_t(e.results()[0])();
         }

         return result;
      }

      #define def_fp_retval(N)                               \
      struct func_##N##param_retval : public func_##N##param \
      {                                                      \
         inline T value(expression_t& e)                     \
         {                                                   \
            return return_value(e);                          \
         }                                                   \
      };                                                     \

      def_fp_retval(0)
      def_fp_retval(1)
      def_fp_retval(2)
      def_fp_retval(3)
      def_fp_retval(4)
      def_fp_retval(5)
      def_fp_retval(6)

      template <typename Allocator,
                template <typename, typename> class Sequence>
      inline bool add(const std::string& name,
                      const std::string& expression,
                      const Sequence<std::string,Allocator>& var_list,
                      const bool override = false)
      {
         const typename std::map<std::string,expression_t>::iterator itr = expr_map_.find(name);

         if (expr_map_.end() != itr)
         {
            if (!override)
            {
               exprtk_debug(("Compositor error(add): function '%s' already defined\n",
                             name.c_str()));

               return false;
            }

            remove(name, var_list.size());
         }

         if (compile_expression(name, expression, var_list))
         {
            const std::size_t n = var_list.size();

            fp_map_[n][name]->setup(expr_map_[name]);

            return true;
         }
         else
         {
            exprtk_debug(("Compositor error(add): Failed to compile function '%s'\n",
                          name.c_str()));

            return false;
         }
      }

   public:

      function_compositor()
      : parser_(settings_t::compile_all_opts +
                settings_t::e_disable_zero_return)
      , fp_map_(7)
      {}

      function_compositor(const symbol_table_t& st)
      : symbol_table_(st)
      , parser_(settings_t::compile_all_opts +
                settings_t::e_disable_zero_return)
      , fp_map_(7)
      {}

     ~function_compositor()
      {
         clear();
      }

      inline symbol_table_t& symbol_table()
      {
         return symbol_table_;
      }

      inline const symbol_table_t& symbol_table() const
      {
         return symbol_table_;
      }

      inline void add_auxiliary_symtab(symbol_table_t& symtab)
      {
         auxiliary_symtab_list_.push_back(&symtab);
      }

      void clear()
      {
         symbol_table_.clear();
         expr_map_    .clear();

         for (std::size_t i = 0; i < fp_map_.size(); ++i)
         {
            typename funcparam_t::iterator itr = fp_map_[i].begin();
            typename funcparam_t::iterator end = fp_map_[i].end  ();

            while (itr != end)
            {
               delete itr->second;
               ++itr;
            }

            fp_map_[i].clear();
         }
      }

      inline bool add(const function& f, const bool override = false)
      {
         return add(f.name_, f.expression_, f.v_,override);
      }

   private:

      template <typename Allocator,
                template <typename, typename> class Sequence>
      bool compile_expression(const std::string& name,
                              const std::string& expression,
                              const Sequence<std::string,Allocator>& input_var_list,
                              bool  return_present = false)
      {
         expression_t compiled_expression;
         symbol_table_t local_symbol_table;

         local_symbol_table.load_from(symbol_table_);
         local_symbol_table.add_constants();

         if (!valid(name,input_var_list.size()))
            return false;

         if (!forward(name,
                      input_var_list.size(),
                      local_symbol_table,
                      return_present))
            return false;

         compiled_expression.register_symbol_table(local_symbol_table);

         for (std::size_t i = 0; i < auxiliary_symtab_list_.size(); ++i)
         {
            compiled_expression.register_symbol_table((*auxiliary_symtab_list_[i]));
         }

         std::string mod_expression;

         for (std::size_t i = 0; i < input_var_list.size(); ++i)
         {
            mod_expression += " var " + input_var_list[i] + "{};\n";
         }

         if (
              ('{' == details::front(expression)) &&
              ('}' == details::back (expression))
            )
            mod_expression += "~" + expression + ";";
         else
            mod_expression += "~{" + expression + "};";

         if (!parser_.compile(mod_expression,compiled_expression))
         {
            exprtk_debug(("Compositor Error: %s\n",parser_.error().c_str()));
            exprtk_debug(("Compositor modified expression: \n%s\n",mod_expression.c_str()));

            remove(name,input_var_list.size());

            return false;
         }

         if (!return_present && parser_.dec().return_present())
         {
            remove(name,input_var_list.size());

            return compile_expression(name, expression, input_var_list, true);
         }

         // Make sure every return point has a scalar as its first parameter
         if (parser_.dec().return_present())
         {
            typedef std::vector<std::string> str_list_t;

            str_list_t ret_param_list = parser_.dec().return_param_type_list();

            for (std::size_t i = 0; i < ret_param_list.size(); ++i)
            {
               const std::string& params = ret_param_list[i];

               if (params.empty() || ('T' != params[0]))
               {
                  exprtk_debug(("Compositor Error: Return statement in function '%s' is invalid\n",
                                name.c_str()));

                  remove(name,input_var_list.size());

                  return false;
               }
            }
         }

         expr_map_[name] = compiled_expression;

         Essa::Math::ifunction<T>& ifunc = (*(fp_map_[input_var_list.size()])[name]);

         if (symbol_table_.add_function(name,ifunc))
            return true;
         else
         {
            exprtk_debug(("Compositor Error: Failed to add function '%s' to symbol table\n",
                          name.c_str()));
            return false;
         }
      }

      inline bool symbol_used(const std::string& symbol) const
      {
         return (
                  symbol_table_.is_variable       (symbol) ||
                  symbol_table_.is_stringvar      (symbol) ||
                  symbol_table_.is_function       (symbol) ||
                  symbol_table_.is_vector         (symbol) ||
                  symbol_table_.is_vararg_function(symbol)
                );
      }

      inline bool valid(const std::string& name,
                        const std::size_t& arg_count) const
      {
         if (arg_count > 6)
            return false;
         else if (symbol_used(name))
            return false;
         else if (fp_map_[arg_count].end() != fp_map_[arg_count].find(name))
            return false;
         else
            return true;
      }

      inline bool forward(const std::string& name,
                          const std::size_t& arg_count,
                          symbol_table_t& sym_table,
                          const bool ret_present = false)
      {
         switch (arg_count)
         {
            #define case_stmt(N)                                     \
            case N : (fp_map_[arg_count])[name] =                    \
                     (!ret_present) ? static_cast<base_func*>        \
                                      (new func_##N##param) :        \
                                      static_cast<base_func*>        \
                                      (new func_##N##param_retval) ; \
                     break;                                          \

            case_stmt(0) case_stmt(1) case_stmt(2)
            case_stmt(3) case_stmt(4) case_stmt(5)
            case_stmt(6)
            #undef case_stmt
         }

         Essa::Math::ifunction<T>& ifunc = (*(fp_map_[arg_count])[name]);

         return sym_table.add_function(name,ifunc);
      }

      inline void remove(const std::string& name, const std::size_t& arg_count)
      {
         if (arg_count > 6)
            return;

         const typename std::map<std::string,expression_t>::iterator em_itr = expr_map_.find(name);

         if (expr_map_.end() != em_itr)
         {
            expr_map_.erase(em_itr);
         }

         const typename funcparam_t::iterator fp_itr = fp_map_[arg_count].find(name);

         if (fp_map_[arg_count].end() != fp_itr)
         {
            delete fp_itr->second;
            fp_map_[arg_count].erase(fp_itr);
         }

         symbol_table_.remove_function(name);
      }

   private:

      symbol_table_t symbol_table_;
      parser_t parser_;
      std::map<std::string,expression_t> expr_map_;
      std::vector<funcparam_t> fp_map_;
      std::vector<symbol_table_t*> auxiliary_symtab_list_;
   }; // class function_compositor

} // namespace Essa::Math

#if defined(_WIN32) || defined(__WIN32__) || defined(WIN32)
#   ifndef NOMINMAX
#      define NOMINMAX
#   endif
#   ifndef WIN32_LEAN_AND_MEAN
#      define WIN32_LEAN_AND_MEAN
#   endif
#   include <windows.h>
#   include <ctime>
#else
#   include <ctime>
#   include <sys/time.h>
#   include <sys/types.h>
#endif

namespace Essa::Math
{
   class timer
   {
   public:

      #if defined(_WIN32) || defined(__WIN32__) || defined(WIN32)
      timer()
      : in_use_(false)
      {
         QueryPerformanceFrequency(&clock_frequency_);
      }

      inline void start()
      {
         in_use_ = true;
         QueryPerformanceCounter(&start_time_);
      }

      inline void stop()
      {
         QueryPerformanceCounter(&stop_time_);
         in_use_ = false;
      }

      inline double time() const
      {
         return (1.0 * (stop_time_.QuadPart - start_time_.QuadPart)) / (1.0 * clock_frequency_.QuadPart);
      }

      #else

      timer()
      : in_use_(false)
      {
         start_time_.tv_sec  = 0;
         start_time_.tv_usec = 0;

         stop_time_.tv_sec   = 0;
         stop_time_.tv_usec  = 0;
      }

      inline void start()
      {
         in_use_ = true;
         gettimeofday(&start_time_,0);
      }

      inline void stop()
      {
         gettimeofday(&stop_time_, 0);
         in_use_ = false;
      }

      inline unsigned long long int usec_time() const
      {
         if (!in_use_)
         {
            if (stop_time_.tv_sec >= start_time_.tv_sec)
            {
               return 1000000LLU * static_cast<details::_uint64_t>(stop_time_.tv_sec  - start_time_.tv_sec ) +
                                   static_cast<details::_uint64_t>(stop_time_.tv_usec - start_time_.tv_usec) ;
            }
            else
               return std::numeric_limits<details::_uint64_t>::max();
         }
         else
            return std::numeric_limits<details::_uint64_t>::max();
      }

      inline double time() const
      {
         return usec_time() * 0.000001;
      }

      #endif

      inline bool in_use() const
      {
         return in_use_;
      }

   private:

      bool in_use_;

      #if defined(_WIN32) || defined(__WIN32__) || defined(WIN32)
         LARGE_INTEGER start_time_;
         LARGE_INTEGER stop_time_;
         LARGE_INTEGER clock_frequency_;
      #else
         struct timeval start_time_;
         struct timeval stop_time_;
      #endif
   };

   template <typename T>
   struct type_defs
   {
      typedef symbol_table<T>         symbol_table_t;
      typedef expression<T>           expression_t;
      typedef parser<T>               parser_t;
      typedef parser_error::type      error_t;
      typedef function_compositor<T>  compositor_t;
      typedef typename compositor_t::function function_t;
   };

} // namespace Essa::Math

#ifndef exprtk_disable_rtl_io
namespace Essa::Math
{
   namespace rtl { namespace io { namespace details
   {
      template <typename T>
      inline void print_type(const std::string& fmt,
                             const T v,
                             Essa::Math::details::numeric::details::real_type_tag)
      {
         printf(fmt.c_str(),v);
      }

      template <typename T>
      struct print_impl
      {
         typedef typename igeneric_function<T>::generic_type generic_type;
         typedef typename igeneric_function<T>::parameter_list_t parameter_list_t;
         typedef typename generic_type::scalar_view scalar_t;
         typedef typename generic_type::vector_view vector_t;
         typedef typename generic_type::string_view string_t;
         typedef typename Essa::Math::details::numeric::details::number_type<T>::type num_type;

         static void process(const std::string& scalar_format, parameter_list_t parameters)
         {
            for (std::size_t i = 0; i < parameters.size(); ++i)
            {
               generic_type& gt = parameters[i];

               switch (gt.type)
               {
                  case generic_type::e_scalar : print(scalar_format,scalar_t(gt));
                                                break;

                  case generic_type::e_vector : print(scalar_format,vector_t(gt));
                                                break;

                  case generic_type::e_string : print(string_t(gt));
                                                break;

                  default                     : continue;
               }
            }
         }

         static inline void print(const std::string& scalar_format, const scalar_t& s)
         {
            print_type(scalar_format,s(),num_type());
         }

         static inline void print(const std::string& scalar_format, const vector_t& v)
         {
            for (std::size_t i = 0; i < v.size(); ++i)
            {
               print_type(scalar_format,v[i],num_type());

               if ((i + 1) < v.size())
                  printf(" ");
            }
         }

         static inline void print(const string_t& s)
         {
            printf("%s",to_str(s).c_str());
         }
      };

   } // namespace Essa::Math::rtl::io::details

   template <typename T>
   struct print : public Essa::Math::igeneric_function<T>
   {
      typedef typename igeneric_function<T>::parameter_list_t parameter_list_t;

      using Essa::Math::igeneric_function<T>::operator();

      print(const std::string& scalar_format = "%10.5f")
      : scalar_format_(scalar_format)
      {
         Essa::Math::enable_zero_parameters(*this);
      }

      inline T operator() (parameter_list_t parameters)
      {
         details::print_impl<T>::process(scalar_format_,parameters);
         return T(0);
      }

      std::string scalar_format_;
   };

   template <typename T>
   struct println : public Essa::Math::igeneric_function<T>
   {
      typedef typename igeneric_function<T>::parameter_list_t parameter_list_t;

      using Essa::Math::igeneric_function<T>::operator();

      println(const std::string& scalar_format = "%10.5f")
      : scalar_format_(scalar_format)
      {
         Essa::Math::enable_zero_parameters(*this);
      }

      inline T operator() (parameter_list_t parameters)
      {
         details::print_impl<T>::process(scalar_format_,parameters);
         printf("\n");
         return T(0);
      }

      std::string scalar_format_;
   };

   template <typename T>
   struct package
   {
      print  <T> p;
      println<T> pl;

      bool register_package(Essa::Math::symbol_table<T>& symtab)
      {
         #define exprtk_register_function(FunctionName, FunctionType)             \
         if (!symtab.add_function(FunctionName,FunctionType))                     \
         {                                                                        \
            exprtk_debug((                                                        \
              "Essa::Math::rtl::io::register_package - Failed to add function: %s\n", \
              FunctionName));                                                     \
            return false;                                                         \
         }                                                                        \

         exprtk_register_function("print"  , p )
         exprtk_register_function("println", pl)
         #undef exprtk_register_function

         return true;
      }
   };

   } // namespace Essa::Math::rtl::io
   } // namespace Essa::Math::rtl
}    // namespace Essa::Math
#endif

#ifndef exprtk_disable_rtl_io_file
#include <fstream>
namespace Essa::Math
{
   namespace rtl { namespace io { namespace file { namespace details
   {
      using ::Essa::Math::details::char_ptr;
      using ::Essa::Math::details::char_cptr;

      enum file_mode
      {
         e_error = 0,
         e_read  = 1,
         e_write = 2,
         e_rdwrt = 4
      };

      struct file_descriptor
      {
         file_descriptor(const std::string& fname, const std::string& access)
         : stream_ptr(0)
         , mode(get_file_mode(access))
         , file_name(fname)
         {}

         void*       stream_ptr;
         file_mode   mode;
         std::string file_name;

         bool open()
         {
            if (e_read == mode)
            {
               std::ifstream* stream = new std::ifstream(file_name.c_str(),std::ios::binary);

               if (!(*stream))
               {
                  file_name.clear();
                  delete stream;

                  return false;
               }
               else
                  stream_ptr = stream;

               return true;
            }
            else if (e_write == mode)
            {
               std::ofstream* stream = new std::ofstream(file_name.c_str(),std::ios::binary);

               if (!(*stream))
               {
                  file_name.clear();
                  delete stream;

                  return false;
               }
               else
                  stream_ptr = stream;

               return true;
            }
            else if (e_rdwrt == mode)
            {
               std::fstream* stream = new std::fstream(file_name.c_str(),std::ios::binary);

               if (!(*stream))
               {
                  file_name.clear();
                  delete stream;

                  return false;
               }
               else
                  stream_ptr = stream;

               return true;
            }
            else
               return false;
         }

         template <typename Stream, typename Ptr>
         void close(Ptr& p)
         {
            Stream* stream = reinterpret_cast<Stream*>(p);
            stream->close();
            delete stream;
            p = reinterpret_cast<Ptr>(0);
         }

         bool close()
         {
            switch (mode)
            {
               case e_read  : close<std::ifstream>(stream_ptr);
                              break;

               case e_write : close<std::ofstream>(stream_ptr);
                              break;

               case e_rdwrt : close<std::fstream> (stream_ptr);
                              break;

               default      : return false;
            }

            return true;
         }

         template <typename View>
         bool write(const View& view, const std::size_t amount, const std::size_t offset = 0)
         {
            switch (mode)
            {
               case e_write : reinterpret_cast<std::ofstream*>(stream_ptr)->
                                 write(reinterpret_cast<char_cptr>(view.begin() + offset), amount * sizeof(typename View::value_t));
                              break;

               case e_rdwrt : reinterpret_cast<std::fstream*>(stream_ptr)->
                                 write(reinterpret_cast<char_cptr>(view.begin() + offset) , amount * sizeof(typename View::value_t));
                              break;

               default      : return false;
            }

            return true;
         }

         template <typename View>
         bool read(View& view, const std::size_t amount, const std::size_t offset = 0)
         {
            switch (mode)
            {
               case e_read  : reinterpret_cast<std::ifstream*>(stream_ptr)->
                                 read(reinterpret_cast<char_ptr>(view.begin() + offset), amount * sizeof(typename View::value_t));
                              break;

               case e_rdwrt : reinterpret_cast<std::fstream*>(stream_ptr)->
                                 read(reinterpret_cast<char_ptr>(view.begin() + offset) , amount * sizeof(typename View::value_t));
                              break;

               default      : return false;
            }

            return true;
         }

         bool getline(std::string& s)
         {
            switch (mode)
            {
               case e_read  : return (!!std::getline(*reinterpret_cast<std::ifstream*>(stream_ptr),s));
               case e_rdwrt : return (!!std::getline(*reinterpret_cast<std::fstream* >(stream_ptr),s));
               default      : return false;
            }
         }

         bool eof() const
         {
            switch (mode)
            {
               case e_read  : return reinterpret_cast<std::ifstream*>(stream_ptr)->eof();
               case e_write : return reinterpret_cast<std::ofstream*>(stream_ptr)->eof();
               case e_rdwrt : return reinterpret_cast<std::fstream* >(stream_ptr)->eof();
               default      : return true;
            }
         }

         file_mode get_file_mode(const std::string& access) const
         {
            if (access.empty() || access.size() > 2)
               return e_error;

            std::size_t w_cnt = 0;
            std::size_t r_cnt = 0;

            for (std::size_t i = 0; i < access.size(); ++i)
            {
               switch (std::tolower(access[i]))
               {
                  case 'r' : r_cnt++; break;
                  case 'w' : w_cnt++; break;
                  default  : return e_error;
               }
            }

            if ((0 == r_cnt) && (0 == w_cnt))
               return e_error;
            else if ((r_cnt > 1) || (w_cnt > 1))
               return e_error;
            else if ((1 == r_cnt) && (1 == w_cnt))
               return e_rdwrt;
            else if (1 == r_cnt)
               return e_read;
            else
               return e_write;
         }
      };

      template <typename T>
      file_descriptor* make_handle(T v)
      {
         const std::size_t fd_size    = sizeof(details::file_descriptor*);
         details::file_descriptor* fd = reinterpret_cast<file_descriptor*>(0);

         std::memcpy(reinterpret_cast<char_ptr >(&fd),
                     reinterpret_cast<char_cptr>(&v ),
                     fd_size);
         return fd;
      }

      template <typename T>
      void perform_check()
      {
         #ifdef _MSC_VER
         #pragma warning(push)
         #pragma warning(disable: 4127)
         #endif
         if (sizeof(T) < sizeof(void*))
         {
            throw std::runtime_error("Essa::Math::rtl::io::file - Error - pointer size larger than holder.");
         }
         #ifdef _MSC_VER
         #pragma warning(pop)
         #endif
      }

   } // namespace Essa::Math::rtl::io::file::details

   template <typename T>
   class open : public Essa::Math::igeneric_function<T>
   {
   public:

      typedef typename Essa::Math::igeneric_function<T> igfun_t;
      typedef typename igfun_t::parameter_list_t    parameter_list_t;
      typedef typename igfun_t::generic_type        generic_type;
      typedef typename generic_type::string_view    string_t;

      using Essa::Math::igeneric_function<T>::operator();

      open()
      : Essa::Math::igeneric_function<T>("S|SS")
      { details::perform_check<T>(); }

      inline T operator() (const std::size_t& ps_index, parameter_list_t parameters)
      {
         const std::string file_name = to_str(string_t(parameters[0]));

         if (file_name.empty())
            return T(0);

         if ((1 == ps_index) && (0 == string_t(parameters[1]).size()))
         {
            return T(0);
         }

         const std::string access =
            (0 == ps_index) ? "r" : to_str(string_t(parameters[1]));

         details::file_descriptor* fd = new details::file_descriptor(file_name,access);

         if (fd->open())
         {
            T t = T(0);

            const std::size_t fd_size = sizeof(details::file_descriptor*);

            std::memcpy(reinterpret_cast<char*>(&t ),
                        reinterpret_cast<char*>(&fd),
                        fd_size);
            return t;
         }
         else
         {
            delete fd;
            return T(0);
         }
      }
   };

   template <typename T>
   struct close : public Essa::Math::ifunction<T>
   {
      using Essa::Math::ifunction<T>::operator();

      close()
      : Essa::Math::ifunction<T>(1)
      { details::perform_check<T>(); }

      inline T operator() (const T& v)
      {
         details::file_descriptor* fd = details::make_handle(v);

         if (!fd->close())
            return T(0);

         delete fd;

         return T(1);
      }
   };

   template <typename T>
   class write : public Essa::Math::igeneric_function<T>
   {
   public:

      typedef typename Essa::Math::igeneric_function<T> igfun_t;
      typedef typename igfun_t::parameter_list_t    parameter_list_t;
      typedef typename igfun_t::generic_type        generic_type;
      typedef typename generic_type::string_view    string_t;
      typedef typename generic_type::scalar_view    scalar_t;
      typedef typename generic_type::vector_view    vector_t;

      using Essa::Math::igeneric_function<T>::operator();

      write()
      : igfun_t("TS|TST|TV|TVT")
      { details::perform_check<T>(); }

      inline T operator() (const std::size_t& ps_index, parameter_list_t parameters)
      {
         details::file_descriptor* fd = details::make_handle(scalar_t(parameters[0])());

         switch (ps_index)
         {
            case 0  : {
                         const string_t buffer(parameters[1]);
                         const std::size_t amount = buffer.size();
                         return T(fd->write(buffer, amount) ? 1 : 0);
                      }

            case 1  : {
                         const string_t buffer(parameters[1]);
                         const std::size_t amount =
                                  std::min(buffer.size(),
                                           static_cast<std::size_t>(scalar_t(parameters[2])()));
                         return T(fd->write(buffer, amount) ? 1 : 0);
                      }

            case 2  : {
                         const vector_t vec(parameters[1]);
                         const std::size_t amount = vec.size();
                         return T(fd->write(vec, amount) ? 1 : 0);
                      }

            case 3  : {
                         const vector_t vec(parameters[1]);
                         const std::size_t amount =
                                  std::min(vec.size(),
                                           static_cast<std::size_t>(scalar_t(parameters[2])()));
                         return T(fd->write(vec, amount) ? 1 : 0);
                      }
         }

         return T(0);
      }
   };

   template <typename T>
   class read : public Essa::Math::igeneric_function<T>
   {
   public:

      typedef typename Essa::Math::igeneric_function<T> igfun_t;
      typedef typename igfun_t::parameter_list_t    parameter_list_t;
      typedef typename igfun_t::generic_type        generic_type;
      typedef typename generic_type::string_view    string_t;
      typedef typename generic_type::scalar_view    scalar_t;
      typedef typename generic_type::vector_view    vector_t;

      using Essa::Math::igeneric_function<T>::operator();

      read()
      : igfun_t("TS|TST|TV|TVT")
      { details::perform_check<T>(); }

      inline T operator() (const std::size_t& ps_index, parameter_list_t parameters)
      {
         details::file_descriptor* fd = details::make_handle(scalar_t(parameters[0])());

         switch (ps_index)
         {
            case 0  : {
                         string_t buffer(parameters[1]);
                         const std::size_t amount = buffer.size();
                         return T(fd->read(buffer,amount) ? 1 : 0);
                      }

            case 1  : {
                         string_t buffer(parameters[1]);
                         const std::size_t amount =
                                  std::min(buffer.size(),
                                           static_cast<std::size_t>(scalar_t(parameters[2])()));
                         return T(fd->read(buffer,amount) ? 1 : 0);
                      }

            case 2  : {
                         vector_t vec(parameters[1]);
                         const std::size_t amount = vec.size();
                         return T(fd->read(vec,amount) ? 1 : 0);
                      }

            case 3  : {
                         vector_t vec(parameters[1]);
                         const std::size_t amount =
                                  std::min(vec.size(),
                                           static_cast<std::size_t>(scalar_t(parameters[2])()));
                         return T(fd->read(vec,amount) ? 1 : 0);
                      }
         }

         return T(0);
      }
   };

   template <typename T>
   class getline : public Essa::Math::igeneric_function<T>
   {
   public:

      typedef typename Essa::Math::igeneric_function<T> igfun_t;
      typedef typename igfun_t::parameter_list_t    parameter_list_t;
      typedef typename igfun_t::generic_type        generic_type;
      typedef typename generic_type::string_view    string_t;
      typedef typename generic_type::scalar_view    scalar_t;

      using Essa::Math::igeneric_function<T>::operator();

      getline()
      : igfun_t("T",igfun_t::e_rtrn_string)
      { details::perform_check<T>(); }

      inline T operator() (std::string& result,
                           parameter_list_t parameters)
      {
         details::file_descriptor* fd = details::make_handle(scalar_t(parameters[0])());
         return T(fd->getline(result) ? 1 : 0);
      }
   };

   template <typename T>
   struct eof : public Essa::Math::ifunction<T>
   {
      using Essa::Math::ifunction<T>::operator();

      eof()
      : Essa::Math::ifunction<T>(1)
      { details::perform_check<T>(); }

      inline T operator() (const T& v)
      {
         details::file_descriptor* fd = details::make_handle(v);

         return (fd->eof() ? T(1) : T(0));
      }
   };

   template <typename T>
   struct package
   {
      open   <T> o;
      close  <T> c;
      write  <T> w;
      read   <T> r;
      getline<T> g;
      eof    <T> e;

      bool register_package(Essa::Math::symbol_table<T>& symtab)
      {
         #define exprtk_register_function(FunctionName, FunctionType)                   \
         if (!symtab.add_function(FunctionName,FunctionType))                           \
         {                                                                              \
            exprtk_debug((                                                              \
              "Essa::Math::rtl::io::file::register_package - Failed to add function: %s\n", \
              FunctionName));                                                           \
            return false;                                                               \
         }                                                                              \

         exprtk_register_function("open"    , o)
         exprtk_register_function("close"   , c)
         exprtk_register_function("write"   , w)
         exprtk_register_function("read"    , r)
         exprtk_register_function("getline" , g)
         exprtk_register_function("eof"     , e)
         #undef exprtk_register_function

         return true;
      }
   };

   } // namespace Essa::Math::rtl::io::file
   } // namespace Essa::Math::rtl::io
   } // namespace Essa::Math::rtl
}    // namespace Essa::Math
#endif

#ifndef exprtk_disable_rtl_vecops
namespace Essa::Math
{
   namespace rtl { namespace vecops {

   namespace helper
   {
      template <typename Vector>
      inline bool invalid_range(const Vector& v, const std::size_t r0, const std::size_t r1)
      {
         if (r0 > (v.size() - 1))
            return true;
         else if (r1 > (v.size() - 1))
            return true;
         else if (r1 < r0)
            return true;
         else
            return false;
      }

      template <typename T>
      struct load_vector_range
      {
         typedef typename Essa::Math::igeneric_function<T> igfun_t;
         typedef typename igfun_t::parameter_list_t    parameter_list_t;
         typedef typename igfun_t::generic_type        generic_type;
         typedef typename generic_type::scalar_view    scalar_t;
         typedef typename generic_type::vector_view    vector_t;

         static inline bool process(parameter_list_t& parameters,
                                    std::size_t& r0, std::size_t& r1,
                                    const std::size_t& r0_prmidx,
                                    const std::size_t& r1_prmidx,
                                    const std::size_t vec_idx = 0)
         {
            if (r0_prmidx >= parameters.size())
               return false;

            if (r1_prmidx >= parameters.size())
               return false;

            if (!scalar_t(parameters[r0_prmidx]).to_uint(r0))
               return false;

            if (!scalar_t(parameters[r1_prmidx]).to_uint(r1))
               return false;

            return !invalid_range(vector_t(parameters[vec_idx]), r0, r1);
         }
      };
   }

   namespace details
   {
      template <typename T>
      inline void kahan_sum(T& sum, T& error, const T v)
      {
         const T x = v - error;
         const T y = sum + x;
         error = (y - sum) - x;
         sum = y;
      }

   } // namespace Essa::Math::rtl::details

   template <typename T>
   class all_true : public Essa::Math::igeneric_function<T>
   {
   public:

      typedef typename Essa::Math::igeneric_function<T> igfun_t;
      typedef typename igfun_t::parameter_list_t    parameter_list_t;
      typedef typename igfun_t::generic_type        generic_type;
      typedef typename generic_type::vector_view    vector_t;

      using Essa::Math::igeneric_function<T>::operator();

      all_true()
      : Essa::Math::igeneric_function<T>("V|VTT")
        /*
           Overloads:
           0. V   - vector
           1. VTT - vector, r0, r1
        */
      {}

      inline T operator() (const std::size_t& ps_index, parameter_list_t parameters)
      {
         const vector_t vec(parameters[0]);

         std::size_t r0 = 0;
         std::size_t r1 = vec.size() - 1;

         if (
              (1 == ps_index) &&
              !helper::load_vector_range<T>::process(parameters, r0, r1, 1, 2, 0)
            )
            return std::numeric_limits<T>::quiet_NaN();

         for (std::size_t i = r0; i <= r1; ++i)
         {
            if (vec[i] == T(0))
            {
               return T(0);
            }
         }

         return T(1);
      }
   };

   template <typename T>
   class all_false : public Essa::Math::igeneric_function<T>
   {
   public:

      typedef typename Essa::Math::igeneric_function<T> igfun_t;
      typedef typename igfun_t::parameter_list_t    parameter_list_t;
      typedef typename igfun_t::generic_type        generic_type;
      typedef typename generic_type::vector_view    vector_t;

      using Essa::Math::igeneric_function<T>::operator();

      all_false()
      : Essa::Math::igeneric_function<T>("V|VTT")
        /*
           Overloads:
           0. V   - vector
           1. VTT - vector, r0, r1
        */
      {}

      inline T operator() (const std::size_t& ps_index, parameter_list_t parameters)
      {
         const vector_t vec(parameters[0]);

         std::size_t r0 = 0;
         std::size_t r1 = vec.size() - 1;

         if (
              (1 == ps_index) &&
              !helper::load_vector_range<T>::process(parameters, r0, r1, 1, 2, 0)
            )
            return std::numeric_limits<T>::quiet_NaN();

         for (std::size_t i = r0; i <= r1; ++i)
         {
            if (vec[i] != T(0))
            {
               return T(0);
            }
         }

         return T(1);
      }
   };

   template <typename T>
   class any_true : public Essa::Math::igeneric_function<T>
   {
   public:

      typedef typename Essa::Math::igeneric_function<T> igfun_t;
      typedef typename igfun_t::parameter_list_t    parameter_list_t;
      typedef typename igfun_t::generic_type        generic_type;
      typedef typename generic_type::vector_view    vector_t;

      using Essa::Math::igeneric_function<T>::operator();

      any_true()
      : Essa::Math::igeneric_function<T>("V|VTT")
        /*
           Overloads:
           0. V   - vector
           1. VTT - vector, r0, r1
        */
      {}

      inline T operator() (const std::size_t& ps_index, parameter_list_t parameters)
      {
         const vector_t vec(parameters[0]);

         std::size_t r0 = 0;
         std::size_t r1 = vec.size() - 1;

         if (
              (1 == ps_index) &&
              !helper::load_vector_range<T>::process(parameters, r0, r1, 1, 2, 0)
            )
            return std::numeric_limits<T>::quiet_NaN();

         for (std::size_t i = r0; i <= r1; ++i)
         {
            if (vec[i] != T(0))
            {
               return T(1);
            }
         }

         return T(0);
      }
   };

   template <typename T>
   class any_false : public Essa::Math::igeneric_function<T>
   {
   public:

      typedef typename Essa::Math::igeneric_function<T> igfun_t;
      typedef typename igfun_t::parameter_list_t    parameter_list_t;
      typedef typename igfun_t::generic_type        generic_type;
      typedef typename generic_type::vector_view    vector_t;

      using Essa::Math::igeneric_function<T>::operator();

      any_false()
      : Essa::Math::igeneric_function<T>("V|VTT")
        /*
           Overloads:
           0. V   - vector
           1. VTT - vector, r0, r1
        */
      {}

      inline T operator() (const std::size_t& ps_index, parameter_list_t parameters)
      {
         const vector_t vec(parameters[0]);

         std::size_t r0 = 0;
         std::size_t r1 = vec.size() - 1;

         if (
              (1 == ps_index) &&
              !helper::load_vector_range<T>::process(parameters, r0, r1, 1, 2, 0)
            )
            return std::numeric_limits<T>::quiet_NaN();

         for (std::size_t i = r0; i <= r1; ++i)
         {
            if (vec[i] == T(0))
            {
               return T(1);
            }
         }

         return T(0);
      }
   };

   template <typename T>
   class count : public Essa::Math::igeneric_function<T>
   {
   public:

      typedef typename Essa::Math::igeneric_function<T> igfun_t;
      typedef typename igfun_t::parameter_list_t    parameter_list_t;
      typedef typename igfun_t::generic_type        generic_type;
      typedef typename generic_type::vector_view    vector_t;

      using Essa::Math::igeneric_function<T>::operator();

      count()
      : Essa::Math::igeneric_function<T>("V|VTT")
        /*
           Overloads:
           0. V   - vector
           1. VTT - vector, r0, r1
        */
      {}

      inline T operator() (const std::size_t& ps_index, parameter_list_t parameters)
      {
         const vector_t vec(parameters[0]);

         std::size_t r0 = 0;
         std::size_t r1 = vec.size() - 1;

         if (
              (1 == ps_index) &&
              !helper::load_vector_range<T>::process(parameters, r0, r1, 1, 2, 0)
            )
            return std::numeric_limits<T>::quiet_NaN();

         std::size_t cnt = 0;

         for (std::size_t i = r0; i <= r1; ++i)
         {
            if (vec[i] != T(0)) ++cnt;
         }

         return T(cnt);
      }
   };

   template <typename T>
   class copy : public Essa::Math::igeneric_function<T>
   {
   public:

      typedef typename Essa::Math::igeneric_function<T> igfun_t;
      typedef typename igfun_t::parameter_list_t    parameter_list_t;
      typedef typename igfun_t::generic_type        generic_type;
      typedef typename generic_type::scalar_view    scalar_t;
      typedef typename generic_type::vector_view    vector_t;

      using Essa::Math::igeneric_function<T>::operator();

      copy()
      : Essa::Math::igeneric_function<T>("VV|VTTVTT")
        /*
           Overloads:
           0. VV     - x(vector), y(vector)
           1. VTTVTT - x(vector), xr0, xr1, y(vector), yr0, yr1,
        */
      {}

      inline T operator() (const std::size_t& ps_index, parameter_list_t parameters)
      {
         const vector_t x(parameters[0]);
               vector_t y(parameters[(0 == ps_index) ? 1 : 3]);

         std::size_t xr0 = 0;
         std::size_t xr1 = x.size() - 1;

         std::size_t yr0 = 0;
         std::size_t yr1 = y.size() - 1;

         if (1 == ps_index)
         {
            if (
                 !helper::load_vector_range<T>::process(parameters, xr0, xr1, 1, 2, 0) ||
                 !helper::load_vector_range<T>::process(parameters, yr0, yr1, 4, 5, 3)
               )
               return T(0);
         }

         const std::size_t n = std::min(xr1 - xr0 + 1, yr1 - yr0 + 1);

         std::copy(
            x.begin() + xr0,
            x.begin() + xr0 + n,
            y.begin() + yr0);

         return T(n);
      }
   };

   template <typename T>
   class rol : public Essa::Math::igeneric_function<T>
   {
   public:

      typedef typename Essa::Math::igeneric_function<T> igfun_t;
      typedef typename igfun_t::parameter_list_t    parameter_list_t;
      typedef typename igfun_t::generic_type        generic_type;
      typedef typename generic_type::scalar_view    scalar_t;
      typedef typename generic_type::vector_view    vector_t;

      using Essa::Math::igeneric_function<T>::operator();

      rol()
      : Essa::Math::igeneric_function<T>("VT|VTTT")
        /*
           Overloads:
           0. VT   - vector, N
           1. VTTT - vector, N, r0, r1
        */
      {}

      inline T operator() (const std::size_t& ps_index, parameter_list_t parameters)
      {
         vector_t vec(parameters[0]);

         std::size_t n  = 0;
         std::size_t r0 = 0;
         std::size_t r1 = vec.size() - 1;

         if (!scalar_t(parameters[1]).to_uint(n))
            return T(0);

         if (
              (1 == ps_index) &&
              !helper::load_vector_range<T>::process(parameters, r0, r1, 2, 3, 0)
            )
            return T(0);

         const std::size_t dist  = r1 - r0 + 1;
         const std::size_t shift = n % dist;

         std::rotate(
            vec.begin() + r0,
            vec.begin() + r0 + shift,
            vec.begin() + r1 + 1);

         return T(1);
      }
   };

   template <typename T>
   class ror : public Essa::Math::igeneric_function<T>
   {
   public:

      typedef typename Essa::Math::igeneric_function<T> igfun_t;
      typedef typename igfun_t::parameter_list_t    parameter_list_t;
      typedef typename igfun_t::generic_type        generic_type;
      typedef typename generic_type::scalar_view    scalar_t;
      typedef typename generic_type::vector_view    vector_t;

      using Essa::Math::igeneric_function<T>::operator();

      ror()
      : Essa::Math::igeneric_function<T>("VT|VTTT")
        /*
           Overloads:
           0. VT   - vector, N
           1. VTTT - vector, N, r0, r1
        */
      {}

      inline T operator() (const std::size_t& ps_index, parameter_list_t parameters)
      {
         vector_t vec(parameters[0]);

         std::size_t n  = 0;
         std::size_t r0 = 0;
         std::size_t r1 = vec.size() - 1;

         if (!scalar_t(parameters[1]).to_uint(n))
            return T(0);

         if (
              (1 == ps_index) &&
              !helper::load_vector_range<T>::process(parameters, r0, r1, 2, 3, 0)
            )
            return T(0);

         std::size_t dist  = r1 - r0 + 1;
         std::size_t shift = (dist - (n % dist)) % dist;

         std::rotate(
            vec.begin() + r0,
            vec.begin() + r0 + shift,
            vec.begin() + r1 + 1);

         return T(1);
      }
   };

   template <typename T>
   class shift_left : public Essa::Math::igeneric_function<T>
   {
   public:

      typedef typename Essa::Math::igeneric_function<T> igfun_t;
      typedef typename igfun_t::parameter_list_t    parameter_list_t;
      typedef typename igfun_t::generic_type        generic_type;
      typedef typename generic_type::scalar_view    scalar_t;
      typedef typename generic_type::vector_view    vector_t;

      using Essa::Math::igeneric_function<T>::operator();

      shift_left()
      : Essa::Math::igeneric_function<T>("VT|VTTT")
        /*
           Overloads:
           0. VT   - vector, N
           1. VTTT - vector, N, r0, r1
        */
      {}

      inline T operator() (const std::size_t& ps_index, parameter_list_t parameters)
      {
         vector_t vec(parameters[0]);

         std::size_t n  = 0;
         std::size_t r0 = 0;
         std::size_t r1 = vec.size() - 1;

         if (!scalar_t(parameters[1]).to_uint(n))
            return T(0);

         if (
              (1 == ps_index) &&
              !helper::load_vector_range<T>::process(parameters, r0, r1, 2, 3, 0)
            )
            return T(0);

         const std::size_t dist = r1 - r0 + 1;

         if (n > dist)
            return T(0);

         std::rotate(
            vec.begin() + r0,
            vec.begin() + r0 + n,
            vec.begin() + r1 + 1);

         for (std::size_t i = r1 - n + 1; i <= r1; ++i)
         {
            vec[i] = T(0);
         }

         return T(1);
      }
   };

   template <typename T>
   class shift_right : public Essa::Math::igeneric_function<T>
   {
   public:

      typedef typename Essa::Math::igeneric_function<T> igfun_t;
      typedef typename igfun_t::parameter_list_t    parameter_list_t;
      typedef typename igfun_t::generic_type        generic_type;
      typedef typename generic_type::scalar_view    scalar_t;
      typedef typename generic_type::vector_view    vector_t;

      using Essa::Math::igeneric_function<T>::operator();

      shift_right()
      : Essa::Math::igeneric_function<T>("VT|VTTT")
        /*
           Overloads:
           0. VT   - vector, N
           1. VTTT - vector, N, r0, r1
        */
      {}

      inline T operator() (const std::size_t& ps_index, parameter_list_t parameters)
      {
         vector_t vec(parameters[0]);

         std::size_t n  = 0;
         std::size_t r0 = 0;
         std::size_t r1 = vec.size() - 1;

         if (!scalar_t(parameters[1]).to_uint(n))
            return T(0);

         if (
              (1 == ps_index) &&
              !helper::load_vector_range<T>::process(parameters, r0, r1, 2, 3, 0)
            )
            return T(0);

         const std::size_t dist = r1 - r0 + 1;

         if (n > dist)
            return T(0);

         const std::size_t shift = (dist - (n % dist)) % dist;

         std::rotate(
            vec.begin() + r0,
            vec.begin() + r0 + shift,
            vec.begin() + r1 + 1);

         for (std::size_t i = r0; i < r0 + n; ++i)
         {
            vec[i] = T(0);
         }

         return T(1);
      }
   };

   template <typename T>
   class sort : public Essa::Math::igeneric_function<T>
   {
   public:

      typedef typename Essa::Math::igeneric_function<T> igfun_t;
      typedef typename igfun_t::parameter_list_t    parameter_list_t;
      typedef typename igfun_t::generic_type        generic_type;
      typedef typename generic_type::string_view    string_t;
      typedef typename generic_type::vector_view    vector_t;

      using Essa::Math::igeneric_function<T>::operator();

      sort()
      : Essa::Math::igeneric_function<T>("V|VTT|VS|VSTT")
        /*
           Overloads:
           0. V    - vector
           1. VTT  - vector, r0, r1
           2. VS   - vector, string
           3. VSTT - vector, string, r0, r1
        */
      {}

      inline T operator() (const std::size_t& ps_index, parameter_list_t parameters)
      {
         vector_t vec(parameters[0]);

         std::size_t r0 = 0;
         std::size_t r1 = vec.size() - 1;

         if ((1 == ps_index) && !helper::load_vector_range<T>::process(parameters, r0, r1, 1, 2, 0))
            return T(0);
         if ((3 == ps_index) && !helper::load_vector_range<T>::process(parameters, r0, r1, 2, 3, 0))
            return T(0);

         bool ascending = true;

         if ((2 == ps_index) || (3 == ps_index))
         {
            if (Essa::Math::details::imatch(to_str(string_t(parameters[1])),"ascending"))
               ascending = true;
            else if (Essa::Math::details::imatch(to_str(string_t(parameters[1])),"descending"))
               ascending = false;
            else
               return T(0);
         }

         if (ascending)
            std::sort(
               vec.begin() + r0,
               vec.begin() + r1 + 1,
               std::less<T>());
         else
            std::sort(
               vec.begin() + r0,
               vec.begin() + r1 + 1,
               std::greater<T>());

         return T(1);
      }
   };

   template <typename T>
   class nthelement : public Essa::Math::igeneric_function<T>
   {
   public:

      typedef typename Essa::Math::igeneric_function<T> igfun_t;
      typedef typename igfun_t::parameter_list_t    parameter_list_t;
      typedef typename igfun_t::generic_type        generic_type;
      typedef typename generic_type::scalar_view    scalar_t;
      typedef typename generic_type::vector_view    vector_t;

      using Essa::Math::igeneric_function<T>::operator();

      nthelement()
      : Essa::Math::igeneric_function<T>("VT|VTTT")
        /*
           Overloads:
           0. VT   - vector, nth-element
           1. VTTT - vector, nth-element, r0, r1
        */
      {}

      inline T operator() (const std::size_t& ps_index, parameter_list_t parameters)
      {
         vector_t vec(parameters[0]);

         std::size_t n  = 0;
         std::size_t r0 = 0;
         std::size_t r1 = vec.size() - 1;

         if (!scalar_t(parameters[1]).to_uint(n))
            return T(0);

         if ((1 == ps_index) && !helper::load_vector_range<T>::process(parameters, r0, r1, 2, 3, 0))
            return std::numeric_limits<T>::quiet_NaN();

         std::nth_element(
            vec.begin() + r0,
            vec.begin() + r0 + n ,
            vec.begin() + r1 + 1);

         return T(1);
      }
   };

   template <typename T>
   class iota : public Essa::Math::igeneric_function<T>
   {
   public:

      typedef typename Essa::Math::igeneric_function<T> igfun_t;
      typedef typename igfun_t::parameter_list_t    parameter_list_t;
      typedef typename igfun_t::generic_type        generic_type;
      typedef typename generic_type::scalar_view    scalar_t;
      typedef typename generic_type::vector_view    vector_t;

      using Essa::Math::igeneric_function<T>::operator();

      iota()
      : Essa::Math::igeneric_function<T>("VT|VTT|VTTT|VTTTT")
        /*
           Overloads:
           0. VT    - vector, increment
           1. VTT   - vector, increment, base
           2. VTTTT - vector, increment, r0, r1
           3. VTTTT - vector, increment, base, r0, r1
        */
      {}

      inline T operator() (const std::size_t& ps_index, parameter_list_t parameters)
      {
         vector_t vec(parameters[0]);

         T increment = scalar_t(parameters[1])();
         T base      = ((1 == ps_index) || (3 == ps_index)) ? scalar_t(parameters[2])() : T(0);

         std::size_t r0 = 0;
         std::size_t r1 = vec.size() - 1;

         if ((2 == ps_index) && !helper::load_vector_range<T>::process(parameters, r0, r1, 2, 3, 0))
            return std::numeric_limits<T>::quiet_NaN();
         else if ((3 == ps_index) && !helper::load_vector_range<T>::process(parameters, r0, r1, 3, 4, 0))
            return std::numeric_limits<T>::quiet_NaN();
         else
         {
            long long j = 0;

            for (std::size_t i = r0; i <= r1; ++i, ++j)
            {
               vec[i] = base + (increment * j);
            }
         }

         return T(1);
      }
   };

   template <typename T>
   class sumk : public Essa::Math::igeneric_function<T>
   {
   public:

      typedef typename Essa::Math::igeneric_function<T> igfun_t;
      typedef typename igfun_t::parameter_list_t    parameter_list_t;
      typedef typename igfun_t::generic_type        generic_type;
      typedef typename generic_type::vector_view    vector_t;

      using Essa::Math::igeneric_function<T>::operator();

      sumk()
      : Essa::Math::igeneric_function<T>("V|VTT")
        /*
           Overloads:
           0. V   - vector
           1. VTT - vector, r0, r1
        */
      {}

      inline T operator() (const std::size_t& ps_index, parameter_list_t parameters)
      {
         const vector_t vec(parameters[0]);

         std::size_t r0 = 0;
         std::size_t r1 = vec.size() - 1;

         if ((1 == ps_index) && !helper::load_vector_range<T>::process(parameters, r0, r1, 1, 2, 0))
            return std::numeric_limits<T>::quiet_NaN();

         T result = T(0);
         T error  = T(0);

         for (std::size_t i = r0; i <= r1; ++i)
         {
            details::kahan_sum(result, error, vec[i]);
         }

         return result;
      }
   };

   template <typename T>
   class axpy : public Essa::Math::igeneric_function<T>
   {
   public:

      typedef typename Essa::Math::igeneric_function<T> igfun_t;
      typedef typename igfun_t::parameter_list_t    parameter_list_t;
      typedef typename igfun_t::generic_type        generic_type;
      typedef typename generic_type::scalar_view    scalar_t;
      typedef typename generic_type::vector_view    vector_t;

      using Essa::Math::igeneric_function<T>::operator();

      axpy()
      : Essa::Math::igeneric_function<T>("TVV|TVVTT")
        /*
           y <- ax + y
           Overloads:
           0. TVV   - a, x(vector), y(vector)
           1. TVVTT - a, x(vector), y(vector), r0, r1
        */
      {}

      inline T operator() (const std::size_t& ps_index, parameter_list_t parameters)
      {
         const vector_t x(parameters[1]);
               vector_t y(parameters[2]);

         std::size_t r0 = 0;
         std::size_t r1 = std::min(x.size(),y.size()) - 1;

         if ((1 == ps_index) && !helper::load_vector_range<T>::process(parameters, r0, r1, 3, 4, 1))
            return std::numeric_limits<T>::quiet_NaN();
         else if (helper::invalid_range(y, r0, r1))
            return std::numeric_limits<T>::quiet_NaN();

         const T a = scalar_t(parameters[0])();

         for (std::size_t i = r0; i <= r1; ++i)
         {
            y[i] = (a * x[i]) + y[i];
         }

         return T(1);
      }
   };

   template <typename T>
   class axpby : public Essa::Math::igeneric_function<T>
   {
   public:

      typedef typename Essa::Math::igeneric_function<T> igfun_t;
      typedef typename igfun_t::parameter_list_t    parameter_list_t;
      typedef typename igfun_t::generic_type        generic_type;
      typedef typename generic_type::scalar_view    scalar_t;
      typedef typename generic_type::vector_view    vector_t;

      using Essa::Math::igeneric_function<T>::operator();

      axpby()
      : Essa::Math::igeneric_function<T>("TVTV|TVTVTT")
        /*
           y <- ax + by
           Overloads:
           0. TVTV   - a, x(vector), b, y(vector)
           1. TVTVTT - a, x(vector), b, y(vector), r0, r1
        */
      {}

      inline T operator() (const std::size_t& ps_index, parameter_list_t parameters)
      {
         const vector_t x(parameters[1]);
               vector_t y(parameters[3]);

         std::size_t r0 = 0;
         std::size_t r1 = std::min(x.size(),y.size()) - 1;

         if ((1 == ps_index) && !helper::load_vector_range<T>::process(parameters, r0, r1, 4, 5, 1))
            return std::numeric_limits<T>::quiet_NaN();
         else if (helper::invalid_range(y, r0, r1))
            return std::numeric_limits<T>::quiet_NaN();

         const T a = scalar_t(parameters[0])();
         const T b = scalar_t(parameters[2])();

         for (std::size_t i = r0; i <= r1; ++i)
         {
            y[i] = (a * x[i]) + (b * y[i]);
         }

         return T(1);
      }
   };

   template <typename T>
   class axpyz : public Essa::Math::igeneric_function<T>
   {
   public:

      typedef typename Essa::Math::igeneric_function<T> igfun_t;
      typedef typename igfun_t::parameter_list_t    parameter_list_t;
      typedef typename igfun_t::generic_type        generic_type;
      typedef typename generic_type::scalar_view    scalar_t;
      typedef typename generic_type::vector_view    vector_t;

      using Essa::Math::igeneric_function<T>::operator();

      axpyz()
      : Essa::Math::igeneric_function<T>("TVVV|TVVVTT")
        /*
           z <- ax + y
           Overloads:
           0. TVVV   - a, x(vector), y(vector), z(vector)
           1. TVVVTT - a, x(vector), y(vector), z(vector), r0, r1
        */
      {}

      inline T operator() (const std::size_t& ps_index, parameter_list_t parameters)
      {
         const vector_t x(parameters[1]);
         const vector_t y(parameters[2]);
               vector_t z(parameters[3]);

         std::size_t r0 = 0;
         std::size_t r1 = std::min(x.size(),y.size()) - 1;

         if ((1 == ps_index) && !helper::load_vector_range<T>::process(parameters, r0, r1, 3, 4, 1))
            return std::numeric_limits<T>::quiet_NaN();
         else if (helper::invalid_range(y, r0, r1))
            return std::numeric_limits<T>::quiet_NaN();
         else if (helper::invalid_range(z, r0, r1))
            return std::numeric_limits<T>::quiet_NaN();

         const T a = scalar_t(parameters[0])();

         for (std::size_t i = r0; i <= r1; ++i)
         {
            z[i] = (a * x[i]) + y[i];
         }

         return T(1);
      }
   };

   template <typename T>
   class axpbyz : public Essa::Math::igeneric_function<T>
   {
   public:

      typedef typename Essa::Math::igeneric_function<T> igfun_t;
      typedef typename igfun_t::parameter_list_t    parameter_list_t;
      typedef typename igfun_t::generic_type        generic_type;
      typedef typename generic_type::scalar_view    scalar_t;
      typedef typename generic_type::vector_view    vector_t;

      using Essa::Math::igeneric_function<T>::operator();

      axpbyz()
      : Essa::Math::igeneric_function<T>("TVTVV|TVTVVTT")
        /*
           z <- ax + by
           Overloads:
           0. TVTVV   - a, x(vector), b, y(vector), z(vector)
           1. TVTVVTT - a, x(vector), b, y(vector), z(vector), r0, r1
        */
      {}

      inline T operator() (const std::size_t& ps_index, parameter_list_t parameters)
      {
         const vector_t x(parameters[1]);
         const vector_t y(parameters[3]);
               vector_t z(parameters[4]);

         std::size_t r0 = 0;
         std::size_t r1 = std::min(x.size(),y.size()) - 1;

         if ((1 == ps_index) && !helper::load_vector_range<T>::process(parameters, r0, r1, 4, 5, 1))
            return std::numeric_limits<T>::quiet_NaN();
         else if (helper::invalid_range(y, r0, r1))
            return std::numeric_limits<T>::quiet_NaN();
         else if (helper::invalid_range(z, r0, r1))
            return std::numeric_limits<T>::quiet_NaN();

         const T a = scalar_t(parameters[0])();
         const T b = scalar_t(parameters[2])();

         for (std::size_t i = r0; i <= r1; ++i)
         {
            z[i] = (a * x[i]) + (b * y[i]);
         }

         return T(1);
      }
   };

   template <typename T>
   class axpbz : public Essa::Math::igeneric_function<T>
   {
   public:

      typedef typename Essa::Math::igeneric_function<T> igfun_t;
      typedef typename igfun_t::parameter_list_t    parameter_list_t;
      typedef typename igfun_t::generic_type        generic_type;
      typedef typename generic_type::scalar_view    scalar_t;
      typedef typename generic_type::vector_view    vector_t;

      using Essa::Math::igeneric_function<T>::operator();

      axpbz()
      : Essa::Math::igeneric_function<T>("TVTV|TVTVTT")
        /*
           z <- ax + b
           Overloads:
           0. TVTV   - a, x(vector), b, z(vector)
           1. TVTVTT - a, x(vector), b, z(vector), r0, r1
        */
      {}

      inline T operator() (const std::size_t& ps_index, parameter_list_t parameters)
      {
         const vector_t x(parameters[1]);
               vector_t z(parameters[3]);

         std::size_t r0 = 0;
         std::size_t r1 = x.size() - 1;

         if ((1 == ps_index) && !helper::load_vector_range<T>::process(parameters, r0, r1, 4, 5, 1))
            return std::numeric_limits<T>::quiet_NaN();
         else if (helper::invalid_range(z, r0, r1))
            return std::numeric_limits<T>::quiet_NaN();

         const T a = scalar_t(parameters[0])();
         const T b = scalar_t(parameters[2])();

         for (std::size_t i = r0; i <= r1; ++i)
         {
            z[i] = (a * x[i]) + b;
         }

         return T(1);
      }
   };

   template <typename T>
   class dot : public Essa::Math::igeneric_function<T>
   {
   public:

      typedef typename Essa::Math::igeneric_function<T> igfun_t;
      typedef typename igfun_t::parameter_list_t    parameter_list_t;
      typedef typename igfun_t::generic_type        generic_type;
      typedef typename generic_type::scalar_view    scalar_t;
      typedef typename generic_type::vector_view    vector_t;

      using Essa::Math::igeneric_function<T>::operator();

      dot()
      : Essa::Math::igeneric_function<T>("VV|VVTT")
        /*
           Overloads:
           0. VV   - x(vector), y(vector)
           1. VVTT - x(vector), y(vector), r0, r1
        */
      {}

      inline T operator() (const std::size_t& ps_index, parameter_list_t parameters)
      {
         const vector_t x(parameters[0]);
         const vector_t y(parameters[1]);

         std::size_t r0 = 0;
         std::size_t r1 = std::min(x.size(),y.size()) - 1;

         if ((1 == ps_index) && !helper::load_vector_range<T>::process(parameters, r0, r1, 2, 3, 0))
            return std::numeric_limits<T>::quiet_NaN();
         else if (helper::invalid_range(y, r0, r1))
            return std::numeric_limits<T>::quiet_NaN();

         T result = T(0);

         for (std::size_t i = r0; i <= r1; ++i)
         {
            result += (x[i] * y[i]);
         }

         return result;
      }
   };

   template <typename T>
   class dotk : public Essa::Math::igeneric_function<T>
   {
   public:

      typedef typename Essa::Math::igeneric_function<T> igfun_t;
      typedef typename igfun_t::parameter_list_t    parameter_list_t;
      typedef typename igfun_t::generic_type        generic_type;
      typedef typename generic_type::scalar_view    scalar_t;
      typedef typename generic_type::vector_view    vector_t;

      using Essa::Math::igeneric_function<T>::operator();

      dotk()
      : Essa::Math::igeneric_function<T>("VV|VVTT")
        /*
           Overloads:
           0. VV   - x(vector), y(vector)
           1. VVTT - x(vector), y(vector), r0, r1
        */
      {}

      inline T operator() (const std::size_t& ps_index, parameter_list_t parameters)
      {
         const vector_t x(parameters[0]);
         const vector_t y(parameters[1]);

         std::size_t r0 = 0;
         std::size_t r1 = std::min(x.size(),y.size()) - 1;

         if ((1 == ps_index) && !helper::load_vector_range<T>::process(parameters, r0, r1, 2, 3, 0))
            return std::numeric_limits<T>::quiet_NaN();
         else if (helper::invalid_range(y, r0, r1))
            return std::numeric_limits<T>::quiet_NaN();

         T result = T(0);
         T error  = T(0);

         for (std::size_t i = r0; i <= r1; ++i)
         {
            details::kahan_sum(result, error, (x[i] * y[i]));
         }

         return result;
      }
   };

   template <typename T>
   struct package
   {
      all_true   <T> at;
      all_false  <T> af;
      any_true   <T> nt;
      any_false  <T> nf;
      count      <T>  c;
      copy       <T> cp;
      rol        <T> rl;
      ror        <T> rr;
      shift_left <T> sl;
      shift_right<T> sr;
      sort       <T> st;
      nthelement <T> ne;
      iota       <T> ia;
      sumk       <T> sk;
      axpy       <T> b1_axpy;
      axpby      <T> b1_axpby;
      axpyz      <T> b1_axpyz;
      axpbyz     <T> b1_axpbyz;
      axpbz      <T> b1_axpbz;
      dot        <T> dt;
      dotk       <T> dtk;

      bool register_package(Essa::Math::symbol_table<T>& symtab)
      {
         #define exprtk_register_function(FunctionName, FunctionType)                 \
         if (!symtab.add_function(FunctionName,FunctionType))                         \
         {                                                                            \
            exprtk_debug((                                                            \
              "Essa::Math::rtl::vecops::register_package - Failed to add function: %s\n", \
              FunctionName));                                                         \
            return false;                                                             \
         }                                                                            \

         exprtk_register_function("all_true"     , at       )
         exprtk_register_function("all_false"    , af       )
         exprtk_register_function("any_true"     , nt       )
         exprtk_register_function("any_false"    , nf       )
         exprtk_register_function("count"        , c        )
         exprtk_register_function("copy"         , cp       )
         exprtk_register_function("rotate_left"  , rl       )
         exprtk_register_function("rol"          , rl       )
         exprtk_register_function("rotate_right" , rr       )
         exprtk_register_function("ror"          , rr       )
         exprtk_register_function("shftl"        , sl       )
         exprtk_register_function("shftr"        , sr       )
         exprtk_register_function("sort"         , st       )
         exprtk_register_function("nth_element"  , ne       )
         exprtk_register_function("iota"         , ia       )
         exprtk_register_function("sumk"         , sk       )
         exprtk_register_function("axpy"         , b1_axpy  )
         exprtk_register_function("axpby"        , b1_axpby )
         exprtk_register_function("axpyz"        , b1_axpyz )
         exprtk_register_function("axpbyz"       , b1_axpbyz)
         exprtk_register_function("axpbz"        , b1_axpbz )
         exprtk_register_function("dot"          , dt       )
         exprtk_register_function("dotk"         , dtk      )
         #undef exprtk_register_function

         return true;
      }
   };

   } // namespace Essa::Math::rtl::vecops
   } // namespace Essa::Math::rtl
}    // namespace Essa::Math
#endif

namespace Essa::Math
{
   namespace information
   {
      using ::Essa::Math::details::char_cptr;

      static char_cptr library = "Mathematical Expression Toolkit";
      static char_cptr version = "2.71828182845904523536028747135266"
                                 "2497757247093699959574966967627724"
                                 "0766303535475945713821785251664274"
                                 "2746639193200305992181741359662904";
      static char_cptr date    = "20230101";
      static char_cptr min_cpp = "199711L";

      static inline std::string data()
      {
         static const std::string info_str = std::string(library) +
                                             std::string(" v") + std::string(version) +
                                             std::string(" (") + date + std::string(")") +
                                             std::string(" (") + min_cpp + std::string(")");
         return info_str;
      }

   } // namespace information

   #ifdef exprtk_debug
   #undef exprtk_debug
   #endif

   #ifdef exprtk_error_location
   #undef exprtk_error_location
   #endif

   #ifdef exprtk_disable_fallthrough_begin
   #undef exprtk_disable_fallthrough_begin
   #endif

   #ifdef exprtk_disable_fallthrough_end
   #undef exprtk_disable_fallthrough_end
   #endif

   #ifdef exprtk_override
   #undef exprtk_override
   #endif

   #ifdef exprtk_final
   #undef exprtk_final
   #endif

   #ifdef exprtk_delete
   #undef exprtk_delete
   #endif

} // namespace Essa::Math

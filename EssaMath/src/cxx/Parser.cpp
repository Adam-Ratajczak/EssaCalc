#include "include/Parser.hpp"
#include "include/Operators.hpp"


namespace Essa::Math{
   namespace parser_error
   {
    
        type::type()
         : mode(parser_error::e_unknown)
         , line_no  (0)
         , column_no(0)
         {}

      type make_error(const error_mode mode,
                             const std::string& diagnostic,
                             const std::string& src_location)
      {
         type t;
         t.mode         = mode;
         t.token.type   = lexer::token::e_error;
         t.diagnostic   = diagnostic;
         t.src_location = src_location;
         exprtk_debug(("%s\n",diagnostic .c_str()));
         return t;
      }

      type make_error(const error_mode mode,
                             const lexer::token& tk,
                             const std::string& diagnostic,
                             const std::string& src_location)
      {
         type t;
         t.mode         = mode;
         t.token        = tk;
         t.diagnostic   = diagnostic;
         t.src_location = src_location;
         exprtk_debug(("%s\n",diagnostic .c_str()));
         return t;
      }

      std::string to_str(error_mode mode)
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

      bool update_error(type& error, const std::string& expression)
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

      void dump_error(const type& error)
      {
         printf("Position: %02d   Type: [%s]   Msg: %s\n",
                static_cast<int>(error.token.position),
                Essa::Math::parser_error::to_str(error.mode).c_str(),
                error.diagnostic.c_str());
      }
   }

template<typename T> parser<T>::scope_element::scope_element()
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
         , str_node(0)
         {}

         template<typename T> bool parser<T>::scope_element::operator < (const scope_element& se) const
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

         template<typename T> void parser<T>::scope_element::clear()
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
            str_node  = 0;
         }

        template<typename T> parser<T>::scope_element_manager::scope_element_manager(parser<T>& p)
         : parser_(p)
         , input_param_cnt_(0)
         {}

        template<typename T> std::size_t parser<T>::scope_element_manager::size() const
         {
            return element_.size();
         }

        template<typename T>  bool parser<T>::scope_element_manager::empty() const
         {
            return element_.empty();
         }

         template<typename T> parser<T>::scope_element& parser<T>::scope_element_manager::get_element(const std::size_t& index)
         {
            if (index < element_.size())
               return element_[index];
            else
               return null_element_;
         }

         template<typename T> parser<T>::scope_element& parser<T>::scope_element_manager::get_element(const std::string& var_name,
                                           const std::size_t index)
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

         template<typename T> parser<T>::scope_element& parser<T>::scope_element_manager::get_active_element(const std::string& var_name,
                                                  const std::size_t index)
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

         template<typename T> bool parser<T>::scope_element_manager::add_element(const scope_element& se)
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

         template<typename T> void parser<T>::scope_element_manager::deactivate(const std::size_t& scope_depth)
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

         template<typename T> void parser<T>::scope_element_manager::free_element(scope_element& se)
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

               case scope_element::e_string     : 
                  if(!details::disable_string_capabilities){

                     delete reinterpret_cast<std::string*>(se.data);
                                                  delete se.str_node;
                  }else{
                     return;
                  }
                                                  break;

               default                          : return;
            }

            se.clear();
         }

         template<typename T> void parser<T>::scope_element_manager::cleanup()
         {
            for (std::size_t i = 0; i < element_.size(); ++i)
            {
               free_element(element_[i]);
            }

            element_.clear();

            input_param_cnt_ = 0;
         }

         template<typename T> std::size_t parser<T>::scope_element_manager::next_ip_index()
         {
            return ++input_param_cnt_;
         }

         template<typename T> parser<T>::expression_node_ptr parser<T>::scope_element_manager::get_variable(const T& v)
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
         
         template<typename T> parser<T>::scope_handler::scope_handler(parser<T>& p)
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

        template<typename T> parser<T>::scope_handler::~scope_handler()
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

      template<typename T> parser<T>::stack_limit_handler::stack_limit_handler(parser<T>& p)
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

        template<typename T> parser<T>::stack_limit_handler::~stack_limit_handler()
         {
            parser_.state_.stack_depth--;
         }

        template<typename T> bool parser<T>::stack_limit_handler::operator!()
         {
            return limit_exceeded_;
         }

         template<typename T> bool parser<T>::symtab_store::empty() const
         {
            return symtab_list_.empty();
         }

         template<typename T> void parser<T>::symtab_store::clear()
         {
            symtab_list_.clear();
         }

         template<typename T> bool parser<T>::symtab_store::valid() const
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

         template<typename T> bool parser<T>::symtab_store::valid_symbol(const std::string& symbol) const
         {
            if (!symtab_list_.empty())
               return symtab_list_[0].valid_symbol(symbol);
            else
               return false;
         }

         template<typename T> bool parser<T>::symtab_store::valid_function_name(const std::string& symbol) const
         {
            if (!symtab_list_.empty())
               return symtab_list_[0].valid_function(symbol);
            else
               return false;
         }

         template<typename T> parser<T>::symtab_store::variable_context parser<T>::symtab_store::get_variable_context(const std::string& variable_name) const
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

         template<typename T> parser<T>::symtab_store::variable_ptr parser<T>::symtab_store::get_variable(const std::string& variable_name) const
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

         template<typename T> parser<T>::symtab_store::variable_ptr parser<T>::symtab_store::get_variable(const T& var_ref) const
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

         template<typename T> parser<T>::symtab_store::string_context parser<T>::symtab_store::get_string_context(const std::string& string_name) const
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

         template<typename T> parser<T>::symtab_store::stringvar_ptr parser<T>::symtab_store::get_stringvar(const std::string& string_name) const
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

         template<typename T> parser<T>::symtab_store::function_ptr parser<T>::symtab_store::get_function(const std::string& function_name) const
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

         template<typename T> parser<T>::symtab_store::vararg_function_ptr parser<T>::symtab_store::get_vararg_function(const std::string& vararg_function_name) const
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

         template<typename T> parser<T>::symtab_store::generic_function_ptr parser<T>::symtab_store::get_generic_function(const std::string& function_name) const
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

         template<typename T> parser<T>::symtab_store::generic_function_ptr parser<T>::symtab_store::get_string_function(const std::string& function_name) const
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

         template<typename T> parser<T>::symtab_store::generic_function_ptr parser<T>::symtab_store::get_overload_function(const std::string& function_name) const
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

         template<typename T> parser<T>::symtab_store::vector_context parser<T>::symtab_store::get_vector_context(const std::string& vector_name) const
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

         template<typename T> parser<T>::symtab_store::vector_holder_ptr parser<T>::symtab_store::get_vector(const std::string& vector_name) const
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

         template<typename T> bool parser<T>::symtab_store::is_constant_node(const std::string& symbol_name) const
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

         template<typename T> bool parser<T>::symtab_store::is_constant_string(const std::string& symbol_name) const
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

         template<typename T> bool parser<T>::symtab_store::symbol_exists(const std::string& symbol) const
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

         template<typename T> bool parser<T>::symtab_store::is_variable(const std::string& variable_name) const
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

         template<typename T> bool parser<T>::symtab_store::is_stringvar(const std::string& stringvar_name) const
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

         template<typename T> bool parser<T>::symtab_store::is_conststr_stringvar(const std::string& symbol_name) const
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

         template<typename T> bool parser<T>::symtab_store::is_function(const std::string& function_name) const
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

         template<typename T> bool parser<T>::symtab_store::is_vararg_function(const std::string& vararg_function_name) const
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

         template<typename T> bool parser<T>::symtab_store::is_vector(const std::string& vector_name) const
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

         template<typename T> std::string parser<T>::symtab_store::get_variable_name(const expression_node_ptr& ptr) const
         {
            return local_data().variable_store.entity_name(ptr);
         }

         template<typename T> std::string parser<T>::symtab_store::get_vector_name(const vector_holder_ptr& ptr) const
         {
            return local_data().vector_store.entity_name(ptr);
         }

         template<typename T> std::string parser<T>::symtab_store::get_stringvar_name(const expression_node_ptr& ptr) const
         {
            return local_data().stringvar_store.entity_name(ptr);
         }

         template<typename T> std::string parser<T>::symtab_store::get_conststr_stringvar_name(const expression_node_ptr& ptr) const
         {
            return local_data().stringvar_store.entity_name(ptr);
         }

         template<typename T> parser<T>::symtab_store::local_data_t& parser<T>::symtab_store::local_data(const std::size_t& index)
         {
            return symtab_list_[index].local_data();
         }

         template<typename T> const parser<T>::symtab_store::local_data_t& parser<T>::symtab_store::local_data(const std::size_t& index) const
         {
            return symtab_list_[index].local_data();
         }

         template<typename T> parser<T>::symbol_table_t& parser<T>::symtab_store::get_symbol_table(const std::size_t& index)
         {
            return symtab_list_[index];
         }

         template<typename T> parser<T>::parser_state::parser_state()
         : type_check_enabled(true)
         {
            reset();
         }

         template<typename T> void parser<T>::parser_state::reset()
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
         template<typename T> void parser<T>::parser_state::activate_side_effect(const std::string&)
         #else
         template<typename T> void parser<T>::parser_state::activate_side_effect(const std::string& source)
         #endif
         {
            if (!side_effect_present)
            {
               side_effect_present = true;

               exprtk_debug(("activate_side_effect() - caller: %s\n",source.c_str()));
            }
         }

         template<typename T> bool parser<T>::unknown_symbol_resolver::process(const std::string& /*unknown_symbol*/,
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

         template<typename T> bool parser<T>::unknown_symbol_resolver::process(const std::string& /* unknown_symbol */,
                              symbol_table_t&    /* symbol_table   */,
                              std::string&       /* error_message  */)
         {
            return false;
         }

         template<typename T> parser<T>::dependent_entity_collector::dependent_entity_collector(const std::size_t options)
         : options_(options)
         , collect_variables_  ((options_ & e_ct_variables  ) == e_ct_variables  )
         , collect_functions_  ((options_ & e_ct_functions  ) == e_ct_functions  )
         , collect_assignments_((options_ & e_ct_assignments) == e_ct_assignments)
         , return_present_   (false)
         , final_stmt_return_(false)
         {}

         template<typename T> void parser<T>::dependent_entity_collector::clear()
         {
            symbol_name_list_    .clear();
            assignment_name_list_.clear();
            retparam_list_       .clear();
            return_present_    = false;
            final_stmt_return_ = false;
         }

         template<typename T> bool& parser<T>::dependent_entity_collector::collect_variables()
         {
            return collect_variables_;
         }

         template<typename T> bool& parser<T>::dependent_entity_collector::collect_functions()
         {
            return collect_functions_;
         }

         template<typename T> bool& parser<T>::dependent_entity_collector::collect_assignments()
         {
            return collect_assignments_;
         }

         template<typename T> bool parser<T>::dependent_entity_collector::return_present() const
         {
            return return_present_;
         }

         template<typename T> bool parser<T>::dependent_entity_collector::final_stmt_return() const
         {
            return final_stmt_return_;
         }

         template<typename T> parser<T>::dependent_entity_collector::retparam_list_t parser<T>::dependent_entity_collector::return_param_type_list() const
         {
            return retparam_list_;
         }

         template<typename T> void parser<T>::dependent_entity_collector::add_symbol(const std::string& symbol, const symbol_type st)
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

         template<typename T> void parser<T>::dependent_entity_collector::add_assignment(const std::string& symbol, const symbol_type st)
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

         template<typename T> const std::size_t parser<T>::settings_store::compile_all_opts =
                                     e_replacer          +
                                     e_joiner            +
                                     e_numeric_check     +
                                     e_bracket_check     +
                                     e_sequence_check    +
                                     e_commutative_check +
                                     e_strength_reduction;

         template<typename T> parser<T>::settings_store::settings_store(const std::size_t compile_options)
         : max_stack_depth_(400)
         , max_node_depth_(10000)
         {
           load_compile_options(compile_options);
         }

         template<typename T> parser<T>::settings_store& parser<T>::settings_store::enable_all_base_functions()
         {
            disabled_func_set_.clear();
            return (*this);
         }

         template<typename T> parser<T>::settings_store& parser<T>::settings_store::enable_all_control_structures()
         {
            disabled_ctrl_set_.clear();
            return (*this);
         }

         template<typename T> parser<T>::settings_store& parser<T>::settings_store::enable_all_logic_ops()
         {
            disabled_logic_set_.clear();
            return (*this);
         }

         template<typename T> parser<T>::settings_store& parser<T>::settings_store::enable_all_arithmetic_ops()
         {
            disabled_arithmetic_set_.clear();
            return (*this);
         }

         template<typename T> parser<T>::settings_store& parser<T>::settings_store::enable_all_assignment_ops()
         {
            disabled_assignment_set_.clear();
            return (*this);
         }

         template<typename T> parser<T>::settings_store& parser<T>::settings_store::enable_all_inequality_ops()
         {
            disabled_inequality_set_.clear();
            return (*this);
         }

         template<typename T> parser<T>::settings_store& parser<T>::settings_store::enable_local_vardef()
         {
            disable_vardef_ = false;
            return (*this);
         }

         template<typename T> parser<T>::settings_store& parser<T>::settings_store::disable_all_base_functions()
         {
            std::copy(details::base_function_list,
                      details::base_function_list + details::base_function_list_size,
                      std::insert_iterator<disabled_entity_set_t>
                        (disabled_func_set_, disabled_func_set_.begin()));
            return (*this);
         }

         template<typename T> parser<T>::settings_store& parser<T>::settings_store::disable_all_control_structures()
         {
            std::copy(details::cntrl_struct_list,
                      details::cntrl_struct_list + details::cntrl_struct_list_size,
                      std::insert_iterator<disabled_entity_set_t>
                        (disabled_ctrl_set_, disabled_ctrl_set_.begin()));
            return (*this);
         }

         template<typename T> parser<T>::settings_store& parser<T>::settings_store::disable_all_logic_ops()
         {
            std::copy(details::logic_ops_list,
                      details::logic_ops_list + details::logic_ops_list_size,
                      std::insert_iterator<disabled_entity_set_t>
                        (disabled_logic_set_, disabled_logic_set_.begin()));
            return (*this);
         }

         template<typename T> parser<T>::settings_store& parser<T>::settings_store::disable_all_arithmetic_ops()
         {
            std::copy(details::arithmetic_ops_list,
                      details::arithmetic_ops_list + details::arithmetic_ops_list_size,
                      std::insert_iterator<disabled_entity_set_t>
                        (disabled_arithmetic_set_, disabled_arithmetic_set_.begin()));
            return (*this);
         }

         template<typename T> parser<T>::settings_store& parser<T>::settings_store::disable_all_assignment_ops()
         {
            std::copy(details::assignment_ops_list,
                      details::assignment_ops_list + details::assignment_ops_list_size,
                      std::insert_iterator<disabled_entity_set_t>
                        (disabled_assignment_set_, disabled_assignment_set_.begin()));
            return (*this);
         }

         template<typename T> parser<T>::settings_store& parser<T>::settings_store::disable_all_inequality_ops()
         {
            std::copy(details::inequality_ops_list,
                      details::inequality_ops_list + details::inequality_ops_list_size,
                      std::insert_iterator<disabled_entity_set_t>
                        (disabled_inequality_set_, disabled_inequality_set_.begin()));
            return (*this);
         }

         template<typename T> parser<T>::settings_store& parser<T>::settings_store::disable_local_vardef()
         {
            disable_vardef_ = true;
            return (*this);
         }

         template<typename T> bool parser<T>::settings_store::replacer_enabled           () const { return enable_replacer_;           }
         template<typename T> bool parser<T>::settings_store::commutative_check_enabled  () const { return enable_commutative_check_;  }
         template<typename T> bool parser<T>::settings_store::joiner_enabled             () const { return enable_joiner_;             }
         template<typename T> bool parser<T>::settings_store::numeric_check_enabled      () const { return enable_numeric_check_;      }
         template<typename T> bool parser<T>::settings_store::bracket_check_enabled      () const { return enable_bracket_check_;      }
         template<typename T> bool parser<T>::settings_store::sequence_check_enabled     () const { return enable_sequence_check_;     }
         template<typename T> bool parser<T>::settings_store::strength_reduction_enabled () const { return enable_strength_reduction_; }
         template<typename T> bool parser<T>::settings_store::collect_variables_enabled  () const { return enable_collect_vars_;       }
         template<typename T> bool parser<T>::settings_store::collect_functions_enabled  () const { return enable_collect_funcs_;      }
         template<typename T> bool parser<T>::settings_store::collect_assignments_enabled() const { return enable_collect_assings_;    }
         template<typename T> bool parser<T>::settings_store::vardef_disabled            () const { return disable_vardef_;            }
         template<typename T> bool parser<T>::settings_store::rsrvd_sym_usr_disabled     () const { return disable_rsrvd_sym_usr_;     }
         template<typename T> bool parser<T>::settings_store::zero_return_disabled       () const { return disable_zero_return_;       }

         template<typename T> bool parser<T>::settings_store::function_enabled(const std::string& function_name) const
         {
            if (disabled_func_set_.empty())
               return true;
            else
               return (disabled_func_set_.end() == disabled_func_set_.find(function_name));
         }

         template<typename T> bool parser<T>::settings_store::control_struct_enabled(const std::string& control_struct) const
         {
            if (disabled_ctrl_set_.empty())
               return true;
            else
               return (disabled_ctrl_set_.end() == disabled_ctrl_set_.find(control_struct));
         }

         template<typename T> bool parser<T>::settings_store::logic_enabled(const std::string& logic_operation) const
         {
            if (disabled_logic_set_.empty())
               return true;
            else
               return (disabled_logic_set_.end() == disabled_logic_set_.find(logic_operation));
         }

         template<typename T> bool parser<T>::settings_store::arithmetic_enabled(const details::operator_type& arithmetic_operation) const
         {
            if (disabled_logic_set_.empty())
               return true;
            else
               return disabled_arithmetic_set_.end() == disabled_arithmetic_set_
                                                            .find(arith_opr_to_string(arithmetic_operation));
         }

         template<typename T> bool parser<T>::settings_store::assignment_enabled(const details::operator_type& assignment) const
         {
            if (disabled_assignment_set_.empty())
               return true;
            else
               return disabled_assignment_set_.end() == disabled_assignment_set_
                                                           .find(assign_opr_to_string(assignment));
         }

         template<typename T> bool parser<T>::settings_store::inequality_enabled(const details::operator_type& inequality) const
         {
            if (disabled_inequality_set_.empty())
               return true;
            else
               return disabled_inequality_set_.end() == disabled_inequality_set_
                                                           .find(inequality_opr_to_string(inequality));
         }

         template<typename T> bool parser<T>::settings_store::function_disabled(const std::string& function_name) const
         {
            if (disabled_func_set_.empty())
               return false;
            else
               return (disabled_func_set_.end() != disabled_func_set_.find(function_name));
         }

         template<typename T> bool parser<T>::settings_store::control_struct_disabled(const std::string& control_struct) const
         {
            if (disabled_ctrl_set_.empty())
               return false;
            else
               return (disabled_ctrl_set_.end() != disabled_ctrl_set_.find(control_struct));
         }

         template<typename T> bool parser<T>::settings_store::logic_disabled(const std::string& logic_operation) const
         {
            if (disabled_logic_set_.empty())
               return false;
            else
               return (disabled_logic_set_.end() != disabled_logic_set_.find(logic_operation));
         }

         template<typename T> bool parser<T>::settings_store::assignment_disabled(const details::operator_type assignment_operation) const
         {
            if (disabled_assignment_set_.empty())
               return false;
            else
               return disabled_assignment_set_.end() != disabled_assignment_set_
                                                           .find(assign_opr_to_string(assignment_operation));
         }

         template<typename T> bool parser<T>::settings_store::logic_disabled(const details::operator_type logic_operation) const
         {
            if (disabled_logic_set_.empty())
               return false;
            else
               return disabled_logic_set_.end() != disabled_logic_set_
                                                           .find(logic_opr_to_string(logic_operation));
         }

         template<typename T> bool parser<T>::settings_store::arithmetic_disabled(const details::operator_type arithmetic_operation) const
         {
            if (disabled_arithmetic_set_.empty())
               return false;
            else
               return disabled_arithmetic_set_.end() != disabled_arithmetic_set_
                                                           .find(arith_opr_to_string(arithmetic_operation));
         }

         template<typename T> bool parser<T>::settings_store::inequality_disabled(const details::operator_type& inequality) const
         {
            if (disabled_inequality_set_.empty())
               return false;
            else
               return disabled_inequality_set_.end() != disabled_inequality_set_
                                                           .find(inequality_opr_to_string(inequality));
         }

         template<typename T> parser<T>::settings_store& parser<T>::settings_store::disable_base_function(settings_base_funcs bf)
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

         template<typename T> parser<T>::settings_store& parser<T>::settings_store::disable_control_structure(settings_control_structs ctrl_struct)
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

         template<typename T> parser<T>::settings_store& parser<T>::settings_store::disable_logic_operation(settings_logic_opr logic)
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

         template<typename T> parser<T>::settings_store& parser<T>::settings_store::disable_arithmetic_operation(settings_arithmetic_opr arithmetic)
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

         template<typename T> parser<T>::settings_store& parser<T>::settings_store::disable_assignment_operation(settings_assignment_opr assignment)
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

         template<typename T> parser<T>::settings_store& parser<T>::settings_store::disable_inequality_operation(settings_inequality_opr inequality)
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

         template<typename T> parser<T>::settings_store& parser<T>::settings_store::enable_base_function(settings_base_funcs bf)
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

         template<typename T> parser<T>::settings_store& parser<T>::settings_store::enable_control_structure(settings_control_structs ctrl_struct)
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

         template<typename T> parser<T>::settings_store& parser<T>::settings_store::enable_logic_operation(settings_logic_opr logic)
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

         template<typename T> parser<T>::settings_store& parser<T>::settings_store::enable_arithmetic_operation(settings_arithmetic_opr arithmetic)
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

         template<typename T> parser<T>::settings_store& parser<T>::settings_store::enable_assignment_operation(settings_assignment_opr assignment)
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

         template<typename T> parser<T>::settings_store& parser<T>::settings_store::enable_inequality_operation(settings_inequality_opr inequality)
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

         template<typename T> void parser<T>::settings_store::set_max_stack_depth(const std::size_t max_stack_depth)
         {
            max_stack_depth_ = max_stack_depth;
         }

         template<typename T> void parser<T>::settings_store::set_max_node_depth(const std::size_t max_node_depth)
         {
            max_node_depth_ = max_node_depth;
         }

         template<typename T> void parser<T>::settings_store::load_compile_options(const std::size_t compile_options)
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

         template<typename T> std::string parser<T>::settings_store::assign_opr_to_string(details::operator_type opr) const
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

         template<typename T> std::string parser<T>::settings_store::arith_opr_to_string(details::operator_type opr) const
         {
            switch (opr)
            {
               case details::e_add : return "+";
               case details::e_sub : return "-";
               case details::e_mul : return "*";
               case details::e_div : return "/";
               case details::e_mod : return "mod";
               default             : return "" ;
            }
         }

         template<typename T> std::string parser<T>::settings_store::inequality_opr_to_string(details::operator_type opr) const
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

         template<typename T> std::string parser<T>::settings_store::logic_opr_to_string(details::operator_type opr) const
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

      template<typename T> parser<T>::parser(const settings_t& settings)
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
        settings_.disable_all_logic_ops();

        settings_.disable_arithmetic_operation(settings_t::e_arith_mod);

        settings_.disable_inequality_operation(settings_t::e_ineq_eq);
        settings_.disable_inequality_operation(settings_t::e_ineq_nequal);

        settings_.disable_base_function(settings_t::e_bf_and);
        settings_.disable_base_function(settings_t::e_bf_avg);
        settings_.disable_base_function(settings_t::e_bf_break);
        settings_.disable_base_function(settings_t::e_bf_case);
        settings_.disable_base_function(settings_t::e_bf_ceil);
        settings_.disable_base_function(settings_t::e_bf_clamp);
        settings_.disable_base_function(settings_t::e_bf_continue);
        settings_.disable_base_function(settings_t::e_bf_default);
        settings_.disable_base_function(settings_t::e_bf_deg2grad);
        settings_.disable_base_function(settings_t::e_bf_deg2rad);
        settings_.disable_base_function(settings_t::e_bf_equal);
        settings_.disable_base_function(settings_t::e_bf_false);
        settings_.disable_base_function(settings_t::e_bf_floor);
        settings_.disable_base_function(settings_t::e_bf_for);
        settings_.disable_base_function(settings_t::e_bf_frac);
        settings_.disable_base_function(settings_t::e_bf_grad2deg);
        settings_.disable_base_function(settings_t::e_bf_hypot);
        settings_.disable_base_function(settings_t::e_bf_iclamp);
        settings_.disable_base_function(settings_t::e_bf_if);
        settings_.disable_base_function(settings_t::e_bf_else);
        settings_.disable_base_function(settings_t::e_bf_ilike);
        settings_.disable_base_function(settings_t::e_bf_in);
        settings_.disable_base_function(settings_t::e_bf_inrange);
        settings_.disable_base_function(settings_t::e_bf_like);
        settings_.disable_base_function(settings_t::e_bf_mand);
        settings_.disable_base_function(settings_t::e_bf_max);
        settings_.disable_base_function(settings_t::e_bf_min);
        settings_.disable_base_function(settings_t::e_bf_mod);
        settings_.disable_base_function(settings_t::e_bf_mor);
        settings_.disable_base_function(settings_t::e_bf_mul);
        settings_.disable_base_function(settings_t::e_bf_nand);
        settings_.disable_base_function(settings_t::e_bf_nor);
        settings_.disable_base_function(settings_t::e_bf_not);
        settings_.disable_base_function(settings_t::e_bf_not_equal);
        settings_.disable_base_function(settings_t::e_bf_null);
        settings_.disable_base_function(settings_t::e_bf_or);
        settings_.disable_base_function(settings_t::e_bf_rad2deg);
        settings_.disable_base_function(settings_t::e_bf_repeat);
        settings_.disable_base_function(settings_t::e_bf_return);
        settings_.disable_base_function(settings_t::e_bf_round);
        settings_.disable_base_function(settings_t::e_bf_roundn);
        settings_.disable_base_function(settings_t::e_bf_sgn);
        settings_.disable_base_function(settings_t::e_bf_shl);
        settings_.disable_base_function(settings_t::e_bf_shr);
        settings_.disable_base_function(settings_t::e_bf_sum);
        settings_.disable_base_function(settings_t::e_bf_swap);
        settings_.disable_base_function(settings_t::e_bf_switch);
        settings_.disable_base_function(settings_t::e_bf_true);
        settings_.disable_base_function(settings_t::e_bf_trunc);
        settings_.disable_base_function(settings_t::e_bf_until);
        settings_.disable_base_function(settings_t::e_bf_var);
        settings_.disable_base_function(settings_t::e_bf_while);
        settings_.disable_base_function(settings_t::e_bf_xnor);
        settings_.disable_base_function(settings_t::e_bf_xor);
        settings_.disable_base_function(settings_t::e_bf_and2);
        settings_.disable_base_function(settings_t::e_bf_or2);
      }

      template <typename T> void parser<T>::init_precompilation()
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

      template<typename T> bool parser<T>::compile(const std::string& expression_string, expression<T>& expr)
      {
         for(size_t i = 0; i < 2; i++){
            if(i == 0){
               details::disable_enhanced_features = false;
               details::disable_cardinal_pow_optimisation = false;
            }else{
               details::disable_enhanced_features = true;
               details::disable_cardinal_pow_optimisation = true;
            }

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

               if(i == 0){
                  expr.set_expression(e);
                  expr.set_retinvk(retinvk_ptr);
               }else{
                  expr.set_unoptimized_expr(e);
               }
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
         
         register_local_vars(expr);
         register_return_results(expr);
         details::disable_enhanced_features = false;
         details::disable_cardinal_pow_optimisation = false;
         return !(!expr);
      }

      template<typename T> parser<T>::expression_t parser<T>::compile(const std::string& expression_string, parser<T>::symbol_table_t& symtab)
      {
         expression_t expression;
         expression.register_symbol_table(symtab);
         compile(expression_string,expression);
         return expression;
      }

      template<typename T> void parser<T>::process_lexer_errors()
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

      template<typename T> bool parser<T>::run_assemblies()
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

      // settings_store& settings()
      // {
      //    return settings_;
      // }

      template<typename T> parser_error::type parser<T>::get_error(const std::size_t& index) const
      {
         if (index < error_list_.size())
            return error_list_[index];
         else
            throw std::invalid_argument("parser::get_error() - Invalid error index specificed");
      }

      template <typename T> std::string parser<T>::error() const
      {
         if (!error_list_.empty())
         {
            return error_list_[0].diagnostic;
         }
         else
            return std::string("No Error");
      }

      template<typename T> std::size_t parser<T>::error_count() const
      {
         return error_list_.size();
      }

      template<typename T> parser<T>::dependent_entity_collector& parser<T>::dec()
      {
         return dec_;
      }

      template<typename T> bool parser<T>::replace_symbol(const std::string& old_symbol, const std::string& new_symbol)
      {
         if (!settings_.replacer_enabled())
            return false;
         else if (details::is_reserved_word(old_symbol))
            return false;
         else
            return symbol_replacer_.add_replace(old_symbol,new_symbol,lexer::token::e_symbol);
      }

      template<typename T> bool parser<T>::remove_replace_symbol(const std::string& symbol)
      {
         if (!settings_.replacer_enabled())
            return false;
         else if (details::is_reserved_word(symbol))
            return false;
         else
            return symbol_replacer_.remove(symbol);
      }

      template<typename T> void parser<T>::enable_unknown_symbol_resolver(unknown_symbol_resolver* usr)
      {
         resolve_unknown_symbol_ = true;

         if (usr)
            unknown_symbol_resolver_ = usr;
         else
            unknown_symbol_resolver_ = &default_usr_;
      }

      template<typename T> void parser<T>::enable_unknown_symbol_resolver(unknown_symbol_resolver& usr)
      {
         enable_unknown_symbol_resolver(&usr);
      }

      template<typename T> void parser<T>::disable_unknown_symbol_resolver()
      {
         resolve_unknown_symbol_  = false;
         unknown_symbol_resolver_ = &default_usr_;
      }

      template<typename T> void parser<T>::register_loop_runtime_check(loop_runtime_check& lrtchk)
      {
         loop_runtime_check_ = &lrtchk;
      }

      template<typename T> void parser<T>::clear_loop_runtime_check()
      {
         loop_runtime_check_ = loop_runtime_check_ptr(0);
      }

      template <typename T> bool parser<T>::valid_base_operation(const std::string& symbol) const
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

      template <typename T> bool parser<T>::valid_vararg_operation(const std::string& symbol) const
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

      template <typename T> bool parser<T>::is_invalid_logic_operation(const details::operator_type operation) const
      {
         return settings_.logic_disabled(operation);
      }

      template <typename T> bool parser<T>::is_invalid_arithmetic_operation(const details::operator_type operation) const
      {
         return settings_.arithmetic_disabled(operation);
      }

      template <typename T> bool parser<T>::is_invalid_assignment_operation(const details::operator_type operation) const
      {
         return settings_.assignment_disabled(operation);
      }

      template <typename T> bool parser<T>::is_invalid_inequality_operation(const details::operator_type operation) const
      {
         return settings_.inequality_disabled(operation);
      }

      #ifdef exprtk_enable_debugging
      template <typename T> void parser<T>::next_token()
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

      template <typename T> parser<T>::expression_node_ptr parser<T>::parse_corpus()
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

      template <typename T> std::string parser<T>::construct_subexpr(lexer::token& begin_token, lexer::token& end_token)
      {
         std::string result = lexer().substr(begin_token.position,end_token.position);

         for (std::size_t i = 0; i < result.size(); ++i)
         {
            if (details::is_whitespace(result[i])) result[i] = ' ';
         }

         return result;
      }

      template <typename T> const parser<T>::precedence_level parser<T>::default_precedence = e_level00;

         template <typename T> void parser<T>::state_t::set(const precedence_level& l,
                         const precedence_level& r,
                         const details::operator_type& o)
         {
            left  = l;
            right = r;
            operation = o;
         }

         template <typename T> void parser<T>::state_t::reset()
         {
            left      = e_level00;
            right     = e_level00;
            operation = details::e_default;
         }

      template <typename T> parser<T>::expression_node_ptr parser<T>::parse_expression(precedence_level precedence)
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
                                              if(!details::disable_sc_andor)
                                                current_state.set(e_level03, e_level04, details::e_scand);
                                              else
                                                current_state.set(e_level03, e_level04, details::e_and);
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
                                              if(!details::disable_sc_andor)
                                                current_state.set(e_level01, e_level02, details::e_scor);
                                              else
                                                current_state.set(e_level01, e_level02, details::e_or);
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

      template <typename T> bool parser<T>::simplify_unary_negation_branch(expression_node_ptr& node)
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

      template <typename T> parser<T>::expression_node_ptr parser<T>::error_node()
      {
         return reinterpret_cast<expression_node_ptr>(0);
      }

        template <typename T>  parser<T>::scoped_expression_delete::scoped_expression_delete(parser<T>& pr, expression_node_ptr& expression)
         : delete_ptr(true)
         , parser_(pr)
         , expression_(expression)
         {}

        template <typename T> parser<T>::scoped_expression_delete::~scoped_expression_delete()
         {
            if (delete_ptr)
            {
               free_node(parser_.node_allocator_, expression_);
            }
         }

        template <typename T> parser<T>::scoped_bool_negator::scoped_bool_negator(bool& bb)
         : b(bb)
         { b = !b; }

        template <typename T> parser<T>::scoped_bool_negator::~scoped_bool_negator()
         { b = !b; }

        
        template <typename T> parser<T>::scoped_bool_or_restorer::scoped_bool_or_restorer(bool& bb)
         : b(bb)
         , original_value_(bb)
         {}

        template <typename T> parser<T>::scoped_bool_or_restorer::~scoped_bool_or_restorer()
         {
            b = b || original_value_;
         }

        template <typename T> parser<T>::scoped_inc_dec::scoped_inc_dec(std::size_t& v)
         : v_(v)
         { ++v_; }

        template <typename T> parser<T>::scoped_inc_dec::~scoped_inc_dec()
         {
           assert(v_ > 0);
           --v_;
         }

      template<typename T> parser<T>::expression_node_ptr parser<T>::parse_function_invocation(ifunction<T>* function, const std::string& function_name)
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

      template<typename T> parser<T>::expression_node_ptr parser<T>::parse_function_call_0(ifunction<T>* function, const std::string& function_name)
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


      template<typename T> parser<T>::expression_node_ptr parser<T>::parse_base_operation()
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

      template<typename T> parser<T>::expression_node_ptr parser<T>::parse_conditional_statement_01(expression_node_ptr condition)
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

         if (result && !details::disable_string_capabilities)
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

      template<typename T> parser<T>::expression_node_ptr parser<T>::parse_conditional_statement_02(expression_node_ptr condition)
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

         if (result && !details::disable_string_capabilities)
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

      template<typename T> parser<T>::expression_node_ptr parser<T>::parse_conditional_statement()
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

      template<typename T> parser<T>::expression_node_ptr parser<T>::parse_ternary_conditional_statement(expression_node_ptr condition)
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

         if (result && !details::disable_string_capabilities)
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

      template<typename T> parser<T>::expression_node_ptr parser<T>::parse_not_statement()
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

      template<typename T> void parser<T>::handle_brkcnt_scope_exit()
      {
         assert(!brkcnt_list_.empty());
         brkcnt_list_.pop_front();
      }

      template<typename T> parser<T>::expression_node_ptr parser<T>::parse_while_loop()
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

      template<typename T> parser<T>::expression_node_ptr parser<T>::parse_repeat_until_loop()
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

      template<typename T> parser<T>::expression_node_ptr parser<T>::parse_for_loop()
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
                     nse.var_node  = node_allocator_.allocate<variable_node_t>(*reinterpret_cast<T*>(nse.data), nse.name);

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

      template<typename T> parser<T>::expression_node_ptr parser<T>::parse_switch_statement()
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

      template<typename T> parser<T>::expression_node_ptr parser<T>::parse_multi_switch_statement()
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

      template<typename T> parser<T>::expression_node_ptr parser<T>::parse_vararg_function()
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

      template<typename T> parser<T>::expression_node_ptr parser<T>::parse_string_range_statement(expression_node_ptr& expression)
      {
         if(details::disable_string_capabilities){
            return error_node();
         }

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

      template<typename T> void parser<T>::parse_pending_string_rangesize(expression_node_ptr& expression)
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

      template<typename T> parser<T>::expression_node_ptr parser<T>::parse_multi_sequence(const std::string& source,
                                                      const bool enforce_crlbrackets)
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

      template<typename T> bool parser<T>::parse_range(range_t& rp, const bool skip_lsqr)
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

               if (details::is_true(details::numeric::geq<T>(r0_value, T(0))))
               {
                  rp.n0_c.first  = true;
                  rp.n0_c.second = static_cast<std::size_t>(details::numeric::to_int64(r0_value));
                  rp.cache.first = rp.n0_c.second;
               }

               free_node(node_allocator_,r0);

               if (details::is_true(details::numeric::lth<T>(r0_value, T(0))))
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

               if (details::is_true(details::numeric::geq<T>(r1_value, T(0))))
               {
                  rp.n1_c.first   = true;
                  rp.n1_c.second  = static_cast<std::size_t>(details::numeric::to_int64(r1_value));
                  rp.cache.second = rp.n1_c.second;
               }

               free_node(node_allocator_,r1);

               if (details::is_true(details::numeric::lth<T>(r1_value, T(0))))
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

      template<typename T> void parser<T>::lodge_symbol(const std::string& symbol,
                               const symbol_type st)
      {
         dec_.add_symbol(symbol,st);
      }

      template<typename T> parser<T>::expression_node_ptr parser<T>::parse_string()
      {
         if(details::disable_string_capabilities){
            return error_node();
         }

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

      template<typename T> parser<T>::expression_node_ptr parser<T>::parse_const_string()
      {
         if(details::disable_string_capabilities){
            return error_node();
         }

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

      template<typename T> parser<T>::expression_node_ptr parser<T>::parse_vector()
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

      template<typename T> parser<T>::expression_node_ptr parser<T>::parse_vararg_function_call(ivararg_function<T>* vararg_function, const std::string& vararg_function_name)
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
      
         template<typename T> parser<T>::type_checker::type_checker(parser_t& p,
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

         template<typename T> bool parser<T>::type_checker::verify(const std::string& param_seq, std::size_t& pseq_index)
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

         template<typename T> std::size_t parser<T>::type_checker::paramseq_count() const
         {
            return function_definition_list_.size();
         }

         template<typename T> std::string parser<T>::type_checker::paramseq(const std::size_t& index) const
         {
            return function_definition_list_[index].param_seq;
         }

         template<typename T> parser<T>::type_checker::return_type_t parser<T>::type_checker::return_type(const std::size_t& index) const
         {
            return function_definition_list_[index].return_type;
         }

         template<typename T> bool parser<T>::type_checker::invalid() const
         {
            return !invalid_state_;
         }

         template<typename T> bool parser<T>::type_checker::allow_zero_parameters() const
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

         template<typename T> std::vector<std::string> parser<T>::type_checker::split_param_seq(const std::string& param_seq, const details::char_t delimiter) const
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

         template<typename T> bool parser<T>::type_checker::is_valid_token(std::string param_seq,
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

         template<typename T> void parser<T>::type_checker::parse_function_prototypes(const std::string& func_prototypes)
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

      template<typename T> parser<T>::expression_node_ptr parser<T>::parse_generic_function_call(igeneric_function<T>* function, const std::string& function_name)
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

      template<typename T> bool parser<T>::parse_igeneric_function_params(std::string& param_type_list,
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

      template<typename T> parser<T>::expression_node_ptr parser<T>::parse_string_function_call(igeneric_function<T>* function, const std::string& function_name)
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

      template<typename T> parser<T>::expression_node_ptr parser<T>::parse_overload_function_call(igeneric_function<T>* function, const std::string& function_name)
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

      template<typename T> parser<T>::expression_node_ptr parser<T>::parse_special_function()
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

      template<typename T> parser<T>::expression_node_ptr parser<T>::parse_null_statement()
      {
         next_token();
         return node_allocator_.allocate<details::null_node<T> >();
      }

      template<typename T> parser<T>::expression_node_ptr parser<T>::parse_break_statement()
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

      template<typename T> parser<T>::expression_node_ptr parser<T>::parse_continue_statement()
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

      template<typename T> parser<T>::expression_node_ptr parser<T>::parse_define_vector_statement(const std::string& vec_name)
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
              (details::is_true(details::numeric::leq<T>(vector_size, T(0)))) ||
              std::not_equal_to<T>()
              (T(0),vector_size - details::numeric::trunc(vector_size)) ||
              (details::is_true(details::numeric::gth<T>(vector_size, max_vector_size)))
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

            if (details::is_true(details::numeric::gth<T>(T(vec_initilizer_list.size()), vector_size)))
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

      template<typename T> parser<T>::expression_node_ptr parser<T>::parse_define_string_statement(const std::string& str_name, expression_node_ptr initialisation_expression)
      {
         if(details::disable_string_capabilities){
            return error_node();
         }

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

      template<typename T> bool parser<T>::local_variable_is_shadowed(const std::string& symbol)
      {
         const scope_element& se = sem_.get_element(symbol);
         return (se.name == symbol) && se.active;
      }

      template<typename T> parser<T>::expression_node_ptr parser<T>::parse_define_var_statement()
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
            nse.var_node  = node_allocator_.allocate<variable_node_t>(*reinterpret_cast<T*>(nse.data), nse.name);

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

      template<typename T> parser<T>::expression_node_ptr parser<T>::parse_uninitialised_var_statement(const std::string& var_name)
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
            nse.var_node  = node_allocator_.allocate<variable_node_t>(*reinterpret_cast<T*>(nse.data), nse.name);

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

      template<typename T> parser<T>::expression_node_ptr parser<T>::parse_swap_statement()
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

      template<typename T> parser<T>::expression_node_ptr parser<T>::parse_return_statement()
      {
         if(details::disable_return_statement){
            return error_node();
         }

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

      template<typename T> bool parser<T>::post_variable_process(const std::string& symbol)
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

      template<typename T> bool parser<T>::post_bracket_process(const typename token_t::token_type& token, expression_node_ptr& branch)
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

      template<typename T> parser<T>::interval_t parser<T>::make_memory_range(const T& t)
      {
         const T* begin = reinterpret_cast<const T*>(&t);
         const T* end   = begin + 1;
         return interval_t(begin, end);
      }

      template<typename T> parser<T>::interval_t parser<T>::make_memory_range(const T* begin, const std::size_t size)
      {
         return interval_t(begin, begin + size);
      }

      template<typename T> parser<T>::interval_t parser<T>::make_memory_range(details::char_cptr begin, const std::size_t size)
      {
         return interval_t(begin, begin + size);
      }

      template<typename T> void parser<T>::lodge_immutable_symbol(const lexer::token& token, const interval_t interval)
      {
         immutable_memory_map_.add_interval(interval);
         immutable_symtok_map_[interval] = token;
      }

      template<typename T> parser<T>::expression_node_ptr parser<T>::parse_symtab_symbol()
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
               else if (scope_element::e_string == se.type && !details::disable_string_capabilities)
               {
                  return parse_string();
               }
            }
         }

         // Are we dealing with a string variable?
         if (symtab_store_.is_stringvar(symbol) && !details::disable_string_capabilities)
         {
            return parse_string();
         }

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

         if(!details::disable_string_capabilities)
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

      template<typename T> parser<T>::expression_node_ptr parser<T>::parse_symbol()
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
         else if (details::imatch(symbol, symbol_break) && !details::disable_break_continue)
         {
            return parse_break_statement();
         }
         else if (details::imatch(symbol, symbol_continue) && !details::disable_break_continue)
         {
            return parse_continue_statement();
         }
         else if (details::imatch(symbol, symbol_var))
         {
            return parse_define_var_statement();
         }
         else if (details::imatch(symbol, symbol_swap))
         {
            return parse_swap_statement();
         }
         else if (
                   details::imatch(symbol, symbol_return) &&
                   settings_.control_struct_enabled(symbol) && !details::disable_return_statement
                 )
         {
            return parse_return_statement();
         }
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

      template<typename T> parser<T>::expression_node_ptr parser<T>::parse_branch(precedence_level precedence)
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
         else if (token_t::e_string == current_token().type && !details::disable_string_capabilities)
         {
            branch = parse_const_string();
         }
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

      template<typename T> void parser<T>::set_error(const parser_error::type& error_type)
      {
         error_list_.push_back(error_type);
      }

      template<typename T> void parser<T>::remove_last_error()
      {
         if (!error_list_.empty())
         {
            error_list_.pop_back();
         }
      }

      template<typename T> void parser<T>::set_synthesis_error(const std::string& synthesis_error_message)
      {
         if (synthesis_error_.empty())
         {
            synthesis_error_ = synthesis_error_message;
         }
      }

      template<typename T> void parser<T>::register_local_vars(expression<T>& e)
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
            else if (scope_element::e_string == se.type && !details::disable_string_capabilities)
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

            se.var_node  = 0;
            se.vec_node  = 0;
            se.str_node  = 0;
            se.data      = 0;
            se.ref_count = 0;
            se.active    = false;
         }
      }

      template<typename T> void parser<T>::register_return_results(expression<T>& e)
      {
         e.register_return_results(results_context_);
         results_context_ = 0;
      }

      template<typename T> void parser<T>::load_unary_operations_map(unary_op_map_t& m)
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

      template<typename T> void parser<T>::load_binary_operations_map(binary_op_map_t& m)
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

      template<typename T> void parser<T>::load_inv_binary_operations_map(inv_binary_op_map_t& m)
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

      template<typename T> void parser<T>::load_sf3_map(sf3_map_t& sf3_map)
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

      template<typename T> void parser<T>::load_sf4_map(sf4_map_t& sf4_map)
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

      template<typename T> parser<T>::results_context_t& parser<T>::results_ctx()
      {
         if (0 == results_context_)
         {
            results_context_ = new results_context_t();
         }

         return (*results_context_);
      }

      template<typename T> void parser<T>::return_cleanup()
      {
         if(details::disable_return_statement) 
            return;
         if (results_context_)
         {
            delete results_context_;
            results_context_ = 0;
         }

         state_.return_stmt_present = false;
      }

         template class parser<int16_t>;
         template class parser<int32_t>;
         template class parser<int64_t>;
         template class parser<float>;
         template class parser<double>;
         template class parser<long double>;
         template class parser<std::complex<float>>;
         template class parser<std::complex<double>>;
         template class parser<std::complex<long double>>;
}

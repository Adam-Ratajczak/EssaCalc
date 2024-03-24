#include "include/OperatorHelpers.hpp"
#include "include/ExpressionNodes.hpp"
#include <cstdint>


namespace Essa::Math{
   namespace details
   {
      std::string to_str(const operator_type opr)
      {
         switch (opr)
         {
            case e_add     : return "%s+%s"  ;
            case e_sub     : return "%s-%s"  ;
            case e_mul     : return  "%s*%s"  ;
            case e_div     : return  "%s/%s"  ;
            case e_mod     : return  "%smod%s"  ;
            case e_pow     : return  "%s^%s"  ;
            case e_assign  : return "%s:=%s"  ;
            case e_addass  : return "%s+=%s"  ;
            case e_subass  : return "%s-=%s"  ;
            case e_mulass  : return "%s*=%s"  ;
            case e_divass  : return "%s/=%s"  ;
            case e_modass  : return "%s%=%s"  ;
            case e_lt      : return  "%s<%s"  ;
            case e_lte     : return "%s<=%s"  ;
            case e_eq      : return "%s==%s"  ;
            case e_equal   : return  "%s=%s"  ;
            case e_ne      : return "%s!=%s"  ;
            case e_nequal  : return "%s<>%s"  ;
            case e_gte     : return "%s>=%s"  ;
            case e_gt      : return  "%s>%s"  ;
            case e_and     : return "%s&%s" ;
            case e_or      : return "%s|%s"  ;
            case e_xor     : return "%sxor%s" ;
            case e_nand    : return "~(%s&%s)";
            case e_nor     : return "~(%s|%s)" ;
            case e_xnor    : return "!(%sxor%s)";
            case e_atan2   : return "atan(%s)";
            case e_min     : return "min(%s)";
            case e_max     : return "max(%s)";
            case e_avg     : return "avg(%s)";
            case e_sum     : return "sum(%s)";
            case e_prod    : return "prod(%s)";
            case e_mand    : return "mand(%s)";
            case e_mor     : return "mor(%s)";
            case e_scand   : return "scand(%s)";
            case e_scor    : return "scor(%s)";
            case e_shr     : return "%s>>%s";
            case e_shl     : return "%s<<%s";
            case e_abs     : return "abs(%s)";
            case e_acos    : return "acos(%s)";
            case e_acosh   : return "acosh(%s)";
            case e_asin    : return "asin(%s)";
            case e_asinh   : return "asinh(%s)";
            case e_atan    : return "atan(%s)";
            case e_atanh   : return "atanh(%s)";
            case e_ceil    : return "ceil(%s)";
            case e_cos     : return "cos(%s)";
            case e_cosh    : return "cosh(%s)";
            case e_exp     : return "exp(%s)";
            case e_expm1   : return "exp(%s-1)";
            case e_floor   : return "floor(%s)";
            case e_log     : return "log(%s)";
            case e_log10   : return "log(%s)/log(10)";
            case e_log2    : return "log(%s)/log(2)";
            case e_log1p   : return "log(1/(%s))";
            case e_logn    : return "log(%s)/log(%s)";
            case e_neg     : return "(-%s)";
            case e_pos     : return "pos(%s)";
            case e_round   : return "round(%s)";
            case e_roundn  : return "round(%s,%s)";
            case e_root    : return "(%s)^(1/(%s))";
            case e_sqrt    : return "sqrt(%s)";
            case e_sin     : return "sin(%s)";
            case e_sinc    : return "sinc(%s)";
            case e_sinh    : return "sinh(%s)";
            case e_sec     : return "sec(%s)";
            case e_csc     : return "csc(%s)";
            case e_tan     : return "tan(%s)";
            case e_tanh    : return "tanh(%s)";
            case e_cot     : return "cot(%s)";
            case e_clamp   : return "clamp(%s,%s,%s)";
            case e_iclamp  : return "iclamp(%s,%s,%s)";
            case e_inrange : return "inrange(%s,%s,%s)";
            case e_sgn     : return "sgn(%s)";
            case e_r2d     : return "r2d(%s)";
            case e_d2r     : return "d2r(%s)";
            case e_d2g     : return "d2r(%s)";
            case e_g2d     : return "g2d(%s)";
            case e_hypot   : return "hypot(%s,%s)";
            case e_notl    : return "notl(%s)";
            case e_erf     : return "erf(%s)";
            case e_erfc    : return "erfc(%s)";
            case e_ncdf    : return "ncdf(%s)";
            case e_frac    : return "frac(%s)";
            case e_trunc   : return "trunc(%s)";
            case e_in      : return "in(%s,%s,%s)";
            case e_like    : return "like(%s)";
            case e_ilike   : return "ilike(%s)";
            case e_multi   : return "multi(%s,%s,%s)";
            case e_smulti  : return "smulti(%s,%s,%s)";
            case e_swap    : return "swap(%s,%s)";
            default        : return "N/A";
            }
      }

      bool check_significance(const operator_type _op1, const operator_type _op2){
        switch (_op1) {
        case e_pow:
            return _op2 == e_add || _op2 == e_sub || _op2 == e_mul || _op2 == e_div; 
        case e_mul:
        case e_div:
            return _op2 == e_add || _op2 == e_sub;
        case e_add:
        case e_sub:
            return false;
         default:
            return true;
          break;
        }

        return false;
    }

    base_operation_t::base_operation_t(const operator_type t, const unsigned int& np)
        : type(t)
        , num_params(np)
    {}

      namespace loop_unroll
      {
         const unsigned int global_loop_batch_size = 16;

         details::details(const std::size_t& vsize, const unsigned int loop_batch_size)
            : batch_size(loop_batch_size   )
            , remainder (vsize % batch_size)
            , upper_bound(static_cast<int>(vsize - (remainder ? loop_batch_size : 0)))
            {}
      }

      #ifdef exprtk_enable_debugging
      void dump_ptr(const std::string& s, const void* ptr, const std::size_t size = 0)
      {
         if (size)
            exprtk_debug(("%s - addr: %p size: %d\n",
                          s.c_str(),
                          ptr,
                          static_cast<unsigned int>(size)));
         else
            exprtk_debug(("%s - addr: %p\n",s.c_str(),ptr));
      }
      #else
        void dump_ptr(const std::string&, const void*) {}
        void dump_ptr(const std::string&, const void*, const std::size_t) {}
    #endif

        template<typename T>
        vec_data_store<T>::control_block::control_block()
            : ref_count(1)
            , size     (0)
            , data     (0)
            , destruct (true)
            {}

        template<typename T>
        vec_data_store<T>::control_block::control_block(const std::size_t& dsize)
            : ref_count(1    )
            , size     (dsize)
            , data     (0    )
            , destruct (true )
            { create_data(); }

        template<typename T>
        vec_data_store<T>::control_block::control_block(const std::size_t& dsize, data_t dptr, bool dstrct)
            : ref_count(1     )
            , size     (dsize )
            , data     (dptr  )
            , destruct (dstrct)
            {}

        template<typename T>
        vec_data_store<T>::control_block::~control_block()
            {
               if (data && destruct && (0 == ref_count))
               {
                  dump_ptr("~vec_data_store::control_block() data",data);
                  delete[] data;
                  data = reinterpret_cast<data_t>(0);
               }
            }

        template<typename T>
        vec_data_store<T>::control_block* vec_data_store<T>::control_block::create(const std::size_t& dsize, data_t data_ptr, bool dstrct)
        {
           if (dsize)
           {
              if (0 == data_ptr)
                 return (new control_block(dsize));
              else
                 return (new control_block(dsize, data_ptr, dstrct));
           }
           else
              return (new control_block);
        }

        template<typename T>
        void vec_data_store<T>::control_block::destroy(vec_data_store<T>::control_block*& cntrl_blck)
        {
           if (cntrl_blck)
           {
              if (
                   (0 !=   cntrl_blck->ref_count) &&
                   (0 == --cntrl_blck->ref_count)
                 )
              {
                 delete cntrl_blck;
              }

              cntrl_blck = 0;
           }
        }
        
        template<typename T>
        void vec_data_store<T>::control_block::create_data()
        {
           destruct = true;
           data     = new T[size];
           std::fill_n(data, size, T(0));
           dump_ptr("control_block::create_data() - data", data, size);
        }

        template<typename T>
        vec_data_store<T>::vec_data_store()
         : control_block_(control_block::create(0))
         {}

        template<typename T>
        vec_data_store<T>::vec_data_store(const std::size_t& size)
         : control_block_(control_block::create(size,reinterpret_cast<data_t>(0),true))
         {}

         
        template<typename T>
        vec_data_store<T>::vec_data_store(const std::size_t& size, data_t data, bool dstrct)
         : control_block_(control_block::create(size, data, dstrct))
         {}

        
        template<typename T>
        vec_data_store<T>::vec_data_store(const type& vds)
         {
            control_block_ = vds.control_block_;
            control_block_->ref_count++;
         }

        template<typename T>
        vec_data_store<T>::~vec_data_store()
         {
            control_block::destroy(control_block_);
         }

        template<typename T>
        vec_data_store<T>::type& vec_data_store<T>::operator=(const vec_data_store<T>::type& vds)
         {
            if (this != &vds)
            {
               std::size_t final_size = min_size(control_block_, vds.control_block_);

               vds.control_block_->size = final_size;
                   control_block_->size = final_size;

               if (control_block_->destruct || (0 == control_block_->data))
               {
                  control_block::destroy(control_block_);

                  control_block_ = vds.control_block_;
                  control_block_->ref_count++;
               }
            }

            return (*this);
         }

        template<typename T>
        vec_data_store<T>::data_t vec_data_store<T>::data()
         {
            return control_block_->data;
         }

        template<typename T>
        vec_data_store<T>::data_t vec_data_store<T>::data() const
         {
            return control_block_->data;
         }

        template<typename T>
        std::size_t vec_data_store<T>::size() const
         {
            return control_block_->size;
         }

        template<typename T>
        vec_data_store<T>::data_t& vec_data_store<T>::ref()
         {
            return control_block_->data;
         }

        template<typename T>
        void vec_data_store<T>::dump() const
         {
            #ifdef exprtk_enable_debugging
            exprtk_debug(("size: %d\taddress:%p\tdestruct:%c\n",
                          size(),
                          data(),
                          (control_block_->destruct ? 'T' : 'F')));

            for (std::size_t i = 0; i < size(); ++i)
            {
               if (5 == i)
                  exprtk_debug(("\n"));

               exprtk_debug(("%15.10f ",data()[i]));
            }
            exprtk_debug(("\n"));
            #endif
         }

        template<typename T>
         void vec_data_store<T>::match_sizes(vec_data_store<T>::type& vds0, vec_data_store<T>::type& vds1)
         {
            const std::size_t size = min_size(vds0.control_block_,vds1.control_block_);
            vds0.control_block_->size = size;
            vds1.control_block_->size = size;
         }

        template<typename T>
         std::size_t vec_data_store<T>::min_size(const vec_data_store<T>::control_block* cb0, const vec_data_store<T>::control_block* cb1)
         {
            const std::size_t size0 = cb0->size;
            const std::size_t size1 = cb1->size;

            if (size0 && size1)
               return std::min(size0,size1);
            else
               return (size0) ? size0 : size1;
         }
    
        template class vec_data_store<int16_t>;
        template class vec_data_store<int32_t>;
        template class vec_data_store<int64_t>;
        template class vec_data_store<float>;
        template class vec_data_store<double>;
        template class vec_data_store<long double>;
        template class vec_data_store<std::complex<float>>;
        template class vec_data_store<std::complex<double>>;
        template class vec_data_store<std::complex<long double>>;

      namespace numeric
      {
         namespace details
         {
            template <typename T>
            T process_impl(const operator_type operation, const T arg)
            {
               switch (operation)
               {
                  case e_abs   : return numeric::abs  (arg);
                  case e_acos  : return numeric::acos (arg);
                  case e_acosh : return numeric::acosh(arg);
                  case e_asin  : return numeric::asin (arg);
                  case e_asinh : return numeric::asinh(arg);
                  case e_atan  : return numeric::atan (arg);
                  case e_atanh : return numeric::atanh(arg);
                  case e_ceil  : return numeric::ceil (arg);
                  case e_cos   : return numeric::cos  (arg);
                  case e_cosh  : return numeric::cosh (arg);
                  case e_exp   : return numeric::exp  (arg);
                  case e_expm1 : return numeric::expm1(arg);
                  case e_floor : return numeric::floor(arg);
                  case e_log   : return numeric::log  (arg);
                  case e_log10 : return numeric::log10(arg);
                  case e_log2  : return numeric::log2 (arg);
                  case e_log1p : return numeric::log1p(arg);
                  case e_neg   : return numeric::neg  (arg);
                  case e_pos   : return numeric::pos  (arg);
                  case e_round : return numeric::round(arg);
                  case e_sin   : return numeric::sin  (arg);
                  case e_sinc  : return numeric::sinc (arg);
                  case e_sinh  : return numeric::sinh (arg);
                  case e_sqrt  : return numeric::sqrt (arg);
                  case e_tan   : return numeric::tan  (arg);
                  case e_tanh  : return numeric::tanh (arg);
                  case e_cot   : return numeric::cot  (arg);
                  case e_sec   : return numeric::sec  (arg);
                  case e_csc   : return numeric::csc  (arg);
                  case e_r2d   : return numeric::r2d  (arg);
                  case e_d2r   : return numeric::d2r  (arg);
                  case e_d2g   : return numeric::d2g  (arg);
                  case e_g2d   : return numeric::g2d  (arg);
                  case e_notl  : return numeric::notl (arg);
                  case e_sgn   : return numeric::sgn  (arg);
                  case e_erf   : return numeric::erf  (arg);
                  case e_erfc  : return numeric::erfc (arg);
                  case e_ncdf  : return numeric::ncdf (arg);
                  case e_frac  : return numeric::frac (arg);
                  case e_trunc : return numeric::trunc(arg);

                  default      : exprtk_debug(("numeric::details::process_impl<T> - Invalid unary operation.\n"));
                                 return std::numeric_limits<T>::quiet_NaN();
               }
            }

            template <typename T>
            T process_impl(const operator_type operation, const T arg0, const T arg1)
            {
               switch (operation)
               {
                  case e_add    : return (arg0 + arg1);
                  case e_sub    : return (arg0 - arg1);
                  case e_mul    : return (arg0 * arg1);
                  case e_div    : return (arg0 / arg1);
                  case e_mod    : return modulus<T>(arg0,arg1);
                  case e_pow    : return pow<T>(arg0,arg1);
                  case e_atan2  : return atan2<T>(arg0,arg1);
                  case e_min    : return min_num<T>(arg0,arg1);
                  case e_max    : return max_num<T>(arg0,arg1);
                  case e_logn   : return logn<T>(arg0,arg1);
                  case e_lt     : return lth<T>(arg0,arg1);
                  case e_lte    : return leq<T>(arg0,arg1);
                  case e_eq     : return std::equal_to<T>()(arg0,arg1) ? T(1) : T(0);
                  case e_ne     : return std::not_equal_to<T>()(arg0,arg1) ? T(1) : T(0);
                  case e_gte    : return geq<T>(arg0,arg1);
                  case e_gt     : return gth<T>(arg0,arg1);
                  case e_and    : return and_opr <T>(arg0,arg1);
                  case e_nand   : return nand_opr<T>(arg0,arg1);
                  case e_or     : return or_opr  <T>(arg0,arg1);
                  case e_nor    : return nor_opr <T>(arg0,arg1);
                  case e_xor    : return xor_opr <T>(arg0,arg1);
                  case e_xnor   : return xnor_opr<T>(arg0,arg1);
                  case e_root   : return root    <T>(arg0,arg1);
                  case e_roundn : return roundn  <T>(arg0,arg1);
                  case e_equal  : return equal      (arg0,arg1);
                  case e_nequal : return nequal     (arg0,arg1);
                  case e_hypot  : return hypot   <T>(arg0,arg1);
                  case e_shr    : return shr     <T>(arg0,arg1);
                  case e_shl    : return shl     <T>(arg0,arg1);

                  default       : exprtk_debug(("numeric::details::process_impl<T> - Invalid binary operation.\n"));
                                  return std::numeric_limits<T>::quiet_NaN();
               }
            }
         }

         template <typename T>
         T process(const operator_type operation, const T arg)
         {
            return Essa::Math::details::numeric::details::process_impl(operation,arg);
         }
         template int16_t process(const operator_type, const int16_t);
         template int32_t process(const operator_type, const int32_t);
         template int64_t process(const operator_type, const int64_t);
         template float process(const operator_type, const float);
         template double process(const operator_type, const double);
         template long double process(const operator_type, const long double);
         template std::complex<float> process(const operator_type, const std::complex<float>);
         template std::complex<double> process(const operator_type, const std::complex<double>);
         template std::complex<long double> process(const operator_type, const std::complex<long double>);

         template <typename T>
         T process(const operator_type operation, const T arg0, const T arg1)
         {
            return Essa::Math::details::numeric::details::process_impl(operation, arg0, arg1);
         }
         template int16_t process(const operator_type, const int16_t, const int16_t);
         template int32_t process(const operator_type, const int32_t, const int32_t);
         template int64_t process(const operator_type, const int64_t, const int64_t);
         template float process(const operator_type, const float, const float);
         template double process(const operator_type, const double, const double);
         template long double process(const operator_type, const long double, const long double);
         template std::complex<float> process(const operator_type, const std::complex<float>, const std::complex<float>);
         template std::complex<double> process(const operator_type, const std::complex<double>, const std::complex<double>);
         template std::complex<long double> process(const operator_type, const std::complex<long double>, const std::complex<long double>);
      }

      template <typename T>
      bool is_generally_string_node(const expression_node<T>* node);

      bool is_true(const int16_t v)
      {
         return std::not_equal_to()(0.0,v);
      }

      bool is_true(const int32_t v)
      {
         return std::not_equal_to()(0.0,v);
      }

      bool is_true(const int64_t v)
      {
         return std::not_equal_to()(0.0,v);
      }

      bool is_true(const float v)
      {
         return std::not_equal_to()(0.0,v);
      }

      bool is_true(const double v)
      {
         return std::not_equal_to()(0.0,v);
      }

      bool is_true(const long double v)
      {
         return std::not_equal_to()(0.0,v);
      }

      bool is_true(const std::complex<float> v)
      {
         return std::not_equal_to()(std::complex<float>(0.0),v);
      }

      bool is_true(const std::complex<double> v)
      {
         return std::not_equal_to()(std::complex<double>(0.0),v);
      }

      bool is_true(const std::complex<long double> v)
      {
         return std::not_equal_to()(std::complex<long double>(0.0),v);
      }

      #define ADD_FUNC_TEMPLATES(FunctionName)                                      \
      template bool FunctionName(const expression_node<int16_t>*);                   \
      template bool FunctionName(const expression_node<int32_t>*);                   \
      template bool FunctionName(const expression_node<int64_t>*);                   \
      template bool FunctionName(const expression_node<float>*);                     \
      template bool FunctionName(const expression_node<double>*);                    \
      template bool FunctionName(const expression_node<long double>*);               \
      template bool FunctionName(const expression_node<std::complex<float>>*);       \
      template bool FunctionName(const expression_node<std::complex<double>>*);      \
      template bool FunctionName(const expression_node<std::complex<long double>>*);

      template <typename T>
      bool is_true(const expression_node<T>* node)
      {
         return std::not_equal_to<T>()(T(0),node->value());
      }
      template bool is_true(const expression_node<int16_t>*);
      template bool is_true(const expression_node<int32_t>*);
      template bool is_true(const expression_node<int64_t>*);
      template bool is_true(const expression_node<float>*);
      template bool is_true(const expression_node<double>*);
      template bool is_true(const expression_node<long double>*);
      template bool is_true(const expression_node<std::complex<float>>*);
      template bool is_true(const expression_node<std::complex<double>>*);
      template bool is_true(const expression_node<std::complex<long double>>*);

      template <typename T>
      bool is_true(const std::pair<expression_node<T>*,bool>& node)
      {
         return std::not_equal_to<T>()(T(0),node.first->value());
      }
      template bool is_true(const std::pair<expression_node<int16_t>*, bool>&);
      template bool is_true(const std::pair<expression_node<int32_t>*, bool>&);
      template bool is_true(const std::pair<expression_node<int64_t>*, bool>&);
      template bool is_true(const std::pair<expression_node<float>*, bool>&);
      template bool is_true(const std::pair<expression_node<double>*, bool>&);
      template bool is_true(const std::pair<expression_node<long double>*, bool>&);
      template bool is_true(const std::pair<expression_node<std::complex<float>>*, bool>&);
      template bool is_true(const std::pair<expression_node<std::complex<double>>*, bool>&);
      template bool is_true(const std::pair<expression_node<std::complex<long double>>*, bool>&);

      template <typename T>
      bool is_false(const expression_node<T>* node)
      {
         return std::equal_to<T>()(T(0),node->value());
      }
      template bool is_false(const expression_node<int16_t>*);
      template bool is_false(const expression_node<int32_t>*);
      template bool is_false(const expression_node<int64_t>*);
      template bool is_false(const expression_node<float>*);
      template bool is_false(const expression_node<double>*);
      template bool is_false(const expression_node<long double>*);
      template bool is_false(const expression_node<std::complex<float>>*);
      template bool is_false(const expression_node<std::complex<double>>*);
      template bool is_false(const expression_node<std::complex<long double>>*);

      template <typename T>
      bool is_false(const std::pair<expression_node<T>*,bool>& node)
      {
         return std::equal_to<T>()(T(0),node.first->value());
      }
      template bool is_false(const std::pair<expression_node<int16_t>*, bool>&);
      template bool is_false(const std::pair<expression_node<int32_t>*, bool>&);
      template bool is_false(const std::pair<expression_node<int64_t>*, bool>&);
      template bool is_false(const std::pair<expression_node<float>*, bool>&);
      template bool is_false(const std::pair<expression_node<double>*, bool>&);
      template bool is_false(const std::pair<expression_node<long double>*, bool>&);
      template bool is_false(const std::pair<expression_node<std::complex<float>>*, bool>&);
      template bool is_false(const std::pair<expression_node<std::complex<double>>*, bool>&);
      template bool is_false(const std::pair<expression_node<std::complex<long double>>*, bool>&);

      template <typename T>
      bool is_unary_node(const expression_node<T>* node)
      {
         return node && (details::expression_node<T>::e_unary == node->type());
      }
      ADD_FUNC_TEMPLATES(is_unary_node)

      template <typename T>
      bool is_neg_unary_node(const expression_node<T>* node)
      {
         return node && (details::expression_node<T>::e_neg == node->type());
      }
      ADD_FUNC_TEMPLATES(is_neg_unary_node)

      template <typename T>
      bool is_binary_node(const expression_node<T>* node)
      {
         return node && (details::expression_node<T>::e_binary == node->type());
      }
      ADD_FUNC_TEMPLATES(is_binary_node)

      template <typename T>
      bool is_variable_node(const expression_node<T>* node)
      {
         return node && (details::expression_node<T>::e_variable == node->type());
      }
      ADD_FUNC_TEMPLATES(is_variable_node)

      template <typename T>
      bool is_ivariable_node(const expression_node<T>* node)
      {
         return node &&
                (
                  details::expression_node<T>::e_variable   == node->type() ||
                  details::expression_node<T>::e_vecelem    == node->type() ||
                  details::expression_node<T>::e_rbvecelem  == node->type() ||
                  details::expression_node<T>::e_rbveccelem == node->type()
                );
      }
      ADD_FUNC_TEMPLATES(is_ivariable_node)

      template <typename T>
      bool is_vector_elem_node(const expression_node<T>* node)
      {
         return node && (details::expression_node<T>::e_vecelem == node->type());
      }
      ADD_FUNC_TEMPLATES(is_vector_elem_node)

      template <typename T>
      bool is_rebasevector_elem_node(const expression_node<T>* node)
      {
         return node && (details::expression_node<T>::e_rbvecelem == node->type());
      }
      ADD_FUNC_TEMPLATES(is_rebasevector_elem_node)

      template <typename T>
      bool is_rebasevector_celem_node(const expression_node<T>* node)
      {
         return node && (details::expression_node<T>::e_rbveccelem == node->type());
      }
      ADD_FUNC_TEMPLATES(is_rebasevector_celem_node)

      template <typename T>
      bool is_vector_node(const expression_node<T>* node)
      {
         return node && (details::expression_node<T>::e_vector == node->type());
      }
      ADD_FUNC_TEMPLATES(is_vector_node)

      template <typename T>
      bool is_ivector_node(const expression_node<T>* node)
      {
         if (node)
         {
            switch (node->type())
            {
               case details::expression_node<T>::e_vector      :
               case details::expression_node<T>::e_vecvalass   :
               case details::expression_node<T>::e_vecvecass   :
               case details::expression_node<T>::e_vecopvalass :
               case details::expression_node<T>::e_vecopvecass :
               case details::expression_node<T>::e_vecvecswap  :
               case details::expression_node<T>::e_vecvecarith :
               case details::expression_node<T>::e_vecvalarith :
               case details::expression_node<T>::e_valvecarith :
               case details::expression_node<T>::e_vecunaryop  :
               case details::expression_node<T>::e_vecondition : return true;
               default                                         : return false;
            }
         }
         else
            return false;
      }
      ADD_FUNC_TEMPLATES(is_ivector_node)

      template <typename T>
      bool is_constant_node(const expression_node<T>* node)
      {
         return node &&
         (
           details::expression_node<T>::e_constant    == node->type() ||
           details::expression_node<T>::e_stringconst == node->type()
         );
      }
      ADD_FUNC_TEMPLATES(is_constant_node)

      template <typename T>
      bool is_null_node(const expression_node<T>* node)
      {
         return node && (details::expression_node<T>::e_null == node->type());
      }
      ADD_FUNC_TEMPLATES(is_null_node)

      template <typename T>
      bool is_break_node(const expression_node<T>* node)
      {
         return node && (details::expression_node<T>::e_break == node->type());
      }
      ADD_FUNC_TEMPLATES(is_break_node)

      template <typename T>
      bool is_continue_node(const expression_node<T>* node)
      {
         return node && (details::expression_node<T>::e_continue == node->type());
      }
      ADD_FUNC_TEMPLATES(is_continue_node)

      template <typename T>
      bool is_swap_node(const expression_node<T>* node)
      {
         return node && (details::expression_node<T>::e_swap == node->type());
      }
      ADD_FUNC_TEMPLATES(is_swap_node)

      template <typename T>
      bool is_function(const expression_node<T>* node)
      {
         return node && (details::expression_node<T>::e_function == node->type());
      }
      ADD_FUNC_TEMPLATES(is_function)

      template <typename T>
      bool is_return_node(const expression_node<T>* node)
      {
         return node && (details::expression_node<T>::e_return == node->type());
      }
      ADD_FUNC_TEMPLATES(is_return_node)

      template <typename T> class unary_node;

      template <typename T>
      bool is_negate_node(const expression_node<T>* node)
      {
         if (node && is_unary_node(node))
         {
            return (details::e_neg == static_cast<const unary_node<T>*>(node)->operation());
         }
         else
            return false;
      }
      ADD_FUNC_TEMPLATES(is_negate_node)

      template <typename T>
      bool branch_deletable(const expression_node<T>* node)
      {
         return (0 != node)             &&
                !is_variable_node(node) &&
                !is_string_node  (node) ;
      }
      ADD_FUNC_TEMPLATES(branch_deletable)

      void load_operations_map(std::multimap<std::string,details::base_operation_t,details::ilesscompare>& m)
      {
         #define register_op(Symbol, Type, Args)                                             \
         m.insert(std::make_pair(std::string(Symbol),details::base_operation_t(Type,Args)));

         register_op("abs"       , e_abs     , 1)
         register_op("acos"      , e_acos    , 1)
         register_op("acosh"     , e_acosh   , 1)
         register_op("asin"      , e_asin    , 1)
         register_op("asinh"     , e_asinh   , 1)
         register_op("atan"      , e_atan    , 1)
         register_op("atanh"     , e_atanh   , 1)
         register_op("ceil"      , e_ceil    , 1)
         register_op("cos"       , e_cos     , 1)
         register_op("cosh"      , e_cosh    , 1)
         register_op("exp"       , e_exp     , 1)
         register_op("expm1"     , e_expm1   , 1)
         register_op("floor"     , e_floor   , 1)
         register_op("log"       , e_log     , 1)
         register_op("log10"     , e_log10   , 1)
         register_op("log2"      , e_log2    , 1)
         register_op("log1p"     , e_log1p   , 1)
         register_op("sin"       , e_sin     , 1)
         register_op("sinh"      , e_sinh    , 1)
         register_op("sec"       , e_sec     , 1)
         register_op("csc"       , e_csc     , 1)
         register_op("sqrt"      , e_sqrt    , 1)
         register_op("tan"       , e_tan     , 1)
         register_op("tanh"      , e_tanh    , 1)
         register_op("cot"       , e_cot     , 1)
         register_op("erf"       , e_erf     , 1)
         register_op("atan2"     , e_atan2   , 2)
         register_op("logn"      , e_logn    , 2)
         register_op("pow"       , e_pow     , 2)
         register_op("root"      , e_root    , 2)
         #undef register_op
      }
   }
}

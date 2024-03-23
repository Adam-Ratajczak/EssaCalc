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

#include "Numeric.hpp"
#include <deque>
#include <iostream>

namespace Essa::Math{
   namespace details
   {
      enum operator_type
      {
         e_default , e_null    , e_add     , e_sub     ,
         e_mul     , e_div     , e_mod     , e_pow     ,
         e_atan2   , e_min     , e_max     , e_avg     ,
         e_sum     , e_prod    , e_lt      , e_lte     ,
         e_eq      , e_equal   , e_ne      , e_nequal  ,
         e_gte     , e_gt      , e_and     , e_nand    ,
         e_or      , e_nor     , e_xor     , e_xnor    ,
         e_mand    , e_mor     , e_scand   , e_scor    ,
         e_shr     , e_shl     , e_abs     , e_acos    ,
         e_acosh   , e_asin    , e_asinh   , e_atan    ,
         e_atanh   , e_ceil    , e_cos     , e_cosh    ,
         e_exp     , e_expm1   , e_floor   , e_log     ,
         e_log10   , e_log2    , e_log1p   , e_logn    ,
         e_neg     , e_pos     , e_round   , e_roundn  ,
         e_root    , e_sqrt    , e_sin     , e_sinc    ,
         e_sinh    , e_sec     , e_csc     , e_tan     ,
         e_tanh    , e_cot     , e_clamp   , e_iclamp  ,
         e_inrange , e_sgn     , e_r2d     , e_d2r     ,
         e_d2g     , e_g2d     , e_hypot   , e_notl    ,
         e_erf     , e_erfc    , e_ncdf    , e_frac    ,
         e_trunc   , e_assign  , e_addass  , e_subass  ,
         e_mulass  , e_divass  , e_modass  , e_in      ,
         e_like    , e_ilike   , e_multi   , e_smulti  ,
         e_swap    ,

         // Do not add new functions/operators after this point.
         e_sf00 = 1000, e_sf01 = 1001, e_sf02 = 1002, e_sf03 = 1003,
         e_sf04 = 1004, e_sf05 = 1005, e_sf06 = 1006, e_sf07 = 1007,
         e_sf08 = 1008, e_sf09 = 1009, e_sf10 = 1010, e_sf11 = 1011,
         e_sf12 = 1012, e_sf13 = 1013, e_sf14 = 1014, e_sf15 = 1015,
         e_sf16 = 1016, e_sf17 = 1017, e_sf18 = 1018, e_sf19 = 1019,
         e_sf20 = 1020, e_sf21 = 1021, e_sf22 = 1022, e_sf23 = 1023,
         e_sf24 = 1024, e_sf25 = 1025, e_sf26 = 1026, e_sf27 = 1027,
         e_sf28 = 1028, e_sf29 = 1029, e_sf30 = 1030, e_sf31 = 1031,
         e_sf32 = 1032, e_sf33 = 1033, e_sf34 = 1034, e_sf35 = 1035,
         e_sf36 = 1036, e_sf37 = 1037, e_sf38 = 1038, e_sf39 = 1039,
         e_sf40 = 1040, e_sf41 = 1041, e_sf42 = 1042, e_sf43 = 1043,
         e_sf44 = 1044, e_sf45 = 1045, e_sf46 = 1046, e_sf47 = 1047,
         e_sf48 = 1048, e_sf49 = 1049, e_sf50 = 1050, e_sf51 = 1051,
         e_sf52 = 1052, e_sf53 = 1053, e_sf54 = 1054, e_sf55 = 1055,
         e_sf56 = 1056, e_sf57 = 1057, e_sf58 = 1058, e_sf59 = 1059,
         e_sf60 = 1060, e_sf61 = 1061, e_sf62 = 1062, e_sf63 = 1063,
         e_sf64 = 1064, e_sf65 = 1065, e_sf66 = 1066, e_sf67 = 1067,
         e_sf68 = 1068, e_sf69 = 1069, e_sf70 = 1070, e_sf71 = 1071,
         e_sf72 = 1072, e_sf73 = 1073, e_sf74 = 1074, e_sf75 = 1075,
         e_sf76 = 1076, e_sf77 = 1077, e_sf78 = 1078, e_sf79 = 1079,
         e_sf80 = 1080, e_sf81 = 1081, e_sf82 = 1082, e_sf83 = 1083,
         e_sf84 = 1084, e_sf85 = 1085, e_sf86 = 1086, e_sf87 = 1087,
         e_sf88 = 1088, e_sf89 = 1089, e_sf90 = 1090, e_sf91 = 1091,
         e_sf92 = 1092, e_sf93 = 1093, e_sf94 = 1094, e_sf95 = 1095,
         e_sf96 = 1096, e_sf97 = 1097, e_sf98 = 1098, e_sf99 = 1099,
         e_sffinal  = 1100,
         e_sf4ext00 = 2000, e_sf4ext01 = 2001, e_sf4ext02 = 2002, e_sf4ext03 = 2003,
         e_sf4ext04 = 2004, e_sf4ext05 = 2005, e_sf4ext06 = 2006, e_sf4ext07 = 2007,
         e_sf4ext08 = 2008, e_sf4ext09 = 2009, e_sf4ext10 = 2010, e_sf4ext11 = 2011,
         e_sf4ext12 = 2012, e_sf4ext13 = 2013, e_sf4ext14 = 2014, e_sf4ext15 = 2015,
         e_sf4ext16 = 2016, e_sf4ext17 = 2017, e_sf4ext18 = 2018, e_sf4ext19 = 2019,
         e_sf4ext20 = 2020, e_sf4ext21 = 2021, e_sf4ext22 = 2022, e_sf4ext23 = 2023,
         e_sf4ext24 = 2024, e_sf4ext25 = 2025, e_sf4ext26 = 2026, e_sf4ext27 = 2027,
         e_sf4ext28 = 2028, e_sf4ext29 = 2029, e_sf4ext30 = 2030, e_sf4ext31 = 2031,
         e_sf4ext32 = 2032, e_sf4ext33 = 2033, e_sf4ext34 = 2034, e_sf4ext35 = 2035,
         e_sf4ext36 = 2036, e_sf4ext37 = 2037, e_sf4ext38 = 2038, e_sf4ext39 = 2039,
         e_sf4ext40 = 2040, e_sf4ext41 = 2041, e_sf4ext42 = 2042, e_sf4ext43 = 2043,
         e_sf4ext44 = 2044, e_sf4ext45 = 2045, e_sf4ext46 = 2046, e_sf4ext47 = 2047,
         e_sf4ext48 = 2048, e_sf4ext49 = 2049, e_sf4ext50 = 2050, e_sf4ext51 = 2051,
         e_sf4ext52 = 2052, e_sf4ext53 = 2053, e_sf4ext54 = 2054, e_sf4ext55 = 2055,
         e_sf4ext56 = 2056, e_sf4ext57 = 2057, e_sf4ext58 = 2058, e_sf4ext59 = 2059,
         e_sf4ext60 = 2060, e_sf4ext61 = 2061
      };

      inline std::string to_str(const operator_type opr)
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

      inline bool check_significance(const operator_type _op1, const operator_type _op2){
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

      struct base_operation_t
      {
         base_operation_t(const operator_type t, const unsigned int& np)
         : type(t)
         , num_params(np)
         {}

         operator_type type;
         unsigned int num_params;
      };

      namespace loop_unroll
      {
         const unsigned int global_loop_batch_size = 16;

         struct details
         {
            explicit details(const std::size_t& vsize,
                             const unsigned int loop_batch_size = global_loop_batch_size)
            : batch_size(loop_batch_size   )
            , remainder (vsize % batch_size)
            , upper_bound(static_cast<int>(vsize - (remainder ? loop_batch_size : 0)))
            {}

            unsigned int batch_size;
            int remainder;
            int upper_bound;
         };
      }

      #ifdef exprtk_enable_debugging
      inline void dump_ptr(const std::string& s, const void* ptr, const std::size_t size = 0)
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
      inline void dump_ptr(const std::string&, const void*) {}
      inline void dump_ptr(const std::string&, const void*, const std::size_t) {}
      #endif

      template <typename T>
      class vec_data_store
      {
      public:

         typedef vec_data_store<T> type;
         typedef T* data_t;

      private:

         struct control_block
         {
            control_block()
            : ref_count(1)
            , size     (0)
            , data     (0)
            , destruct (true)
            {}

            explicit control_block(const std::size_t& dsize)
            : ref_count(1    )
            , size     (dsize)
            , data     (0    )
            , destruct (true )
            { create_data(); }

            control_block(const std::size_t& dsize, data_t dptr, bool dstrct = false)
            : ref_count(1     )
            , size     (dsize )
            , data     (dptr  )
            , destruct (dstrct)
            {}

           ~control_block()
            {
               if (data && destruct && (0 == ref_count))
               {
                  dump_ptr("~vec_data_store::control_block() data",data);
                  delete[] data;
                  data = reinterpret_cast<data_t>(0);
               }
            }

            static inline control_block* create(const std::size_t& dsize, data_t data_ptr = data_t(0), bool dstrct = false)
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

            static inline void destroy(control_block*& cntrl_blck)
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

            std::size_t ref_count;
            std::size_t size;
            data_t      data;
            bool        destruct;

         private:

            control_block(const control_block&) exprtk_delete;
            control_block& operator=(const control_block&) exprtk_delete;

            inline void create_data()
            {
               destruct = true;
               data     = new T[size];
               std::fill_n(data, size, T(0));
               dump_ptr("control_block::create_data() - data", data, size);
            }
         };

      public:

         vec_data_store()
         : control_block_(control_block::create(0))
         {}

         explicit vec_data_store(const std::size_t& size)
         : control_block_(control_block::create(size,reinterpret_cast<data_t>(0),true))
         {}

         vec_data_store(const std::size_t& size, data_t data, bool dstrct = false)
         : control_block_(control_block::create(size, data, dstrct))
         {}

         vec_data_store(const type& vds)
         {
            control_block_ = vds.control_block_;
            control_block_->ref_count++;
         }

        ~vec_data_store()
         {
            control_block::destroy(control_block_);
         }

         type& operator=(const type& vds)
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

         inline data_t data()
         {
            return control_block_->data;
         }

         inline data_t data() const
         {
            return control_block_->data;
         }

         inline std::size_t size() const
         {
            return control_block_->size;
         }

         inline data_t& ref()
         {
            return control_block_->data;
         }

         inline void dump() const
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

         static inline void match_sizes(type& vds0, type& vds1)
         {
            const std::size_t size = min_size(vds0.control_block_,vds1.control_block_);
            vds0.control_block_->size = size;
            vds1.control_block_->size = size;
         }

      private:

         static inline std::size_t min_size(const control_block* cb0, const control_block* cb1)
         {
            const std::size_t size0 = cb0->size;
            const std::size_t size1 = cb1->size;

            if (size0 && size1)
               return std::min(size0,size1);
            else
               return (size0) ? size0 : size1;
         }

         control_block* control_block_;
      };

      namespace numeric
      {
         namespace details
         {
            template <typename T>
            inline T process_impl(const operator_type operation, const T arg)
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
            inline T process_impl(const operator_type operation, const T arg0, const T arg1)
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
         inline T process(const operator_type operation, const T arg)
         {
            return Essa::Math::details::numeric::details::process_impl(operation,arg);
         }

         template <typename T>
         inline T process(const operator_type operation, const T arg0, const T arg1)
         {
            return Essa::Math::details::numeric::details::process_impl(operation, arg0, arg1);
         }
      }

      template <typename Node>
      struct node_collector_interface
      {
         typedef Node* node_ptr_t;
         typedef Node** node_pp_t;
         typedef std::vector<node_pp_t> noderef_list_t;

         virtual ~node_collector_interface() {}

         virtual void collect_nodes(noderef_list_t&) {}
      };

      template <typename Node>
      struct node_depth_base;

      template <typename T>
      class expression_node : public node_collector_interface<expression_node<T> >,
                              public node_depth_base<expression_node<T> >
      {
      public:

         enum node_type
         {
            e_none          , e_null          , e_constant    , e_unary        ,
            e_binary        , e_binary_ext    , e_trinary     , e_quaternary   ,
            e_vararg        , e_conditional   , e_while       , e_repeat       ,
            e_for           , e_switch        , e_mswitch     , e_return       ,
            e_retenv        , e_variable      , e_stringvar   , e_stringconst  ,
            e_stringvarrng  , e_cstringvarrng , e_strgenrange , e_strconcat    ,
            e_stringvarsize , e_strswap       , e_stringsize  , e_stringvararg ,
            e_function      , e_vafunction    , e_genfunction , e_strfunction  ,
            e_strcondition  , e_strccondition , e_add         , e_sub          ,
            e_mul           , e_div           , e_mod         , e_pow          ,
            e_lt            , e_lte           , e_gt          , e_gte          ,
            e_eq            , e_ne            , e_and         , e_nand         ,
            e_or            , e_nor           , e_xor         , e_xnor         ,
            e_in            , e_like          , e_ilike       , e_inranges     ,
            e_ipow          , e_ipowinv       , e_abs         , e_acos         ,
            e_acosh         , e_asin          , e_asinh       , e_atan         ,
            e_atanh         , e_ceil          , e_cos         , e_cosh         ,
            e_exp           , e_expm1         , e_floor       , e_log          ,
            e_log10         , e_log2          , e_log1p       , e_neg          ,
            e_pos           , e_round         , e_sin         , e_sinc         ,
            e_sinh          , e_sqrt          , e_tan         , e_tanh         ,
            e_cot           , e_sec           , e_csc         , e_r2d          ,
            e_d2r           , e_d2g           , e_g2d         , e_notl         ,
            e_sgn           , e_erf           , e_erfc        , e_ncdf         ,
            e_frac          , e_trunc         , e_uvouv       , e_vov          ,
            e_cov           , e_voc           , e_vob         , e_bov          ,
            e_cob           , e_boc           , e_vovov       , e_vovoc        ,
            e_vocov         , e_covov         , e_covoc       , e_vovovov      ,
            e_vovovoc       , e_vovocov       , e_vocovov     , e_covovov      ,
            e_covocov       , e_vocovoc       , e_covovoc     , e_vococov      ,
            e_sf3ext        , e_sf4ext        , e_nulleq      , e_strass       ,
            e_vector        , e_vecelem       , e_rbvecelem   , e_rbveccelem   ,
            e_vecdefass     , e_vecvalass     , e_vecvecass   , e_vecopvalass  ,
            e_vecopvecass   , e_vecfunc       , e_vecvecswap  , e_vecvecineq   ,
            e_vecvalineq    , e_valvecineq    , e_vecvecarith , e_vecvalarith  ,
            e_valvecarith   , e_vecunaryop    , e_vecondition , e_break        ,
            e_continue      , e_swap
         };

         typedef T value_type;
         typedef expression_node<T>* expression_ptr;
         typedef node_collector_interface<expression_node<T> > nci_t;
         typedef typename nci_t::noderef_list_t noderef_list_t;
         typedef node_depth_base<expression_node<T> > ndb_t;

         virtual ~expression_node() {}

         inline virtual T value() const
         {
            return std::numeric_limits<T>::quiet_NaN();
         }

         inline virtual expression_node<T>* branch(const std::size_t& index = 0) const
         {
            return reinterpret_cast<expression_ptr>(index * 0);
         }

         inline virtual node_type type() const
         {
            return e_none;
         }

         inline virtual std::string to_string() const {
            return "(expression_node)";
         }
      }; // class expression_node

      template <typename T>
      inline bool is_generally_string_node(const expression_node<T>* node);

      inline bool is_true(const int16_t v)
      {
         return std::not_equal_to()(0.0,v);
      }

      inline bool is_true(const int32_t v)
      {
         return std::not_equal_to()(0.0,v);
      }

      inline bool is_true(const int64_t v)
      {
         return std::not_equal_to()(0.0,v);
      }

      inline bool is_true(const float v)
      {
         return std::not_equal_to()(0.0,v);
      }

      inline bool is_true(const double v)
      {
         return std::not_equal_to()(0.0,v);
      }

      inline bool is_true(const long double v)
      {
         return std::not_equal_to()(0.0,v);
      }

      inline bool is_true(const std::complex<float> v)
      {
         return std::not_equal_to()(std::complex<float>(0.0),v);
      }

      inline bool is_true(const std::complex<double> v)
      {
         return std::not_equal_to()(std::complex<double>(0.0),v);
      }

      inline bool is_true(const std::complex<long double> v)
      {
         return std::not_equal_to()(std::complex<long double>(0.0),v);
      }

      template <typename T>
      inline bool is_true(const expression_node<T>* node)
      {
         return std::not_equal_to<T>()(T(0),node->value());
      }

      template <typename T>
      inline bool is_true(const std::pair<expression_node<T>*,bool>& node)
      {
         return std::not_equal_to<T>()(T(0),node.first->value());
      }

      template <typename T>
      inline bool is_false(const expression_node<T>* node)
      {
         return std::equal_to<T>()(T(0),node->value());
      }

      template <typename T>
      inline bool is_false(const std::pair<expression_node<T>*,bool>& node)
      {
         return std::equal_to<T>()(T(0),node.first->value());
      }

      template <typename T>
      inline bool is_unary_node(const expression_node<T>* node)
      {
         return node && (details::expression_node<T>::e_unary == node->type());
      }

      template <typename T>
      inline bool is_neg_unary_node(const expression_node<T>* node)
      {
         return node && (details::expression_node<T>::e_neg == node->type());
      }

      template <typename T>
      inline bool is_binary_node(const expression_node<T>* node)
      {
         return node && (details::expression_node<T>::e_binary == node->type());
      }

      template <typename T>
      inline bool is_variable_node(const expression_node<T>* node)
      {
         return node && (details::expression_node<T>::e_variable == node->type());
      }

      template <typename T>
      inline bool is_ivariable_node(const expression_node<T>* node)
      {
         return node &&
                (
                  details::expression_node<T>::e_variable   == node->type() ||
                  details::expression_node<T>::e_vecelem    == node->type() ||
                  details::expression_node<T>::e_rbvecelem  == node->type() ||
                  details::expression_node<T>::e_rbveccelem == node->type()
                );
      }

      template <typename T>
      inline bool is_vector_elem_node(const expression_node<T>* node)
      {
         return node && (details::expression_node<T>::e_vecelem == node->type());
      }

      template <typename T>
      inline bool is_rebasevector_elem_node(const expression_node<T>* node)
      {
         return node && (details::expression_node<T>::e_rbvecelem == node->type());
      }

      template <typename T>
      inline bool is_rebasevector_celem_node(const expression_node<T>* node)
      {
         return node && (details::expression_node<T>::e_rbveccelem == node->type());
      }

      template <typename T>
      inline bool is_vector_node(const expression_node<T>* node)
      {
         return node && (details::expression_node<T>::e_vector == node->type());
      }

      template <typename T>
      inline bool is_ivector_node(const expression_node<T>* node)
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

      template <typename T>
      inline bool is_constant_node(const expression_node<T>* node)
      {
         return node &&
         (
           details::expression_node<T>::e_constant    == node->type() ||
           details::expression_node<T>::e_stringconst == node->type()
         );
      }

      template <typename T>
      inline bool is_null_node(const expression_node<T>* node)
      {
         return node && (details::expression_node<T>::e_null == node->type());
      }

      template <typename T>
      inline bool is_break_node(const expression_node<T>* node)
      {
         return node && (details::expression_node<T>::e_break == node->type());
      }

      template <typename T>
      inline bool is_continue_node(const expression_node<T>* node)
      {
         return node && (details::expression_node<T>::e_continue == node->type());
      }

      template <typename T>
      inline bool is_swap_node(const expression_node<T>* node)
      {
         return node && (details::expression_node<T>::e_swap == node->type());
      }

      template <typename T>
      inline bool is_function(const expression_node<T>* node)
      {
         return node && (details::expression_node<T>::e_function == node->type());
      }

      template <typename T>
      inline bool is_return_node(const expression_node<T>* node)
      {
         return node && (details::expression_node<T>::e_return == node->type());
      }

      template <typename T> class unary_node;

      template <typename T>
      inline bool is_negate_node(const expression_node<T>* node)
      {
         if (node && is_unary_node(node))
         {
            return (details::e_neg == static_cast<const unary_node<T>*>(node)->operation());
         }
         else
            return false;
      }

      template <typename T>
      inline bool branch_deletable(expression_node<T>* node)
      {
         return (0 != node)             &&
                !is_variable_node(node) &&
                !is_string_node  (node) ;
      }

      template <std::size_t N, typename T>
      inline bool all_nodes_valid(expression_node<T>* (&b)[N])
      {
         for (std::size_t i = 0; i < N; ++i)
         {
            if (0 == b[i]) return false;
         }

         return true;
      }

      template <typename T,
                typename Allocator,
                template <typename, typename> class Sequence>
      inline bool all_nodes_valid(const Sequence<expression_node<T>*,Allocator>& b)
      {
         for (std::size_t i = 0; i < b.size(); ++i)
         {
            if (0 == b[i]) return false;
         }

         return true;
      }

      template <std::size_t N, typename T>
      inline bool all_nodes_variables(expression_node<T>* (&b)[N])
      {
         for (std::size_t i = 0; i < N; ++i)
         {
            if (0 == b[i])
               return false;
            else if (!is_variable_node(b[i]))
               return false;
         }

         return true;
      }

      template <typename T,
                typename Allocator,
                template <typename, typename> class Sequence>
      inline bool all_nodes_variables(Sequence<expression_node<T>*,Allocator>& b)
      {
         for (std::size_t i = 0; i < b.size(); ++i)
         {
            if (0 == b[i])
               return false;
            else if (!is_variable_node(b[i]))
               return false;
         }

         return true;
      }

      template <typename Node>
      class node_collection_destructor
      {
      public:

         typedef node_collector_interface<Node> nci_t;

         typedef typename nci_t::node_ptr_t     node_ptr_t;
         typedef typename nci_t::node_pp_t      node_pp_t;
         typedef typename nci_t::noderef_list_t noderef_list_t;

         static void delete_nodes(node_ptr_t& root)
         {
            std::vector<node_pp_t> node_delete_list;
            node_delete_list.reserve(1000);

            collect_nodes(root, node_delete_list);

            for (std::size_t i = 0; i < node_delete_list.size(); ++i)
            {
               node_ptr_t& node = *node_delete_list[i];
               exprtk_debug(("ncd::delete_nodes() - deleting: %p\n", static_cast<void*>(node)));
               delete node;
               node = reinterpret_cast<node_ptr_t>(0);
            }
         }

      private:

         static void collect_nodes(node_ptr_t& root, noderef_list_t& node_delete_list)
         {
            std::deque<node_ptr_t> node_list;
            node_list.push_back(root);
            node_delete_list.push_back(&root);

            noderef_list_t child_node_delete_list;
            child_node_delete_list.reserve(1000);

            while (!node_list.empty())
            {
               node_list.front()->collect_nodes(child_node_delete_list);

               if (!child_node_delete_list.empty())
               {
                  for (std::size_t i = 0; i < child_node_delete_list.size(); ++i)
                  {
                     node_pp_t& node = child_node_delete_list[i];

                     if (0 == (*node))
                     {
                        exprtk_debug(("ncd::collect_nodes() - null node encountered.\n"));
                     }

                     node_list.push_back(*node);
                  }

                  node_delete_list.insert(
                     node_delete_list.end(),
                     child_node_delete_list.begin(), child_node_delete_list.end());

                  child_node_delete_list.clear();
               }

               node_list.pop_front();
            }

            std::reverse(node_delete_list.begin(), node_delete_list.end());
         }
      };

      template <typename NodeAllocator, typename T, std::size_t N>
      inline void free_all_nodes(NodeAllocator& node_allocator, expression_node<T>* (&b)[N])
      {
         for (std::size_t i = 0; i < N; ++i)
         {
            free_node(node_allocator,b[i]);
         }
      }

      template <typename NodeAllocator,
                typename T,
                typename Allocator,
                template <typename, typename> class Sequence>
      inline void free_all_nodes(NodeAllocator& node_allocator, Sequence<expression_node<T>*,Allocator>& b)
      {
         for (std::size_t i = 0; i < b.size(); ++i)
         {
            free_node(node_allocator,b[i]);
         }

         b.clear();
      }

      template <typename NodeAllocator, typename T>
      inline void free_node(NodeAllocator&, expression_node<T>*& node)
      {
         if ((0 == node) || is_variable_node(node) || is_string_node(node))
         {
            return;
         }

         node_collection_destructor<expression_node<T> >
            ::delete_nodes(node);
      }

      template <typename T>
      inline void destroy_node(expression_node<T>*& node)
      {
         if (0 != node)
         {
            node_collection_destructor<expression_node<T> >
               ::delete_nodes(node);
         }
      }

      template <typename Node>
      struct node_depth_base
      {
         typedef Node* node_ptr_t;
         typedef std::pair<node_ptr_t,bool> nb_pair_t;

         node_depth_base()
         : depth_set(false)
         , depth(0)
         {}

         virtual ~node_depth_base() {}

         virtual std::size_t node_depth() const { return 1; }

         std::size_t compute_node_depth(const Node* const& node) const
         {
            if (!depth_set)
            {
               depth = 1 + (node ? node->node_depth() : 0);
               depth_set = true;
            }

            return depth;
         }

         std::size_t compute_node_depth(const nb_pair_t& branch) const
         {
            if (!depth_set)
            {
               depth = 1 + (branch.first ? branch.first->node_depth() : 0);
               depth_set = true;
            }

            return depth;
         }

         template <std::size_t N>
         std::size_t compute_node_depth(const nb_pair_t (&branch)[N]) const
         {
            if (!depth_set)
            {
               depth = 0;
               for (std::size_t i = 0; i < N; ++i)
               {
                  if (branch[i].first)
                  {
                     depth = std::max(depth,branch[i].first->node_depth());
                  }
               }
               depth += 1;
               depth_set = true;
            }

            return depth;
         }

         template <typename BranchType>
         std::size_t compute_node_depth(const BranchType& n0, const BranchType& n1) const
         {
            if (!depth_set)
            {
               depth = 1 + std::max(compute_node_depth(n0), compute_node_depth(n1));
               depth_set = true;
            }

            return depth;
         }

         template <typename BranchType>
         std::size_t compute_node_depth(const BranchType& n0, const BranchType& n1,
                                        const BranchType& n2) const
         {
            if (!depth_set)
            {
               depth = 1 + std::max(
                              std::max(compute_node_depth(n0), compute_node_depth(n1)),
                              compute_node_depth(n2));
               depth_set = true;
            }

            return depth;
         }

         template <typename BranchType>
         std::size_t compute_node_depth(const BranchType& n0, const BranchType& n1,
                                        const BranchType& n2, const BranchType& n3) const
         {
            if (!depth_set)
            {
               depth = 1 + std::max(
                           std::max(compute_node_depth(n0), compute_node_depth(n1)),
                           std::max(compute_node_depth(n2), compute_node_depth(n3)));
               depth_set = true;
            }

            return depth;
         }

         template <typename Allocator,
                   template <typename, typename> class Sequence>
         std::size_t compute_node_depth(const Sequence<node_ptr_t, Allocator>& branch_list) const
         {
            if (!depth_set)
            {
               for (std::size_t i = 0; i < branch_list.size(); ++i)
               {
                  if (branch_list[i])
                  {
                     depth = std::max(depth, compute_node_depth(branch_list[i]));
                  }
               }
               depth_set = true;
            }

            return depth;
         }

         template <typename Allocator,
                   template <typename, typename> class Sequence>
         std::size_t compute_node_depth(const Sequence<nb_pair_t,Allocator>& branch_list) const
         {
            if (!depth_set)
            {
               for (std::size_t i = 0; i < branch_list.size(); ++i)
               {
                  if (branch_list[i].first)
                  {
                     depth = std::max(depth, compute_node_depth(branch_list[i].first));
                  }
               }
               depth_set = true;
            }

            return depth;
         }

         mutable bool depth_set;
         mutable std::size_t depth;

         template <typename NodeSequence>
         void collect(node_ptr_t const& node,
                      const bool deletable,
                      NodeSequence& delete_node_list) const
         {
            if ((0 != node) && deletable)
            {
               delete_node_list.push_back(const_cast<node_ptr_t*>(&node));
            }
         }

         template <typename NodeSequence>
         void collect(const nb_pair_t& branch,
                      NodeSequence& delete_node_list) const
         {
            collect(branch.first, branch.second, delete_node_list);
         }

         template <typename NodeSequence>
         void collect(Node*& node,
                      NodeSequence& delete_node_list) const
         {
            collect(node, branch_deletable(node), delete_node_list);
         }

         template <std::size_t N, typename NodeSequence>
         void collect(const nb_pair_t(&branch)[N],
                      NodeSequence& delete_node_list) const
         {
            for (std::size_t i = 0; i < N; ++i)
            {
               collect(branch[i].first, branch[i].second, delete_node_list);
            }
         }

         template <typename Allocator,
                   template <typename, typename> class Sequence,
                   typename NodeSequence>
         void collect(const Sequence<nb_pair_t, Allocator>& branch,
                      NodeSequence& delete_node_list) const
         {
            for (std::size_t i = 0; i < branch.size(); ++i)
            {
               collect(branch[i].first, branch[i].second, delete_node_list);
            }
         }

         template <typename Allocator,
                   template <typename, typename> class Sequence,
                   typename NodeSequence>
         void collect(const Sequence<node_ptr_t, Allocator>& branch_list,
                      NodeSequence& delete_node_list) const
         {
            for (std::size_t i = 0; i < branch_list.size(); ++i)
            {
               collect(branch_list[i], branch_deletable(branch_list[i]), delete_node_list);
            }
         }

         template <typename Boolean,
                   typename AllocatorT,
                   typename AllocatorB,
                   template <typename, typename> class Sequence,
                   typename NodeSequence>
         void collect(const Sequence<node_ptr_t, AllocatorT>& branch_list,
                      const Sequence<Boolean, AllocatorB>& branch_deletable_list,
                      NodeSequence& delete_node_list) const
         {
            for (std::size_t i = 0; i < branch_list.size(); ++i)
            {
               collect(branch_list[i], branch_deletable_list[i], delete_node_list);
            }
         }
      };
      inline void load_operations_map(std::multimap<std::string,details::base_operation_t,details::ilesscompare>& m)
      {
         #define register_op(Symbol, Type, Args)                                             \
         m.insert(std::make_pair(std::string(Symbol),details::base_operation_t(Type,Args))); \

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

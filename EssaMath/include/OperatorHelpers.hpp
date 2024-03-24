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

#include "include/Numeric.hpp"
#include <deque>
#include <vector>
#include <map>
#include <algorithm>

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

      std::string to_str(const operator_type opr);
      bool check_significance(const operator_type _op1, const operator_type _op2);

      struct base_operation_t
      {
         base_operation_t(const operator_type t, const unsigned int& np);

         operator_type type;
         unsigned int num_params;
      };

      namespace loop_unroll
      {
         extern const unsigned int global_loop_batch_size;

         struct details
         {
            explicit details(const std::size_t& vsize,
                             const unsigned int loop_batch_size = global_loop_batch_size);

            unsigned int batch_size;
            int remainder;
            int upper_bound;
         };
      }

      #ifdef exprtk_enable_debugging
      void dump_ptr(const std::string& s, const void* ptr, const std::size_t size = 0);
      #else
      void dump_ptr(const std::string&, const void*);
      void dump_ptr(const std::string&, const void*, const std::size_t);
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
            control_block();

            explicit control_block(const std::size_t& dsize);

            control_block(const std::size_t& dsize, data_t dptr, bool dstrct = false);

           ~control_block();

            static control_block* create(const std::size_t& dsize, data_t data_ptr = data_t(0), bool dstrct = false);

            static void destroy(control_block*& cntrl_blck);

            std::size_t ref_count;
            std::size_t size;
            data_t      data;
            bool        destruct;

         private:

            control_block(const control_block&) exprtk_delete;
            control_block& operator=(const control_block&) exprtk_delete;

            void create_data();
         };

      public:

         vec_data_store();

         explicit vec_data_store(const std::size_t& size);

         vec_data_store(const std::size_t& size, data_t data, bool dstrct = false);

         vec_data_store(const type& vds);

        ~vec_data_store();

         type& operator=(const type& vds);
         data_t data();
         data_t data() const;

         std::size_t size() const;
         data_t& ref();

         void dump() const;

         static void match_sizes(type& vds0, type& vds1);

      private:

         static std::size_t min_size(const control_block* cb0, const control_block* cb1);

         control_block* control_block_;
      };

      namespace numeric
      {
         template <typename T>
         T process(const operator_type operation, const T arg);

         template <typename T>
         T process(const operator_type operation, const T arg0, const T arg1);
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
      class expression_node;

      template <typename T>
      inline bool is_generally_string_node(const expression_node<T>* node);

      bool is_true(const int16_t v);

      bool is_true(const int32_t v);

      bool is_true(const int64_t v);

      bool is_true(const float v);

      bool is_true(const double v);

      bool is_true(const long double v);

      bool is_true(const std::complex<float> v);

      bool is_true(const std::complex<double> v);

      bool is_true(const std::complex<long double> v);

      template <typename T>
      bool is_true(const expression_node<T>* node);

      template <typename T>
      bool is_true(const std::pair<expression_node<T>*,bool>& node);

      template <typename T>
      bool is_false(const expression_node<T>* node);

      template <typename T>
      bool is_false(const std::pair<expression_node<T>*,bool>& node);

      template <typename T>
      bool is_unary_node(const expression_node<T>* node);

      template <typename T>
      bool is_neg_unary_node(const expression_node<T>* node);

      template <typename T>
      bool is_binary_node(const expression_node<T>* node);

      template <typename T>
      bool is_variable_node(const expression_node<T>* node);

      template <typename T>
      bool is_ivariable_node(const expression_node<T>* node);

      template <typename T>
      bool is_vector_elem_node(const expression_node<T>* node);

      template <typename T>
      bool is_rebasevector_elem_node(const expression_node<T>* node);

      template <typename T>
      bool is_rebasevector_celem_node(const expression_node<T>* node);

      template <typename T>
      bool is_vector_node(const expression_node<T>* node);

      template <typename T>
      bool is_ivector_node(const expression_node<T>* node);

      template <typename T>
      bool is_constant_node(const expression_node<T>* node);

      template <typename T>
      bool is_null_node(const expression_node<T>* node);

      template <typename T>
      bool is_break_node(const expression_node<T>* node);

      template <typename T>
      bool is_continue_node(const expression_node<T>* node);

      template <typename T>
      bool is_swap_node(const expression_node<T>* node);

      template <typename T>
      bool is_function(const expression_node<T>* node);

      template <typename T>
      bool is_return_node(const expression_node<T>* node);

      template <typename T> class unary_node;

      template <typename T>
      bool is_negate_node(const expression_node<T>* node);

      template <typename T>
      bool branch_deletable(const expression_node<T>* node);

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

      void load_operations_map(std::multimap<std::string,details::base_operation_t,details::ilesscompare>& m);
   }
}

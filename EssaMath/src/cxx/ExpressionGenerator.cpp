#include "include/ExpressionGenerator.hpp"
#include "include/Parser.hpp"

namespace Essa::Math{

        template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::error_node(){
         return ::Essa::Math::parser<T>::error_node();
        }
    
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

        template<typename T>
         struct synthesize_vov_expression
         {
            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               const T& v1 = static_cast<details::variable_node<T>*>(branch[0])->ref();
               const T& v2 = static_cast<details::variable_node<T>*>(branch[1])->ref();

               switch (operation)
               {
                  #define case_stmt(op0, op1)                                                      \
                  case op0 : return expr_gen.node_allocator()->                                     \
                                template allocate_rr<typename details::vov_node<T,op1<T> > > \
                                   (v1, v2);                                                       \

                  basic_opr_switch_statements
                  extended_opr_switch_statements
                  #undef case_stmt
                  default : return expression_generator<T>::error_node();
               }
            }
         };

        template<typename T>
         struct synthesize_cov_expression
         {
            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               const T  c = static_cast<details::literal_node<T>*> (branch[0])->value();
               const T& v = static_cast<details::variable_node<T>*>(branch[1])->ref  ();

               details::free_node(*(expr_gen.node_allocator()),branch[0]);

               if (std::equal_to<T>()(T(0),c) && (details::e_mul == operation))
                  return expr_gen(T(0));
               else if (std::equal_to<T>()(T(0),c) && (details::e_div == operation))
                  return expr_gen(T(0));
               else if (std::equal_to<T>()(T(0),c) && (details::e_add == operation))
                  return static_cast<details::variable_node<T>*>(branch[1]);
               else if (std::equal_to<T>()(T(1),c) && (details::e_mul == operation))
                  return static_cast<details::variable_node<T>*>(branch[1]);

               switch (operation)
               {
                  #define case_stmt(op0, op1)                                                      \
                  case op0 : return expr_gen.node_allocator()->                                     \
                                template allocate_cr<typename details::cov_node<T,op1<T> > > \
                                   (c, v);                                                         \

                  basic_opr_switch_statements
                  extended_opr_switch_statements
                  #undef case_stmt
                  default : return expression_generator<T>::error_node();
               }
            }
         };

        template<typename T>
         struct synthesize_voc_expression
         {
            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               const T& v = static_cast<details::variable_node<T>*>(branch[0])->ref  ();
               const T  c = static_cast<details::literal_node<T>*> (branch[1])->value();

               details::free_node(*(expr_gen.node_allocator()), branch[1]);

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
                  return static_cast<details::variable_node<T>*>(branch[0]);
               else if (std::equal_to<T>()(T(1),c) && (details::e_mul == operation))
                  return static_cast<details::variable_node<T>*>(branch[0]);
               else if (std::equal_to<T>()(T(1),c) && (details::e_div == operation))
                  return static_cast<details::variable_node<T>*>(branch[0]);

               switch (operation)
               {
                  #define case_stmt(op0, op1)                                                      \
                  case op0 : return expr_gen.node_allocator()->                                     \
                                template allocate_rc<typename details::voc_node<T,op1<T> > > \
                                   (v, c);                                                         \

                  basic_opr_switch_statements
                  extended_opr_switch_statements
                  #undef case_stmt
                  default : return expression_generator<T>::error_node();
               }
            }
         };

        template<typename T>
         struct synthesize_sf3ext_expression
         {
            template <typename T0, typename T1, typename T2>
            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& sf3opr,
                                                      T0 t0, T1 t1, T2 t2)
            {
               switch (sf3opr)
               {
                  #define case_stmt(op)                                                                              \
                  case details::e_sf##op : return details::T0oT1oT2_sf3ext<T,T0,T1,T2,details::sf##op##_op<T> >:: \
                                allocate(*(expr_gen.node_allocator()), t0, t1, t2);                                   \

                  case_stmt(00) case_stmt(01) case_stmt(02) case_stmt(03)
                  case_stmt(04) case_stmt(05) case_stmt(06) case_stmt(07)
                  case_stmt(08) case_stmt(09) case_stmt(10) case_stmt(11)
                  case_stmt(12) case_stmt(13) case_stmt(14) case_stmt(15)
                  case_stmt(16) case_stmt(17) case_stmt(18) case_stmt(19)
                  case_stmt(20) case_stmt(21) case_stmt(22) case_stmt(23)
                  case_stmt(24) case_stmt(25) case_stmt(26) case_stmt(27)
                  case_stmt(28) case_stmt(29) case_stmt(30)
                  #undef case_stmt
                  default : return expression_generator<T>::error_node();
               }
            }

            template <typename T0, typename T1, typename T2>
            static bool compile(expression_generator<T>& expr_gen, const std::string& id,
                                       T0 t0, T1 t1, T2 t2,
                                       details::expression_node<T>*& result)
            {
               details::operator_type sf3opr;

               if (!expr_gen.sf3_optimisable(id,sf3opr))
                  return false;
               else
                  result = synthesize_sf3ext_expression<T>::template process<T0, T1, T2>
                              (expr_gen, sf3opr, t0, t1, t2);

               return true;
            }
         };

        template<typename T>
         struct synthesize_sf4ext_expression
         {
            template <typename T0, typename T1, typename T2, typename T3>
            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& sf4opr,
                                                      T0 t0, T1 t1, T2 t2, T3 t3)
            {
               switch (sf4opr)
               {
                  #define case_stmt0(op)                                                                                      \
                  case details::e_sf##op : return details::T0oT1oT2oT3_sf4ext<T,T0,T1,T2,T3,details::sf##op##_op<T> >:: \
                                allocate(*(expr_gen.node_allocator()), t0, t1, t2, t3);                                        \

                  #define case_stmt1(op)                                                                                             \
                  case details::e_sf4ext##op : return details::T0oT1oT2oT3_sf4ext<T,T0,T1,T2,T3,details::sfext##op##_op<T> >:: \
                                allocate(*(expr_gen.node_allocator()), t0, t1, t2, t3);                                               \

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
                  default : return expression_generator<T>::error_node();
               }
            }

            template <typename T0, typename T1, typename T2, typename T3>
            static bool compile(expression_generator<T>& expr_gen, const std::string& id,
                                       T0 t0, T1 t1, T2 t2, T3 t3,
                                       details::expression_node<T>*& result)
            {
               details::operator_type sf4opr;

               if (!expr_gen.sf4_optimisable(id,sf4opr))
                  return false;
               else
                  result = synthesize_sf4ext_expression<T>::template process<T0, T1, T2, T3>
                              (expr_gen, sf4opr, t0, t1, t2, t3);

               return true;
            }

            // T o (sf3ext)
            template <typename ExternalType>
            static bool compile_right(expression_generator<T>& expr_gen,
                                             ExternalType t,
                                             const details::operator_type& operation,
                                             details::expression_node<T>*& sf3node,
                                             details::expression_node<T>*& result)
            {
               if (!details::is_sf3ext_node(sf3node))
                  return false;

               typedef details::T0oT1oT2_base_node<T>* sf3ext_base_ptr;

               sf3ext_base_ptr n = static_cast<sf3ext_base_ptr>(sf3node);
               const std::string id = "t" + expr_gen.to_str(operation) + "(" + n->type_id() + ")";

               switch (n->type())
               {
                  case details::expression_node<T>::e_covoc : return compile_right_impl
                                                                    <typename expression_generator<T>::covoc_t::sf3_type_node,ExternalType, typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::ctype>
                                                                       (expr_gen, id, t, sf3node, result);

                  case details::expression_node<T>::e_covov : return compile_right_impl
                                                                    <typename expression_generator<T>::covov_t::sf3_type_node,ExternalType, typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>
                                                                       (expr_gen, id, t, sf3node, result);

                  case details::expression_node<T>::e_vocov : return compile_right_impl
                                                                    <typename expression_generator<T>::vocov_t::sf3_type_node,ExternalType, typename expression_generator<T>::vtype, typename expression_generator<T>::ctype, typename expression_generator<T>::vtype>
                                                                       (expr_gen, id, t, sf3node, result);

                  case details::expression_node<T>::e_vovoc : return compile_right_impl
                                                                    <typename expression_generator<T>::vovoc_t::sf3_type_node,ExternalType, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype, typename expression_generator<T>::ctype>
                                                                       (expr_gen, id, t, sf3node, result);

                  case details::expression_node<T>::e_vovov : return compile_right_impl
                                                                    <typename expression_generator<T>::vovov_t::sf3_type_node,ExternalType, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>
                                                                       (expr_gen, id, t, sf3node, result);

                  default                                      : return false;
               }
            }

            // (sf3ext) o T
            template <typename ExternalType>
            static bool compile_left(expression_generator<T>& expr_gen,
                                            ExternalType t,
                                            const details::operator_type& operation,
                                            details::expression_node<T>*& sf3node,
                                            details::expression_node<T>*& result)
            {
               if (!details::is_sf3ext_node(sf3node))
                  return false;

               typedef details::T0oT1oT2_base_node<T>* sf3ext_base_ptr;

               sf3ext_base_ptr n = static_cast<sf3ext_base_ptr>(sf3node);

               const std::string id = "(" + n->type_id() + ")" + expr_gen.to_str(operation) + "t";

               switch (n->type())
               {
                  case details::expression_node<T>::e_covoc : return compile_left_impl
                                                                    <typename expression_generator<T>::covoc_t::sf3_type_node,ExternalType, typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::ctype>
                                                                       (expr_gen, id, t, sf3node, result);

                  case details::expression_node<T>::e_covov : return compile_left_impl
                                                                    <typename expression_generator<T>::covov_t::sf3_type_node,ExternalType, typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>
                                                                       (expr_gen, id, t, sf3node, result);

                  case details::expression_node<T>::e_vocov : return compile_left_impl
                                                                    <typename expression_generator<T>::vocov_t::sf3_type_node,ExternalType, typename expression_generator<T>::vtype, typename expression_generator<T>::ctype, typename expression_generator<T>::vtype>
                                                                       (expr_gen, id, t, sf3node, result);

                  case details::expression_node<T>::e_vovoc : return compile_left_impl
                                                                    <typename expression_generator<T>::vovoc_t::sf3_type_node,ExternalType, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype, typename expression_generator<T>::ctype>
                                                                       (expr_gen, id, t, sf3node, result);

                  case details::expression_node<T>::e_vovov : return compile_left_impl
                                                                    <typename expression_generator<T>::vovov_t::sf3_type_node,ExternalType, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>
                                                                       (expr_gen, id, t, sf3node, result);

                  default                                      : return false;
               }
            }

            template <typename SF3TypeNode, typename ExternalType, typename T0, typename T1, typename T2>
            static bool compile_right_impl(expression_generator<T>& expr_gen,
                                                  const std::string& id,
                                                  ExternalType t,
                                                  details::expression_node<T>*& node,
                                                  details::expression_node<T>*& result)
            {
               SF3TypeNode* n = dynamic_cast<SF3TypeNode*>(node);

               if (n)
               {
                  T0 t0 = n->t0();
                  T1 t1 = n->t1();
                  T2 t2 = n->t2();

                  return synthesize_sf4ext_expression<T>::template compile<ExternalType, T0, T1, T2>
                            (expr_gen, id, t, t0, t1, t2, result);
               }
               else
                  return false;
            }

            template <typename SF3TypeNode, typename ExternalType, typename T0, typename T1, typename T2>
            static bool compile_left_impl(expression_generator<T>& expr_gen,
                                                 const std::string& id,
                                                 ExternalType t,
                                                 details::expression_node<T>*& node,
                                                 details::expression_node<T>*& result)
            {
               SF3TypeNode* n = dynamic_cast<SF3TypeNode*>(node);

               if (n)
               {
                  T0 t0 = n->t0();
                  T1 t1 = n->t1();
                  T2 t2 = n->t2();

                  return synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, ExternalType>
                            (expr_gen, id, t0, t1, t2, t, result);
               }
               else
                  return false;
            }
         };

        template<typename T>
         struct synthesize_vovov_expression0
         {
            typedef typename expression_generator<T>::vovov_t::type0 node_type;
            typedef typename expression_generator<T>::vovov_t::sf3_type sf3_type;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // (v0 o0 v1) o1 (v2)
               const details::vov_base_node<T>* vov = static_cast<details::vov_base_node<T>*>(branch[0]);
               const T& v0 = vov->v0();
               const T& v1 = vov->v1();
               const T& v2 = static_cast<details::variable_node<T>*>(branch[1])->ref();
               const details::operator_type o0 = vov->operation();
               const details::operator_type o1 = operation;

               details::free_node(*(expr_gen.node_allocator()),branch[0]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               if (expr_gen.parser()->settings().strength_reduction_enabled())
               {
                  // (v0 / v1) / v2 --> (vovov) v0 / (v1 * v2)
                  if ((details::e_div == o0) && (details::e_div == o1))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::vtype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "t/(t*t)", v0, v1, v2, result);

                     exprtk_debug(("(v0 / v1) / v2 --> (vovov) v0 / (v1 * v2)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
               }

               const bool synthesis_result =
                  synthesize_sf3ext_expression<T>::template compile<typename expression_generator<T>::vtype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>
                     (expr_gen, id(expr_gen, o0, o1), v0, v1, v2, result);

               if (synthesis_result)
                  return result;

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return expression_generator<T>::error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator()), v0, v1, v2, f0, f1);
            }

            static std::string id(expression_generator<T>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1)
            {
               return details::build_string()
                         << "(t" << expr_gen.to_str(o0)
                         << "t)" << expr_gen.to_str(o1)
                         << "t";
            }
         };

        template<typename T>
         struct synthesize_vovov_expression1
         {
            typedef typename expression_generator<T>::vovov_t::type1 node_type;
            typedef typename expression_generator<T>::vovov_t::sf3_type sf3_type;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // (v0) o0 (v1 o1 v2)
               const details::vov_base_node<T>* vov = static_cast<details::vov_base_node<T>*>(branch[1]);
               const T& v0 = static_cast<details::variable_node<T>*>(branch[0])->ref();
               const T& v1 = vov->v0();
               const T& v2 = vov->v1();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = vov->operation();

               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               if (expr_gen.parser()->settings().strength_reduction_enabled())
               {
                  // v0 / (v1 / v2) --> (vovov) (v0 * v2) / v1
                  if ((details::e_div == o0) && (details::e_div == o1))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::vtype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "(t*t)/t", v0, v2, v1, result);

                     exprtk_debug(("v0 / (v1 / v2) --> (vovov) (v0 * v2) / v1\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
               }

               const bool synthesis_result =
                  synthesize_sf3ext_expression<T>::template compile<typename expression_generator<T>::vtype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>
                     (expr_gen, id(expr_gen, o0, o1), v0, v1, v2, result);

               if (synthesis_result)
                  return result;

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return expression_generator<T>::error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator()), v0, v1, v2, f0, f1);
            }

            static std::string id(expression_generator<T>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1)
            {
               return details::build_string()
                         << "t"  << expr_gen.to_str(o0)
                         << "(t" << expr_gen.to_str(o1)
                         << "t)";
            }
         };

        template<typename T>
         struct synthesize_vovoc_expression0
         {
            typedef typename expression_generator<T>::vovoc_t::type0 node_type;
            typedef typename expression_generator<T>::vovoc_t::sf3_type sf3_type;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // (v0 o0 v1) o1 (c)
               const details::vov_base_node<T>* vov = static_cast<details::vov_base_node<T>*>(branch[0]);
               const T& v0 = vov->v0();
               const T& v1 = vov->v1();
               const T   c = static_cast<details::literal_node<T>*>(branch[1])->value();
               const details::operator_type o0 = vov->operation();
               const details::operator_type o1 = operation;

               details::free_node(*(expr_gen.node_allocator()),branch[0]);
               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               if (expr_gen.parser()->settings().strength_reduction_enabled())
               {
                  // (v0 / v1) / c --> (vovoc) v0 / (v1 * c)
                  if ((details::e_div == o0) && (details::e_div == o1))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::vtype, typename expression_generator<T>::vtype, typename expression_generator<T>::ctype>(expr_gen, "t/(t*t)", v0, v1, c, result);

                     exprtk_debug(("(v0 / v1) / c --> (vovoc) v0 / (v1 * c)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
               }

               const bool synthesis_result =
                  synthesize_sf3ext_expression<T>::template compile<typename expression_generator<T>::vtype, typename expression_generator<T>::vtype, typename expression_generator<T>::ctype>
                     (expr_gen, id(expr_gen, o0, o1), v0, v1, c, result);

               if (synthesis_result)
                  return result;

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return expression_generator<T>::error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator()), v0, v1, c, f0, f1);
            }

            static std::string id(expression_generator<T>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1)
            {
               return details::build_string()
                         << "(t" << expr_gen.to_str(o0)
                         << "t)" << expr_gen.to_str(o1)
                         << "t";
            }
         };

        template<typename T>
         struct synthesize_vovoc_expression1
         {
            typedef typename expression_generator<T>::vovoc_t::type1 node_type;
            typedef typename expression_generator<T>::vovoc_t::sf3_type sf3_type;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // (v0) o0 (v1 o1 c)
               const details::voc_base_node<T>* voc = static_cast<const details::voc_base_node<T>*>(branch[1]);
               const T& v0 = static_cast<details::variable_node<T>*>(branch[0])->ref();
               const T& v1 = voc->v();
               const T   c = voc->c();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = voc->operation();

               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               if (expr_gen.parser()->settings().strength_reduction_enabled())
               {
                  // v0 / (v1 / c) --> (vocov) (v0 * c) / v1
                  if ((details::e_div == o0) && (details::e_div == o1))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::vtype, typename expression_generator<T>::ctype, typename expression_generator<T>::vtype>(expr_gen, "(t*t)/t", v0, c, v1, result);

                     exprtk_debug(("v0 / (v1 / c) --> (vocov) (v0 * c) / v1\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
               }

               const bool synthesis_result =
                  synthesize_sf3ext_expression<T>::template compile<typename expression_generator<T>::vtype, typename expression_generator<T>::vtype, typename expression_generator<T>::ctype>
                     (expr_gen, id(expr_gen, o0, o1), v0, v1, c, result);

               if (synthesis_result)
                  return result;

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return expression_generator<T>::error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator()), v0, v1, c, f0, f1);
            }

            static std::string id(expression_generator<T>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1)
            {
               return details::build_string()
                         << "t"  << expr_gen.to_str(o0)
                         << "(t" << expr_gen.to_str(o1)
                         << "t)";
            }
         };

        template<typename T>
         struct synthesize_vocov_expression0
         {
            typedef typename expression_generator<T>::vocov_t::type0 node_type;
            typedef typename expression_generator<T>::vocov_t::sf3_type sf3_type;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // (v0 o0 c) o1 (v1)
               const details::voc_base_node<T>* voc = static_cast<details::voc_base_node<T>*>(branch[0]);
               const T& v0 = voc->v();
               const T   c = voc->c();
               const T& v1 = static_cast<details::variable_node<T>*>(branch[1])->ref();
               const details::operator_type o0 = voc->operation();
               const details::operator_type o1 = operation;

               details::free_node(*(expr_gen.node_allocator()),branch[0]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               if (expr_gen.parser()->settings().strength_reduction_enabled())
               {
                  // (v0 / c) / v1 --> (vovoc) v0 / (v1 * c)
                  if ((details::e_div == o0) && (details::e_div == o1))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::vtype, typename expression_generator<T>::vtype, typename expression_generator<T>::ctype>(expr_gen, "t/(t*t)", v0, v1, c, result);

                     exprtk_debug(("(v0 / c) / v1 --> (vovoc) v0 / (v1 * c)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
               }

               const bool synthesis_result =
                  synthesize_sf3ext_expression<T>::template compile<typename expression_generator<T>::vtype, typename expression_generator<T>::ctype, typename expression_generator<T>::vtype>
                     (expr_gen, id(expr_gen, o0, o1), v0, c, v1, result);

               if (synthesis_result)
                  return result;

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return expression_generator<T>::error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator()), v0, c, v1, f0, f1);
            }

            static std::string id(expression_generator<T>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1)
            {
               return details::build_string()
                         << "(t" << expr_gen.to_str(o0)
                         << "t)" << expr_gen.to_str(o1)
                         << "t";
            }
         };

        template<typename T>
         struct synthesize_vocov_expression1
         {
            typedef typename expression_generator<T>::vocov_t::type1 node_type;
            typedef typename expression_generator<T>::vocov_t::sf3_type sf3_type;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // (v0) o0 (c o1 v1)
               const details::cov_base_node<T>* cov = static_cast<details::cov_base_node<T>*>(branch[1]);
               const T& v0 = static_cast<details::variable_node<T>*>(branch[0])->ref();
               const T   c = cov->c();
               const T& v1 = cov->v();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = cov->operation();

               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               if (expr_gen.parser()->settings().strength_reduction_enabled())
               {
                  // v0 / (c / v1) --> (vovoc) (v0 * v1) / c
                  if ((details::e_div == o0) && (details::e_div == o1))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::vtype, typename expression_generator<T>::vtype, typename expression_generator<T>::ctype>(expr_gen, "(t*t)/t", v0, v1, c, result);

                     exprtk_debug(("v0 / (c / v1) --> (vovoc) (v0 * v1) / c\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
               }

               const bool synthesis_result =
                  synthesize_sf3ext_expression<T>::template compile<typename expression_generator<T>::vtype, typename expression_generator<T>::ctype, typename expression_generator<T>::vtype>
                     (expr_gen, id(expr_gen, o0, o1), v0, c, v1, result);

               if (synthesis_result)
                  return result;

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return expression_generator<T>::error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator()), v0, c, v1, f0, f1);
            }

            static std::string id(expression_generator<T>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1)
            {
               return details::build_string()
                         << "t"  << expr_gen.to_str(o0)
                         << "(t" << expr_gen.to_str(o1)
                         << "t)";
            }
         };

        template<typename T>
         struct synthesize_covov_expression0
         {
            typedef typename expression_generator<T>::covov_t::type0 node_type;
            typedef typename expression_generator<T>::covov_t::sf3_type sf3_type;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // (c o0 v0) o1 (v1)
               const details::cov_base_node<T>* cov = static_cast<details::cov_base_node<T>*>(branch[0]);
               const T   c = cov->c();
               const T& v0 = cov->v();
               const T& v1 = static_cast<details::variable_node<T>*>(branch[1])->ref();
               const details::operator_type o0 = cov->operation();
               const details::operator_type o1 = operation;

               details::free_node(*(expr_gen.node_allocator()),branch[0]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               if (expr_gen.parser()->settings().strength_reduction_enabled())
               {
                  // (c / v0) / v1 --> (covov) c / (v0 * v1)
                  if ((details::e_div == o0) && (details::e_div == o1))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "t/(t*t)", c, v0, v1, result);

                     exprtk_debug(("(c / v0) / v1 --> (covov) c / (v0 * v1)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
               }

               const bool synthesis_result =
                  synthesize_sf3ext_expression<T>::template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>
                     (expr_gen, id(expr_gen, o0, o1), c, v0, v1, result);

               if (synthesis_result)
                  return result;

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return expression_generator<T>::error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator()), c, v0, v1, f0, f1);
            }

            static std::string id(expression_generator<T>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1)
            {
               return details::build_string()
                         << "(t" << expr_gen.to_str(o0)
                         << "t)" << expr_gen.to_str(o1)
                         << "t";
            }
         };

        template<typename T>
         struct synthesize_covov_expression1
         {
            typedef typename expression_generator<T>::covov_t::type1 node_type;
            typedef typename expression_generator<T>::covov_t::sf3_type sf3_type;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // (c) o0 (v0 o1 v1)
               const details::vov_base_node<T>* vov = static_cast<details::vov_base_node<T>*>(branch[1]);
               const T   c = static_cast<details::literal_node<T>*>(branch[0])->value();
               const T& v0 = vov->v0();
               const T& v1 = vov->v1();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = vov->operation();

               details::free_node(*(expr_gen.node_allocator()),branch[0]);
               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               if (expr_gen.parser()->settings().strength_reduction_enabled())
               {
                  // c / (v0 / v1) --> (covov) (c * v1) / v0
                  if ((details::e_div == o0) && (details::e_div == o1))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "(t*t)/t", c, v1, v0, result);

                     exprtk_debug(("c / (v0 / v1) --> (covov) (c * v1) / v0\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
               }

               const bool synthesis_result =
                  synthesize_sf3ext_expression<T>::template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>
                     (expr_gen, id(expr_gen, o0, o1), c, v0, v1, result);

               if (synthesis_result)
                  return result;

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return expression_generator<T>::error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator()), c, v0, v1, f0, f1);
            }

            static std::string id(expression_generator<T>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1)
            {
               return details::build_string()
                         << "t"  << expr_gen.to_str(o0)
                         << "(t" << expr_gen.to_str(o1)
                         << "t)";
            }
         };

        template<typename T>
         struct synthesize_covoc_expression0
         {
            typedef typename expression_generator<T>::covoc_t::type0 node_type;
            typedef typename expression_generator<T>::covoc_t::sf3_type sf3_type;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // (c0 o0 v) o1 (c1)
               const details::cov_base_node<T>* cov = static_cast<details::cov_base_node<T>*>(branch[0]);
               const T  c0 = cov->c();
               const T&  v = cov->v();
               const T  c1 = static_cast<details::literal_node<T>*>(branch[1])->value();
               const details::operator_type o0 = cov->operation();
               const details::operator_type o1 = operation;

               details::free_node(*(expr_gen.node_allocator()),branch[0]);
               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               if (expr_gen.parser()->settings().strength_reduction_enabled())
               {
                  // (c0 + v) + c1 --> (cov) (c0 + c1) + v
                  if ((details::e_add == o0) && (details::e_add == o1))
                  {
                     exprtk_debug(("(c0 + v) + c1 --> (cov) (c0 + c1) + v\n"));

                     return expr_gen.node_allocator()->
                               template allocate_cr<typename details::cov_node<T,details::add_op<T> > >(c0 + c1, v);
                  }
                  // (c0 + v) - c1 --> (cov) (c0 - c1) + v
                  else if ((details::e_add == o0) && (details::e_sub == o1))
                  {
                     exprtk_debug(("(c0 + v) - c1 --> (cov) (c0 - c1) + v\n"));

                     return expr_gen.node_allocator()->
                               template allocate_cr<typename details::cov_node<T,details::add_op<T> > >(c0 - c1, v);
                  }
                  // (c0 - v) + c1 --> (cov) (c0 + c1) - v
                  else if ((details::e_sub == o0) && (details::e_add == o1))
                  {
                     exprtk_debug(("(c0 - v) + c1 --> (cov) (c0 + c1) - v\n"));

                     return expr_gen.node_allocator()->
                               template allocate_cr<typename details::cov_node<T,details::sub_op<T> > >(c0 + c1, v);
                  }
                  // (c0 - v) - c1 --> (cov) (c0 - c1) - v
                  else if ((details::e_sub == o0) && (details::e_sub == o1))
                  {
                     exprtk_debug(("(c0 - v) - c1 --> (cov) (c0 - c1) - v\n"));

                     return expr_gen.node_allocator()->
                               template allocate_cr<typename details::cov_node<T,details::sub_op<T> > >(c0 - c1, v);
                  }
                  // (c0 * v) * c1 --> (cov) (c0 * c1) * v
                  else if ((details::e_mul == o0) && (details::e_mul == o1))
                  {
                     exprtk_debug(("(c0 * v) * c1 --> (cov) (c0 * c1) * v\n"));

                     return expr_gen.node_allocator()->
                               template allocate_cr<typename details::cov_node<T,details::mul_op<T> > >(c0 * c1, v);
                  }
                  // (c0 * v) / c1 --> (cov) (c0 / c1) * v
                  else if ((details::e_mul == o0) && (details::e_div == o1))
                  {
                     exprtk_debug(("(c0 * v) / c1 --> (cov) (c0 / c1) * v\n"));

                     return expr_gen.node_allocator()->
                               template allocate_cr<typename details::cov_node<T,details::mul_op<T> > >(c0 / c1, v);
                  }
                  // (c0 / v) * c1 --> (cov) (c0 * c1) / v
                  else if ((details::e_div == o0) && (details::e_mul == o1))
                  {
                     exprtk_debug(("(c0 / v) * c1 --> (cov) (c0 * c1) / v\n"));

                     return expr_gen.node_allocator()->
                               template allocate_cr<typename details::cov_node<T,details::div_op<T> > >(c0 * c1, v);
                  }
                  // (c0 / v) / c1 --> (cov) (c0 / c1) / v
                  else if ((details::e_div == o0) && (details::e_div == o1))
                  {
                     exprtk_debug(("(c0 / v) / c1 --> (cov) (c0 / c1) / v\n"));

                     return expr_gen.node_allocator()->
                               template allocate_cr<typename details::cov_node<T,details::div_op<T> > >(c0 / c1, v);
                  }
               }

               const bool synthesis_result =
                  synthesize_sf3ext_expression<T>::template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::ctype>
                     (expr_gen, id(expr_gen, o0, o1), c0, v, c1, result);

               if (synthesis_result)
                  return result;

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return expression_generator<T>::error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator()), c0, v, c1, f0, f1);
            }

            static std::string id(expression_generator<T>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1)
            {
               return details::build_string()
                         << "(t" << expr_gen.to_str(o0)
                         << "t)" << expr_gen.to_str(o1)
                         << "t";
            }
         };

        template<typename T>
         struct synthesize_covoc_expression1
         {
            typedef typename expression_generator<T>::covoc_t::type1 node_type;
            typedef typename expression_generator<T>::covoc_t::sf3_type sf3_type;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // (c0) o0 (v o1 c1)
               const details::voc_base_node<T>* voc = static_cast<details::voc_base_node<T>*>(branch[1]);
               const T  c0 = static_cast<details::literal_node<T>*>(branch[0])->value();
               const T&  v = voc->v();
               const T  c1 = voc->c();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = voc->operation();

               details::free_node(*(expr_gen.node_allocator()),branch[0]);
               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               if (expr_gen.parser()->settings().strength_reduction_enabled())
               {
                  // (c0) + (v + c1) --> (cov) (c0 + c1) + v
                  if ((details::e_add == o0) && (details::e_add == o1))
                  {
                     exprtk_debug(("(c0) + (v + c1) --> (cov) (c0 + c1) + v\n"));

                     return expr_gen.node_allocator()->
                               template allocate_cr<typename details::cov_node<T,details::add_op<T> > >(c0 + c1, v);
                  }
                  // (c0) + (v - c1) --> (cov) (c0 - c1) + v
                  else if ((details::e_add == o0) && (details::e_sub == o1))
                  {
                     exprtk_debug(("(c0) + (v - c1) --> (cov) (c0 - c1) + v\n"));

                     return expr_gen.node_allocator()->
                               template allocate_cr<typename details::cov_node<T,details::add_op<T> > >(c0 - c1, v);
                  }
                  // (c0) - (v + c1) --> (cov) (c0 - c1) - v
                  else if ((details::e_sub == o0) && (details::e_add == o1))
                  {
                     exprtk_debug(("(c0) - (v + c1) --> (cov) (c0 - c1) - v\n"));

                     return expr_gen.node_allocator()->
                               template allocate_cr<typename details::cov_node<T,details::sub_op<T> > >(c0 - c1, v);
                  }
                  // (c0) - (v - c1) --> (cov) (c0 + c1) - v
                  else if ((details::e_sub == o0) && (details::e_sub == o1))
                  {
                     exprtk_debug(("(c0) - (v - c1) --> (cov) (c0 + c1) - v\n"));

                     return expr_gen.node_allocator()->
                               template allocate_cr<typename details::cov_node<T,details::sub_op<T> > >(c0 + c1, v);
                  }
                  // (c0) * (v * c1) --> (voc) v * (c0 * c1)
                  else if ((details::e_mul == o0) && (details::e_mul == o1))
                  {
                     exprtk_debug(("(c0) * (v * c1) --> (voc) v * (c0 * c1)\n"));

                     return expr_gen.node_allocator()->
                               template allocate_cr<typename details::cov_node<T,details::mul_op<T> > >(c0 * c1, v);
                  }
                  // (c0) * (v / c1) --> (cov) (c0 / c1) * v
                  else if ((details::e_mul == o0) && (details::e_div == o1))
                  {
                     exprtk_debug(("(c0) * (v / c1) --> (cov) (c0 / c1) * v\n"));

                     return expr_gen.node_allocator()->
                               template allocate_cr<typename details::cov_node<T,details::mul_op<T> > >(c0 / c1, v);
                  }
                  // (c0) / (v * c1) --> (cov) (c0 / c1) / v
                  else if ((details::e_div == o0) && (details::e_mul == o1))
                  {
                     exprtk_debug(("(c0) / (v * c1) --> (cov) (c0 / c1) / v\n"));

                     return expr_gen.node_allocator()->
                               template allocate_cr<typename details::cov_node<T,details::div_op<T> > >(c0 / c1, v);
                  }
                  // (c0) / (v / c1) --> (cov) (c0 * c1) / v
                  else if ((details::e_div == o0) && (details::e_div == o1))
                  {
                     exprtk_debug(("(c0) / (v / c1) --> (cov) (c0 * c1) / v\n"));

                     return expr_gen.node_allocator()->
                               template allocate_cr<typename details::cov_node<T,details::div_op<T> > >(c0 * c1, v);
                  }
               }

               const bool synthesis_result =
                  synthesize_sf3ext_expression<T>::template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::ctype>
                     (expr_gen, id(expr_gen, o0, o1), c0, v, c1, result);

               if (synthesis_result)
                  return result;

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return expression_generator<T>::error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator()), c0, v, c1, f0, f1);
            }

            static std::string id(expression_generator<T>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1)
            {
               return details::build_string()
                         << "t"  << expr_gen.to_str(o0)
                         << "(t" << expr_gen.to_str(o1)
                         << "t)";
            }
         };

        template<typename T>
         struct synthesize_cocov_expression0
         {
            typedef typename expression_generator<T>::cocov_t::type0 node_type;
            static details::expression_node<T>* process(expression_generator<T>&,
                                                      const details::operator_type&,
                                                      details::expression_node<T>* (&)[2])
            {
               // (c0 o0 c1) o1 (v) - Not possible.
               return expression_generator<T>::error_node();
            }
         };

        template<typename T>
         struct synthesize_cocov_expression1
         {
            typedef typename expression_generator<T>::cocov_t::type1 node_type;
            typedef typename expression_generator<T>::cocov_t::sf3_type sf3_type;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // (c0) o0 (c1 o1 v)
               const details::cov_base_node<T>* cov = static_cast<details::cov_base_node<T>*>(branch[1]);
               const T  c0 = static_cast<details::literal_node<T>*>(branch[0])->value();
               const T  c1 = cov->c();
               const T&  v = cov->v();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = cov->operation();

               details::free_node(*(expr_gen.node_allocator()),branch[0]);
               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               if (expr_gen.parser()->settings().strength_reduction_enabled())
               {
                  // (c0) + (c1 + v) --> (cov) (c0 + c1) + v
                  if ((details::e_add == o0) && (details::e_add == o1))
                  {
                     exprtk_debug(("(c0) + (c1 + v) --> (cov) (c0 + c1) + v\n"));

                     return expr_gen.node_allocator()->
                               template allocate_cr<typename details::cov_node<T,details::add_op<T> > >(c0 + c1, v);
                  }
                  // (c0) + (c1 - v) --> (cov) (c0 + c1) - v
                  else if ((details::e_add == o0) && (details::e_sub == o1))
                  {
                     exprtk_debug(("(c0) + (c1 - v) --> (cov) (c0 + c1) - v\n"));

                     return expr_gen.node_allocator()->
                               template allocate_cr<typename details::cov_node<T,details::sub_op<T> > >(c0 + c1, v);
                  }
                  // (c0) - (c1 + v) --> (cov) (c0 - c1) - v
                  else if ((details::e_sub == o0) && (details::e_add == o1))
                  {
                     exprtk_debug(("(c0) - (c1 + v) --> (cov) (c0 - c1) - v\n"));

                     return expr_gen.node_allocator()->
                               template allocate_cr<typename details::cov_node<T,details::sub_op<T> > >(c0 - c1, v);
                  }
                  // (c0) - (c1 - v) --> (cov) (c0 - c1) + v
                  else if ((details::e_sub == o0) && (details::e_sub == o1))
                  {
                     exprtk_debug(("(c0) - (c1 - v) --> (cov) (c0 - c1) + v\n"));

                     return expr_gen.node_allocator()->
                               template allocate_cr<typename details::cov_node<T,details::add_op<T> > >(c0 - c1, v);
                  }
                  // (c0) * (c1 * v) --> (cov) (c0 * c1) * v
                  else if ((details::e_mul == o0) && (details::e_mul == o1))
                  {
                     exprtk_debug(("(c0) * (c1 * v) --> (cov) (c0 * c1) * v\n"));

                     return expr_gen.node_allocator()->
                               template allocate_cr<typename details::cov_node<T,details::mul_op<T> > >(c0 * c1, v);
                  }
                  // (c0) * (c1 / v) --> (cov) (c0 * c1) / v
                  else if ((details::e_mul == o0) && (details::e_div == o1))
                  {
                     exprtk_debug(("(c0) * (c1 / v) --> (cov) (c0 * c1) / v\n"));

                     return expr_gen.node_allocator()->
                               template allocate_cr<typename details::cov_node<T,details::div_op<T> > >(c0 * c1, v);
                  }
                  // (c0) / (c1 * v) --> (cov) (c0 / c1) / v
                  else if ((details::e_div == o0) && (details::e_mul == o1))
                  {
                     exprtk_debug(("(c0) / (c1 * v) --> (cov) (c0 / c1) / v\n"));

                     return expr_gen.node_allocator()->
                               template allocate_cr<typename details::cov_node<T,details::div_op<T> > >(c0 / c1, v);
                  }
                  // (c0) / (c1 / v) --> (cov) (c0 / c1) * v
                  else if ((details::e_div == o0) && (details::e_div == o1))
                  {
                     exprtk_debug(("(c0) / (c1 / v) --> (cov) (c0 / c1) * v\n"));

                     return expr_gen.node_allocator()->
                               template allocate_cr<typename details::cov_node<T,details::mul_op<T> > >(c0 / c1, v);
                  }
               }

               const bool synthesis_result =
                  synthesize_sf3ext_expression<T>::template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::ctype, typename expression_generator<T>::vtype>
                     (expr_gen, id(expr_gen, o0, o1), c0, c1, v, result);

               if (synthesis_result)
                  return result;

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return expression_generator<T>::error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator()), c0, c1, v, f0, f1);
            }

            static std::string id(expression_generator<T>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1)
            {
               return details::build_string()
                         << "t"  << expr_gen.to_str(o0)
                         << "(t" << expr_gen.to_str(o1)
                         << "t)";
            }
         };

        template<typename T>
         struct synthesize_vococ_expression0
         {
            typedef typename expression_generator<T>::vococ_t::type0 node_type;
            typedef typename expression_generator<T>::vococ_t::sf3_type sf3_type;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // (v o0 c0) o1 (c1)
               const details::voc_base_node<T>* voc = static_cast<details::voc_base_node<T>*>(branch[0]);
               const T&  v = voc->v();
               const T& c0 = voc->c();
               const T& c1 = static_cast<details::literal_node<T>*>(branch[1])->value();
               const details::operator_type o0 = voc->operation();
               const details::operator_type o1 = operation;

               details::free_node(*(expr_gen.node_allocator()),branch[0]);
               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               if (expr_gen.parser()->settings().strength_reduction_enabled())
               {
                  // (v + c0) + c1 --> (voc) v + (c0 + c1)
                  if ((details::e_add == o0) && (details::e_add == o1))
                  {
                     exprtk_debug(("(v + c0) + c1 --> (voc) v + (c0 + c1)\n"));

                     return expr_gen.node_allocator()->
                               template allocate_rc<typename details::voc_node<T,details::add_op<T> > >(v, c0 + c1);
                  }
                  // (v + c0) - c1 --> (voc) v + (c0 - c1)
                  else if ((details::e_add == o0) && (details::e_sub == o1))
                  {
                     exprtk_debug(("(v + c0) - c1 --> (voc) v + (c0 - c1)\n"));

                     return expr_gen.node_allocator()->
                               template allocate_rc<typename details::voc_node<T,details::add_op<T> > >(v, c0 - c1);
                  }
                  // (v - c0) + c1 --> (voc) v - (c0 + c1)
                  else if ((details::e_sub == o0) && (details::e_add == o1))
                  {
                     exprtk_debug(("(v - c0) + c1 --> (voc) v - (c0 + c1)\n"));

                     return expr_gen.node_allocator()->
                               template allocate_rc<typename details::voc_node<T,details::add_op<T> > >(v, c1 - c0);
                  }
                  // (v - c0) - c1 --> (voc) v - (c0 + c1)
                  else if ((details::e_sub == o0) && (details::e_sub == o1))
                  {
                     exprtk_debug(("(v - c0) - c1 --> (voc) v - (c0 + c1)\n"));

                     return expr_gen.node_allocator()->
                               template allocate_rc<typename details::voc_node<T,details::sub_op<T> > >(v, c0 + c1);
                  }
                  // (v * c0) * c1 --> (voc) v * (c0 * c1)
                  else if ((details::e_mul == o0) && (details::e_mul == o1))
                  {
                     exprtk_debug(("(v * c0) * c1 --> (voc) v * (c0 * c1)\n"));

                     return expr_gen.node_allocator()->
                               template allocate_rc<typename details::voc_node<T,details::mul_op<T> > >(v, c0 * c1);
                  }
                  // (v * c0) / c1 --> (voc) v * (c0 / c1)
                  else if ((details::e_mul == o0) && (details::e_div == o1))
                  {
                     exprtk_debug(("(v * c0) / c1 --> (voc) v * (c0 / c1)\n"));

                     return expr_gen.node_allocator()->
                               template allocate_rc<typename details::voc_node<T,details::mul_op<T> > >(v, c0 / c1);
                  }
                  // (v / c0) * c1 --> (voc) v * (c1 / c0)
                  else if ((details::e_div == o0) && (details::e_mul == o1))
                  {
                     exprtk_debug(("(v / c0) * c1 --> (voc) v * (c1 / c0)\n"));

                     return expr_gen.node_allocator()->
                               template allocate_rc<typename details::voc_node<T,details::mul_op<T> > >(v, c1 / c0);
                  }
                  // (v / c0) / c1 --> (voc) v / (c0 * c1)
                  else if ((details::e_div == o0) && (details::e_div == o1))
                  {
                     exprtk_debug(("(v / c0) / c1 --> (voc) v / (c0 * c1)\n"));

                     return expr_gen.node_allocator()->
                               template allocate_rc<typename details::voc_node<T,details::div_op<T> > >(v, c0 * c1);
                  }
                  // (v ^ c0) ^ c1 --> (voc) v ^ (c0 * c1)
                  else if ((details::e_pow == o0) && (details::e_pow == o1))
                  {
                     exprtk_debug(("(v ^ c0) ^ c1 --> (voc) v ^ (c0 * c1)\n"));

                     return expr_gen.node_allocator()->
                               template allocate_rc<typename details::voc_node<T,details::pow_op<T> > >(v, c0 * c1);
                  }
               }

               const bool synthesis_result =
                  synthesize_sf3ext_expression<T>::template compile<typename expression_generator<T>::vtype, typename expression_generator<T>::ctype, typename expression_generator<T>::ctype>
                     (expr_gen, id(expr_gen, o0, o1), v, c0, c1, result);

               if (synthesis_result)
                  return result;

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return expression_generator<T>::error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator()), v, c0, c1, f0, f1);
            }

            static std::string id(expression_generator<T>& expr_gen,
                                         const details::operator_type o0,
                                         const details::operator_type o1)
            {
               return details::build_string()
                         << "(t" << expr_gen.to_str(o0)
                         << "t)" << expr_gen.to_str(o1)
                         << "t";
            }
         };

        template<typename T>
         struct synthesize_vococ_expression1
         {
            typedef typename expression_generator<T>::vococ_t::type0 node_type;

            static details::expression_node<T>* process(expression_generator<T>&,
                                                      const details::operator_type&,
                                                      details::expression_node<T>* (&)[2])
            {
               // (v) o0 (c0 o1 c1) - Not possible.
               exprtk_debug(("(v) o0 (c0 o1 c1) - Not possible.\n"));
               return expression_generator<T>::error_node();
            }
         };

        template<typename T>
         struct synthesize_vovovov_expression0
         {
            typedef typename expression_generator<T>::vovovov_t::type0 node_type;
            typedef typename expression_generator<T>::vovovov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // (v0 o0 v1) o1 (v2 o2 v3)
               const details::vov_base_node<T>* vov0 = static_cast<details::vov_base_node<T>*>(branch[0]);
               const details::vov_base_node<T>* vov1 = static_cast<details::vov_base_node<T>*>(branch[1]);
               const T& v0 = vov0->v0();
               const T& v1 = vov0->v1();
               const T& v2 = vov1->v0();
               const T& v3 = vov1->v1();
               const details::operator_type o0 = vov0->operation();
               const details::operator_type o1 = operation;
               const details::operator_type o2 = vov1->operation();

               details::free_node(*(expr_gen.node_allocator()),branch[0]);
               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               if (expr_gen.parser()->settings().strength_reduction_enabled())
               {
                  // (v0 / v1) * (v2 / v3) --> (vovovov) (v0 * v2) / (v1 * v3)
                  if ((details::e_div == o0) && (details::e_mul == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf4ext_expression<T>::
                           template compile<typename expression_generator<T>::vtype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "(t*t)/(t*t)", v0, v2, v1, v3, result);

                     exprtk_debug(("(v0 / v1) * (v2 / v3) --> (vovovov) (v0 * v2) / (v1 * v3)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (v0 / v1) / (v2 / v3) --> (vovovov) (v0 * v3) / (v1 * v2)
                  else if ((details::e_div == o0) && (details::e_div == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf4ext_expression<T>::
                           template compile<typename expression_generator<T>::vtype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "(t*t)/(t*t)", v0, v3, v1, v2, result);

                     exprtk_debug(("(v0 / v1) / (v2 / v3) --> (vovovov) (v0 * v3) / (v1 * v2)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (v0 + v1) / (v2 / v3) --> (vovovov) (v0 + v1) * (v3 / v2)
                  else if ((details::e_add == o0) && (details::e_div == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf4ext_expression<T>::
                           template compile<typename expression_generator<T>::vtype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "(t+t)*(t/t)", v0, v1, v3, v2, result);

                     exprtk_debug(("(v0 + v1) / (v2 / v3) --> (vovovov) (v0 + v1) * (v3 / v2)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (v0 - v1) / (v2 / v3) --> (vovovov) (v0 + v1) * (v3 / v2)
                  else if ((details::e_sub == o0) && (details::e_div == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf4ext_expression<T>::
                           template compile<typename expression_generator<T>::vtype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "(t-t)*(t/t)", v0, v1, v3, v2, result);

                     exprtk_debug(("(v0 - v1) / (v2 / v3) --> (vovovov) (v0 - v1) * (v3 / v2)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (v0 * v1) / (v2 / v3) --> (vovovov) ((v0 * v1) * v3) / v2
                  else if ((details::e_mul == o0) && (details::e_div == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf4ext_expression<T>::
                           template compile<typename expression_generator<T>::vtype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "((t*t)*t)/t", v0, v1, v3, v2, result);

                     exprtk_debug(("(v0 * v1) / (v2 / v3) --> (vovovov) ((v0 * v1) * v3) / v2\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
               }

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, v1, v2, v3, result);

               if (synthesis_result)
                  return result;

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f2 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return expression_generator<T>::error_node();
               else if (!expr_gen.valid_operator(o2,f2))
                  return expression_generator<T>::error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator()), v0, v1, v2, v3, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_vovovoc_expression0
         {
            typedef typename expression_generator<T>::vovovoc_t::type0 node_type;
            typedef typename expression_generator<T>::vovovoc_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // (v0 o0 v1) o1 (v2 o2 c)
               const details::vov_base_node<T>* vov = static_cast<details::vov_base_node<T>*>(branch[0]);
               const details::voc_base_node<T>* voc = static_cast<details::voc_base_node<T>*>(branch[1]);
               const T& v0 = vov->v0();
               const T& v1 = vov->v1();
               const T& v2 = voc->v ();
               const T   c = voc->c ();
               const details::operator_type o0 = vov->operation();
               const details::operator_type o1 = operation;
               const details::operator_type o2 = voc->operation();

               details::free_node(*(expr_gen.node_allocator()),branch[0]);
               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               if (expr_gen.parser()->settings().strength_reduction_enabled())
               {
                  // (v0 / v1) * (v2 / c) --> (vovovoc) (v0 * v2) / (v1 * c)
                  if ((details::e_div == o0) && (details::e_mul == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf4ext_expression<T>::
                           template compile<typename expression_generator<T>::vtype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype, typename expression_generator<T>::ctype>(expr_gen, "(t*t)/(t*t)", v0, v2, v1, c, result);

                     exprtk_debug(("(v0 / v1) * (v2 / c) --> (vovovoc) (v0 * v2) / (v1 * c)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (v0 / v1) / (v2 / c) --> (vocovov) (v0 * c) / (v1 * v2)
                  if ((details::e_div == o0) && (details::e_div == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf4ext_expression<T>::
                           template compile<typename expression_generator<T>::vtype, typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "(t*t)/(t*t)", v0, c, v1, v2, result);

                     exprtk_debug(("(v0 / v1) / (v2 / c) --> (vocovov) (v0 * c) / (v1 * v2)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
               }

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, v1, v2, c, result);

               if (synthesis_result)
                  return result;

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f2 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return expression_generator<T>::error_node();
               else if (!expr_gen.valid_operator(o2,f2))
                  return expression_generator<T>::error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator()), v0, v1, v2, c, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_vovocov_expression0
         {
            typedef typename expression_generator<T>::vovocov_t::type0 node_type;
            typedef typename expression_generator<T>::vovocov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // (v0 o0 v1) o1 (c o2 v2)
               const details::vov_base_node<T>* vov = static_cast<details::vov_base_node<T>*>(branch[0]);
               const details::cov_base_node<T>* cov = static_cast<details::cov_base_node<T>*>(branch[1]);
               const T& v0 = vov->v0();
               const T& v1 = vov->v1();
               const T& v2 = cov->v ();
               const T   c = cov->c ();
               const details::operator_type o0 = vov->operation();
               const details::operator_type o1 = operation;
               const details::operator_type o2 = cov->operation();

               details::free_node(*(expr_gen.node_allocator()),branch[0]);
               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               if (expr_gen.parser()->settings().strength_reduction_enabled())
               {
                  // (v0 / v1) * (c / v2) --> (vocovov) (v0 * c) / (v1 * v2)
                  if ((details::e_div == o0) && (details::e_mul == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf4ext_expression<T>::
                           template compile<typename expression_generator<T>::vtype, typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "(t*t)/(t*t)", v0, c, v1, v2, result);

                     exprtk_debug(("(v0 / v1) * (c / v2) --> (vocovov) (v0 * c) / (v1 * v2)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (v0 / v1) / (c / v2) --> (vovovoc) (v0 * v2) / (v1 * c)
                  if ((details::e_div == o0) && (details::e_div == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf4ext_expression<T>::
                           template compile<typename expression_generator<T>::vtype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype, typename expression_generator<T>::ctype>(expr_gen, "(t*t)/(t*t)", v0, v2, v1, c, result);

                     exprtk_debug(("(v0 / v1) / (c / v2) --> (vovovoc) (v0 * v2) / (v1 * c)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
               }

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, v1, c, v2, result);

               if (synthesis_result)
                  return result;

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f2 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return expression_generator<T>::error_node();
               else if (!expr_gen.valid_operator(o2,f2))
                  return expression_generator<T>::error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator()), v0, v1, c, v2, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_vocovov_expression0
         {
            typedef typename expression_generator<T>::vocovov_t::type0 node_type;
            typedef typename expression_generator<T>::vocovov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // (v0 o0 c) o1 (v1 o2 v2)
               const details::voc_base_node<T>* voc = static_cast<details::voc_base_node<T>*>(branch[0]);
               const details::vov_base_node<T>* vov = static_cast<details::vov_base_node<T>*>(branch[1]);
               const T   c = voc->c ();
               const T& v0 = voc->v ();
               const T& v1 = vov->v0();
               const T& v2 = vov->v1();
               const details::operator_type o0 = voc->operation();
               const details::operator_type o1 = operation;
               const details::operator_type o2 = vov->operation();

               details::free_node(*(expr_gen.node_allocator()),branch[0]);
               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               if (expr_gen.parser()->settings().strength_reduction_enabled())
               {
                  // (v0 / c) * (v1 / v2) --> (vovocov) (v0 * v1) / (c * v2)
                  if ((details::e_div == o0) && (details::e_mul == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf4ext_expression<T>::
                           template compile<typename expression_generator<T>::vtype, typename expression_generator<T>::vtype, typename expression_generator<T>::ctype, typename expression_generator<T>::vtype>(expr_gen, "(t*t)/(t*t)", v0, v1, c, v2, result);

                     exprtk_debug(("(v0 / c) * (v1 / v2) --> (vovocov) (v0 * v1) / (c * v2)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (v0 / c) / (v1 / v2) --> (vovocov) (v0 * v2) / (c * v1)
                  if ((details::e_div == o0) && (details::e_div == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf4ext_expression<T>::
                           template compile<typename expression_generator<T>::vtype, typename expression_generator<T>::vtype, typename expression_generator<T>::ctype, typename expression_generator<T>::vtype>(expr_gen, "(t*t)/(t*t)", v0, v2, c, v1, result);

                     exprtk_debug(("(v0 / c) / (v1 / v2) --> (vovocov) (v0 * v2) / (c * v1)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
               }

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, c, v1, v2, result);

               if (synthesis_result)
                  return result;

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f2 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return expression_generator<T>::error_node();
               else if (!expr_gen.valid_operator(o2,f2))
                  return expression_generator<T>::error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator()), v0, c, v1, v2, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_covovov_expression0
         {
            typedef typename expression_generator<T>::covovov_t::type0 node_type;
            typedef typename expression_generator<T>::covovov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // (c o0 v0) o1 (v1 o2 v2)
               const details::cov_base_node<T>* cov = static_cast<details::cov_base_node<T>*>(branch[0]);
               const details::vov_base_node<T>* vov = static_cast<details::vov_base_node<T>*>(branch[1]);
               const T   c = cov->c ();
               const T& v0 = cov->v ();
               const T& v1 = vov->v0();
               const T& v2 = vov->v1();
               const details::operator_type o0 = cov->operation();
               const details::operator_type o1 = operation;
               const details::operator_type o2 = vov->operation();

               details::free_node(*(expr_gen.node_allocator()),branch[0]);
               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               if (expr_gen.parser()->settings().strength_reduction_enabled())
               {
                  // (c / v0) * (v1 / v2) --> (covovov) (c * v1) / (v0 * v2)
                  if ((details::e_div == o0) && (details::e_mul == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf4ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "(t*t)/(t*t)", c, v1, v0, v2, result);

                     exprtk_debug(("(c / v0) * (v1 / v2) --> (covovov) (c * v1) / (v0 * v2)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (c / v0) / (v1 / v2) --> (covovov) (c * v2) / (v0 * v1)
                  if ((details::e_div == o0) && (details::e_div == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf4ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "(t*t)/(t*t)", c, v2, v0, v1, result);

                     exprtk_debug(("(c / v0) / (v1 / v2) --> (covovov) (c * v2) / (v0 * v1)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
               }

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), c, v0, v1, v2, result);

               if (synthesis_result)
                  return result;

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f2 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return expression_generator<T>::error_node();
               else if (!expr_gen.valid_operator(o2,f2))
                  return expression_generator<T>::error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator()), c, v0, v1, v2, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_covocov_expression0
         {
            typedef typename expression_generator<T>::covocov_t::type0 node_type;
            typedef typename expression_generator<T>::covocov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // (c0 o0 v0) o1 (c1 o2 v1)
               const details::cov_base_node<T>* cov0 = static_cast<details::cov_base_node<T>*>(branch[0]);
               const details::cov_base_node<T>* cov1 = static_cast<details::cov_base_node<T>*>(branch[1]);
               const T  c0 = cov0->c();
               const T& v0 = cov0->v();
               const T  c1 = cov1->c();
               const T& v1 = cov1->v();
               const details::operator_type o0 = cov0->operation();
               const details::operator_type o1 = operation;
               const details::operator_type o2 = cov1->operation();

               details::free_node(*(expr_gen.node_allocator()),branch[0]);
               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               if (expr_gen.parser()->settings().strength_reduction_enabled())
               {
                  // (c0 + v0) + (c1 + v1) --> (covov) (c0 + c1) + v0 + v1
                  if ((details::e_add == o0) && (details::e_add == o1) && (details::e_add == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "(t+t)+t", (c0 + c1), v0, v1, result);

                     exprtk_debug(("(c0 + v0) + (c1 + v1) --> (covov) (c0 + c1) + v0 + v1\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (c0 + v0) - (c1 + v1) --> (covov) (c0 - c1) + v0 - v1
                  else if ((details::e_add == o0) && (details::e_sub == o1) && (details::e_add == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "(t+t)-t", (c0 - c1), v0, v1, result);

                     exprtk_debug(("(c0 + v0) - (c1 + v1) --> (covov) (c0 - c1) + v0 - v1\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (c0 - v0) - (c1 - v1) --> (covov) (c0 - c1) - v0 + v1
                  else if ((details::e_sub == o0) && (details::e_sub == o1) && (details::e_sub == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "(t-t)+t", (c0 - c1), v0, v1, result);

                     exprtk_debug(("(c0 - v0) - (c1 - v1) --> (covov) (c0 - c1) - v0 + v1\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (c0 * v0) * (c1 * v1) --> (covov) (c0 * c1) * v0 * v1
                  else if ((details::e_mul == o0) && (details::e_mul == o1) && (details::e_mul == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "(t*t)*t", (c0 * c1), v0, v1, result);

                     exprtk_debug(("(c0 * v0) * (c1 * v1) --> (covov) (c0 * c1) * v0 * v1\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (c0 * v0) / (c1 * v1) --> (covov) (c0 / c1) * (v0 / v1)
                  else if ((details::e_mul == o0) && (details::e_div == o1) && (details::e_mul == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "(t*t)/t", (c0 / c1), v0, v1, result);

                     exprtk_debug(("(c0 * v0) / (c1 * v1) --> (covov) (c0 / c1) * (v0 / v1)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (c0 / v0) * (c1 / v1) --> (covov) (c0 * c1) / (v0 * v1)
                  else if ((details::e_div == o0) && (details::e_mul == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "t/(t*t)", (c0 * c1), v0, v1, result);

                     exprtk_debug(("(c0 / v0) * (c1 / v1) --> (covov) (c0 * c1) / (v0 * v1)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (c0 / v0) / (c1 / v1) --> (covov) ((c0 / c1) * v1) / v0
                  else if ((details::e_div == o0) && (details::e_div == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "(t*t)/t", (c0 / c1), v1, v0, result);

                     exprtk_debug(("(c0 / v0) / (c1 / v1) --> (covov) ((c0 / c1) * v1) / v0\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (c0 * v0) / (c1 / v1) --> (covov) (c0 / c1) * (v0 * v1)
                  else if ((details::e_mul == o0) && (details::e_div == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "t*(t*t)", (c0 / c1), v0, v1, result);

                     exprtk_debug(("(c0 * v0) / (c1 / v1) --> (covov) (c0 / c1) * (v0 * v1)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (c0 / v0) / (c1 * v1) --> (covov) (c0 / c1) / (v0 * v1)
                  else if ((details::e_div == o0) && (details::e_div == o1) && (details::e_mul == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "t/(t*t)", (c0 / c1), v0, v1, result);

                     exprtk_debug(("(c0 / v0) / (c1 * v1) --> (covov) (c0 / c1) / (v0 * v1)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
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
                        default             : return expression_generator<T>::error_node();
                     }

                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, specfunc, c0, v0, v1, result);

                     exprtk_debug(("(c * v0) +/- (c * v1) --> (covov) c * (v0 +/- v1)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
               }

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), c0, v0, c1, v1, result);

               if (synthesis_result)
                  return result;

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f2 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return expression_generator<T>::error_node();
               else if (!expr_gen.valid_operator(o2,f2))
                  return expression_generator<T>::error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator()), c0, v0, c1, v1, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_vocovoc_expression0
         {
            typedef typename expression_generator<T>::vocovoc_t::type0 node_type;
            typedef typename expression_generator<T>::vocovoc_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // (v0 o0 c0) o1 (v1 o2 c1)
               const details::voc_base_node<T>* voc0 = static_cast<details::voc_base_node<T>*>(branch[0]);
               const details::voc_base_node<T>* voc1 = static_cast<details::voc_base_node<T>*>(branch[1]);
               const T  c0 = voc0->c();
               const T& v0 = voc0->v();
               const T  c1 = voc1->c();
               const T& v1 = voc1->v();
               const details::operator_type o0 = voc0->operation();
               const details::operator_type o1 = operation;
               const details::operator_type o2 = voc1->operation();

               details::free_node(*(expr_gen.node_allocator()),branch[0]);
               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               if (expr_gen.parser()->settings().strength_reduction_enabled())
               {
                  // (v0 + c0) + (v1 + c1) --> (covov) (c0 + c1) + v0 + v1
                  if ((details::e_add == o0) && (details::e_add == o1) && (details::e_add == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "(t+t)+t", (c0 + c1), v0, v1, result);

                     exprtk_debug(("(v0 + c0) + (v1 + c1) --> (covov) (c0 + c1) + v0 + v1\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (v0 + c0) - (v1 + c1) --> (covov) (c0 - c1) + v0 - v1
                  else if ((details::e_add == o0) && (details::e_sub == o1) && (details::e_add == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "(t+t)-t", (c0 - c1), v0, v1, result);

                     exprtk_debug(("(v0 + c0) - (v1 + c1) --> (covov) (c0 - c1) + v0 - v1\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (v0 - c0) - (v1 - c1) --> (covov) (c1 - c0) + v0 - v1
                  else if ((details::e_sub == o0) && (details::e_sub == o1) && (details::e_sub == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "(t+t)-t", (c1 - c0), v0, v1, result);

                     exprtk_debug(("(v0 - c0) - (v1 - c1) --> (covov) (c1 - c0) + v0 - v1\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (v0 * c0) * (v1 * c1) --> (covov) (c0 * c1) * v0 * v1
                  else if ((details::e_mul == o0) && (details::e_mul == o1) && (details::e_mul == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "(t*t)*t", (c0 * c1), v0, v1, result);

                     exprtk_debug(("(v0 * c0) * (v1 * c1) --> (covov) (c0 * c1) * v0 * v1\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (v0 * c0) / (v1 * c1) --> (covov) (c0 / c1) * (v0 / v1)
                  else if ((details::e_mul == o0) && (details::e_div == o1) && (details::e_mul == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "(t*t)/t", (c0 / c1), v0, v1, result);

                     exprtk_debug(("(v0 * c0) / (v1 * c1) --> (covov) (c0 / c1) * (v0 / v1)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (v0 / c0) * (v1 / c1) --> (covov) (1 / (c0 * c1)) * v0 * v1
                  else if ((details::e_div == o0) && (details::e_mul == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "(t*t)*t", T(1) / (c0 * c1), v0, v1, result);

                     exprtk_debug(("(v0 / c0) * (v1 / c1) --> (covov) (1 / (c0 * c1)) * v0 * v1\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (v0 / c0) / (v1 / c1) --> (covov) ((c1 / c0) * v0) / v1
                  else if ((details::e_div == o0) && (details::e_div == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "(t*t)/t", (c1 / c0), v0, v1, result);

                     exprtk_debug(("(v0 / c0) / (v1 / c1) --> (covov) ((c1 / c0) * v0) / v1\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (v0 * c0) / (v1 / c1) --> (covov) (c0 * c1) * (v0 / v1)
                  else if ((details::e_mul == o0) && (details::e_div == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "t*(t/t)", (c0 * c1), v0, v1, result);

                     exprtk_debug(("(v0 * c0) / (v1 / c1) --> (covov) (c0 * c1) * (v0 / v1)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (v0 / c0) / (v1 * c1) --> (covov) (1 / (c0 * c1)) * v0 / v1
                  else if ((details::e_div == o0) && (details::e_div == o1) && (details::e_mul == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "t*(t/t)", T(1) / (c0 * c1), v0, v1, result);

                     exprtk_debug(("(v0 / c0) / (v1 * c1) --> (covov) (1 / (c0 * c1)) * v0 / v1\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (v0 / c0) * (v1 + c1) --> (vocovoc) (v0 * (1 / c0)) * (v1 + c1)
                  else if ((details::e_div == o0) && (details::e_mul == o1) && (details::e_add == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf4ext_expression<T>::
                           template compile<typename expression_generator<T>::vtype, typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::ctype>(expr_gen, "(t*t)*(t+t)", v0, T(1) / c0, v1, c1, result);

                     exprtk_debug(("(v0 / c0) * (v1 + c1) --> (vocovoc) (v0 * (1 / c0)) * (v1 + c1)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (v0 / c0) * (v1 - c1) --> (vocovoc) (v0 * (1 / c0)) * (v1 - c1)
                  else if ((details::e_div == o0) && (details::e_mul == o1) && (details::e_sub == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf4ext_expression<T>::
                           template compile<typename expression_generator<T>::vtype, typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::ctype>(expr_gen, "(t*t)*(t-t)", v0, T(1) / c0, v1, c1, result);

                     exprtk_debug(("(v0 / c0) * (v1 - c1) --> (vocovoc) (v0 * (1 / c0)) * (v1 - c1)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
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
                        default             : return expression_generator<T>::error_node();
                     }

                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, specfunc, c0, v0, v1, result);

                     exprtk_debug(("(v0 * c) +/- (v1 * c) --> (covov) c * (v0 +/- v1)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
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
                        default             : return expression_generator<T>::error_node();
                     }

                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::vtype, typename expression_generator<T>::vtype, typename expression_generator<T>::ctype>(expr_gen, specfunc, v0, v1, c0, result);

                     exprtk_debug(("(v0 / c) +/- (v1 / c) --> (vovoc) (v0 +/- v1) / c\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
               }

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, c0, v1, c1, result);

               if (synthesis_result)
                  return result;

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f2 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return expression_generator<T>::error_node();
               else if (!expr_gen.valid_operator(o2,f2))
                  return expression_generator<T>::error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator()), v0, c0, v1, c1, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_covovoc_expression0
         {
            typedef typename expression_generator<T>::covovoc_t::type0 node_type;
            typedef typename expression_generator<T>::covovoc_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // (c0 o0 v0) o1 (v1 o2 c1)
               const details::cov_base_node<T>* cov = static_cast<details::cov_base_node<T>*>(branch[0]);
               const details::voc_base_node<T>* voc = static_cast<details::voc_base_node<T>*>(branch[1]);
               const T  c0 = cov->c();
               const T& v0 = cov->v();
               const T  c1 = voc->c();
               const T& v1 = voc->v();
               const details::operator_type o0 = cov->operation();
               const details::operator_type o1 = operation;
               const details::operator_type o2 = voc->operation();

               details::free_node(*(expr_gen.node_allocator()),branch[0]);
               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               if (expr_gen.parser()->settings().strength_reduction_enabled())
               {
                  // (c0 + v0) + (v1 + c1) --> (covov) (c0 + c1) + v0 + v1
                  if ((details::e_add == o0) && (details::e_add == o1) && (details::e_add == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "(t+t)+t", (c0 + c1), v0, v1, result);

                     exprtk_debug(("(c0 + v0) + (v1 + c1) --> (covov) (c0 + c1) + v0 + v1\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (c0 + v0) - (v1 + c1) --> (covov) (c0 - c1) + v0 - v1
                  else if ((details::e_add == o0) && (details::e_sub == o1) && (details::e_add == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "(t+t)-t", (c0 - c1), v0, v1, result);

                     exprtk_debug(("(c0 + v0) - (v1 + c1) --> (covov) (c0 - c1) + v0 - v1\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (c0 - v0) - (v1 - c1) --> (covov) (c0 + c1) - v0 - v1
                  else if ((details::e_sub == o0) && (details::e_sub == o1) && (details::e_sub == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "t-(t+t)", (c0 + c1), v0, v1, result);

                     exprtk_debug(("(c0 - v0) - (v1 - c1) --> (covov) (c0 + c1) - v0 - v1\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (c0 * v0) * (v1 * c1) --> (covov) (c0 * c1) * v0 * v1
                  else if ((details::e_mul == o0) && (details::e_mul == o1) && (details::e_mul == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "(t*t)*t", (c0 * c1), v0, v1, result);

                     exprtk_debug(("(c0 * v0) * (v1 * c1) --> (covov) (c0 * c1) * v0 * v1\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (c0 * v0) / (v1 * c1) --> (covov) (c0 / c1) * (v0 / v1)
                  else if ((details::e_mul == o0) && (details::e_div == o1) && (details::e_mul == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "(t*t)/t", (c0 / c1), v0, v1, result);

                     exprtk_debug(("(c0 * v0) / (v1 * c1) --> (covov) (c0 / c1) * (v0 / v1)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (c0 / v0) * (v1 / c1) --> (covov) (c0 / c1) * (v1 / v0)
                  else if ((details::e_div == o0) && (details::e_mul == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "t*(t/t)", (c0 / c1), v1, v0, result);

                     exprtk_debug(("(c0 / v0) * (v1 / c1) --> (covov) (c0 / c1) * (v1 / v0)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (c0 / v0) / (v1 / c1) --> (covov) (c0 * c1) / (v0 * v1)
                  else if ((details::e_div == o0) && (details::e_div == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "t/(t*t)", (c0 * c1), v0, v1, result);

                     exprtk_debug(("(c0 / v0) / (v1 / c1) --> (covov) (c0 * c1) / (v0 * v1)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (c0 * v0) / (v1 / c1) --> (covov) (c0 * c1) * (v0 / v1)
                  else if ((details::e_mul == o0) && (details::e_div == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "(t*t)/t", (c0 * c1), v0, v1, result);

                     exprtk_debug(("(c0 * v0) / (v1 / c1) --> (covov) (c0 * c1) * (v0 / v1)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (c0 / v0) / (v1 * c1) --> (covov) (c0 / c1) / (v0 * v1)
                  else if ((details::e_div == o0) && (details::e_div == o1) && (details::e_mul == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "t/(t*t)", (c0 / c1), v0, v1, result);

                     exprtk_debug(("(c0 / v0) / (v1 * c1) --> (covov) (c0 / c1) / (v0 * v1)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
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
                        default             : return expression_generator<T>::error_node();
                     }

                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, specfunc, c0, v0, v1, result);

                     exprtk_debug(("(c * v0) +/- (v1 * c) --> (covov) c * (v0 +/- v1)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
               }

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), c0, v0, v1, c1, result);

               if (synthesis_result)
                  return result;

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f2 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return expression_generator<T>::error_node();
               else if (!expr_gen.valid_operator(o2,f2))
                  return expression_generator<T>::error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator()), c0, v0, v1, c1, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_vococov_expression0
         {
            typedef typename expression_generator<T>::vococov_t::type0 node_type;
            typedef typename expression_generator<T>::vococov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // (v0 o0 c0) o1 (c1 o2 v1)
               const details::voc_base_node<T>* voc = static_cast<details::voc_base_node<T>*>(branch[0]);
               const details::cov_base_node<T>* cov = static_cast<details::cov_base_node<T>*>(branch[1]);
               const T  c0 = voc->c();
               const T& v0 = voc->v();
               const T  c1 = cov->c();
               const T& v1 = cov->v();
               const details::operator_type o0 = voc->operation();
               const details::operator_type o1 = operation;
               const details::operator_type o2 = cov->operation();

               details::free_node(*(expr_gen.node_allocator()),branch[0]);
               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               if (expr_gen.parser()->settings().strength_reduction_enabled())
               {
                  // (v0 + c0) + (c1 + v1) --> (covov) (c0 + c1) + v0 + v1
                  if ((details::e_add == o0) && (details::e_add == o1) && (details::e_add == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "(t+t)+t", (c0 + c1), v0, v1, result);

                     exprtk_debug(("(v0 + c0) + (c1 + v1) --> (covov) (c0 + c1) + v0 + v1\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (v0 + c0) - (c1 + v1) --> (covov) (c0 - c1) + v0 - v1
                  else if ((details::e_add == o0) && (details::e_sub == o1) && (details::e_add == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "(t+t)-t", (c0 - c1), v0, v1, result);

                     exprtk_debug(("(v0 + c0) - (c1 + v1) --> (covov) (c0 - c1) + v0 - v1\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (v0 - c0) - (c1 - v1) --> (vovoc) v0 + v1 - (c1 + c0)
                  else if ((details::e_sub == o0) && (details::e_sub == o1) && (details::e_sub == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::vtype, typename expression_generator<T>::vtype, typename expression_generator<T>::ctype>(expr_gen, "(t+t)-t", v0, v1, (c1 + c0), result);

                     exprtk_debug(("(v0 - c0) - (c1 - v1) --> (vovoc) v0 + v1 - (c1 + c0)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (v0 * c0) * (c1 * v1) --> (covov) (c0 * c1) * v0 * v1
                  else if ((details::e_mul == o0) && (details::e_mul == o1) && (details::e_mul == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "(t*t)*t", (c0 * c1), v0, v1, result);

                     exprtk_debug(("(v0 * c0) * (c1 * v1) --> (covov) (c0 * c1) * v0 * v1\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (v0 * c0) / (c1 * v1) --> (covov) (c0 / c1) * (v0 * v1)
                  else if ((details::e_mul == o0) && (details::e_div == o1) && (details::e_mul == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "(t*t)/t", (c0 / c1), v0, v1, result);

                     exprtk_debug(("(v0 * c0) / (c1 * v1) --> (covov) (c0 / c1) * (v0 * v1)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (v0 / c0) * (c1 / v1) --> (covov) (c1 / c0) * (v0 / v1)
                  else if ((details::e_div == o0) && (details::e_mul == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "(t*t)/t", (c1 / c0), v0, v1, result);

                     exprtk_debug(("(v0 / c0) * (c1 / v1) --> (covov) (c1 / c0) * (v0 / v1)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (v0 * c0) / (c1 / v1) --> (covov) (c0 / c1) * (v0 * v1)
                  else if ((details::e_mul == o0) && (details::e_div == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "(t*t)*t", (c0 / c1), v0, v1, result);

                     exprtk_debug(("(v0 * c0) / (c1 / v1) --> (covov) (c0 / c1) * (v0 * v1)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (v0 / c0) / (c1 * v1) --> (covov) (1 / (c0 * c1)) * (v0 / v1)
                  else if ((details::e_div == o0) && (details::e_div == o1) && (details::e_mul == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, "(t*t)/t", T(1) / (c0 * c1), v0, v1, result);

                     exprtk_debug(("(v0 / c0) / (c1 * v1) --> (covov) (1 / (c0 * c1)) * (v0 / v1)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
                  // (v0 / c0) / (c1 / v1) --> (vovoc) (v0 * v1) * (1 / (c0 * c1))
                  else if ((details::e_div == o0) && (details::e_div == o1) && (details::e_div == o2))
                  {
                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::vtype, typename expression_generator<T>::vtype, typename expression_generator<T>::ctype>(expr_gen, "(t*t)*t", v0, v1, T(1) / (c0 * c1), result);

                     exprtk_debug(("(v0 / c0) / (c1 / v1) --> (vovoc) (v0 * v1) * (1 / (c0 * c1))\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
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
                        default             : return expression_generator<T>::error_node();
                     }

                     const bool synthesis_result =
                        synthesize_sf3ext_expression<T>::
                           template compile<typename expression_generator<T>::ctype, typename expression_generator<T>::vtype, typename expression_generator<T>::vtype>(expr_gen, specfunc, c0, v0, v1, result);

                     exprtk_debug(("(v0 * c) +/- (c * v1) --> (covov) c * (v0 +/- v1)\n"));

                     return (synthesis_result) ? result : expression_generator<T>::error_node();
                  }
               }

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, c0, c1, v1, result);

               if (synthesis_result)
                  return result;

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f2 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();
               else if (!expr_gen.valid_operator(o1,f1))
                  return expression_generator<T>::error_node();
               else if (!expr_gen.valid_operator(o2,f2))
                  return expression_generator<T>::error_node();
               else
                  return node_type::allocate(*(expr_gen.node_allocator()), v0, c0, c1, v1, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_vovovov_expression1
         {
            typedef typename expression_generator<T>::vovovov_t::type1 node_type;
            typedef typename expression_generator<T>::vovovov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // v0 o0 (v1 o1 (v2 o2 v3))
               typedef typename synthesize_vovov_expression1<T>::node_type lcl_vovov_t;

               const lcl_vovov_t* vovov = static_cast<const lcl_vovov_t*>(branch[1]);
               const T& v0 = static_cast<details::variable_node<T>*>(branch[0])->ref();
               const T& v1 = vovov->t0();
               const T& v2 = vovov->t1();
               const T& v3 = vovov->t2();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = expr_gen.get_operator(vovov->f0());
               const details::operator_type o2 = expr_gen.get_operator(vovov->f1());

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = vovov->f0();
               typename expression_generator<T>::binary_functor_t f2 = vovov->f1();

               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen,id(expr_gen, o0, o1, o2), v0, v1, v2, v3, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();

               exprtk_debug(("v0 o0 (v1 o1 (v2 o2 v3))\n"));

               return node_type::allocate(*(expr_gen.node_allocator()), v0, v1, v2, v3, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_vovovoc_expression1
         {
            typedef typename expression_generator<T>::vovovoc_t::type1 node_type;
            typedef typename expression_generator<T>::vovovoc_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // v0 o0 (v1 o1 (v2 o2 c))
               typedef typename synthesize_vovoc_expression1<T>::node_type lcl_vovoc_t;

               const lcl_vovoc_t* vovoc = static_cast<const lcl_vovoc_t*>(branch[1]);
               const T& v0 = static_cast<details::variable_node<T>*>(branch[0])->ref();
               const T& v1 = vovoc->t0();
               const T& v2 = vovoc->t1();
               const T   c = vovoc->t2();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = expr_gen.get_operator(vovoc->f0());
               const details::operator_type o2 = expr_gen.get_operator(vovoc->f1());

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = vovoc->f0();
               typename expression_generator<T>::binary_functor_t f2 = vovoc->f1();

               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, v1, v2, c, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();

               exprtk_debug(("v0 o0 (v1 o1 (v2 o2 c))\n"));

               return node_type::allocate(*(expr_gen.node_allocator()), v0, v1, v2, c, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_vovocov_expression1
         {
            typedef typename expression_generator<T>::vovocov_t::type1 node_type;
            typedef typename expression_generator<T>::vovocov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // v0 o0 (v1 o1 (c o2 v2))
               typedef typename synthesize_vocov_expression1<T>::node_type lcl_vocov_t;

               const lcl_vocov_t* vocov = static_cast<const lcl_vocov_t*>(branch[1]);
               const T& v0 = static_cast<details::variable_node<T>*>(branch[0])->ref();
               const T& v1 = vocov->t0();
               const T   c = vocov->t1();
               const T& v2 = vocov->t2();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = expr_gen.get_operator(vocov->f0());
               const details::operator_type o2 = expr_gen.get_operator(vocov->f1());

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = vocov->f0();
               typename expression_generator<T>::binary_functor_t f2 = vocov->f1();

               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, v1, c, v2, result);

               if (synthesis_result)
                  return result;
               if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();

               exprtk_debug(("v0 o0 (v1 o1 (c o2 v2))\n"));

               return node_type::allocate(*(expr_gen.node_allocator()), v0, v1, c, v2, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_vocovov_expression1
         {
            typedef typename expression_generator<T>::vocovov_t::type1 node_type;
            typedef typename expression_generator<T>::vocovov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // v0 o0 (c o1 (v1 o2 v2))
               typedef typename synthesize_covov_expression1<T>::node_type lcl_covov_t;

               const lcl_covov_t* covov = static_cast<const lcl_covov_t*>(branch[1]);
               const T& v0 = static_cast<details::variable_node<T>*>(branch[0])->ref();
               const T   c = covov->t0();
               const T& v1 = covov->t1();
               const T& v2 = covov->t2();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = expr_gen.get_operator(covov->f0());
               const details::operator_type o2 = expr_gen.get_operator(covov->f1());

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = covov->f0();
               typename expression_generator<T>::binary_functor_t f2 = covov->f1();

               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, c, v1, v2, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();

               exprtk_debug(("v0 o0 (c o1 (v1 o2 v2))\n"));

               return node_type::allocate(*(expr_gen.node_allocator()), v0, c, v1, v2, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_covovov_expression1
         {
            typedef typename expression_generator<T>::covovov_t::type1 node_type;
            typedef typename expression_generator<T>::covovov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // c o0 (v0 o1 (v1 o2 v2))
               typedef typename synthesize_vovov_expression1<T>::node_type lcl_vovov_t;

               const lcl_vovov_t* vovov = static_cast<const lcl_vovov_t*>(branch[1]);
               const T   c = static_cast<details::literal_node<T>*>(branch[0])->value();
               const T& v0 = vovov->t0();
               const T& v1 = vovov->t1();
               const T& v2 = vovov->t2();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = expr_gen.get_operator(vovov->f0());
               const details::operator_type o2 = expr_gen.get_operator(vovov->f1());

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = vovov->f0();
               typename expression_generator<T>::binary_functor_t f2 = vovov->f1();

               details::free_node(*(expr_gen.node_allocator()),branch[0]);
               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), c, v0, v1, v2, result);

               if (synthesis_result)
                  return result;
               if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();

               exprtk_debug(("c o0 (v0 o1 (v1 o2 v2))\n"));

               return node_type::allocate(*(expr_gen.node_allocator()), c, v0, v1, v2, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_covocov_expression1
         {
            typedef typename expression_generator<T>::covocov_t::type1 node_type;
            typedef typename expression_generator<T>::covocov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // c0 o0 (v0 o1 (c1 o2 v1))
               typedef typename synthesize_vocov_expression1<T>::node_type lcl_vocov_t;

               const lcl_vocov_t* vocov = static_cast<const lcl_vocov_t*>(branch[1]);
               const T  c0 = static_cast<details::literal_node<T>*>(branch[0])->value();
               const T& v0 = vocov->t0();
               const T  c1 = vocov->t1();
               const T& v1 = vocov->t2();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = expr_gen.get_operator(vocov->f0());
               const details::operator_type o2 = expr_gen.get_operator(vocov->f1());

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = vocov->f0();
               typename expression_generator<T>::binary_functor_t f2 = vocov->f1();

               details::free_node(*(expr_gen.node_allocator()),branch[0]);
               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), c0, v0, c1, v1, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();

               exprtk_debug(("c0 o0 (v0 o1 (c1 o2 v1))\n"));

               return node_type::allocate(*(expr_gen.node_allocator()), c0, v0, c1, v1, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_vocovoc_expression1
         {
            typedef typename expression_generator<T>::vocovoc_t::type1 node_type;
            typedef typename expression_generator<T>::vocovoc_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // v0 o0 (c0 o1 (v1 o2 c2))
               typedef typename synthesize_covoc_expression1<T>::node_type lcl_covoc_t;

               const lcl_covoc_t* covoc = static_cast<const lcl_covoc_t*>(branch[1]);
               const T& v0 = static_cast<details::variable_node<T>*>(branch[0])->ref();
               const T  c0 = covoc->t0();
               const T& v1 = covoc->t1();
               const T  c1 = covoc->t2();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = expr_gen.get_operator(covoc->f0());
               const details::operator_type o2 = expr_gen.get_operator(covoc->f1());

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = covoc->f0();
               typename expression_generator<T>::binary_functor_t f2 = covoc->f1();

               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, c0, v1, c1, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();

               exprtk_debug(("v0 o0 (c0 o1 (v1 o2 c2))\n"));

               return node_type::allocate(*(expr_gen.node_allocator()), v0, c0, v1, c1, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_covovoc_expression1
         {
            typedef typename expression_generator<T>::covovoc_t::type1 node_type;
            typedef typename expression_generator<T>::covovoc_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;
            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // c0 o0 (v0 o1 (v1 o2 c1))
               typedef typename synthesize_vovoc_expression1<T>::node_type lcl_vovoc_t;

               const lcl_vovoc_t* vovoc = static_cast<const lcl_vovoc_t*>(branch[1]);
               const T  c0 = static_cast<details::literal_node<T>*>(branch[0])->value();
               const T& v0 = vovoc->t0();
               const T& v1 = vovoc->t1();
               const T  c1 = vovoc->t2();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = expr_gen.get_operator(vovoc->f0());
               const details::operator_type o2 = expr_gen.get_operator(vovoc->f1());

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = vovoc->f0();
               typename expression_generator<T>::binary_functor_t f2 = vovoc->f1();

               details::free_node(*(expr_gen.node_allocator()),branch[0]);
               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), c0, v0, v1, c1, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();

               exprtk_debug(("c0 o0 (v0 o1 (v1 o2 c1))\n"));

               return node_type::allocate(*(expr_gen.node_allocator()), c0, v0, v1, c1, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_vococov_expression1
         {
            typedef typename expression_generator<T>::vococov_t::type1 node_type;
            typedef typename expression_generator<T>::vococov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // v0 o0 (c0 o1 (c1 o2 v1))
               typedef typename synthesize_cocov_expression1<T>::node_type lcl_cocov_t;

               const lcl_cocov_t* cocov = static_cast<const lcl_cocov_t*>(branch[1]);
               const T& v0 = static_cast<details::variable_node<T>*>(branch[0])->ref();
               const T  c0 = cocov->t0();
               const T  c1 = cocov->t1();
               const T& v1 = cocov->t2();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = expr_gen.get_operator(cocov->f0());
               const details::operator_type o2 = expr_gen.get_operator(cocov->f1());

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = cocov->f0();
               typename expression_generator<T>::binary_functor_t f2 = cocov->f1();

               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, c0, c1, v1, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();

               exprtk_debug(("v0 o0 (c0 o1 (c1 o2 v1))\n"));

               return node_type::allocate(*(expr_gen.node_allocator()), v0, c0, c1, v1, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_vovovov_expression2
         {
            typedef typename expression_generator<T>::vovovov_t::type2 node_type;
            typedef typename expression_generator<T>::vovovov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // v0 o0 ((v1 o1 v2) o2 v3)
               typedef typename synthesize_vovov_expression0<T>::node_type lcl_vovov_t;

               const lcl_vovov_t* vovov = static_cast<const lcl_vovov_t*>(branch[1]);
               const T& v0 = static_cast<details::variable_node<T>*>(branch[0])->ref();
               const T& v1 = vovov->t0();
               const T& v2 = vovov->t1();
               const T& v3 = vovov->t2();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = expr_gen.get_operator(vovov->f0());
               const details::operator_type o2 = expr_gen.get_operator(vovov->f1());

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = vovov->f0();
               typename expression_generator<T>::binary_functor_t f2 = vovov->f1();

               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, v1, v2, v3, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();

               exprtk_debug(("v0 o0 ((v1 o1 v2) o2 v3)\n"));

               return node_type::allocate(*(expr_gen.node_allocator()), v0, v1, v2, v3, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_vovovoc_expression2
         {
            typedef typename expression_generator<T>::vovovoc_t::type2 node_type;
            typedef typename expression_generator<T>::vovovoc_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // v0 o0 ((v1 o1 v2) o2 c)
               typedef typename synthesize_vovoc_expression0<T>::node_type lcl_vovoc_t;

               const lcl_vovoc_t* vovoc = static_cast<const lcl_vovoc_t*>(branch[1]);
               const T& v0 = static_cast<details::variable_node<T>*>(branch[0])->ref();
               const T& v1 = vovoc->t0();
               const T& v2 = vovoc->t1();
               const T   c = vovoc->t2();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = expr_gen.get_operator(vovoc->f0());
               const details::operator_type o2 = expr_gen.get_operator(vovoc->f1());

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = vovoc->f0();
               typename expression_generator<T>::binary_functor_t f2 = vovoc->f1();

               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, v1, v2, c, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();

               exprtk_debug(("v0 o0 ((v1 o1 v2) o2 c)\n"));

               return node_type::allocate(*(expr_gen.node_allocator()), v0, v1, v2, c, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_vovocov_expression2
         {
            typedef typename expression_generator<T>::vovocov_t::type2 node_type;
            typedef typename expression_generator<T>::vovocov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // v0 o0 ((v1 o1 c) o2 v2)
               typedef typename synthesize_vocov_expression0<T>::node_type lcl_vocov_t;

               const lcl_vocov_t* vocov = static_cast<const lcl_vocov_t*>(branch[1]);
               const T& v0 = static_cast<details::variable_node<T>*>(branch[0])->ref();
               const T& v1 = vocov->t0();
               const T   c = vocov->t1();
               const T& v2 = vocov->t2();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = expr_gen.get_operator(vocov->f0());
               const details::operator_type o2 = expr_gen.get_operator(vocov->f1());

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = vocov->f0();
               typename expression_generator<T>::binary_functor_t f2 = vocov->f1();

               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, v1, c, v2, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();

               exprtk_debug(("v0 o0 ((v1 o1 c) o2 v2)\n"));

               return node_type::allocate(*(expr_gen.node_allocator()), v0, v1, c, v2, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_vocovov_expression2
         {
            typedef typename expression_generator<T>::vocovov_t::type2 node_type;
            typedef typename expression_generator<T>::vocovov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // v0 o0 ((c o1 v1) o2 v2)
               typedef typename synthesize_covov_expression0<T>::node_type lcl_covov_t;

               const lcl_covov_t* covov = static_cast<const lcl_covov_t*>(branch[1]);
               const T& v0 = static_cast<details::variable_node<T>*>(branch[0])->ref();
               const T   c = covov->t0();
               const T& v1 = covov->t1();
               const T& v2 = covov->t2();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = expr_gen.get_operator(covov->f0());
               const details::operator_type o2 = expr_gen.get_operator(covov->f1());

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = covov->f0();
               typename expression_generator<T>::binary_functor_t f2 = covov->f1();

               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, c, v1, v2, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();

               exprtk_debug(("v0 o0 ((c o1 v1) o2 v2)\n"));

               return node_type::allocate(*(expr_gen.node_allocator()), v0, c, v1, v2, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_covovov_expression2
         {
            typedef typename expression_generator<T>::covovov_t::type2 node_type;
            typedef typename expression_generator<T>::covovov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // c o0 ((v1 o1 v2) o2 v3)
               typedef typename synthesize_vovov_expression0<T>::node_type lcl_vovov_t;

               const lcl_vovov_t* vovov = static_cast<const lcl_vovov_t*>(branch[1]);
               const T   c = static_cast<details::literal_node<T>*>(branch[0])->value();
               const T& v0 = vovov->t0();
               const T& v1 = vovov->t1();
               const T& v2 = vovov->t2();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = expr_gen.get_operator(vovov->f0());
               const details::operator_type o2 = expr_gen.get_operator(vovov->f1());

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = vovov->f0();
               typename expression_generator<T>::binary_functor_t f2 = vovov->f1();

               details::free_node(*(expr_gen.node_allocator()),branch[0]);
               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), c, v0, v1, v2, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();

               exprtk_debug(("c o0 ((v1 o1 v2) o2 v3)\n"));

               return node_type::allocate(*(expr_gen.node_allocator()), c, v0, v1, v2, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_covocov_expression2
         {
            typedef typename expression_generator<T>::covocov_t::type2 node_type;
            typedef typename expression_generator<T>::covocov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // c0 o0 ((v0 o1 c1) o2 v1)
               typedef typename synthesize_vocov_expression0<T>::node_type lcl_vocov_t;

               const lcl_vocov_t* vocov = static_cast<const lcl_vocov_t*>(branch[1]);
               const T  c0 = static_cast<details::literal_node<T>*>(branch[0])->value();
               const T& v0 = vocov->t0();
               const T  c1 = vocov->t1();
               const T& v1 = vocov->t2();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = expr_gen.get_operator(vocov->f0());
               const details::operator_type o2 = expr_gen.get_operator(vocov->f1());

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = vocov->f0();
               typename expression_generator<T>::binary_functor_t f2 = vocov->f1();

               details::free_node(*(expr_gen.node_allocator()),branch[0]);
               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), c0, v0, c1, v1, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();

               exprtk_debug(("c0 o0 ((v0 o1 c1) o2 v1)\n"));

               return node_type::allocate(*(expr_gen.node_allocator()), c0, v0, c1, v1, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_vocovoc_expression2
         {
            typedef typename expression_generator<T>::vocovoc_t::type2 node_type;
            typedef typename expression_generator<T>::vocovoc_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // v0 o0 ((c0 o1 v1) o2 c1)
               typedef typename synthesize_covoc_expression0<T>::node_type lcl_covoc_t;

               const lcl_covoc_t* covoc = static_cast<const lcl_covoc_t*>(branch[1]);
               const T& v0 = static_cast<details::variable_node<T>*>(branch[0])->ref();
               const T  c0 = covoc->t0();
               const T& v1 = covoc->t1();
               const T  c1 = covoc->t2();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = expr_gen.get_operator(covoc->f0());
               const details::operator_type o2 = expr_gen.get_operator(covoc->f1());

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = covoc->f0();
               typename expression_generator<T>::binary_functor_t f2 = covoc->f1();

               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, c0, v1, c1, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();

               exprtk_debug(("v0 o0 ((c0 o1 v1) o2 c1)\n"));

               return node_type::allocate(*(expr_gen.node_allocator()), v0, c0, v1, c1, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_covovoc_expression2
         {
            typedef typename expression_generator<T>::covovoc_t::type2 node_type;
            typedef typename expression_generator<T>::covovoc_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // c0 o0 ((v0 o1 v1) o2 c1)
               typedef typename synthesize_vovoc_expression0<T>::node_type lcl_vovoc_t;

               const lcl_vovoc_t* vovoc = static_cast<const lcl_vovoc_t*>(branch[1]);
               const T  c0 = static_cast<details::literal_node<T>*>(branch[0])->value();
               const T& v0 = vovoc->t0();
               const T& v1 = vovoc->t1();
               const T  c1 = vovoc->t2();
               const details::operator_type o0 = operation;
               const details::operator_type o1 = expr_gen.get_operator(vovoc->f0());
               const details::operator_type o2 = expr_gen.get_operator(vovoc->f1());

               typename expression_generator<T>::binary_functor_t f0 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);
               typename expression_generator<T>::binary_functor_t f1 = vovoc->f0();
               typename expression_generator<T>::binary_functor_t f2 = vovoc->f1();

               details::free_node(*(expr_gen.node_allocator()),branch[0]);
               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), c0, v0, v1, c1, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o0,f0))
                  return expression_generator<T>::error_node();

               exprtk_debug(("c0 o0 ((v0 o1 v1) o2 c1)\n"));

               return node_type::allocate(*(expr_gen.node_allocator()), c0, v0, v1, c1, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_vococov_expression2
         {
            typedef typename expression_generator<T>::vococov_t::type2 node_type;
            static details::expression_node<T>* process(expression_generator<T>&,
                                                      const details::operator_type&,
                                                      details::expression_node<T>* (&)[2])
            {
               // v0 o0 ((c0 o1 c1) o2 v1) - Not possible
               exprtk_debug(("v0 o0 ((c0 o1 c1) o2 v1) - Not possible\n"));
               return expression_generator<T>::error_node();
            }

            static std::string id(expression_generator<T>&,
                                         const details::operator_type,
                                         const details::operator_type,
                                         const details::operator_type)
            {
               return "INVALID";
            }
         };

        template<typename T>
         struct synthesize_vovovov_expression3
         {
            typedef typename expression_generator<T>::vovovov_t::type3 node_type;
            typedef typename expression_generator<T>::vovovov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // ((v0 o0 v1) o1 v2) o2 v3
               typedef typename synthesize_vovov_expression0<T>::node_type lcl_vovov_t;

               const lcl_vovov_t* vovov = static_cast<const lcl_vovov_t*>(branch[0]);
               const T& v0 = vovov->t0();
               const T& v1 = vovov->t1();
               const T& v2 = vovov->t2();
               const T& v3 = static_cast<details::variable_node<T>*>(branch[1])->ref();
               const details::operator_type o0 = expr_gen.get_operator(vovov->f0());
               const details::operator_type o1 = expr_gen.get_operator(vovov->f1());
               const details::operator_type o2 = operation;

               typename expression_generator<T>::binary_functor_t f0 = vovov->f0();
               typename expression_generator<T>::binary_functor_t f1 = vovov->f1();
               typename expression_generator<T>::binary_functor_t f2 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               details::free_node(*(expr_gen.node_allocator()),branch[0]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, v1, v2, v3, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o2,f2))
                  return expression_generator<T>::error_node();

               exprtk_debug(("((v0 o0 v1) o1 v2) o2 v3\n"));

               return node_type::allocate(*(expr_gen.node_allocator()), v0, v1, v2, v3, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_vovovoc_expression3
         {
            typedef typename expression_generator<T>::vovovoc_t::type3 node_type;
            typedef typename expression_generator<T>::vovovoc_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // ((v0 o0 v1) o1 v2) o2 c
               typedef typename synthesize_vovov_expression0<T>::node_type lcl_vovov_t;

               const lcl_vovov_t* vovov = static_cast<const lcl_vovov_t*>(branch[0]);
               const T& v0 = vovov->t0();
               const T& v1 = vovov->t1();
               const T& v2 = vovov->t2();
               const T   c = static_cast<details::literal_node<T>*>(branch[1])->value();
               const details::operator_type o0 = expr_gen.get_operator(vovov->f0());
               const details::operator_type o1 = expr_gen.get_operator(vovov->f1());
               const details::operator_type o2 = operation;

               typename expression_generator<T>::binary_functor_t f0 = vovov->f0();
               typename expression_generator<T>::binary_functor_t f1 = vovov->f1();
               typename expression_generator<T>::binary_functor_t f2 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               details::free_node(*(expr_gen.node_allocator()),branch[0]);
               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, v1, v2, c, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o2,f2))
                  return expression_generator<T>::error_node();

               exprtk_debug(("((v0 o0 v1) o1 v2) o2 c\n"));

               return node_type::allocate(*(expr_gen.node_allocator()), v0, v1, v2, c, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_vovocov_expression3
         {
            typedef typename expression_generator<T>::vovocov_t::type3 node_type;
            typedef typename expression_generator<T>::vovocov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // ((v0 o0 v1) o1 c) o2 v2
               typedef typename synthesize_vovoc_expression0<T>::node_type lcl_vovoc_t;

               const lcl_vovoc_t* vovoc = static_cast<const lcl_vovoc_t*>(branch[0]);
               const T& v0 = vovoc->t0();
               const T& v1 = vovoc->t1();
               const T   c = vovoc->t2();
               const T& v2 = static_cast<details::variable_node<T>*>(branch[1])->ref();
               const details::operator_type o0 = expr_gen.get_operator(vovoc->f0());
               const details::operator_type o1 = expr_gen.get_operator(vovoc->f1());
               const details::operator_type o2 = operation;

               typename expression_generator<T>::binary_functor_t f0 = vovoc->f0();
               typename expression_generator<T>::binary_functor_t f1 = vovoc->f1();
               typename expression_generator<T>::binary_functor_t f2 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               details::free_node(*(expr_gen.node_allocator()),branch[0]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, v1, c, v2, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o2,f2))
                  return expression_generator<T>::error_node();

               exprtk_debug(("((v0 o0 v1) o1 c) o2 v2\n"));

               return node_type::allocate(*(expr_gen.node_allocator()), v0, v1, c, v2, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_vocovov_expression3
         {
            typedef typename expression_generator<T>::vocovov_t::type3 node_type;
            typedef typename expression_generator<T>::vocovov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // ((v0 o0 c) o1 v1) o2 v2
               typedef typename synthesize_vocov_expression0<T>::node_type lcl_vocov_t;

               const lcl_vocov_t* vocov = static_cast<const lcl_vocov_t*>(branch[0]);
               const T& v0 = vocov->t0();
               const T   c = vocov->t1();
               const T& v1 = vocov->t2();
               const T& v2 = static_cast<details::variable_node<T>*>(branch[1])->ref();
               const details::operator_type o0 = expr_gen.get_operator(vocov->f0());
               const details::operator_type o1 = expr_gen.get_operator(vocov->f1());
               const details::operator_type o2 = operation;

               typename expression_generator<T>::binary_functor_t f0 = vocov->f0();
               typename expression_generator<T>::binary_functor_t f1 = vocov->f1();
               typename expression_generator<T>::binary_functor_t f2 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               details::free_node(*(expr_gen.node_allocator()),branch[0]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, c, v1, v2, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o2,f2))
                  return expression_generator<T>::error_node();

               exprtk_debug(("((v0 o0 c) o1 v1) o2 v2\n"));

               return node_type::allocate(*(expr_gen.node_allocator()), v0, c, v1, v2, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_covovov_expression3
         {
            typedef typename expression_generator<T>::covovov_t::type3 node_type;
            typedef typename expression_generator<T>::covovov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // ((c o0 v0) o1 v1) o2 v2
               typedef typename synthesize_covov_expression0<T>::node_type lcl_covov_t;

               const lcl_covov_t* covov = static_cast<const lcl_covov_t*>(branch[0]);
               const T   c = covov->t0();
               const T& v0 = covov->t1();
               const T& v1 = covov->t2();
               const T& v2 = static_cast<details::variable_node<T>*>(branch[1])->ref();
               const details::operator_type o0 = expr_gen.get_operator(covov->f0());
               const details::operator_type o1 = expr_gen.get_operator(covov->f1());
               const details::operator_type o2 = operation;

               typename expression_generator<T>::binary_functor_t f0 = covov->f0();
               typename expression_generator<T>::binary_functor_t f1 = covov->f1();
               typename expression_generator<T>::binary_functor_t f2 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               details::free_node(*(expr_gen.node_allocator()),branch[0]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), c, v0, v1, v2, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o2,f2))
                  return expression_generator<T>::error_node();

               exprtk_debug(("((c o0 v0) o1 v1) o2 v2\n"));

               return node_type::allocate(*(expr_gen.node_allocator()), c, v0, v1, v2, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_covocov_expression3
         {
            typedef typename expression_generator<T>::covocov_t::type3 node_type;
            typedef typename expression_generator<T>::covocov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // ((c0 o0 v0) o1 c1) o2 v1
               typedef typename synthesize_covoc_expression0<T>::node_type lcl_covoc_t;

               const lcl_covoc_t* covoc = static_cast<const lcl_covoc_t*>(branch[0]);
               const T  c0 = covoc->t0();
               const T& v0 = covoc->t1();
               const T  c1 = covoc->t2();
               const T& v1 = static_cast<details::variable_node<T>*>(branch[1])->ref();
               const details::operator_type o0 = expr_gen.get_operator(covoc->f0());
               const details::operator_type o1 = expr_gen.get_operator(covoc->f1());
               const details::operator_type o2 = operation;

               typename expression_generator<T>::binary_functor_t f0 = covoc->f0();
               typename expression_generator<T>::binary_functor_t f1 = covoc->f1();
               typename expression_generator<T>::binary_functor_t f2 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               details::free_node(*(expr_gen.node_allocator()),branch[0]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), c0, v0, c1, v1, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o2,f2))
                  return expression_generator<T>::error_node();

               exprtk_debug(("((c0 o0 v0) o1 c1) o2 v1\n"));

               return node_type::allocate(*(expr_gen.node_allocator()), c0, v0, c1, v1, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_vocovoc_expression3
         {
            typedef typename expression_generator<T>::vocovoc_t::type3 node_type;
            typedef typename expression_generator<T>::vocovoc_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // ((v0 o0 c0) o1 v1) o2 c1
               typedef typename synthesize_vocov_expression0<T>::node_type lcl_vocov_t;

               const lcl_vocov_t* vocov = static_cast<const lcl_vocov_t*>(branch[0]);
               const T& v0 = vocov->t0();
               const T  c0 = vocov->t1();
               const T& v1 = vocov->t2();
               const T  c1 = static_cast<details::literal_node<T>*>(branch[1])->value();
               const details::operator_type o0 = expr_gen.get_operator(vocov->f0());
               const details::operator_type o1 = expr_gen.get_operator(vocov->f1());
               const details::operator_type o2 = operation;

               typename expression_generator<T>::binary_functor_t f0 = vocov->f0();
               typename expression_generator<T>::binary_functor_t f1 = vocov->f1();
               typename expression_generator<T>::binary_functor_t f2 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               details::free_node(*(expr_gen.node_allocator()),branch[0]);
               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, c0, v1, c1, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o2,f2))
                  return expression_generator<T>::error_node();

               exprtk_debug(("((v0 o0 c0) o1 v1) o2 c1\n"));

               return node_type::allocate(*(expr_gen.node_allocator()), v0, c0, v1, c1, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_covovoc_expression3
         {
            typedef typename expression_generator<T>::covovoc_t::type3 node_type;
            typedef typename expression_generator<T>::covovoc_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // ((c0 o0 v0) o1 v1) o2 c1
               typedef typename synthesize_covov_expression0<T>::node_type lcl_covov_t;

               const lcl_covov_t* covov = static_cast<const lcl_covov_t*>(branch[0]);
               const T  c0 = covov->t0();
               const T& v0 = covov->t1();
               const T& v1 = covov->t2();
               const T  c1 = static_cast<details::literal_node<T>*>(branch[1])->value();
               const details::operator_type o0 = expr_gen.get_operator(covov->f0());
               const details::operator_type o1 = expr_gen.get_operator(covov->f1());
               const details::operator_type o2 = operation;

               typename expression_generator<T>::binary_functor_t f0 = covov->f0();
               typename expression_generator<T>::binary_functor_t f1 = covov->f1();
               typename expression_generator<T>::binary_functor_t f2 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               details::free_node(*(expr_gen.node_allocator()),branch[0]);
               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), c0, v0, v1, c1, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o2,f2))
                  return expression_generator<T>::error_node();

               exprtk_debug(("((c0 o0 v0) o1 v1) o2 c1\n"));

               return node_type::allocate(*(expr_gen.node_allocator()), c0, v0, v1, c1, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_vococov_expression3
         {
            typedef typename expression_generator<T>::vococov_t::type3 node_type;
            typedef typename expression_generator<T>::vococov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // ((v0 o0 c0) o1 c1) o2 v1
               typedef typename synthesize_vococ_expression0<T>::node_type lcl_vococ_t;

               const lcl_vococ_t* vococ = static_cast<const lcl_vococ_t*>(branch[0]);
               const T& v0 = vococ->t0();
               const T  c0 = vococ->t1();
               const T  c1 = vococ->t2();
               const T& v1 = static_cast<details::variable_node<T>*>(branch[1])->ref();
               const details::operator_type o0 = expr_gen.get_operator(vococ->f0());
               const details::operator_type o1 = expr_gen.get_operator(vococ->f1());
               const details::operator_type o2 = operation;

               typename expression_generator<T>::binary_functor_t f0 = vococ->f0();
               typename expression_generator<T>::binary_functor_t f1 = vococ->f1();
               typename expression_generator<T>::binary_functor_t f2 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               details::free_node(*(expr_gen.node_allocator()),branch[0]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, c0, c1, v1, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o2,f2))
                  return expression_generator<T>::error_node();

               exprtk_debug(("((v0 o0 c0) o1 c1) o2 v1\n"));

               return node_type::allocate(*(expr_gen.node_allocator()), v0, c0, c1, v1, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_vovovov_expression4
         {
            typedef typename expression_generator<T>::vovovov_t::type4 node_type;
            typedef typename expression_generator<T>::vovovov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // (v0 o0 (v1 o1 v2)) o2 v3
               typedef typename synthesize_vovov_expression1<T>::node_type lcl_vovov_t;

               const lcl_vovov_t* vovov = static_cast<const lcl_vovov_t*>(branch[0]);
               const T& v0 = vovov->t0();
               const T& v1 = vovov->t1();
               const T& v2 = vovov->t2();
               const T& v3 = static_cast<details::variable_node<T>*>(branch[1])->ref();
               const details::operator_type o0 = expr_gen.get_operator(vovov->f0());
               const details::operator_type o1 = expr_gen.get_operator(vovov->f1());
               const details::operator_type o2 = operation;

               typename expression_generator<T>::binary_functor_t f0 = vovov->f0();
               typename expression_generator<T>::binary_functor_t f1 = vovov->f1();
               typename expression_generator<T>::binary_functor_t f2 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               details::free_node(*(expr_gen.node_allocator()),branch[0]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, v1, v2, v3, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o2,f2))
                  return expression_generator<T>::error_node();

               exprtk_debug(("(v0 o0 (v1 o1 v2)) o2 v3\n"));

               return node_type::allocate(*(expr_gen.node_allocator()), v0, v1, v2, v3, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_vovovoc_expression4
         {
            typedef typename expression_generator<T>::vovovoc_t::type4 node_type;
            typedef typename expression_generator<T>::vovovoc_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // ((v0 o0 (v1 o1 v2)) o2 c)
               typedef typename synthesize_vovov_expression1<T>::node_type lcl_vovov_t;

               const lcl_vovov_t* vovov = static_cast<const lcl_vovov_t*>(branch[0]);
               const T& v0 = vovov->t0();
               const T& v1 = vovov->t1();
               const T& v2 = vovov->t2();
               const T   c = static_cast<details::literal_node<T>*>(branch[1])->value();
               const details::operator_type o0 = expr_gen.get_operator(vovov->f0());
               const details::operator_type o1 = expr_gen.get_operator(vovov->f1());
               const details::operator_type o2 = operation;

               typename expression_generator<T>::binary_functor_t f0 = vovov->f0();
               typename expression_generator<T>::binary_functor_t f1 = vovov->f1();
               typename expression_generator<T>::binary_functor_t f2 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               details::free_node(*(expr_gen.node_allocator()),branch[0]);
               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, v1, v2, c, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o2,f2))
                  return expression_generator<T>::error_node();

               exprtk_debug(("((v0 o0 (v1 o1 v2)) o2 c)\n"));

               return node_type::allocate(*(expr_gen.node_allocator()), v0, v1, v2, c, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_vovocov_expression4
         {
            typedef typename expression_generator<T>::vovocov_t::type4 node_type;
            typedef typename expression_generator<T>::vovocov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // ((v0 o0 (v1 o1 c)) o2 v1)
               typedef typename synthesize_vovoc_expression1<T>::node_type lcl_vovoc_t;

               const lcl_vovoc_t* vovoc = static_cast<const lcl_vovoc_t*>(branch[0]);
               const T& v0 = vovoc->t0();
               const T& v1 = vovoc->t1();
               const T   c = vovoc->t2();
               const T& v2 = static_cast<details::variable_node<T>*>(branch[1])->ref();
               const details::operator_type o0 = expr_gen.get_operator(vovoc->f0());
               const details::operator_type o1 = expr_gen.get_operator(vovoc->f1());
               const details::operator_type o2 = operation;

               typename expression_generator<T>::binary_functor_t f0 = vovoc->f0();
               typename expression_generator<T>::binary_functor_t f1 = vovoc->f1();
               typename expression_generator<T>::binary_functor_t f2 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               details::free_node(*(expr_gen.node_allocator()),branch[0]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, v1, c, v2, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o2,f2))
                  return expression_generator<T>::error_node();

               exprtk_debug(("((v0 o0 (v1 o1 c)) o2 v1)\n"));

               return node_type::allocate(*(expr_gen.node_allocator()), v0, v1, c, v2, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_vocovov_expression4
         {
            typedef typename expression_generator<T>::vocovov_t::type4 node_type;
            typedef typename expression_generator<T>::vocovov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // ((v0 o0 (c o1 v1)) o2 v2)
               typedef typename synthesize_vocov_expression1<T>::node_type lcl_vocov_t;

               const lcl_vocov_t* vocov = static_cast<const lcl_vocov_t*>(branch[0]);
               const T& v0 = vocov->t0();
               const T   c = vocov->t1();
               const T& v1 = vocov->t2();
               const T& v2 = static_cast<details::variable_node<T>*>(branch[1])->ref();
               const details::operator_type o0 = expr_gen.get_operator(vocov->f0());
               const details::operator_type o1 = expr_gen.get_operator(vocov->f1());
               const details::operator_type o2 = operation;

               typename expression_generator<T>::binary_functor_t f0 = vocov->f0();
               typename expression_generator<T>::binary_functor_t f1 = vocov->f1();
               typename expression_generator<T>::binary_functor_t f2 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               details::free_node(*(expr_gen.node_allocator()),branch[0]);
               details::expression_node<T>* result = expression_generator<T>::error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, c, v1, v2, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o2,f2))
                  return expression_generator<T>::error_node();

               exprtk_debug(("((v0 o0 (c o1 v1)) o2 v2)\n"));

               return node_type::allocate(*(expr_gen.node_allocator()), v0, c, v1, v2, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_covovov_expression4
         {
            typedef typename expression_generator<T>::covovov_t::type4 node_type;
            typedef typename expression_generator<T>::covovov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // ((c o0 (v0 o1 v1)) o2 v2)
               typedef typename synthesize_covov_expression1<T>::node_type lcl_covov_t;

               const lcl_covov_t* covov = static_cast<const lcl_covov_t*>(branch[0]);
               const T   c = covov->t0();
               const T& v0 = covov->t1();
               const T& v1 = covov->t2();
               const T& v2 = static_cast<details::variable_node<T>*>(branch[1])->ref();
               const details::operator_type o0 = expr_gen.get_operator(covov->f0());
               const details::operator_type o1 = expr_gen.get_operator(covov->f1());
               const details::operator_type o2 = operation;

               typename expression_generator<T>::binary_functor_t f0 = covov->f0();
               typename expression_generator<T>::binary_functor_t f1 = covov->f1();
               typename expression_generator<T>::binary_functor_t f2 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               details::free_node(*(expr_gen.node_allocator()),branch[0]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), c, v0, v1, v2, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o2,f2))
                  return expression_generator<T>::error_node();

               exprtk_debug(("((c o0 (v0 o1 v1)) o2 v2)\n"));

               return node_type::allocate(*(expr_gen.node_allocator()), c, v0, v1, v2, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_covocov_expression4
         {
            typedef typename expression_generator<T>::covocov_t::type4 node_type;
            typedef typename expression_generator<T>::covocov_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // ((c0 o0 (v0 o1 c1)) o2 v1)
               typedef typename synthesize_covoc_expression1<T>::node_type lcl_covoc_t;

               const lcl_covoc_t* covoc = static_cast<const lcl_covoc_t*>(branch[0]);
               const T  c0 = covoc->t0();
               const T& v0 = covoc->t1();
               const T  c1 = covoc->t2();
               const T& v1 = static_cast<details::variable_node<T>*>(branch[1])->ref();
               const details::operator_type o0 = expr_gen.get_operator(covoc->f0());
               const details::operator_type o1 = expr_gen.get_operator(covoc->f1());
               const details::operator_type o2 = operation;

               typename expression_generator<T>::binary_functor_t f0 = covoc->f0();
               typename expression_generator<T>::binary_functor_t f1 = covoc->f1();
               typename expression_generator<T>::binary_functor_t f2 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               details::free_node(*(expr_gen.node_allocator()),branch[0]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), c0, v0, c1, v1, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o2,f2))
                  return expression_generator<T>::error_node();

               exprtk_debug(("((c0 o0 (v0 o1 c1)) o2 v1)\n"));

               return node_type::allocate(*(expr_gen.node_allocator()), c0, v0, c1, v1, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_vocovoc_expression4
         {
            typedef typename expression_generator<T>::vocovoc_t::type4 node_type;
            typedef typename expression_generator<T>::vocovoc_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // ((v0 o0 (c0 o1 v1)) o2 c1)
               typedef typename synthesize_vocov_expression1<T>::node_type lcl_vocov_t;

               const lcl_vocov_t* vocov = static_cast<const lcl_vocov_t*>(branch[0]);
               const T& v0 = vocov->t0();
               const T  c0 = vocov->t1();
               const T& v1 = vocov->t2();
               const T  c1 = static_cast<details::literal_node<T>*>(branch[1])->value();
               const details::operator_type o0 = expr_gen.get_operator(vocov->f0());
               const details::operator_type o1 = expr_gen.get_operator(vocov->f1());
               const details::operator_type o2 = operation;

               typename expression_generator<T>::binary_functor_t f0 = vocov->f0();
               typename expression_generator<T>::binary_functor_t f1 = vocov->f1();
               typename expression_generator<T>::binary_functor_t f2 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               details::free_node(*(expr_gen.node_allocator()),branch[0]);
               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), v0, c0, v1, c1, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o2,f2))
                  return expression_generator<T>::error_node();

               exprtk_debug(("((v0 o0 (c0 o1 v1)) o2 c1)\n"));

               return node_type::allocate(*(expr_gen.node_allocator()), v0, c0, v1, c1, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_covovoc_expression4
         {
            typedef typename expression_generator<T>::covovoc_t::type4 node_type;
            typedef typename expression_generator<T>::covovoc_t::sf4_type sf4_type;
            typedef typename node_type::T0 T0;
            typedef typename node_type::T1 T1;
            typedef typename node_type::T2 T2;
            typedef typename node_type::T3 T3;

            static details::expression_node<T>* process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      details::expression_node<T>* (&branch)[2])
            {
               // ((c0 o0 (v0 o1 v1)) o2 c1)
               typedef typename synthesize_covov_expression1<T>::node_type lcl_covov_t;

               const lcl_covov_t* covov = static_cast<const lcl_covov_t*>(branch[0]);
               const T  c0 = covov->t0();
               const T& v0 = covov->t1();
               const T& v1 = covov->t2();
               const T  c1 = static_cast<details::literal_node<T>*>(branch[1])->value();
               const details::operator_type o0 = expr_gen.get_operator(covov->f0());
               const details::operator_type o1 = expr_gen.get_operator(covov->f1());
               const details::operator_type o2 = operation;

               typename expression_generator<T>::binary_functor_t f0 = covov->f0();
               typename expression_generator<T>::binary_functor_t f1 = covov->f1();
               typename expression_generator<T>::binary_functor_t f2 = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

               details::free_node(*(expr_gen.node_allocator()),branch[0]);
               details::free_node(*(expr_gen.node_allocator()),branch[1]);

               details::expression_node<T>* result = expression_generator<T>::error_node();

               const bool synthesis_result =
                  synthesize_sf4ext_expression<T>::template compile<T0, T1, T2, T3>
                     (expr_gen, id(expr_gen, o0, o1, o2), c0, v0, v1, c1, result);

               if (synthesis_result)
                  return result;
               else if (!expr_gen.valid_operator(o2,f2))
                  return expression_generator<T>::error_node();

               exprtk_debug(("((c0 o0 (v0 o1 v1)) o2 c1)\n"));

               return node_type::allocate(*(expr_gen.node_allocator()), c0, v0, v1, c1, f0, f1, f2);
            }

            static std::string id(expression_generator<T>& expr_gen,
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

        template<typename T>
         struct synthesize_vococov_expression4
         {
            typedef typename expression_generator<T>::vococov_t::type4 node_type;
            static details::expression_node<T>* process(expression_generator<T>&,
                                                      const details::operator_type&,
                                                      details::expression_node<T>* (&)[2])
            {
               // ((v0 o0 (c0 o1 c1)) o2 v1) - Not possible
               exprtk_debug(("((v0 o0 (c0 o1 c1)) o2 v1) - Not possible\n"));
               return expression_generator<T>::error_node();
            }

            static std::string id(expression_generator<T>&,
                                         const details::operator_type,
                                         const details::operator_type,
                                         const details::operator_type)
            {
               return "INVALID";
            }
         };


        template<typename T>
         struct synthesize_binary_ext_expression
         {
            static expression_generator<T>::expression_node_ptr process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_generator<T>::expression_node_ptr (&branch)[2])
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
                          !expr_gen.parser()->simplify_unary_negation_branch(branch[0]) ||
                          !expr_gen.parser()->simplify_unary_negation_branch(branch[1])
                        )
                     {
                        details::free_all_nodes(*expr_gen.node_allocator(),branch);

                        return expression_generator<T>::error_node();
                     }
                  }

                  switch (operation)
                  {
                                           // -f(x + 1) + -g(y + 1) --> -(f(x + 1) + g(y + 1))
                     case details::e_add : return expr_gen(details::e_neg,
                                              expr_gen.node_allocator()->
                                                 template allocate<typename details::binary_ext_node<T,details::add_op<T> > >
                                                    (branch[0],branch[1]));

                                           // -f(x + 1) - -g(y + 1) --> g(y + 1) - f(x + 1)
                     case details::e_sub : return expr_gen.node_allocator()->
                                              template allocate<typename details::binary_ext_node<T,details::sub_op<T> > >
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
                     if (!expr_gen.parser()->simplify_unary_negation_branch(branch[0]))
                     {
                        details::free_all_nodes(*expr_gen.node_allocator(),branch);

                        return expression_generator<T>::error_node();
                     }

                     switch (operation)
                     {
                                              // -f(x + 1) + g(y + 1) --> g(y + 1) - f(x + 1)
                        case details::e_add : return expr_gen.node_allocator()->
                                                 template allocate<typename details::binary_ext_node<T,details::sub_op<T> > >
                                                   (branch[1], branch[0]);

                                              // -f(x + 1) - g(y + 1) --> -(f(x + 1) + g(y + 1))
                        case details::e_sub : return expr_gen(details::e_neg,
                                                 expr_gen.node_allocator()->
                                                    template allocate<typename details::binary_ext_node<T,details::add_op<T> > >
                                                       (branch[0], branch[1]));

                                              // -f(x + 1) * g(y + 1) --> -(f(x + 1) * g(y + 1))
                        case details::e_mul : return expr_gen(details::e_neg,
                                                 expr_gen.node_allocator()->
                                                    template allocate<typename details::binary_ext_node<T,details::mul_op<T> > >
                                                       (branch[0], branch[1]));

                                              // -f(x + 1) / g(y + 1) --> -(f(x + 1) / g(y + 1))
                        case details::e_div : return expr_gen(details::e_neg,
                                                 expr_gen.node_allocator()->
                                                    template allocate<typename details::binary_ext_node<T,details::div_op<T> > >
                                                       (branch[0], branch[1]));

                        default             : return expression_generator<T>::error_node();
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
                     if (!expr_gen.parser()->simplify_unary_negation_branch(branch[1]))
                     {
                        details::free_all_nodes(*expr_gen.node_allocator(),branch);

                        return expression_generator<T>::error_node();
                     }

                     switch (operation)
                     {
                                              // f(x + 1) + -g(y + 1) --> f(x + 1) - g(y + 1)
                        case details::e_add : return expr_gen.node_allocator()->
                                                 template allocate<typename details::binary_ext_node<T,details::sub_op<T> > >
                                                   (branch[0], branch[1]);

                                              // f(x + 1) - - g(y + 1) --> f(x + 1) + g(y + 1)
                        case details::e_sub : return expr_gen.node_allocator()->
                                                 template allocate<typename details::binary_ext_node<T,details::add_op<T> > >
                                                   (branch[0], branch[1]);

                                              // f(x + 1) * -g(y + 1) --> -(f(x + 1) * g(y + 1))
                        case details::e_mul : return expr_gen(details::e_neg,
                                                 expr_gen.node_allocator()->
                                                    template allocate<typename details::binary_ext_node<T,details::mul_op<T> > >
                                                       (branch[0], branch[1]));

                                              // f(x + 1) / -g(y + 1) --> -(f(x + 1) / g(y + 1))
                        case details::e_div : return expr_gen(details::e_neg,
                                                 expr_gen.node_allocator()->
                                                    template allocate<typename details::binary_ext_node<T,details::div_op<T> > >
                                                       (branch[0], branch[1]));

                        default             : return expression_generator<T>::error_node();
                     }
                  }
               }

               switch (operation)
               {
                  #define case_stmt(op0, op1)                                                          \
                  case op0 : return expr_gen.node_allocator()->                                         \
                                template allocate<typename details::binary_ext_node<T,op1<T> > > \
                                   (branch[0], branch[1]);                                             \

                  basic_opr_switch_statements
                  extended_opr_switch_statements
                  #undef case_stmt
                  default : return expression_generator<T>::error_node();
               }
            }
         };

        template<typename T>
         struct synthesize_vob_expression
         {
            static expression_generator<T>::expression_node_ptr process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_generator<T>::expression_node_ptr (&branch)[2])
            {
               const T& v = static_cast<details::variable_node<T>*>(branch[0])->ref();

               if (details::is_sf3ext_node(branch[1]))
               {
                  typename expression_generator<T>::expression_node_ptr result = expression_generator<T>::error_node();

                  const bool synthesis_result =
                     synthesize_sf4ext_expression<T>::template compile_right<typename expression_generator<T>::vtype>
                        (expr_gen, v, operation, branch[1], result);

                  if (synthesis_result)
                  {
                     details::free_node(*expr_gen.node_allocator(),branch[1]);
                     return result;
                  }
               }

               if (
                    (details::e_mul == operation) ||
                    (details::e_div == operation)
                  )
               {
                  if (details::is_uv_node(branch[1]))
                  {
                     typedef details::uv_base_node<T>* uvbn_ptr_t;

                     details::operator_type o = static_cast<uvbn_ptr_t>(branch[1])->operation();

                     if (details::e_neg == o)
                     {
                        const T& v1 = static_cast<uvbn_ptr_t>(branch[1])->v();

                        details::free_node(*expr_gen.node_allocator(),branch[1]);

                        switch (operation)
                        {
                           case details::e_mul : return expr_gen(details::e_neg,
                                                    expr_gen.node_allocator()->
                                                       template allocate_rr<typename details::
                                                          vov_node<T,details::mul_op<T> > >(v,v1));

                           case details::e_div : return expr_gen(details::e_neg,
                                                    expr_gen.node_allocator()->
                                                       template allocate_rr<typename details::
                                                          vov_node<T,details::div_op<T> > >(v,v1));

                           default             : break;
                        }
                     }
                  }
               }

               switch (operation)
               {
                  #define case_stmt(op0, op1)                                                      \
                  case op0 : return expr_gen.node_allocator()->                                     \
                                template allocate_rc<typename details::vob_node<T,op1<T> > > \
                                   (v, branch[1]);                                                 \

                  basic_opr_switch_statements
                  extended_opr_switch_statements
                  #undef case_stmt
                  default : return expression_generator<T>::error_node();
               }
            }
         };

        template<typename T>
         struct synthesize_bov_expression
         {
            static expression_generator<T>::expression_node_ptr process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_generator<T>::expression_node_ptr (&branch)[2])
            {
               const T& v = static_cast<details::variable_node<T>*>(branch[1])->ref();

               if (details::is_sf3ext_node(branch[0]))
               {
                  typename expression_generator<T>::expression_node_ptr result = expression_generator<T>::error_node();

                  const bool synthesis_result =
                     synthesize_sf4ext_expression<T>::template compile_left<typename expression_generator<T>::vtype>
                        (expr_gen, v, operation, branch[0], result);

                  if (synthesis_result)
                  {
                     details::free_node(*expr_gen.node_allocator(), branch[0]);

                     return result;
                  }
               }

               if (
                    (details::e_add == operation) ||
                    (details::e_sub == operation) ||
                    (details::e_mul == operation) ||
                    (details::e_div == operation)
                  )
               {
                  if (details::is_uv_node(branch[0]))
                  {
                     typedef details::uv_base_node<T>* uvbn_ptr_t;

                     details::operator_type o = static_cast<uvbn_ptr_t>(branch[0])->operation();

                     if (details::e_neg == o)
                     {
                        const T& v0 = static_cast<uvbn_ptr_t>(branch[0])->v();

                        details::free_node(*expr_gen.node_allocator(),branch[0]);

                        switch (operation)
                        {
                           case details::e_add : return expr_gen.node_allocator()->
                                                    template allocate_rr<typename details::
                                                       vov_node<T,details::sub_op<T> > >(v,v0);

                           case details::e_sub : return expr_gen(details::e_neg,
                                                    expr_gen.node_allocator()->
                                                       template allocate_rr<typename details::
                                                          vov_node<T,details::add_op<T> > >(v0,v));

                           case details::e_mul : return expr_gen(details::e_neg,
                                                    expr_gen.node_allocator()->
                                                       template allocate_rr<typename details::
                                                          vov_node<T,details::mul_op<T> > >(v0,v));

                           case details::e_div : return expr_gen(details::e_neg,
                                                    expr_gen.node_allocator()->
                                                       template allocate_rr<typename details::
                                                          vov_node<T,details::div_op<T> > >(v0,v));
                           default : break;
                        }
                     }
                  }
               }

               switch (operation)
               {
                  #define case_stmt(op0, op1)                                                      \
                  case op0 : return expr_gen.node_allocator()->                                     \
                                template allocate_cr<typename details::bov_node<T,op1<T> > > \
                                   (branch[0], v);                                                 \

                  basic_opr_switch_statements
                  extended_opr_switch_statements
                  #undef case_stmt
                  default : return expression_generator<T>::error_node();
               }
            }
         };

        template<typename T>
         struct synthesize_cob_expression
         {
            static expression_generator<T>::expression_node_ptr process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_generator<T>::expression_node_ptr (&branch)[2])
            {
               const T c = static_cast<details::literal_node<T>*>(branch[0])->value();

               details::free_node(*expr_gen.node_allocator(),branch[0]);

               if (std::equal_to<T>()(T(0),c) && (details::e_mul == operation))
               {
                  details::free_node(*expr_gen.node_allocator(),branch[1]);

                  return expr_gen(T(0));
               }
               else if (std::equal_to<T>()(T(0),c) && (details::e_div == operation))
               {
                  details::free_node(*expr_gen.node_allocator(), branch[1]);

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
                     details::cob_base_node<T>* cobnode = static_cast<details::cob_base_node<T>*>(branch[1]);

                     if (operation == cobnode->operation())
                     {
                        switch (operation)
                        {
                           case details::e_add : cobnode->set_c(c + cobnode->c()); break;
                           case details::e_mul : cobnode->set_c(c * cobnode->c()); break;
                           default             : return expression_generator<T>::error_node();
                        }

                        return cobnode;
                     }
                  }

                  if (operation == details::e_mul)
                  {
                     details::cob_base_node<T>* cobnode = static_cast<details::cob_base_node<T>*>(branch[1]);
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
                           default             : return expression_generator<T>::error_node();
                        }

                        return cobnode;
                     }
                  }
                  else if (operation == details::e_div)
                  {
                     details::cob_base_node<T>* cobnode = static_cast<details::cob_base_node<T>*>(branch[1]);
                     details::operator_type cob_opr = cobnode->operation();

                     if (
                          (details::e_div == cob_opr) ||
                          (details::e_mul == cob_opr)
                        )
                     {
                        details::expression_node<T>* new_cobnode = expression_generator<T>::error_node();

                        switch (cob_opr)
                        {
                           case details::e_div : new_cobnode = expr_gen.node_allocator()->
                                                    template allocate_tt<typename details::cob_node<T,details::mul_op<T> > >
                                                       (c / cobnode->c(), cobnode->move_branch(0));
                                                 break;

                           case details::e_mul : new_cobnode = expr_gen.node_allocator()->
                                                    template allocate_tt<typename details::cob_node<T,details::div_op<T> > >
                                                       (c / cobnode->c(), cobnode->move_branch(0));
                                                 break;

                           default             : return expression_generator<T>::error_node();
                        }

                        details::free_node(*expr_gen.node_allocator(),branch[1]);

                        return new_cobnode;
                     }
                  }
               }
               else if (details::is_sf3ext_node(branch[1]))
               {
                  typename expression_generator<T>::expression_node_ptr result = expression_generator<T>::error_node();

                  const bool synthesis_result =
                     synthesize_sf4ext_expression<T>::template compile_right<typename expression_generator<T>::ctype>
                        (expr_gen, c, operation, branch[1], result);

                  if (synthesis_result)
                  {
                     details::free_node(*expr_gen.node_allocator(),branch[1]);

                     return result;
                  }
               }

               switch (operation)
               {
                  #define case_stmt(op0, op1)                                                      \
                  case op0 : return expr_gen.node_allocator()->                                     \
                                template allocate_tt<typename details::cob_node<T,op1<T> > > \
                                   (c,  branch[1]);                                                \

                  basic_opr_switch_statements
                  extended_opr_switch_statements
                  #undef case_stmt
                  default : return expression_generator<T>::error_node();
               }
            }
         };

        template<typename T>
         struct synthesize_boc_expression
         {
            static expression_generator<T>::expression_node_ptr process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_generator<T>::expression_node_ptr (&branch)[2])
            {
               const T c = static_cast<details::literal_node<T>*>(branch[1])->value();

               details::free_node(*(expr_gen.node_allocator()), branch[1]);

               if (std::equal_to<T>()(T(0),c) && (details::e_mul == operation))
               {
                  details::free_node(*expr_gen.node_allocator(), branch[0]);

                  return expr_gen(T(0));
               }
               else if (std::equal_to<T>()(T(0),c) && (details::e_div == operation))
               {
                  details::free_node(*expr_gen.node_allocator(), branch[0]);

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
                     details::boc_base_node<T>* bocnode = static_cast<details::boc_base_node<T>*>(branch[0]);

                     if (operation == bocnode->operation())
                     {
                        switch (operation)
                        {
                           case details::e_add : bocnode->set_c(c + bocnode->c()); break;
                           case details::e_mul : bocnode->set_c(c * bocnode->c()); break;
                           default             : return expression_generator<T>::error_node();
                        }

                        return bocnode;
                     }
                  }
                  else if (operation == details::e_div)
                  {
                     details::boc_base_node<T>* bocnode = static_cast<details::boc_base_node<T>*>(branch[0]);
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
                           default             : return expression_generator<T>::error_node();
                        }

                        return bocnode;
                     }
                  }
                  else if (operation == details::e_pow)
                  {
                     // (v ^ c0) ^ c1 --> v ^(c0 * c1)
                     details::boc_base_node<T>* bocnode = static_cast<details::boc_base_node<T>*>(branch[0]);
                     details::operator_type        boc_opr = bocnode->operation();

                     if (details::e_pow == boc_opr)
                     {
                        bocnode->set_c(bocnode->c() * c);

                        return bocnode;
                     }
                  }
               }

               if (details::is_sf3ext_node(branch[0]))
               {
                  typename expression_generator<T>::expression_node_ptr result = expression_generator<T>::error_node();

                  const bool synthesis_result =
                     synthesize_sf4ext_expression<T>::template compile_left<typename expression_generator<T>::ctype>
                        (expr_gen, c, operation, branch[0], result);

                  if (synthesis_result)
                  {
                     free_node(*expr_gen.node_allocator(), branch[0]);

                     return result;
                  }
               }

               switch (operation)
               {
                  #define case_stmt(op0, op1)                                                      \
                  case op0 : return expr_gen.node_allocator()->                                     \
                                template allocate_cr<typename details::boc_node<T,op1<T> > > \
                                   (branch[0], c);                                                 \

                  basic_opr_switch_statements
                  extended_opr_switch_statements
                  #undef case_stmt
                  default : return expression_generator<T>::error_node();
               }
            }
         };

        template<typename T>
         struct synthesize_cocob_expression
         {
            static expression_generator<T>::expression_node_ptr process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_generator<T>::expression_node_ptr (&branch)[2])
            {
               typename expression_generator<T>::expression_node_ptr result = expression_generator<T>::error_node();

               // (cob) o c --> cob
               if (details::is_cob_node(branch[0]))
               {
                  details::cob_base_node<T>* cobnode = static_cast<details::cob_base_node<T>*>(branch[0]);

                  const T c = static_cast<details::literal_node<T>*>(branch[1])->value();

                  if (std::equal_to<T>()(T(0),c) && (details::e_mul == operation))
                  {
                     details::free_node(*expr_gen.node_allocator(), branch[0]);
                     details::free_node(*expr_gen.node_allocator(), branch[1]);

                     return expr_gen(T(0));
                  }
                  else if (std::equal_to<T>()(T(0),c) && (details::e_div == operation))
                  {
                     details::free_node(*expr_gen.node_allocator(), branch[0]);
                     details::free_node(*expr_gen.node_allocator(), branch[1]);

                     return expr_gen(T(std::numeric_limits<T>::quiet_NaN()));
                  }
                  else if (std::equal_to<T>()(T(0),c) && (details::e_add == operation))
                  {
                     details::free_node(*expr_gen.node_allocator(), branch[1]);

                     return branch[0];
                  }
                  else if (std::equal_to<T>()(T(1),c) && (details::e_mul == operation))
                  {
                     details::free_node(*expr_gen.node_allocator(), branch[1]);

                     return branch[0];
                  }
                  else if (std::equal_to<T>()(T(1),c) && (details::e_div == operation))
                  {
                     details::free_node(*expr_gen.node_allocator(), branch[1]);

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
                        default             : return expression_generator<T>::error_node();
                     }

                     result = cobnode;
                  }
                  else if (details::e_mul == cobnode->operation())
                  {
                     switch (operation)
                     {
                        case details::e_mul : cobnode->set_c(cobnode->c() * c); break;
                        case details::e_div : cobnode->set_c(cobnode->c() / c); break;
                        default             : return expression_generator<T>::error_node();
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
                        result = expr_gen.node_allocator()->
                                    template allocate_tt<typename details::cob_node<T,details::div_op<T> > >
                                       (cobnode->c() / c, cobnode->move_branch(0));

                        details::free_node(*expr_gen.node_allocator(), branch[0]);
                     }
                  }

                  if (result)
                  {
                     details::free_node(*expr_gen.node_allocator(),branch[1]);
                  }
               }

               // c o (cob) --> cob
               else if (details::is_cob_node(branch[1]))
               {
                  details::cob_base_node<T>* cobnode = static_cast<details::cob_base_node<T>*>(branch[1]);

                  const T c = static_cast<details::literal_node<T>*>(branch[0])->value();

                  if (std::equal_to<T>()(T(0),c) && (details::e_mul == operation))
                  {
                     details::free_node(*expr_gen.node_allocator(), branch[0]);
                     details::free_node(*expr_gen.node_allocator(), branch[1]);

                     return expr_gen(T(0));
                  }
                  else if (std::equal_to<T>()(T(0),c) && (details::e_div == operation))
                  {
                     details::free_node(*expr_gen.node_allocator(), branch[0]);
                     details::free_node(*expr_gen.node_allocator(), branch[1]);

                     return expr_gen(T(0));
                  }
                  else if (std::equal_to<T>()(T(0),c) && (details::e_add == operation))
                  {
                     details::free_node(*expr_gen.node_allocator(), branch[0]);

                     return branch[1];
                  }
                  else if (std::equal_to<T>()(T(1),c) && (details::e_mul == operation))
                  {
                     details::free_node(*expr_gen.node_allocator(), branch[0]);

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
                        result = expr_gen.node_allocator()->
                                    template allocate_tt<typename details::cob_node<T,details::sub_op<T> > >
                                       (c - cobnode->c(), cobnode->move_branch(0));

                        details::free_node(*expr_gen.node_allocator(),branch[1]);
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
                        result = expr_gen.node_allocator()->
                                    template allocate_tt<typename details::cob_node<T,details::add_op<T> > >
                                       (c - cobnode->c(), cobnode->move_branch(0));

                        details::free_node(*expr_gen.node_allocator(),branch[1]);
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
                        result = expr_gen.node_allocator()->
                                    template allocate_tt<typename details::cob_node<T,details::div_op<T> > >
                                       (c / cobnode->c(), cobnode->move_branch(0));

                        details::free_node(*expr_gen.node_allocator(),branch[1]);
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
                        result = expr_gen.node_allocator()->
                                    template allocate_tt<typename details::cob_node<T,details::mul_op<T> > >
                                       (c / cobnode->c(), cobnode->move_branch(0));

                        details::free_node(*expr_gen.node_allocator(),branch[1]);
                     }
                  }

                  if (result)
                  {
                     details::free_node(*expr_gen.node_allocator(),branch[0]);
                  }
               }

               return result;
            }
         };

        template<typename T>
         struct synthesize_coboc_expression
         {
            static expression_generator<T>::expression_node_ptr process(expression_generator<T>& expr_gen,
                                                      const details::operator_type& operation,
                                                      expression_generator<T>::expression_node_ptr (&branch)[2])
            {
               typename expression_generator<T>::expression_node_ptr result = expression_generator<T>::error_node();

               // (boc) o c --> boc
               if (details::is_boc_node(branch[0]))
               {
                  details::boc_base_node<T>* bocnode = static_cast<details::boc_base_node<T>*>(branch[0]);

                  const T c = static_cast<details::literal_node<T>*>(branch[1])->value();

                  if (details::e_add == bocnode->operation())
                  {
                     switch (operation)
                     {
                        case details::e_add : bocnode->set_c(bocnode->c() + c); break;
                        case details::e_sub : bocnode->set_c(bocnode->c() - c); break;
                        default             : return expression_generator<T>::error_node();
                     }

                     result = bocnode;
                  }
                  else if (details::e_mul == bocnode->operation())
                  {
                     switch (operation)
                     {
                        case details::e_mul : bocnode->set_c(bocnode->c() * c); break;
                        case details::e_div : bocnode->set_c(bocnode->c() / c); break;
                        default             : return expression_generator<T>::error_node();
                     }

                     result = bocnode;
                  }
                  else if (details::e_sub == bocnode->operation())
                  {
                     if (details::e_add == operation)
                     {
                        result = expr_gen.node_allocator()->
                                    template allocate_tt<typename details::boc_node<T,details::add_op<T> > >
                                       (bocnode->move_branch(0), c - bocnode->c());

                        details::free_node(*expr_gen.node_allocator(),branch[0]);
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
                        default             : return expression_generator<T>::error_node();
                     }

                     result = bocnode;
                  }

                  if (result)
                  {
                     details::free_node(*expr_gen.node_allocator(), branch[1]);
                  }
               }

               // c o (boc) --> boc
               else if (details::is_boc_node(branch[1]))
               {
                  details::boc_base_node<T>* bocnode = static_cast<details::boc_base_node<T>*>(branch[1]);

                  const T c = static_cast<details::literal_node<T>*>(branch[0])->value();

                  if (details::e_add == bocnode->operation())
                  {
                     if (details::e_add == operation)
                     {
                        bocnode->set_c(c + bocnode->c());
                        result = bocnode;
                     }
                     else if (details::e_sub == operation)
                     {
                        result = expr_gen.node_allocator()->
                                    template allocate_tt<typename details::cob_node<T,details::sub_op<T> > >
                                       (c - bocnode->c(), bocnode->move_branch(0));

                        details::free_node(*expr_gen.node_allocator(),branch[1]);
                     }
                  }
                  else if (details::e_sub == bocnode->operation())
                  {
                     if (details::e_add == operation)
                     {
                        result = expr_gen.node_allocator()->
                                    template allocate_tt<typename details::boc_node<T,details::add_op<T> > >
                                       (bocnode->move_branch(0), c - bocnode->c());

                        details::free_node(*expr_gen.node_allocator(),branch[1]);
                     }
                     else if (details::e_sub == operation)
                     {
                        result = expr_gen.node_allocator()->
                                    template allocate_tt<typename details::cob_node<T,details::sub_op<T> > >
                                       (c + bocnode->c(), bocnode->move_branch(0));

                        details::free_node(*expr_gen.node_allocator(),branch[1]);
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
                        result = expr_gen.node_allocator()->
                                    template allocate_tt<typename details::cob_node<T,details::div_op<T> > >
                                       (c / bocnode->c(), bocnode->move_branch(0));

                        details::free_node(*expr_gen.node_allocator(),branch[1]);
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
                        result = expr_gen.node_allocator()->
                                    template allocate_tt<typename details::cob_node<T,details::div_op<T> > >
                                       (c * bocnode->c(), bocnode->move_branch(0));

                        details::free_node(*expr_gen.node_allocator(),branch[1]);
                     }
                  }

                  if (result)
                  {
                     details::free_node(*expr_gen.node_allocator(),branch[0]);
                  }
               }

               return result;
            }
         };

        template<typename T> void expression_generator<T>::init_synthesize_map()
         {
            if(details::disable_enhanced_features)
               return;
            synthesize_map_["(v)o(v)"] = synthesize_vov_expression<T>::process;
            synthesize_map_["(c)o(v)"] = synthesize_cov_expression<T>::process;
            synthesize_map_["(v)o(c)"] = synthesize_voc_expression<T>::process;

            #define register_synthezier(S)                      \
            synthesize_map_[S ::node_type::id()] = S ::process; \

            register_synthezier(synthesize_vovov_expression0<T>)
            register_synthezier(synthesize_vovov_expression1<T>)
            register_synthezier(synthesize_vovoc_expression0<T>)
            register_synthezier(synthesize_vovoc_expression1<T>)
            register_synthezier(synthesize_vocov_expression0<T>)
            register_synthezier(synthesize_vocov_expression1<T>)
            register_synthezier(synthesize_covov_expression0<T>)
            register_synthezier(synthesize_covov_expression1<T>)
            register_synthezier(synthesize_covoc_expression0<T>)
            register_synthezier(synthesize_covoc_expression1<T>)
            register_synthezier(synthesize_cocov_expression1<T>)
            register_synthezier(synthesize_vococ_expression0<T>)

            register_synthezier(synthesize_vovovov_expression0<T>)
            register_synthezier(synthesize_vovovoc_expression0<T>)
            register_synthezier(synthesize_vovocov_expression0<T>)
            register_synthezier(synthesize_vocovov_expression0<T>)
            register_synthezier(synthesize_covovov_expression0<T>)
            register_synthezier(synthesize_covocov_expression0<T>)
            register_synthezier(synthesize_vocovoc_expression0<T>)
            register_synthezier(synthesize_covovoc_expression0<T>)
            register_synthezier(synthesize_vococov_expression0<T>)

            register_synthezier(synthesize_vovovov_expression1<T>)
            register_synthezier(synthesize_vovovoc_expression1<T>)
            register_synthezier(synthesize_vovocov_expression1<T>)
            register_synthezier(synthesize_vocovov_expression1<T>)
            register_synthezier(synthesize_covovov_expression1<T>)
            register_synthezier(synthesize_covocov_expression1<T>)
            register_synthezier(synthesize_vocovoc_expression1<T>)
            register_synthezier(synthesize_covovoc_expression1<T>)
            register_synthezier(synthesize_vococov_expression1<T>)

            register_synthezier(synthesize_vovovov_expression2<T>)
            register_synthezier(synthesize_vovovoc_expression2<T>)
            register_synthezier(synthesize_vovocov_expression2<T>)
            register_synthezier(synthesize_vocovov_expression2<T>)
            register_synthezier(synthesize_covovov_expression2<T>)
            register_synthezier(synthesize_covocov_expression2<T>)
            register_synthezier(synthesize_vocovoc_expression2<T>)
            register_synthezier(synthesize_covovoc_expression2<T>)

            register_synthezier(synthesize_vovovov_expression3<T>)
            register_synthezier(synthesize_vovovoc_expression3<T>)
            register_synthezier(synthesize_vovocov_expression3<T>)
            register_synthezier(synthesize_vocovov_expression3<T>)
            register_synthezier(synthesize_covovov_expression3<T>)
            register_synthezier(synthesize_covocov_expression3<T>)
            register_synthezier(synthesize_vocovoc_expression3<T>)
            register_synthezier(synthesize_covovoc_expression3<T>)
            register_synthezier(synthesize_vococov_expression3<T>)

            register_synthezier(synthesize_vovovov_expression4<T>)
            register_synthezier(synthesize_vovovoc_expression4<T>)
            register_synthezier(synthesize_vovocov_expression4<T>)
            register_synthezier(synthesize_vocovov_expression4<T>)
            register_synthezier(synthesize_covovov_expression4<T>)
            register_synthezier(synthesize_covocov_expression4<T>)
            register_synthezier(synthesize_vocovoc_expression4<T>)
            register_synthezier(synthesize_covovoc_expression4<T>)
         }

         template<typename T> void expression_generator<T>::set_parser(parser_t& p)
         {
            parser_ = &p;
         }

         template<typename T> void expression_generator<T>::set_uom(unary_op_map_t& unary_op_map)
         {
            unary_op_map_ = &unary_op_map;
         }

         template<typename T> void expression_generator<T>::set_bom(binary_op_map_t& binary_op_map)
         {
            binary_op_map_ = &binary_op_map;
         }

         template<typename T> void expression_generator<T>::set_ibom(inv_binary_op_map_t& inv_binary_op_map)
         {
            inv_binary_op_map_ = &inv_binary_op_map;
         }

         template<typename T> void expression_generator<T>::set_sf3m(sf3_map_t& sf3_map)
         {
            sf3_map_ = &sf3_map;
         }

         template<typename T> void expression_generator<T>::set_sf4m(sf4_map_t& sf4_map)
         {
            sf4_map_ = &sf4_map;
         }

         template<typename T> void expression_generator<T>::set_allocator(details::node_allocator& na)
         {
            node_allocator_ = &na;
         }

         template<typename T> void expression_generator<T>::set_strength_reduction_state(const bool enabled)
         {
            strength_reduction_enabled_ = enabled;
         }

         template<typename T> bool expression_generator<T>::strength_reduction_enabled() const
         {
            return strength_reduction_enabled_;
         }

         template<typename T> bool expression_generator<T>::valid_operator(const details::operator_type& operation, expression_generator<T>::binary_functor_t& bop)
         {
            typename binary_op_map_t::iterator bop_itr = binary_op_map_->find(operation);

            if ((*binary_op_map_).end() == bop_itr)
               return false;

            bop = bop_itr->second;

            return true;
         }

         template<typename T> bool expression_generator<T>::valid_operator(const details::operator_type& operation, unary_functor_t& uop)
         {
            typename unary_op_map_t::iterator uop_itr = unary_op_map_->find(operation);

            if ((*unary_op_map_).end() == uop_itr)
               return false;

            uop = uop_itr->second;

            return true;
         }

         template<typename T> details::operator_type expression_generator<T>::get_operator(const expression_generator<T>::binary_functor_t& bop) const
         {
            return (*inv_binary_op_map_).find(bop)->second;
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::operator() (const T& v) const
         {
            return node_allocator_->template allocate<literal_node_t>(v);
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::operator() (const std::string& s) const
         {
            return node_allocator_->template allocate<string_literal_node_t>(s);
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::operator() (std::string& s, range_t& rp) const
         {
            return node_allocator_->template allocate_rr<string_range_node_t>(s,rp);
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::operator() (const std::string& s, range_t& rp) const
         {
            return node_allocator_->template allocate_tt<const_string_range_node_t>(s,rp);
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::operator() (expression_node_ptr branch, range_t& rp) const
         {
            if (is_generally_string_node(branch))
               return node_allocator_->template allocate_tt<generic_string_range_node_t>(branch,rp);
            else
               return error_node();
         }

         template<typename T> bool expression_generator<T>::unary_optimisable(const details::operator_type& operation) const
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

         template<typename T> bool expression_generator<T>::sf3_optimisable(const std::string& sf3id, trinary_functor_t& tfunc) const
         {
            typename sf3_map_t::const_iterator itr = sf3_map_->find(sf3id);

            if (sf3_map_->end() == itr)
               return false;
            else
               tfunc = itr->second.first;

            return true;
         }

         template<typename T> bool expression_generator<T>::sf4_optimisable(const std::string& sf4id, quaternary_functor_t& qfunc) const
         {
            typename sf4_map_t::const_iterator itr = sf4_map_->find(sf4id);

            if (sf4_map_->end() == itr)
               return false;
            else
               qfunc = itr->second.first;

            return true;
         }

         template<typename T> bool expression_generator<T>::sf3_optimisable(const std::string& sf3id, details::operator_type& operation) const
         {
            typename sf3_map_t::const_iterator itr = sf3_map_->find(sf3id);

            if (sf3_map_->end() == itr)
               return false;
            else
               operation = itr->second.second;

            return true;
         }

         template<typename T> bool expression_generator<T>::sf4_optimisable(const std::string& sf4id, details::operator_type& operation) const
         {
            typename sf4_map_t::const_iterator itr = sf4_map_->find(sf4id);

            if (sf4_map_->end() == itr)
               return false;
            else
               operation = itr->second.second;

            return true;
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::operator() (const details::operator_type& operation, expression_node_ptr (&branch)[1])
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

         template<typename T> bool expression_generator<T>::is_assignment_operation(const details::operator_type& operation) const
         {
            return (
                     (details::e_addass == operation) ||
                     (details::e_subass == operation) ||
                     (details::e_mulass == operation) ||
                     (details::e_divass == operation) ||
                     (details::e_modass == operation)
                   ) &&
                   parser_->settings().assignment_enabled(operation);
         }

         template<typename T> bool expression_generator<T>::valid_string_operation(const details::operator_type& operation) const
         {
            if(!details::disable_string_capabilities){
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
            }else{
               return false;
            }
         }

         template<typename T> std::string expression_generator<T>::to_str(const details::operator_type& operation) const
         {
            switch (operation)
            {
               case details::e_add  : return "+"      ;
               case details::e_sub  : return "-"      ;
               case details::e_mul  : return "*"      ;
               case details::e_div  : return "/"      ;
               case details::e_mod  : return "mod"      ;
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

         template<typename T> bool expression_generator<T>::operation_optimisable(const details::operator_type& operation) const
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

         template<typename T> std::string expression_generator<T>::branch_to_id(expression_node_ptr branch) const
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

         template<typename T> std::string expression_generator<T>::branch_to_id(expression_node_ptr (&branch)[2]) const
         {
            return branch_to_id(branch[0]) + std::string("o") + branch_to_id(branch[1]);
         }

         template<typename T> bool expression_generator<T>::cov_optimisable(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const
         {
            if (!operation_optimisable(operation))
               return false;
            else
               return details::is_constant_node(branch[0]) &&
                      details::is_variable_node(branch[1]) ;
         }

         template<typename T> bool expression_generator<T>::voc_optimisable(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const
         {
            if (!operation_optimisable(operation))
               return false;
            else
               return details::is_variable_node(branch[0]) &&
                      details::is_constant_node(branch[1]) ;
         }

         template<typename T> bool expression_generator<T>::vov_optimisable(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const
         {
            if (!operation_optimisable(operation))
               return false;
            else
               return details::is_variable_node(branch[0]) &&
                      details::is_variable_node(branch[1]) ;
         }

         template<typename T> bool expression_generator<T>::cob_optimisable(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const
         {
            if (!operation_optimisable(operation))
               return false;
            else
               return details::is_constant_node(branch[0]) &&
                     !details::is_constant_node(branch[1]) ;
         }

         template<typename T> bool expression_generator<T>::boc_optimisable(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const
         {
            if (!operation_optimisable(operation))
               return false;
            else
               return !details::is_constant_node(branch[0]) &&
                       details::is_constant_node(branch[1]) ;
         }

         template<typename T> bool expression_generator<T>::cocob_optimisable(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const
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

         template<typename T> bool expression_generator<T>::coboc_optimisable(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const
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

         template<typename T> bool expression_generator<T>::uvouv_optimisable(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const
         {
            if (!operation_optimisable(operation))
               return false;
            else
               return details::is_uv_node(branch[0]) &&
                      details::is_uv_node(branch[1]) ;
         }

         template<typename T> bool expression_generator<T>::vob_optimisable(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const
         {
            if (!operation_optimisable(operation))
               return false;
            else
               return details::is_variable_node(branch[0]) &&
                     !details::is_variable_node(branch[1]) ;
         }

         template<typename T> bool expression_generator<T>::bov_optimisable(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const
         {
            if (!operation_optimisable(operation))
               return false;
            else
               return !details::is_variable_node(branch[0]) &&
                       details::is_variable_node(branch[1]) ;
         }

         template<typename T> bool expression_generator<T>::binext_optimisable(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const
         {
            if (!operation_optimisable(operation))
               return false;
            else
               return !details::is_constant_node(branch[0]) ||
                      !details::is_constant_node(branch[1]) ;
         }

         template<typename T> bool expression_generator<T>::is_invalid_assignment_op(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const
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

         template<typename T> bool expression_generator<T>::is_constpow_operation(const details::operator_type& operation, expression_node_ptr(&branch)[2]) const
         {
            if (
                 !details::is_constant_node(branch[1]) ||
                  details::is_constant_node(branch[0]) ||
                  details::is_variable_node(branch[0]) ||
                  details::is_vector_node  (branch[0]) ||
                  details::is_generally_string_node(branch[0])
               )
               return false;

            const T c = static_cast<details::literal_node<T>*>(branch[1])->value();

            return cardinal_pow_optimisable(operation, c);
         }

         template<typename T> bool expression_generator<T>::is_invalid_break_continue_op(expression_node_ptr (&branch)[2]) const
         {
            return (
                     details::is_break_node   (branch[0]) ||
                     details::is_break_node   (branch[1]) ||
                     details::is_continue_node(branch[0]) ||
                     details::is_continue_node(branch[1])
                   );
         }

         template<typename T> bool expression_generator<T>::is_invalid_string_op(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const
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

         template<typename T> bool expression_generator<T>::is_invalid_string_op(const details::operator_type& operation, expression_node_ptr (&branch)[3]) const
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

         template<typename T> bool expression_generator<T>::is_string_operation(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const
         {
            const bool b0_string = is_generally_string_node(branch[0]);
            const bool b1_string = is_generally_string_node(branch[1]);

            return (b0_string && b1_string && valid_string_operation(operation));
         }

         template<typename T> bool expression_generator<T>::is_string_operation(const details::operator_type& operation, expression_node_ptr (&branch)[3]) const
         {
            const bool b0_string = is_generally_string_node(branch[0]);
            const bool b1_string = is_generally_string_node(branch[1]);
            const bool b2_string = is_generally_string_node(branch[2]);

            return (b0_string && b1_string && b2_string && (details::e_inrange == operation));
         }

         template<typename T> bool expression_generator<T>::is_shortcircuit_expression(const details::operator_type& operation) const
         {
            if(details::disable_sc_andor)
               return false;
            return (
                     (details::e_scand == operation) ||
                     (details::e_scor  == operation)
                   );
         }

         template<typename T> bool expression_generator<T>::is_null_present(expression_node_ptr (&branch)[2]) const
         {
            return (
                     details::is_null_node(branch[0]) ||
                     details::is_null_node(branch[1])
                   );
         }

         template<typename T> bool expression_generator<T>::is_vector_eqineq_logic_operation(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const
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

         template<typename T> bool expression_generator<T>::is_vector_arithmetic_operation(const details::operator_type& operation, expression_node_ptr (&branch)[2]) const
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

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::operator() (const details::operator_type& operation, expression_node_ptr (&branch)[2])
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
            else if (is_constpow_operation(operation, branch) && !details::disable_cardinal_pow_optimisation)
            {
               return cardinal_pow_optimisation(branch);
            }

            expression_node_ptr result = error_node();

            if(!details::disable_enhanced_features){
               if (synthesize_expression(operation, branch, result))
               {
                  return result;
               }
               else
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
                     result = synthesize_cocob_expression<T>::process((*this), operation, branch);
                  }
                  else if (coboc_optimisable(operation, branch) && (0 == result))
                  {
                     result = synthesize_coboc_expression<T>::process((*this), operation, branch);
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
                  return synthesize_vob_expression<T>::process((*this), operation, branch);
               }
               else if (bov_optimisable(operation, branch))
               {
                  return synthesize_bov_expression<T>::process((*this), operation, branch);
               }
               else if (cob_optimisable(operation, branch))
               {
                  return synthesize_cob_expression<T>::process((*this), operation, branch);
               }
               else if (boc_optimisable(operation, branch))
               {
                  return synthesize_boc_expression<T>::process((*this), operation, branch);
               }
               else if (cov_optimisable(operation, branch))
               {
                  return synthesize_cov_expression<T>::process((*this), operation, branch);
               }
               else if (binext_optimisable(operation, branch))
               {
                  return synthesize_binary_ext_expression<T>::process((*this), operation, branch);
               }
               else
                  return synthesize_expression<binary_node_t,2>(operation, branch);
            }else{
               return synthesize_expression<binary_node_t,2>(operation, branch);
            }
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::operator() (const details::operator_type& operation, expression_node_ptr (&branch)[3])
         {
            if (
                 (0 == branch[0]) ||
                 (0 == branch[1]) ||
                 (0 == branch[2])
               )
            {
               details::free_all_nodes(*node_allocator(),branch);

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

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::operator() (const details::operator_type& operation, expression_node_ptr (&branch)[4])
         {
            return synthesize_expression<quaternary_node_t,4>(operation,branch);
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::operator() (const details::operator_type& operation, expression_node_ptr b0)
         {
            expression_node_ptr branch[1] = { b0 };
            return (*this)(operation,branch);
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::operator() (const details::operator_type& operation, expression_node_ptr& b0, expression_node_ptr& b1)
         {
            expression_node_ptr result = error_node();

            if ((0 != b0) && (0 != b1))
            {
               expression_node_ptr branch[2] = { b0, b1 };
               result = expression_generator<T>::operator()(operation, branch);
               b0 = branch[0];
               b1 = branch[1];
            }

            return result;
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::conditional(expression_node_ptr condition,
                                                expression_node_ptr consequent,
                                                expression_node_ptr alternative) const
         {
            if(details::disable_string_capabilities){
               return error_node();
            }

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
                     return node_allocator_->template allocate<details::null_node<T> >();
               }
            }
            else if ((0 != consequent) && (0 != alternative))
            {
               return node_allocator_->template allocate<conditional_node_t>(condition, consequent, alternative);
            }
            else
               return node_allocator_->template allocate<cons_conditional_node_t>(condition, consequent);
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::conditional_string(expression_node_ptr condition,
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
                     return node_allocator_->template allocate_c<details::string_literal_node<T> >("");
               }
            }
            else if ((0 != consequent) && (0 != alternative))
               return node_allocator_->template allocate<conditional_string_node_t>(condition, consequent, alternative);
            else
               return error_node();
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::conditional_vector(expression_node_ptr condition,
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
                     return node_allocator_->template allocate<details::null_node<T> >();

               }
            }
            else if ((0 != consequent) && (0 != alternative))
            {
               return node_allocator_->template allocate<conditional_vector_node_t>(condition, consequent, alternative);
            }
            else
               return error_node();
         }

         template<typename T> loop_runtime_check_ptr expression_generator<T>::get_loop_runtime_check(const loop_runtime_check::loop_types loop_type) const
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

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::while_loop(expression_node_ptr& condition,
                                               expression_node_ptr& branch,
                                               const bool break_continue_present) const
         {
            if (!break_continue_present && details::is_constant_node(condition))
            {
               expression_node_ptr result = error_node();
               if (details::is_true(condition))
                  // Infinite loops are not allowed.
                  result = error_node();
               else
                  result = node_allocator_->template allocate<details::null_node<T> >();

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
                  return node_allocator_->template allocate<while_loop_rtc_node_t>
                           (condition, branch,  rtc);
               else
                  return node_allocator_->template allocate<while_loop_node_t>
                           (condition, branch);
            }
            else if(!details::disable_break_continue)
            {
               if (rtc)
                  return node_allocator_->template allocate<while_loop_bc_rtc_node_t>
                           (condition, branch, rtc);
               else
                  return node_allocator_->template allocate<while_loop_bc_node_t>
                           (condition, branch);
            }
            else
               return error_node();
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::repeat_until_loop(expression_node_ptr& condition,
                                                      expression_node_ptr& branch,
                                                      const bool break_continue_present) const
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
                  return node_allocator_->template allocate<repeat_until_loop_rtc_node_t>
                           (condition, branch,  rtc);
               else
                  return node_allocator_->template allocate<repeat_until_loop_node_t>
                           (condition, branch);
            }
            else if(!details::disable_break_continue)
            {
               if (rtc)
                  return node_allocator_->template allocate<repeat_until_loop_bc_rtc_node_t>
                           (condition, branch, rtc);
               else
                  return node_allocator_->template allocate<repeat_until_loop_bc_node_t>
                           (condition, branch);
            } else
               return error_node();
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::for_loop(expression_node_ptr& initialiser,
                                             expression_node_ptr& condition,
                                             expression_node_ptr& incrementor,
                                             expression_node_ptr& loop_body,
                                             bool break_continue_present) const
         {
            if (!break_continue_present && details::is_constant_node(condition))
            {
               expression_node_ptr result = error_node();

               if (details::is_true(condition))
                  // Infinite loops are not allowed.
                  result = error_node();
               else
                  result = node_allocator_->template allocate<details::null_node<T> >();

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
                  return node_allocator_->template allocate<for_loop_rtc_node_t>
                                          (
                                            initialiser,
                                            condition,
                                            incrementor,
                                            loop_body,
                                            rtc
                                          );
               else
                  return node_allocator_->template allocate<for_loop_node_t>
                                          (
                                            initialiser,
                                            condition,
                                            incrementor,
                                            loop_body
                                          );
            }
            else if(!details::disable_break_continue)
            {
               if (rtc)
                  return node_allocator_->template allocate<for_loop_bc_rtc_node_t>
                                          (
                                            initialiser,
                                            condition,
                                            incrementor,
                                            loop_body,
                                            rtc
                                          );
               else
                  return node_allocator_->template allocate<for_loop_bc_node_t>
                                          (
                                            initialiser,
                                            condition,
                                            incrementor,
                                            loop_body
                                          );
            } else
               return error_node();
         }


            #define case_stmt(N)                                                         \
            if (is_true(arg[(2 * N)].first)) { return arg[(2 * N) + 1].first->value(); } \

               template<typename T> T expression_generator<T>::switch_nodes::switch_impl_1::process(const arg_list_t& arg)
               {
                  case_stmt(0)

                  assert(arg.size() == ((2 * 1) + 1));

                  return arg.back().first->value();
               }

               template<typename T> T expression_generator<T>::switch_nodes::switch_impl_2::process(const arg_list_t& arg)
               {
                  case_stmt(0) case_stmt(1)

                  assert(arg.size() == ((2 * 2) + 1));

                  return arg.back().first->value();
               }

            template<typename T> T expression_generator<T>::switch_nodes::switch_impl_3::process(const arg_list_t& arg)
               {
                  case_stmt(0) case_stmt(1)
                  case_stmt(2)

                  assert(arg.size() == ((2 * 3) + 1));

                  return arg.back().first->value();
               }
            
            template<typename T> T expression_generator<T>::switch_nodes::switch_impl_4::process(const arg_list_t& arg)
               {
                  case_stmt(0) case_stmt(1)
                  case_stmt(2) case_stmt(3)

                  assert(arg.size() == ((2 * 4) + 1));

                  return arg.back().first->value();
               }
               
            template<typename T> T expression_generator<T>::switch_nodes::switch_impl_5::process(const arg_list_t& arg)
               {
                  case_stmt(0) case_stmt(1)
                  case_stmt(2) case_stmt(3)
                  case_stmt(4)

                  assert(arg.size() == ((2 * 5) + 1));

                  return arg.back().first->value();
               }
               
            template<typename T> T expression_generator<T>::switch_nodes::switch_impl_6::process(const arg_list_t& arg)
               {
                  case_stmt(0) case_stmt(1)
                  case_stmt(2) case_stmt(3)
                  case_stmt(4) case_stmt(5)

                  assert(arg.size() == ((2 * 6) + 1));

                  return arg.back().first->value();
               }
               
            template<typename T> T expression_generator<T>::switch_nodes::switch_impl_7::process(const arg_list_t& arg)
               {
                  case_stmt(0) case_stmt(1)
                  case_stmt(2) case_stmt(3)
                  case_stmt(4) case_stmt(5)
                  case_stmt(6)

                  assert(arg.size() == ((2 * 7) + 1));

                  return arg.back().first->value();
               }

            #undef case_stmt

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

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::synthesize_uv_expression(const details::operator_type& operation,
                                                             expression_node_ptr (&branch)[1])
         {
            T& v = static_cast<details::variable_node<T>*>(branch[0])->ref();

            switch (operation)
            {
               #define case_stmt(op0, op1)                                                         \
               case op0 : return node_allocator_->template allocate<typename details::unary_variable_node<T,op1<T> > >(v);

               unary_opr_switch_statements
               #undef case_stmt
               default : return error_node();
            }
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::synthesize_uvec_expression(const details::operator_type& operation,
                                                               expression_node_ptr (&branch)[1])
         {
            switch (operation)
            {
               #define case_stmt(op0, op1)                                                   \
               case op0 : return node_allocator_->template allocate<typename details::unary_vector_node<T,op1<T> > > (operation, branch[0]);

               unary_opr_switch_statements
               #undef case_stmt
               default : return error_node();
            }
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::synthesize_unary_expression(const details::operator_type& operation,
                                                                expression_node_ptr (&branch)[1])
         {
            switch (operation)
            {
               #define case_stmt(op0, op1)                                                               \
               case op0 : return node_allocator_->template allocate<typename details::unary_branch_node<T,op1<T> > >(branch[0]);

               unary_opr_switch_statements
               #undef case_stmt
               default : return error_node();
            }
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::const_optimise_sf3(const details::operator_type& operation,
                                                       expression_node_ptr (&branch)[3])
         {
            expression_node_ptr temp_node = error_node();

            switch (operation)
            {
               #define case_stmt(op)                                                                                                      \
               case details::e_sf##op : temp_node = node_allocator_->template allocate<details::sf3_node<T,details::sf##op##_op<T> > >   \
                                (operation, branch);                                                                                      \
                             break;

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

            return node_allocator_->template allocate<literal_node_t>(v);
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::varnode_optimise_sf3(const details::operator_type& operation, expression_node_ptr (&branch)[3])
         {
            typedef details::variable_node<T>* variable_ptr;

            const T& v0 = static_cast<variable_ptr>(branch[0])->ref();
            const T& v1 = static_cast<variable_ptr>(branch[1])->ref();
            const T& v2 = static_cast<variable_ptr>(branch[2])->ref();

            switch (operation)
            {
               #define case_stmt(op)                                                                \
               case details::e_sf##op : return node_allocator_->template allocate_rrr<details::sf3_var_node<T,details::sf##op##_op<T> > > \
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

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::special_function(const details::operator_type& operation, expression_node_ptr (&branch)[3])
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
                  case details::e_sf##op : return node_allocator_->template allocate<details::sf3_node<T,details::sf##op##_op<T> > >(operation, branch);

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

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::const_optimise_sf4(const details::operator_type& operation, expression_node_ptr (&branch)[4])
         {
            expression_node_ptr temp_node = error_node();

            switch (operation)
            {
               #define case_stmt(op)                                                                                                      \
               case details::e_sf##op : temp_node = node_allocator_-> template allocate<details::sf4_node<T,details::sf##op##_op<T> > >  \
                                            (operation, branch);                                                                          \
                                        break;

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

            return node_allocator_->template allocate<literal_node_t>(v);
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::varnode_optimise_sf4(const details::operator_type& operation, expression_node_ptr (&branch)[4])
         {
            typedef details::variable_node<T>* variable_ptr;

            const T& v0 = static_cast<variable_ptr>(branch[0])->ref();
            const T& v1 = static_cast<variable_ptr>(branch[1])->ref();
            const T& v2 = static_cast<variable_ptr>(branch[2])->ref();
            const T& v3 = static_cast<variable_ptr>(branch[3])->ref();

            switch (operation)
            {
               #define case_stmt(op)                                                                 \
               case details::e_sf##op : return node_allocator_->template allocate_rrrr<details::sf4_var_node<T,details::sf##op##_op<T> > > (v0, v1, v2, v3);

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

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::special_function(const details::operator_type& operation, expression_node_ptr (&branch)[4])
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
               case details::e_sf##op : return node_allocator_->template allocate<details::sf4_node<T,details::sf##op##_op<T> > > (operation, branch);

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

         template<typename T> bool expression_generator<T>::special_one_parameter_vararg(const details::operator_type& operation) const
         {
            return (
                     (details::e_sum  == operation) ||
                     (details::e_prod == operation) ||
                     (details::e_avg  == operation) ||
                     (details::e_min  == operation) ||
                     (details::e_max  == operation)
                   );
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::function(ifunction_t* f)
         {
            typedef typename details::function_N_node<T,ifunction_t,0> function_N_node_t;
            return node_allocator_->template allocate<function_N_node_t>(f);
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::vararg_function_call(ivararg_function_t* vaf,
                                                         std::vector<expression_node_ptr>& arg_list)
         {
            if (!all_nodes_valid(arg_list))
            {
               details::free_all_nodes(*node_allocator_,arg_list);

               return error_node();
            }

            typedef details::vararg_function_node<T,ivararg_function_t> alloc_type;

            expression_node_ptr result = node_allocator_->template allocate<alloc_type>(vaf,arg_list);

            if (
                 !arg_list.empty()        &&
                 !vaf->has_side_effects() &&
                 is_constant_foldable(arg_list)
               )
            {
               const T v = result->value();
               details::free_node(*node_allocator_,result);
               result = node_allocator_->template allocate<literal_node_t>(v);
            }

            parser_->state_.activate_side_effect("vararg_function_call()");

            return result;
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::generic_function_call(igeneric_function_t* gf,
                                                          std::vector<expression_node_ptr>& arg_list,
                                                          const std::size_t& param_seq_index)
         {
            if (!all_nodes_valid(arg_list))
            {
               details::free_all_nodes(*node_allocator_,arg_list);
               return error_node();
            }

            typedef details::generic_function_node     <T,igeneric_function_t> alloc_type1;
            typedef details::multimode_genfunction_node<T,igeneric_function_t> alloc_type2;

            const std::size_t no_psi = std::numeric_limits<std::size_t>::max();

            expression_node_ptr result = error_node();

            if (no_psi == param_seq_index)
               result = node_allocator_->template allocate<alloc_type1>(arg_list,gf);
            else
               result = node_allocator_->template allocate<alloc_type2>(gf, param_seq_index, arg_list);

            alloc_type1* genfunc_node_ptr = static_cast<alloc_type1*>(result);

            if (
                 !arg_list.empty()                  &&
                 !gf->has_side_effects()            &&
                 parser_->state_.type_check_enabled &&
                 is_constant_foldable(arg_list)
               )
            {
               genfunc_node_ptr->init_branches();

               const T v = result->value();

               details::free_node(*node_allocator_,result);

               return node_allocator_->template allocate<literal_node_t>(v);
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

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::string_function_call(igeneric_function_t* gf,
                                                         std::vector<expression_node_ptr>& arg_list,
                                                         const std::size_t& param_seq_index)
         {
            if (!all_nodes_valid(arg_list))
            {
               details::free_all_nodes(*node_allocator_,arg_list);
               return error_node();
            }

            typedef details::string_function_node      <T,igeneric_function_t> alloc_type1;
            typedef details::multimode_strfunction_node<T,igeneric_function_t> alloc_type2;

            const std::size_t no_psi = std::numeric_limits<std::size_t>::max();

            expression_node_ptr result = error_node();

            if (no_psi == param_seq_index)
               result = node_allocator_->template allocate<alloc_type1>(gf,arg_list);
            else
               result = node_allocator_->template allocate<alloc_type2>(gf, param_seq_index, arg_list);

            alloc_type1* strfunc_node_ptr = static_cast<alloc_type1*>(result);

            if (
                 !arg_list.empty()       &&
                 !gf->has_side_effects() &&
                 is_constant_foldable(arg_list)
               )
            {
               strfunc_node_ptr->init_branches();

               const T v = result->value();

               details::free_node(*node_allocator_,result);

               return node_allocator_->template allocate<literal_node_t>(v);
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

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::return_call(std::vector<expression_node_ptr>& arg_list)
         {
            if(details::disable_enhanced_features){
               return error_node();
            }

            if (!all_nodes_valid(arg_list))
            {
               details::free_all_nodes(*node_allocator_,arg_list);
               return error_node();
            }

            typedef details::return_node<T> alloc_type;

            expression_node_ptr result = node_allocator_->template allocate_rr<alloc_type>(arg_list,parser_->results_ctx());

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

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::return_envelope(expression_node_ptr body,
                                                    results_context_t* rc,
                                                    bool*& return_invoked)
         {
            if(details::disable_enhanced_features){
               return error_node();
            }

            typedef details::return_envelope_node<T> alloc_type;

            expression_node_ptr result = node_allocator_->template allocate_cr<alloc_type>(body,(*rc));

            return_invoked = static_cast<alloc_type*>(result)->retinvk_ptr();

            return result;
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::vector_element(const std::string& symbol,
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
                  return node_allocator_->template allocate<rebasevector_celem_node_t>(i,vector_base);
               }

               const typename ::Essa::Math::parser<T>::scope_element& se = parser_->sem_.get_element(symbol,i);

               if (se.index == i)
               {
                  result = se.var_node;
               }
               else
               {
                  typename ::Essa::Math::parser<T>::scope_element nse;
                  nse.name      = symbol;
                  nse.active    = true;
                  nse.ref_count = 1;
                  nse.type      = ::Essa::Math::parser<T>::scope_element::e_vecelem;
                  nse.index     = i;
                  nse.depth     = parser_->state_.scope_depth;
                  nse.data      = 0;
                  nse.var_node  = node_allocator_->template allocate<variable_node_t>((*(*vector_base)[i]), nse.name);

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
               result = node_allocator_->template allocate<rebasevector_elem_node_t>(index,vector_base);
            else
               result = node_allocator_->template allocate<vector_elem_node_t>(index,vector_base);

            return result;
         }

         template<typename T> void expression_generator<T>::lodge_assignment(symbol_type cst, expression_node_ptr node)
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

               case e_st_string   : 
                  if(!details::disable_string_capabilities)
                     symbol_name = parser_->symtab_store_.get_stringvar_name(node);
                                    break;
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
               parser_->dec_.add_assignment(symbol_name,static_cast<::Essa::Math::parser<T>::symbol_type>(cst));
            }
         }

         template<typename T> const void* expression_generator<T>::base_ptr(expression_node_ptr node)
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

                  case details::expression_node<T>::e_stringvar:
                     if(!details::disable_string_capabilities)
                        return reinterpret_cast<const void*>((static_cast<stringvar_node_t*>(node)->base()));
                  case details::expression_node<T>::e_stringvarrng:
                     if(!details::disable_string_capabilities)
                        return reinterpret_cast<const void*>((static_cast<string_range_node_t*>(node)->base()));
                  default : return reinterpret_cast<const void*>(0);
               }
            }

            return reinterpret_cast<const void*>(0);
         }

         template<typename T> bool expression_generator<T>::assign_immutable_symbol(expression_node_ptr node)
         {
            typename ::Essa::Math::parser<T>::interval_t interval;
            const void* baseptr_addr = base_ptr(node);

            exprtk_debug(("assign_immutable_symbol - base ptr addr: %p\n", baseptr_addr));

            if (parser_->immutable_memory_map_.in_interval(baseptr_addr,interval))
            {
               typename ::Essa::Math::parser<T>::immutable_symtok_map_t::iterator itr = parser_->immutable_symtok_map_.find(interval);

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

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::synthesize_assignment_expression(const details::operator_type& operation, expression_node_ptr (&branch)[2])
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
            else if (details::is_string_node(branch[0]) && !details::disable_string_capabilities)
            {
               lodge_assignment(e_st_string,branch[0]);
               return synthesize_expression<assignment_string_node_t,2>(operation, branch);
            }
            else if (details::is_string_range_node(branch[0]) && !details::disable_string_capabilities)
            {
               lodge_assignment(e_st_string,branch[0]);
               return synthesize_expression<assignment_string_range_node_t,2>(operation, branch);
            }
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

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::synthesize_assignment_operation_expression(const details::operator_type& operation,
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
                                template allocate_rrr<typename details::assignment_op_node<T,op1<T> > > \
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
                                 template allocate_rrr<typename details::assignment_vec_elem_op_node<T,op1<T> > > \
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
                                 template allocate_rrr<typename details::assignment_rebasevec_elem_op_node<T,op1<T> > > \
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
                                 template allocate_rrr<typename details::assignment_rebasevec_celem_op_node<T,op1<T> > > \
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
                                   template allocate_rrr<typename details::assignment_vecvec_op_node<T,op1<T> > > \
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
                                   template allocate_rrr<typename details::assignment_vec_op_node<T,op1<T> > > \
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
            else if (
                      (details::e_addass == operation) &&
                      details::is_string_node(branch[0]) &&
                      !details::disable_string_capabilities
                    )
            {
               typedef details::assignment_string_node<T,details::asn_addassignment> addass_t;

               lodge_assignment(e_st_string,branch[0]);

               return synthesize_expression<addass_t,2>(operation,branch);
            }
            else
            {
               parser_->set_synthesis_error("Invalid assignment operation[2]");

               return error_node();
            }
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::synthesize_veceqineqlogic_operation_expression(const details::operator_type& operation,
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
                                template allocate_rrr<typename details::vec_binop_vecvec_node<T,op1<T> > > \
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
                                template allocate_rrr<typename details::vec_binop_vecval_node<T,op1<T> > > \
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
                                template allocate_rrr<typename details::vec_binop_valvec_node<T,op1<T> > > \
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

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::synthesize_vecarithmetic_operation_expression(const details::operator_type& operation,
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
                                template allocate_rrr<typename details::vec_binop_vecvec_node<T,op1<T> > > \
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
                                template allocate_rrr<typename details::vec_binop_vecval_node<T,op1<T> > > \
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
                                template allocate_rrr<typename details::vec_binop_valvec_node<T,op1<T> > > \
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

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::synthesize_swap_expression(expression_node_ptr (&branch)[2])
         {
            const bool v0_is_ivar = details::is_ivariable_node(branch[0]);
            const bool v1_is_ivar = details::is_ivariable_node(branch[1]);

            const bool v0_is_ivec = details::is_ivector_node  (branch[0]);
            const bool v1_is_ivec = details::is_ivector_node  (branch[1]);

            const bool v0_is_str = details::is_generally_string_node(branch[0]);
            const bool v1_is_str = details::is_generally_string_node(branch[1]);

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
                  result = node_allocator_->template allocate<details::swap_node<T> >(v0,v1);
               }
               else
                  result = node_allocator_->template allocate<details::swap_generic_node<T> >(branch[0],branch[1]);
            }
            else if (v0_is_ivec && v1_is_ivec)
            {
               result = node_allocator_->template allocate<details::swap_vecvec_node<T> >(branch[0],branch[1]);
            }
            else if (v0_is_str && v1_is_str && !details::disable_string_capabilities)
            {
               if (is_string_node(branch[0]) && is_string_node(branch[1]))
                  result = node_allocator_->template allocate<details::swap_string_node<T> >
                                               (branch[0], branch[1]);
               else
                  result = node_allocator_->template allocate<details::swap_genstrings_node<T> >
                                               (branch[0], branch[1]);
            }
            else
            {
               parser_->set_synthesis_error("Only variables, strings, vectors or vector elements can be swapped");

               return error_node();
            }

            parser_->state_.activate_side_effect("synthesize_swap_expression()");

            return result;
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::synthesize_shortcircuit_expression(const details::operator_type& operation, expression_node_ptr (&branch)[2])
         {
            if(details::disable_sc_andor)
               return error_node();
            expression_node_ptr result = error_node();

            if (details::is_constant_node(branch[0]))
            {
               if (
                    (details::e_scand == operation) &&
                    std::equal_to<T>()(T(0),branch[0]->value())
                  )
                  result = node_allocator_->template allocate_c<literal_node_t>(T(0));
               else if (
                         (details::e_scor == operation) &&
                         std::not_equal_to<T>()(T(0),branch[0]->value())
                       )
                  result = node_allocator_->template allocate_c<literal_node_t>(T(1));
            }

            if (details::is_constant_node(branch[1]) && (0 == result))
            {
               if (
                    (details::e_scand == operation) &&
                    std::equal_to<T>()(T(0),branch[1]->value())
                  )
                  result = node_allocator_->template allocate_c<literal_node_t>(T(0));
               else if (
                         (details::e_scor == operation) &&
                         std::not_equal_to<T>()(T(0),branch[1]->value())
                       )
                  result = node_allocator_->template allocate_c<literal_node_t>(T(1));
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

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::cardinal_pow_optimisation(const T& v, const T& c)
         {
            if(details::disable_cardinal_pow_optimisation)
               return error_node();
            const bool not_recipricol = details::is_true(details::numeric::geq<T>(c, T(0)));
            const unsigned int p = static_cast<unsigned int>(details::numeric::to_int32(details::numeric::abs(c)));

            if (0 == p)
               return node_allocator_->template allocate_c<literal_node_t>(T(1));
            else if (std::equal_to<T>()(T(2),c))
            {
               return node_allocator_->
                  template allocate_rr<typename details::vov_node<T,details::mul_op<T> > >(v,v);
            }
            else
            {
               if (not_recipricol)
                  return cardinal_pow_optimisation_impl<T,details::ipow_node>(v,p);
               else
                  return cardinal_pow_optimisation_impl<T,details::ipowinv_node>(v,p);
            }
         }

         template<typename T> bool expression_generator<T>::cardinal_pow_optimisable(const details::operator_type& operation, const T& c) const
         {
            if(details::disable_cardinal_pow_optimisation)
               return false;
            return (details::e_pow == operation) && (details::is_true(details::numeric::leq<T>(details::numeric::abs(c), T(60)))) && details::numeric::is_integer(c);
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::cardinal_pow_optimisation(expression_node_ptr (&branch)[2])
         {
            if(details::disable_cardinal_pow_optimisation)
               return error_node();
            const T c = static_cast<details::literal_node<T>*>(branch[1])->value();
            const bool not_recipricol = details::is_true(details::numeric::geq<T>(c, T(0)));
            const unsigned int p = static_cast<unsigned int>(details::numeric::to_int32(details::numeric::abs(c)));

            node_allocator_->free(branch[1]);

            if (0 == p)
            {
               details::free_all_nodes(*node_allocator_, branch);

               return node_allocator_->template allocate_c<literal_node_t>(T(1));
            }
            else if (not_recipricol)
               return cardinal_pow_optimisation_impl<expression_node_ptr,details::bipow_node>(branch[0],p);
            else
               return cardinal_pow_optimisation_impl<expression_node_ptr,details::bipowninv_node>(branch[0],p);
         }

         template<typename T> bool expression_generator<T>::synthesize_expression(const details::operator_type& operation,
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

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::synthesize_uvouv_expression(const details::operator_type& operation, expression_node_ptr (&branch)[2])
         {
            // Definition: uv o uv
            details::operator_type o0 = static_cast<details::uv_base_node<T>*>(branch[0])->operation();
            details::operator_type o1 = static_cast<details::uv_base_node<T>*>(branch[1])->operation();
            const T& v0 = static_cast<details::uv_base_node<T>*>(branch[0])->v();
            const T& v1 = static_cast<details::uv_base_node<T>*>(branch[1])->v();
            unary_functor_t u0 = reinterpret_cast<unary_functor_t> (0);
            unary_functor_t u1 = reinterpret_cast<unary_functor_t> (0);
            typename expression_generator<T>::binary_functor_t f = reinterpret_cast<expression_generator<T>::binary_functor_t>(0);

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
                                                       template allocate_rr<typename details::
                                                          vov_node<T,details::add_op<T> > >(v0, v1));
                                        exprtk_debug(("(-v0 + -v1) --> -(v0 + v1)\n"));
                                        break;

                  // (-v0 - -v1) --> (v1 - v0)
                  case details::e_sub : result = node_allocator_->
                                                    template allocate_rr<typename details::
                                                       vov_node<T,details::sub_op<T> > >(v1, v0);
                                        exprtk_debug(("(-v0 - -v1) --> (v1 - v0)\n"));
                                        break;

                  // (-v0 * -v1) --> (v0 * v1)
                  case details::e_mul : result = node_allocator_->
                                                    template allocate_rr<typename details::
                                                       vov_node<T,details::mul_op<T> > >(v0, v1);
                                        exprtk_debug(("(-v0 * -v1) --> (v0 * v1)\n"));
                                        break;

                  // (-v0 / -v1) --> (v0 / v1)
                  case details::e_div : result = node_allocator_->
                                                    template allocate_rr<typename details::
                                                       vov_node<T,details::div_op<T> > >(v0, v1);
                                        exprtk_debug(("(-v0 / -v1) --> (v0 / v1)\n"));
                                        break;

                  default             : break;
               }
            }

            if (0 == result)
            {
               result = node_allocator_->template allocate_rrrrr<typename details::uvouv_node<T> >(v0, v1, u0, u1, f);
            }

            details::free_all_nodes(*node_allocator_,branch);
            return result;
         }

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
         case_stmt(details::e_ilike , details::ilike_op)

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::synthesize_sos_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2])
         {
            std::string& s0 = static_cast<details::stringvar_node<T>*>(branch[0])->ref();
            std::string& s1 = static_cast<details::stringvar_node<T>*>(branch[1])->ref();

            return synthesize_sos_expression_impl<std::string&,std::string&>(opr, s0, s1);
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::synthesize_sros_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2])
         {
            std::string&  s0 = static_cast<details::string_range_node<T>*>(branch[0])->ref  ();
            std::string&  s1 = static_cast<details::stringvar_node<T>*>   (branch[1])->ref  ();
            range_t      rp0 = static_cast<details::string_range_node<T>*>(branch[0])->range();

            static_cast<details::string_range_node<T>*>(branch[0])->range_ref().clear();

            details::free_node(*node_allocator_,branch[0]);

            return synthesize_str_xrox_expression_impl<std::string&,std::string&>(opr, s0, s1, rp0);
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::synthesize_sosr_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2])
         {
            std::string&  s0 = static_cast<details::stringvar_node<T>*>   (branch[0])->ref  ();
            std::string&  s1 = static_cast<details::string_range_node<T>*>(branch[1])->ref  ();
            range_t      rp1 = static_cast<details::string_range_node<T>*>(branch[1])->range();

            static_cast<details::string_range_node<T>*>(branch[1])->range_ref().clear();

            details::free_node(*node_allocator_,branch[1]);

            return synthesize_str_xoxr_expression_impl<std::string&,std::string&>(opr, s0, s1, rp1);
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::synthesize_socsr_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2])
         {
            std::string&  s0 = static_cast<details::stringvar_node<T>*>         (branch[0])->ref  ();
            std::string   s1 = static_cast<details::const_string_range_node<T>*>(branch[1])->str  ();
            range_t      rp1 = static_cast<details::const_string_range_node<T>*>(branch[1])->range();

            static_cast<details::const_string_range_node<T>*>(branch[1])->range_ref().clear();

            details::free_node(*node_allocator_,branch[1]);

            return synthesize_str_xoxr_expression_impl<std::string&, const std::string>(opr, s0, s1, rp1);
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::synthesize_srosr_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2])
         {
            std::string&  s0 = static_cast<details::string_range_node<T>*>(branch[0])->ref  ();
            std::string&  s1 = static_cast<details::string_range_node<T>*>(branch[1])->ref  ();
            range_t      rp0 = static_cast<details::string_range_node<T>*>(branch[0])->range();
            range_t      rp1 = static_cast<details::string_range_node<T>*>(branch[1])->range();

            static_cast<details::string_range_node<T>*>(branch[0])->range_ref().clear();
            static_cast<details::string_range_node<T>*>(branch[1])->range_ref().clear();

            details::free_node(*node_allocator_,branch[0]);
            details::free_node(*node_allocator_,branch[1]);

            return synthesize_str_xroxr_expression_impl<std::string&,std::string&>(opr, s0, s1, rp0, rp1);
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::synthesize_socs_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2])
         {
            std::string& s0 = static_cast<     details::stringvar_node<T>*>(branch[0])->ref();
            std::string  s1 = static_cast<details::string_literal_node<T>*>(branch[1])->str();

            details::free_node(*node_allocator_,branch[1]);

            return synthesize_sos_expression_impl<std::string&, const std::string>(opr, s0, s1);
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::synthesize_csos_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2])
         {
            std::string  s0 = static_cast<details::string_literal_node<T>*>(branch[0])->str();
            std::string& s1 = static_cast<details::stringvar_node<T>*     >(branch[1])->ref();

            details::free_node(*node_allocator_,branch[0]);

            return synthesize_sos_expression_impl<const std::string,std::string&>(opr, s0, s1);
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::synthesize_csosr_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2])
         {
            std::string  s0  = static_cast<details::string_literal_node<T>*>(branch[0])->str  ();
            std::string& s1  = static_cast<details::string_range_node<T>*  >(branch[1])->ref  ();
            range_t      rp1 = static_cast<details::string_range_node<T>*  >(branch[1])->range();

            static_cast<details::string_range_node<T>*>(branch[1])->range_ref().clear();

            details::free_node(*node_allocator_,branch[0]);
            details::free_node(*node_allocator_,branch[1]);

            return synthesize_str_xoxr_expression_impl<const std::string,std::string&>(opr, s0, s1, rp1);
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::synthesize_srocs_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2])
         {
            std::string&  s0 = static_cast<details::string_range_node<T>*  >(branch[0])->ref  ();
            std::string   s1 = static_cast<details::string_literal_node<T>*>(branch[1])->str  ();
            range_t      rp0 = static_cast<details::string_range_node<T>*  >(branch[0])->range();

            static_cast<details::string_range_node<T>*>(branch[0])->range_ref().clear();

            details::free_node(*node_allocator_,branch[0]);
            details::free_node(*node_allocator_,branch[1]);

            return synthesize_str_xrox_expression_impl<std::string&, const std::string>(opr, s0, s1, rp0);
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::synthesize_srocsr_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2])
         {
            std::string&  s0 = static_cast<details::string_range_node<T>*      >(branch[0])->ref  ();
            std::string   s1 = static_cast<details::const_string_range_node<T>*>(branch[1])->str  ();
            range_t      rp0 = static_cast<details::string_range_node<T>*      >(branch[0])->range();
            range_t      rp1 = static_cast<details::const_string_range_node<T>*>(branch[1])->range();

            static_cast<details::string_range_node<T>*>      (branch[0])->range_ref().clear();
            static_cast<details::const_string_range_node<T>*>(branch[1])->range_ref().clear();

            details::free_node(*node_allocator_,branch[0]);
            details::free_node(*node_allocator_,branch[1]);

            return synthesize_str_xroxr_expression_impl<std::string&, const std::string>(opr, s0, s1, rp0, rp1);
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::synthesize_csocs_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2])
         {
            const std::string s0 = static_cast<details::string_literal_node<T>*>(branch[0])->str();
            const std::string s1 = static_cast<details::string_literal_node<T>*>(branch[1])->str();

            expression_node_ptr result = error_node();

            if (details::e_add == opr)
               result = node_allocator_->template allocate_c<details::string_literal_node<T> >(s0 + s1);
            else if (details::e_in == opr)
               result = node_allocator_->template allocate_c<details::literal_node<T> >(details::in_op   <T>::process(s0,s1));
            else if (details::e_like == opr)
               result = node_allocator_->template allocate_c<details::literal_node<T> >(details::like_op <T>::process(s0,s1));
            else if (details::e_ilike == opr)
               result = node_allocator_->template allocate_c<details::literal_node<T> >(details::ilike_op<T>::process(s0,s1));
            else
            {
               expression_node_ptr temp = synthesize_sos_expression_impl<const std::string, const std::string>(opr, s0, s1);

               const T v = temp->value();

               details::free_node(*node_allocator_,temp);

               result = node_allocator_->template allocate<literal_node_t>(v);
            }

            details::free_all_nodes(*node_allocator_,branch);

            return result;
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::synthesize_csocsr_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2])
         {
            const std::string s0 = static_cast<details::string_literal_node<T>*    >(branch[0])->str  ();
                  std::string s1 = static_cast<details::const_string_range_node<T>*>(branch[1])->str  ();
            range_t          rp1 = static_cast<details::const_string_range_node<T>*>(branch[1])->range();

            static_cast<details::const_string_range_node<T>*>(branch[1])->range_ref().clear();

            details::free_node(*node_allocator_,branch[0]);
            details::free_node(*node_allocator_,branch[1]);

            return synthesize_str_xoxr_expression_impl<const std::string, const std::string>(opr, s0, s1, rp1);
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::synthesize_csros_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2])
         {
            std::string   s0 = static_cast<details::const_string_range_node<T>*>(branch[0])->str  ();
            std::string&  s1 = static_cast<details::stringvar_node<T>*         >(branch[1])->ref  ();
            range_t      rp0 = static_cast<details::const_string_range_node<T>*>(branch[0])->range();

            static_cast<details::const_string_range_node<T>*>(branch[0])->range_ref().clear();

            details::free_node(*node_allocator_,branch[0]);

            return synthesize_str_xrox_expression_impl<const std::string,std::string&>(opr, s0, s1, rp0);
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::synthesize_csrosr_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2])
         {
            const std::string  s0 = static_cast<details::const_string_range_node<T>*>(branch[0])->str  ();
                  std::string& s1 = static_cast<details::string_range_node<T>*      >(branch[1])->ref  ();
            const range_t     rp0 = static_cast<details::const_string_range_node<T>*>(branch[0])->range();
            const range_t     rp1 = static_cast<details::string_range_node<T>*      >(branch[1])->range();

            static_cast<details::const_string_range_node<T>*>(branch[0])->range_ref().clear();
            static_cast<details::string_range_node<T>*>      (branch[1])->range_ref().clear();

            details::free_node(*node_allocator_,branch[0]);
            details::free_node(*node_allocator_,branch[1]);

            return synthesize_str_xroxr_expression_impl<const std::string,std::string&>(opr, s0, s1, rp0, rp1);
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::synthesize_csrocs_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2])
         {
            const std::string s0 = static_cast<details::const_string_range_node<T>*>(branch[0])->str  ();
            const std::string s1 = static_cast<details::string_literal_node<T>*    >(branch[1])->str  ();
            const range_t    rp0 = static_cast<details::const_string_range_node<T>*>(branch[0])->range();

            static_cast<details::const_string_range_node<T>*>(branch[0])->range_ref().clear();

            details::free_all_nodes(*node_allocator_,branch);

            return synthesize_str_xrox_expression_impl<const std::string,std::string>(opr, s0, s1, rp0);
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::synthesize_csrocsr_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2])
         {
            const std::string s0 = static_cast<details::const_string_range_node<T>*>(branch[0])->str  ();
            const std::string s1 = static_cast<details::const_string_range_node<T>*>(branch[1])->str  ();
            const range_t    rp0 = static_cast<details::const_string_range_node<T>*>(branch[0])->range();
            const range_t    rp1 = static_cast<details::const_string_range_node<T>*>(branch[1])->range();

            static_cast<details::const_string_range_node<T>*>(branch[0])->range_ref().clear();
            static_cast<details::const_string_range_node<T>*>(branch[1])->range_ref().clear();

            details::free_all_nodes(*node_allocator_,branch);

            return synthesize_str_xroxr_expression_impl<const std::string, const std::string>(opr, s0, s1, rp0, rp1);
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::synthesize_strogen_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2])
         {
            switch (opr)
            {
               #define case_stmt(op0, op1)                                                      \
               case op0 : return node_allocator_->template allocate_ttt<typename details::str_sogens_node<T,op1<T> > >  \
                                (opr, branch[0], branch[1]);                                    \

               string_opr_switch_statements
               #undef case_stmt
               default : return error_node();
            }
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::synthesize_string_expression(const details::operator_type& opr, expression_node_ptr (&branch)[2])
         {
            if(details::disable_string_capabilities){
               details::free_all_nodes(*node_allocator_,branch);
               return error_node();
            }

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

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::synthesize_string_expression(const details::operator_type& opr, expression_node_ptr (&branch)[3])
         {
            if(details::disable_string_capabilities){
               details::free_all_nodes(*node_allocator_,branch);
               return error_node();
            }

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
               const std::string s0 = static_cast<details::string_literal_node<T>*>(branch[0])->str();
               const std::string s1 = static_cast<details::string_literal_node<T>*>(branch[1])->str();
               const std::string s2 = static_cast<details::string_literal_node<T>*>(branch[2])->str();

               const T v = (((s0 <= s1) && (s1 <= s2)) ? T(1) : T(0));

               details::free_all_nodes(*node_allocator_,branch);

               return node_allocator_->allocate_c<details::literal_node<T> >(v);
            }
            else if (
                      details::is_string_node(branch[0]) &&
                      details::is_string_node(branch[1]) &&
                      details::is_string_node(branch[2])
                    )
            {
               std::string& s0 = static_cast<details::stringvar_node<T>*>(branch[0])->ref();
               std::string& s1 = static_cast<details::stringvar_node<T>*>(branch[1])->ref();
               std::string& s2 = static_cast<details::stringvar_node<T>*>(branch[2])->ref();

               typedef typename details::sosos_node<T, std::string&, std::string&, std::string&, details::inrange_op<T> > inrange_t;

               return node_allocator_->allocate_type<inrange_t, std::string&, std::string&, std::string&>(s0, s1, s2);
            }
            else if (
                      details::is_const_string_node(branch[0]) &&
                            details::is_string_node(branch[1]) &&
                      details::is_const_string_node(branch[2])
                    )
            {
               std::string  s0 = static_cast<details::string_literal_node<T>*>(branch[0])->str();
               std::string& s1 = static_cast<details::stringvar_node<T>*     >(branch[1])->ref();
               std::string  s2 = static_cast<details::string_literal_node<T>*>(branch[2])->str();

               typedef typename details::sosos_node<T, std::string, std::string&, std::string, details::inrange_op<T> > inrange_t;

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
               std::string&  s0 = static_cast<details::stringvar_node<T>*     >(branch[0])->ref();
               std::string   s1 = static_cast<details::string_literal_node<T>*>(branch[1])->str();
               std::string&  s2 = static_cast<details::stringvar_node<T>*     >(branch[2])->ref();

               typedef typename details::sosos_node<T, std::string&, std::string, std::string&, details::inrange_op<T> > inrange_t;

               details::free_node(*node_allocator_,branch[1]);

               return node_allocator_->allocate_type<inrange_t, std::string&, std::string, std::string&>(s0, s1, s2);
            }
            else if (
                      details::is_string_node(branch[0]) &&
                      details::is_string_node(branch[1]) &&
                      details::is_const_string_node(branch[2])
                    )
            {
               std::string& s0 = static_cast<details::stringvar_node<T>*     >(branch[0])->ref();
               std::string& s1 = static_cast<details::stringvar_node<T>*     >(branch[1])->ref();
               std::string  s2 = static_cast<details::string_literal_node<T>*>(branch[2])->str();

               typedef typename details::sosos_node<T, std::string&, std::string&, std::string, details::inrange_op<T> > inrange_t;

               details::free_node(*node_allocator_,branch[2]);

               return node_allocator_->allocate_type<inrange_t, std::string&, std::string&, std::string>(s0, s1, s2);
            }
            else if (
                      details::is_const_string_node(branch[0]) &&
                      details::      is_string_node(branch[1]) &&
                      details::      is_string_node(branch[2])
                    )
            {
               std::string  s0 = static_cast<details::string_literal_node<T>*>(branch[0])->str();
               std::string& s1 = static_cast<details::stringvar_node<T>*     >(branch[1])->ref();
               std::string& s2 = static_cast<details::stringvar_node<T>*     >(branch[2])->ref();

               typedef typename details::sosos_node<T, std::string, std::string&, std::string&, details::inrange_op<T> > inrange_t;

               details::free_node(*node_allocator_,branch[0]);

               return node_allocator_->allocate_type<inrange_t, std::string, std::string&, std::string&>(s0, s1, s2);
            }
            else
               return error_node();
         }

         template<typename T> expression_generator<T>::expression_node_ptr expression_generator<T>::synthesize_null_expression(const details::operator_type& operation, expression_node_ptr (&branch)[2])
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

            return node_allocator_->template allocate<details::null_node<T> >();
         }

         template class expression_generator<int16_t>;
         template class expression_generator<int32_t>;
         template class expression_generator<int64_t>;
         template class expression_generator<float>;
         template class expression_generator<double>;
         template class expression_generator<long double>;
         template class expression_generator<std::complex<float>>;
         template class expression_generator<std::complex<double>>;
         template class expression_generator<std::complex<long double>>;
}

#pragma once
#include "Defines.hpp"

namespace Essa::Math{
   namespace details{
         namespace numeric{
            namespace details{
            template <typename T>
            inline bool is_nan_impl(const T v, real_type_tag)
            {
               return std::not_equal_to<T>()(v,v);
            }

            template <typename T>
            inline int to_int32_impl(const T v, real_type_tag)
            {
               return static_cast<int>(v);
            }

            template <typename T>
            inline _int64_t to_int64_impl(const T v, real_type_tag)
            {
               return static_cast<_int64_t>(v);
            }

            template <typename T>
            inline bool is_true_impl(const T v)
            {
               return std::not_equal_to<T>()(T(0),v);
            }

            template <typename T>
            inline bool is_false_impl(const T v)
            {
               return std::equal_to<T>()(T(0),v);
            }

            template <typename T>
            inline T abs_impl(const T v, real_type_tag)
            {
               return ((v < T(0)) ? -v : v);
            }

            template <typename T>
            inline T min_impl(const T v0, const T v1, real_type_tag)
            {
               return std::min<T>(v0,v1);
            }

            template <typename T>
            inline T max_impl(const T v0, const T v1, real_type_tag)
            {
               return std::max<T>(v0,v1);
            }

            template <typename T>
            inline T equal_impl(const T v0, const T v1, real_type_tag)
            {
               const T epsilon = epsilon_type<T>::value();
               return (abs_impl(v0 - v1,real_type_tag()) <= (std::max(T(1),std::max(abs_impl(v0,real_type_tag()),abs_impl(v1,real_type_tag()))) * epsilon)) ? T(1) : T(0);
            }

            inline float equal_impl(const float v0, const float v1, real_type_tag)
            {
               const float epsilon = epsilon_type<float>::value();
               return (abs_impl(v0 - v1,real_type_tag()) <= (std::max(1.0f,std::max(abs_impl(v0,real_type_tag()),abs_impl(v1,real_type_tag()))) * epsilon)) ? 1.0f : 0.0f;
            }

            template <typename T>
            inline T equal_impl(const T v0, const T v1, int_type_tag)
            {
               return (v0 == v1) ? 1 : 0;
            }

            template <typename T>
            inline T expm1_impl(const T v, real_type_tag)
            {
               // return std::expm1<T>(v);
               if (abs_impl(v,real_type_tag()) < T(0.00001))
                  return v + (T(0.5) * v * v);
               else
                  return std::exp(v) - T(1);
            }

            template <typename T>
            inline T expm1_impl(const T v, int_type_tag)
            {
               return T(std::exp<double>(v)) - T(1);
            }

            template <typename T>
            inline T nequal_impl(const T v0, const T v1, real_type_tag)
            {
               typedef real_type_tag rtg;
               const T epsilon = epsilon_type<T>::value();
               return (abs_impl(v0 - v1,rtg()) > (std::max(T(1),std::max(abs_impl(v0,rtg()),abs_impl(v1,rtg()))) * epsilon)) ? T(1) : T(0);
            }

            inline float nequal_impl(const float v0, const float v1, real_type_tag)
            {
               typedef real_type_tag rtg;
               const float epsilon = epsilon_type<float>::value();
               return (abs_impl(v0 - v1,rtg()) > (std::max(1.0f,std::max(abs_impl(v0,rtg()),abs_impl(v1,rtg()))) * epsilon)) ? 1.0f : 0.0f;
            }

            template <typename T>
            inline T nequal_impl(const T v0, const T v1, int_type_tag)
            {
               return (v0 != v1) ? 1 : 0;
            }

            template <typename T>
            inline T modulus_impl(const T v0, const T v1, real_type_tag)
            {
               return std::fmod(v0,v1);
            }

            template <typename T>
            inline T modulus_impl(const T v0, const T v1, int_type_tag)
            {
               return v0 % v1;
            }

            template <typename T>
            inline T pow_impl(const T v0, const T v1, real_type_tag)
            {
               return std::pow(v0,v1);
            }

            template <typename T>
            inline T pow_impl(const T v0, const T v1, int_type_tag)
            {
               return std::pow(static_cast<double>(v0),static_cast<double>(v1));
            }

            template <typename T>
            inline T logn_impl(const T v0, const T v1, real_type_tag)
            {
               return std::log(v0) / std::log(v1);
            }

            template <typename T>
            inline T logn_impl(const T v0, const T v1, int_type_tag)
            {
               return static_cast<T>(logn_impl<double>(static_cast<double>(v0),static_cast<double>(v1),real_type_tag()));
            }

            template <typename T>
            inline T log1p_impl(const T v, real_type_tag)
            {
               if (v > T(-1))
               {
                  if (abs_impl(v,real_type_tag()) > T(0.0001))
                  {
                     return std::log(T(1) + v);
                  }
                  else
                     return (T(-0.5) * v + T(1)) * v;
               }
               else
                  return std::numeric_limits<T>::quiet_NaN();
            }

            template <typename T>
            inline T log1p_impl(const T v, int_type_tag)
            {
               if (v > T(-1))
               {
                  return std::log(T(1) + v);
               }
               else
                  return std::numeric_limits<T>::quiet_NaN();
            }

            template <typename T>
            inline T root_impl(const T v0, const T v1, real_type_tag)
            {
               if (v1 < T(0))
                  return std::numeric_limits<T>::quiet_NaN();

               const std::size_t n = static_cast<std::size_t>(v1);

               if ((v0 < T(0)) && (0 == (n % 2)))
                  return std::numeric_limits<T>::quiet_NaN();

               return std::pow(v0, T(1) / n);
            }

            template <typename T>
            inline T root_impl(const T v0, const T v1, int_type_tag)
            {
               return root_impl<double>(static_cast<double>(v0),static_cast<double>(v1),real_type_tag());
            }

            template <typename T>
            inline T round_impl(const T v, real_type_tag)
            {
               return ((v < T(0)) ? std::ceil(v - T(0.5)) : std::floor(v + T(0.5)));
            }

            template <typename T>
            inline T roundn_impl(const T v0, const T v1, real_type_tag)
            {
               const int index = std::max<int>(0, std::min<int>(pow10_size - 1, static_cast<int>(std::floor(v1))));
               const T p10 = T(pow10[index]);

               if (v0 < T(0))
                  return T(std::ceil ((v0 * p10) - T(0.5)) / p10);
               else
                  return T(std::floor((v0 * p10) + T(0.5)) / p10);
            }

            template <typename T>
            inline T roundn_impl(const T v0, const T, int_type_tag)
            {
               return v0;
            }

            template <typename T>
            inline T hypot_impl(const T v0, const T v1, real_type_tag)
            {
               return std::sqrt((v0 * v0) + (v1 * v1));
            }

            template <typename T>
            inline T hypot_impl(const T v0, const T v1, int_type_tag)
            {
               return static_cast<T>(std::sqrt(static_cast<double>((v0 * v0) + (v1 * v1))));
            }

            template <typename T>
            inline T atan2_impl(const T v0, const T v1, real_type_tag)
            {
               return std::atan2(v0,v1);
            }

            template <typename T>
            inline T atan2_impl(const T, const T, int_type_tag)
            {
               return 0;
            }

            template <typename T>
            inline T shr_impl(const T v0, const T v1, real_type_tag)
            {
               return v0 * (T(1) / std::pow(T(2),static_cast<T>(static_cast<int>(v1))));
            }

            template <typename T>
            inline T shr_impl(const T v0, const T v1, int_type_tag)
            {
               return v0 >> v1;
            }

            template <typename T>
            inline T shl_impl(const T v0, const T v1, real_type_tag)
            {
               return v0 * std::pow(T(2),static_cast<T>(static_cast<int>(v1)));
            }

            template <typename T>
            inline T shl_impl(const T v0, const T v1, int_type_tag)
            {
               return v0 << v1;
            }

            template <typename T>
            inline T sgn_impl(const T v, real_type_tag)
            {
               if      (v > T(0)) return T(+1);
               else if (v < T(0)) return T(-1);
               else               return T( 0);
            }

            template <typename T>
            inline T sgn_impl(const T v, int_type_tag)
            {
               if      (v > T(0)) return T(+1);
               else if (v < T(0)) return T(-1);
               else               return T( 0);
            }

            template <typename T>
            inline T and_impl(const T v0, const T v1, real_type_tag)
            {
               return (is_true_impl(v0) && is_true_impl(v1)) ? T(1) : T(0);
            }

            template <typename T>
            inline T and_impl(const T v0, const T v1, int_type_tag)
            {
               return v0 && v1;
            }

            template <typename T>
            inline T nand_impl(const T v0, const T v1, real_type_tag)
            {
               return (is_false_impl(v0) || is_false_impl(v1)) ? T(1) : T(0);
            }

            template <typename T>
            inline T nand_impl(const T v0, const T v1, int_type_tag)
            {
               return !(v0 && v1);
            }

            template <typename T>
            inline T or_impl(const T v0, const T v1, real_type_tag)
            {
               return (is_true_impl(v0) || is_true_impl(v1)) ? T(1) : T(0);
            }

            template <typename T>
            inline T or_impl(const T v0, const T v1, int_type_tag)
            {
               return (v0 || v1);
            }

            template <typename T>
            inline T nor_impl(const T v0, const T v1, real_type_tag)
            {
               return (is_false_impl(v0) && is_false_impl(v1)) ? T(1) : T(0);
            }

            template <typename T>
            inline T nor_impl(const T v0, const T v1, int_type_tag)
            {
               return !(v0 || v1);
            }

            template <typename T>
            inline T xor_impl(const T v0, const T v1, real_type_tag)
            {
               return (is_false_impl(v0) != is_false_impl(v1)) ? T(1) : T(0);
            }

            template <typename T>
            inline T xor_impl(const T v0, const T v1, int_type_tag)
            {
               return v0 ^ v1;
            }

            template <typename T>
            inline T xnor_impl(const T v0, const T v1, real_type_tag)
            {
               const bool v0_true = is_true_impl(v0);
               const bool v1_true = is_true_impl(v1);

               if ((v0_true &&  v1_true) || (!v0_true && !v1_true))
                  return T(1);
               else
                  return T(0);
            }

            template <typename T>
            inline T xnor_impl(const T v0, const T v1, int_type_tag)
            {
               const bool v0_true = is_true_impl(v0);
               const bool v1_true = is_true_impl(v1);

               if ((v0_true &&  v1_true) || (!v0_true && !v1_true))
                  return T(1);
               else
                  return T(0);
            }

            #if (defined(_MSC_VER) && (_MSC_VER >= 1900)) || !defined(_MSC_VER)
            #define exprtk_define_erf(TT, impl)                \
            inline TT erf_impl(const TT v) { return impl(v); } \

            exprtk_define_erf(      float,::erff)
            exprtk_define_erf(     double,::erf )
            exprtk_define_erf(long double,::erfl)
            #undef exprtk_define_erf
            #endif

            template <typename T>
            inline T erf_impl(const T v, real_type_tag)
            {
               #if defined(_MSC_VER) && (_MSC_VER < 1900)
               // Credits: Abramowitz & Stegun Equations 7.1.25-28
               static const T c[] = {
                                      T( 1.26551223), T(1.00002368),
                                      T( 0.37409196), T(0.09678418),
                                      T(-0.18628806), T(0.27886807),
                                      T(-1.13520398), T(1.48851587),
                                      T(-0.82215223), T(0.17087277)
                                    };

               const T t = T(1) / (T(1) + T(0.5) * abs_impl(v,real_type_tag()));

               const T result = T(1) - t * std::exp((-v * v) -
                                            c[0] + t * (c[1] + t *
                                           (c[2] + t * (c[3] + t *
                                           (c[4] + t * (c[5] + t *
                                           (c[6] + t * (c[7] + t *
                                           (c[8] + t * (c[9]))))))))));

               return (v >= T(0)) ? result : -result;
               #else
               return erf_impl(v);
               #endif
            }

            template <typename T>
            inline T erf_impl(const T v, int_type_tag)
            {
               return erf_impl(static_cast<double>(v),real_type_tag());
            }

            #if (defined(_MSC_VER) && (_MSC_VER >= 1900)) || !defined(_MSC_VER)
            #define exprtk_define_erfc(TT, impl)                \
            inline TT erfc_impl(const TT v) { return impl(v); } \

            exprtk_define_erfc(float      ,::erfcf)
            exprtk_define_erfc(double     ,::erfc )
            exprtk_define_erfc(long double,::erfcl)
            #undef exprtk_define_erfc
            #endif

            template <typename T>
            inline T erfc_impl(const T v, real_type_tag)
            {
               #if defined(_MSC_VER) && (_MSC_VER < 1900)
               return T(1) - erf_impl(v,real_type_tag());
               #else
               return erfc_impl(v);
               #endif
            }

            template <typename T>
            inline T erfc_impl(const T v, int_type_tag)
            {
               return erfc_impl(static_cast<double>(v),real_type_tag());
            }

            template <typename T>
            inline T ncdf_impl(const T v, real_type_tag)
            {
               const T cnd = T(0.5) * (T(1) +
                             erf_impl(abs_impl(v,real_type_tag()) /
                                      T(numeric::constant::sqrt2),real_type_tag()));
               return  (v < T(0)) ? (T(1) - cnd) : cnd;
            }

            template <typename T>
            inline T ncdf_impl(const T v, int_type_tag)
            {
               return ncdf_impl(static_cast<double>(v),real_type_tag());
            }

            template <typename T>
            inline T sinc_impl(const T v, real_type_tag)
            {
               if (std::abs(v) >= std::numeric_limits<T>::epsilon())
                   return(std::sin(v) / v);
               else
                  return T(1);
            }

            template <typename T>
            inline T sinc_impl(const T v, int_type_tag)
            {
               return sinc_impl(static_cast<double>(v),real_type_tag());
            }

            template <typename T> inline T  acos_impl(const T v, real_type_tag) { return std::acos (v); }
            template <typename T> inline T acosh_impl(const T v, real_type_tag) { return std::log(v + std::sqrt((v * v) - T(1))); }
            template <typename T> inline T  asin_impl(const T v, real_type_tag) { return std::asin (v); }
            template <typename T> inline T asinh_impl(const T v, real_type_tag) { return std::log(v + std::sqrt((v * v) + T(1))); }
            template <typename T> inline T  atan_impl(const T v, real_type_tag) { return std::atan (v); }
            template <typename T> inline T atanh_impl(const T v, real_type_tag) { return (std::log(T(1) + v) - std::log(T(1) - v)) / T(2); }
            template <typename T> inline T  ceil_impl(const T v, real_type_tag) { return std::ceil (v); }
            template <typename T> inline T   cos_impl(const T v, real_type_tag) { return std::cos  (v); }
            template <typename T> inline T  cosh_impl(const T v, real_type_tag) { return std::cosh (v); }
            template <typename T> inline T   exp_impl(const T v, real_type_tag) { return std::exp  (v); }
            template <typename T> inline T floor_impl(const T v, real_type_tag) { return std::floor(v); }
            template <typename T> inline T   log_impl(const T v, real_type_tag) { return std::log  (v); }
            template <typename T> inline T log10_impl(const T v, real_type_tag) { return std::log10(v); }
            template <typename T> inline T  log2_impl(const T v, real_type_tag) { return std::log(v)/T(numeric::constant::log2); }
            template <typename T> inline T   neg_impl(const T v, real_type_tag) { return -v;            }
            template <typename T> inline T   pos_impl(const T v, real_type_tag) { return +v;            }
            template <typename T> inline T   sin_impl(const T v, real_type_tag) { return std::sin  (v); }
            template <typename T> inline T  sinh_impl(const T v, real_type_tag) { return std::sinh (v); }
            template <typename T> inline T  sqrt_impl(const T v, real_type_tag) { return std::sqrt (v); }
            template <typename T> inline T   tan_impl(const T v, real_type_tag) { return std::tan  (v); }
            template <typename T> inline T  tanh_impl(const T v, real_type_tag) { return std::tanh (v); }
            template <typename T> inline T   cot_impl(const T v, real_type_tag) { return T(1) / std::tan(v); }
            template <typename T> inline T   sec_impl(const T v, real_type_tag) { return T(1) / std::cos(v); }
            template <typename T> inline T   csc_impl(const T v, real_type_tag) { return T(1) / std::sin(v); }
            template <typename T> inline T   r2d_impl(const T v, real_type_tag) { return (v * T(numeric::constant::_180_pi)); }
            template <typename T> inline T   d2r_impl(const T v, real_type_tag) { return (v * T(numeric::constant::pi_180));  }
            template <typename T> inline T   d2g_impl(const T v, real_type_tag) { return (v * T(10.0/9.0)); }
            template <typename T> inline T   g2d_impl(const T v, real_type_tag) { return (v * T(9.0/10.0)); }
            template <typename T> inline T  notl_impl(const T v, real_type_tag) { return (std::not_equal_to<T>()(T(0),v) ? T(0) : T(1)); }
            template <typename T> inline T  frac_impl(const T v, real_type_tag) { return (v - static_cast<long long>(v)); }
            template <typename T> inline T trunc_impl(const T v, real_type_tag) { return T(static_cast<long long>(v));    }

            template <typename T> inline T   const_pi_impl(real_type_tag) { return T(numeric::constant::pi);            }
            template <typename T> inline T    const_e_impl(real_type_tag) { return T(numeric::constant::e);             }
            template <typename T> inline T const_qnan_impl(real_type_tag) { return std::numeric_limits<T>::quiet_NaN(); }

            template <typename T> inline T   abs_impl(const T v, int_type_tag) { return ((v >= T(0)) ? v : -v); }
            template <typename T> inline T   exp_impl(const T v, int_type_tag) { return std::exp  (v); }
            template <typename T> inline T   log_impl(const T v, int_type_tag) { return std::log  (v); }
            template <typename T> inline T log10_impl(const T v, int_type_tag) { return std::log10(v); }
            template <typename T> inline T  log2_impl(const T v, int_type_tag) { return std::log(v)/T(numeric::constant::log2); }
            template <typename T> inline T   neg_impl(const T v, int_type_tag) { return -v;            }
            template <typename T> inline T   pos_impl(const T v, int_type_tag) { return +v;            }
            template <typename T> inline T  ceil_impl(const T v, int_type_tag) { return v;             }
            template <typename T> inline T floor_impl(const T v, int_type_tag) { return v;             }
            template <typename T> inline T round_impl(const T v, int_type_tag) { return v;             }
            template <typename T> inline T  notl_impl(const T v, int_type_tag) { return !v;            }
            template <typename T> inline T  sqrt_impl(const T v, int_type_tag) { return std::sqrt (v); }
            template <typename T> inline T  frac_impl(const T  , int_type_tag) { return T(0);          }
            template <typename T> inline T trunc_impl(const T v, int_type_tag) { return v;             }
            template <typename T> inline T  acos_impl(const T  , int_type_tag) { return std::numeric_limits<T>::quiet_NaN(); }
            template <typename T> inline T acosh_impl(const T  , int_type_tag) { return std::numeric_limits<T>::quiet_NaN(); }
            template <typename T> inline T  asin_impl(const T  , int_type_tag) { return std::numeric_limits<T>::quiet_NaN(); }
            template <typename T> inline T asinh_impl(const T  , int_type_tag) { return std::numeric_limits<T>::quiet_NaN(); }
            template <typename T> inline T  atan_impl(const T  , int_type_tag) { return std::numeric_limits<T>::quiet_NaN(); }
            template <typename T> inline T atanh_impl(const T  , int_type_tag) { return std::numeric_limits<T>::quiet_NaN(); }
            template <typename T> inline T   cos_impl(const T  , int_type_tag) { return std::numeric_limits<T>::quiet_NaN(); }
            template <typename T> inline T  cosh_impl(const T  , int_type_tag) { return std::numeric_limits<T>::quiet_NaN(); }
            template <typename T> inline T   sin_impl(const T  , int_type_tag) { return std::numeric_limits<T>::quiet_NaN(); }
            template <typename T> inline T  sinh_impl(const T  , int_type_tag) { return std::numeric_limits<T>::quiet_NaN(); }
            template <typename T> inline T   tan_impl(const T  , int_type_tag) { return std::numeric_limits<T>::quiet_NaN(); }
            template <typename T> inline T  tanh_impl(const T  , int_type_tag) { return std::numeric_limits<T>::quiet_NaN(); }
            template <typename T> inline T   cot_impl(const T  , int_type_tag) { return std::numeric_limits<T>::quiet_NaN(); }
            template <typename T> inline T   sec_impl(const T  , int_type_tag) { return std::numeric_limits<T>::quiet_NaN(); }
            template <typename T> inline T   csc_impl(const T  , int_type_tag) { return std::numeric_limits<T>::quiet_NaN(); }

            template <typename T>
            inline bool is_integer_impl(const T& v, real_type_tag)
            {
               return std::equal_to<T>()(T(0),std::fmod(v,T(1)));
            }

            template <typename T>
            inline bool is_integer_impl(const T&, int_type_tag)
            {
               return true;
            }
         }

         template <typename Type>
         struct numeric_info { enum { length = 0, size = 32, bound_length = 0, min_exp = 0, max_exp = 0 }; };

         template <> struct numeric_info<int        > { enum { length = 10, size = 16, bound_length = 9 }; };
         template <> struct numeric_info<float      > { enum { min_exp =  -38, max_exp =  +38 }; };
         template <> struct numeric_info<double     > { enum { min_exp = -308, max_exp = +308 }; };
         template <> struct numeric_info<long double> { enum { min_exp = -308, max_exp = +308 }; };

         template <typename T>
         inline int to_int32(const T v)
         {
            const typename details::number_type<T>::type num_type;
            return to_int32_impl(v, num_type);
         }

         template <typename T>
         inline _int64_t to_int64(const T v)
         {
            const typename details::number_type<T>::type num_type;
            return to_int64_impl(v, num_type);
         }

         template <typename T>
         inline bool is_nan(const T v)
         {
            const typename details::number_type<T>::type num_type;
            return is_nan_impl(v, num_type);
         }

         template <typename T>
         inline T min(const T v0, const T v1)
         {
            const typename details::number_type<T>::type num_type;
            return min_impl(v0, v1, num_type);
         }

         template <typename T>
         inline T max(const T v0, const T v1)
         {
            const typename details::number_type<T>::type num_type;
            return max_impl(v0, v1, num_type);
         }

         template <typename T>
         inline T equal(const T v0, const T v1)
         {
            const typename details::number_type<T>::type num_type;
            return equal_impl(v0, v1, num_type);
         }

         template <typename T>
         inline T nequal(const T v0, const T v1)
         {
            const typename details::number_type<T>::type num_type;
            return nequal_impl(v0, v1, num_type);
         }

         template <typename T>
         inline T modulus(const T v0, const T v1)
         {
            const typename details::number_type<T>::type num_type;
            return modulus_impl(v0, v1, num_type);
         }

         template <typename T>
         inline T pow(const T v0, const T v1)
         {
            const typename details::number_type<T>::type num_type;
            return pow_impl(v0, v1, num_type);
         }

         template <typename T>
         inline T logn(const T v0, const T v1)
         {
            const typename details::number_type<T>::type num_type;
            return logn_impl(v0, v1, num_type);
         }

         template <typename T>
         inline T root(const T v0, const T v1)
         {
            const typename details::number_type<T>::type num_type;
            return root_impl(v0, v1, num_type);
         }

         template <typename T>
         inline T roundn(const T v0, const T v1)
         {
            const typename details::number_type<T>::type num_type;
            return roundn_impl(v0, v1, num_type);
         }

         template <typename T>
         inline T hypot(const T v0, const T v1)
         {
            const typename details::number_type<T>::type num_type;
            return hypot_impl(v0, v1, num_type);
         }

         template <typename T>
         inline T atan2(const T v0, const T v1)
         {
            const typename details::number_type<T>::type num_type;
            return atan2_impl(v0, v1, num_type);
         }

         template <typename T>
         inline T shr(const T v0, const T v1)
         {
            const typename details::number_type<T>::type num_type;
            return shr_impl(v0, v1, num_type);
         }

         template <typename T>
         inline T shl(const T v0, const T v1)
         {
            const typename details::number_type<T>::type num_type;
            return shl_impl(v0, v1, num_type);
         }

         template <typename T>
         inline T and_opr(const T v0, const T v1)
         {
            const typename details::number_type<T>::type num_type;
            return and_impl(v0, v1, num_type);
         }

         template <typename T>
         inline T nand_opr(const T v0, const T v1)
         {
            const typename details::number_type<T>::type num_type;
            return nand_impl(v0, v1, num_type);
         }

         template <typename T>
         inline T or_opr(const T v0, const T v1)
         {
            const typename details::number_type<T>::type num_type;
            return or_impl(v0, v1, num_type);
         }

         template <typename T>
         inline T nor_opr(const T v0, const T v1)
         {
            const typename details::number_type<T>::type num_type;
            return nor_impl(v0, v1, num_type);
         }

         template <typename T>
         inline T xor_opr(const T v0, const T v1)
         {
            const typename details::number_type<T>::type num_type;
            return xor_impl(v0, v1, num_type);
         }

         template <typename T>
         inline T xnor_opr(const T v0, const T v1)
         {
            const typename details::number_type<T>::type num_type;
            return xnor_impl(v0, v1, num_type);
         }

         template <typename T>
         inline bool is_integer(const T v)
         {
            const typename details::number_type<T>::type num_type;
            return is_integer_impl(v, num_type);
         }

         template <typename T, unsigned int N>
         struct fast_exp
         {
            static inline T result(T v)
            {
               unsigned int k = N;
               T l = T(1);

               while (k)
               {
                  if (1 == (k % 2))
                  {
                     l *= v;
                     --k;
                  }

                  v *= v;
                  k /= 2;
               }

               return l;
            }
         };

         template <typename T> struct fast_exp<T,10> { static inline T result(const T v) { T v_5 = fast_exp<T,5>::result(v); return v_5 * v_5; } };
         template <typename T> struct fast_exp<T, 9> { static inline T result(const T v) { return fast_exp<T,8>::result(v) * v; } };
         template <typename T> struct fast_exp<T, 8> { static inline T result(const T v) { T v_4 = fast_exp<T,4>::result(v); return v_4 * v_4; } };
         template <typename T> struct fast_exp<T, 7> { static inline T result(const T v) { return fast_exp<T,6>::result(v) * v; } };
         template <typename T> struct fast_exp<T, 6> { static inline T result(const T v) { T v_3 = fast_exp<T,3>::result(v); return v_3 * v_3; } };
         template <typename T> struct fast_exp<T, 5> { static inline T result(const T v) { return fast_exp<T,4>::result(v) * v; } };
         template <typename T> struct fast_exp<T, 4> { static inline T result(const T v) { T v_2 = v * v; return v_2 * v_2; } };
         template <typename T> struct fast_exp<T, 3> { static inline T result(const T v) { return v * v * v; } };
         template <typename T> struct fast_exp<T, 2> { static inline T result(const T v) { return v * v;     } };
         template <typename T> struct fast_exp<T, 1> { static inline T result(const T v) { return v;         } };
         template <typename T> struct fast_exp<T, 0> { static inline T result(const T  ) { return T(1);      } };

         #define exprtk_define_unary_function(FunctionName)        \
         template <typename T>                                     \
         inline T FunctionName (const T v)                         \
         {                                                         \
            const typename details::number_type<T>::type num_type; \
            return  FunctionName##_impl(v,num_type);               \
         }                                                         \

         exprtk_define_unary_function(abs  )
         exprtk_define_unary_function(acos )
         exprtk_define_unary_function(acosh)
         exprtk_define_unary_function(asin )
         exprtk_define_unary_function(asinh)
         exprtk_define_unary_function(atan )
         exprtk_define_unary_function(atanh)
         exprtk_define_unary_function(ceil )
         exprtk_define_unary_function(cos  )
         exprtk_define_unary_function(cosh )
         exprtk_define_unary_function(exp  )
         exprtk_define_unary_function(expm1)
         exprtk_define_unary_function(floor)
         exprtk_define_unary_function(log  )
         exprtk_define_unary_function(log10)
         exprtk_define_unary_function(log2 )
         exprtk_define_unary_function(log1p)
         exprtk_define_unary_function(neg  )
         exprtk_define_unary_function(pos  )
         exprtk_define_unary_function(round)
         exprtk_define_unary_function(sin  )
         exprtk_define_unary_function(sinc )
         exprtk_define_unary_function(sinh )
         exprtk_define_unary_function(sqrt )
         exprtk_define_unary_function(tan  )
         exprtk_define_unary_function(tanh )
         exprtk_define_unary_function(cot  )
         exprtk_define_unary_function(sec  )
         exprtk_define_unary_function(csc  )
         exprtk_define_unary_function(r2d  )
         exprtk_define_unary_function(d2r  )
         exprtk_define_unary_function(d2g  )
         exprtk_define_unary_function(g2d  )
         exprtk_define_unary_function(notl )
         exprtk_define_unary_function(sgn  )
         exprtk_define_unary_function(erf  )
         exprtk_define_unary_function(erfc )
         exprtk_define_unary_function(ncdf )
         exprtk_define_unary_function(frac )
         exprtk_define_unary_function(trunc)
         #undef exprtk_define_unary_function
      }

      template <typename T>
      inline T compute_pow10(T d, const int exponent)
      {
         static const double fract10[] =
         {
           0.0,
           1.0E+001, 1.0E+002, 1.0E+003, 1.0E+004, 1.0E+005, 1.0E+006, 1.0E+007, 1.0E+008, 1.0E+009, 1.0E+010,
           1.0E+011, 1.0E+012, 1.0E+013, 1.0E+014, 1.0E+015, 1.0E+016, 1.0E+017, 1.0E+018, 1.0E+019, 1.0E+020,
           1.0E+021, 1.0E+022, 1.0E+023, 1.0E+024, 1.0E+025, 1.0E+026, 1.0E+027, 1.0E+028, 1.0E+029, 1.0E+030,
           1.0E+031, 1.0E+032, 1.0E+033, 1.0E+034, 1.0E+035, 1.0E+036, 1.0E+037, 1.0E+038, 1.0E+039, 1.0E+040,
           1.0E+041, 1.0E+042, 1.0E+043, 1.0E+044, 1.0E+045, 1.0E+046, 1.0E+047, 1.0E+048, 1.0E+049, 1.0E+050,
           1.0E+051, 1.0E+052, 1.0E+053, 1.0E+054, 1.0E+055, 1.0E+056, 1.0E+057, 1.0E+058, 1.0E+059, 1.0E+060,
           1.0E+061, 1.0E+062, 1.0E+063, 1.0E+064, 1.0E+065, 1.0E+066, 1.0E+067, 1.0E+068, 1.0E+069, 1.0E+070,
           1.0E+071, 1.0E+072, 1.0E+073, 1.0E+074, 1.0E+075, 1.0E+076, 1.0E+077, 1.0E+078, 1.0E+079, 1.0E+080,
           1.0E+081, 1.0E+082, 1.0E+083, 1.0E+084, 1.0E+085, 1.0E+086, 1.0E+087, 1.0E+088, 1.0E+089, 1.0E+090,
           1.0E+091, 1.0E+092, 1.0E+093, 1.0E+094, 1.0E+095, 1.0E+096, 1.0E+097, 1.0E+098, 1.0E+099, 1.0E+100,
           1.0E+101, 1.0E+102, 1.0E+103, 1.0E+104, 1.0E+105, 1.0E+106, 1.0E+107, 1.0E+108, 1.0E+109, 1.0E+110,
           1.0E+111, 1.0E+112, 1.0E+113, 1.0E+114, 1.0E+115, 1.0E+116, 1.0E+117, 1.0E+118, 1.0E+119, 1.0E+120,
           1.0E+121, 1.0E+122, 1.0E+123, 1.0E+124, 1.0E+125, 1.0E+126, 1.0E+127, 1.0E+128, 1.0E+129, 1.0E+130,
           1.0E+131, 1.0E+132, 1.0E+133, 1.0E+134, 1.0E+135, 1.0E+136, 1.0E+137, 1.0E+138, 1.0E+139, 1.0E+140,
           1.0E+141, 1.0E+142, 1.0E+143, 1.0E+144, 1.0E+145, 1.0E+146, 1.0E+147, 1.0E+148, 1.0E+149, 1.0E+150,
           1.0E+151, 1.0E+152, 1.0E+153, 1.0E+154, 1.0E+155, 1.0E+156, 1.0E+157, 1.0E+158, 1.0E+159, 1.0E+160,
           1.0E+161, 1.0E+162, 1.0E+163, 1.0E+164, 1.0E+165, 1.0E+166, 1.0E+167, 1.0E+168, 1.0E+169, 1.0E+170,
           1.0E+171, 1.0E+172, 1.0E+173, 1.0E+174, 1.0E+175, 1.0E+176, 1.0E+177, 1.0E+178, 1.0E+179, 1.0E+180,
           1.0E+181, 1.0E+182, 1.0E+183, 1.0E+184, 1.0E+185, 1.0E+186, 1.0E+187, 1.0E+188, 1.0E+189, 1.0E+190,
           1.0E+191, 1.0E+192, 1.0E+193, 1.0E+194, 1.0E+195, 1.0E+196, 1.0E+197, 1.0E+198, 1.0E+199, 1.0E+200,
           1.0E+201, 1.0E+202, 1.0E+203, 1.0E+204, 1.0E+205, 1.0E+206, 1.0E+207, 1.0E+208, 1.0E+209, 1.0E+210,
           1.0E+211, 1.0E+212, 1.0E+213, 1.0E+214, 1.0E+215, 1.0E+216, 1.0E+217, 1.0E+218, 1.0E+219, 1.0E+220,
           1.0E+221, 1.0E+222, 1.0E+223, 1.0E+224, 1.0E+225, 1.0E+226, 1.0E+227, 1.0E+228, 1.0E+229, 1.0E+230,
           1.0E+231, 1.0E+232, 1.0E+233, 1.0E+234, 1.0E+235, 1.0E+236, 1.0E+237, 1.0E+238, 1.0E+239, 1.0E+240,
           1.0E+241, 1.0E+242, 1.0E+243, 1.0E+244, 1.0E+245, 1.0E+246, 1.0E+247, 1.0E+248, 1.0E+249, 1.0E+250,
           1.0E+251, 1.0E+252, 1.0E+253, 1.0E+254, 1.0E+255, 1.0E+256, 1.0E+257, 1.0E+258, 1.0E+259, 1.0E+260,
           1.0E+261, 1.0E+262, 1.0E+263, 1.0E+264, 1.0E+265, 1.0E+266, 1.0E+267, 1.0E+268, 1.0E+269, 1.0E+270,
           1.0E+271, 1.0E+272, 1.0E+273, 1.0E+274, 1.0E+275, 1.0E+276, 1.0E+277, 1.0E+278, 1.0E+279, 1.0E+280,
           1.0E+281, 1.0E+282, 1.0E+283, 1.0E+284, 1.0E+285, 1.0E+286, 1.0E+287, 1.0E+288, 1.0E+289, 1.0E+290,
           1.0E+291, 1.0E+292, 1.0E+293, 1.0E+294, 1.0E+295, 1.0E+296, 1.0E+297, 1.0E+298, 1.0E+299, 1.0E+300,
           1.0E+301, 1.0E+302, 1.0E+303, 1.0E+304, 1.0E+305, 1.0E+306, 1.0E+307, 1.0E+308
         };

         static const int fract10_size = static_cast<int>(sizeof(fract10) / sizeof(double));

         const int e = std::abs(exponent);

         if (exponent >= std::numeric_limits<T>::min_exponent10)
         {
            if (e < fract10_size)
            {
               if (exponent > 0)
                  return T(d * fract10[e]);
               else
                  return T(d / fract10[e]);
            }
            else
               return T(d * std::pow(10.0, 10.0 * exponent));
         }
         else
         {
                     d /= T(fract10[           -std::numeric_limits<T>::min_exponent10]);
            return T(d /    fract10[-exponent + std::numeric_limits<T>::min_exponent10]);
         }
      }
   }
}
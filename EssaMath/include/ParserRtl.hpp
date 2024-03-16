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

#include "Parser.hpp"

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

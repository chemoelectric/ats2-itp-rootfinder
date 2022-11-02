(*
  Copyright © 2022 Barry Schwartz

  This program is free software: you can redistribute it and/or
  modify it under the terms of the GNU General Public License, as
  published by the Free Software Foundation, either version 3 of the
  License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful, but
  WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
  General Public License for more details.

  You should have received copies of the GNU General Public License
  along with this program. If not, see
  <https://www.gnu.org/licenses/>.
*)

(* A TEST OF FIXED-POINT. *)

#include "share/atspre_staload.hats"
#include "itp-rootfinder/HATS/itp-rootfinder.hats"

#define ATS_EXTERN_PREFIX "my_"

%{^

#include <inttypes.h>

typedef __int128 my_i128;
typedef atstype_int64 my_fixed32p32;

#define MY_SCALE (INT64_C(1) << 32)

#define my_inline ATSinline()

my_inline atsvoid_t0ype
my_fprint_fixed32p32 (atstype_ref r, my_fixed32p32 x)
{
  fprintf ((FILE *) r, "%Lf", ((long double) x) / MY_SCALE);
}

#define my_print_fixed32p32(x) my_fprint_fixed32p32 (stdout, (x))
#define my_prerr_fixed32p32(x) my_fprint_fixed32p32 (stderr, (x))

my_inline my_fixed32p32
my_g0float_epsilon_fixed32p32 (void)
{
  return (my_fixed32p32) 1;
}

my_inline my_fixed32p32
my_g0int2float_int_fixed32p32 (atstype_int x)
{
  return (((my_fixed32p32) x) * MY_SCALE);
}

my_inline my_fixed32p32
my_g0int2float_lint_fixed32p32 (atstype_lint x)
{
  return (((my_fixed32p32) x) * MY_SCALE);
}

my_inline my_fixed32p32
my_g0float_neg_fixed32p32 (my_fixed32p32 x)
{
  return (-x);
}

my_inline my_fixed32p32
my_g0float_abs_fixed32p32 (my_fixed32p32 x)
{
  return (x < 0) ? (-x) : x;
}

my_inline my_fixed32p32
my_g0float_add_fixed32p32 (my_fixed32p32 x, my_fixed32p32 y)
{
  return (x + y);
}

my_inline my_fixed32p32
my_g0float_sub_fixed32p32 (my_fixed32p32 x, my_fixed32p32 y)
{
  return (x - y);
}

my_inline my_fixed32p32
my_g0float_mul_fixed32p32 (my_fixed32p32 x, my_fixed32p32 y)
{
  return (my_fixed32p32) ((((my_i128) x) * y) / MY_SCALE);
}

my_inline my_fixed32p32
my_g0float_div_fixed32p32 (my_fixed32p32 x, my_fixed32p32 y)
{
  return (my_fixed32p32) ((((my_i128) x) * MY_SCALE) / y);
}

my_inline atstype_bool
my_g0float_eq_fixed32p32 (my_fixed32p32 x, my_fixed32p32 y)
{
  return (x == y);
}

my_inline atstype_bool
my_g0float_neq_fixed32p32 (my_fixed32p32 x, my_fixed32p32 y)
{
  return (x != y);
}

my_inline atstype_bool
my_g0float_lt_fixed32p32 (my_fixed32p32 x, my_fixed32p32 y)
{
  return (x < y);
}

my_inline atstype_bool
my_g0float_lte_fixed32p32 (my_fixed32p32 x, my_fixed32p32 y)
{
  return (x <= y);
}

my_inline atstype_bool
my_g0float_gt_fixed32p32 (my_fixed32p32 x, my_fixed32p32 y)
{
  return (x > y);
}

my_inline atstype_bool
my_g0float_gte_fixed32p32 (my_fixed32p32 x, my_fixed32p32 y)
{
  return (x >= y);
}

%}

tkindef fixed32p32_kind = "my_fixed32p32"
stadef fix32p32knd = fixed32p32_kind
stadef fixed32p32 = g0float fix32p32knd

extern fn print_fixed32p32 : fixed32p32 -> void = "mac#%"
extern fn prerr_fixed32p32 : fixed32p32 -> void = "mac#%"
extern fn fprint_fixed32p32 : fprint_type fixed32p32 = "mac#%"
overload print with print_fixed32p32
overload prerr with prerr_fixed32p32
overload fprint with fprint_fixed32p32
implement fprint_val<fixed32p32> = fprint_fixed32p32

extern fn g0int2float_int_fixed32p32 : int -<> fixed32p32 = "mac#%"
extern fn g0int2float_lint_fixed32p32 : lint -<> fixed32p32 = "mac#%"
implement g0int2float<intknd,fix32p32knd> =
  g0int2float_int_fixed32p32
implement g0int2float<lintknd,fix32p32knd> =
  g0int2float_lint_fixed32p32

extern fn g0float_neg_fixed32p32 :
  fixed32p32 -<> fixed32p32 = "mac#%"
extern fn g0float_abs_fixed32p32 :
  fixed32p32 -<> fixed32p32 = "mac#%"
extern fn g0float_add_fixed32p32 :
  (fixed32p32, fixed32p32) -<> fixed32p32 = "mac#%"
extern fn g0float_sub_fixed32p32 :
  (fixed32p32, fixed32p32) -<> fixed32p32 = "mac#%"
extern fn g0float_mul_fixed32p32 :
  (fixed32p32, fixed32p32) -<> fixed32p32 = "mac#%"
extern fn g0float_div_fixed32p32 :
  (fixed32p32, fixed32p32) -<> fixed32p32 = "mac#%"
extern fn g0float_eq_fixed32p32 :
  (fixed32p32, fixed32p32) -<> bool = "mac#%"
extern fn g0float_neq_fixed32p32 :
  (fixed32p32, fixed32p32) -<> bool = "mac#%"
extern fn g0float_lt_fixed32p32 :
  (fixed32p32, fixed32p32) -<> bool = "mac#%"
extern fn g0float_lte_fixed32p32 :
  (fixed32p32, fixed32p32) -<> bool = "mac#%"
extern fn g0float_gt_fixed32p32 :
  (fixed32p32, fixed32p32) -<> bool = "mac#%"
extern fn g0float_gte_fixed32p32 :
  (fixed32p32, fixed32p32) -<> bool = "mac#%"
implement g0float_neg<fix32p32knd> = g0float_neg_fixed32p32
implement g0float_abs<fix32p32knd> = g0float_abs_fixed32p32
implement g0float_add<fix32p32knd> = g0float_add_fixed32p32
implement g0float_sub<fix32p32knd> = g0float_sub_fixed32p32
implement g0float_mul<fix32p32knd> = g0float_mul_fixed32p32
implement g0float_div<fix32p32knd> = g0float_div_fixed32p32
implement g0float_eq<fix32p32knd> = g0float_eq_fixed32p32
implement g0float_neq<fix32p32knd> = g0float_neq_fixed32p32
implement g0float_lt<fix32p32knd> = g0float_lt_fixed32p32
implement g0float_lte<fix32p32knd> = g0float_lte_fixed32p32
implement g0float_gt<fix32p32knd> = g0float_gt_fixed32p32
implement g0float_gte<fix32p32knd> = g0float_gte_fixed32p32

extern fn g0float_epsilon_fixed32p32 : () -<> fixed32p32 = "mac#%"
implement rootfinder$g0float_epsilon<fix32p32knd> =
  g0float_epsilon_fixed32p32

macdef i2fx = g0int2float<intknd,fix32p32knd>

implement
main0 () =
  let
    (* An alternative way to set kappa2 to 2, avoiding the need to
       write an actual pow function for our fixed-point type: *)
    implement
    rootfinder$g0float_pow<fix32p32knd> (x, _kappa2) = x * x

    val root = rootfinder_fun (i2fx 9 / i2fx 10,
                               i2fx 11 / i2fx 10,
                               lam x =<> (x * x) - i2fx 1)
    val- true = (abs (root - i2fx 1) < i2fx 1 / i2fx 1000000)

    val root = rootfinder_fun (i2fx 9 / i2fx 10,
                               i2fx 11 / i2fx 10,
                               lam x =<> (x * x) - i2fx 1,
                               i2fx 1 / i2fx 10000)
    val- true = (abs (root - i2fx 1) <= i2fx 1 / i2fx 10000)

    val root = rootfinder_cloref (i2fx 9 / i2fx 10,
                                  i2fx 11 / i2fx 10,
                                  lam x =<cloref> (x * x) - i2fx 1)
    val- true = (abs (root - i2fx 1) < i2fx 1 / i2fx 1000000)

    val root = rootfinder_cloref (i2fx 9 / i2fx 10,
                                  i2fx 11 / i2fx 10,
                                  lam x =<cloref> (x * x) - i2fx 1,
                                  i2fx 1 / i2fx 10000)
    val- true = (abs (root - i2fx 1) <= i2fx 1 / i2fx 10000)
  in
  end

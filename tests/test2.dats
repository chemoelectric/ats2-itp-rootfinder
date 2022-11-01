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

#define ATS_EXTERN_PREFIX "my_"

%{^

typedef __int128 my_i128;
typedef atstype_int64 my_fixed32p32;

#define MY_SCALE 0x100000000LL

#define my_inline ATSinline()

my_inline atsvoid_t0ype
my_fprint_fixed32p32 (atstype_ref r, my_fixed32p32 x)
{
  fprintf ((FILE *) r, "%Lf", ((long double) x) / MY_SCALE);
}

#define my_print_fixed32p32(x) my_fprint_fixed32p32 (stdout, (x))
#define my_prerr_fixed32p32(x) my_fprint_fixed32p32 (stderr, (x))

my_inline my_fixed32p32
my_g0int2float_int_fixed32p32 (atstype_int x)
{
  return (((my_fixed32p32) x) * MY_SCALE);
}

my_inline my_fixed32p32
my_g0float_neg_fixed32p32 (my_fixed32p32 x)
{
  return (-x);
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
implement g0int2float<intknd,fix32p32knd> = g0int2float_int_fixed32p32

extern fn g0float_neg_fixed32p32 :
  fixed32p32 -<> fixed32p32 = "mac#%"
extern fn g0float_add_fixed32p32 :
  (fixed32p32, fixed32p32) -<> fixed32p32 = "mac#%"
extern fn g0float_sub_fixed32p32 :
  (fixed32p32, fixed32p32) -<> fixed32p32 = "mac#%"
extern fn g0float_mul_fixed32p32 :
  (fixed32p32, fixed32p32) -<> fixed32p32 = "mac#%"
extern fn g0float_div_fixed32p32 :
  (fixed32p32, fixed32p32) -<> fixed32p32 = "mac#%"
implement g0float_neg<fix32p32knd> = g0float_neg_fixed32p32
implement g0float_add<fix32p32knd> = g0float_add_fixed32p32
implement g0float_sub<fix32p32knd> = g0float_sub_fixed32p32
implement g0float_mul<fix32p32knd> = g0float_mul_fixed32p32
implement g0float_div<fix32p32knd> = g0float_div_fixed32p32

#include "itp-rootfinder/HATS/itp-rootfinder.hats"

implement
main0 () =
  let
    // FIXME // FIXME // FIXME // FIXME // FIXME // FIXME // FIXME // FIXME // FIXME // FIXME // FIXME
    // FIXME // FIXME // FIXME // FIXME // FIXME // FIXME // FIXME // FIXME // FIXME // FIXME // FIXME
    // FIXME // FIXME // FIXME // FIXME // FIXME // FIXME // FIXME // FIXME // FIXME // FIXME // FIXME
    // FIXME // FIXME // FIXME // FIXME // FIXME // FIXME // FIXME // FIXME // FIXME // FIXME // FIXME

    val x : fixed32p32 = g0i2f 10
    val y : fixed32p32 = g0i2f ~3
    val () = println! (x + y)
    val () = println! (x - y)
    val () = println! (x * y)
    val () = println! (x / y)
  in
  end

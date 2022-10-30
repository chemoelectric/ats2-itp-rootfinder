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

(*

ITP rootfinding for a univariate real function.

Reference:

  I.F.D. Oliveira and R.H.C. Takahashi. 2020. An Enhancement of
  the Bisection Method Average Performance Preserving Minmax
  Optimality. ACM Trans. Math. Softw. 47, 1, Article 5 (December
  2020), 24 pages. https://doi.org/10.1145/3423597

Note that I write constants as fractions instead of as floating point
constants. This is in hopes to simplify the use of a fixed-point
representation as if it were floating point.

*)

#define ATS_DYNLOADFLAG 0

#define ATS_PACKNAME "ats2-itp-rootfinder"
#define ATS_EXTERN_PREFIX "ats2_itp_rootfinder_"

#include "share/atspre_staload.hats"

staload "itp-rootfinder/SATS/itp-rootfinder.sats"

macdef raise_exception (kind, message) =
  $raise itp_rootfinder_exc ($mylocation, ,(kind), ,(message))

(* The Golden Ratio, (1 + √5)/2, rounded down by about
   0.00003398875. *)
#define PHI_NUMERATOR 1618
#define PHI_DENOMINATOR 1000

extern fn g0float2int_ldouble_llint :
  g0float ldblknd -<> g0int intknd = "mac#%"
implement g0float2int<ldblknd,intknd> = g0float2int_ldouble_llint

extern fn epsilon_float : () -<> g0float fltknd = "mac#%"
extern fn epsilon_double : () -<> g0float dblknd = "mac#%"
extern fn epsilon_ldouble : () -<> g0float ldblknd = "mac#%"
extern fn {tk : tkind} epsilon : () -<> g0float tk
implement epsilon<fltknd> = epsilon_float
implement epsilon<dblknd> = epsilon_double
implement epsilon<ldblknd> = epsilon_ldouble

extern fn log2_ldouble : g0float ldblknd -<> g0float ldblknd = "mac#%"
extern fn {tk : tkind} log2 : g0float tk -<> g0float tk
implement log2<ldblknd> = log2_ldouble

extern fn ceil_ldouble : g0float ldblknd -<> g0float ldblknd = "mac#%"
extern fn {tk : tkind} ceil : g0float tk -<> g0float tk
implement ceil<ldblknd> = ceil_ldouble

implement {tk}
itp_rootfinder$epsilon () =
  let
    macdef i2f = g0int2float<intknd,tk>
  in
    i2f 1000 * epsilon<tk> ()
  end

implement {}
itp_rootfinder$extra_steps () =
  0LL

implement {tk}
itp_rootfinder$kappa1 () =
  let
    macdef i2f = g0int2float<intknd,tk>
  in
    i2f 1 / i2f 10
  end

implement {tk}
itp_rootfinder$kappa2 () =
  let
    macdef i2f = g0int2float<intknd,tk>
  in
    i2f 2
  end

(* Integer powers where base and power are of any unsigned integer
   types. *)
fn {tk_b, tk_p : tkind}
g1uint_ipow
          (base  : g1uint tk_b,
           power : g1uint tk_p)
    :<> g1uint tk_b =
  let
    fun
    loop {p : nat}
         .<p>.
         (b     : g1uint tk_b,
          p     : g1uint (tk_p, p),
          accum : g1uint tk_b)
        :<> g1uint tk_b =
      let
        val ph = half p
        val accum = (if ph + ph = p then accum else accum * b)
      in
        if ph = g1i2u 0 then
          accum
        else
          loop (b * b, ph, accum)
      end

    prval () = lemma_g1uint_param base
    prval () = lemma_g1uint_param power
  in
    loop (base, power, g1i2u 1)
  end

fn {tk_b, tk_p : tkind}
g0uint_ipow
          (base  : g0uint tk_b,
           power : g0uint tk_p)
    :<> g0uint tk_b =
  g0ofg1 (g1uint_ipow (g1ofg0 base, g1ofg0 power))

fn {tk : tkind}
root_bracket_finder
          (a : g0float tk,
           b : g0float tk)
    : @(g0float tk, g0float tk) =
  let
    typedef real = g0float tk
    macdef i2f = g0int2float<intknd,tk>
    macdef zero = i2f 0

    typedef sign_t = [s : int | ~1 <= s; s <= 1] int s

    fn {}
    sign (x : real)
        :<> sign_t =
      if x < zero then
        ~1
      else if zero < x then
        1
      else
        0

    fn {}
    apply_sign (sign : sign_t, x : real)
        :<> real =
      if sign < 0 then
        ~x
      else if 0 < sign then
        x
      else
        zero

    val one_plus_phi =
      i2f (PHI_DENOMINATOR + PHI_NUMERATOR) / i2f PHI_DENOMINATOR

    val eps = itp_rootfinder$epsilon ()
    val two_eps = eps + eps

    val nhalf : llint =
      g0f2i (ceil (log2 (g0f2f ((b - a) / two_eps))))
    val n0 = itp_rootfinder$extra_steps ()
    val n_max = nhalf + n0

    val ya = itp_rootfinder$func a
    and yb = itp_rootfinder$func b

    val sign_ya = sign ya
    and sign_yb = sign yb
  in
    if sign_ya = 0 then
      @(a, a)
    else if sign_yb = 0 then
      @(b, b)
    else if 0 < sign_ya * sign_yb then
      raise_exception (itp_rootfinder_root_not_bracketed,
                       "the root is not bracketed")
    else
@(zero, zero)                     (* FIXME *)
  end

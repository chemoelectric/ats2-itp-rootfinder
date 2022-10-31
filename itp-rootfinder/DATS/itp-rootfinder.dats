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

extern praxi
lemma_square_is_gte :
  {i : int} () -<prf> [i <= i * i] void

macdef raise_exception (kind, message) =
  $raise itp_rootfinder_exc ($mylocation, ,(kind))

(* The Golden Ratio, (1 + √5)/2, rounded down by about
   0.00003398875. *)
#define PHI_NUMERATOR 1618
#define PHI_DENOMINATOR 1000

extern fn epsilon_float : () -<> g0float fltknd = "mac#%"
extern fn epsilon_double : () -<> g0float dblknd = "mac#%"
extern fn epsilon_ldouble : () -<> g0float ldblknd = "mac#%"
extern fn {tk : tkind} epsilon : () -<> g0float tk
implement epsilon<fltknd> = epsilon_float
implement epsilon<dblknd> = epsilon_double
implement epsilon<ldblknd> = epsilon_ldouble

extern fn pow_float :
  (g0float fltknd, g0float fltknd) -<> g0float fltknd = "mac#%"
extern fn pow_double :
  (g0float dblknd, g0float dblknd) -<> g0float dblknd = "mac#%"
extern fn pow_ldouble :
  (g0float ldblknd, g0float ldblknd) -<> g0float ldblknd = "mac#%"
extern fn {tk : tkind} pow : (g0float tk, g0float tk) -<> g0float tk
implement pow<fltknd> = pow_float
implement pow<dblknd> = pow_double
implement pow<ldblknd> = pow_ldouble

implement {tk}
itp_rootfinder$epsilon () =
  let
    macdef i2f = g0int2float<intknd,tk>
  in
    i2f 1000 * epsilon<tk> ()
  end

implement {}
itp_rootfinder$extra_steps () =
  0L

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

fn {tk : tkind}
g1int_pow2 {k : nat}
           (k : g1int (tk, k))
    :<> [pow : pos] g1int (tk, pow) =
  let
    fun
    loop {b    : int | 2 <= b}
         {i    : nat}
         {pow0 : pos}
         .<i>.
         (b     : g1int (tk, b),
          i     : g1int (tk, i),
          accum : g1int (tk, pow0))
        :<> [pow1 : pos] g1int (tk, pow1) =
      let
        prval () = lemma_square_is_gte {b} ()
        val ihalf = half i
      in
        if ihalf + ihalf = i then
          begin
            if ihalf = g1i2i 0 then
              accum
            else
              loop (b * b, ihalf, accum)
          end
        else
          let
            prval () = mul_pos_pos_pos (mul_make {pow0, b} ())
          in
            if ihalf = g1i2i 0 then
              accum * b
            else
              loop (b * b, ihalf, accum * b)
          end
      end
  in
    loop (g1i2i 2, k, g1i2i 1)
  end

fn {tk : tkind}
root_bracket_finder
          (a : g0float tk,
           b : g0float tk)
    : @(g0float tk, g0float tk) =
  let
    typedef real = g0float tk
    macdef i2f = g0int2float<intknd,tk>
    macdef zero = i2f 0
    macdef one = i2f 1

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

    fn
    ceil_log2 (x : real)
        :<!exn> [i : pos] lint i =
      let
        fun
        loop {i : pos}
             {k : nat}
             .<k>.
             (i : lint i,
              k : int k)
            :<!exn> [i : pos] lint i =
          if x <= g0i2f i then
            i
          else if k <= 1 then
            raise_exception itp_rootfinder_epsilon_too_small
          else
            loop {2 * i} {k - 1} (i + i, pred k)

        prval () = lemma_sizeof {lint} ()
      in
        loop (1L, sz2i (i2sz 8 * sizeof<lint>))
      end

    val one_plus_phi =
      i2f (PHI_DENOMINATOR + PHI_NUMERATOR) / i2f PHI_DENOMINATOR

    val eps = itp_rootfinder$epsilon ()
    val two_eps = eps + eps

    val nbisect = ceil_log2 ((b - a) / two_eps)
    val n0 = itp_rootfinder$extra_steps ()
    val n_max = nbisect + n0

    val kappa1 = itp_rootfinder$kappa1 ()
    and kappa2 = itp_rootfinder$kappa2 ()

    val () =
      if kappa1 <= zero then
        raise_exception itp_rootfinder_kappa1_not_positive
    val () =
      if (kappa2 < one) + (one_plus_phi < kappa2) then
        raise_exception itp_rootfinder_kappa2_out_of_range

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
      raise_exception itp_rootfinder_root_not_bracketed
    else
@(zero, zero)                     (* FIXME *)
  end

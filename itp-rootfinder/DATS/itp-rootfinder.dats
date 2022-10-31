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
  $raise itp_rootfinder_exc ($mylocation, ,(kind))

typedef integer (i : int) = lint i
typedef Integer = [i : int] integer i

extern praxi
lemma_square_is_gte :
  {i : int} () -<prf> [i <= i * i] void

(* The Golden Ratio, (1 + √5)/2, rounded down by about
   0.00003398875. *)
#define PHI_NUMERATOR 1618
#define PHI_DENOMINATOR 1000

extern fn g0float_epsilon_float : () -<> g0float fltknd = "mac#%"
extern fn g0float_epsilon_double : () -<> g0float dblknd = "mac#%"
extern fn g0float_epsilon_ldouble : () -<> g0float ldblknd = "mac#%"
implement itp_rootfinder$g0float_epsilon<fltknd> =
  g0float_epsilon_float
implement itp_rootfinder$g0float_epsilon<dblknd> =
  g0float_epsilon_double
implement itp_rootfinder$g0float_epsilon<ldblknd> =
  g0float_epsilon_ldouble

extern fn g0float_pow_float :
  (g0float fltknd, g0float fltknd) -<> g0float fltknd = "mac#%"
extern fn g0float_pow_double :
  (g0float dblknd, g0float dblknd) -<> g0float dblknd = "mac#%"
extern fn g0float_pow_ldouble :
  (g0float ldblknd, g0float ldblknd) -<> g0float ldblknd = "mac#%"
implement itp_rootfinder$g0float_pow<fltknd> = g0float_pow_float
implement itp_rootfinder$g0float_pow<dblknd> = g0float_pow_double
implement itp_rootfinder$g0float_pow<ldblknd> = g0float_pow_ldouble

implement {tk}
itp_rootfinder$epsilon () =
  let
    macdef i2f = g0int2float<intknd,tk>
  in
    i2f 1000 * itp_rootfinder$g0float_epsilon<tk> ()
  end

implement {}
itp_rootfinder$extra_steps () =
  g1i2i 0

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
  (* The following code is based on an earlier implementation I wrote
     in Scheme. *)
  let
    val () = assertloc (a <= b)

    typedef real = g0float tk
    macdef i2f = g0int2float<intknd,tk>
    macdef zero = i2f 0
    macdef one = i2f 1
    macdef real_pow = itp_rootfinder$g0float_pow<tk>

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
        :<!exn> [i : pos] integer i =
      let
        fun
        loop {i : pos}
             {k : nat}
             .<k>.
             (i : integer i,
              k : int k)
            :<!exn> [i : pos] integer i =
          if x <= g0i2f i then
            i
          else if k <= 1 then
            raise_exception itp_rootfinder_epsilon_too_small
          else
            loop {2 * i} {k - 1} (i + i, pred k)

        prval () = lemma_sizeof {Integer} ()
      in
        loop (1L, sz2i (i2sz 8 * sizeof<Integer>))
      end

    val one_plus_phi =
      i2f (PHI_DENOMINATOR + PHI_NUMERATOR) / i2f PHI_DENOMINATOR

    val eps = itp_rootfinder$epsilon ()
    val two_eps = eps + eps

    val nbisect = ceil_log2 ((b - a) / two_eps)
    val n0 = itp_rootfinder$extra_steps ()
    val n_max = nbisect + g1i2i n0

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

    val sigma_ya = sign ya
    and sigma_yb = sign yb

    fun
    loop {pow2 : pos}
         .<pow2>.
         (pow2 : integer pow2,
          a    : real,
          b    : real,
          ya   : real,
          yb   : real)
        : @(real, real) =
      if pow2 = g1i2i 1 then
        @(a, b)
      else if b - a <= two_eps then
        @(a, b)
      else
        let
          val b_sub_a = b - a
          val half_of_b_sub_a = (b - a) / i2f 2

          val xbisect = a + half_of_b_sub_a
          
          (* xf – interpolation by regula falsi. *)
          val yb_sub_ya = yb - ya
          val xf = ((yb / yb_sub_ya) * a) - ((ya / yb_sub_ya) * b)

          val delta = kappa1 * abs (real_pow (b_sub_a, kappa2))
          val xbisect_sub_xf = xbisect - xf
          val sigma = sign (xbisect_sub_xf)

          (* xt – the ‘truncation’ of xf. *)
          val xt =
            if delta <= abs (xbisect - xf) then
              xf + apply_sign (sigma, delta)
            else
              xbisect

          val r = (g0i2f pow2 * eps) - half_of_b_sub_a

          (* xp – the projection of xt onto [x½-r,x½+r]. *)
          val xp =
            if abs (xt - xbisect) <= r then
              xt
            else
              xbisect - apply_sign (sigma, r)

          val yp = itp_rootfinder$func xp
          val sigma_yp = sign yp
        in
          if sigma_yp = sigma_ya then
            (* yp has the same sign as ya. Make it the new ya. *)
            loop (half pow2, xp, b, yp, yb)
          else if sigma_yp = sigma_yb then
            (* yp has the same sign as yb. Make it the new yb. *)
            loop (half pow2, a, xp, ya, yp)
          else
            (* yp is zero. *)
            @(xp, xp)
        end
  in
    if sigma_ya = 0 then
      @(a, a)
    else if sigma_yb = 0 then
      @(b, b)
    else if 0 < sigma_ya * sigma_yb then
      raise_exception itp_rootfinder_root_not_bracketed
    else
@(zero, zero)                     (* FIXME *)
  end

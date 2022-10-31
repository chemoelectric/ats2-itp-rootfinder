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

*)

#define ATS_PACKNAME "ats2-itp-rootfinder"
#define ATS_EXTERN_PREFIX "ats2_itp_rootfinder_"

%{#
#include <itp-rootfinder/CATS/itp-rootfinder.cats>
%}

datatype itp_rootfinder_exc_kind =
| itp_rootfinder_epsilon_too_small
| itp_rootfinder_kappa1_not_positive
| itp_rootfinder_kappa2_out_of_range
| itp_rootfinder_root_not_bracketed

exception itp_rootfinder_exc of
  (string, itp_rootfinder_exc_kind)

(* The tolerance for terminating the algorithm. The current default is
   1000 times the "epsilon" for g0float(tk). *)
fn {tk : tkind}
itp_rootfinder$epsilon :
  () -> g0float tk

(* Increase itp_rootfinder$extra_steps above zero, if you wish to try
   to speed up convergence, at the expense of that many more steps in
   the worst case. *)
fn {}
itp_rootfinder$extra_steps :
  () -> [n0 : nat] lint n0

(* A positive value. The default is 1/10. *)
fn {tk : tkind}
itp_rootfinder$kappa1 :
  () -> g0float tk

(* A value between 1 and 2618/1000, inclusive. The default is 2. *)
fn {tk : tkind}
itp_rootfinder$kappa2 :
  () -> g0float tk

(* The function to evaluate. *)
fn {tk : tkind}
itp_rootfinder$func :
  g0float tk -> g0float tk

(* If necessary, implement itp_rootfinder$g0float_pow<tk>(x, y) as x
   raised to the power y for your typekind. The value of x will be
   positive, and that of y will be kappa2. The function may already be
   implemented for your typekind. *)
fn {tk : tkind}
itp_rootfinder$g0float_pow :
  (g0float tk, g0float tk) -> g0float tk

(* If necessary, implement itp_rootfinder$g0float_epsilon<tk>() as the
   "epsilon" for your typekind. The function may already be
   implemented for your typekind, and is not used if you implement
   your own itp_rootfinder$epsilon<tk>(). *)
fn {tk : tkind}
itp_rootfinder$g0float_epsilon :
  () -<> g0float tk

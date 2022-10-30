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
| itp_rootfinder_root_not_bracketed

exception itp_rootfinder_exc of
  (string, itp_rootfinder_exc_kind, string)

(* The tolerance for terminating the algorithm. *)
fn {tk : tkind}
itp_rootfinder$epsilon :
  () -<> g0float tk

(* Increase itp_rootfinder$extra_steps above zero, if you wish to try
   to speed up convergence, at the expense of that many more steps in
   the worst case. *)
fn {}
itp_rootfinder$extra_steps :
  () -<> [n0 : nat] llint n0

(* A positive value. *)
fn {tk : tkind}
itp_rootfinder$kappa1 :
  () -<> g0float tk

(* A value between 1 and 2618/1000, inclusive. *)
fn {tk : tkind}
itp_rootfinder$kappa2 :
  () -<> g0float tk

(* The function to evaluate. *)
fn {tk : tkind}
itp_rootfinder$func :
  g0float tk -> g0float tk

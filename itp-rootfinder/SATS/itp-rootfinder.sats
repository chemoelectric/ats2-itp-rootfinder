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

(*------------------------------------------------------------------*)

datatype rootfinder_exc_kind =
| rootfinder_epsilon_too_small
| rootfinder_kappa1_not_positive
| rootfinder_kappa2_out_of_range
| rootfinder_root_not_bracketed

exception rootfinder_exc of
  (string, rootfinder_exc_kind)

(*------------------------------------------------------------------*)

(* Given an initial bracket (with the arguments in either order),
   produce a refined bracket with the lesser-or-equal value first. *)

(* rootbracketer_with_template_epsilon<tk> (a, b) *)
fn {tk : tkind}
rootbracketer_with_template_epsilon :
  (g0float tk, g0float tk) -< !exn >
    @(g0float tk, g0float tk)

(* rootbracketer_with_given_epsilon<tk> (a, b, eps) *)
fn {tk : tkind}
rootbracketer_with_given_epsilon :
  (g0float tk, g0float tk, g0float tk) -< !exn >
    @(g0float tk, g0float tk)

overload rootbracketer with rootbracketer_with_template_epsilon
overload rootbracketer with rootbracketer_with_given_epsilon

(*------------------------------------------------------------------*)

(* Given an initial bracket (with the arguments in either order),
   produce an estimate of the root. *)

(* rootfinder_with_template_epsilon<tk> (a, b) *)
fn {tk : tkind}
rootfinder_with_template_epsilon :
  (g0float tk, g0float tk) -< !exn >
    g0float tk

(* rootfinder_with_given_epsilon<tk> (a, b, eps) *)
fn {tk : tkind}
rootfinder_with_given_epsilon :
  (g0float tk, g0float tk, g0float tk) -< !exn >
    g0float tk

overload rootfinder with rootfinder_with_template_epsilon
overload rootfinder with rootfinder_with_given_epsilon

(*------------------------------------------------------------------*)

(* The function to evaluate. *)

fn {tk : tkind}
rootfinder$func :
  g0float tk -< !exn > g0float tk

(*------------------------------------------------------------------*)

(* Interfaces that take a function or closure instead of one having to
   implement rootfinder$func. *)

fn {tk : tkind}
rootbracketer_fun_with_template_epsilon :
  (g0float tk -< !exn > g0float tk,
   g0float tk, g0float tk) -< !exn >
    @(g0float tk, g0float tk)

fn {tk : tkind}
rootbracketer_fun_with_given_epsilon :
  (g0float tk -< !exn > g0float tk,
   g0float tk, g0float tk, g0float tk) -< !exn >
    @(g0float tk, g0float tk)

fn {tk : tkind}
rootfinder_fun_with_template_epsilon :
  (g0float tk -< !exn > g0float tk,
   g0float tk, g0float tk) -< !exn >
    g0float tk

fn {tk : tkind}
rootfinder_fun_with_given_epsilon :
  (g0float tk -< !exn > g0float tk,
   g0float tk, g0float tk, g0float tk) -< !exn >
    g0float tk

fn {tk : tkind}
rootbracketer_cloref_with_template_epsilon :
  (g0float tk -< !exn,cloref > g0float tk,
   g0float tk, g0float tk) -< !exn >
    @(g0float tk, g0float tk)

fn {tk : tkind}
rootbracketer_cloref_with_given_epsilon :
  (g0float tk -< !exn,cloref > g0float tk,
   g0float tk, g0float tk, g0float tk) -< !exn >
    @(g0float tk, g0float tk)

fn {tk : tkind}
rootfinder_cloref_with_template_epsilon :
  (g0float tk -< !exn,cloref > g0float tk,
   g0float tk, g0float tk) -< !exn >
    g0float tk

fn {tk : tkind}
rootfinder_cloref_with_given_epsilon :
  (g0float tk -< !exn,cloref > g0float tk,
   g0float tk, g0float tk, g0float tk) -< !exn >
    g0float tk

overload rootbracketer_fun with
  rootbracketer_fun_with_template_epsilon
overload rootbracketer_fun with
  rootbracketer_fun_with_given_epsilon

overload rootfinder_fun with
  rootfinder_fun_with_template_epsilon
overload rootfinder_fun with
  rootfinder_fun_with_given_epsilon

overload rootbracketer_cloref with
  rootbracketer_cloref_with_template_epsilon
overload rootbracketer_cloref with
  rootbracketer_cloref_with_given_epsilon

overload rootfinder_cloref with
  rootfinder_cloref_with_template_epsilon
overload rootfinder_cloref with
  rootfinder_cloref_with_given_epsilon

(*------------------------------------------------------------------*)

(* The tolerance for terminating the algorithm. The current default is
   1000 times the "epsilon" for g0float(tk). *)
fn {tk : tkind}
rootfinder$epsilon :
  () -<> g0float tk

(* Increase rootfinder$extra_steps above zero, if you wish to try to
   speed up convergence, at the expense of that many more steps in the
   worst case. *)
fn {}
rootfinder$extra_steps :
  () -<> [n0 : nat] lint n0

(* A positive value. The default is 1/10. *)
fn {tk : tkind}
rootfinder$kappa1 :
  () -<> g0float tk

(* A value between 1 and 2618/1000, inclusive. The default is 2. *)
fn {tk : tkind}
rootfinder$kappa2 :
  () -<> g0float tk

(*------------------------------------------------------------------*)

(* If necessary, implement rootfinder$g0float_pow<tk>(x, y) as x
   raised to the power y for your typekind. The value of x will be
   positive, and that of y will be kappa2. This is the only way in
   which kappa2 is used.

   Thus, if you implement rootfinder$g0float_pow<tk> as an identity
   function, then kappa2 will be ignored and the effect will be the
   same as kappa2 = 1.

   If you implement rootfinder$g0float_pow<tk> as squaring, then
   kappa2 will be ignored and the effect will be the same as kappa2 =
   2.

   (Therefore you do not actually need a pow function for your
   typekind.) *)
fn {tk : tkind}
rootfinder$g0float_pow :
  (g0float tk, g0float tk) -<> g0float tk

(* If necessary, implement rootfinder$g0float_epsilon<tk>() as the
   "epsilon" for your typekind. The function is not used if you
   implement your own rootfinder$epsilon<tk>(). *)
fn {tk : tkind}
rootfinder$g0float_epsilon :
  () -<> g0float tk

(*------------------------------------------------------------------*)


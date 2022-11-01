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

#include "share/atspre_staload.hats"
#include "itp-rootfinder/HATS/itp-rootfinder.hats"

implement
main0 () =
  let
    val root = rootfinder_fun (0.9, 1.1, lam x =<> (x * x) - 1.0)
    val- true = (abs (root - 1.0) < 0.000001)

    val root = rootfinder_fun (1.0, 1.0, lam x =<> (x * x) - 1.0)
    val- true = (root = 1.0)

    val root = rootfinder_fun (1.0, 300.0, lam x =<> (x * x) - 1.0)
    val- true = (root = 1.0)

    val root = rootfinder_fun (~300.0, 1.0, lam x =<> (x * x) - 1.0)
    val- true = (root = 1.0)

    val root =
      rootfinder_fun
        (~0.2L, 0.1L, lam x =<> $extfcall (ldouble, "sinl", x),
         0.0001L)
    val- true = (abs root <= 0.0001L)

    val root =
      rootfinder_cloref
        (3.0F, 3.2F, lam x =<cloref> $extfcall (float, "sinf", x))
    val- true = (abs (root - 3.1415926535F) < 0.0001F)

    val root =
      rootfinder_cloref
        (3.0F, 3.2F, lam x =<cloref> $extfcall (float, "sinf", x),
         0.01F)
    val- true = (abs (root - 3.1415926535F) <= 0.01F)

    implement rootfinder$func<dblknd> x = (x * x) - 1.0
    val @(a, b) = rootbracketer (1.0, 300.0)
    val- true = (a = 1.0) * (b = 1.0)

    implement rootfinder$func<dblknd> x = (x * x) - 1.0
    val @(a, b) = rootbracketer (~300.0, 1.0)
    val- true = (a = 1.0) * (b = 1.0)

    implement rootfinder$func<dblknd> x = (x * x) - 1.0
    val @(a, b) = rootbracketer (0.0, 2.0, 0.001)
    val- true = (1.0 - a <= 0.001) * (b - 1.0 <= 0.001)
  in
  end

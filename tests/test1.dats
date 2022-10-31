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
    val r1 = rootfinder_fun (0.9, 1.1, lam x =<> (x * x) - 1.0)
    val- true = (abs (r1 - 1.0) < 0.000001)
  in
  end


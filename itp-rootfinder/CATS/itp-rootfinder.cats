/*
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
*/

#ifndef ATS2_ITP_ROOTFINDER_CATS__HEADER_GUARD__
#define ATS2_ITP_ROOTFINDER_CATS__HEADER_GUARD__

#include <float.h>
#include <math.h>

#define ats2_itp_rootfinder_inline ATSinline ()

ats2_itp_rootfinder_inline atstype_float
ats2_itp_rootfinder_g0int2float_int_float (atstype_int x)
{
  return x;
}

ats2_itp_rootfinder_inline atstype_float
ats2_itp_rootfinder_g0int2float_lint_float (atstype_lint x)
{
  return x;
}

ats2_itp_rootfinder_inline atstype_double
ats2_itp_rootfinder_g0int2float_int_double (atstype_int x)
{
  return x;
}

ats2_itp_rootfinder_inline atstype_double
ats2_itp_rootfinder_g0int2float_lint_double (atstype_lint x)
{
  return x;
}

ats2_itp_rootfinder_inline atstype_ldouble
ats2_itp_rootfinder_g0int2float_int_ldouble (atstype_int x)
{
  return x;
}

ats2_itp_rootfinder_inline atstype_ldouble
ats2_itp_rootfinder_g0int2float_lint_ldouble (atstype_lint x)
{
  return x;
}

ats2_itp_rootfinder_inline atstype_float
ats2_itp_rootfinder_g0float_epsilon_float (void)
{
  return FLT_EPSILON;
}

ats2_itp_rootfinder_inline atstype_double
ats2_itp_rootfinder_g0float_epsilon_double (void)
{
  return DBL_EPSILON;
}

ats2_itp_rootfinder_inline atstype_ldouble
ats2_itp_rootfinder_g0float_epsilon_ldouble (void)
{
  return LDBL_EPSILON;
}

ats2_itp_rootfinder_inline atstype_float
ats2_itp_rootfinder_g0float_pow_float (atstype_float x,
                                       atstype_float y)
{
  return powf (x, y);
}

ats2_itp_rootfinder_inline atstype_double
ats2_itp_rootfinder_g0float_pow_double (atstype_double x,
                                        atstype_double y)
{
  return pow (x, y);
}

ats2_itp_rootfinder_inline atstype_ldouble
ats2_itp_rootfinder_g0float_pow_ldouble (atstype_ldouble x,
                                         atstype_ldouble y)
{
  return powl (x, y);
}

#endif /* ATS2_ITP_ROOTFINDER_CATS__HEADER_GUARD__ */

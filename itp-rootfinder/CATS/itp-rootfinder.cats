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

ats2_itp_rootfinder_inline atstype_llint
ats2_itp_rootfinder_g0float2int_ldouble_llint (atstype_ldouble x)
{
  return (atstype_llint) x;
}

ats2_itp_rootfinder_inline atstype_float
ats2_itp_rootfinder_epsilon_float (void)
{
  return FLT_EPSILON;
}

ats2_itp_rootfinder_inline atstype_double
ats2_itp_rootfinder_epsilon_double (void)
{
  return DBL_EPSILON;
}

ats2_itp_rootfinder_inline atstype_ldouble
ats2_itp_rootfinder_epsilon_ldouble (void)
{
  return LDBL_EPSILON;
}

ats2_itp_rootfinder_inline atstype_ldouble
ats2_itp_rootfinder_log2_ldouble (atstype_ldouble x)
{
  return log2l (x);
}

ats2_itp_rootfinder_inline atstype_ldouble
ats2_itp_rootfinder_ceil_ldouble (atstype_ldouble x)
{
  return ceill (x);
}

#endif /* ATS2_ITP_ROOTFINDER_CATS__HEADER_GUARD__ */

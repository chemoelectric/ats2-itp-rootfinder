#
# Copyright © 2022 Barry Schwartz
#
# This program is free software: you can redistribute it and/or
# modify it under the terms of the GNU General Public License, as
# published by the Free Software Foundation, either version 3 of the
# License, or (at your option) any later version.
#
# This program is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
# General Public License for more details.
#
# You should have received copies of the GNU General Public License
# along with this program. If not, see
# <https://www.gnu.org/licenses/>.
#

.DELETE_ON_ERROR:

ACLOCAL_AMFLAGS = -I m4 --install
AUTOMAKE_OPTIONS =
AUTOMAKE_OPTIONS += foreign
AUTOMAKE_OPTIONS += subdir-objects
AUTOMAKE_OPTIONS += -Wno-portability

include $(top_srcdir)/aminclude_static.am
@GNU@ include $(top_srcdir)/silent-rules.mk
@GNU@ -include ats-dependencies/*.mk

EXTRA_DIST =
MOSTLYCLEANFILES =
CLEANFILES =
DISTCLEANFILES =
BUILT_SOURCES =
AM_M4FLAGS =
AM_CPPFLAGS =
AM_CFLAGS =
AM_LDFLAGS =
LDADD =
bin_PROGRAMS =
lib_LTLIBRARIES =
EXTRA_PROGRAMS =
TESTS =
nobase_nodist_pkginclude_HEADERS =
nodist_pkgconfig_DATA =

EXTRA_DIST += $(srcdir)/silent-rules.mk
EXTRA_DIST += COPYING
EXTRA_DIST += INSTALL
EXTRA_DIST += README
EXTRA_DIST += AUTHORS

DISTCLEANFILES += Makefile
DISTCLEANFILES += GNUmakefile

AM_CPPFLAGS += -I$(builddir)
AM_CPPFLAGS += -I$(srcdir)
AM_CPPFLAGS += -I$(PATSHOME)
AM_CPPFLAGS += -I$(PATSHOME)/ccomp/runtime/

LDADD += $(CODE_COVERAGE_LIBS)

CODE_COVERAGE_IGNORE_PATTERN =
CODE_COVERAGE_IGNORE_PATTERN += /usr/include/*
CODE_COVERAGE_IGNORE_PATTERN += /usr/include/*/*
CODE_COVERAGE_IGNORE_PATTERN += $(PATSHOME)/ccomp/runtime/*
CODE_COVERAGE_IGNORE_PATTERN += $(PATSHOME)/prelude/CATS/*

clean-local: code-coverage-clean tests-clean xats-c-clean
distclean-local: code-coverage-dist-clean ats-includes-distclean

#--------------------------------------------------------------------------

PATSOPT_DEPS =

AM_PATSOPTFLAGS =
AM_PATSOPTFLAGS += -IATS $(builddir)
AM_PATSOPTFLAGS += -IATS $(srcdir)

TOTAL_PATSOPTFLAGS =
TOTAL_PATSOPTFLAGS += $(AM_PATSOPTFLAGS)
TOTAL_PATSOPTFLAGS += $(PATSOPTFLAGS)
TOTAL_PATSOPTFLAGS += $(XPATSOPTFLAGS)

TESTS_PATSOPTFLAGS =
TESTS_PATSOPTFLAGS += -IATS $(builddir)/tests
TESTS_PATSOPTFLAGS += -IATS $(srcdir)/tests

@GNU@ define write-dependencies-file =
@GNU@	$(MKDIR_P) ats-dependencies && \
@GNU@		echo $(1): $(shell ./list-ats-dependencies $(2)) \
@GNU@			> ats-dependencies/`echo $(@) | $(SED) 's|/|_057_|g'`.mk
@GNU@ endef

.PHONY: ats-includes-distclean
ats-includes-distclean:
	-rm -f -R ats-dependencies

if DEPENDENCY_TRACKING

%_sats.c: %.sats $(PATSOPT_DEPS) list-ats-dependencies
	@$(call write-dependencies-file,$(@),$(<))
	@$(MKDIR_P) $(@D)
	$(call v,PATSOPT)$(PATSOPT) -o $(@) $(TOTAL_PATSOPTFLAGS) -s $(<)

%_dats.c: %.dats $(PATSOPT_DEPS) list-ats-dependencies
	@$(call write-dependencies-file,$(@),$(<))
	@$(MKDIR_P) $(@D)
	$(call v,PATSOPT)$(PATSOPT) -o $(@) $(TOTAL_PATSOPTFLAGS) -d $(<)

%_tests.c: %.dats $(PATSOPT_DEPS) list-ats-dependencies
	@$(call write-dependencies-file,$(@),$(<))
	@$(MKDIR_P) $(@D)
	$(call v,PATSOPT)$(PATSOPT) -o $(@) $(TOTAL_PATSOPTFLAGS) \
			$(TESTS_PATSOPTFLAGS) -d $(<)

else !DEPENDENCY_TRACKING

%_sats.c: %.sats $(PATSOPT_DEPS)
	@$(MKDIR_P) $(@D)
	$(call v,PATSOPT)$(PATSOPT) -o $(@) $(TOTAL_PATSOPTFLAGS) -s $(<)

%_dats.c: %.dats $(PATSOPT_DEPS)
	@$(MKDIR_P) $(@D)
	$(call v,PATSOPT)$(PATSOPT) -o $(@) $(TOTAL_PATSOPTFLAGS) -d $(<)

%_tests.c: %.dats $(PATSOPT_DEPS)
	@$(MKDIR_P) $(@D)
	$(call v,PATSOPT)$(PATSOPT) -o $(@) $(TOTAL_PATSOPTFLAGS) \
			$(TESTS_PATSOPTFLAGS) -d $(<)

endif !DEPENDENCY_TRACKING

%_depsprog.c: %.dats $(PATSOPT_DEPS)
	@$(MKDIR_P) $(@D)
	$(call v,PATSOPT)$(PATSOPT) -o $(@) $(TOTAL_PATSOPTFLAGS) -d $(<)

#--------------------------------------------------------------------------
#
# The ATS2 library.
#

lib_LTLIBRARIES += libats2-itp-rootfinder.la

ITP_ROOTFINDER_SATS = itp-rootfinder/SATS/itp-rootfinder.sats
ITP_ROOTFINDER_SATS_C = itp-rootfinder/SATS/itp-rootfinder_sats.c
ITP_ROOTFINDER_DATS = itp-rootfinder/DATS/itp-rootfinder.dats
ITP_ROOTFINDER_DATS_C = itp-rootfinder/DATS/itp-rootfinder_dats.c
ITP_ROOTFINDER_CATS = itp-rootfinder/CATS/itp-rootfinder.cats
ITP_ROOTFINDER_HATS = itp-rootfinder/HATS/itp-rootfinder.hats

nobase_dist_pkginclude_HEADERS =
nobase_dist_pkginclude_HEADERS += $(ITP_ROOTFINDER_SATS)
nobase_dist_pkginclude_HEADERS += $(ITP_ROOTFINDER_DATS)
nobase_dist_pkginclude_HEADERS += $(ITP_ROOTFINDER_CATS)
nobase_dist_pkginclude_HEADERS += $(ITP_ROOTFINDER_HATS)

nodist_libats2_itp_rootfinder_la_SOURCES =
nodist_libats2_itp_rootfinder_la_SOURCES += $(ITP_ROOTFINDER_SATS_C)
nodist_libats2_itp_rootfinder_la_SOURCES += $(ITP_ROOTFINDER_DATS_C)

# Make the %.o files depend on %.c files.
$(foreach source_file, \
	$(nodist_libats2_itp_rootfinder_la_SOURCES), \
	$(eval $(patsubst %.c,%.$(OBJEXT),$(source_file)): $(source_file)))

xats-c-clean:
	-rm -f itp-rootfinder/SATS/*_sats.c
	-rm -f itp-rootfinder/DATS/*_dats.c

#--------------------------------------------------------------------------
#
# Tests go here.
#

TESTS_DEPS =
TESTS_DEPS += itp-rootfinder/HATS/itp-rootfinder.hats
TESTS_DEPS += itp-rootfinder/SATS/itp-rootfinder.sats
TESTS_DEPS += itp-rootfinder/DATS/itp-rootfinder.dats

TESTS += tests/test1
EXTRA_DIST += tests/test1.dats
nodist_tests_test1_SOURCES = tests/test1_tests.c
tests_test1_DEPENDENCIES = $(TESTS_DEPS)
tests_test1_CPPFLAGS = $(AM_CPPFLAGS) -DATS_MEMALLOC_LIBC
tests_test1_LDADD = libats2-itp-rootfinder.la -lm

if HAVE_INT128
TESTS += tests/test2
EXTRA_DIST += tests/test2.dats
nodist_tests_test2_SOURCES = tests/test2_tests.c
tests_test2_DEPENDENCIES = $(TESTS_DEPS)
tests_test2_CPPFLAGS = $(AM_CPPFLAGS) -DATS_MEMALLOC_LIBC
tests_test2_LDADD = libats2-itp-rootfinder.la -lm
endif HAVE_INT128

EXTRA_PROGRAMS += $(TESTS)

tests-clean:
	-rm -f tests/*.$(OBJEXT)
	-rm -f $(addsuffix _tests.c,$(TESTS))
CLEANFILES += $(TESTS)

#--------------------------------------------------------------------------
#
# Computation of dependencies.
#

EXTRA_PROGRAMS += list-ats-dependencies
EXTRA_DIST += list-ats-dependencies.dats
CLEANFILES += list-ats-dependencies
CLEANFILES += list-ats-dependencies_depsprog.c

nodist_list_ats_dependencies_SOURCES =
nodist_list_ats_dependencies_SOURCES += list-ats-dependencies_depsprog.c
list_ats_dependencies_CPPFLAGS =
list_ats_dependencies_CPPFLAGS += $(AM_CPPFLAGS)
list_ats_dependencies_CPPFLAGS += -DATS_MEMALLOC_LIBC
list_ats_dependencies_DEPENDENCIES =
list_ats_dependencies_DEPENDENCIES += list-ats-dependencies.dats
list_ats_dependencies_LDADD =
list_ats_dependencies_LDADD += -L'$(PATSHOME)/ccomp/atslib/lib'
list_ats_dependencies_LDADD += -latslib

#--------------------------------------------------------------------------

nodist_pkgconfig_DATA += ats2-itp-rootfinder.pc

#--------------------------------------------------------------------------
# local variables:
# coding: utf-8
# end:

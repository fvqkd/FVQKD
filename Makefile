# -*- Makefile -*-

# --------------------------------------------------------------------
DUNEOPTS ?=
DUNE     := dune
ASSUMPTIONS_TIMEOUT ?= 60
CHECK_COQ_TIMEOUT ?= 300
CI_JOBS ?= 2
# If OPAM_SWITCH is set, route dune through that switch. Otherwise default to
# the Rocq 9.1 switch that scripts/setup-opam-switch creates ('qkd-rocq91').
OPAM_SWITCH ?= $(shell opam switch list -s 2>/dev/null | grep -qx qkd-rocq91 && echo qkd-rocq91)
DUNE_RUN := $(if $(OPAM_SWITCH),opam exec --switch=$(OPAM_SWITCH) --,) $(DUNE)
NAME     := coq-mathcomp-qkd
DISTDIR  := $(NAME)
SED      := sed
TAR      := tar
REPO     := default=https://opam.ocaml.org,coq-released=https://coq.inria.fr/opam/released

# --------------------------------------------------------------------
.PHONY: default setup build build-ci build-serial full-check audit-assumptions build-local opam clean mrproper dist distcheck utils

default: build

setup:
	sh ./scripts/setup-opam-switch

build:
	$(DUNE_RUN) build --root=. -j$(CI_JOBS) $(DUNEOPTS)

build-ci:
	$(DUNE_RUN) build --root=. -j$(CI_JOBS) $(DUNEOPTS)

build-serial:
	$(DUNE_RUN) build --root=. -j1 $(DUNEOPTS)

full-check:
	COQ_DEFAULT_TIMEOUT=$(CHECK_COQ_TIMEOUT) $(DUNE_RUN) build --root=. -j$(CI_JOBS) $(DUNEOPTS)
	! rg -n '^\s*(Admitted\.|admit\.|Axiom\b|Parameter\b|Conjecture\b)' src
	COQ_DEFAULT_TIMEOUT=$(CHECK_COQ_TIMEOUT) $(MAKE) audit-assumptions

audit-assumptions:
	$(DUNE_RUN) build --root=. $(DUNEOPTS) src/qkd/bb84/bb84.vo
	$(DUNE_RUN) build --root=. $(DUNEOPTS) src/qkd/example/instantiation.vo
	output=$$(printf '%s\n' \
	  'From qkd.bb84 Require Import bb84.' \
	  'From qkd.example Require Import example.' \
	  'From qkd.example Require Import instantiation.' \
	  'Print Assumptions bb84_secure.' \
	  'Print Assumptions bb84_secure_protocol.' \
	  'Print Assumptions bb84_secure_example.' \
	  'Quit.' \
	| $(DUNE_RUN) exec --root=. -- coqtop -q -quiet \
	    -R _build/default/src/utils utils \
	    -R _build/default/src/entropy entropy \
	    -R _build/default/src/eur eur \
	    -R _build/default/src/lhl lhl \
	    -R _build/default/src/qkd qkd \
	    -set "Default Timeout=$(ASSUMPTIONS_TIMEOUT)" 2>&1); \
	status=$$?; \
	printf '%s\n' "$$output"; \
	test "$$status" -eq 0 || exit "$$status"; \
	errors=$$(printf '%s\n' "$$output" | grep -E '^Error:' || true); \
	test -z "$$errors" || { echo "coqtop error(s) during assumption audit:" >&2; printf '%s\n' "$$errors" >&2; exit 1; }; \
	assumptions=$$(printf '%s\n' "$$output" \
	  | awk '/^Axioms:$$/{p=1; next} /^Coq </{p=0} p && /^[[:alnum:]_.]+[[:space:]]*(:.*)?$$/{sub(/[[:space:]]*:.*/, ""); print}'); \
	unexpected=$$(printf '%s\n' "$$assumptions" \
	  | grep -Ev '^(boolp\.propositional_extensionality|boolp\.functional_extensionality_dep|boolp\.constructive_indefinite_description)$$' \
	  || true); \
	test -z "$$unexpected" || { echo "unexpected assumption(s) in bb84_secure / bb84_secure_protocol / bb84_secure_example:" >&2; printf '%s\n' "$$unexpected" >&2; exit 1; }

utils:
	$(DUNE_RUN) build --root=. $(DUNEOPTS) src/utils/

build-local: opam
	opam config exec -- $(DUNE) build --root=. $(DUNEOPTS)

opam:
	[ -d _opam ] || opam switch create --yes --deps-only --repositories=$(REPO) .

clean:
	$(DUNE) clean --root=.
	find src -type f \( \
	    -name '*.vo'   -o -name '*.vos' -o -name '*.vok' \
	 -o -name '*.glob' -o -name '*.v.d' -o -name '*.aux' \
	\) -delete

mrproper: clean
	rm -rf _opam

dist:
	rm -rf $(DISTDIR) $(NAME).tar.gz
	./scripts/distribution $(DISTDIR) MANIFEST
	$(TAR) -czf $(NAME).tar.gz --owner=0 --group=0 $(DISTDIR)
	rm -rf $(DISTDIR)

distcheck: dist
	$(TAR) -xof $(NAME).tar.gz
	set -x; \
       $(MAKE) -C $(DISTDIR) build-local \
    && $(MAKE) -C $(DISTDIR) dist \
    && mkdir $(DISTDIR)/dist1 $(DISTDIR)/dist2 \
    && ( cd $(DISTDIR)/dist1 && tar -xof ../$(NAME).tar.gz ) \
    && ( cd $(DISTDIR)/dist2 && tar -xof ../../$(NAME).tar.gz ) \
    && diff -rq $(DISTDIR)/dist1 $(DISTDIR)/dist2 \
    || exit 1
	rm -rf $(DISTDIR)
	@echo "$(DISTDIR) is ready for distribution" | \
    $(SED) -e 1h -e 1s/./=/g -e 1p -e 1x -e '$$p' -e '$$x'

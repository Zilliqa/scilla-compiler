# Invoke `make` to build, `make clean` to clean up, etc.

OCAML_VERSION_RECOMMENDED=4.12.0
OCAMLFORMAT_VERSION=0.22.4

# Dependencies useful for developing Scilla
OPAM_DEV_DEPS := \
merlin \
ocamlformat.$(OCAMLFORMAT_VERSION) \
ocp-indent \
utop

.PHONY: default release utop dev clean

default: release

# Build one library and one standalone executable that implements
# multiple subcommands and uses the library.
# The library can be loaded in utop for interactive testing.
release:
	dune build --profile release @install
	@test -L bin || ln -s _build/install/default/bin .

dev:
	dune build --profile dev @install
	@test -L bin || ln -s _build/install/default/bin .

# Launch utop such that it finds the libraroes.
utop: release
	OCAMLPATH=_build/install/default/lib:$(OCAMLPATH) utop

fmt:
	dune build @fmt --auto-promote

# Installer and uninstaller
install : release
	dune install

uninstall : release
	dune uninstall

# Debug with ocamldebug: Build byte code instead of native code.
debug :
	dune build --profile dev src/runners/scilla_llvm.bc
	dune build --profile dev src/runners/expr_llvm.bc
	@echo "Example: ocamldebug _build/default/src/runners/scilla_llvm.bc -libdir src/stdlib -gaslimit 10000 tests/codegen/contr/simple-map.scilla"

test: dev
	ulimit -n 1024; dune exec -- tests/testsuite.exe -print-diff true

gold: dev
	ulimit -n 4096; dune exec -- tests/testsuite.exe -update-gold true

# Clean up
clean:
# Remove files produced by dune.
	dune clean

# Diagnostic builds
verbose:
	dune build --profile dev @install --verbose

opamdep-ci:
	opam init --disable-sandboxing --compiler=$(OCAML_VERSION) --yes
	eval $$(opam env)
	opam pin add scilla git+https://github.com/Zilliqa/scilla#opam_fix --yes
	opam update scilla
	opam install ./scilla-compiler.opam --deps-only --with-test --yes
	opam install ocamlformat.$(OCAMLFORMAT_VERSION) --yes

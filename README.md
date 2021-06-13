# Scilla Compiler

![Build Status](https://github.com/Zilliqa/scilla-compiler/workflows/CI/badge.svg)
[![License](https://img.shields.io/badge/License-GPLv3-blue.svg)](https://github.com/Zilliqa/scilla/blob/master/LICENSE)

<p align="center">
  <a href="https://scilla-lang.org/"><img src="https://github.com/Zilliqa/scilla/blob/master/imgs/scilla-logo-color.jpg" width="200" height="200"></a>
</p>

## Introduction
A compiler to translate Scilla to LLVM-IR. Scilla transitions in the 
generated LLVM-IR can be compiled to shared libraries and executed from
[ScillaRTL](https://github.com/Zilliqa/scilla-rtl).
The project is under active development and is not intended for production use yet.

## Building

### Prerequisites:

  - `sudo apt-get update && sudo apt-get install -yq ninja-build libboost-system-dev libboost-test-dev`

### Install Scilla_base and other dependencies

The compiler depends on Scilla base, which can be installed by following the
instructions [here](https://github.com/Zilliqa/scilla/#installing-scilla-with-opam)
After installing Scilla_base, run the following.

  - `opam install ./ --deps-only --with-test --yes`

### Building LLVM from Source

LLVM must be built with OCaml support. To install the OCaml bindings to your local
opam directory, the following CMake configuration flags must be provided
to LLVM

  - `-DLLVM_OCAML_INSTALL_PATH="~/.opam/4.12.0/lib"`: change
    the value based on your [OCaml switch](https://github.com/Zilliqa/scilla/blob/master/INSTALL.md#installing-opam-packages).
    The built OCaml bindings will be installed to this path.
  - `-DLLVM_ENABLE_RTTI=ON`: This is required by ScillaRTL.
  - `-G "Ninja"` to build LLVM using `ninja` instead of `make`.
    This is not necessary, but is usually faster.

Check if your LLVM bindings are built successfully:

  - `ninja check-llvm-bindings-ocaml`.

Install the bindings to your opam switch:

  - `ninja bindings/ocaml/install`

For convenience and CI purposes `scripts/build_install_llvm.sh` has been provided
which downloads and builds LLVM in `${HOME}` and installs it to the `4.12.0` opam
switch. You can modify and use it as necessary.

### Build the Compiler

To build and obtain the executables in the project's `bin` directory:

  - `LIBRARY_PATH=/path/to/llvm/build/lib make`

If you are using LLVM from a non-system path (because you built it
yourself, for example) then the environment variable `LIBRARY_PATH`
must be set to the directory that contains built LLVM libraries.

### Installing the compiler to your opam switch

This will install the compiler binaries to your current opam switch.
This step is not usually necessary to try out and use the compiler.

  - `make install`

This will uninstall Scilla compiler installed with the previous command.

  - `make uninstall`

## Compiling Scilla to LLVM-IR

LLVM-IR generated with the compiler can be compiled and linked into
a shared library (`clang -shared`) and executed using [ScillaRTL](https://github.com/Zilliqa/scilla-rtl).
(If you didn't install the compiler to your opam switch, you can run the binaries directly
from the `bin` directory).

Compile a full Scilla contract:

  - `scilla-llvm -libdir src/stdlib tests/codegen/contr/simple-map.scilla -gaslimit 10000`

Compile a pure Scilla expression:

  - `expr-llvm -libdir src/stdlib tests/codegen/expr/match_assign.scilexp -gaslimit 10000`

### Testsuite

The testsuite includes both Scilla expressions and full contracts for
which LLVM-IR is generated and compared against pre-generated text.

  - `make test`

# Scilla Compiler

![Build Status](https://github.com/Zilliqa/scilla-compiler/workflows/CI/badge.svg)
[![License](https://img.shields.io/badge/License-GPLv3-blue.svg)](https://github.com/Zilliqa/scilla/blob/master/LICENSE)

<p align="center">
  <a href="https://scilla-lang.org/"><img src="https://github.com/Zilliqa/scilla/blob/master/imgs/scilla-logo-color.jpg" width="200" height="200"></a>
</p>

## Introduction
A compiler to translate Scilla to LLVM-IR. Scilla transitions in the 
generated LLVM-IR can be executed with [ScillaVM](https://github.com/Zilliqa/scilla-vm).
The project is under active development and is not intended for production use yet.

## Building

### Install LLVM

Add Ubuntu repository for llvm-10. Below command line is for Ubuntu 18.04, change
suitably for your OS (see the LLVM [apt page](https://apt.llvm.org/https://apt.llvm.org/))

```
sudo add-apt-repository 'deb http://apt.llvm.org/bionic/ llvm-toolchain-bionic-10 main' -y
wget -O - https://apt.llvm.org/llvm-snapshot.gpg.key|sudo apt-key add -
```

Install LLVM-10

```
sudo apt-get install llvm-10-dev
```

### Building LLVM from Source

If you are building LLVM from source instead of from installing it via
your OS's package manager, ensure that the OCaml bindings
are built and installed. To install the OCaml bindings to your local
opam directory, the following CMake configuration flags must be provided
to LLVM

  - `-DLLVM_OCAML_INSTALL_PATH="~/.opam/4.12.0/lib"`: change
  the value based on your [OCaml switch](https://github.com/Zilliqa/scilla/blob/master/INSTALL.md#installing-opam-packages).
  The built OCaml bindings will be installed to this path.
  - `-DLLVM_ENABLE_RTTI=ON`: This is required by Scilla-VM.

To check if your LLVM bindings are built successfully, run
`ninja check-llvm-bindings-ocaml`. If that succeeds, you can install
the bindings to your opam switch using `ninja bindings/ocaml/install`
You may use `make` instead of `ninja` if you're building LLVM using `GNU Make`.

### Install Scilla_base and other dependencies

The compiler depends on Scilla base, which can be installed by following the
instructions [here](https://github.com/Zilliqa/scilla/#installing-scilla-with-opam)

```
opam install batteries
```

### Build the Compiler

To build and obtain the executables in the project's `bin` directory:

```
make
```

If you are using LLVM from a non-system path (because you built it
yourself, for example) then the environment variable `LIBRARY_PATH`
must be set to the directory that contains built LLVM libraries.

### Installing the compiler to your opam switch

This will install the compiler binaries to your current opam switch.

```
make install
```

This will uninstall Scilla compiler installed with the previous command.

```
make uninstall
```

## Compiling Scilla to LLVM-IR

LLVM-IR generated with the compiler can be run on [ScillaVM](https://github.com/Zilliqa/scilla-vm).
(If you didn't install the compiler to your opam switch, you can run the binaries directly
from the `bin` directory).

Compile a full Scilla contract:

```scilla-llvm -libdir src/stdlib tests/codegen/contr/simple-map.scilla -gaslimit 10000```

Compile a pure Scilla expression:

```expr-llvm -libdir src/stdlib tests/codegen/expr/match_assign.scilexp -gaslimit 10000```

### Testsuite

The testsuite includes both Scilla expressions and full contracts for
which LLVM-IR is generated and compared against pre-generated text.

```
make test
```

# Scilla Compiler

[![Build Status](https://travis-ci.com/Zilliqa/scilla-compiler.svg?token=7qzjATfZuxTQvRjMHPVQ&branch=master)](https://travis-ci.com/Zilliqa/scilla-compiler)
[![License](https://img.shields.io/badge/License-GPLv3-blue.svg)](https://github.com/Zilliqa/scilla/blob/master/LICENSE)

<p align="center">
  <a href="https://scilla-lang.org/"><img src="https://github.com/Zilliqa/scilla/blob/master/imgs/scilla-logo-color.jpg" width="200" height="200"></a>
</p>

## Introduction
A compiler to translate Scilla to LLVM-IR. Scilla transitions in the 
generated LLVM-IR can be executed with [ScillaVM](https://github.com/Zilliqa/scilla-vm).
The project is under active development and is not intended for production use yet.

## Building

### Install LLVM (Ubuntu 18.04)

Add Ubuntu repository for llvm-10
```
sudo add-apt-repository 'deb http://apt.llvm.org/bionic/ llvm-toolchain-bionic-10 main' -y
wget -O - https://apt.llvm.org/llvm-snapshot.gpg.key|sudo apt-key add -
```
Install LLVM-10
```
sudo apt-get install llvm-10-dev
```

### Install Scilla_base

The compiler depends on Scilla base, which can be installed by following the
instructions [here](https://github.com/Zilliqa/scilla/#installing-scilla-with-opam)

### Build the Compiler

To build and obtain the executables in the project's `bin` directory:

```
make
```

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

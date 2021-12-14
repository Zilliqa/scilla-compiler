#!/usr/bin/bash

# ./gas_verify_expr.sh scilla/bin/eval-runner scilla-compiler/bin/expr-llvm scilla-rtl/build/bin/expr-runner /media/data/scilla-compiler/src/stdlib/ scilla-compiler/tests/codegen/expr/

interpreter=$1
compiler=$2
rtlexec=$3
libdir=$4
testexprs_dir=$5

gas_limit=1000000

if [ ! -f "$interpreter" ] || [ ! -f "$compiler" ]|| [ ! -f "$rtlexec" ] || [ ! -d "$libdir" ] || [ ! -d "$testexprs_dir" ]
then
    echo "Usage: $0: /interpreter /compiler /rtlexec /libdir /test_expr_dir"
    exit 1
fi

for testexpr in "$testexprs_dir"/*.scilexp
do
    interpreter_output=$($interpreter -libdir "$libdir" -gaslimit $gas_limit "$testexpr" | grep "Gas remaining")
    $compiler -libdir "$libdir" -gaslimit $gas_limit "$testexpr" > /tmp/tmp.ll
    srtl_output=$($rtlexec -g $gas_limit /tmp/tmp.ll | grep "Gas remaining")
    if [ "$srtl_output" != "$interpreter_output" ]
    then
       echo "Mismatch for $testexpr"
    fi
done

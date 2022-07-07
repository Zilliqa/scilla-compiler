(* Filter used to filter out strings from test output when
   compared to gold output. Filters out the lines starting with
   "target triple = " and "target datalayout = " that differ
   depending on the machine the LLVM is generate by.
   Allows for `make test` to pass when run on different machines.
*)
let diff_filter s =
  Str.global_replace
    (Str.regexp "\\(target triple = .+\\)\\|\\(target datalayout = .+\\)")
    "" s

(*  Filter used to filter out strings from test output when
    compared to gold output. Filters out the lines starting with
    "target triple = " and "target datalayout = " that differ
    depending on the machine the LLVM is generate by.
    Allows for `make test` to pass when run on different machines.
*)
let diff_filter s =
  let sl = Str.split (Str.regexp "\n") s in
  let re1 = Str.regexp_string "target triple = " in
  let re2 = Str.regexp_string "target datalayout = " in
  let sl' =
    List.filter
      (fun s ->
        try
          ignore (Str.search_forward re1 s 0);
          false
        with Not_found -> true)
      sl
  in
  let sl'' =
    List.filter
      (fun s ->
        try
          ignore (Str.search_forward re2 s 0);
          false
        with Not_found -> true)
      sl'
  in
  String.concat "\n" sl''

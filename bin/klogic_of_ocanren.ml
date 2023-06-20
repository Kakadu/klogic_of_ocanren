type config =
  { mutable out_file : string
  ; mutable input_file : string
  }

let config = { out_file = "asdf.kt"; input_file = "" }

let () =
  Arg.parse
    [ "-o", Arg.String (fun s -> config.out_file <- s), "" ]
    (fun s -> config.input_file <- s)
    "";
  Klogic_of_ocanren_lib.Lib.run config.input_file config.out_file
;;

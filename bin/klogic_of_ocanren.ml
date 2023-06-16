type config =
  { mutable outfile : string
  ; mutable input_file : string
  }

let config = { outfile = "asdf.kt"; input_file = "" }

let () =
  Arg.parse
    [ "-o", Arg.String (fun s -> config.outfile <- s), "" ]
    (fun s -> config.input_file <- s)
    "";
  Klogic_of_ocanren_lib.Lib.run config.input_file
;;

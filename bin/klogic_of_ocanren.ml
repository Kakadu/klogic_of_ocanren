open Klogic_of_ocanren_lib
open Trans_config

let () =
  Arg.parse
    [ "-o", Arg.String (fun s -> config.out_file <- s), ""
    ; "-pretty", Arg.Unit (fun () -> config.pretty <- true), ""
    ; "-scheme", Arg.Unit (fun () -> config.lang <- Scheme), " Output scheme"
    ]
    (fun s -> config.input_file <- s)
    "";
  Lib.run config.input_file config.out_file
;;

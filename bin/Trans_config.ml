type config =
  { mutable out_file : string
  ; mutable input_file : string
  ; mutable pretty : bool
  }

let config = { out_file = "asdf.kt"; input_file = ""; pretty = false }

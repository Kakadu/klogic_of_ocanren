type transl_lang =
  | Scheme
  | Kotlin

type config =
  { mutable out_file : string
  ; mutable input_file : string
  ; mutable pretty : bool
  ; mutable lang : transl_lang
  }

let config = { out_file = "asdf.kt"; input_file = ""; pretty = false; lang = Kotlin }

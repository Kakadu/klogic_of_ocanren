module Make () = struct
  type config = { mutable unifications : int }

  let config = { unifications = 0 }
  let clear_unifications () = config.unifications <- 0
  let incr_counter () = config.unifications <- config.unifications + 1
end

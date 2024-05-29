type ('a, 'b) either =
  | Left of 'a
  | Right of 'b

let lft es = match es with
  | Left e -> e
  | _ -> raise (Failure "Not left")

let rht es = match es with
  | Right e -> e
  | _ -> raise (Failure "Not right")

open Io

let create_error_printer file =
  fun msg ln_opt -> 
    Printf.printf "Error: %s\n" msg ;
    if Option.is_some ln_opt then (
      let line = Option.get ln_opt in
      let lines = String.split_on_char '\n' (read_file file) in
      let printer =  print_line lines in match line with
      | 1 -> printer 0 ; printer 1
      | n when n = (List.length lines)-1 -> printer (n-2) ; printer (n-1)
      | _ ->  printer (line-2) ; printer (line-1) ; printer line
    )
    else Printf.printf "\n" ;
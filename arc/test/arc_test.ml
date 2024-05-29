
open File_tests

let tests : (string * (unit -> unit)) list = [
  "Inference tests", Inference_tests.test_all;
  "Random tests", Random_tests.run_random_tests;
]

let tests = if Array.length Sys.argv >= 2 then (
  let working_test_files_dir = Sys.argv.(1) ^ "/works/" in
  let failing_test_files_dir = Sys.argv.(1) ^ "/fails/" in
  let working_files = Sys.readdir (working_test_files_dir) |> Array.to_list |> List.map (fun f -> working_test_files_dir^f) in
  let failing_files = Sys.readdir (failing_test_files_dir) |> Array.to_list |> List.map (fun f -> failing_test_files_dir^f) in

  ("Failing type checks on files", fun _ -> List.iter failing_file_typing_test failing_files) :: 
  ("Succeding type checks on files", fun _ -> List.iter succeding_file_typing_test working_files) ::
  tests
)
else tests


let () =
  List.iter ( fun (test_title,f) ->
    Printf.printf "###%s\n" test_title;
    f ();
    Printf.printf "\n"
  ) tests
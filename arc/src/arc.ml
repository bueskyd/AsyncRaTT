
module ProgramEnv = Arclib.Program_env.Make(Example.Simulator)

module Main = Arclib.Main.Make(ProgramEnv)(Program_env_string)

let () = Main.run ()

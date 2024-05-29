
TARGET=$1

function file_content {
  cat $1 | sed 's/%/%%/g' | sed 's/\\/\\\\/g' | sed 's/\"/\\\"/g' 
}

HERE=$(dirname ${BASH_SOURCE[0]})

echo "let template = format_of_string \"" > $TARGET

echo "module Arclib = struct" >> $TARGET
echo "module Absyn = struct" >> $TARGET
file_content $HERE/absyn.ml >> $TARGET
echo "end" >> $TARGET

echo "module Runtime_value = struct" >> $TARGET
file_content $HERE/runtime_value.ml >> $TARGET
echo "end" >> $TARGET

echo "module Program_env = struct" >> $TARGET
file_content $HERE/program_env.ml >> $TARGET
echo "end" >> $TARGET
echo "end" >> $TARGET

echo "module Program_env_impl = struct %s end" >> $TARGET
echo "module Transpiled = struct %s end" >> $TARGET 

echo "module PE = Arclib.Program_env.Make(Program_env_impl)" >> $TARGET
echo "module Program = Transpiled.Make(PE)" >> $TARGET
echo "let _ = Program.run ()" >> $TARGET

echo "(*"  >> $TARGET
echo "compile using:" >> $TARGET 
echo "    'ocamlc unix.cma -thread threads.cma <file>' " >> $TARGET
echo "    or" >> $TARGET 
echo "    'ocamlopt unix.cmxa -thread threads.cmxa <file>' " >> $TARGET
echo "*)" >> $TARGET
echo "\"" >> $TARGET 

echo "let empty_template () = Printf.sprintf template \"\" \"\"" >> $TARGET
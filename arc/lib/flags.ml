

type flag_record = {
  mutable debug : bool ;
  mutable optimize : bool ;
  mutable transpile : bool
}

let flags : flag_record = {
  debug = false ;
  optimize = false ;
  transpile = false
} 

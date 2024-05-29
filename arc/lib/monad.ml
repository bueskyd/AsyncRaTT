module type State = sig
  type s
  type e
  val debug_info : (s -> string) option
end

module type Monad = sig
  type s
  type e
  type !+'a monad = M of (s -> ('a * s, e) result)
  val (>>=) : 'a monad -> ('a -> 'b monad) -> 'b monad
  val (>>>=) : 'a monad -> 'b monad -> 'b monad
  val (>=>) : 'a monad -> ('a -> 'b) -> 'b monad
  val fail : e -> 'a monad
  val map_error : (e -> e) -> 'a monad -> 'a monad
  val return : 'a -> 'a monad
  val join : 'a monad monad -> 'a monad
  val map : 'a monad -> ('a -> 'b) -> 'b monad
  val map2 : 'a monad -> 'b monad -> ('a -> 'b -> 'c) -> 'c monad
  val combine : 'a monad -> 'b monad -> ('a * 'b) monad
  val sequence : 'a monad list -> 'a list monad
  val list_map : ('a -> 'b monad) -> 'a list -> 'b list monad
  val fold_left : ('a -> 'b -> 'a monad) -> 'a -> 'b list -> 'a monad
  val undo : 'a monad -> 'a monad
  val eval_m : 'a monad -> s -> ('a * s, e) result
  val debug_print : string -> unit monad
end

module Make (S: State) = struct
  
  type s = S.s
  type e = S.e
  type 'a monad = M of (s -> ('a * s, e) result)
  
  let (>>=) (M monad) f =
    M (fun s ->
      match monad s with
      | Ok(v,s') -> 
        let M f' = f v in
        f' s'  
      | Error e -> Error e
    )

  let (>>>=) monad0 monad1 =
      monad0 >>= fun _ -> monad1

  let fail error =
    M(fun _ -> Error error)

  let map_error f monad = 
    M (fun s ->
      match monad s with
      | Ok res -> Ok res
      | Error e -> Error (f e)
    )

  let return v = M(fun s -> Ok(v,s))

  let (>=>) monad f =
      monad >>= (fun x -> return (f x))

  let join monad = monad >>= fun a -> a

  let map monad f = 
    monad >>= fun a -> f a |> return

  let map2 a b f =
      a >>= fun a -> b >>= fun b -> return (f a b)

  let combine a b =
    map2 a b (fun a b -> (a, b))

  let sequence ms =
    List.fold_right (fun m acc -> map2 m acc (fun a b -> a :: b)) ms (return [])

  let list_map f lst =
    List.map f lst |> sequence

  let fold_left f acc lst =
    List.fold_left (fun m_acc e -> m_acc >>= fun a -> f a e) (return acc) lst

  let undo (M monad) =
    M (fun s ->
      match monad s with
      | Ok(v, _) -> Ok(v,s)
      | Error e -> Error e
    )

  let eval_m (M monad) s =
    monad s
  
  let debug_print msg =
    if Flags.flags.debug then
    M (fun s -> match S.debug_info with
      | Some debug_info -> 
        Printf.printf "%s:\n%s\n%!" msg (debug_info s);
        Ok((), s)
      | None -> 
        Printf.printf "%s\n%!" msg;
        Ok((), s)
    )
    else M(fun env -> Ok((),env))   

end

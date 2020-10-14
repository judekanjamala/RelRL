(** lib.ml -- utility functions and modules *)

module Opt = struct
  include Option

  module Applicative_syntax = struct
    let ( let+ ) m k =
      match m with
      | Some e -> Some (k e)
      | None -> None

    let ( and+ ) ma mb =
      match ma, mb with
      | Some a, Some b -> Some (a,b)
      | _, _ -> None
  end

  module Monad_syntax = struct
    open Applicative_syntax
    let ( let* ) = bind
    let ( and* ) = ( and+ )
  end

  let (<|>) ma mb =
    match ma, mb with
    | None, r -> r
    | l, _ -> l

  let sequence (ma: 'a option list) : 'a list option =
    let open Monad_syntax in
    List.fold_right (fun elt acc ->
        let* p = elt and* q = acc in
        some (p :: q)
      ) ma (some [])
end

module Res = struct
  include Result

  module Applicative_syntax = struct
    let ( let+ ) m k =
      match m with
      | Ok a -> Ok (k a)
      | Error b -> Error b

    let ( and+ ) ma mb =
      match ma, mb with
      | Ok a, Ok b -> Ok (a,b)
      | Error msg, _ | _, Error msg -> Error msg
  end

  module Monad_syntax = struct
    open Applicative_syntax
    let ( let* ) = bind
    let ( and* ) = ( and+ )
  end

  let guard b msg = if b then ok () else Error msg

  let (<|>) ma mb =
    match ma, mb with
    | Error _, r -> r
    | l, _ -> l

  let sequence (ma: ('a,'b) result list) : ('a list,'b) result =
    let open Monad_syntax in
    List.fold_right (fun elt acc ->
        let* p = elt and* q = acc in
        ok (p :: q)
      ) ma (ok [])

end

let concat_map f xs = List.(flatten (map f xs))

let concat_filter_map f xs = List.(flatten (filter_map f xs))

let (%) f g x = f (g x)

let const x y = x

let flip f x y = f y x

let pair x y = (x, y)

let map_pair f (x, y) = (f x, f y)

let pair_ap (f, g) (x, y) = (f x, g y)

let uncurry f (x, y) = f x y

let curry f x y = f (x, y)

let scomb f g x = f x (g x)

let rec last = function
  | [] -> invalid_arg "last"
  | [x] -> x
  | _ :: xs -> last xs

let anyp preds e = List.exists (fun p -> p e) preds

let rec unique = function
  | [] -> true
  | x :: xs -> not (List.exists ((=) x) xs) && unique xs

let index n lst =
  let rec aux n c = function
    | [] -> raise Not_found
    | m :: ms -> if n = m then c else aux n (c+1) ms in
  aux n 0 lst

let rec prefix_satisfying p = function
  | e :: es when p e -> e :: prefix_satisfying p es
  | _ -> []

let rec unzip = function
  | [] -> [], []
  | (a, b) :: rest -> let p, q = unzip rest in (a :: p, b :: q)

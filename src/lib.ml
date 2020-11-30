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

let (%) f g x = f (g x)

let const x y = x

let flip f x y = f y x

let pair x y = (x, y)

let map_pair f (x, y) = (f x, f y)

let cross (f, g) (x, y) = (f x, g y)

let uncurry f (x, y) = f x y

let curry f x y = f (x, y)

let scomb f g x = f x (g x)

let can f x = try (f x; true) with _ -> false

let check p x = if p x then x else failwith "check"

let check_opt p x = if p x then Some x else None

let anyp preds e = List.exists (fun p -> p e) preds

let is_nil = function [] -> true | _ -> false

let rec last = function
  | [] -> invalid_arg "last"
  | [x] -> x
  | _::xs -> last xs

let rec is_unique = function
  | [] -> true
  | x :: xs -> not (List.exists ((=) x) xs) && is_unique xs

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

let rec inter xs ys =
  match xs with
  | [] -> []
  | x :: xs when List.mem x ys -> x :: inter xs ys
  | _ :: xs -> inter xs ys

let nub xs =
  let ucons xs x = if List.mem x xs then xs else x :: xs in
  List.(rev (fold_left ucons [] xs))


(* Functions from the List module brought into scope and possibly renamed. *)

let map = List.map
let rev = List.rev
let mem = List.mem
let zip = List.combine
let find = List.find
let flat = List.flatten
let assoc = List.assoc
let length = List.length
let forall = List.for_all
let exists = List.exists
let filter = List.filter
let filtermap = List.filter_map
let partition = List.partition
let tabulate f n = List.init n f

(* fold_left and fold_right with an easy to remember argument order. *)

let foldl f acc xs = List.fold_left (flip f) acc xs
let foldr f acc xs = List.fold_right f xs acc

let rec concat_map f xs =
  match xs with
  | [] -> []
  | h::t -> f h @ concat_map f t

let rec concat_filter_map f xs =
  match xs with
  | [] -> []
  | h::t ->
    let t' = concat_filter_map f t in
    match f h with None -> t' | Some h' -> h' @ t'

let rev_assoc b = find (fun (x,y) -> b=y)

let uniq_cons x ls = if mem x ls then ls else x :: ls

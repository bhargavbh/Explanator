(*******************************************************************)
(*     This is part of Explanator, it is distributed under the     *)
(*  terms of the GNU Lesser General Public License version 3       *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2018:                                                *)
(*  Bhargav Bhatt (ETH Zürich)                                     *)
(*  Dmitriy Traytel (ETH Zürich)                                   *)
(*******************************************************************)

open Str

module Int = struct type t = int let compare = compare end
module IntMap = Map.Make(Int)

(*make the list [from, from + 1, ..., to]*)
let rec ( -- ) i j =
  if i > j then [] else i :: (i + 1 -- j)

let rec take i xs = match i, xs with
  | 0, _ | _, [] -> []
  | _, x::xs -> x :: take (i - 1) xs

  let last l = List.nth l (List.length l - 1)

let sum mes = List.fold_left (fun a b -> a + mes b) 0

let rec max_list = List.fold_left max 0
let rec min_list = List.fold_left min 0

let map_filter f =
  let rec go acc = function
    | [] -> List.rev acc
    | x :: xs -> match f x with
      | None -> go acc xs
      | Some y -> go (y :: acc) xs
  in go []

let chop_while p =
  let rec go ls = function
    | [] -> (List.rev ls, [])
    | x :: xs -> if p x then go (x :: ls) xs else (List.rev ls, x :: xs)
  in go []

let drop_while p =
  let rec go = function
    | [] -> []
    | x :: xs -> if p x then go xs else x :: xs
  in go

let paren h k x = if h>k then "("^^x^^")" else x

let eat s t = s ^ String.trim t

let list_to_string indent f = function
  | [] -> indent ^ "[]"
  | [x] -> indent ^ eat "[" (f indent x ^ "]")
  | x :: xs ->
      List.fold_left (fun s el -> eat (s ^ "\n" ^ indent ^ "; ") (f indent el))
        (indent ^ eat "[ " (f indent x)) xs ^ " ]"

let substring s1 s2 =
  let re = Str.regexp_string s2
  in
    try ignore (Str.search_forward re s1 0); true
    with Not_found -> false

let remove_newline s =
  let n = String.length s in
  if n > 0 && s.[n-1] = '\n' then String.sub s 0 (n-1) else s

let word_to_string ll = String.concat "\n" (List.map (String.concat ",") ll)

let prod_le p q r s = p r s && q r s
let lex_le p q r s = p r s || (not (p s r) && q r s)
let mk_le f r s = f r <= f s

(*stolen from https://github.com/Octachron/ocaml/blob/posets_for_parmatch/typing/parmatch.ml#L1501*)
let get_mins le ps =
  let rec select_rec r = function
    | [] -> r
    | p::ps ->
      if List.exists (fun x -> le x p) r
      then select_rec r ps
      else select_rec (p :: List.filter (fun x -> not (le p x)) r) ps in
  List.rev (select_rec [] ps)


(*******************************************************************)
(*     This is part of Explanator, it is distributed under the     *)
(*  terms of the GNU Lesser General Public License version 3       *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2018:                                                *)
(*  Bhargav Bhatt (ETH Zürich)                                     *)
(*  Dmitriy Traytel (ETH Zürich)                                   *)
(*******************************************************************)

open Util
open Hashcons

type formula_ =
  | TT
  | FF
  | P of string
  | Neg of formula
  | Conj of formula * formula
  | Disj of formula * formula
  | Impl of formula * formula
  | Iff of formula * formula
  | Prev of formula
  | Once of formula
  | Historically of formula
  | Since of formula * formula
  | Next of formula
  | Always of formula
  | Eventually of formula
  | Until of formula * formula
and formula = formula_ hash_consed

let hash x = x.hkey
let head x = x.node

let m = Hashcons.create 271

let hashcons =
  let hash = function
    | TT -> Hashtbl.hash 1
    | FF -> Hashtbl.hash 0
    | P x -> Hashtbl.hash x
    | Neg f -> Hashtbl.hash (2, f.hkey)
    | Conj (f, g) -> Hashtbl.hash (3, f.hkey, g.hkey)
    | Disj (f, g) -> Hashtbl.hash (5, f.hkey, g.hkey)
    | Impl (f, g) -> Hashtbl.hash (37, f.hkey, g.hkey)
    | Iff (f, g) -> Hashtbl.hash (41, f.hkey, g.hkey)
    | Prev f -> Hashtbl.hash (7, f.hkey)
    | Once f -> Hashtbl.hash (11, f.hkey)
    | Historically f -> Hashtbl.hash (13, f.hkey)
    | Since (f, g) -> Hashtbl.hash (17, f.hkey, g.hkey)
    | Next f -> Hashtbl.hash (19, f.hkey)
    | Always f -> Hashtbl.hash (23, f.hkey)
    | Eventually f -> Hashtbl.hash (29, f.hkey)
    | Until (f, g) -> Hashtbl.hash (31, f.hkey, g.hkey) in
  let equal x y = match x, y with
    | TT, TT -> true
    | P x, P y -> x = y
    | Neg f, Neg f' | Prev f, Prev f' | Next f, Next f'
    | Once f, Once f' | Historically f, Historically f'
    | Always f, Always f' | Eventually f, Eventually f' -> f == f'
    | Conj (f, g), Conj (f', g') | Disj (f, g), Disj (f', g')
    | Impl (f, g), Impl (f', g') | Iff (f, g), Iff (f', g')
    | Since (f, g), Since (f', g') | Until (f, g), Until (f', g') -> f == f' && g == g'
    | _ -> false in
  Hashcons.hashcons hash equal m

let tt = hashcons TT
let ff = hashcons FF
let p x = hashcons (P x)
let neg f = hashcons (Neg f)
let conj f g = hashcons (Conj (f, g))
let disj f g = hashcons (Disj (f, g))
let prev f = hashcons (Prev f)
let next f = hashcons (Next f)
let since f g = hashcons (Since (f, g))
let until f g = hashcons (Until (f, g))
let eventually f = hashcons (Eventually f)
let always f = hashcons (Always f)
let once f = hashcons (Once f)
let historically f = hashcons (Historically f)
let impl f g = hashcons (Impl (f, g))
let iff f g = hashcons (Iff (f, g))
let release f g = neg (until (neg f) (neg g))
let weak_until f g = release g (disj f g)
let trigger f g = neg (since (neg f) (neg g))

let rec atoms x = match x.node with
  | TT | FF -> []
  | P x -> [x]
  | Neg f | Next f | Always f | Eventually f | Prev f | Once f | Historically f -> atoms f
  | Conj (f1, f2) | Disj (f1, f2)
  | Impl (f1, f2) | Iff (f1, f2) | Until (f1, f2) | Since (f1, f2) ->
      List.sort_uniq String.compare (List.append (atoms f1) (atoms f2))

let rec hp x = match x.node with
  | TT | FF | P _ -> 0
  | Neg f | Next f | Always f | Eventually f -> hp f
  | Conj (f1, f2) | Disj (f1, f2)
  | Impl (f1, f2) | Iff (f1, f2) | Until (f1, f2) -> max (hp f1) (hp f2)
  | Prev f | Once f | Historically f -> hp f + 1
  | Since (f1, f2) -> max (hp f1) (hp f2) + 1

let rec hf x = match x.node with
  | TT | FF | P _ -> 0
  | Neg f | Next f | Once f | Historically f -> hf f
  | Conj (f1, f2) | Disj (f1, f2)
  | Impl (f1, f2) | Iff (f1, f2) | Since (f1, f2) -> max (hf f1) (hf f2)
  | Prev f | Always f | Eventually f -> hf f + 1
  | Until (f1, f2) -> max (hf f1) (hf f2) + 1

let height f = hp f + hf f

type word = string list list
type lasso = W of word * word

type sexpl =
  | STT of int
  | SAtom of int * string
  | SNeg of vexpl
  | SDisjL of sexpl
  | SDisjR of sexpl
  | SConj of sexpl * sexpl
  | SImplL of vexpl
  | SImplR of sexpl
  | SIffS of sexpl * sexpl
  | SIffV of vexpl * vexpl
  | SPrev of sexpl
  | SOnce of int * sexpl
  | SHistorically of sexpl list
  | SNext of sexpl
  | SEventually of int * sexpl
  | SAlways of sexpl list
  | SSince of sexpl * sexpl list
  | SUntil of sexpl * sexpl list
and vexpl =
  | VFF of int
  | VAtom of int * string
  | VNeg of sexpl
  | VDisj of vexpl * vexpl
  | VConjL of vexpl
  | VConjR of vexpl
  | VImpl of sexpl * vexpl
  | VIffL of sexpl * vexpl
  | VIffR of vexpl * sexpl
  | VPrev0
  | VPrev of vexpl
  | VOnce of vexpl list
  | VHistorically of int * vexpl
  | VNext of vexpl
  | VEventually of vexpl list
  | VAlways of int * vexpl
  | VSince of vexpl * vexpl list
  | VSincew of vexpl list
  | VUntil of vexpl * vexpl list
  | VUntilw of vexpl list

type expl = S of sexpl | V of vexpl

exception VEXPL
exception SEXPL

let unS = function S p -> p | _ -> raise VEXPL
let unV = function V p -> p | _ -> raise SEXPL

let expl_to_bool = function
  | S _ -> true
  | V _ -> false

let mem_lasso (W(u, v)) i a = if i < List.length u
  then List.mem a (List.nth u i)
  else List.mem a (List.nth v ((i - List.length u) mod List.length v))

let rec search_sproof xs ys k = match xs with        (*xs is beta list*)
  | [] -> []
  | x :: xs -> List.append
      (try [S (SUntil (unS x, List.map unS (take k ys)))] with VEXPL -> [])
    (search_sproof xs ys (k+1))

let rec search_vproof xs ys k = match xs with        (*xs is alpha list*)
  | [] -> []
  | x :: xs -> List.append
      (try [V (VUntil (unV x, List.map unV (take (k + 1) ys)))] with SEXPL -> [])
    (search_vproof xs ys (k+1))

let search_proof mk f1 f2 i lv =
  let pf1s = List.map (fun k -> mk k f1) (i -- (i + lv - 1)) in
  let pf2s = List.map (fun k -> mk k f2) (i -- (i + lv - 1)) in
  List.append (search_sproof pf2s pf1s 0) (search_vproof pf1s pf2s 0)

let sappend sp' sp_f1 = match sp' with
  | SSince (sp_f2, sp_f1s) -> SSince (sp_f2, List.append sp_f1s [sp_f1])
  | SHistorically sp_f1s -> SHistorically (List.append sp_f1s [sp_f1])
  | SUntil (sp_f2, sp_f1s) -> SUntil (sp_f2, sp_f1 :: sp_f1s)
  | SAlways sp_f1s -> SAlways (sp_f1 :: sp_f1s)
  | _ -> failwith "bad arguments for sappend"

let slift = function
  | SOnce (i, sp) -> SOnce (i + 1, sp)
  | SEventually (i, sp) -> SEventually (i - 1, sp)
  | _ -> failwith "bad arguments for slift"

let vlift = function
  | VHistorically (i, vp) -> VHistorically (i + 1, vp)
  | VAlways (i, vp) -> VAlways (i - 1, vp)
  | _ -> failwith "bad arguments for vlift"

let vappend vp' vp_f2 = match vp' with
  | VSince (vp_f1, vp_f2s) -> VSince (vp_f1, List.append vp_f2s [vp_f2])
  | VSincew vp_f2s -> VSincew (List.append vp_f2s [vp_f2])
  | VOnce vp_f2s -> VOnce (List.append vp_f2s [vp_f2])
  | VUntil (vp_f1, vp_f2s) -> VUntil (vp_f1, vp_f2 :: vp_f2s)
  | VUntilw vp_f2s -> VUntilw (vp_f2 :: vp_f2s)
  | VEventually vp_f2s -> VEventually (vp_f2 :: vp_f2s)
  | _ -> failwith "bad arguments for vappend"

let doSince minimum expl_f1 expl_f2 expl_f' =
  match expl_f', expl_f1, expl_f2 with
  | V _, _, S f2 | S _, V _, S f2 -> S (SSince (f2, []))
  | V f, S _, V f2 -> V (vappend f f2)
  | V f, V f1, V f2 -> minimum (V (vappend f f2)) (V (VSince (f1, [f2])))
  | S f, S f1, S f2 -> minimum (S (sappend f f1)) (S (SSince (f2, [])))
  | S f, S f1, V _ -> S (sappend f f1)
  | S _, V f1, V f2 -> V (VSince (f1, [f2]))

let doOnce minimum i expl_g expl_f' =
  match expl_f', expl_g with
  | V f, V g -> V (vappend f g)
  | V _, S g -> S (SOnce (i, g))
  | S f, V _ -> S (slift f)
  | S f, S g -> minimum (S (slift f)) (S (SOnce (i, g)))

let doHistorically minimum i expl_g expl_f' =
  match expl_f', expl_g with
  | V f, V g -> minimum (V (vlift f)) (V (VHistorically (i, g)))
  | V f, S _ -> V (vlift f)
  | S _, V g -> V (VHistorically (i, g))
  | S f, S g -> S (sappend f g)

let doUntil minimum expl_f1 expl_f2 expl_f' =
  match expl_f', expl_f1, expl_f2 with
  | V _, _, S f2 | S _, V _, S f2 -> S (SUntil (f2, []))
  | V f, S _, V f2 -> V (vappend f f2)
  | V f, V f1, V f2 -> minimum (V (vappend f f2)) (V (VUntil (f1, [f2])))
  | S f, S f1, S f2 -> minimum (S (sappend f f1)) (S (SUntil (f2, [])))
  | S f, S f1, V _ -> S (sappend f f1)
  | S _, V f1, V f2 -> V (VUntil (f1, [f2]))

let doEventually minimum i expl_g expl_f' =
  match expl_f', expl_g with
  | V f, V g -> V (vappend f g)
  | V _, S g -> S (SEventually (i, g))
  | S f, V _ -> S (slift f)
  | S f, S g -> minimum (S (slift f)) (S (SEventually (i, g)))

let doAlways minimum i expl_g expl_f' =
  match expl_f', expl_g with
  | V f, V g -> minimum (V (vlift f)) (V (VAlways (i, g)))
  | V f, S _ -> V (vlift f)
  | S _, V g -> V (VAlways (i, g))
  | S f, S g -> S (sappend f g)

let memo_rec2 f =
  let t = ref IntMap.empty in
  let rec aux x y =
    try let tx = IntMap.find x !t in
  try Hmap.find y !tx
  with Not_found ->
    let z = f aux x y in
    tx := Hmap.add y z !tx; z
    with Not_found ->
      let z = f aux x y in
      let tx = ref Hmap.empty in
      t := IntMap.add x tx !t;
      tx := Hmap.add y z !tx;
      z
  in aux

(*size*)

let rec s_size = function
  | STT i -> 1
  | SAtom (i, _) -> 1
  | SNeg expl -> 1 + v_size expl
  | SPrev expl -> 1 + s_size expl
  | SOnce (i, expl) -> 1 + s_size expl
  | SHistorically expls -> 1 + sum s_size expls
  | SNext expl -> 1 + s_size expl
  | SEventually (i, expl) -> 1 + s_size expl
  | SAlways expls -> 1 + sum s_size expls
  | SConj (sphi, spsi) -> 1 + s_size sphi + s_size spsi
  | SDisjL sphi -> 1 + s_size sphi
  | SDisjR spsi -> 1 + s_size spsi
  | SImplL vphi -> 1 + v_size vphi
  | SImplR spsi -> 1 + s_size spsi
  | SIffS (sphi, spsi) -> 1 + s_size sphi + s_size spsi
  | SIffV (vphi, vpsi) -> 1 + v_size vphi + v_size vpsi
  | SSince (spsi, sphis) -> 1 + s_size spsi + sum s_size sphis
  | SUntil (spsi, sphis) -> 1 + s_size spsi + sum s_size sphis
and v_size = function
  | VFF i -> 1
  | VAtom (i, _) -> 1
  | VNeg sphi -> 1 + s_size sphi
  | VDisj (vphi, vpsi) -> 1 + v_size vphi + v_size vpsi
  | VConjL vphi -> 1 + v_size vphi
  | VConjR vpsi -> 1 + v_size vpsi
  | VImpl (sphi, vpsi) -> 1 + s_size sphi + v_size vpsi
  | VIffL (sphi, vpsi) -> 1 + s_size sphi + v_size vpsi
  | VIffR (vphi, spsi) -> 1 + v_size vphi + s_size spsi
  | VPrev vphi -> 1 + v_size vphi
  | VPrev0 -> 1
  | VOnce expls -> 1 + sum v_size expls
  | VHistorically (i, expl) -> 1 + v_size expl
  | VNext vphi -> 1 + v_size vphi
  | VEventually expls -> 1 + sum v_size expls
  | VAlways (i, expl) -> 1 + v_size expl
  | VSince (vphi, vpsis) -> 1 + v_size vphi + sum v_size vpsis
  | VSincew vpsis-> 1 + sum v_size vpsis
  | VUntilw vpsis -> 1 + sum v_size vpsis
  | VUntil (vphi, vpsis) -> 1 + v_size vphi + sum v_size vpsis

let size = function
  | S s_p -> s_size s_p
  | V v_p -> v_size v_p

let size_le = mk_le size

let minsize a b = if size a <= size b then a else b
let minsize_list = function
  | [] -> failwith "empty list for minsize_list"
  | x::xs -> List.fold_left minsize x xs

let optimal_proof (W (u, v)) le =
  let mem = mem_lasso (W (u, v)) in
  let lu = List.length u in
  let lv = List.length v in
  let thr f = lu + hp f * lv in
  let minimum_list ps = minsize_list (get_mins le ps) in
  let minimum a b = minimum_list [a; b] in

  (*let rec op i f = ( *)
  let op = memo_rec2 (fun op i f -> match f.node with
    | TT -> S (STT i)
    | FF -> V (VFF i)
    | P a -> if mem i a then S (SAtom (i, a)) else V (VAtom (i, a))
    | Neg f -> (match op i f with
      | S pf -> V (VNeg pf)
      | V pf -> S (SNeg pf))
    | Conj (f1, f2) -> (match op i f1, op i f2 with
      | S pf1, S pf2 -> S (SConj (pf1, pf2))
      | S pf1, V pf2 -> V (VConjR pf2)
      | V pf1, S pf2 -> V (VConjL pf1)
      | V pf1, V pf2 -> minimum (V (VConjL pf1)) (V (VConjR pf2)))
    | Disj (f1, f2) -> (match op i f1, op i f2 with
      | V pf1, V pf2 -> V (VDisj (pf1, pf2))
      | V pf1, S pf2 -> S (SDisjR pf2)
      | S pf1, V pf2 -> S (SDisjL pf1)
      | S pf1, S pf2 -> minimum (S (SDisjL pf1)) (S (SDisjR pf2)))
    | Impl (f1, f2) -> (match op i f1, op i f2 with
      | V pf1, V _ -> S (SImplL pf1)
      | V pf1, S pf2 -> minimum (S (SImplL pf1)) (S (SImplR pf2))
      | S pf1, V pf2 -> V (VImpl (pf1, pf2))
      | S _, S pf2 -> S (SImplR pf2))
    | Iff (f1, f2) -> (match op i f1, op i f2 with
      | V pf1, V pf2 -> S (SIffV (pf1, pf2))
      | V pf1, S pf2 -> V (VIffR (pf1, pf2))
      | S pf1, V pf2 -> V (VIffL (pf1, pf2))
      | S pf1, S pf2 -> S (SIffS (pf1, pf2)))
    | Prev f -> (if i = 0 then V (VPrev0) else match op (i - 1) f with
      | S pf -> S (SPrev pf)
      | V pf -> V (VPrev pf))
    | Once g ->
        let pg = op i g in
        if i = 0 then match pg with
        | S pf -> S (SOnce (0, pf))
        | V pf -> V (VOnce [pf])
        else doOnce minimum i pg (op (i - 1) f)
    | Historically g ->
        let pg = op i g in
        if i = 0 then match pg with
        | S pf -> S (SHistorically [pf])
        | V pf -> V (VHistorically (0, pf))
        else doHistorically minimum i pg (op (i - 1) f)
    | Next f -> (match op (i + 1) f with
      | S pf -> S (SNext pf)
      | V pf -> V (VNext pf))
    | Eventually g -> if i < thr g then doEventually minimum i (op i g) (op (i + 1) f)
        else let pgs = List.map (fun k -> op k g) (i -- (i + lv - 1)) in
        (try V (VEventually (List.map unV pgs)) with
        | SEXPL -> minimum_list (map_filter (fun pg ->
            match pg with S p -> Some (S (SEventually (i, p))) | _ -> None ) pgs))
    | Always g -> if i < thr g then doAlways minimum i (op i g) (op (i + 1) f)
        else let pgs = List.map (fun k -> op k g) (i -- (i + lv - 1)) in
        (try S (SAlways (List.map unS pgs)) with
        | VEXPL -> minimum_list (map_filter (fun pg ->
            match pg with V p -> Some (V (VAlways (i, p))) | _ -> None ) pgs))
    | Since (f1, f2) ->
        let pf2 = op i f2 in
        if i = 0 then match pf2 with
        | S pf -> S (SSince (pf, []))
        | V pf -> V (VSincew [pf])
        else doSince minimum (op i f1) pf2 (op (i - 1) f)
    | Until (f1, f2) ->
        match i < thr f2, i < thr f with
        | true, true -> doUntil minimum (op i f1) (op i f2) (op (i + 1) f)
        | true, _ -> minimum_list (search_proof op f1 f2 i lv)
        | _ -> minimum_list (List.append (search_proof op f1 f2 i lv)
           (try [V (VUntilw (List.map (fun k -> unV (op k f2)) (i -- (i + lv - 1))))] with
           | SEXPL -> [])))
  in op 0

(*proof checking*)

let rec s_at = function
  | STT i -> i
  | SAtom (i, _) -> i
  | SNeg vphi -> v_at vphi
  | SConj (sphi, spsi) -> s_at sphi
  | SDisjL sphi -> s_at sphi
  | SDisjR spsi -> s_at spsi
  | SImplL vphi -> v_at vphi
  | SImplR spsi -> s_at spsi
  | SIffS (sphi, spsi) -> s_at sphi
  | SIffV (vphi, vspi) -> v_at vphi
  | SPrev sphi -> s_at sphi + 1
  | SOnce (i, _) -> i
  | SHistorically sphis -> s_at (last sphis)
  | SNext sphi -> s_at sphi - 1
  | SEventually (i, _) -> i
  | SAlways sphis -> s_at (List.hd sphis)
  | SSince (spsi, sphis) -> (match sphis with
      | [] -> s_at spsi
      | _ -> s_at (last sphis))
  | SUntil (spsi, sphis) -> (match sphis with
      | [] -> s_at spsi
      | x::xs -> s_at x)
and v_at = function
  | VFF i -> i
  | VAtom (i, _) -> i
  | VNeg sphi -> s_at sphi
  | VDisj (vphi, vpsi) -> v_at vphi
  | VConjL vphi -> v_at vphi
  | VConjR vpsi -> v_at vpsi
  | VImpl (sphi, vpsi) -> s_at sphi
  | VIffL (sphi, vpsi) -> s_at sphi
  | VIffR (vphi, sspi) -> v_at vphi
  | VPrev0 -> 0
  | VPrev vphi -> v_at vphi + 1
  | VOnce vphis -> v_at (last vphis)
  | VHistorically (i, _) -> i
  | VNext vphi -> v_at vphi - 1
  | VAlways (i, _) -> i
  | VEventually vphis -> v_at (List.hd vphis)
  | VSince (vphi, vpsis) -> (match vpsis with
      | [] -> failwith "empty list of VSince"
      | _ -> v_at (last vpsis))
  | VSincew vpsis -> (match vpsis with
      | [] -> failwith "empty list of VSincew"
      | _ -> v_at (last vpsis))
  | VUntilw vpsis -> (match vpsis with
      | [] -> failwith "empty list of VUntilw"
      | x::xs -> v_at x)
  | VUntil (vphi, vpsis) -> (match vpsis with
      | [] -> failwith "empty list of VUntil"
      | x::xs -> v_at x)

let p_at = function
| S s_p -> s_at s_p
| V v_p -> v_at v_p

let check_proof (W(u, v)) =
  let mem = mem_lasso (W(u, v)) in
  let lu = List.length u in
  let lv = List.length v in
  let thr f = lu + hp f * lv in

  let rec s_go f p = match f.node, p with
    | TT, STT _ -> true
    | P x, SAtom (i, y) -> x = y && mem i x
    | Neg phi, SNeg vphi -> v_go phi vphi
    | Conj (phi, psi), SConj (sphi, spsi) -> s_go phi sphi && s_go psi spsi && s_at sphi = s_at spsi
    | Disj (phi, psi), SDisjL sphi -> s_go phi sphi
    | Disj (phi, psi), SDisjR spsi -> s_go psi spsi
    | Impl (phi, psi), SImplL vphi -> v_go phi vphi
    | Impl (phi, psi), SImplR spsi -> s_go psi spsi
    | Iff (phi, psi), SIffS (sphi, spsi) -> s_go phi sphi && s_go psi spsi && s_at sphi = s_at spsi
    | Iff (phi, psi), SIffV (vphi, vpsi) -> v_go phi vphi && v_go psi vpsi && v_at vphi = v_at vpsi
    | Prev phi, SPrev sphi -> s_go phi sphi
    | Once phi, SOnce (i, sphi) -> s_at sphi <= i && s_go phi sphi
    | Historically phi, (SHistorically sphis as sf) ->
        List.map s_at sphis = 0 -- s_at sf && List.for_all (s_go phi) sphis
    | Next phi, SNext sphi -> s_go phi sphi
    | Eventually phi, SEventually (i, sphi) -> i <= s_at sphi && s_go phi sphi
    | Always phi, (SAlways sphis as sf) ->
        let i = s_at sf in
        List.map s_at sphis = i -- (max i (thr phi) + lv - 1) && List.for_all (s_go phi) sphis
    | Since (phi, psi), (SSince (spsi, sphis) as sf) ->
        let i = s_at sf in
        let j = s_at spsi in
        List.map s_at sphis = j + 1 -- i && s_go psi spsi && List.for_all (s_go phi) sphis
    | Until (phi, psi), (SUntil (spsi, sphis) as sf) ->
        let i = s_at sf in
        let j = s_at spsi in
        List.map s_at sphis = i -- (j - 1) && s_go psi spsi && List.for_all (s_go phi) sphis
    | _ -> false
  and v_go f p = match f.node, p with
    | FF, VFF _ -> true
    | P x, VAtom (i, y) -> x = y && not (mem i x)
    | Neg phi, VNeg sphi -> s_go phi sphi
    | Conj (phi, psi), VConjL vphi -> v_go phi vphi
    | Conj (phi, psi), VConjR vpsi -> v_go psi vpsi
    | Disj (phi, psi), VDisj (vphi, vpsi) -> v_go phi vphi && v_go psi vpsi && v_at vphi = v_at vpsi
    | Impl (phi, psi), VImpl (sphi, vpsi) -> s_go phi sphi && v_go psi vpsi && s_at sphi = v_at vpsi
    | Iff (phi, psi), VIffL (sphi, vpsi) -> s_go phi sphi && v_go psi vpsi && s_at sphi = v_at vpsi
    | Iff (phi, psi), VIffR (vphi, spsi) -> v_go phi vphi && s_go psi spsi && v_at vphi = s_at spsi
    | Prev phi, VPrev vphi -> v_go phi vphi
    | Prev phi, VPrev0 -> true
    | Once phi, (VOnce vphis as vf) ->
        List.map v_at vphis = 0 -- v_at vf && List.for_all (v_go phi) vphis
    | Historically phi, VHistorically (i, vphi) -> v_at vphi <= i && v_go phi vphi
    | Next phi, VNext vphi -> v_go phi vphi
    | Eventually phi, (VEventually vphis as vf) ->
        let i = v_at vf in
        List.map v_at vphis = i -- (max i (thr phi) + lv - 1) && List.for_all (v_go phi) vphis
    | Always phi, VAlways (i, vphi) -> i <= v_at vphi && v_go phi vphi
    | Since (phi, psi), (VSince (vphi, vpsis) as vf) ->
        let i = v_at vf in
        let j = v_at vphi in
        j <= i && List.map v_at vpsis = j -- i && v_go phi vphi && List.for_all (v_go psi) vpsis
    | Since (phi, psi), (VSincew vpsis as vf) ->
        let i = v_at vf in
        List.map v_at vpsis = 0 -- i && List.for_all (v_go psi) vpsis
    | Until (phi, psi), (VUntil (vphi, vpsis) as vf) ->
        let i = v_at vf in
        let j = v_at vphi in
        i <= j && List.map v_at vpsis = i -- j && v_go phi vphi && List.for_all (v_go psi) vpsis
    | Until (phi, psi), (VUntilw vpsis as vf) ->
        let i = v_at vf in
        List.map v_at vpsis = i -- (max i (thr psi) + lv - 1) && List.for_all (v_go psi) vpsis
    | _ -> false in
  let go f = function
    | S p -> s_go f p
    | V p -> v_go f p in
  go

(*width*)

let rec s_high = function
  | STT i -> i
  | SAtom (i, _) -> i
  | SNeg vphi -> v_high vphi
  | SConj (sphi, spsi) -> max (s_high sphi) (s_high spsi)
  | SDisjL sphi -> s_high sphi
  | SDisjR spsi -> s_high spsi
  | SImplL vphi -> v_high vphi
  | SImplR spsi -> s_high spsi
  | SIffS (sphi, spsi) -> max (s_high sphi) (s_high spsi)
  | SIffV (vphi, vpsi) -> max (v_high vphi) (v_high vpsi)
  | SPrev sphi -> max (s_at (SPrev sphi)) (s_high sphi)
  | SOnce (i, sphi) -> max i (s_high sphi)
  | SHistorically sphis -> max_list (List.map s_high sphis)
  | SNext sphi -> max (s_at (SNext sphi)) (s_high sphi)
  | SEventually (i, sphi) -> max i (s_high sphi)
  | SAlways sphis -> max_list (List.map s_high sphis)
  | SSince (spsi, sphis) -> max (s_high spsi) (max_list (List.map s_high sphis))
  | SUntil (spsi, sphis) -> max (s_high spsi) (max_list (List.map s_high sphis))
and v_high p = match p with
  | VFF i -> i
  | VAtom (i, _) -> i
  | VNeg sphi -> s_high sphi
  | VDisj (vphi, vpsi) -> max (v_high vphi) (v_high vpsi)
  | VConjL vphi -> v_high vphi
  | VConjR vpsi -> v_high vpsi
  | VImpl (sphi, vpsi) -> max (s_high sphi) (v_high vpsi)
  | VIffL (sphi, vpsi) -> max (s_high sphi) (v_high vpsi)
  | VIffR (vphi, spsi) -> max (v_high vphi) (s_high spsi)
  | VPrev vphi -> max (v_at (VPrev vphi)) (v_high vphi)
  | VPrev0 -> 0
  | VHistorically (i, vphi) -> max i (v_high vphi)
  | VOnce vphis -> max_list (List.map v_high vphis)
  | VNext vphi -> max (v_at (VNext vphi)) (v_high vphi)
  | VAlways (i, vphi) -> max i (v_high vphi)
  | VEventually vphis -> max_list (List.map v_high vphis)
  | VSince (vphi, vpsis) -> max (v_high vphi) (max_list (List.map v_high vpsis))
  | VSincew vpsis-> max_list (List.map v_high vpsis)
  | VUntilw vpsis -> max_list (List.map v_high vpsis)
  | VUntil (vphi, vpsis) -> max (v_high vphi) (max_list (List.map v_high vpsis))

let rec s_low = function
  | STT i -> i
  | SAtom (i, _) -> i
  | SNeg vphi -> v_low vphi
  | SConj (sphi, spsi) -> min (s_low sphi) (s_low spsi)
  | SDisjL sphi -> s_low sphi
  | SDisjR spsi -> s_low spsi
  | SImplL vphi -> v_low vphi
  | SImplR spsi -> s_low spsi
  | SIffS (sphi, spsi) -> min (s_low sphi) (s_low spsi)
  | SIffV (vphi, vpsi) -> min (v_low vphi) (v_low vpsi)
  | SPrev sphi -> min (s_at (SPrev sphi)) (s_low sphi)
  | SOnce (i, sphi) -> min i (s_low sphi)
  | SHistorically sphis -> min_list (List.map s_low sphis)
  | SNext sphi -> min (s_at (SNext sphi)) (s_low sphi)
  | SEventually (i, sphi) -> min i (s_low sphi)
  | SAlways sphis -> min_list (List.map s_low sphis)
  | SSince (spsi, sphis) -> min (s_low spsi) (min_list (List.map s_low sphis))
  | SUntil (spsi, sphis) -> min (s_low spsi) (min_list (List.map s_low sphis))
and v_low p = match p with
  | VFF i -> i
  | VAtom (i, _) -> i
  | VNeg sphi -> s_low sphi
  | VDisj (vphi, vpsi) -> min (v_low vphi) (v_low vpsi)
  | VConjL vphi -> v_low vphi
  | VConjR vpsi -> v_low vpsi
  | VImpl (sphi, vpsi) -> min (s_low sphi) (v_low vpsi)
  | VIffL (sphi, vpsi) -> min (s_low sphi) (v_low vpsi)
  | VIffR (vphi, spsi) -> min (v_low vphi) (s_low spsi)
  | VPrev vphi -> min (v_at (VPrev vphi)) (v_low vphi)
  | VPrev0 -> 0
  | VHistorically (i, vphi) -> min i (v_low vphi)
  | VOnce vphis -> min_list (List.map v_low vphis)
  | VNext vphi -> min (v_at (VNext vphi)) (v_low vphi)
  | VAlways (i, vphi) -> min i (v_low vphi)
  | VEventually vphis -> min_list (List.map v_low vphis)
  | VSince (vphi, vpsis) -> min (v_low vphi) (min_list (List.map v_low vpsis))
  | VSincew vpsis -> min_list (List.map v_low vpsis)
  | VUntilw vpsis -> min_list (List.map v_low vpsis)
  | VUntil (vphi, vpsis) -> min (v_low vphi) (min_list (List.map v_low vpsis))

let high p = match p with
  | S s_p -> s_high s_p
  | V v_p -> v_high v_p

let low p = match p with
  | S s_p -> s_low s_p
  | V v_p -> v_low v_p

(*let width p = high p - low p  *)

let high_le = mk_le high
let low_le = mk_le (fun p -> - low p)

(*pred*)

let rec s_pred = function
  | STT i -> 0
  | SAtom (i, _) -> 1
  | SNeg expl -> v_pred expl
  | SPrev expl -> s_pred expl
  | SOnce (i, expl) -> s_pred expl
  | SHistorically expls -> sum s_pred expls
  | SNext expl -> s_pred expl
  | SEventually (i, expl) -> s_pred expl
  | SAlways expls -> sum s_pred expls
  | SConj (sphi, spsi) -> s_pred sphi + s_pred spsi
  | SDisjL sphi -> s_pred sphi
  | SDisjR spsi -> s_pred spsi
  | SImplL vphi -> v_pred vphi
  | SImplR spsi -> s_pred spsi
  | SIffS (sphi, spsi) -> s_pred sphi + s_pred spsi
  | SIffV (vphi, vpsi) -> v_pred vphi + v_pred vpsi
  | SSince (spsi, sphis) -> s_pred spsi + sum s_pred sphis
  | SUntil (spsi, sphis) -> s_pred spsi + sum s_pred sphis
and v_pred = function
  | VFF i -> 0
  | VAtom (i, _) -> 1
  | VNeg sphi -> s_pred sphi
  | VDisj (vphi, vpsi) -> v_pred vphi + v_pred vpsi
  | VConjL vphi -> v_pred vphi
  | VConjR vpsi -> v_pred vpsi
  | VImpl (sphi, vpsi) -> s_pred sphi + v_pred vpsi
  | VIffL (sphi, vpsi) -> s_pred sphi + v_pred vpsi
  | VIffR (vphi, spsi) -> v_pred vphi + s_pred spsi
  | VPrev vphi -> v_pred vphi
  | VPrev0 -> 0
  | VOnce expls -> sum v_pred expls
  | VHistorically (i, expl) -> v_pred expl
  | VNext vphi -> v_pred vphi
  | VEventually expls -> sum v_pred expls
  | VAlways (i, expl) -> v_pred expl
  | VSince (vphi, vpsis) -> v_pred vphi + sum v_pred vpsis
  | VSincew vpsis-> sum v_pred vpsis
  | VUntilw vpsis -> sum v_pred vpsis
  | VUntil (vphi, vpsis) -> v_pred vphi + sum v_pred vpsis

let predicates = function
  | S s_p -> s_pred s_p
  | V v_p -> v_pred v_p

let predicates_le = mk_le predicates

let mem_expl (i,a) =
  let rec s_mem = function
    | STT i -> false
    | SAtom (j, b) -> i = j && a = b
    | SNeg expl -> v_mem expl
    | SPrev expl -> s_mem expl
    | SOnce (i, expl) -> s_mem expl
    | SHistorically expls -> List.exists s_mem expls
    | SNext expl -> s_mem expl
    | SEventually (i, expl) -> s_mem expl
    | SAlways expls -> List.exists s_mem expls
    | SConj (sphi, spsi) -> s_mem sphi || s_mem spsi
    | SDisjL sphi -> s_mem sphi
    | SDisjR spsi -> s_mem spsi
    | SImplL vphi -> v_mem vphi
    | SImplR spsi -> s_mem spsi
    | SIffS (sphi, spsi) -> s_mem sphi || s_mem spsi
    | SIffV (vphi, vpsi) -> v_mem vphi || v_mem vpsi
    | SSince (spsi, sphis) -> s_mem spsi || List.exists s_mem sphis
    | SUntil (spsi, sphis) -> s_mem spsi || List.exists s_mem sphis
  and v_mem = function
    | VFF i -> false
    | VAtom (j, b) -> i = j && a = b
    | VNeg sphi -> s_mem sphi
    | VDisj (vphi, vpsi) -> v_mem vphi || v_mem vpsi
    | VConjL vphi -> v_mem vphi
    | VConjR vpsi -> v_mem vpsi
    | VImpl (sphi, vpsi) -> s_mem sphi || v_mem vpsi
    | VIffL (sphi, vpsi) -> s_mem sphi || v_mem vpsi
    | VIffR (vphi, spsi) -> v_mem vphi || s_mem spsi
    | VPrev vphi -> v_mem vphi
    | VPrev0 -> false
    | VOnce expls -> List.exists v_mem expls
    | VHistorically (i, expl) -> v_mem expl
    | VNext vphi -> v_mem vphi
    | VEventually expls -> List.exists v_mem expls
    | VAlways (i, expl) -> v_mem expl
    | VSince (vphi, vpsis) -> v_mem vphi || List.exists v_mem vpsis
    | VSincew vpsis-> List.exists v_mem vpsis
    | VUntilw vpsis -> List.exists v_mem vpsis
    | VUntil (vphi, vpsis) -> v_mem vphi || List.exists v_mem vpsis in
  function
    | S s_p -> s_mem s_p
    | V v_p -> v_mem v_p
let mem_expl p i a = mem_expl (i,a) p

(*printing*)

let rec s_to_string indent p =
  let indent' = "\t" ^ indent in
  match p with
  | STT i -> Printf.sprintf "%strue{%d}" indent i
  | SAtom (i, a) -> Printf.sprintf "%s%s{%d}" indent a i
  | SNeg vphi -> Printf.sprintf "%sSNeg{%d}\n%s" indent (s_at p) (v_to_string indent' vphi)
  | SConj (sphi, spsi) -> Printf.sprintf "%sSConj{%d}\n%s\n%s)" indent (s_at p) (s_to_string indent' sphi) (s_to_string indent' spsi)
  | SDisjL sphi -> Printf.sprintf "%sSDisjL{%d}\n%s" indent (s_at p) (s_to_string indent' sphi)
  | SDisjR spsi -> Printf.sprintf "%sSDisjR{%d}\n%s" indent (s_at p) (s_to_string indent' spsi)
  | SImplL vphi -> Printf.sprintf "%sSImplL{%d}\n%s" indent (s_at p) (v_to_string indent' vphi)
  | SImplR spsi -> Printf.sprintf "%sSImplR{%d}\n%s" indent (s_at p) (s_to_string indent' spsi)
  | SIffS (sphi, spsi) -> Printf.sprintf "%sSIffS{%d}\n%s\n%s)" indent (s_at p) (s_to_string indent' sphi) (s_to_string indent' spsi)
  | SIffV (vphi, vpsi) -> Printf.sprintf "%sSIffV{%d}\n%s\n%s)" indent (s_at p) (v_to_string indent' vphi) (v_to_string indent' vpsi)
  | SPrev sphi -> Printf.sprintf "%sSPrev{%d}\n%s" indent (s_at p) (s_to_string indent' sphi)
  | SOnce (_, sphi) -> Printf.sprintf "%sSOnce{%d}\n%s" indent (s_at p) (s_to_string indent' sphi)
  | SHistorically sphis -> Printf.sprintf "%sSHistorically{%d}\n%s" indent (s_at p) (list_to_string indent' s_to_string sphis)
  | SNext sphi -> Printf.sprintf "%sSNext{%d}\n%s" indent (s_at p) (s_to_string indent' sphi)
  | SEventually (_, sphi) -> Printf.sprintf "%sSEventually{%d}\n%s" indent (s_at p) (s_to_string indent' sphi)
  | SAlways sphis -> Printf.sprintf "%sSAlways{%d}\n%s" indent (s_at p) (list_to_string indent' s_to_string sphis)
  | SSince (spsi, sphis) ->
      Printf.sprintf "%sSSince{%d}\n%s\n%s" indent (s_at p) (s_to_string indent' spsi) (list_to_string indent' s_to_string sphis)
  | SUntil (spsi, sphis) ->
      Printf.sprintf "%sSUntil{%d}\n%s\n%s" indent (s_at p) (list_to_string indent' s_to_string sphis) (s_to_string indent' spsi)
and v_to_string indent p =
  let indent' = "\t" ^ indent in
  match p with
  | VFF i -> Printf.sprintf "%sfalse{%d}" indent i
  | VAtom (i, a) -> Printf.sprintf "%s!%s{%d}" indent a i
  | VNeg sphi -> Printf.sprintf "%sVNeg{%d}\n%s" indent (v_at p) (s_to_string indent' sphi)
  | VConjL vphi -> Printf.sprintf "%sVConjL{%d}\n%s" indent (v_at p) (v_to_string indent' vphi)
  | VConjR vpsi -> Printf.sprintf "%sVConjR{%d}\n%s" indent (v_at p) (v_to_string indent' vpsi)
  | VDisj (vphi, vpsi) -> Printf.sprintf "%sVDisj{%d}\n%s\n%s" indent (v_at p) (v_to_string indent' vphi) (v_to_string indent' vpsi)
  | VImpl (sphi, vpsi) -> Printf.sprintf "%sVImpl{%d}\n%s\n%s)" indent (v_at p) (s_to_string indent' sphi) (v_to_string indent' vpsi)
  | VIffL (sphi, vpsi) -> Printf.sprintf "%sVIffL{%d}\n%s\n%s)" indent (v_at p) (s_to_string indent' sphi) (v_to_string indent' vpsi)
  | VIffR (vphi, spsi) -> Printf.sprintf "%sVIffR{%d}\n%s\n%s)" indent (v_at p) (v_to_string indent' vphi) (s_to_string indent' spsi)
  | VPrev0 -> Printf.sprintf "%sVPrev{0}" indent'
  | VPrev vphi -> Printf.sprintf "%sVPrev{%d}\n%s" indent (v_at p) (v_to_string indent' vphi)
  | VOnce vphis -> Printf.sprintf "%sVOnce{%d}\n%s" indent (v_at p) (list_to_string indent' v_to_string vphis)
  | VHistorically (_, vphi) -> Printf.sprintf "%sVHistorically{%d}\n%s" indent (v_at p) (v_to_string indent' vphi)
  | VNext vphi -> Printf.sprintf "%sVNext{%d}\n%s" indent (v_at p) (v_to_string indent' vphi)
  | VEventually vphis -> Printf.sprintf "%sVEventually{%d}\n%s" indent (v_at p) (list_to_string indent' v_to_string vphis)
  | VAlways (_, vphi) -> Printf.sprintf "%sVAlways{%d}\n%s" indent (v_at p) (v_to_string indent' vphi)
  | VSince (vphi, vpsis) ->
      Printf.sprintf "%sVSince{%d}\n%s\n%s" indent (v_at p) (v_to_string indent' vphi) (list_to_string indent' v_to_string vpsis)
  | VUntil (vphi, vpsis) ->
      Printf.sprintf "%sVUntil{%d}\n%s\n%s" indent (v_at p) (list_to_string indent' v_to_string vpsis) (v_to_string indent' vphi)
  | VSincew vpsis ->
      Printf.sprintf "%sVSincew{%d}\n%s" indent (v_at p) (list_to_string indent' v_to_string vpsis)
  | VUntilw vpsis ->
      Printf.sprintf "%sVUntilw{%d}\n%s" indent (v_at p) (list_to_string indent' v_to_string vpsis)

let to_string = function
  | S p -> s_to_string "" p
  | V p -> v_to_string "" p

let rec formula_to_string l f = match f.node with
  | P x -> Printf.sprintf "%s" x
  | TT -> Printf.sprintf "⊤"
  | FF -> Printf.sprintf "⊥"
  | Conj (f, g) -> Printf.sprintf (paren l 4 "%a ∧ %a") (fun x -> formula_to_string 4) f (fun x -> formula_to_string 4) g
  | Disj (f, g) -> Printf.sprintf (paren l 3 "%a ∨ %a") (fun x -> formula_to_string 3) f (fun x -> formula_to_string 4) g
  | Impl (f, g) -> Printf.sprintf (paren l 2 "%a → %a") (fun x -> formula_to_string 2) f (fun x -> formula_to_string 4) g
  | Iff (f, g) -> Printf.sprintf (paren l 1 "%a ↔ %a") (fun x -> formula_to_string 1) f (fun x -> formula_to_string 4) g
  | Neg f -> Printf.sprintf "¬%a" (fun x -> formula_to_string 5) f
  | Prev f -> Printf.sprintf (paren l 5 "● %a") (fun x -> formula_to_string 5) f
  | Once f -> Printf.sprintf (paren l 5 "⧫ %a") (fun x -> formula_to_string 5) f
  | Historically f -> Printf.sprintf (paren l 5 "■ %a") (fun x -> formula_to_string 5) f
  | Next f -> Printf.sprintf (paren l 5 "○ %a") (fun x -> formula_to_string 5) f
  | Eventually f -> Printf.sprintf (paren l 5 "◊ %a") (fun x -> formula_to_string 5) f
  | Always f -> Printf.sprintf (paren l 5 "□ %a") (fun x -> formula_to_string 5) f
  | Since (f, g) -> Printf.sprintf (paren l 0 "%a S %a") (fun x -> formula_to_string 5) f (fun x -> formula_to_string 5) g
  | Until (f, g) -> Printf.sprintf (paren l 0 "%a U %a") (fun x -> formula_to_string 5) f (fun x -> formula_to_string 5) g
let formula_to_string = formula_to_string 0

let lasso_to_string (W (u, v)) =
  if u = [] then "u =\nv =\n" ^ word_to_string v
  else "u =\n" ^ word_to_string u ^ "\nv =\n" ^ word_to_string v

let length_pair_lasso (W (u,v)) = (List.length u, List.length v)
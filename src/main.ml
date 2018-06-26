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
open Explanator
open Ltl_parser
open Ltl_lexer

exception EXIT

let measure_ref = ref None
let fmla_ref = ref (disj (always (eventually (p "p"))) (eventually (conj (p "p") (next (p "q")))))
let log_ref = ref stdin
let out_ref = ref stdout
let full_ref = ref true
let nusmv = ref false
let filter_atoms = ref false

let usage () = Format.eprintf
"Example usage: explanator -measure size -fmla test.fmla -log test.log -out test.out
Arguments:
\t -nusmv   - parse formula and lasso word from nusmv's output log
\t -ap      - output only the \"responsible atomic proposition\" view
\t -filter  - remove those atoms from the trace that do not occur in the formula (only nusmv)
\t -O
\t\t size   - optimize proof size (default)
\t\t high   - optimize highest time-point occuring in a proof (lower is better)
\t\t predicates  - optimize multiset cardinality of atomic predicates
\t\t none   - give any proof
\t -fmla
\t\t <file> or <string> - formula to be explained (if none given some default formula will be used)\n
\t -log
\t\t <file> - log file (default: stdin)
\t -out
\t\t <file> - output file where the explanation is printed to (default: stdout)\n%!"; raise EXIT

let measure_error () =
  Format.eprintf "mode should be either of \"size\", \"high\", \"pred\", or \"none\" (without quotes)\n%!";
  raise EXIT

let process_args =
  let rec go = function
    | ("-nusmv" :: args) ->
        nusmv := true;
        go args
    | ("-filter" :: args) ->
        filter_atoms := true;
        go args
    | ("-ap" :: args) ->
        full_ref := false;
        go args
    | ("-O" :: mode :: args) ->
        let mode =
          match mode with
          | "size" | "SIZE" | "Size" -> size_le
          | "high" | "HIGH" | "High" -> high_le
          | "pred" | "PRED" | "Pred" -> predicates_le
          | "none" | "NONE" | "None" -> (fun _ _ -> true)
          | _ -> measure_error () in
        measure_ref := (match !measure_ref with
          | None -> Some mode
          | Some mode' -> Some (prod_le mode mode'));
        go args
    | ("-Olex" :: mode :: args) ->
        let mode =
          match mode with
          | "size" | "SIZE" | "Size" -> size_le
          | "high" | "HIGH" | "High" -> high_le
          | "pred" | "PRED" | "Pred" -> predicates_le
          | "none" | "NONE" | "None" -> (fun _ _ -> true)
          | _ -> measure_error () in
        measure_ref := (match !measure_ref with
          | None -> Some mode
          | Some mode' -> Some (lex_le mode mode'));
        go args
    | ("-log" :: logfile :: args) ->
        log_ref := open_in logfile;
        go args
    | ("-fmla" :: fmlafile :: args) ->
        (try
          let in_ch = open_in fmlafile in
          fmla_ref := Ltl_parser.formula Ltl_lexer.token (Lexing.from_channel in_ch);
          close_in in_ch
        with
          _ -> fmla_ref := Ltl_parser.formula Ltl_lexer.token (Lexing.from_string fmlafile));
        go args
    | ("-out" :: outfile :: args) ->
        out_ref := open_out outfile;
        go args
    | [] -> ()
    | _ -> usage () in
  go

let read_lines ic : string list =
  let try_read () =
    try Some (input_line ic) with End_of_file -> None in
  let rec loop acc = match try_read () with
    | Some s -> loop (s :: acc)
    | None -> close_in ic; List.rev acc in
  loop []

let parse_nusmv_output ch =
  let ls = List.map remove_newline (read_lines ch) in
  let f = match List.find_opt (fun l -> substring l "evaluating LTL specification") ls with
    | None -> !fmla_ref
    | Some fl -> Ltl_parser.formula Ltl_lexer.token (Lexing.from_string
        (String.sub fl 29 (String.length fl - 29))) in
  let atms = atoms f in
  let btms = List.filter (fun a -> not (substring a "=")) atms in
  let btms0 = List.map (fun a -> a ^ "=0") btms in
  let btms1 = List.map (fun a -> a ^ "=1") btms in
  let ls = List.map (fun l -> String.concat "" (String.split_on_char ' ' l))
    (drop_while (fun l -> not (substring l "Loop") && not (substring l "<-")) ls) in
  let rec next_char = function
    | [] -> None
    | (l :: ls) -> if substring l "Loop" then None
      else if substring l "Input:" then
        next_char (drop_while (fun l -> not (substring l "Loop") && not (String.contains l '<')) ls)
      else if substring l "State:" then
        Some (chop_while (fun l -> not (substring l "Loop") && not (String.contains l '<') && not (String.contains l '#')) ls)
      else None in
  let rec next_word ls cs =
    match next_char ls with
    | None -> (List.rev cs, ls)
    | Some (c, ls) -> next_word ls (c :: cs) in
  let (rawu, ls) = next_word ls [] in
  let (rawv, _) = next_word (List.tl ls) [] in
  (*let _ = List.iter (Format.printf "u: %s\n") (List.map (String.concat ",") rawu) in*)
  (*let _ = List.iter (Format.printf "v: %s\n") (List.map (String.concat ",") rawv) in*)
  let name_of x = List.hd (String.split_on_char '=' x) in
  let enrich_one prev curr = List.merge String.compare curr
    (List.filter (fun p -> not (List.exists (fun c -> name_of p = name_of c) curr)) prev) in
  let enrich prev = List.fold_left (fun (prev, u) curr ->
    let l = enrich_one prev curr in (l, l :: u)) (prev, []) in
  let (lastu, revu) = enrich [] rawu in
  let (_, revv) = enrich lastu rawv in
  let bsimplify x =
    if List.mem x btms0 then None
    else if List.mem x btms1 then Some (name_of x)
    else if !filter_atoms then if List.mem x atms then Some x else None else Some x in
  let normalize u = List.map (fun xs -> List.sort String.compare (map_filter bsimplify xs)) u in
  f, W (normalize (List.rev revu), if revv = [] then [[]] else normalize (List.rev revv))

let parse_lasso ch =
  let ls = List.map remove_newline (read_lines ch) in
  let split l = List.map String.trim (String.split_on_char ',' l) in
  let (_, u, v) = List.fold_right (fun l (b, u, v) ->
    if b && (substring l "v =" || substring l "Loop") then (false, u, v)
    else if b then (b, u, split l :: v)
    else if substring l "u =" then (b, u, v)
    else (b, split l :: u, v)) ls (true, [], []) in
  W (List.map (List.sort String.compare) u,
    if v = [] then [[]] else List.map (List.sort String.compare) v)

let visualize (W(u,v) as l) f p =
  let (ulen, vlen) = length_pair_lasso l in
  let n = ulen + if high p < ulen then 0
    else vlen * int_of_float (ceil (float_of_int (high p + 1 - ulen) /. float_of_int vlen)) in
  let alph = List.sort_uniq String.compare (List.concat (atoms f :: List.append u v)) in
  let maxlen = max_list (List.map String.length alph) in
  let pad a = a ^ String.make (maxlen - String.length a) ' ' ^ "|" in
  let col = match p with S _ -> "42" | V _ -> "41" in
  let highlight s = "\027[" ^ col ^ "m" ^ s ^ "\027[0m" in
  let mk_cell a i =
    (if i >= ulen && ((i - ulen) mod vlen) = 0 then "|" else "") ^
    (if mem_expl p i a then highlight else (fun x -> x))
    (if mem_lasso l i a then "X" else " ") in
  let mk_line a = pad a ^ String.concat "" (List.map (mk_cell a) (0 -- (n - 1))) ^ "|" in
  String.concat "\n" (List.map mk_line alph)

let _ =
  try
    process_args (List.tl (Array.to_list Sys.argv));
    let f, l = if !nusmv then parse_nusmv_output !log_ref else !fmla_ref, parse_lasso !log_ref in
    let p = optimal_proof l (match !measure_ref with None -> size_le | Some mode -> mode) f in
    let (ulen, vlen) = length_pair_lasso l in
    if !full_ref then
      let _ = Printf.fprintf !out_ref "Formula: %s\n" (formula_to_string f) in
      let _ = Printf.fprintf !out_ref "Word:\n%s\n" (lasso_to_string l) in
      let _ = Printf.fprintf !out_ref "Lasso Length: |u| = %d , |v| = %d \n" ulen vlen in
      let _ = Printf.fprintf !out_ref "Past height: %d , Future height: %d \n" (hp f) (hf f) in
      let _ = Printf.fprintf !out_ref "Proof Statistics: Size = %d, High = %d, Low = %d, Predicates = %d\n" (size p) (high p) (low p) (predicates p) in
      let _ = Printf.fprintf !out_ref "Proof: \n%s\n" (to_string p) in
      let pos = p_at p in
      if check_proof l f p then
        if pos = 0 then Printf.fprintf !out_ref "Checked proof at 0. Everything is fine.\n"
        else Printf.fprintf !out_ref
          "This proof isn't a proof at 0 but at %d. You have discovered a bug.\n" pos
      else Printf.fprintf !out_ref "This proof isn't a proof. You have discovered a bug.\n"
    else
      let _ = Printf.fprintf !out_ref "Formula: %s\n%s\n" (formula_to_string f) (visualize l f p) in
      ()
  with
    | End_of_file -> let _ = Printf.fprintf !out_ref "Bye.\n" in close_out !out_ref; exit 0
    | EXIT -> close_out !out_ref; exit 1

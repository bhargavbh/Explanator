(*******************************************************************)
(*     This is part of Explanator, it is distributed under the     *)
(*  terms of the GNU Lesser General Public License version 3       *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2018:                                                *)
(*  Bhargav Bhatt (ETH Zürich)                                     *)
(*  Dmitriy Traytel (ETH Zürich)                                   *)
(*******************************************************************)

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

val tt: formula
val p: string -> formula
val neg: formula -> formula
val conj: formula -> formula -> formula
val disj: formula -> formula -> formula
val prev: formula -> formula
val next: formula -> formula
val since: formula -> formula -> formula
val until: formula -> formula -> formula
val ff: formula
val impl: formula -> formula -> formula
val iff: formula -> formula -> formula
val release: formula -> formula -> formula
val weak_until: formula -> formula -> formula
val trigger: formula -> formula -> formula
val eventually: formula -> formula
val always: formula -> formula
val historically: formula -> formula
val once: formula -> formula

val atoms: formula -> string list

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

val optimal_proof: lasso -> (expl -> expl -> bool) -> formula -> expl
val check_proof: lasso -> formula -> expl -> bool
val size: expl -> int
val high: expl -> int
val low: expl -> int
val predicates: expl -> int
val size_le: expl -> expl -> bool
val high_le: expl -> expl -> bool
val low_le: expl -> expl -> bool
val predicates_le: expl -> expl -> bool
val p_at: expl -> int
val formula_to_string: formula -> string
val to_string: expl -> string
val lasso_to_string: lasso -> string
val hp: formula -> int
val hf: formula -> int
val height: formula -> int
val length_pair_lasso: lasso -> (int * int)
val mem_expl: expl -> int -> string -> bool
val mem_lasso: lasso -> int -> string -> bool
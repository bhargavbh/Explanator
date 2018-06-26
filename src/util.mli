(*******************************************************************)
(*     This is part of Explanator, it is distributed under the     *)
(*  terms of the GNU Lesser General Public License version 3       *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2018:                                                *)
(*  Bhargav Bhatt (ETH Zürich)                                     *)
(*  Dmitriy Traytel (ETH Zürich)                                   *)
(*******************************************************************)

module IntMap: Map.S with type key = int
val ( -- ): int -> int -> int list
val take: int -> 'a list -> 'a list
val last: 'a list -> 'a
val sum: ('a -> int) -> 'a list -> int
val map_filter: ('a -> 'b option) -> 'a list -> 'b list
val drop_while: ('a -> bool) -> 'a list -> 'a list
val chop_while: ('a -> bool) -> 'a list -> 'a list * 'a list
val max_list: int list -> int
val min_list: int list -> int
val paren: int -> int -> ('b, 'c, 'd, 'e, 'f, 'g) format6 -> ('b, 'c, 'd, 'e, 'f, 'g) format6
val list_to_string: string -> (string -> 'a -> string) -> 'a list -> string
val substring: string -> string -> bool
val remove_newline: string -> string
val word_to_string: string list list -> string
val prod_le: ('a -> 'a -> bool) -> ('a -> 'a -> bool) -> 'a -> 'a -> bool
val lex_le: ('a -> 'a -> bool) -> ('a -> 'a -> bool) -> 'a -> 'a -> bool
val mk_le: ('a -> int) -> 'a -> 'a -> bool
val get_mins: ('a -> 'a -> bool) -> 'a list -> 'a list

(************************************************************************)
(* Copyright (c) 2021, Gergei Bana and Qianli Zhang                     *)
(*                                                                      *)
(* This work is licensed under the MIT license. The license is          *)
(* described in the file "LICENSE" available at the root of the source  *)
(* or at https://opensource.org/licenses/MIT                            *)
(************************************************************************)


Require Export Core.


(* length function symbol for
bit-string length. Note the output is also in ppt *)


Definition Lens : Symbols Deterministic (narg 1) := symbols Deterministic (narg 1) [3].
Notation "'Len'" := (FuncInt Deterministic (narg 1) Lens).
Notation "'|' c1 '|'" := (Len [c1]) (at level 100, left associativity).


(* No axioms for Length here. Axioms such as that certain function symbols
 preserve length should be included among the axioms for specific protocols if needed. *)
(* Later one can include an axioms representing that the output of Len is a constant. *)

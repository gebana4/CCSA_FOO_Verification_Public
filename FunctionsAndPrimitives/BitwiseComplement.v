
(************************************************************************)
(* Copyright (c) 2021, Gergei Bana and Qianli Zhang                     *)
(*                                                                      *)
(* This work is licensed under the MIT license. The license is          *)
(* described in the file "LICENSE" available at the root of the source  *)
(* or at https://opensource.org/licenses/MIT                            *)
(************************************************************************)


Require Export Core.



(*  *)

Definition  Compls : Symbols Deterministic (narg 1) := symbols Deterministic (narg 1) [3; 1].
Notation "'Compl'" := (FuncInt Deterministic (narg 1) Compls).
Notation compl x := ((FuncInt Deterministic (narg 1) Compls) [x]).

(*  *)

Axiom ComplNeq: forall t,  ((compl t) ≟ t) = FAlse.


(* Axiom ComplLen_prop: forall t, forall L : list ppt -> ppt, L [compl t] =  L [ t ]. *)


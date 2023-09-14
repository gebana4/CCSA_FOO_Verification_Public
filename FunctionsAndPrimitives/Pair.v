
(************************************************************************)
(* Copyright (c) 2020, Gergei Bana and Qianli Zhang                     *)
(*                                                                      *)
(* This work is licensed under the MIT license. The license is          *)
(* described in the file "LICENSE" available at the root of the source  *)
(* or at https://opensource.org/licenses/MIT                            *)
(************************************************************************)


Require Import Core.



Definition Pairs : Symbols Deterministic (narg 2) := symbols Deterministic (narg 2) [1; 0].
Notation "'Pair'" := (FuncInt Deterministic (narg 2) Pairs).
Notation "'＜' c1 ',' c2 '＞'" := (Pair [c1; c2]) (at level 30, right associativity). (* U+FF1C and U+FF1E)*)


Definition Proj1s : Symbols Deterministic (narg 1) := symbols Deterministic (narg 1) [1; 1].
Notation "'Proj1'" := (FuncInt Deterministic (narg 1) Proj1s).
Notation "'π1' x" := ((FuncInt Deterministic (narg 1) Proj1s) [x]) (at level 35, right associativity).



Definition Proj2s : Symbols Deterministic (narg 1) := symbols Deterministic (narg 1) [1].
Notation "'Proj2'" := (FuncInt Deterministic (narg 1) Proj2s).
Notation "'π2' x" := ((FuncInt Deterministic (narg 1) Proj2s) [x]) (at level 35, right associativity).


Axiom Proj1Pair : forall {x1 x2 : ppt},  π1 ＜ x1, x2 ＞ = x1.
Axiom Proj2Pair : forall {x1 x2 : ppt},  π2 ＜ x1, x2 ＞ = x2.



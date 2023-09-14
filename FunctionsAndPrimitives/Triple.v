
(************************************************************************)
(* Copyright (c) 2021, Gergei Bana and Qianli Zhang                     *)
(*                                                                      *)
(* This work is licensed under the MIT license. The license is          *)
(* described in the file "LICENSE" available at the root of the source  *)
(* or at https://opensource.org/licenses/MIT                            *)
(************************************************************************)


Require Export Core.

(*  *)
Definition Triples : Symbols Deterministic (narg 3) := symbols Deterministic (narg 3) [2; 0].
Notation "'Triple'" := (FuncInt Deterministic (narg 3) Triples).
Notation "'＜' c1 ',' c2 ',' c3 '＞'" := (Triple [c1; c2; c3]) (at level 30, right associativity). (* U+FF1C and U+FF1E)*) (*overload ＜,＞ notation*)

Definition Troj1s : Symbols Deterministic (narg 1) := symbols Deterministic (narg 1) [2; 1].
Notation "'Troj1'" := (FuncInt Deterministic (narg 1) Troj1s).
Notation "'τ1' x" := ((FuncInt Deterministic (narg 1) Troj1s) [x]) (at level 35, right associativity).

Definition Troj2s : Symbols Deterministic (narg 1) := symbols Deterministic (narg 1) [2; 2].
Notation "'Troj2'" := (FuncInt Deterministic (narg 1) Troj2s).
Notation "'τ2' x" := ((FuncInt Deterministic (narg 1) Troj2s) [x]) (at level 35, right associativity).

Definition Troj3s : Symbols Deterministic (narg 1) := symbols Deterministic (narg 1) [2; 3].
Notation "'Troj3'" := (FuncInt Deterministic (narg 1) Troj3s).
Notation "'τ3' x" := ((FuncInt Deterministic (narg 1) Troj3s) [x]) (at level 35, right associativity).


(*  *)
Axiom Troj1Tri : forall {x1 x2 x3: ppt}, τ1 ＜ x1, x2, x3 ＞ = x1.
Axiom Troj2Tri : forall {x1 x2 x3: ppt}, τ2 ＜ x1, x2, x3 ＞ = x2.
Axiom Troj3Tri : forall {x1 x2 x3: ppt}, τ3 ＜ x1, x2, x3 ＞ = x3.


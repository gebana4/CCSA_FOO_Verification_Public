
(************************************************************************)
(* Copyright (c) 2021, Gergei Bana and Qianli Zhang                     *)
(*                                                                      *)
(* This work is licensed under the MIT license. The license is          *)
(* described in the file "LICENSE" available at the root of the source  *)
(* or at https://opensource.org/licenses/MIT                            *)
(************************************************************************)


Require Import Core.
Require Import Pair.



(* The Commitment Scheme will include three function symbols: { com, comk, L } 

   com  : a commitment function symbol that has two input parameters, with the first a plaintext and the second a commitment key.
   comk : a function symbols that can consume a nonce to generate the commitment key.
   L    : a function symbols that could return the length of input.  *)


(*  Computational Commitment hidding property for a Commitment Scheme: *)

Definition CompHid_prop (L com comk : list ppt -> ppt) : Prop :=
  forall (t0 : list ppt -> list ppt) (t t1 t2 : ppt) (n1 n2 : nat),
  n1 <> n2 ->
  Fresh (nonce n1) [t; t1; t2] -> Freshc (nonce n1) t0 ->
  Fresh (nonce n2) [t; t1; t2] -> Freshc (nonce n2) t0 ->
  t0 [If (L [t1] ≟ L [t2]) Then (＜(com [t1; (comk [nonce n1])]), (com [t2; (comk [nonce n2])]) ＞) Else t]
 ~
  t0 [If (L [t1] ≟ L [t2]) Then (＜(com [t2; (comk [nonce n1])]), (com [t1; (comk [nonce n2])]) ＞) Else t] .


(* Computational Commitment Binding property for a Commitment Scheme: *)

Definition CompBind_prop (com : list ppt -> ppt) : Prop :=
  forall (x x' r r': ppt),
    If ((com [x; r]) ≟ (com [x'; r'])) Then (x ≟ x') Else FAlse
    =
    ((com [x; r]) ≟ (com [x'; r'])).

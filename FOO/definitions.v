(************************************************************************)
(* Copyright (c) 2022, Gergei Bana, Qianli Zhang                        *)
(*                                                                      *)
(* This work is licensed under the MIT license. The license is          *)
(* described in the file "LICENSE" available at the root of the source  *)
(* or at https://opensource.org/licenses/MIT                            *)
(*                                                                      *)
(* Special thanks to Dr. Eeralla                                        *)
(************************************************************************)

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.micromega.Lia.

Require Export Core.
Require Export BasicExamples.
Require Export RandomizedPublicKeyEncryptions.
Require Export Pair.
Require Export Triple.
Require Export Length.
Require Export BlindSignatures.
Require Export Commitments.
Require Export BitwiseComplement.



(*-------------- Public key Enc ----------------*)

(*Key generation: honest public key - secret key generation is applied on the same fresh nonce *)
Parameter Pkeys : Symbols Deterministic (narg 1) .
Notation "'Pkey'" := (FuncInt Deterministic (narg 1) Pkeys).


Parameter Skeys x: Symbols Deterministic (narg 1).
Notation "'Skey'" := (FuncInt Deterministic (narg 1) Skeys).


(*Random input: honest random imput generation applied on a fresh nonce *)
Parameter Rands : Symbols Deterministic (narg 1).
Notation "'Rand'" := (FuncInt Deterministic (narg 1) Rands).



(*Encryption: first argument is for plaintext, second is for key third for randomness *)
Parameter Encs : Symbols Deterministic (narg 3).
Notation "'Enc'" := (FuncInt Deterministic (narg 3) Encs).
Notation "'❴' c1 '❵_' c2 '＾' c3 " := (Enc [c1; c2; c3]) (at level 100, left associativity).  (*'❴' is U+23A1 U+23A4, '＾' is U+02C6*)

(*Decryption: first argument is for plaintext, second for key *)
Parameter Decs : Symbols Deterministic (narg 2).
Notation "'Dec'" := (FuncInt Deterministic (narg 2) Decs).





(*----------------------------------*)
(*  *)
Parameter Bottoms : Symbols Deterministic (narg 0).
Notation "⫠"  := (ConstInt Deterministic Bottoms). (* U+2AE0 *)

(*  *)
Parameter KeyBlindings : Symbols Deterministic (narg 0).
Notation t := (ConstInt Deterministic KeyBlindings).

(*  *)
Parameter Blindings : Symbols Deterministic (narg 3).
Notation "'Blinding'" := (FuncInt Deterministic (narg 3) Blindings).
Notation b x y z:= ((FuncInt Deterministic (narg 3) Blindings) [x; y; z]).

(*  *)
Parameter BlindRands: Symbols Deterministic (narg 1).
Notation "'BlindRand'" := (FuncInt Deterministic (narg 1) BlindRands).
Notation Brand x := ((FuncInt Deterministic (narg 1) BlindRands) [x]).

(*  *)
Definition Accepts := symbols Deterministic (narg 4) [1; 0; 0; 1; 1; 1; 1].
Notation "'Accept'" := (FuncInt Deterministic (narg 4) Accepts).
Notation acc x y z u := ((FuncInt Deterministic (narg 4) Accepts) [x; y; z; u]).

(*  *)
Parameter Unblindings : Symbols Deterministic (narg 4).
Notation "'Unblinding'" := (FuncInt Deterministic (narg 4) Unblindings).
Notation ub x y z u := ((FuncInt Deterministic (narg 4) Unblindings) [x; y; z; u]).

(*----------------------------------*)
(*  *)
Parameter Commitments : Symbols Deterministic (narg 2).
Notation "'Commitment'" := (FuncInt Deterministic (narg 2) Commitments).
Notation com x y := ((FuncInt Deterministic (narg 2) Commitments) [x; y]).

(*  *)
Parameter Commitkeys : Symbols Deterministic (narg 1).
Notation "'Commitkey'" := (FuncInt Deterministic (narg 1) Commitkeys).
Notation Comk x := ((FuncInt Deterministic (narg 1) Commitkeys) [x]).


(*----------------------------------*)
(*  *)
Notation "x '≠' y"    := ((x ≟ y) = FAlse)                (at level 20, right associativity).   (*  *)

(*Additional function symbols*)
Parameter ERrors : Symbols Deterministic (narg 0).
Notation "'Error'" := (ConstInt Deterministic ERrors).



(*
Definition cca_2      := (CCA2 Len Enc Dec Pkey Skey Rand Error).

*)


(*  *)
Parameter Votting0s : Symbols Deterministic (narg 0).
Notation "'vot0'"  := (ConstInt Deterministic Votting0s) : type_scope.

Parameter Votting1s : Symbols Deterministic (narg 0).
Notation "'vot1'" := (ConstInt Deterministic Votting1s) : type_scope.

(*  *)
Parameter Phase2 : Symbols Deterministic (narg 0).
Notation ph2 := (ConstInt Deterministic Phase2).

(*  *)
Parameter Phase3 : Symbols Deterministic (narg 0).
Notation ph3 := (ConstInt Deterministic Phase3).

(*  *)
Parameter Shuffles : Symbols Deterministic (narg 3). (*  *)
Notation shufl x y z := ((FuncInt Deterministic (narg 3) Shuffles) [x; y; z]).

(*  *)
Parameter Llbl : Symbols Deterministic (narg 0).
Notation llbl := (ConstInt Deterministic Llbl).

(* 
Parameter Compls : Symbols Deterministic (narg 1). (*  *)
Notation compl x := ((FuncInt Deterministic (narg 1) Compls) [x]). *)



(* Page 24 *)
Definition isin x y  := ( (x ≟ (τ1 y)) or (x ≟ (τ2 y)) or (x ≟ (τ3 y))).

(* page 35 and page 23 *)
Definition dist x y z := (!(x ≟ y) & !(x ≟ z) & !(y ≟ z)).
Definition pchkv x := ((ph2 ≟ (π2 (τ1 x))) & (ph2 ≟ (π2 (τ2 x))) & (ph2 ≟ (π2 (τ3 x)))).

(* Page 24  *)
Definition label x y := (If (x ≟ (τ2 (π2 (τ1 y)))) Then (π1 (τ1 y))
                   Else (If (x ≟ (τ2 (π2 (τ2 y)))) Then (π1 (τ2 y))
                   Else (If (x ≟ (τ2 (π2 (τ3 y)))) Then (π1 (τ3 y)) Else ⫠ ))). (* I feel this notation is useless. It has the same Ecological niche as a function symbol *)
(* Page 24 *)
Definition ncheck x y  := (isin x (＜ (τ3 (π2 (τ1 y))) , (τ3 (π2 (τ2 y))) , (τ3 (π2 (τ3 y))) ＞)).

(* Page 24 *)
Definition bcheck x y := (isin x (＜ (τ1 (π2 (τ1 y))) , (τ1 (π2 (τ2 y))) , (τ1 (π2 (τ3 y))) ＞)).
Definition bnlcheck x y z := (bcheck x y ) & ((| label x z |) ≟ llbl) & (ncheck y z).

(*  *)
Definition pchko x := ((ph3 ≟ (π2 (τ1 x))) & (ph3 ≟ (π2 (τ2 x))) & (ph3 ≟ (π2 (τ3 x)))).
Definition isinkc kc0 kc1 x := (isin kc0 x) ⨀ (isin kc1 x).






(*   *)
Notation kc0   := (Comk (nonce 0)).  (*  *)
Notation kc1   := (Comk (nonce 1)).  (*  *)
Notation bn0   := (Brand (nonce 2)).  (*  *)
Notation bn1   := (Brand (nonce 3)).  (*  *)

(*   *)
Notation n0     := (nonce 4). (*  *)
Notation n0'    := (nonce 13). (*  *)
Notation n1     := (nonce 5). (*  *)
Notation n1'     := (nonce 16). (*  *)
Notation kc0'     := (Comk (nonce 14)). (*  *)
Notation kc1'     := (Comk (nonce 15)). (*  *)

Notation pkS    := (Pkey [nonce 6]). (*  *)
Notation skS    := (Skey [nonce 6]). (*  *)

Notation rd0    := (Rand [nonce 7]). (*  *)
Notation rd1    := (Rand [nonce 8]). (*  *)

Notation rdd0    := (Rand [nonce 10]). (*  *)
Notation rdd1    := (Rand [nonce 11]). (*  *)

Notation decS c := (Dec [c; skS]).  (*  *)
Notation encS m r := (❴m❵_pkS ＾ r).





(** --------------- **)

Notation t0  Φ1 := (adv (2) Φ1).  (*   *)
Notation t1  Φ1 := (adv (3) Φ1).  (*   *)
Notation f2  Φ2 := (adv (4) Φ2).  (*   *)
Notation f3  Φ3 := (adv (5) Φ3).  (*   *)
Notation f4  Φ4 := (adv (6) Φ4).  (*   *)
Notation f5  Φ5 := (adv (7) Φ5).  (*   *)



(** --------------- **)

Inductive Sides := lhs : Sides | rhs : Sides.
Definition op s := match s with lhs => rhs | rhs => lhs end.

(* This definition has flaw *)
Definition vot s := match s with lhs => vot0 | rhs => vot1 end.



(** --------------- **)

Notation c00 := (com vot0 kc0).  (*  *)
Notation c01 := (com vot1 kc1).  (*  *)
Notation c10 := (com vot1 kc0).  (*  *)
Notation c11 := (com vot0 kc1).  (*  *)

(*  *)
Definition c0 s := match s with lhs => c00 | rhs => c10 end.
Definition c1 s := match s with lhs => c01 | rhs => c11 end.

(*  *)


(*  *)
Definition b0 c := (b c t bn0).
Definition b1 c := (b c t bn1).

(*  *)
Definition ti0 c0 c1 := (t0 [b0 c0; b1 c1]). (*  *)
Definition ti1 c0 c1 := (t1 [b0 c0; b1 c1]). (*  *)




(** --------------- **)

Definition acc0 c0 c1 := (acc c0 t bn0 (ti0 c0 c1)).
Definition acc1 c0 c1 := (acc c1 t bn1 (ti1 c0 c1)).

(**)
Definition σ0 c0 c1 := (ub c0 t bn0 (ti0 c0 c1)).
Definition σ1 c0 c1 := (ub c1 t bn1 (ti1 c0 c1)).

(**)
Definition pv0 c0 c1 n0 := (＜c0, (σ0 c0 c1), n0＞).  (*  *)
Definition pv1 c0 c1 n1 := (＜c1, (σ1 c0 c1), n1＞).  (*  *)

(**)
Definition m0 c0 c1 n0 := (＜ (pv0 c0 c1 n0), ph2 ＞).
Definition m1 c0 c1 n1 := (＜ (pv1 c0 c1 n1), ph2 ＞).

(**)
Definition e0 c0 c1 n0 := ❴ (m0 c0 c1 n0) ❵_pkS ＾ rd0.
Definition e1 c0 c1 n1 := ❴ (m1 c0 c1 n1) ❵_pkS ＾ rd1.





(* We introduce variables x0 and x1 for the encryptions to be able to easily build the
contexts for CCA2 *)
(*  x0 takes (e0 c0 c1 n0) and x1 takes (e1 c0 c1 n1) *)

Definition fΦ2  c0 c1       := (f2 [(b0 c0);  (b1 c1);  (e0 c0 c1 n0);  (e1 c0 c1 n1)]). (*  *)
Definition fFΦ2 c0 c1 x0    := (f2 [(b0 c0);  (b1 c1);  x0;             (e1 c0 c1 n1)]).
Definition fGΦ2 c0 c1    x1 := (f2 [(b0 c0);  (b1 c1);  (e0 c0 c1 n0);  x1           ]).





(** --------------- **)

Definition v1 c0 c1 := (decS (τ1 (fΦ2 c0 c1))). (* *)
Definition v2 c0 c1 := (decS (τ2 (fΦ2 c0 c1))).
Definition v3 c0 c1 := (decS (τ3 (fΦ2 c0 c1))).

Definition Fv1 c0 c1 x0 := (decS (τ1 (fFΦ2 c0 c1 x0))).
Definition Fv2 c0 c1 x0 := (decS (τ2 (fFΦ2 c0 c1 x0))).
Definition Fv3 c0 c1 x0 := (decS (τ3 (fFΦ2 c0 c1 x0))).

Definition Gv1 c0 c1 x1 := (decS (τ1 (fGΦ2 c0 c1 x1))).
Definition Gv2 c0 c1 x1 := (decS (τ2 (fGΦ2 c0 c1 x1))).
Definition Gv3 c0 c1 x1 := (decS (τ3 (fGΦ2 c0 c1 x1))).



(* To be able to apply CCA2, the context on the encyption has to have checks
making sure the decryption oracle is not used on the encyption. To this end,
Fiv is a transformation with ifthenelse of Fv that is in the form needed to apply CCA2 for e *)

Definition Fiv1 c0 c1 x0 m0 := If (τ1 (fFΦ2 c0 c1 x0)) ≟ x0 Then m0 (* (m0 c0 c1 n0) *)
                      Else (If (τ1 (fFΦ2 c0 c1 x0)) ≟ x0 Then Error Else (decS (τ1 (fFΦ2 c0 c1 x0)))).
Definition Fiv2 c0 c1 x0 m0 := If (τ2 (fFΦ2 c0 c1 x0)) ≟ x0 Then m0
                      Else (If (τ2 (fFΦ2 c0 c1 x0)) ≟ x0 Then Error Else (decS (τ2 (fFΦ2 c0 c1 x0)))).
Definition Fiv3 c0 c1 x0 m0 := If (τ3 (fFΦ2 c0 c1 x0)) ≟ x0 Then m0
                      Else (If (τ3 (fFΦ2 c0 c1 x0)) ≟ x0 Then Error Else (decS (τ3 (fFΦ2 c0 c1 x0)))).

Definition Giv1 c0 c1 x1 m1 := If (τ1 (fGΦ2 c0 c1 x1)) ≟ x1 Then m1 (* (m1 c0 c1 n1) *)
                      Else (If (τ1 (fGΦ2 c0 c1 x1)) ≟ x1 Then Error Else (decS (τ1 (fGΦ2 c0 c1 x1)))).
Definition Giv2 c0 c1 x1 m1 := If (τ2 (fGΦ2 c0 c1 x1)) ≟ x1 Then m1
                      Else (If (τ2 (fGΦ2 c0 c1 x1)) ≟ x1 Then Error Else (decS (τ2 (fGΦ2 c0 c1 x1)))).
Definition Giv3 c0 c1 x1 m1 := If (τ3 (fGΦ2 c0 c1 x1)) ≟ x1 Then m1
                      Else (If (τ3 (fGΦ2 c0 c1 x1)) ≟ x1 Then Error Else (decS (τ3 (fGΦ2 c0 c1 x1)))).

Definition s v1 v2 v3  :=
     shufl (π1 v1) (π1 v2) (π1 v3).






(*
Definition s c0 c1 v1 v2 v3  := (If ( ! (isin (pv0 c0 c1 n0) (＜(π1 v1), (π1 v2), (π1 v3)＞))) Then (shufl (π1 v1) (π1 v2) (π1 v3)) Else ⫠).
Definition s' c0 c1 v1 v2 v3 := (If ( ! (isin (pv1 c0 c1 n1) (＜(π1 v1), (π1 v2), (π1 v3)＞))) Then (shufl (π1 v1) (π1 v2) (π1 v3)) Else ⫠).*)


(**)
Definition dv v1 v2 v3 y := If (dist v1 v2 v3) & (pchkv (＜ v1, v2, v3 ＞)) Then y Else ⫠.

(* Page 35  *)
Definition fΦ3 c0 c1 := let v1 := v1 c0 c1 in
                        let v2 := v2 c0 c1 in
                        let v3 := v3 c0 c1 in
  (f3 [(b0 c0);  (b1 c1);  (e0 c0 c1 n0);  (e1 c0 c1 n1); dv v1 v2 v3 (s v1 v2 v3) ]). 


(* Fiv can be decided by x0 *)
Definition fFΦ3 c0 c1 x0 v1 v2 v3 := (* v1 := Fiv1 c0 c1 x0 *)
  (f3 [(b0 c0);  (b1 c1);  x0;  (e1 c0 c1 n1);  dv v1 v2 v3 (s v1 v2 v3) ]).

Definition fGΦ3 c0 c1 x1 v1 v2 v3 := (* v1 := Giv1 c0 c1 x1 *)
  (f3 [(b0 c0);  (b1 c1);  (e0 c0 c1 n0);  x1;  dv v1 v2 v3 (s v1 v2 v3) ]).





(** --------------- **)

Definition l0 c0 c1 := If (bnlcheck c0 n0 (fΦ3 c0 c1)) (* n0 is the global variable *)
                          Then ❴＜＜(label c0 (fΦ3 c0 c1)), kc0 ＞, ph3 ＞❵_pkS ＾ rdd0
                          Else ⫠.

Definition l1 c0 c1 := If (bnlcheck c1 n1 (fΦ3 c0 c1))
                          Then ❴＜＜(label c1 (fΦ3 c0 c1)), kc1 ＞, ph3 ＞❵_pkS ＾ rdd1
                          Else ⫠.

(*   *)
Definition Fl0 c0 c1 x0 v1 v2 v3 := If (bnlcheck c0 n0 (fFΦ3 c0 c1 x0 v1 v2 v3))
                                       Then ❴＜＜(label c0 (fFΦ3 c0 c1 x0 v1 v2 v3)), kc0 ＞, ph3 ＞❵_pkS ＾ rdd0  Else ⫠.

Definition Fl1 c0 c1 x0 v1 v2 v3 := If (bnlcheck c1 n1 (fFΦ3 c0 c1 x0 v1 v2 v3))
                                       Then ❴＜＜(label c1 (fFΦ3 c0 c1 x0 v1 v2 v3)), kc1 ＞, ph3 ＞❵_pkS ＾ rdd1  Else ⫠.

(*   *)
Definition Gl0 c0 c1 x1 v1 v2 v3 := If (bnlcheck c0 n0 (fGΦ3 c0 c1 x1 v1 v2 v3))
                                       Then ❴＜＜(label c0 (fGΦ3 c0 c1 x1 v1 v2 v3)), kc0 ＞, ph3 ＞❵_pkS ＾ rdd0 Else ⫠.

Definition Gl1 c0 c1 x1 v1 v2 v3 := If (bnlcheck c1 n1 (fGΦ3 c0 c1 x1 v1 v2 v3))
                                       Then ❴＜＜(label c1 (fGΦ3 c0 c1 x1 v1 v2 v3)), kc1 ＞, ph3 ＞❵_pkS ＾ rdd1 Else ⫠.

(*  *)
Definition fΦ5 c0 c1 := let v1 := v1 c0 c1 in
                        let v2 := v2 c0 c1 in
                        let v3 := v3 c0 c1 in
  (f5 [(b0 c0);  (b1 c1);  (e0 c0 c1 n0);  (e1 c0 c1 n1);  dv v1 v2 v3 (s v1 v2 v3); l0 c0 c1; l1 c0 c1 ]).

Definition fFΦ5 c0 c1 x0 v1 v2 v3 :=
  (f5 [(b0 c0);  (b1 c1);  x0;  (e1 c0 c1 n1);  dv v1 v2 v3 (s v1 v2 v3);
       Fl0 c0 c1 x0 v1 v2 v3; Fl1 c0 c1 x0 v1 v2 v3]).

Definition fGΦ5 c0 c1 x1 v1 v2 v3 :=
  (f5 [(b0 c0);  (b1 c1);  (e0 c0 c1 n0);  x1;  dv v1 v2 v3 (s v1 v2 v3);
       Gl0 c0 c1 x1 v1 v2 v3; Gl1 c0 c1 x1 v1 v2 v3]).





(** --------------- **)

Definition o1 c0 c1 :=  (decS (τ1 (fΦ5 c0 c1))). (*  *)
Definition o2 c0 c1 :=  (decS (τ2 (fΦ5 c0 c1))).
Definition o3 c0 c1 :=  (decS (τ3 (fΦ5 c0 c1))).

Definition Fo1 c0 c1 x0 v1 v2 v3 :=  (decS (τ1 (fFΦ5 c0 c1 x0 v1 v2 v3))). (*  *)
Definition Fo2 c0 c1 x0 v1 v2 v3 :=  (decS (τ2 (fFΦ5 c0 c1 x0 v1 v2 v3))).
Definition Fo3 c0 c1 x0 v1 v2 v3 :=  (decS (τ3 (fFΦ5 c0 c1 x0 v1 v2 v3))).

Definition Go1 c0 c1 x1 v1 v2 v3 :=  (decS (τ1 (fGΦ5 c0 c1 x1 v1 v2 v3))). (*  *)
Definition Go2 c0 c1 x1 v1 v2 v3 :=  (decS (τ2 (fGΦ5 c0 c1 x1 v1 v2 v3))).
Definition Go3 c0 c1 x1 v1 v2 v3 :=  (decS (τ3 (fGΦ5 c0 c1 x1 v1 v2 v3))).

(* phase check should turn false *)
Definition Fio1 c0 c1 x0 v1 v2 v3 n0 :=  If (τ1 (fFΦ5 c0 c1 x0 v1 v2 v3 )) ≟ x0 Then (m0 c0 c1 n0) (* (m0 c0 c1 n0) *)
                       Else (If (τ1 (fFΦ5 c0 c1 x0 v1 v2 v3)) ≟ x0 Then Error Else (decS (τ1 (fFΦ5 c0 c1 x0 v1 v2 v3)))).

Definition Fio2 c0 c1 x0 v1 v2 v3 n0 :=  If (τ2 (fFΦ5 c0 c1 x0 v1 v2 v3 )) ≟ x0 Then (m0 c0 c1 n0)
                       Else (If (τ2 (fFΦ5 c0 c1 x0 v1 v2 v3)) ≟ x0 Then Error Else (decS (τ2 (fFΦ5 c0 c1 x0 v1 v2 v3)))).

Definition Fio3 c0 c1 x0 v1 v2 v3 n0 :=  If (τ3 (fFΦ5 c0 c1 x0 v1 v2 v3)) ≟ x0 Then (m0 c0 c1 n0)
                       Else (If (τ3 (fFΦ5 c0 c1 x0 v1 v2 v3)) ≟ x0 Then Error Else (decS (τ3 (fFΦ5 c0 c1 x0 v1 v2 v3)))).








(** --------------- **)

(* *)
Definition do c0 c1 := let o1 := (o1 c0 c1 ) in
                       let o2 := (o2 c0 c1 ) in
                       let o3 := (o3 c0 c1 ) in
  (If ((dist o1 o2 o3) & (pchko (＜ o1, o2, o3 ＞)) & (isinkc kc0 kc1 (＜(π2 (π1 o1)), (π2 (π1 o2)), (π2 (π1 o3))＞)))
      Then (shufl (π1 o1) (π1 o2) (π1 o3))
      Else ⫠).


(* *)
Definition Fdo c0 c1 x0 v1 v2 v3 := let o1 := (Fo1 c0 c1 x0 v1 v2 v3) in
                                    let o2 := (Fo2 c0 c1 x0 v1 v2 v3) in
                                    let o3 := (Fo3 c0 c1 x0 v1 v2 v3) in
  (If ((dist o1 o2 o3) & (pchko (＜ o1, o2, o3 ＞)) & (isinkc kc0 kc1 (＜(π2 (π1 o1)), (π2 (π1 o2)), (π2 (π1 o3))＞)))
      Then (shufl (π1 o1) (π1 o2) (π1 o3))
      Else ⫠).

(* *)
Definition Fido c0 c1 x0 v1 v2 v3 n0 := let o1 := (Fio1 c0 c1 x0 v1 v2 v3 n0) in
                                        let o2 := (Fio2 c0 c1 x0 v1 v2 v3 n0) in
                                        let o3 := (Fio3 c0 c1 x0 v1 v2 v3 n0) in
  (If ((dist o1 o2 o3) & (pchko (＜ o1, o2, o3 ＞)) & (isinkc kc0 kc1 (＜(π2 (π1 o1)), (π2 (π1 o2)), (π2 (π1 o3))＞)))
      Then (shufl (π1 o1) (π1 o2) (π1 o3))
      Else ⫠).
(*  *)



(*  *)
(*DO means decryption in the opening phase *)
Definition Do o1 o2 o3 :=
  (If ((dist o1 o2 o3) & (pchko (＜ o1, o2, o3 ＞)) & (isinkc kc0 kc1 (＜(π2 (π1 o1)), (π2 (π1 o2)), (π2 (π1 o3))＞)))
      Then (shufl (π1 o1) (π1 o2) (π1 o3))
      Else ⫠).

(**)
Definition FIDO o1 o2 o3 :=
  (If ((dist o1 o2 o3) & (pchko (＜ o1, o2, o3 ＞)) & ! (isin kc1 (＜(π2 (π1 o1)), (π2 (π1 o2)), (π2 (π1 o3))＞))) (* notice that kc0 is eliminated in FIDO *)
      Then (shufl (π1 o1) (π1 o2) (π1 o3))
      Else ⫠).

(**)
Definition GIDO o1 o2 o3 :=
  (If ((dist o1 o2 o3) & (pchko (＜ o1, o2, o3 ＞)) & ! (isin kc0 (＜(π2 (π1 o1)), (π2 (π1 o2)), (π2 (π1 o3))＞))) (* notice that kc0 is eliminated in FIDO *)
      Then (shufl (π1 o1) (π1 o2) (π1 o3))
      Else ⫠).

(*  *)
Definition FDO o1 o2 o3 :=
  (If ((dist o1 o2 o3) & (pchko (＜ o1, o2, o3 ＞))) (*both kc0 and kc1 are eliminated *)
      Then (shufl (π1 o1) (π1 o2) (π1 o3))
      Else ⫠).





(** --------------- **)

(*  *)
Definition FFΦ2 c0 c1  := (f2 [(b0 c0);  (b1 c1);  (e0 c0 c1 n0');  (e1 c0 c1 n1)]).

(*  *)
Definition FFΦ3 c0 c1  := let v1 := Fv1 c0 c1 (e0 c0 c1 n0') in
                          let v2 := Fv2 c0 c1 (e0 c0 c1 n0') in
                          let v3 := Fv3 c0 c1 (e0 c0 c1 n0') in
  (f3 [(b0 c0);  (b1 c1);  (e0 c0 c1 n0');  (e1 c0 c1 n1);  dv v1 v2 v3 (shufl (π1 v1) (π1 v2) (π1 v3)) ]).

(*  *)
Definition M1 c0 c1 kc := (＜＜(label c1 (fFΦ3 c0 c1 (e0 c0 c1 n0') (Fv1 c0 c1 (e0 c0 c1 n0')) (Fv2 c0 c1 (e0 c0 c1 n0')) (Fv3 c0 c1 (e0 c0 c1 n0')))), kc ＞, ph3 ＞).

(*  *)
Definition E1 c0 c1 kc := ❴ (M1 c0 c1 kc) ❵_pkS ＾ rdd1.

(*  *)
Definition FL1 c0 c1 y1 := If (bnlcheck c1 n1 (fFΦ3 c0 c1 (e0 c0 c1 n0') (Fv1 c0 c1 (e0 c0 c1 n0')) (Fv2 c0 c1 (e0 c0 c1 n0')) (Fv3 c0 c1 (e0 c0 c1 n0')))) Then y1 Else ⫠.

(*  *)
Definition FFΦ5 c0 c1 y1 :=
  (f5 [(b0 c0);         (b1 c1);  (e0 c0 c1 n0');  (e1 c0 c1 n1);
       (dv (Fv1 c0 c1 (e0 c0 c1 n0')) (Fv2 c0 c1 (e0 c0 c1 n0')) (Fv3 c0 c1 (e0 c0 c1 n0'))
           (shufl (π1 (Fv1 c0 c1 (e0 c0 c1 n0'))) (π1 (Fv2 c0 c1 (e0 c0 c1 n0'))) (π1 (Fv3 c0 c1 (e0 c0 c1 n0'))))); (* I changed s to shufl *)
       ⫠;  FL1 c0 c1 y1 ]).

(*  *)
Definition FO1 c0 c1 y1 :=  (decS (τ1 (FFΦ5 c0 c1 y1))). (*  *)
Definition FO2 c0 c1 y1 :=  (decS (τ2 (FFΦ5 c0 c1 y1))).
Definition FO3 c0 c1 y1 :=  (decS (τ3 (FFΦ5 c0 c1 y1))).

(*  *)
Definition FiiO1 c0 c1 y1 := If (τ1 (FFΦ5 c0 c1 y1)) ≟ y1 Then (M1 c0 c1 kc1) Else (If (τ1 (FFΦ5 c0 c1 y1)) ≟ y1 Then Error Else (decS (τ1 (FFΦ5 c0 c1 y1)))).
Definition FiiO2 c0 c1 y1 := If (τ2 (FFΦ5 c0 c1 y1)) ≟ y1 Then (M1 c0 c1 kc1) Else (If (τ2 (FFΦ5 c0 c1 y1)) ≟ y1 Then Error Else (decS (τ2 (FFΦ5 c0 c1 y1)))).
Definition FiiO3 c0 c1 y1 := If (τ3 (FFΦ5 c0 c1 y1)) ≟ y1 Then (M1 c0 c1 kc1) Else (If (τ3 (FFΦ5 c0 c1 y1)) ≟ y1 Then Error Else (decS (τ3 (FFΦ5 c0 c1 y1)))).

(*  *)
Definition FiO1 c0 c1 y1 := If (τ1 (FFΦ5 c0 c1 y1)) ≟ y1 Then (＜ ⫠, ph2 ＞) Else decS (τ1 (FFΦ5 c0 c1 y1)).
Definition FiO2 c0 c1 y1 := If (τ2 (FFΦ5 c0 c1 y1)) ≟ y1 Then (＜ ⫠, ph2 ＞) Else decS (τ2 (FFΦ5 c0 c1 y1)).
Definition FiO3 c0 c1 y1 := If (τ3 (FFΦ5 c0 c1 y1)) ≟ y1 Then (＜ ⫠, ph2 ＞) Else decS (τ3 (FFΦ5 c0 c1 y1)).






(********************************************************************)


(* prioriy of (τ2 (fΦΦ2 c0 c1 x0 x1)) ≟ x0 & (τ1 (fΦΦ2 c0 c1 x0 x1)) ≟ x1 and
((τ2 (fΦΦ2 c0 c1 x0 x1)) ≟ x0) & ((τ1 (fΦΦ2 c0 c1 x0 x1)) ≟ x1) ??????*)

(* We only focus on the encryption in the opening phase in those definitions *)

(*  (FGΦ2 c0 c1 (e0 c0 c1 n0) (e1 c0 c1 n1) = fΦ2 c0 c1).  *)
Definition fΦΦ2 c0 c1 x0 x1 := (f2 [(b0 c0);  (b1 c1);  x0 ;  x1  ]). (*  *)

(* s26 can be changed to If (τ3 (fΦ2 c0 c1)) ≟ (e0 c0 c1 n0) Then bot Else (τ3 (fΦ2 c0 c1)) ≟ (e1 c0 c1 n1) Then bot else s26*)
Definition s26 c0 c1 v3 := (If ((τ2 (fΦ2 c0 c1)) ≟ (e0 c0 c1 n0)) & ((τ1 (fΦ2 c0 c1)) ≟ (e1 c0 c1 n1))
                               Then (shufl (pv1 c0 c1 n1) (pv0 c0 c1 n0) (π1 v3)) Else ⫠). (* If (τ2 (fΦ2 c0 c1)) ≟ (e0 c0 c1 n0) & (τ1 (fΦ2 c0 c1)) ≟ (e1 c0 c1 n1) *)



(* in v3 there should also be x0 and x1 *)
Definition fs26 c0 c1 x0 x1 v3 := (If ((τ2 (fΦΦ2 c0 c1 x0 x1)) ≟ x0) & ((τ1 (fΦΦ2 c0 c1 x0 x1)) ≟ x1)
                                  Then (shufl (pv1 c0 c1 n1) (pv0 c0 c1 n0) (π1 v3)) Else ⫠).
(*  *)
Definition fv3 c0 c1 x0 x1 := decS (τ3 (fΦΦ2 c0 c1 x0 x1)).

Goal forall c0 c1, s26 c0 c1 (v3 c0 c1) = fs26 c0 c1 (e0 c0 c1 n0) (e1 c0 c1 n1) (fv3 c0 c1 (e0 c0 c1 n0) (e1 c0 c1 n1)). reflexivity. Qed.


(* then we need to change (dv s26) to CCA2 form. *)
Definition fis26 c0 c1 x0 x1 v3 := (If ((τ2 (fΦΦ2 c0 c1 x0 x1)) ≟ x0 & (τ1 (fΦΦ2 c0 c1 x0 x1)) ≟ x1 & ! ((τ3 (fΦΦ2 c0 c1 x0 x1)) ≟ x0))
                                    Then (shufl (pv1 c0 c1 n1) (pv0 c0 c1 n0) (π1 v3))
                               Else If ((τ2 (fΦΦ2 c0 c1 x0 x1)) ≟ x0 & (τ1 (fΦΦ2 c0 c1 x0 x1)) ≟ x1 & ! ((τ3 (fΦΦ2 c0 c1 x0 x1)) ≟ x1))
                                    Then (shufl (pv1 c0 c1 n1) (pv0 c0 c1 n0) (π1 v3)) Else ⫠).







(** --------------- **)
(**)
Definition fΦΦ3 c0 c1 :=
  let v1 := v1 c0 c1 in
  let v2 := v2 c0 c1 in
  let v3 := v3 c0 c1 in
  (f3 [(b0 c0);  (b1 c1);  (e0 c0 c1 n0);  (e1 c0 c1 n1);  dv v1 v2 v3 (s26 c0 c1 v3)]).

(**)
Definition enco0 c0 c1 kc0 := ( ❴＜＜(label c0 (fΦΦ3 c0 c1)), kc0 ＞, ph3 ＞❵_pkS ＾ rdd0).
Definition enco1 c0 c1 kc1 := ( ❴＜＜(label c1 (fΦΦ3 c0 c1)), kc1 ＞, ph3 ＞❵_pkS ＾ rdd1).

(**)
Definition LL0 c0 c1 y0 := If (bnlcheck c0 n0 (fΦΦ3 c0 c1)) Then y0  Else ⫠.

(**)
Definition LL1 c0 c1 y1 := If (bnlcheck c1 n1 (fΦΦ3 c0 c1)) Then y1  Else ⫠.

(*
Definition fΦΦ5 c0 c1 :=
  let v1 := v1 c0 c1 in
  let v2 := v2 c0 c1 in
  let v3 := v3 c0 c1 in
  (f5 [(b0 c0);  (b1 c1);  (e0 c0 c1 n0);  (e1 c0 c1 n1);  dv v1 v2 v3 (s26 c0 c1 v3);   LL0 c0 c1 (enco0 c0 c1 kc0);  LL1 c0 c1 (enco1 c0 c1 kc1) ]).
*)

(**)
Definition FGΦΦ5 c0 c1 y0 y1 := (* y0 could be LL0 c0 c1 (enco0 c0 c1) *)
  let v1 := v1 c0 c1 in
  let v2 := v2 c0 c1 in
  let v3 := v3 c0 c1 in
  (f5 [(b0 c0);  (b1 c1);  (e0 c0 c1 n0);  (e1 c0 c1 n1);  dv v1 v2 v3 (s26 c0 c1 v3);   y0  ;  y1 ]).


(* y0 in FGO1 should be LL0 *)
Definition FGO1 c0 c1 LL0 LL1 :=  (decS (τ1 (FGΦΦ5 c0 c1 LL0 LL1))). (*  *)
Definition FGO2 c0 c1 LL0 LL1 :=  (decS (τ2 (FGΦΦ5 c0 c1 LL0 LL1))).
Definition FGO3 c0 c1 LL0 LL1 :=  (decS (τ3 (FGΦΦ5 c0 c1 LL0 LL1))).


(* CCA2 for formula 14 *)
Definition FIIO1 c0 c1 enco0 m :=  If (τ1 (FGΦΦ5 c0 c1 enco0 ⫠)) ≟ enco0 Then m
                             Else (If (τ1 (FGΦΦ5 c0 c1 enco0 ⫠)) ≟ enco0 Then Error Else (decS (τ1 (FGΦΦ5 c0 c1 enco0 ⫠)))).
Definition FIIO2 c0 c1 enco0 m :=  If (τ2 (FGΦΦ5 c0 c1 enco0 ⫠)) ≟ enco0 Then m
                             Else (If (τ2 (FGΦΦ5 c0 c1 enco0 ⫠)) ≟ enco0 Then Error Else (decS (τ2 (FGΦΦ5 c0 c1 enco0 ⫠)))).
Definition FIIO3 c0 c1 enco0 m :=  If (τ3 (FGΦΦ5 c0 c1 enco0 ⫠)) ≟ enco0 Then m
                             Else (If (τ3 (FGΦΦ5 c0 c1 enco0 ⫠)) ≟ enco0 Then Error Else (decS (τ3 (FGΦΦ5 c0 c1 enco0 ⫠)))).

(*  (＜ ⫠, ph2 ＞) is an example of consts that appear the same as enco0 in do *)
Definition FIO1 c0 c1 enco0 :=  (If (τ1 (FGΦΦ5 c0 c1 enco0 ⫠)) ≟ enco0 Then (＜ ⫠, ph2 ＞) Else (decS (τ1 (FGΦΦ5 c0 c1 enco0 ⫠)))).
Definition FIO2 c0 c1 enco0 :=  (If (τ2 (FGΦΦ5 c0 c1 enco0 ⫠)) ≟ enco0 Then (＜ ⫠, ph2 ＞) Else (decS (τ2 (FGΦΦ5 c0 c1 enco0 ⫠)))).
Definition FIO3 c0 c1 enco0 :=  (If (τ3 (FGΦΦ5 c0 c1 enco0 ⫠)) ≟ enco0 Then (＜ ⫠, ph2 ＞) Else (decS (τ3 (FGΦΦ5 c0 c1 enco0 ⫠)))).


(* CCA2 for formula 15 *)
Definition GIIO1 c0 c1 enco1 m :=  If (τ1 (FGΦΦ5 c0 c1 ⫠ enco1)) ≟ enco1 Then m
                             Else (If (τ1 (FGΦΦ5 c0 c1 ⫠ enco1)) ≟ enco1 Then Error Else (decS (τ1 (FGΦΦ5 c0 c1 ⫠ enco1)))).
Definition GIIO2 c0 c1 enco1 m :=  If (τ2 (FGΦΦ5 c0 c1 ⫠ enco1)) ≟ enco1 Then m
                             Else (If (τ2 (FGΦΦ5 c0 c1 ⫠ enco1)) ≟ enco1 Then Error Else (decS (τ2 (FGΦΦ5 c0 c1 ⫠ enco1)))).
Definition GIIO3 c0 c1 enco1 m :=  If (τ3 (FGΦΦ5 c0 c1 ⫠ enco1)) ≟ enco1 Then m
                             Else (If (τ3 (FGΦΦ5 c0 c1 ⫠ enco1)) ≟ enco1 Then Error Else (decS (τ3 (FGΦΦ5 c0 c1 ⫠ enco1)))).

(* *)
Definition GIO1 c0 c1 enco1 :=  (If (τ1 (FGΦΦ5 c0 c1 ⫠ enco1)) ≟ enco1 Then (＜ ⫠, ph2 ＞) Else (decS (τ1 (FGΦΦ5 c0 c1 ⫠ enco1)))).
Definition GIO2 c0 c1 enco1 :=  (If (τ2 (FGΦΦ5 c0 c1 ⫠ enco1)) ≟ enco1 Then (＜ ⫠, ph2 ＞) Else (decS (τ2 (FGΦΦ5 c0 c1 ⫠ enco1)))).
Definition GIO3 c0 c1 enco1 :=  (If (τ3 (FGΦΦ5 c0 c1 ⫠ enco1)) ≟ enco1 Then (＜ ⫠, ph2 ＞) Else (decS (τ3 (FGΦΦ5 c0 c1 ⫠ enco1)))).








(*----------------------------------------------------------------------------------------------------------------*)
(*-------------------------------------            Lemma26a.v          -------------------------------------------*)
(*----------------------------------------------------------------------------------------------------------------*)


(*--------      Part_one       ---------*)

Definition FΦΦ2 c0 c1 x0 x1 := (f2 [(b0 c0);  (b1 c1);  x0 ;  x1  ]). (*  *)


(* Notice that in the definition of S26, we have the boolean guard  ((τ2 (FΦΦ2 c0 c1 x0 x1)) ≟ x0) & ((τ1 (FΦΦ2 c0 c1 x0 x1)) ≟ x1)
   Which means the attacker will not replace any ballots from the honest voters
 This is only one branch of the s of Lemma 26, proofs of the other branches are analogous. *)

Definition S26 c0 c1 x0 x1 v3 :=
  If (((τ2 (FΦΦ2 c0 c1 x0 x1)) ≟ x0) & ((τ1 (FΦΦ2 c0 c1 x0 x1)) ≟ x1))
     Then (shufl (pv1 c0 c1 n1) (pv0 c0 c1 n0) (π1 v3))
     Else ⫠.


(* dvS26 is dv if the first component of FΦΦ2 is x1, the second component is x0, and the third component is
none of x0 and x1  *)

Definition dvS26 c0 c1 x0 x1 v3 :=
  If ((τ2 (FΦΦ2 c0 c1 x0 x1)) ≟ x0)
     Then (If ((τ1 (FΦΦ2 c0 c1 x0 x1)) ≟ x1)
              Then (If ((τ3 (FΦΦ2 c0 c1 x0 x1)) ≟ x0)
                       Then ⫠ (*  *)
                       Else (If ((τ3 (FΦΦ2 c0 c1 x0 x1)) ≟ x1)
                                Then ⫠ (*  *)
                                Else dv (m1 c0 c1 n1) (m0 c0 c1 n0) (v3) (shufl (pv1 c0 c1 n1) (pv0 c0 c1 n0) (π1 (v3)))))
              Else ⫠)
     Else ⫠.


(**)
Definition V1 c0 c1 x0 x1 := decS (τ1 (FΦΦ2 c0 c1 x0 x1)).
Definition V2 c0 c1 x0 x1 := decS (τ2 (FΦΦ2 c0 c1 x0 x1)).
Definition V3 c0 c1 x0 x1 := decS (τ3 (FΦΦ2 c0 c1 x0 x1)).

(* *)
Definition fiv3 c0 c1 x0 x1 := (If ((τ3 (FΦΦ2 c0 c1 x0 x1)) ≟ x0) Then Error Else decS (τ3 (FΦΦ2 c0 c1 x0 x1))).
Definition giv3 c0 c1 x0 x1 := (If ((τ3 (FΦΦ2 c0 c1 x0 x1)) ≟ x1) Then Error Else decS (τ3 (FΦΦ2 c0 c1 x0 x1))).


Inductive Voters := voter0 : Voters | voter1 : Voters.
Definition msg voter c0 c1 := match voter with voter0 => m0 c0 c1 n0 | voter1 => m1 c0 c1 n1 end.


Definition FΦΦ3 c0 c1 x0 x1 dvs :=
  (f3 [(b0 c0);  (b1 c1);  x0;  x1;  dvs ]).


(**)
Definition Enco0 c0 c1 x0 x1 dvs := ( ❴＜＜(label c0 (FΦΦ3 c0 c1 x0 x1 dvs)), kc0 ＞, ph3 ＞❵_pkS ＾ rdd0).
Definition Enco1 c0 c1 x0 x1 dvs := ( ❴＜＜(label c1 (FΦΦ3 c0 c1 x0 x1 dvs)), kc1 ＞, ph3 ＞❵_pkS ＾ rdd1).


(**)
Definition fΦΦ5 c0 c1 x0 x1 dvs :=
  (f5 [(b0 c0);  (b1 c1);  x0;  x1;  dvs ;   Enco0 c0 c1 x0 x1 dvs ;  Enco1 c0 c1 x0 x1 dvs ]).

(* *)


(**)
Definition O1 c0 c1 x0 x1 dvs := (decS (τ1 (fΦΦ5 c0 c1 x0 x1 dvs))).
Definition O2 c0 c1 x0 x1 dvs := (decS (τ2 (fΦΦ5 c0 c1 x0 x1 dvs))).
Definition O3 c0 c1 x0 x1 dvs := (decS (τ3 (fΦΦ5 c0 c1 x0 x1 dvs))).

(**)
Definition fiO1 m c0 c1 x0 x1 dvs :=
  If ((τ1 (fΦΦ5 c0 c1 x0 x1 dvs)) ≟ x0)
     Then m (**)
     Else If ((τ1 (fΦΦ5 c0 c1 x0 x1 dvs)) ≟ x0) Then Error Else (decS (τ1 (fΦΦ5 c0 c1 x0 x1 dvs))). (*  *)
Definition fiO2 m c0 c1 x0 x1 dvs :=
  If ((τ2 (fΦΦ5 c0 c1 x0 x1 dvs)) ≟ x0)
     Then m (**)
     Else If ((τ2 (fΦΦ5 c0 c1 x0 x1 dvs)) ≟ x0) Then Error Else (decS (τ2 (fΦΦ5 c0 c1 x0 x1 dvs))). (*  *)
Definition fiO3 m c0 c1 x0 x1 dvs :=
  If ((τ3 (fΦΦ5 c0 c1 x0 x1 dvs)) ≟ x0)
     Then m (**)
     Else If ((τ3 (fΦΦ5 c0 c1 x0 x1 dvs)) ≟ x0) Then Error Else (decS (τ3 (fΦΦ5 c0 c1 x0 x1 dvs))). (*  *)

Definition giO1 m c0 c1 x0 x1 dvs :=
  If ((τ1 (fΦΦ5 c0 c1 x0 x1 dvs)) ≟ x1)
     Then m (**)
     Else If ((τ1 (fΦΦ5 c0 c1 x0 x1 dvs)) ≟ x1) Then Error  Else (decS (τ1 (fΦΦ5 c0 c1 x0 x1 dvs))). (*  *)
Definition giO2 m c0 c1 x0 x1 dvs :=
  If ((τ2 (fΦΦ5 c0 c1 x0 x1 dvs)) ≟ x1)
     Then m (**)
     Else If ((τ2 (fΦΦ5 c0 c1 x0 x1 dvs)) ≟ x1) Then Error  Else (decS (τ2 (fΦΦ5 c0 c1 x0 x1 dvs))). (*  *)
Definition giO3 m c0 c1 x0 x1 dvs :=
  If ((τ3 (fΦΦ5 c0 c1 x0 x1 dvs)) ≟ x1)
     Then m (**)
     Else If ((τ3 (fΦΦ5 c0 c1 x0 x1 dvs)) ≟ x1) Then Error  Else (decS (τ3 (fΦΦ5 c0 c1 x0 x1 dvs))). (*  *)






(*--------      Part_two       ---------*)

Definition opv votervar := match votervar with | voter0 => voter1 | voter1 => voter0 end.

(* we need msgo0 and msgo1 as definitions, or the rewriting will be pretty slow.*)
Definition msgo0 c0 c1 kc :=
    let x0 := (encS (msg voter1 c0 c1) rd0) in (* *)
    let x1 := (encS (msg voter0 c0 c1) rd1) in
    let dvs := (dv (V1 c0 c1 x0 x1) (V2 c0 c1 x0 x1) (V3 c0 c1 x0 x1)) (S26 c0 c1 x0 x1 (V3 c0 c1 x0 x1)) in
    (＜＜(label c0 (FΦΦ3 c0 c1 x0 x1 dvs)), kc ＞, ph3 ＞).
Definition msgo1 c0 c1 kc :=
    let x0 := (encS (msg voter1 c0 c1) rd0) in (* *)
    let x1 := (encS (msg voter0 c0 c1) rd1) in
    let dvs := (dv (V1 c0 c1 x0 x1) (V2 c0 c1 x0 x1) (V3 c0 c1 x0 x1)) (S26 c0 c1 x0 x1 (V3 c0 c1 x0 x1)) in
    (＜＜(label c1 (FΦΦ3 c0 c1 x0 x1 dvs)), kc ＞, ph3 ＞).

(* msgo0 and msgo1 are in the "Then" branch *)
Definition msgo votervar2 c0 c1 kc := (*kc could be kc0, kc1, kc0' or kc1'*)
  match votervar2 with
  | voter0 => msgo0 c0 c1 kc
  | voter1 => msgo1 c0 c1 kc
  end.


(* FFΦΦ5 is the contexts for enco0 and enco1. Note that the plaintexts of e0 and e1 are reversed {when side is rhs}=>{prop26_13_swap_m10_m11 reveals that e0 e1 can be reversed on both sides}. *)
Definition FFΦΦ5 c0 c1 y0 y1 :=         (* *)
  let x0 := (encS (msg voter1 c0 c1) rd0) in         (* *)
  let x1 := (encS (msg voter0 c0 c1) rd1) in   (* *)
  let dvs := (dv (V1 c0 c1 x0 x1) (V2 c0 c1 x0 x1) (V3 c0 c1 x0 x1)) (S26 c0 c1 x0 x1 (V3 c0 c1 x0 x1)) in
  (f5 [(b0 c0);  (b1 c1);  x0;  x1;  dvs ;  y0 ; y1 ]).

(* voter1 means m0 and m1 has been swapped *)
Definition OO1 c0 c1 y0 y1 := (decS (τ1 (FFΦΦ5 c0 c1 y0 y1))).
Definition OO2 c0 c1 y0 y1 := (decS (τ2 (FFΦΦ5 c0 c1 y0 y1))).
Definition OO3 c0 c1 y0 y1 := (decS (τ3 (FFΦΦ5 c0 c1 y0 y1))).


(**)
Definition gOO1 c0 c1 m0 m1 y0 y1 := If ((τ1 (FFΦΦ5 c0 c1 y0 y1)) ≟ y0)
                                        Then m0
                                        Else If ((τ1 (FFΦΦ5 c0 c1 y0 y1)) ≟ y1)
                                             Then m1
                                             Else (decS (τ1 (FFΦΦ5 c0 c1 y0 y1))). (*  *)
Definition gOO2 c0 c1 m0 m1 y0 y1 := If ((τ2 (FFΦΦ5 c0 c1 y0 y1)) ≟ y0)
                                        Then m0
                                        Else If ((τ2 (FFΦΦ5 c0 c1 y0 y1)) ≟ y1)
                                             Then m1
                                             Else (decS (τ2 (FFΦΦ5 c0 c1 y0 y1))). (*  *)
Definition gOO3 c0 c1 m0 m1 y0 y1 := If ((τ3 (FFΦΦ5 c0 c1 y0 y1)) ≟ y0)
                                        Then m0
                                        Else If ((τ3 (FFΦΦ5 c0 c1 y0 y1)) ≟ y1)
                                             Then m1
                                             Else (decS (τ3 (FFΦΦ5 c0 c1 y0 y1))). (*  *)

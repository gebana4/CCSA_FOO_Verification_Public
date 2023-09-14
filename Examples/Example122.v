

  
(************************************************************************)
(* Copyright (c) 2021, Gergei Bana, Qianli Zhang                        *)
(*                                                                      *)
(* This work is licensed under the MIT license. The license is          *)
(* described in the file "LICENSE" available at the root of the source  *)
(* or at https://opensource.org/licenses/MIT                            *)
(************************************************************************)

(*   How to type unicode?
 *   1. in osx, choose Unicode hex input method, then hold option, and type the four digits code.
 *   2. in emacs, type C-x 8 ret, then type the four digits unicode and ret.
 *
 *   Unicode used in this file:
 *   1.'❴' :      U+2774
 *   2.'❵' :      U+2775
 *   3.'＾':      U+FF3E
 *   4.'π' :      U+03C0
 *   5.'＜' :     U+FF1C
 *   6.'＞' :     U+FF1E
 *   7.'≟' :      U+225F*)




Require Import Core.
Require Import RandomizedPublicKeyEncryptions.
Require Import BasicExamples.
Require Import Pair.



(*Additional function symbols*)
Parameter ERrors : Symbols Deterministic (narg 0).
Notation "'Error'" := (ConstInt Deterministic ERrors).

Parameter Lens : Symbols Deterministic (narg 1).
Notation "'Len'" := (FuncInt Deterministic (narg 1) Lens).



(* Some basic notation *)
  Notation "'|' c1 '|'" := (Len [c1]) (at level 100, left associativity).




(*We just assume all the message has the same length now.*)
Axiom EqLen : forall u u', EQ [Len [u]; Len [u']] = TRue.


Theorem If_else: forall {b u u' u''},
    bppt b -> If b Then u Else (If b Then u' Else u'') = If b Then u Else u''.
  intros. rewrite (@If_eval (fun _ => u) (fun x => If x Then u' Else u'') b). rewrite (@If_false u' u''). reflexivity. all: try ProveContext.
Qed.


Lemma If_morph_list :(*"<<<"*)  forall  {f}  , (*">>>"*)
  forall  {b x y} {u} ,
      (*"<<<"*)ContextTerm General List f -> bppt b -> (*">>>"*)
    (f (If b Then x Else y :: u))
                     = (If b Then (f (x :: u) ) Else (f (y :: u))).
Proof.
  intros.
  apply (ceq_transymm  (@If_same b (f (If b Then x Else y :: u)))).
  assert (ContextTerm General Term (fun b' : ppt => f (If b' Then x Else y :: u))). ProveContext.
  rewrite (@If_eval (fun b'=> f (If b' Then x Else y :: u)) (fun b' => f (If b' Then x Else y :: u)) b H1 H1).
  apply (@ceq_subeq (fun x' : ToL Term => If b
    Then (f (x' :: u))
    Else (f  (If FAlse Then x Else y :: u)))
    (fun x': ToL Term => (If b Then f (x :: u) Else f (y :: u))) x (If TRue
               Then x
               Else y)). ProveContext. ProveContext.
 apply ceq_symm. apply If_true.
 apply (@ceq_subeq (fun x': ToL Term => If b
    Then (f (x :: u))
    Else (f (x' :: u)))  (fun x': ToL Term  => (If b
      Then f (x :: u)
      Else f (y :: u))) y (If FAlse
               Then x
               Else y)). ProveContext. ProveContext.
 apply ceq_symm. apply If_false.
 apply ceq_ref. Provebool.
Qed.

(********************************************
 *******        Example 12.2          *******
 ********************************************)

Module Example122.



(* Encryption scheme using key generation and random seed from 1 nonce only *)

(*Key generation*)
Parameter Pkeys : Symbols Deterministic (narg 1) .
Notation "'Pkey'" := (FuncInt Deterministic (narg 1) Pkeys).


Parameter Skeys x: Symbols Deterministic (narg 1).
Notation "'Skey'" := (FuncInt Deterministic (narg 1) Skeys).


(*Random input*)
Parameter Rands : Symbols Deterministic (narg 1).
Notation "'Rand'" := (FuncInt Deterministic (narg 1) Rands).



(*Encryption*)
Parameter Encs : Symbols Deterministic (narg 3).
Notation "'Enc'" := (FuncInt Deterministic (narg 3) Encs).
Notation "'❴' c1 '❵_' c2 '＾' c3 " := (Enc [c1; c2; c3]) (at level 100, left associativity).  (*'❴' is U+23A1 U+23A4, '＾' is U+02C6*)

(*Decryption*)
Parameter Decs : Symbols Deterministic (narg 2).
Notation "'Dec'" := (FuncInt Deterministic (narg 2) Decs).


(*Decrypting the encryption gives plaintext*)
Axiom (*metaaxiom*) decenc :
      forall {m : ppt} {n n'},
        Dec [❴ m ❵_(Pkey [n]) ＾ (Rand [n']);  (Skey [n])] = m.

  
  Notation "'cca_2'" := (CCA2 Len Enc Dec Pkey Skey Rand Error).
  Notation "'adv1' c1" := (adv (1) [c1]) (at level 101, left associativity).
  Notation n   := (nonce 0).        (* n  *)
  Notation n'  := (nonce 1).        (* n' *)
  Notation pk1 := (Pkey  [nonce 2]). (* pk1, sk1 *)
  Notation sk1 := (Skey  [nonce 2]).
  Notation Dec_sk1 c := (Dec [c; Skey [nonce 2]]).
  Notation pk2 := (Pkey  [nonce 3]). (* pk2, sk2 *)
  Notation sk2 := (Skey [nonce 3]).
  Notation Dec_sk2 c := (Dec [c; Skey [nonce 3]]).
  Notation r1  := (Rand [nonce 4]). (* r1 *)
  Notation r2  := (Rand [nonce 5]). (* r2 *)
  Notation n5  := (nonce 6).        (* n5 *)
  Notation n6  := (nonce 7).        (* n6 *)
  Notation n7  := (nonce 8).        (* n7 *)




(***************************************************************
 * (2): t[..sk1..] ~ t[..n6..] and (3): u[..sk1..] ~ u[..n6..] *
 ***************************************************************)

Proposition ex12_1_3: cca_2 -> forall n'', n'' <> 3 -> n'' <> 4 ->
  [❴＜sk1     , n5＞❵_pk2 ＾ r1;   ❴＜π2 Dec_sk2 (adv1(❴＜sk1 ,     n5＞❵_pk2 ＾ r1)), n＞❵_pk1 ＾ r2;   (nonce n'')]
 ~
  [❴＜Skey[n6], n5＞❵_pk2 ＾ r1;   ❴＜π2 Dec_sk2 (adv1(❴＜Skey[n6], n5＞❵_pk2 ＾ r1)), n＞❵_pk1 ＾ r2;   (nonce n'')].
Proof.
  intros cca2 n'' frpk frr.
  assert (forall n8 , [❴＜Skey [n8], n5＞❵_pk2 ＾ r1;   ❴＜π2 Dec_sk2 (adv1 (❴＜Skey [n8], n5＞❵_pk2 ＾ r1)), n＞❵_pk1 ＾ r2;   (nonce n'')]
                =
         ((fun x => [x; ❴＜π2 (If adv1 x ≟ x Then ＜sk1, n5＞ Else (If adv1 x ≟ x Then Error Else Dec_sk2 (adv1 x))), n＞❵_pk1 ＾ r2; (nonce n'')])
                      (If |＜sk1, n5＞| ≟ |＜Skey [n6], n5＞| Then ❴＜Skey [n8], n5＞❵_pk2 ＾ r1 Else Error))).
  intros n8.
  repeat rewrite EqLen in *; repeat rewrite If_true in *; rewrite If_else. 
  rewrite <- (@If_same ((adv1 ❴＜Skey [n8], n5＞❵_pk2 ＾ r1) ≟ (❴＜ Skey [n8], n5＞❵_pk2 ＾r1)) (adv1 ❴＜Skey [n8], n5＞❵_pk2 ＾r1)) at 1.
  rewrite Example7_3.
  rewrite (@If_morph_list (fun x => Dec x)).
  rewrite decenc.
  repeat rewrite (@If_morph_list (fun x => Proj2 x)); repeat rewrite Proj2Pair in *.
  reflexivity.
  all : ProveContext. all: Provebool.
  rewrite (H (nonce 2)). rewrite H.
  apply (cca2 [nonce 3] [nonce 4]  (fun x => [x; ❴＜π2 (If adv1 x ≟ x Then ＜sk1, n5＞ Else (If adv1 x ≟ x Then Error Else Dec_sk2 (adv1 x))), n＞❵_pk1 ＾r2; (nonce n'')]) (＜sk1, n5＞) (＜Skey [n6], n5＞)).
  clear cca2.
  all: ProveCCA2. Qed.

(***********************************************************
 * (2): t[..n..] ~ t[..n7..] and (3): u[..n..] ~ u[..n7..] *
 ***********************************************************)

Proposition ex12_many: cca_2 -> forall n'' ,  n'' <> 2 -> n'' <> 5 ->
  [❴＜Skey [n6], n5＞❵_pk2 ＾ r1;   ❴＜π2 Dec_sk2 (adv1 ❴＜Skey [n6], n5＞❵_pk2 ＾ r1), n＞ ❵_pk1 ＾ r2;   (nonce n'')]
  ~
  [❴＜Skey [n6], n5＞❵_pk2 ＾ r1;   ❴＜π2 Dec_sk2 (adv1 ❴＜Skey [n6], n5＞❵_pk2 ＾ r1), n7＞❵_pk1 ＾ r2;   (nonce n'')].
Proof.
  intros cca2 n'' frpk frr.
  assert (forall n8 , [❴＜Skey [n6], n5＞❵_pk2 ＾r1;   ❴＜π2 Dec_sk2 (adv1 ❴＜Skey [n6], n5＞❵_pk2 ＾ r1), n8＞ ❵_pk1 ＾r2;   (nonce n'')]
                =
         ((fun x => [❴＜Skey [n6], n5＞❵_pk2 ＾r1;   x;   (nonce n'')])
            (If |＜π2 Dec_sk2 (adv1 ❴＜Skey [n6], n5＞❵_pk2 ＾r1), n ＞| ≟ |＜π2 Dec_sk2 (adv1 ❴＜Skey [n6], n5＞❵_pk2 ＾r1), n7＞|
                Then ❴＜π2 Dec_sk2 (adv1 ❴＜Skey [n6], n5＞❵_pk2 ＾r1), n8＞ ❵_pk1 ＾r2 Else Error))).
  intros n8.
  repeat rewrite EqLen in *; repeat rewrite If_true in *; reflexivity.
  rewrite H. rewrite H.
  apply (cca2 [nonce 2] [nonce 5]  (fun x => [❴＜Skey [n6], n5＞❵_pk2 ＾r1;   x;   nonce n'' ]) (＜π2 Dec_sk2 (adv1 ❴＜Skey [n6], n5＞❵_pk2 ＾r1), n ＞)  (＜π2 Dec_sk2 (adv1 ❴＜Skey [n6], n5＞❵_pk2 ＾r1), n7＞)).
  all: ProveCCA2. Qed.

(*************************
 **  Final Proposition  **
 *************************)

Proposition ex12 : cca_2 ->
  [❴＜sk1, n5＞❵_pk2 ＾r1;   ❴＜π2 Dec_sk2 (adv1 ❴＜sk1, n5＞❵_pk2 ＾r1), n＞ ❵_pk1 ＾r2;   n]
  ~
  [❴＜sk1, n5＞❵_pk2 ＾r1;   ❴＜π2 Dec_sk2 (adv1 ❴＜sk1, n5＞❵_pk2 ＾r1), n＞ ❵_pk1 ＾r2;   n'].
Proof.
  intros.
  assert(
    [❴＜Skey [n6], n5＞❵_pk2 ＾ r1;   ❴＜π2 Dec_sk2 (adv1 ❴＜Skey [n6], n5＞❵_pk2 ＾ r1), n7＞ ❵_pk1 ＾ r2]
   ~
    [❴＜Skey [n6], n5＞❵_pk2 ＾ r1;   ❴＜π2 Dec_sk2 (adv1 ❴＜Skey [n6], n5＞❵_pk2 ＾ r1), n7＞ ❵_pk1 ＾ r2]) as ex12_middle.
  apply cind_ref.
  apply (FreshInd n n') in ex12_middle.
  apply (@cind_funcapp (fun lc =>((skipn 1 lc) ++ (firstn 1 lc)))) in ex12_middle; simpl in ex12_middle.
  rewrite ex12_1_3; auto.
  rewrite ex12_many; auto.
  rewrite ex12_middle; auto.
  rewrite <- ex12_many; auto.
  rewrite <- ex12_1_3; auto.
  reflexivity.
  all : try ProveContext.
  all : try ProveFresh.
Qed.

End Example122.

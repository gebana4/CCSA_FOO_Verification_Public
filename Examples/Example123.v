(************************************************************************)
(* Copyright (c) 2022, Gergei Bana, Qianli Zhang                        *)
(*                                                                      *)
(* This work is licensed under the MIT license. The license is          *)
(* described in the file "LICENSE" available at the root of the source  *)
(* or at https://opensource.org/licenses/MIT                            *)
(************************************************************************)


Require Import Coq.Lists.List.
Import ListNotations.
Require Export Core.
Require Export BasicExamples.
Require Export Pair.
Require Export Triple.
Require Export Length.
Require Export RandomizedPublicKeyEncryptions.




(*-------------- Public key Enc ----------------*)


(* default error function symbol *)
Parameter Errors : Symbols Deterministic (narg 0).
Notation "'Error'" := (ConstInt Deterministic Errors).
Notation "⫠"  := (ConstInt Deterministic Errors). (* U+2AE0 *)

(*Key generation: honest public key - secret key generation is applied on the same fresh nonce *)
Parameter Pkeys : Symbols Deterministic (narg 1) .
Notation "'Pkey'" := (FuncInt Deterministic (narg 1) Pkeys).


(* secret key generation function symbol *)
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
Notation dec c sk := (Dec [c; sk]).







(*-------------- Axioms and their implication ----------------*)

(* we claims that, the group {Len Enc Dec Pkey Skey Rand Error} has the CCA2 security property *)
Axiom cca_2 : (CCA2 Len Enc Dec Pkey Skey Rand Error).

Lemma cca2 : (CCA2L Len Enc Dec Pkey Skey Rand Error).
Proof.
  apply CCA2toCCA2L.
  - apply cca_2.
Qed.

(* we claims, messages encrypted with a pkey can be decrypted with skey generated from the same nonce as pkey. *)
Axiom  decenc :
      forall {m : ppt} {n n'},
        Dec [❴ m ❵_(Pkey [n]) ＾ (Rand [n']);  (Skey [n])] = m.

Axiom NonceLen : forall n m , (| nonce n |) = (| nonce m |).

Axiom PairLen :
  forall (x x' y y': ppt) , (| x |) = (| x' |) ->  (| y |) = (| y' |) ->  (| Pair [x ; y ] |) = (| Pair [x' ; y' ] |).

Axiom skLen :  forall n m , (| Skey [nonce n] |) = (| Skey [nonce m] |).





(*-------------- Function symbols ----------------*)

(* *)
Notation adv1 Φ1 := (adv (1) Φ1).  (*   *)
Notation adv2 Φ2 := (adv (2) Φ2).  (*   *)


(* public key of agent1 and BB *)
Notation pk1    := (Pkey [nonce 0]). (*  *)
Notation sk1    := (Skey [nonce 0]). (*  *)
Notation pkBB   := (Pkey [nonce 1]). (*  *)
Notation skBB   := (Skey [nonce 1]). (*  *)

(* r1 represents randomness by agent1 at phase1 
   r2 represents randomness by agent1 at phase2 
   rBB represents randomness by BB *)
Notation r1 := (Rand [nonce 2]).
Notation r2 := (Rand [nonce 3]).
Notation rBB := (Rand [nonce 4]).

(* nonce n1 n2 are from honest parties 
   nonce n2' is from attacker *)
Notation n1 := (nonce 5).
Notation n2 := (nonce 6).
Notation n2' := (nonce 7).

(* sk1' is secret key of attacker *)
Notation sk1'    := (Skey [nonce 10]). (*  *)

Notation Dec1 c  := (Dec [c; sk1]).  (*  *)
Notation DecBB c := (Dec [c; skBB]).  (*  *)

(*  *)
Lemma decGame: forall m r c,
(*-----------------------------------*)
    (DecBB c) = If (c ≟ (❴m❵_pkBB ＾ (Rand [nonce r]))) Then m Else (DecBB c).
Proof.
  intros.
  rewrite <- (@If_same (c ≟ (❴m❵_pkBB ＾ (Rand [nonce r]))) c) at 1.
  rewrite (@Eq_branch (c) (❴m❵_pkBB ＾ (Rand [nonce r]))  (fun x => x) _ ).
  rewrite (@If_morph (fun x => DecBB x) (c ≟ (❴m❵_pkBB ＾ (Rand [nonce r]))) _ _ ).
  rewrite decenc.
  reflexivity.
  all : ProveContext.
Qed.

Lemma decIfThenElse: forall m r c,
(*-----------------------------------*)
    (DecBB  c)
    =
    If (c ≟ (❴m❵_pkBB ＾ (Rand [nonce r])))
       Then m
       Else (If (c ≟ (❴m❵_pkBB ＾ (Rand [nonce r])))
                Then Error
                Else DecBB c).
Proof.
  intros.
  rewrite (@If_eval (fun _ => _) (fun b => If b Then Error Else _) (c ≟ (❴m❵_pkBB ＾ (Rand [nonce r])))).
  rewrite If_false.
  rewrite <- decGame.
  reflexivity.
  all: ProveboolandContext.
Qed.

Lemma decSimpl: forall {b m c error }, bppt b ->
(*-----------------------------------*)
    (If b
       Then m
       Else If b Then error Else c)
    =
    (If b Then m Else c).
Proof.
  intros.
  rewrite (@If_eval (fun _ => _) (fun x => If x Then error Else c) ).
  rewrite If_false.
  reflexivity.
  all: ProveboolandContext.
Qed.


(* *)



(* ========================================================================== *)

(* ex12_lemma0 demonstrates that sk1 in the encryptions can be replaced with sk1' *)

Proposition ex12_lemma0 : forall n, (n = nonce 6) \/ (n = nonce 7) -> 
  [❴＜sk1, n1＞❵_pkBB  ＾  r1;
   ❴＜π2 (DecBB (adv1 [❴＜sk1, n1＞❵_pkBB ＾ r1])), n＞ ❵_pkBB ＾ r2;
   ❴  π2 (DecBB (adv2 [❴＜sk1, n1＞❵_pkBB ＾ r1;   ❴＜π2 DecBB (adv1 [❴＜sk1, n1＞❵_pkBB ＾ r1]), n＞ ❵_pkBB ＾ r2]))❵_pk1 ＾ rBB  ;
   n2]
 ~
 [❴＜sk1', n1＞❵_pkBB  ＾  r1;
   ❴＜π2 (DecBB (adv1 [❴＜sk1', n1＞❵_pkBB ＾ r1])), n＞ ❵_pkBB ＾ r2;
   ❴  π2 (DecBB (adv2 [❴＜sk1', n1＞❵_pkBB ＾ r1;   ❴＜π2 DecBB (adv1 [❴＜sk1', n1＞❵_pkBB ＾ r1]), n＞ ❵_pkBB ＾ r2]))❵_pk1 ＾ rBB  ;
   n2].
Proof.
  intros. 
  
(* RHS *)
  rewrite (decGame (＜sk1', n1＞) 2 (adv1 [❴＜sk1', n1＞❵_pkBB ＾ r1])).
  rewrite (decGame (＜sk1', n1＞) 2 (adv2 [❴＜sk1', n1＞❵_ pkBB ＾ r1;
                                          ❴＜π2 If adv1 [❴ ＜sk1', n1 ＞ ❵_ pkBB ＾ r1] ≟ ❴ ＜ sk1', n1 ＞ ❵_pkBB ＾ r1 Then ＜ sk1', n1 ＞
                                                Else DecBB (adv1 [❴ ＜ sk1', n1 ＞ ❵_ pkBB ＾ r1]), n ＞ ❵_ pkBB ＾ r2])).
  rewrite (@If_morph (fun x => π2 x)). rewrite Proj2Pair.
  rewrite (@If_morph (fun x => π2 x)). rewrite Proj2Pair.

(* LHS *) 
  rewrite (decIfThenElse (＜sk1, n1＞) 2 (adv1 [❴＜sk1, n1＞❵_pkBB ＾ r1])) at 1 2.
  rewrite (decIfThenElse (＜sk1, n1＞) 2 (adv2 [❴＜sk1, n1＞❵_pkBB ＾ r1;
                                               ❴＜ π2 If adv1 [❴＜sk1, n1＞❵_pkBB ＾ r1] ≟ ❴＜sk1, n1＞❵_ pkBB ＾ r1 Then ＜ sk1, n1 ＞
                                                Else If adv1 [❴＜sk1, n1＞❵_pkBB ＾ r1] ≟ ❴＜sk1, n1＞❵_ pkBB ＾ r1 Then ⫠ Else DecBB (adv1 [❴ ＜sk1, n1 ＞ ❵_ pkBB ＾ r1]), n ＞ ❵_ pkBB ＾ r2])). 
  pose (cca2 [nonce 1] [nonce 2]
  (fun x => [x;
          ❴ ＜ π2 (If adv1 [x] ≟ x Then ＜ sk1, n1 ＞ Else If adv1 [x] ≟ x Then ⫠ Else DecBB (adv1 [x])), n ＞ ❵_ pkBB ＾ r2;
          ❴ π2 (If adv2 [x; ❴ ＜ π2 (If adv1 [x] ≟ x Then ＜ sk1, n1 ＞ Else If adv1 [x] ≟ x Then ⫠ Else DecBB (adv1 [x])), n ＞ ❵_ pkBB ＾ r2] ≟ x Then ＜ sk1, n1 ＞
                Else If adv2 [x; ❴ ＜ π2 (If adv1 [x] ≟ x Then ＜ sk1, n1 ＞ Else If adv1 [x] ≟ x Then ⫠ Else DecBB (adv1 [x])), n ＞ ❵_ pkBB ＾ r2] ≟ x Then ⫠
                     Else DecBB
                    (adv2 [x; ❴ ＜ π2 (If adv1 [x] ≟ x Then ＜ sk1, n1 ＞ Else If adv1 [x] ≟ x Then ⫠ Else DecBB (adv1 [x])), n ＞ ❵_ pkBB ＾ r2])) ❵_ pk1 ＾ rBB; n2])
             (＜ sk1, n1 ＞) (＜ sk1' , n1 ＞)) as claim0; simpl in claim0; rewrite claim0; clear claim0.
  rewrite decSimpl. rewrite decSimpl.
  rewrite (@If_morph (fun x => π2 x)). rewrite Proj2Pair.
  rewrite (@If_morph (fun x => π2 x)). rewrite Proj2Pair.

(* LHS = RHS *)
  reflexivity.

(* Context check *)   
  all: ProveboolandContext.
  all: ProveCCA2. all : try (destruct H; rewrite H; ProveCCA2).
  apply PairLen.
  apply skLen.
  reflexivity.
Qed.
 

(* ex12_lemma1 demonstrates that when sk1 is not inside the encryption, n2 can be replaced with n2'  *)

Proposition ex12_lemma1 :
  [❴＜sk1', n1＞❵_pkBB  ＾  r1;
   ❴＜π2 (DecBB (adv1 [❴＜sk1', n1＞❵_pkBB ＾ r1])), n2＞ ❵_pkBB ＾ r2;
   ❴  π2 (DecBB (adv2 [❴＜sk1', n1＞❵_pkBB ＾ r1;   ❴＜π2 DecBB (adv1 [❴＜sk1', n1＞❵_pkBB ＾ r1]), n2＞ ❵_pkBB ＾ r2]))❵_pk1 ＾ rBB  ; n2]
 ~
  [❴＜sk1', n1＞❵_pkBB  ＾  r1;
   ❴＜π2 (DecBB (adv1 [❴＜sk1', n1＞❵_pkBB ＾ r1])), n2'＞ ❵_pkBB ＾ r2;
   ❴ (π2 (DecBB (adv2 [❴＜sk1', n1＞❵_pkBB ＾ r1;   ❴＜π2 DecBB (adv1 [❴＜sk1', n1＞❵_pkBB ＾ r1]), n2'＞ ❵_pkBB ＾ r2]))) ❵_ pk1 ＾ rBB; n2].
Proof.

  (*  *) 
  rewrite (decIfThenElse (＜π2 DecBB (adv1 [❴＜sk1', n1＞❵_pkBB ＾ r1]), n2＞) 3
                         (adv2 [❴＜sk1', n1＞❵_pkBB ＾ r1;   ❴＜π2 DecBB (adv1 [❴＜sk1', n1＞❵_pkBB ＾ r1]), n2＞ ❵_pkBB ＾ r2])) at 1.
  rewrite (@If_morph (fun x => π2 x)). rewrite Proj2Pair.
  (*  *)
  pose (cca2 [nonce 1] [nonce 3]
  (fun x => [❴ ＜ sk1', n1 ＞ ❵_ pkBB ＾ r1; x;
  ❴ If adv2 [❴ ＜ sk1', n1 ＞ ❵_ pkBB ＾ r1; x] ≟ x
    Then n2
    Else π2 (If adv2 [❴ ＜ sk1', n1 ＞ ❵_ pkBB ＾ r1; x]
                ≟ x Then ⫠
             Else DecBB (adv2 [❴ ＜ sk1', n1 ＞ ❵_ pkBB ＾ r1; x])) ❵_ pk1 ＾ rBB; n2])
      (＜ π2 DecBB (adv1 [❴ ＜ sk1', n1 ＞ ❵_ pkBB ＾ r1]), n2 ＞ )
      (＜ π2 DecBB (adv1 [❴ ＜ sk1', n1 ＞ ❵_ pkBB ＾ r1]), n2' ＞ )) as claim1; simpl in claim1; rewrite claim1; clear claim1.
  rewrite (@If_morph (fun x => π2 x)).
  rewrite decSimpl.

  (*  *)
  rewrite (decGame (＜ π2 DecBB (adv1 [❴ ＜ sk1', n1 ＞ ❵_ pkBB ＾ r1]), n2' ＞) 3
                         (adv2 [❴ ＜ sk1', n1 ＞ ❵_ pkBB ＾ r1; ❴ ＜ π2 DecBB (adv1 [❴ ＜ sk1', n1 ＞ ❵_ pkBB ＾ r1]), n2' ＞ ❵_ pkBB ＾ r2])) at 2.
  rewrite (@If_morph (fun x => π2 x)). rewrite Proj2Pair.
  
  (*  *)
  pose (cca2 [nonce 0] [nonce 4]
  (fun x =>  [❴ ＜ sk1', n1 ＞ ❵_ pkBB ＾ r1; ❴ ＜ π2 DecBB (adv1 [❴ ＜ sk1', n1 ＞ ❵_ pkBB ＾ r1]), n2' ＞ ❵_ pkBB ＾ r2; x; n2])
  (If adv2 [❴ ＜ sk1', n1 ＞ ❵_ pkBB ＾ r1; ❴ ＜ π2 DecBB (adv1 [❴ ＜ sk1', n1 ＞ ❵_ pkBB ＾ r1]), n2' ＞ ❵_ pkBB ＾ r2] ≟ ❴ ＜ π2 DecBB (adv1 [❴ ＜ sk1', n1 ＞ ❵_ pkBB ＾ r1]), n2' ＞ ❵_ pkBB ＾ r2
    Then n2 Else π2 DecBB (adv2 [❴ ＜ sk1', n1 ＞ ❵_ pkBB ＾ r1; ❴ ＜ π2 DecBB (adv1 [❴ ＜ sk1', n1 ＞ ❵_ pkBB ＾ r1]), n2' ＞ ❵_ pkBB ＾ r2]))
  (If adv2 [❴ ＜ sk1', n1 ＞ ❵_ pkBB ＾ r1; ❴ ＜ π2 DecBB (adv1 [❴ ＜ sk1', n1 ＞ ❵_ pkBB ＾ r1]), n2' ＞ ❵_ pkBB ＾ r2] ≟ ❴ ＜ π2 DecBB (adv1 [❴ ＜ sk1', n1 ＞ ❵_ pkBB ＾ r1]), n2' ＞ ❵_ pkBB ＾ r2
    Then n2' Else π2 DecBB (adv2 [❴ ＜ sk1', n1 ＞ ❵_ pkBB ＾ r1; ❴ ＜ π2 DecBB (adv1 [❴ ＜ sk1', n1 ＞ ❵_ pkBB ＾ r1]), n2' ＞ ❵_ pkBB ＾ r2]))) as claim2; simpl in claim2; rewrite claim2; clear claim2.

  reflexivity.

  all: ProveboolandContext.
  all: ProveCCA2.
  repeat rewrite (@If_morph (fun x => | x |)).
  simpl. rewrite (NonceLen 6 7).
  reflexivity.
  all : ProveContext.
  apply PairLen.
  reflexivity.
  apply NonceLen.
Qed.


(* ex12_mod shows that the attacker cannot distinguish whether n2 or n2' is encrypted  *)

Proposition ex12_mod :
  [❴＜sk1, n1＞❵_pkBB  ＾  r1;
   ❴＜π2 (DecBB (adv1 [❴＜sk1, n1＞❵_pkBB ＾ r1])), n2＞ ❵_pkBB ＾ r2;
   ❴  π2 (DecBB (adv2 [❴＜sk1, n1＞❵_pkBB ＾ r1;   ❴＜π2 DecBB (adv1 [❴＜sk1, n1＞❵_pkBB ＾ r1]), n2＞ ❵_pkBB ＾ r2]))❵_pk1 ＾ rBB  ;
   n2]
 ~
 [❴＜sk1, n1＞❵_pkBB  ＾  r1;
   ❴＜π2 (DecBB (adv1 [❴＜sk1, n1＞❵_pkBB ＾ r1])), n2＞ ❵_pkBB ＾ r2;
   ❴  π2 (DecBB (adv2 [❴＜sk1, n1＞❵_pkBB ＾ r1;   ❴＜π2 DecBB (adv1 [❴＜sk1, n1＞❵_pkBB ＾ r1]), n2＞ ❵_pkBB ＾ r2]))❵_pk1 ＾ rBB  ;
   n2'].
Proof.

(* First we use ex12_lemma0 to replace sk1 with sk1' on the LHS *)  
  rewrite ex12_lemma0.

(* Then we use ex12_lemma1 to replace n2 with n2' on the LHS *)  
  rewrite ex12_lemma1.

(* We also need to use ex12_lemma0 to replace sk1' back to sk1 on the LHS *)  
  rewrite <- ex12_lemma0.

(* Finally we use {FreshInd + FuncApp} to show how to n2 and n2' are swapped meanwhile keeping indistinguish.
   The order of nonce introduced is here: [0; 5; 1; 2; 7; 3; 6; 4] ~ [0; 5; 1; 2; 6; 3; 7; 4] 
   Finally we will have [sk1; pk1; n1; pkBB; skBB; r1; n2'; r2; n2] ~ [sk1; pk1; n1; pkBB; skBB; r1; n2; r2; n2' ] *)

(* FreshInd *)  
  assert ([] ~ []) as H. reflexivity.
  apply (FreshInd (nonce (0)) (nonce (0))) in H.
  apply (FreshInd (nonce (5)) (nonce (5))) in H.
  apply (FreshInd (nonce (1)) (nonce (1))) in H.
  apply (FreshInd (nonce (2)) (nonce (2))) in H.
  apply (FreshInd (nonce (7)) (nonce (6))) in H.
  apply (FreshInd (nonce (3)) (nonce (3))) in H.
  apply (FreshInd (nonce (6)) (nonce (7))) in H.
  apply (FreshInd (nonce (4)) (nonce (4))) in H.


(* FuncApp *)    
  apply (@cind_funcapp (fun lx =>
        [(Skey [Nth 7 lx]) ; (Pkey [Nth 7 lx]); (Nth 6 lx);  (Pkey [Nth 5 lx]); (Skey [Nth 5 lx]); (Rand [Nth 4 lx]); (Nth 3 lx); (Rand [Nth 2 lx]); (Nth 1 lx); (Rand [Nth 0 lx])])) in H;
    unfold Nth in H; simpl in H.
  apply (@cind_funcapp (fun lx => let sk1 := Nth 0 lx in
                               let pk1 := Nth 1 lx in
                               let n1 := Nth 2 lx in
                               let pkBB := Nth 3 lx in
                               let skBB := Nth 4 lx in
                               let r1 := Nth 5 lx in
                               let n2' := Nth 6 lx in
                               let r2 := Nth 7 lx in
                               let n2 := Nth 8 lx in
                               let rBB := Nth 9 lx in                               
                               let enc0 := (❴ ＜ sk1, n1 ＞ ❵_ pkBB ＾ r1) in
                               let enc1 := (❴ ＜ π2 (dec (adv1 [enc0]) skBB), n2' ＞ ❵_ pkBB ＾ r2) in
                               let enc2 := (❴ π2 (dec (adv2 [enc0; enc1]) skBB) ❵_ pk1 ＾ rBB) in 
        [enc0; enc1; enc2; n2])) in H;
    unfold Nth in H; simpl in H.
  apply H.

(* Context Check and Freshness Check *)
  simpl; ProveContext.
  ProveContext.
  all : ProveFresh; auto.
  all : lia.
Qed.  




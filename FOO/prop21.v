(************************************************************************)
(* Copyright (c) 2022, Gergei Bana, Rohit Chadha, Ajay Kumar Eeralla,   *)
(* Qianli Zhang                                                         *)
(*                                                                      *)
(* This work is licensed under the MIT license. The license is          *)
(* described in the file "LICENSE" available at the root of the source  *)
(* or at https://opensource.org/licenses/MIT                            *)
(************************************************************************)

Require Import Coq.micromega.Lia.
Require Export contexts.
(* Require Export prop11. *)
Import ListNotations.


(********************************************************************)

(* Proposition 15.8 *)
Proposition DoNegElim: forall b, bppt b -> (! ! b) = b.
  intros.
  rewrite (@If_morph (fun x => If x Then FAlse Else TRue)).
  rewrite If_true.
  rewrite If_false.
  rewrite <- If_tf.
  reflexivity.
  all : ProveboolandContext.
Qed.


(* Prop21 is similar to the Blindness property of a blind-signature scheme,  
   but states that even if the attacker has access to the acceptance checks, the blind-signature game will still be indistinguishable. *)

Proposition prop21: forall n0 n1 z, forall m0 m1 t :ppt, forall t0 t1,
      n0 <> n1 ->
  Fresh (nonce n0) (m0 :: m1 :: t :: z) -> FreshTermc (nonce n0) t0 -> FreshTermc (nonce n0) t1 ->
  Fresh (nonce n1) (m0 :: m1 :: t :: z) -> FreshTermc (nonce n1) t0 -> FreshTermc (nonce n1) t1 ->
  let bn0 := Brand (nonce n0) in
  let bn1 := Brand (nonce n1) in
  let ti00 := t0 [b m0 t bn0; b m1 t bn1] in
  let ti01 := t1 [b m0 t bn0; b m1 t bn1] in
  let ti10 := t0 [b m1 t bn0; b m0 t bn1] in
  let ti11 := t1 [b m1 t bn0; b m0 t bn1] in
  z ++ [b m0 t bn0; b m1 t bn1; acc m0 t bn0 ti00 & acc m1 t bn1 ti01 ; If acc m0 t bn0 ti00 & acc m1 t bn1 ti01 Then ＜ ub m0 t bn0 ti00, ub m1 t bn1 ti01 ＞ Else (＜ ⫠, ⫠ ＞)]
  ~
  z ++ [b m1 t bn0; b m0 t bn1; acc m1 t bn0 ti10 & acc m0 t bn1 ti11 ; If acc m1 t bn0 ti10 & acc m0 t bn1 ti11 Then ＜ ub m0 t bn1 ti11, ub m1 t bn0 ti10 ＞ Else (＜ ⫠, ⫠ ＞)].
Proof.
  intros n0 n1 z m0 m1 t t0 t1  noteq. intros.
  pose (Blindness z m0 m1 t (nonce n0) (nonce n1) t0 t1 H H0 H1 H2 H3 H4) as c. simpl in c.
  apply (@cind_funcapp (fun lc =>  (firstn (length z) lc) ++ [(Nth (length z + 0) lc); (Nth (length z + 1) lc); (Nth (length z + 2) lc); ((π1 (Nth (length z + 2) lc)) ≟ ⫠) ])) in c;
    unfold Nth in c;
    repeat rewrite app_nth2_plus in c;
    repeat rewrite firstn_app_exact in c;
    unfold nth in c; simpl in c. 
  rewrite (@If_morph (fun x => (π1 x) ≟ ⫠)) in c.
  rewrite (@If_morph (fun x => (π1 x) ≟ ⫠)) in c.
  repeat rewrite proj1pair in c.
  rewrite ceqeq in c. (*  *)
  fold bn0 bn1 in c. fold ti00 ti01 ti10 ti11 in c. 
  rewrite (AndComm (acc m1 t bn0 ti10) (acc m0 t bn1 ti11)) in c.
  rewrite (@AndGuard2 (acc m0 t bn0 ti00) (acc m1 t bn1 ti01) (ub m0 t bn0 ti00 ≟ ⫠) FAlse TRue) in c.
  rewrite (@AndGuard2 (acc m0 t bn1 ti11) (acc m1 t bn0 ti10) (ub m0 t bn1 ti11 ≟ ⫠) FAlse TRue) in c.
  rewrite (AndComm (acc m0 t bn1 ti11) (acc m1 t bn0 ti10)) in c.
  unfold bn0 , bn1 in c.
  rewrite (UbNotUndefined m0 t (nonce n0) ti00) in c.
  rewrite (UbNotUndefined m0 t (nonce n1) ti11) in c.
  fold bn0 bn1 in c.
  apply (@cind_funcapp (fun lc =>  (firstn (length z) lc) ++ [(Nth (length z + 0) lc); (Nth (length z + 1) lc); ! (Nth (length z + 3) lc); (Nth (length z + 2) lc) ])) in c;
    unfold Nth in c; repeat rewrite app_nth2_plus in c; repeat rewrite firstn_app_exact in c; unfold nth in c; simpl in c.
  rewrite DoNegElim in c. rewrite DoNegElim in c.
  auto.
  all : Provebool.
  all : ProveboolandContext.
  { apply frConc.
  assert (t = Nth 2 (m0 :: m1 :: t :: z)).
  auto.
  rewrite H5.
  ProveFresh.
  assert (m0 = Nth 0 (m0 :: m1 :: t :: z)).
  auto. rewrite H5.
  ProveFresh. }
  2: { apply frConc.
  assert (t = Nth 2 (m0 :: m1 :: t :: z)).
  auto.
  rewrite H5.
  ProveFresh.
  assert (m0 = Nth 0 (m0 :: m1 :: t :: z)).
  auto. rewrite H5.
  ProveFresh. }
  unfold ti01. unfold ti11. apply FreshTermcfromNonceList in H4.
  destruct H4. destruct H4. destruct H4. destruct H5.
  destruct H6. rewrite H7.
  apply  UbNUDAttContListTerm. assumption.
  apply  UbNUDContextApp. apply UbNUDFresh. assumption.
  apply  UbNUDContextConc.
  apply UbNUDFreshTerm.
  inversion H2. inversion H12. inversion H17. unfold bn0.
  ProveFresh. unfold bn1. apply UbNUDContextConc. apply UbNUDBlindSign.
  inversion H2; assumption. inversion H2. inversion H12. inversion H17; assumption.
  apply UbNUDFresh. ProveFresh.
   unfold ti00. unfold ti01. apply FreshTermcfromNonceList in H0.
  destruct H0. destruct H0. destruct H0. destruct H5.
  destruct H6. rewrite H7.
  apply  UbNUDAttContListTerm. assumption.
  apply  UbNUDContextApp. apply UbNUDFresh. assumption.
  apply  UbNUDContextConc.
  apply UbNUDBlindSign.
  inversion H; assumption. inversion H. inversion H12. inversion H17; assumption.
  apply UbNUDFresh. unfold bn1.
  inversion H. inversion H12. inversion H17.
  ProveFresh.
Qed.

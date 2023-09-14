(************************************************************************)
(* Copyright (c) 2022, Gergei Bana, Rohit Chadha, Ajay Kumar Eeralla,   *)
(* Qianli Zhang                                                         *)
(*                                                                      *)
(* This work is licensed under the MIT license. The license is          *)
(* described in the file "LICENSE" available at the root of the source  *)
(* or at https://opensource.org/licenses/MIT                            *)
(************************************************************************)


Require Import Coq.micromega.Lia.
Require Export prop21.
Import ListNotations.



(*************************************************************************)
(***** In this first part of the proof we replace n0 with a fresh n0'*****)
(***** on both sides using CCA2 security of encryption with public *******)
(***** key pkS of the mixer **********************************************)
(*************************************************************************)


(* We use a lot of functions defined in definitions.v to make the terms manageable. 
   Also note that ((τ1 (fFΦ2 c0 c1 x0)) ≟ x0) or ((τ2 (fFΦ2 c0 c1 x0)) ≟ x0 or ((τ3 (fFΦ2 c0 c1 x0)) ≟ x0) expresses that the ballot of the first voter was not replaced,
   the negation of which is the guard of Lemma25 *)

(* The actual statement of Lemma25 is at the end *)



(* In the next proposition we show that the terms with "Fiv" and "Fv" are equal.
   Fiv inserts the if-then-else terms in front of the decrytions of the voting phase that is necessary for the CCA2 axiom. *)

Lemma lemma25_CCA2Game1n:
  forall side n m0,
    ContextTerm General Term (fun _ : ToL Term => m0)
    -> (fun c0 c1 =>
          (fun x0 =>
             (fun v1 v2 v3 =>
                If  ((τ1 (fFΦ2 c0 c1 x0)) ≟ x0)  or ((τ2 (fFΦ2 c0 c1 x0)) ≟ x0)  or ((τ3 (fFΦ2 c0 c1 x0)) ≟ x0)
                  Then ⫠
                  Else (＜＜ x0 , (e1 c0 c1 n1),         (dv v1 v2 v3 (s v1 v2 v3) ) ＞,
                                           ＜ Fl0 c0 c1 x0 v1 v2 v3, Fl1 c0 c1 x0 v1 v2 v3, (Fido c0 c1 x0 v1 v2 v3 n0)＞＞)
             ) (Fiv1 c0 c1 x0 m0) (Fiv2 c0 c1 x0 m0) (Fiv3 c0 c1 x0 m0)
  ) (e0 c0 c1 n)) (c0 side) (c1 side)
=
  (fun c0 c1 => (fun x0 => (fun v1 v2 v3 => If  ((τ1 (fFΦ2 c0 c1 x0)) ≟ x0)  or ((τ2 (fFΦ2 c0 c1 x0)) ≟ x0)  or ((τ3 (fFΦ2 c0 c1 x0)) ≟ x0)
                                    Then ⫠
                                    Else (＜＜ x0 ,               (e1 c0 c1 n1),            (dv v1 v2 v3 (s v1 v2 v3) ) ＞,
                                           ＜ Fl0 c0 c1 x0 v1 v2 v3, Fl1 c0 c1 x0 v1 v2 v3, (Fido c0 c1 x0 v1 v2 v3 n0)＞＞)
             ) (Fv1 c0 c1 x0) (Fv2 c0 c1 x0) (Fv3 c0 c1 x0)
  ) (e0 c0 c1 n)) (c0 side) (c1 side).
Proof.
  intros.
  rewrite (OrComp) at 1.
  unfold Fiv1.
  rewrite (@If_eval (fun _ => _) (fun b1 => If _ Then ⫠ Else If _ Then ⫠
            Else (＜ ＜ _, _,  dv (If b1 Then _ Else If b1 Then _ Else _) _ _ (s (If b1 Then _ Else If b1 Then _ Else _) _ _) ＞,
                  ＜ Fl0 _ _ _ (If b1 Then _ Else If b1 Then _ Else _) _ _,
                     Fl1 _ _ _ (If b1 Then _ Else If b1 Then _ Else _) _ _,
                     Fido _ _ _ (If b1 Then _ Else If b1 Then _ Else _) _ _ _ ＞ ＞) )_ ).
  rewrite If_false. rewrite If_false.

  unfold Fiv2.
  rewrite (@If_eval (fun _ => _) (fun b2 => If _ Then ⫠
            Else (＜ ＜ _, _,  dv _ (If b2 Then _ Else If b2 Then _ Else _) _ (s _ (If b2 Then _ Else If b2 Then _ Else _) _) ＞,
                  ＜ Fl0 _ _ _ _ (If b2 Then _ Else If b2 Then _ Else _)  _,
                     Fl1 _ _ _ _ (If b2 Then _ Else If b2 Then _ Else _)  _,
                     Fido _ _ _ _ (If b2 Then _ Else If b2 Then _ Else _) _ _ ＞ ＞) )_ ).
  rewrite If_false. rewrite If_false.

  unfold Fiv3.
  rewrite (@If_eval (fun _ => _) (fun b3 => (＜ ＜ _, _,  dv _ _ (If b3 Then _ Else If b3 Then _ Else _) (s _ _ (If b3 Then _ Else If b3 Then _ Else _) ) ＞,
                  ＜ Fl0 _ _ _ _ _ (If b3 Then _ Else If b3 Then _ Else _),
                     Fl1 _ _ _ _ _ (If b3 Then _ Else If b3 Then _ Else _),
                     Fido _ _ _ _ _ (If b3 Then _ Else If b3 Then _ Else _) _ ＞ ＞) )_ ).
  rewrite If_false. rewrite If_false.

  rewrite <- OrComp.
  reflexivity.

(*  *)
  1,3,4,6,7,9: ProveboolandContext.
apply lemma25_game1n_context1. auto. 
  apply lemma25_game1n_context2. auto.
  apply lemma25_game1n_context3. auto.
Qed.




(* In the next two propositions we show that the terms with "Fido" and "Fdo" are equal. *)

(* Lemma25_CCA2Game2n_helper expresses that if the ballot of the first voter was sent in the OPENING phase, the shuffle will not be published due to the phase check.
   This shows the protocol could prevent replay attack. *)

Lemma lemma25_CCA2Game2n_helper:
  forall side n n0,
  (fun c0 c1 => (fun x0 => (fun v1 v2 v3 => If  ((τ1 (fFΦ2 c0 c1 x0)) ≟ x0)  or ((τ2 (fFΦ2 c0 c1 x0)) ≟ x0)  or ((τ3 (fFΦ2 c0 c1 x0)) ≟ x0)
                                    Then ⫠
                                    Else (＜＜ x0 ,               (e1 c0 c1 n1),            (dv v1 v2 v3 (s v1 v2 v3) ) ＞,
                                           ＜ Fl0 c0 c1 x0 v1 v2 v3, Fl1 c0 c1 x0 v1 v2 v3, (Fido c0 c1 x0 v1 v2 v3 n0)＞＞)
             ) (Fv1 c0 c1 x0) (Fv2 c0 c1 x0) (Fv3 c0 c1 x0)
   ) (e0 c0 c1 n)) (c0 side) (c1 side)
 =
  (fun c0 c1 => (fun x0 => (fun v1 v2 v3 => If ((τ1 (fFΦ2 c0 c1 x0)) ≟ x0)  or ((τ2 (fFΦ2 c0 c1 x0)) ≟ x0)  or ((τ3 (fFΦ2 c0 c1 x0)) ≟ x0) Then ⫠
                              Else If ((τ1 (fFΦ5 c0 c1 x0 v1 v2 v3)) ≟ x0)
                                   or ((τ2 (fFΦ5 c0 c1 x0 v1 v2 v3)) ≟ x0)
                                   or ((τ3 (fFΦ5 c0 c1 x0 v1 v2 v3)) ≟ x0)
       Then (＜＜ x0 , (e1 c0 c1 n1), (dv v1 v2 v3 (s v1 v2 v3)) ＞, ＜ Fl0 c0 c1 x0 v1 v2 v3, Fl1 c0 c1 x0 v1 v2 v3,   ⫠   ＞＞)
       Else (＜＜ x0 , (e1 c0 c1 n1), (dv v1 v2 v3 (s v1 v2 v3)) ＞, ＜ Fl0 c0 c1 x0 v1 v2 v3, Fl1 c0 c1 x0 v1 v2 v3, (Fdo c0 c1 x0 v1 v2 v3) ＞ ＞)
            ) (Fv1 c0 c1 x0) (Fv2 c0 c1 x0) (Fv3 c0 c1 x0)
                ) (e0 c0 c1 n)) (c0 side) (c1 side).
Proof.
  intros. simpl.
  pose (lemma25_game2n_fFΦ3 side n) as ee.
  pose (lemma25_game2n_fFΦ5 side n) as eee.
  unfold Fido. unfold pchko.
  rewrite Tau1Tri, Tau2Tri, Tau3Tri. (*  *)
  unfold Fio1 at 2. rewrite decSimpl.
  unfold Fio2 at 2. rewrite decSimpl.
  unfold Fio3 at 2. rewrite decSimpl.
  repeat rewrite (@If_morph (fun x => ph3 ≟ (π2 x)) _ _).
  unfold m0. rewrite proj2pair. rewrite ph2Neqph3.
  rewrite AndGuard.
  rewrite (@If_morph (fun x => (＜ ＜ _ , _ , _ ＞, ＜ _, _, If _ & x & _ Then _ Else ⫠ ＞ ＞))).
  rewrite If_false. rewrite If_same. rewrite If_false.
  rewrite (@If_morph (fun x => (＜ ＜ _ , _ , _ ＞, ＜ _, _, If _ & x & _ Then _ Else ⫠ ＞ ＞))).
  rewrite If_false. rewrite If_same. rewrite If_false.
  rewrite (@If_morph (fun x => (＜ ＜ _ , _ , _ ＞, ＜ _, _, If _ & x & _ Then _ Else ⫠ ＞ ＞))).
  rewrite If_false. rewrite If_same. rewrite If_false.

  unfold Fio1.
  rewrite (@If_eval (fun _ => _) (fun b1 => If _ Then _ Else If _ Then _
                 Else (＜ ＜ _, _, _ ＞,
                       ＜ _, _,
                       If dist (If b1 Then _ Else If b1 Then Error Else _) _ _ & (_ & _ & _) &
                          isinkc kc0 kc1 (＜ π2 (π1 (If b1 Then _ Else If b1 Then Error Else _)),  π2 (π1 _), π2 (π1 _) ＞)
                       Then shufl (π1 (If b1 Then _ Else If b1 Then Error Else _)) (π1 _) (π1 _) Else ⫠ ＞ ＞))).
  rewrite If_false. rewrite If_false.

  unfold Fio2.
  rewrite (@If_eval (fun _ => _) (fun b2 => If _ Then _ Else
                      (＜ ＜ _, _, _ ＞,
                       ＜ _, _,
                       If dist _ (If b2 Then _ Else If b2 Then Error Else _) _ & (_ & _ & _) &
                          isinkc kc0 kc1 (＜ π2 (π1 _), π2 (π1 (If b2 Then _ Else If b2 Then Error Else _)),  π2 (π1 _) ＞)
                       Then shufl (π1 _) (π1 (If b2 Then _ Else If b2 Then Error Else _)) (π1 _) Else ⫠ ＞ ＞))).
  rewrite If_false. rewrite If_false.

  unfold Fio3.
  rewrite (@If_eval (fun _ => _) (fun b3 => (＜ ＜ _, _, _ ＞,
                       ＜ _, _,
                       If dist _ _ (If b3 Then _ Else If b3 Then Error Else _) & (_ & _ & _) &
                          isinkc kc0 kc1 (＜ π2 (π1 _), π2 (π1 _), π2 (π1 (If b3 Then _ Else If b3 Then Error Else _)) ＞)
                       Then shufl (π1 _) (π1 _) (π1 (If b3 Then _ Else If b3 Then Error Else _)) Else ⫠ ＞ ＞))).
  rewrite If_false. rewrite If_false.
  rewrite <- OrComp.

(* right hand side *)
  unfold Fdo. unfold pchko. rewrite Tau1Tri, Tau2Tri, Tau3Tri.
  reflexivity.

  time (destruct side; simpl;  ProveboolandContext).
  time (destruct side; simpl;  ProveboolandContext).
  time (destruct side; simpl;  ProveboolandContext).
  time (destruct side; simpl;  ProveboolandContext).
  time (destruct side; simpl;  ProveboolandContext).
  time (destruct side; simpl;  ProveboolandContext).
  time (destruct side; simpl;  ProveboolandContext).
  time (destruct side; simpl;  ProveboolandContext).
  time (destruct side; simpl;  ProveboolandContext).
  time (destruct side; simpl;  ProveboolandContext).
  time (destruct side; simpl;  ProveboolandContext).
  time (destruct side; simpl;  ProveboolandContext).
  time (destruct side; simpl;  ProveboolandContext).
  time (destruct side; simpl;  ProveboolandContext).
  time (destruct side; simpl;  ProveboolandContext).
  time (destruct side; simpl;  ProveboolandContext).
  time (destruct side; simpl;  ProveboolandContext).
  time (destruct side; simpl;  ProveboolandContext).
  time (destruct side; simpl;  ProveboolandContext).
  time (destruct side; simpl;  ProveboolandContext).
  time (destruct side; simpl;  ProveboolandContext).  
  time (destruct side; simpl;  ProveboolandContext).
  time (destruct side; simpl;  ProveboolandContext).
  time (destruct side; simpl;  ProveboolandContext).
Qed.

                                
(* Lemma25_CCA2Game2n expresses that the terms with "Fido" and "Fdo" are equal.
   Fido again inserts the if-then-else terms in front of the decrytions of the opening phase that is necessary for the CCA2 axiom. *)

Lemma lemma25_CCA2Game2n:
  forall side n n0,
  (fun c0 c1 => (fun x0 => (fun v1 v2 v3 => If  ((τ1 (fFΦ2 c0 c1 x0)) ≟ x0)  or ((τ2 (fFΦ2 c0 c1 x0)) ≟ x0)  or ((τ3 (fFΦ2 c0 c1 x0)) ≟ x0)
                                    Then ⫠
                                    Else (＜＜ x0 ,               (e1 c0 c1 n1),            (dv v1 v2 v3 (s v1 v2 v3) ) ＞,
                                           ＜ Fl0 c0 c1 x0 v1 v2 v3, Fl1 c0 c1 x0 v1 v2 v3, (Fido c0 c1 x0 v1 v2 v3 n0)＞＞)
             ) (Fv1 c0 c1 x0) (Fv2 c0 c1 x0) (Fv3 c0 c1 x0)
   ) (e0 c0 c1 n)) (c0 side) (c1 side)
 =
  (fun c0 c1 => (fun x0 => (fun v1 v2 v3 => If  ((τ1 (fFΦ2 c0 c1 x0)) ≟ x0)  or ((τ2 (fFΦ2 c0 c1 x0)) ≟ x0)  or ((τ3 (fFΦ2 c0 c1 x0)) ≟ x0)
                                    Then ⫠
                                    Else (＜＜ x0 ,               (e1 c0 c1 n1),            (dv v1 v2 v3 (s v1 v2 v3) ) ＞,
                                           ＜ Fl0 c0 c1 x0 v1 v2 v3, Fl1 c0 c1 x0 v1 v2 v3, (Fdo c0 c1 x0 v1 v2 v3 )＞＞) (**)
             ) (Fv1 c0 c1 x0) (Fv2 c0 c1 x0) (Fv3 c0 c1 x0)
  ) (e0 c0 c1 n)) (c0 side) (c1 side).
Proof.
  intros; simpl.
  unfold Fdo.

  assert ( let c0 := (c0 side) in let c1 := (c1 side) in
            (Fo1 c0 c1 (e0 c0 c1 n) (Fv1 c0 c1 (e0 c0 c1 n)) (Fv2 c0 c1 (e0 c0 c1 n)) (Fv3 c0 c1 (e0 c0 c1 n)))
          = (Fio1 c0 c1 (e0 c0 c1 n) (Fv1 c0 c1 (e0 c0 c1 n)) (Fv2 c0 c1 (e0 c0 c1 n)) (Fv3 c0 c1 (e0 c0 c1 n)) n)) as H.
    apply (decIfThenElse (m0 (c0 side) (c1 side) n) 7
           (τ1 (fFΦ5 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) (Fv1 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n))
               (Fv2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n)) (Fv3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n))))).
    rewrite H; clear H.

  assert ( let c0 := (c0 side) in let c1 := (c1 side) in
            (Fo2 c0 c1 (e0 c0 c1 n) (Fv1 c0 c1 (e0 c0 c1 n)) (Fv2 c0 c1 (e0 c0 c1 n)) (Fv3 c0 c1 (e0 c0 c1 n)))
          = (Fio2 c0 c1 (e0 c0 c1 n) (Fv1 c0 c1 (e0 c0 c1 n)) (Fv2 c0 c1 (e0 c0 c1 n)) (Fv3 c0 c1 (e0 c0 c1 n)) n)) as H.
    apply (decIfThenElse (m0 (c0 side) (c1 side) n) 7
           (τ2 (fFΦ5 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) (Fv1 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n))
               (Fv2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n)) (Fv3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n))))).
    rewrite H; clear H.

  assert ( let c0 := (c0 side) in let c1 := (c1 side) in
            (Fo3 c0 c1 (e0 c0 c1 n) (Fv1 c0 c1 (e0 c0 c1 n)) (Fv2 c0 c1 (e0 c0 c1 n)) (Fv3 c0 c1 (e0 c0 c1 n)))
          = (Fio3 c0 c1 (e0 c0 c1 n) (Fv1 c0 c1 (e0 c0 c1 n)) (Fv2 c0 c1 (e0 c0 c1 n)) (Fv3 c0 c1 (e0 c0 c1 n)) n)) as H.
    apply (decIfThenElse (m0 (c0 side) (c1 side) n) 7
           (τ3 (fFΦ5 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) (Fv1 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n))
               (Fv2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n)) (Fv3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n))))).
    rewrite H; clear H.

(**)
  rewrite (lemma25_CCA2Game2n_helper side n n0).
(**)
  pose (lemma25_CCA2Game2n_helper side n n) as H.
    unfold Fido in H. rewrite H; clear H.

  reflexivity.
Qed.


(* Now we are ready to use the CCA2 axiom and replace n0 with n0' *)

Proposition prop25_replace_n0_with_n0': forall side,
  (| ＜ pv0 (c0 side) (c1 side) n0, ph2 ＞ |) = (| ＜ pv0 (c0 side) (c1 side) n0', ph2 ＞ |) ->
  (fun c0 c1 => (fun x0 => (fun v1 v2 v3 => [b0 c0; b1 c1; (If ((acc0 c0 c1) & (acc1 c0 c1)) Then
                                   (If ((τ1 (fFΦ2 c0 c1 x0)) ≟ x0)  or ((τ2 (fFΦ2 c0 c1 x0)) ≟ x0)  or ((τ3 (fFΦ2 c0 c1 x0)) ≟ x0)
                                    Then ⫠
                                    Else (＜＜ x0 ,               (e1 c0 c1 n1),            (dv v1 v2 v3 (s v1 v2 v3) ) ＞,
                                           ＜ Fl0 c0 c1 x0 v1 v2 v3, Fl1 c0 c1 x0 v1 v2 v3, (Fdo c0 c1 x0 v1 v2 v3 )＞＞)) Else ⫠)] (**)
             ) (Fv1 c0 c1 x0) (Fv2 c0 c1 x0) (Fv3 c0 c1 x0)
  ) (e0 c0 c1 n0)) (c0 side) (c1 side)
  ~
  (fun c0 c1 => (fun x0 => (fun v1 v2 v3 => [b0 c0; b1 c1; (If ((acc0 c0 c1) & (acc1 c0 c1)) Then
                                   (If  ((τ1 (fFΦ2 c0 c1 x0)) ≟ x0)  or ((τ2 (fFΦ2 c0 c1 x0)) ≟ x0)  or ((τ3 (fFΦ2 c0 c1 x0)) ≟ x0)
                                    Then ⫠
                                    Else (＜＜ x0 ,               (e1 c0 c1 n1),            (dv v1 v2 v3 (s v1 v2 v3) ) ＞,
                                           ＜ Fl0 c0 c1 x0 v1 v2 v3, Fl1 c0 c1 x0 v1 v2 v3, (Fdo c0 c1 x0 v1 v2 v3 )＞＞)) Else ⫠)] (**)
             ) (Fv1 c0 c1 x0) (Fv2 c0 c1 x0) (Fv3 c0 c1 x0)
  ) (e0 c0 c1 n0')) (c0 side) (c1 side).
Proof.
(* Here using lemma25_CCA2Game1n and lemma25_CCA2Game2n to rewrite the term will ensure the context CCA2 applicable. 
   Then we will use CCA2 to replace the nonce n0 with n0'. *)
  intros side. intros.
  simpl.

  rewrite <- (lemma25_CCA2Game2n side n0 n0).
  rewrite <- (lemma25_CCA2Game1n side n0 (＜ pv0 (c0 side) (c1 side) n0, ph2 ＞)).

(* Φ6[x, pv01] is (pkS, rd0, pv00, pv00') −- CCA2 compliant. pkS := nonce 6, rd0 := nonce 7 *)
  pose (cca2 [nonce 6] [nonce 7]
             (fun x0 => (fun c0 c1 => (fun v1 v2 v3 => [b0 c0; b1 c1; (If ((acc0 c0 c1) & (acc1 c0 c1)) Then
                                    If  ((τ1 (fFΦ2 c0 c1 x0)) ≟ x0)  or ((τ2 (fFΦ2 c0 c1 x0)) ≟ x0)  or ((τ3 (fFΦ2 c0 c1 x0)) ≟ x0)
                                    Then ⫠
                                    Else (＜＜ x0 ,                  (e1 c0 c1 n1),         (dv v1 v2 v3 (s v1 v2 v3) ) ＞,
                                           ＜ Fl0 c0 c1 x0 v1 v2 v3, Fl1 c0 c1 x0 v1 v2 v3, (Fido c0 c1 x0 v1 v2 v3 n0)＞＞) Else ⫠
             )]) (Fiv1 c0 c1 x0 (m0 c0 c1 n0)) (Fiv2 c0 c1 x0 (m0 c0 c1 n0)) (Fiv3 c0 c1 x0 (m0 c0 c1 n0))) (c0 side) (c1 side))
             (＜ pv0 (c0 side) (c1 side) n0, ph2 ＞) (＜ pv0 (c0 side) (c1 side) n0', ph2 ＞)) as claim0; simpl in claim0.
  rewrite claim0; clear claim0.

  rewrite <- (lemma25_CCA2Game2n side n0' n0).
  rewrite <- (lemma25_CCA2Game1n side n0' (＜ pv0 (c0 side) (c1 side) n0, ph2 ＞)).
  reflexivity.

  destruct side; ProveContext.
  8 : { destruct side; ProveContext. }
  1,2,3,4,5: destruct side; ProveCCA2.
  apply lemma25_CCA2_n0_n0'_AfterCnxt.
  auto.
Qed.








(*************************************************************************)
(***** Next we show that as n0 is removed, the first voter check of it ***)
(***** in the opening phase fails and the commitment key kc0 is not sent**)
(*************************************************************************)



(* We show that if the ballot of the first voter was replaced, he will not send out his commitment key in the opening phase. 
   More specifically, we see that the bnlcheck in front of the opening-phase encryption fails, and "Fl" will turn to ⫠. *)

Lemma lemma25_Fl0_bot : forall side,
   ⫠ = (fun c0 c1 => (fun x0 => (fun v1 v2 v3 => Fl0 c0 c1 x0 v1 v2 v3) (Fv1 c0 c1 x0) (Fv2 c0 c1 x0) (Fv3 c0 c1 x0)) (e0 c0 c1 n0')) (c0 side) (c1 side).
Proof.
  intros. simpl.
  unfold Fl0. unfold bnlcheck.
  unfold fFΦ3 at 2.
  (* rewrite <- lemma25_isin_pv0_false. *)

  unfold ncheck. unfold isin. rewrite Tau1Tri, Tau2Tri, Tau3Tri.
  assert (n0 ≠ τ3 (π2 τ1 (f3 [b0 (c0 side); b1 (c1 side); e0 (c0 side) (c1 side) n0'; e1 (c0 side) (c1 side) n1;
    dv (Fv1 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0')) (Fv2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0')) (Fv3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0'))
    (s
                         (Fv1 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0'))
                         (Fv2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0'))
                         (Fv3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0'))
                         )]))).
    apply FreshNEqeq.  destruct side; ProveFresh.
    rewrite H. clear H. rewrite If_false.
  assert (n0 ≠ τ3 (π2 τ2 (f3 [b0 (c0 side); b1 (c1 side); e0 (c0 side) (c1 side) n0'; e1 (c0 side) (c1 side) n1;
    dv (Fv1 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0')) (Fv2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0')) (Fv3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0'))
    (s
                         (Fv1 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0'))
                         (Fv2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0'))
                         (Fv3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0'))
                         )]))).
    apply FreshNEqeq.  destruct side; ProveFresh.
    rewrite H. clear H. rewrite If_false.
  assert (n0 ≠ τ3 (π2 τ3 (f3 [b0 (c0 side); b1 (c1 side); e0 (c0 side) (c1 side) n0'; e1 (c0 side) (c1 side) n1;
    dv (Fv1 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0')) (Fv2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0')) (Fv3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0'))
    (s
                         (Fv1 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0'))
                         (Fv2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0'))
                         (Fv3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0'))
                         )]))).
    apply FreshNEqeq.  destruct side; ProveFresh.
    rewrite H. clear H.
  repeat rewrite If_same.
  rewrite If_false.
  reflexivity.
Qed.


(* Now we see that if the Commitment key of the first voter was not sent, the isinkc0 check in front of the OPENING phase shuffle will fail.  *)

Lemma lemma25_ininkc0_false: forall side,
  FAlse = (fun c0 c1 => (fun x0 => (fun v1 v2 v3 => isin kc0 (＜(π2 (π1 (Fo1 c0 c1 x0 v1 v2 v3))), (π2 (π1 (Fo2 c0 c1 x0 v1 v2 v3))), (π2 (π1 (Fo3 c0 c1 x0 v1 v2 v3)))＞)
            ) (Fv1 c0 c1 x0) (Fv2 c0 c1 x0) (Fv3 c0 c1 x0)) (e0 c0 c1 n0')) (c0 side) (c1 side).
Proof.
  intros.
  simpl. unfold Fo1, Fo2, Fo3.
  unfold fFΦ5. rewrite <- lemma25_Fl0_bot.
  unfold isin. rewrite Tau1Tri, Tau2Tri, Tau3Tri.

  assert ((fun c0 c1 => kc0 ≠ π2 (π1 (decS (τ1 (f5 [b0 c0; b1 c1; e0 c0 c1 n0'; e1 c0 c1 n1; dv (Fv1 c0 c1 (e0 c0 c1 n0')) (Fv2 c0 c1 (e0 c0 c1 n0')) (Fv3 c0 c1 (e0 c0 c1 n0'))
                  (s (Fv1 c0 c1 (e0 c0 c1 n0')) (Fv2 c0 c1 (e0 c0 c1 n0')) (Fv3 c0 c1 (e0 c0 c1 n0')) ); ⫠;
                   Fl1 c0 c1 (e0 c0 c1 n0') (Fv1 c0 c1 (e0 c0 c1 n0')) (Fv2 c0 c1 (e0 c0 c1 n0')) (Fv3 c0 c1 (e0 c0 c1 n0'))]))))) (c0 side) (c1 side)).
    pose (@prop11 (fun c0 => (fun c1 => π2 (π1 (decS (τ1 (f5 [b0 c0; b1 c1; e0 c0 c1 n0'; e1 c0 c1 n1; dv (Fv1 c0 c1 (e0 c0 c1 n0')) (Fv2 c0 c1 (e0 c0 c1 n0')) (Fv3 c0 c1 (e0 c0 c1 n0'))
                 (s (Fv1 c0 c1 (e0 c0 c1 n0')) (Fv2 c0 c1 (e0 c0 c1 n0')) (Fv3 c0 c1 (e0 c0 c1 n0'))); ⫠;
                  Fl1 c0 c1 (e0 c0 c1 n0') (Fv1 c0 c1 (e0 c0 c1 n0')) (Fv2 c0 c1 (e0 c0 c1 n0')) (Fv3 c0 c1 (e0 c0 c1 n0'))]))))) (c1 side)) (vot side) 0) as H.
    simpl in *. rewrite c0EqVot in H. rewrite H. auto.
    destruct side; simpl; ProvePPT; ProveFresh.
   apply lemma25_ininkc0_false_FreshC_τ1. 
    rewrite H. rewrite If_false. clear H.

  assert ((fun c0 c1 => kc0 ≠ π2 (π1 (decS (τ2 (f5 [b0 c0; b1 c1; e0 c0 c1 n0'; e1 c0 c1 n1; dv (Fv1 c0 c1 (e0 c0 c1 n0')) (Fv2 c0 c1 (e0 c0 c1 n0')) (Fv3 c0 c1 (e0 c0 c1 n0'))
                  (s (Fv1 c0 c1 (e0 c0 c1 n0')) (Fv2 c0 c1 (e0 c0 c1 n0')) (Fv3 c0 c1 (e0 c0 c1 n0')) ); ⫠;
                   Fl1 c0 c1 (e0 c0 c1 n0') (Fv1 c0 c1 (e0 c0 c1 n0')) (Fv2 c0 c1 (e0 c0 c1 n0')) (Fv3 c0 c1 (e0 c0 c1 n0'))]))))) (c0 side) (c1 side)).
    pose (@prop11 (fun c0 => (fun c1 => π2 (π1 (decS (τ2 (f5 [b0 c0; b1 c1; e0 c0 c1 n0'; e1 c0 c1 n1; dv (Fv1 c0 c1 (e0 c0 c1 n0')) (Fv2 c0 c1 (e0 c0 c1 n0')) (Fv3 c0 c1 (e0 c0 c1 n0'))
                 (s (Fv1 c0 c1 (e0 c0 c1 n0')) (Fv2 c0 c1 (e0 c0 c1 n0')) (Fv3 c0 c1 (e0 c0 c1 n0')) ); ⫠;
                  Fl1 c0 c1 (e0 c0 c1 n0') (Fv1 c0 c1 (e0 c0 c1 n0')) (Fv2 c0 c1 (e0 c0 c1 n0')) (Fv3 c0 c1 (e0 c0 c1 n0'))]))))) (c1 side)) (vot side) 0) as H.
    simpl in *. rewrite c0EqVot in H. rewrite H. auto.
    destruct side; simpl; ProvePPT; ProveFresh.
    apply lemma25_ininkc0_false_FreshC_τ2.
    rewrite H. rewrite If_false. clear H.


  assert ((fun c0 c1 => kc0 ≠ π2 (π1 (decS (τ3 (f5 [b0 c0; b1 c1; e0 c0 c1 n0'; e1 c0 c1 n1; dv (Fv1 c0 c1 (e0 c0 c1 n0')) (Fv2 c0 c1 (e0 c0 c1 n0')) (Fv3 c0 c1 (e0 c0 c1 n0'))
                  (s (Fv1 c0 c1 (e0 c0 c1 n0')) (Fv2 c0 c1 (e0 c0 c1 n0')) (Fv3 c0 c1 (e0 c0 c1 n0')) ); ⫠;
                   Fl1 c0 c1 (e0 c0 c1 n0') (Fv1 c0 c1 (e0 c0 c1 n0')) (Fv2 c0 c1 (e0 c0 c1 n0')) (Fv3 c0 c1 (e0 c0 c1 n0'))]))))) (c0 side) (c1 side)).
    pose (@prop11 (fun c0 => (fun c1 => π2 (π1 (decS (τ3 (f5 [b0 c0; b1 c1; e0 c0 c1 n0'; e1 c0 c1 n1; dv (Fv1 c0 c1 (e0 c0 c1 n0')) (Fv2 c0 c1 (e0 c0 c1 n0')) (Fv3 c0 c1 (e0 c0 c1 n0'))
                 (s (Fv1 c0 c1 (e0 c0 c1 n0')) (Fv2 c0 c1 (e0 c0 c1 n0')) (Fv3 c0 c1 (e0 c0 c1 n0')) ); ⫠;
                  Fl1 c0 c1 (e0 c0 c1 n0') (Fv1 c0 c1 (e0 c0 c1 n0')) (Fv2 c0 c1 (e0 c0 c1 n0')) (Fv3 c0 c1 (e0 c0 c1 n0'))]))))) (c1 side)) (vot side) 0) as H.
    simpl in *. rewrite c0EqVot in H. rewrite H. auto.
    destruct side; simpl; ProvePPT; ProveFresh.
    apply lemma25_ininkc0_false_FreshC_τ3.
    rewrite H.

  reflexivity.
Qed.


(*************************************************************************)
(***** Now we replace kc1 that was sent with a fresh kc1' in the *********)
(***** encryption of the opening phase using again CCA2 ******************)
(*************************************************************************)


(* In the next proposition, again we insert the necessary if-then-else terms to prepare for the use of the CCA2 axiom  *)

Lemma lemma25_CCA2Game1kc: forall side,
  (fun c0 c1 => (fun x0 => (fun v1 v2 v3 => [b0 c0; b1 c1; (If ((acc0 c0 c1) & (acc1 c0 c1)) Then
                                   (If  ((τ1 (fFΦ2 c0 c1 x0)) ≟ x0)  or ((τ2 (fFΦ2 c0 c1 x0)) ≟ x0)  or ((τ3 (fFΦ2 c0 c1 x0)) ≟ x0)
                                    Then ⫠
                                    Else (＜＜ x0 ,               (e1 c0 c1 n1),            (dv v1 v2 v3 (s v1 v2 v3) ) ＞,
                                           ＜ Fl0 c0 c1 x0 v1 v2 v3, Fl1 c0 c1 x0 v1 v2 v3, (Fdo c0 c1 x0 v1 v2 v3 )＞＞)) Else ⫠)] (**)
             ) (Fv1 c0 c1 x0) (Fv2 c0 c1 x0) (Fv3 c0 c1 x0)
  ) (e0 c0 c1 n0')) (c0 side) (c1 side)
=
  (fun c0 c1 => (fun y1 => (fun o1 o2 o3 => [b0 c0; b1 c1; (If ((acc0 c0 c1) & (acc1 c0 c1)) Then
                     (If  ((τ1 (fFΦ2 c0 c1 (e0 c0 c1 n0'))) ≟ (e0 c0 c1 n0'))
                       or ((τ2 (fFΦ2 c0 c1 (e0 c0 c1 n0'))) ≟ (e0 c0 c1 n0'))
                       or ((τ3 (fFΦ2 c0 c1 (e0 c0 c1 n0'))) ≟ (e0 c0 c1 n0'))
                      Then ⫠
                      Else (＜＜ (e0 c0 c1 n0') ,  (e1 c0 c1 n1),
                                (dv (Fv1 c0 c1 (e0 c0 c1 n0')) (Fv2 c0 c1 (e0 c0 c1 n0')) (Fv3 c0 c1 (e0 c0 c1 n0'))
                                    (shufl (π1 (Fv1 c0 c1 (e0 c0 c1 n0'))) (π1 (Fv2 c0 c1 (e0 c0 c1 n0'))) (π1 (Fv3 c0 c1 (e0 c0 c1 n0'))))) ＞,
                              ＜ ⫠,
                                FL1 c0 c1 y1,
                               (FIDO o1 o2 o3 )＞＞)) Else ⫠)] (**)
           ) (FiiO1 c0 c1 y1) (FiiO2 c0 c1 y1) (FiiO3 c0 c1 y1)
  ) (E1 c0 c1 kc1)) (c0 side) (c1 side).

 Proof.
  intros. simpl.

(*  *)
  assert (FiiO1 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1) = FO1 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1)).
    unfold FiiO1, FO1.
    rewrite (decIfThenElse (M1 (c0 side) (c1 side) kc1) 11 (τ1 (FFΦ5 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1)))) at 2.
    reflexivity. rewrite H. clear H.

  assert (FiiO2 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1) = FO2 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1)).
    unfold FiiO2, FO2.
    rewrite (decIfThenElse (M1 (c0 side) (c1 side) kc1) 11 (τ2 (FFΦ5 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1)))) at 2.
    reflexivity. rewrite H. clear H.

  assert (FiiO3 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1) = FO3 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1)).
    unfold FiiO3, FO3.
    rewrite (decIfThenElse (M1 (c0 side) (c1 side) kc1) 11 (τ3 (FFΦ5 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1)))) at 2.
    reflexivity. rewrite H. clear H.

(*  *)
  unfold Fdo.
  unfold isinkc.
  rewrite <- lemma25_ininkc0_false. rewrite If_false. 

(*  *)
  assert (FO1 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1)
        = Fo1 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0') (Fv1 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0'))
              (Fv2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0')) (Fv3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0'))).
    unfold Fo1. unfold fFΦ5.
    rewrite <- lemma25_Fl0_bot.
    unfold FO1.
    unfold FFΦ5.
    reflexivity.
    rewrite <- H.
    clear H.

  assert (FO2 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1)
        = Fo2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0') (Fv1 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0'))
              (Fv2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0')) (Fv3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0'))).
    unfold Fo2. unfold fFΦ5.
    rewrite <- lemma25_Fl0_bot.
    reflexivity.
    rewrite <- H.
    clear H.

  assert (FO3 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1)
        = Fo3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0') (Fv1 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0'))
              (Fv2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0')) (Fv3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0'))).
    unfold Fo3. unfold fFΦ5.
    rewrite <- lemma25_Fl0_bot.
    reflexivity.
    rewrite <- H.
    clear H.

(*  *)
  rewrite <- lemma25_Fl0_bot.

  reflexivity.
Qed.



(* We replace kc1 with kc1' using CCA2 axiom. *)

Proposition prop25_replace_kc1_with_kc1': forall side, (| (M1  (c0 side) (c1 side) kc1) | = |(M1  (c0 side) (c1 side) kc1') |) ->
(fun c0 c1 => (fun y1 => (fun o1 o2 o3 => [b0 c0; b1 c1; (If ((acc0 c0 c1) & (acc1 c0 c1)) Then
                     (If  ((τ1 (fFΦ2 c0 c1 (e0 c0 c1 n0'))) ≟ (e0 c0 c1 n0'))
                       or ((τ2 (fFΦ2 c0 c1 (e0 c0 c1 n0'))) ≟ (e0 c0 c1 n0'))
                       or ((τ3 (fFΦ2 c0 c1 (e0 c0 c1 n0'))) ≟ (e0 c0 c1 n0'))
                      Then ⫠
                      Else (＜＜ (e0 c0 c1 n0') ,  (e1 c0 c1 n1),
                                (dv (Fv1 c0 c1 (e0 c0 c1 n0')) (Fv2 c0 c1 (e0 c0 c1 n0')) (Fv3 c0 c1 (e0 c0 c1 n0'))
                                    (shufl (π1 (Fv1 c0 c1 (e0 c0 c1 n0'))) (π1 (Fv2 c0 c1 (e0 c0 c1 n0'))) (π1 (Fv3 c0 c1 (e0 c0 c1 n0'))))) ＞,
                              ＜ ⫠,
                                FL1 c0 c1 y1,
                               (FIDO o1 o2 o3 )＞＞)) Else ⫠)] (**)
           ) (FiiO1 c0 c1 y1) (FiiO2 c0 c1 y1) (FiiO3 c0 c1 y1)
  ) (E1 c0 c1 kc1)) (c0 side) (c1 side)
  ~
(fun c0 c1 => (fun y1 => (fun o1 o2 o3 => [b0 c0; b1 c1; (If ((acc0 c0 c1) & (acc1 c0 c1)) Then
                     (If  ((τ1 (fFΦ2 c0 c1 (e0 c0 c1 n0'))) ≟ (e0 c0 c1 n0'))
                       or ((τ2 (fFΦ2 c0 c1 (e0 c0 c1 n0'))) ≟ (e0 c0 c1 n0'))
                       or ((τ3 (fFΦ2 c0 c1 (e0 c0 c1 n0'))) ≟ (e0 c0 c1 n0'))
                      Then ⫠
                      Else (＜＜ (e0 c0 c1 n0') ,  (e1 c0 c1 n1),
                                (dv (Fv1 c0 c1 (e0 c0 c1 n0')) (Fv2 c0 c1 (e0 c0 c1 n0')) (Fv3 c0 c1 (e0 c0 c1 n0'))
                                    (shufl (π1 (Fv1 c0 c1 (e0 c0 c1 n0'))) (π1 (Fv2 c0 c1 (e0 c0 c1 n0'))) (π1 (Fv3 c0 c1 (e0 c0 c1 n0'))))) ＞,
                              ＜ ⫠,
                                FL1 c0 c1 y1,
                               (FIDO o1 o2 o3 )＞＞)) Else ⫠)] (**)
           ) (FiiO1 c0 c1 y1) (FiiO2 c0 c1 y1) (FiiO3 c0 c1 y1)
  ) (E1 c0 c1 kc1')) (c0 side) (c1 side).
Proof.
  intros side. intros.
  simpl.

(* Φ6[x, pv01] is (pkS, rdd1, kc1, kc1') −- CCA2 compliant. pkS := nonce 6, rd0 := nonce 11 *)
  pose (cca2 [nonce 6] [nonce 11]
             (fun y1 => (fun c0 c1 => (fun o1 o2 o3 => [b0 c0; b1 c1; (If ((acc0 c0 c1) & (acc1 c0 c1)) Then
                     (If  ((τ1 (fFΦ2 c0 c1 (e0 c0 c1 n0'))) ≟ (e0 c0 c1 n0'))
                       or ((τ2 (fFΦ2 c0 c1 (e0 c0 c1 n0'))) ≟ (e0 c0 c1 n0'))
                       or ((τ3 (fFΦ2 c0 c1 (e0 c0 c1 n0'))) ≟ (e0 c0 c1 n0'))
                      Then ⫠
                      Else (＜＜ (e0 c0 c1 n0') ,  (e1 c0 c1 n1),
                                (dv (Fv1 c0 c1 (e0 c0 c1 n0')) (Fv2 c0 c1 (e0 c0 c1 n0')) (Fv3 c0 c1 (e0 c0 c1 n0'))
                                    (shufl (π1 (Fv1 c0 c1 (e0 c0 c1 n0'))) (π1 (Fv2 c0 c1 (e0 c0 c1 n0'))) (π1 (Fv3 c0 c1 (e0 c0 c1 n0'))))) ＞,
                              ＜ ⫠,
                                FL1 c0 c1 y1,
                               (FIDO o1 o2 o3 )＞＞)) Else ⫠)] (**)
           ) (FiiO1 c0 c1 y1) (FiiO2 c0 c1 y1) (FiiO3 c0 c1 y1)) (c0 side) (c1 side))
          (M1 (c0 side) (c1 side) kc1) (M1 (c0 side) (c1 side) kc1')) as claim0; simpl in claim0. rewrite claim0; clear claim0.
  reflexivity.

  1, 2, 3, 7: ProveCCA2.
  ProveListFresh. lia. 1,2,3 :constructor.

  apply lemma25_CCA2_kc1_kc1'_M1.
  apply lemma25_CCA2_kc1_kc1'_M1'.
  apply lemma25_CCA2_kc1_kc1'_Φ5.
Qed.




(** In the next few propositions we discuss whether the OPENING phase shuffle will be published. **)


(* Notice that ((τ1 (FFΦ5 c0 c1 y1)) ≟ y1) or ((τ2 (FFΦ5 c0 c1 y1)) ≟ y1) or ((τ3 (FFΦ5 c0 c1 y1)) ≟ y1) expresses that the commitment key of the second voter was not replaced,
   then definitely the OPENING phase shuffle will not be published. *)

(* The negation of which is "FDO", where the shuffle might still be published. *)

Lemma lemma25_elim_kc1_in_then_branch: forall side,
 (fun c0 c1 => (fun y1 => (fun o1 o2 o3 => FIDO o1 o2 o3) (FiiO1 c0 c1 y1) (FiiO2 c0 c1 y1) (FiiO3 c0 c1 y1)) (E1 c0 c1 kc1')) (c0 side) (c1 side)
 =
 (fun c0 c1 => (fun y1 => (fun o1 o2 o3 => If (τ1 (FFΦ5 c0 c1 y1)) ≟ y1 Then ⫠
                             Else If (τ2 (FFΦ5 c0 c1 y1)) ≟ y1 Then ⫠
                             Else If (τ3 (FFΦ5 c0 c1 y1)) ≟ y1 Then ⫠
                             Else FDO o1 o2 o3) (FO1 c0 c1 y1) (FO2 c0 c1 y1) (FO3 c0 c1 y1)) (E1 c0 c1 kc1')) (c0 side) (c1 side).
Proof.
  intros.
  pose (lemma25_elim_kc1_cnxtΦ3 side) as ee.
  pose (lemma25_elim_kc1_cnxtΦ5 side) as eee.
  unfold FIDO. simpl.

  unfold isin.
  rewrite Tau1Tri, Tau2Tri, Tau3Tri.

  unfold FiiO1 at 3. unfold FiiO2 at 3. unfold FiiO3 at 3. repeat rewrite decSimpl.
  repeat rewrite (@If_morph (fun x => (kc1 ≟ (π2 (π1 x))))).
  unfold M1.
  rewrite proj1pair, proj2pair.
  rewrite ceqeq.

  simpl.
  assert (((kc1 ≟ (π2 (π1 decS (τ1 (FFΦ5 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1'))))))) = FAlse).
    assert ((com (vot (op side)) kc1) = c1 side).
    destruct side; reflexivity.
    pose (@prop11 (fun x => (π2 (π1 decS (τ1 (FFΦ5 (c0 side) x (E1 (c0 side) x kc1')))))) (vot (op side)) 1) as cont.
    rewrite H in cont.
    apply cont.
    destruct side; simpl; ProvePPT.
    1, 2: ProveFresh.
    apply lemma25_elim_kc1_freshc1.
    rewrite H; clear H; rewrite <- If_tf.
  assert (((kc1 ≟ (π2 (π1 decS (τ2 (FFΦ5 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1'))))))) = FAlse).
    assert ((com (vot (op side)) kc1) = c1 side).
    destruct side; reflexivity.
    pose (@prop11 (fun x => (π2 (π1 decS (τ2 (FFΦ5 (c0 side) x (E1 (c0 side) x kc1')))))) (vot (op side)) 1) as cont.
    rewrite H in cont.
    apply cont.
    destruct side; simpl; ProvePPT.
    1,2: ProveFresh.
    apply lemma25_elim_kc1_freshc2.
    rewrite H; clear H; rewrite <- If_tf.
  assert (((kc1 ≟ (π2 (π1 decS (τ3 (FFΦ5 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1'))))))) = FAlse).
    assert ((com (vot (op side)) kc1) = c1 side).
    destruct side; reflexivity.
    pose (@prop11 (fun x => (π2 (π1 decS (τ3 (FFΦ5 (c0 side) x (E1 (c0 side) x kc1')))))) (vot (op side)) 1) as cont.
    rewrite H in cont.
    apply cont.
    destruct side; simpl; ProvePPT.
    1,2: ProveFresh.
    apply lemma25_elim_kc1_freshc3.
    rewrite H; clear H; rewrite <- If_tf.

  rewrite CNF_IfThenElse.

  repeat rewrite (@If_morph (fun x => If dist (FiiO1 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1')) (FiiO2 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1'))
                              (FiiO3 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1')) &
                           pchko (＜ FiiO1 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1'), FiiO2 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1'),
                                  FiiO3 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1') ＞) & x
     Then shufl (π1 FiiO1 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1')) (π1 FiiO2 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1'))
  (π1 FiiO3 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1')) Else ⫠ )).
  repeat rewrite If_same.  repeat rewrite If_false.

  unfold FiiO1, FiiO2, FiiO3.  repeat rewrite decSimpl. rewrite <- If_tf.

  rewrite (@If_eval (fun _ => _) (fun b1 => If _ Then ⫠ Else If _ Then ⫠
                                      Else If dist (If b1 Then _ Else _) _ _ & pchko (＜ If b1 Then _ Else _ , _ , _ ＞) Then shufl (π1 If b1 Then _ Else _ ) (π1 _) (π1 _) Else ⫠)).
    rewrite If_false.
  rewrite (@If_eval (fun _ => _) (fun b2 => If _ Then ⫠
                                      Else If dist _ (If b2 Then _ Else _) _ & pchko (＜ _,  If b2 Then _ Else _ , _ ＞) Then shufl (π1 _) (π1 If b2 Then _ Else _ ) (π1 _) Else ⫠)).
    rewrite If_false.
  rewrite (@If_eval (fun _ => _) (fun b3 => If dist _ _ (If b3 Then _ Else _) & pchko (＜ _, _, If b3 Then _ Else _ ＞) Then shufl (π1 _) (π1 _) (π1 If b3 Then _ Else _ ) Else ⫠)).
    rewrite If_false.

  reflexivity.
  all : time ProveboolandContext. (*10.709 secs*)
  unfold pchko.
  Provebool.
Qed.


(* In the next two propositions,  we show that in the opening phase
   if the message sent from the second voter is ＜ ⫠, ph2 ＞, and replaced with (＜＜label, kc1' ＞, ph3 ＞) by the attacker,
   then isinkc1 check in front of the OPENING phase shuffle will fail. *)

Lemma lemma25_ininkc1_FIO_false: forall side,
  FAlse
 =
  (fun c0 c1 => (fun y1 => (fun o1 o2 o3 => (isin kc1 (＜(π2 (π1 o1)), (π2 (π1 o2)), (π2 (π1 o3))＞))) (FiO1 c0 c1 y1) (FiO2 c0 c1 y1) (FiO3 c0 c1 y1)) (E1 c0 c1 kc1')) (c0 side) (c1 side).
Proof.
  intros.
  pose (lemma25_ininkc1_Freshkc1_Φ3 side) as ee.
  pose (lemma25_ininkc1_Freshkc1_Φ5 side) as eee.
  unfold isin.
  rewrite Tau1Tri, Tau2Tri, Tau3Tri.
  assert (kc1 ≠ (π2 (π1 FiO1 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1')))).
    assert ((com (vot (op side)) kc1) = c1 side).
    destruct side; reflexivity.
    pose (@prop11 (fun x => (π2 (π1 (FiO1 (c0 side) x (E1 (c0 side) x kc1'))))) (vot (op side)) 1) as cont.
    rewrite H in cont.
    apply cont.
    destruct side; simpl; ProvePPT.
    1, 2: ProveFresh.
    (destruct side; simpl; ProveFreshCTerm).
    rewrite H. clear H.
  assert (kc1 ≠ (π2 (π1 FiO2 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1')))).
    assert ((com (vot (op side)) kc1) = c1 side).
    destruct side; reflexivity.
    pose (@prop11 (fun x => (π2 (π1 (FiO2 (c0 side) x (E1 (c0 side) x kc1'))))) (vot (op side)) 1) as cont.
    rewrite H in cont.
    apply cont.
    destruct side; simpl; ProvePPT.
    1, 2: ProveFresh.
    (destruct side; simpl; ProveFreshCTerm).
    rewrite H. clear H.
  assert (kc1 ≠ (π2 (π1 FiO3 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1')))).
    assert ((com (vot (op side)) kc1) = c1 side).
    destruct side; reflexivity.
    pose (@prop11 (fun x => (π2 (π1 (FiO3 (c0 side) x (E1 (c0 side) x kc1'))))) (vot (op side)) 1) as cont.
    rewrite H in cont.
    apply cont.
    destruct side; simpl; ProvePPT.
    1, 2: ProveFresh.
    (destruct side; simpl; ProveFreshCTerm).
    rewrite H. clear H.
  repeat rewrite If_false.
  reflexivity.
Qed.

(*  *)

Lemma lemma25_elim_kc1_in_FIDO: forall side,
 (fun c0 c1 => (fun y1 => (fun o1 o2 o3 => FIDO o1 o2 o3) (FiO1 c0 c1 y1) (FiO2 c0 c1 y1) (FiO3 c0 c1 y1)) (E1 c0 c1 kc1')) (c0 side) (c1 side)
 =
 (fun c0 c1 => (fun y1 => (fun o1 o2 o3 => FDO o1 o2 o3)  (FiO1 c0 c1 y1) (FiO2 c0 c1 y1) (FiO3 c0 c1 y1)) (E1 c0 c1 kc1')) (c0 side) (c1 side).
Proof.
  intros. simpl.
  unfold FIDO.
  rewrite <- lemma25_ininkc1_FIO_false.
  rewrite If_false. rewrite <- If_tf.
  reflexivity. unfold pchko.  Provebool.
Qed.




(* In the next two propositions, We show that in the opening phase, two scenarios that if 
   "the plaintext sent from the second voter is ＜ ⫠, ph2 ＞,             and replaced with (＜＜label, kc1' ＞, ph3 ＞) by the attacker",
     and 
   "the plaintext sent from the second voter is ＜＜label, kc1 ＞, ph3 ＞, and replaced with (＜＜label, kc1' ＞, ph3 ＞) by the attacker",
   appear to be the same. *)

Lemma lemma25_elim_bot_in_then_branch: forall side,
 (fun c0 c1 => (fun y1 => (fun o1 o2 o3 => FIDO o1 o2 o3) (FiO1 c0 c1 y1) (FiO2 c0 c1 y1) (FiO3 c0 c1 y1)) (E1 c0 c1 kc1')) (c0 side) (c1 side)
 =
 (fun c0 c1 => (fun y1 => (fun o1 o2 o3 => If (τ1 (FFΦ5 c0 c1 y1)) ≟ y1 Then ⫠
                             Else If (τ2 (FFΦ5 c0 c1 y1)) ≟ y1 Then ⫠
                             Else If (τ3 (FFΦ5 c0 c1 y1)) ≟ y1 Then ⫠
                             Else FDO o1 o2 o3) (FO1 c0 c1 y1) (FO2 c0 c1 y1) (FO3 c0 c1 y1)) (E1 c0 c1 kc1')) (c0 side) (c1 side).
Proof.
  intros. simpl.
  pose (lemma25_elim_bot_cnxtΦ3 side) as ee.
  pose (lemma25_elim_bot_cnxtΦ5 side) as eee.
(*  *)
  rewrite lemma25_elim_kc1_in_FIDO.
  unfold FDO. simpl.

(*  *)
  unfold pchko. rewrite Tau1Tri, Tau2Tri, Tau3Tri.
  unfold FiO1 at 2.  unfold FiO2 at 2.  unfold FiO3 at 2.
  repeat rewrite (@If_morph (fun x => (ph3 ≟ (π2 x)))).
  rewrite proj2pair.
  rewrite ph2Neqph3.

(*  *)
  rewrite AndGuard.
  assert (((ph3 ≟ (π2 decS (τ1 (FFΦ5 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1'))))) & (ph3 ≟ (π2 decS (τ2 (FFΦ5 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1')))))
         & (ph3 ≟ (π2 decS (τ3 (FFΦ5 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1'))))))
        = (pchko (＜ FO1 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1'), FO2 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1'),
                     FO3 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1') ＞))).
    unfold pchko. rewrite Tau1Tri, Tau2Tri, Tau3Tri.
    reflexivity.
    simpl. rewrite H; clear H.
    repeat rewrite (@If_morph (fun x => If dist (FiO1 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1'))
                                        (FiO2 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1'))
                                        (FiO3 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1')) & x
           Then shufl (π1 FiO1 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1')) (π1 FiO2 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1'))
         (π1 FiO3 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1')) Else ⫠)).
  repeat rewrite If_same.
  repeat rewrite If_false.

(*  *)
  unfold FiO1, FiO2, FiO3.
  rewrite (@If_eval (fun _ => _) (fun b1 => If _ Then ⫠ Else If _ Then ⫠
                                      Else If dist (If b1 Then _ Else _) _ _ & pchko (＜ _, _ , _ ＞) Then shufl (π1 If b1 Then _ Else _ ) (π1 _) (π1 _) Else ⫠)).
    rewrite If_false.
  rewrite (@If_eval (fun _ => _) (fun b2 => If _ Then ⫠
                                      Else If dist _ (If b2 Then _ Else _) _ & pchko (＜ _,  _, _ ＞) Then shufl (π1 _) (π1 If b2 Then _ Else _ ) (π1 _) Else ⫠)).
    rewrite If_false.
  rewrite (@If_eval (fun _ => _) (fun b3 => If dist _ _ (If b3 Then _ Else _) & pchko (＜ _, _, _ ＞) Then shufl (π1 _) (π1 _) (π1 If b3 Then _ Else _ ) Else ⫠)).
    rewrite If_false.

(*  *)
  reflexivity.

  all : time ProveboolandContext. (*2.667 secs*)
Qed.

(*  *)

Lemma lemma25_CCA2Game2kc: forall side,
  (fun c0 c1 => (fun y1 => (fun o1 o2 o3 => [b0 c0; b1 c1; (If ((acc0 c0 c1) & (acc1 c0 c1)) Then
                     (If  ((τ1 (fFΦ2 c0 c1 (e0 c0 c1 n0'))) ≟ (e0 c0 c1 n0'))
                       or ((τ2 (fFΦ2 c0 c1 (e0 c0 c1 n0'))) ≟ (e0 c0 c1 n0'))
                       or ((τ3 (fFΦ2 c0 c1 (e0 c0 c1 n0'))) ≟ (e0 c0 c1 n0'))
                      Then ⫠
                      Else (＜＜ (e0 c0 c1 n0') ,  (e1 c0 c1 n1),
                                (dv (Fv1 c0 c1 (e0 c0 c1 n0')) (Fv2 c0 c1 (e0 c0 c1 n0')) (Fv3 c0 c1 (e0 c0 c1 n0'))
                                    (shufl (π1 (Fv1 c0 c1 (e0 c0 c1 n0'))) (π1 (Fv2 c0 c1 (e0 c0 c1 n0'))) (π1 (Fv3 c0 c1 (e0 c0 c1 n0'))))) ＞,
                              ＜ ⫠,
                                FL1 c0 c1 y1,
                               (FIDO o1 o2 o3 )＞＞)) Else ⫠)] (**)
           ) (FiiO1 c0 c1 y1) (FiiO2 c0 c1 y1) (FiiO3 c0 c1 y1)
  ) (E1 c0 c1 kc1')) (c0 side) (c1 side)
 =
  (fun c0 c1 => (fun y1 => (fun o1 o2 o3 => [b0 c0; b1 c1; (If ((acc0 c0 c1) & (acc1 c0 c1)) Then
                     (If  ((τ1 (fFΦ2 c0 c1 (e0 c0 c1 n0'))) ≟ (e0 c0 c1 n0'))
                       or ((τ2 (fFΦ2 c0 c1 (e0 c0 c1 n0'))) ≟ (e0 c0 c1 n0'))
                       or ((τ3 (fFΦ2 c0 c1 (e0 c0 c1 n0'))) ≟ (e0 c0 c1 n0'))
                      Then ⫠
                      Else (＜＜ (e0 c0 c1 n0') ,  (e1 c0 c1 n1),
                                (dv (Fv1 c0 c1 (e0 c0 c1 n0')) (Fv2 c0 c1 (e0 c0 c1 n0')) (Fv3 c0 c1 (e0 c0 c1 n0'))
                                    (shufl (π1 (Fv1 c0 c1 (e0 c0 c1 n0'))) (π1 (Fv2 c0 c1 (e0 c0 c1 n0'))) (π1 (Fv3 c0 c1 (e0 c0 c1 n0'))))) ＞,
                              ＜ ⫠,
                                FL1 c0 c1 y1,
                               (FDO o1 o2 o3 )＞＞)) Else ⫠)] (**)
           ) (FiO1 c0 c1 y1) (FiO2 c0 c1 y1) (FiO3 c0 c1 y1)
  ) (E1 c0 c1 kc1')) (c0 side) (c1 side).
Proof.
  (* Same kind of theorems are needed to replace n0 on the other side, and kc1. Then use hiding. *)
  intros. simpl.
  rewrite <- lemma25_elim_kc1_in_FIDO.
  rewrite lemma25_elim_kc1_in_then_branch.
  rewrite lemma25_elim_bot_in_then_branch.
  reflexivity.
Qed.


(*************************************************************************)
(***** Next we put together what we have so far using transitivity: ******)
(*************************************************************************)


Proposition remove_n0_and_kc1_from_both : forall side,
    (| ＜ pv0 (c0 side) (c1 side) n0, ph2 ＞ |) = (| ＜ pv0 (c0 side) (c1 side) n0', ph2 ＞ |) ->
    (| (M1  (c0 side) (c1 side) kc1) | = |(M1  (c0 side) (c1 side) kc1') |) ->
  (fun c0 c1 => (fun x0 => (fun v1 v2 v3 => [b0 c0; b1 c1; (If ((acc0 c0 c1) & (acc1 c0 c1)) Then
                                   (If ((τ1 (fFΦ2 c0 c1 x0)) ≟ x0)  or ((τ2 (fFΦ2 c0 c1 x0)) ≟ x0)  or ((τ3 (fFΦ2 c0 c1 x0)) ≟ x0)
                                    Then ⫠
                                    Else (＜＜ x0 ,               (e1 c0 c1 n1),            (dv v1 v2 v3 (s v1 v2 v3) ) ＞,
                                           ＜ Fl0 c0 c1 x0 v1 v2 v3, Fl1 c0 c1 x0 v1 v2 v3, (Fdo c0 c1 x0 v1 v2 v3 )＞＞)) Else ⫠)] (**)
             ) (Fv1 c0 c1 x0) (Fv2 c0 c1 x0) (Fv3 c0 c1 x0)
  ) (e0 c0 c1 n0)) (c0 side) (c1 side)
 ~
  (fun c0 c1 => (fun y1 => (fun o1 o2 o3 => [b0 c0; b1 c1; (If ((acc0 c0 c1) & (acc1 c0 c1)) Then
                     (If  ((τ1 (fFΦ2 c0 c1 (e0 c0 c1 n0'))) ≟ (e0 c0 c1 n0'))
                       or ((τ2 (fFΦ2 c0 c1 (e0 c0 c1 n0'))) ≟ (e0 c0 c1 n0'))
                       or ((τ3 (fFΦ2 c0 c1 (e0 c0 c1 n0'))) ≟ (e0 c0 c1 n0'))
                      Then ⫠
                      Else (＜＜ (e0 c0 c1 n0') ,  (e1 c0 c1 n1),
                                (dv (Fv1 c0 c1 (e0 c0 c1 n0')) (Fv2 c0 c1 (e0 c0 c1 n0')) (Fv3 c0 c1 (e0 c0 c1 n0'))
                                    (shufl (π1 (Fv1 c0 c1 (e0 c0 c1 n0'))) (π1 (Fv2 c0 c1 (e0 c0 c1 n0'))) (π1 (Fv3 c0 c1 (e0 c0 c1 n0'))))) ＞,
                              ＜ ⫠,
                                FL1 c0 c1 y1,
                               (FDO o1 o2 o3 )＞＞)) Else ⫠)] (**)
           ) (FiO1 c0 c1 y1) (FiO2 c0 c1 y1) (FiO3 c0 c1 y1)
  ) (E1 c0 c1 kc1')) (c0 side) (c1 side).
Proof.
  (* transitivity of ~ and the removal of n0 and kc1 and some of the above rewrites *)
  intros. simpl.
  rewrite prop25_replace_n0_with_n0'.
  rewrite lemma25_CCA2Game1kc.
  rewrite prop25_replace_kc1_with_kc1'.
  rewrite lemma25_CCA2Game2kc.
  reflexivity.
  all : auto.
Qed.








(*************************************************************************)
(***** Finally, we use hiding property of the Commitment to  *************)
(***** show equivalence of the two sides *********************************)
(*************************************************************************)


Lemma lemma25 :
    (fun c0 c1 => [b0 c0; b1 c1; (If ((acc0 c0 c1) & (acc1 c0 c1)) Then
                              (If ((τ1 (fΦ2 c0 c1)) ≟ (e0 c0 c1 n0)) or ((τ2 (fΦ2 c0 c1)) ≟ (e0 c0 c1 n0)) or ((τ3 (fΦ2 c0 c1)) ≟ (e0 c0 c1 n0))
                                    Then ⫠
                                    Else (＜＜(e0 c0 c1 n0), (e1 c0 c1 n1), (dv (v1 c0 c1) (v2 c0 c1) (v3 c0 c1) (s (v1 c0 c1) (v2 c0 c1) (v3 c0 c1)) ) ＞,
                                           ＜ l0 c0 c1,      l1 c0 c1,      (do c0 c1)＞＞)) Else ⫠)]) (c0 lhs) (c1 lhs)
   ~
    (fun c0 c1 => [b0 c0; b1 c1; (If ((acc0 c0 c1) & (acc1 c0 c1)) Then
                              (If ((τ1 (fΦ2 c0 c1)) ≟ (e0 c0 c1 n0)) or ((τ2 (fΦ2 c0 c1)) ≟ (e0 c0 c1 n0)) or ((τ3 (fΦ2 c0 c1)) ≟ (e0 c0 c1 n0))
                                    Then ⫠
                                    Else (＜＜(e0 c0 c1 n0), (e1 c0 c1 n1), (dv (v1 c0 c1) (v2 c0 c1) (v3 c0 c1) (s (v1 c0 c1) (v2 c0 c1) (v3 c0 c1)) ) ＞,
                                           ＜ l0 c0 c1,      l1 c0 c1,      (do c0 c1)＞＞)) Else ⫠)]) (c0 rhs) (c1 rhs).
Proof.
  intros.
  rewrite (remove_n0_and_kc1_from_both lhs).
  rewrite (remove_n0_and_kc1_from_both rhs).
  simpl.

(*  *)
  assert ([c00; c01; b0 c00; b1 c01; acc0 c00 c01 & acc1 c00 c01; e0 c00 c01 n0'; e1 c00 c01 n1;
    dv (Fv1 c00 c01 (e0 c00 c01 n0')) (Fv2 c00 c01 (e0 c00 c01 n0')) (Fv3 c00 c01 (e0 c00 c01 n0'))
                 (shufl (π1 Fv1 c00 c01 (e0 c00 c01 n0')) (π1 Fv2 c00 c01 (e0 c00 c01 n0')) (π1 Fv3 c00 c01 (e0 c00 c01 n0')));
    FL1 c00 c01 (E1 c00 c01 kc1'); FDO (FiO1 c00 c01 (E1 c00 c01 kc1')) (FiO2 c00 c01 (E1 c00 c01 kc1')) (FiO3 c00 c01 (E1 c00 c01 kc1')) ]
 ~
   [c10; c11; b0 c10; b1 c11; acc0 c10 c11 & acc1 c10 c11; e0 c10 c11 n0'; e1 c10 c11 n1;
    dv (Fv1 c10 c11 (e0 c10 c11 n0')) (Fv2 c10 c11 (e0 c10 c11 n0')) (Fv3 c10 c11 (e0 c10 c11 n0'))
                 (shufl (π1 Fv1 c10 c11 (e0 c10 c11 n0')) (π1 Fv2 c10 c11 (e0 c10 c11 n0')) (π1 Fv3 c10 c11 (e0 c10 c11 n0'))) ;
    FL1 c10 c11 (E1 c10 c11 kc1'); FDO (FiO1 c10 c11 (E1 c10 c11 kc1')) (FiO2 c10 c11 (E1 c10 c11 kc1')) (FiO3 c10 c11 (E1 c10 c11 kc1'))]).
    pose lemma25_freshcΦ3kc0.
    pose lemma25_freshcΦ3kc1.
    pose lemma25_freshcΦ5kc0.
    pose lemma25_freshcΦ5kc1.
    apply (@CompHidEx (fun lx => let c0 := Nth 0 lx in let c1 := Nth 1 lx in
         [c0; c1; b0 c0; b1 c1; acc0 c0 c1 & acc1 c0 c1; e0 c0 c1 n0'; e1 c0 c1 n1;
          dv (Fv1 c0 c1 (e0 c0 c1 n0')) (Fv2 c0 c1 (e0 c0 c1 n0')) (Fv3 c0 c1 (e0 c0 c1 n0'))
             (shufl (π1 Fv1 c0 c1 (e0 c0 c1 n0')) (π1 Fv2 c0 c1 (e0 c0 c1 n0')) (π1 Fv3 c0 c1 (e0 c0 c1 n0'))); FL1 c0 c1 (E1 c0 c1 kc1');
          FDO (FiO1 c0 c1 (E1 c0 c1 kc1')) (FiO2 c0 c1 (E1 c0 c1 kc1')) (FiO3 c0 c1 (E1 c0 c1 kc1'))       ])
                    vot0 vot1 0 1).
    all : simpl; time ProveFreshC. (*4.216 secs*)

    (*  *)
  apply voteLen.

(*  *)
  1, 2: ProveFresh.

(*   *)
  apply (@cind_funcapp (fun lc => [Nth 2 lc; Nth 3 lc; Nth 4 lc; Nth 5 lc; Nth 6 lc;
                                ((τ1 (f2 [(Nth 2 lc); (Nth 3 lc); (Nth 5 lc); (Nth 6 lc)])) ≟ (Nth 5 lc)) or
                                ((τ2 (f2 [(Nth 2 lc); (Nth 3 lc); (Nth 5 lc); (Nth 6 lc)])) ≟ (Nth 5 lc)) or
                                ((τ3 (f2 [(Nth 2 lc); (Nth 3 lc); (Nth 5 lc); (Nth 6 lc)])) ≟ (Nth 5 lc));
                               Nth 7 lc; Nth 8 lc; Nth 9 lc])) in H. unfold Nth in H.  unfold nth in H; simpl in H.

  apply (IF_branch' [b0 c00; b1 c01] [b0 c10; b1 c11] _ _ _ _ _ _ ); simpl.
  apply (IF_branch' [b0 c00; b1 c01; acc0 c00 c01 & acc1 c00 c01] [b0 c10; b1 c11; acc0 c10 c11 & acc1 c10 c11] _ _ _ _ _ _ ); simpl.

(**)
  assert (exists x, x = H). exists H; auto. destruct H0. clear H0. rename x into H0.
  apply (@cind_funcapp (fun lc => [(Nth 0 lc); (Nth 1 lc); (Nth 2 lc); (Nth 5 lc); ⫠])) in H0.
     unfold Nth in H0; unfold nth in H0; simpl in H0; apply H0. simpl; ProveContext.
(**)
  assert (exists x, x = H). exists H; auto. destruct H0. clear H0. rename x into H0.
  apply (@cind_funcapp (fun lc => [(Nth 0 lc); (Nth 1 lc); (Nth 2 lc); (Nth 5 lc);
  ＜ ＜ (Nth 3 lc), (Nth 4 lc), (Nth 6 lc) ＞, ＜ ⫠, (Nth 7 lc), (Nth 8 lc) ＞ ＞])) in H0.
     unfold Nth in H0; unfold nth in H0; simpl in H0; auto. clear H0. simpl; ProveContext.

  apply (@cind_funcapp (fun lc => [(Nth 0 lc); (Nth 1 lc); (Nth 2 lc); ⫠])) in H.
     unfold Nth in H; unfold nth in H; simpl in H; auto. clear H. simpl; ProveContext.

  clear H.
  ProveContext.
  - unfold pv0.
    apply PairLen.
    + apply TripleLen.
      * reflexivity.
      * reflexivity.
    + reflexivity.
  - unfold M1.
    apply PairLen.
    + apply PairLen.
      reflexivity.
      apply ComkLen.
    + reflexivity.
  - unfold pv0.
    apply PairLen.
    + apply TripleLen.
      * reflexivity.
      * reflexivity.
    + reflexivity.
  - unfold M1.
    apply PairLen.
    + apply PairLen.
      reflexivity.
      apply ComkLen.
    + reflexivity.
Qed.

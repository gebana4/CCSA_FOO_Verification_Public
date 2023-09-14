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



(***********************************************************************************************************************************)


(**)
Lemma elim_isinkc0_under_bcheck0_in_ELSE_branch : forall s,
  (fun c0 c1 => ((fun enco1 => (fun o1 o2 o3 => Do o1 o2 o3  ) (FGO1 c0 c1 ⫠ enco1) (FGO2 c0 c1 ⫠ enco1) (FGO3 c0 c1 ⫠ enco1)) (enco1 c0 c1 kc1))
           = ((fun enco1 => (fun o1 o2 o3 => FIDO o1 o2 o3) (FGO1 c0 c1 ⫠ enco1) (FGO2 c0 c1 ⫠ enco1) (FGO3 c0 c1 ⫠ enco1)) (enco1 c0 c1 kc1))) (c0 s) (c1 s).
Proof.
  intros; simpl.
  unfold Do.
  unfold isinkc.
  assert (isin kc0 (＜ π2 (π1 FGO1 (c0 s) (c1 s) ⫠ (enco1 (c0 s) (c1 s) kc1)), π2 (π1 FGO2 (c0 s) (c1 s) ⫠ (enco1 (c0 s) (c1 s) kc1)), π2 (π1 FGO3 (c0 s) (c1 s) ⫠ (enco1 (c0 s) (c1 s) kc1)) ＞) = FAlse).
    unfold isin.
    rewrite Tau1Tri, Tau2Tri, Tau3Tri.
    rewrite Freshkc0FGO1_15, Freshkc0FGO2_15, Freshkc0FGO3_15.
    repeat rewrite If_false.
    reflexivity.
  rewrite H. clear H.
  rewrite If_false.
  reflexivity.
Qed.





(* actually the encryption enco0 can be anything excludes kc0  *)
(*  *)
Lemma GIIO_GIO_equiv_under_FIDO: forall s,
    (fun c0 c1 => ((fun enco1 m => (fun o1 o2 o3 => FIDO o1 o2 o3) (GIIO1 c0 c1 enco1 m) (GIIO2 c0 c1 enco1 m) (GIIO3 c0 c1 enco1 m))  (enco1 c0 c1 kc1')
                                                                                                                           (＜ ＜ label c1 (fΦΦ3 c0 c1), kc1 ＞, ph3 ＞))
             = ((fun enco1 =>   (fun o1 o2 o3 => FIDO o1 o2 o3) (GIO1 c0 c1 enco1)    (GIO2 c0 c1 enco1)    (GIO3 c0 c1 enco1))  (enco1 c0 c1 kc1'))) (c0 s) (c1 s).
Proof.
  intros. simpl.

  pose (ContextPhase5_15 s) as HH.
  pose (ContextEnco1 s) as HH0.
  pose (ContextPhase3_15 s) as HH1.

(* left hand side *)
  rewrite (GuardAhead' (FIDO (GIIO1 (c0 s) (c1 s) (enco1 (c0 s) (c1 s) kc1') (＜ ＜ label (c1 s) (fΦΦ3 (c0 s) (c1 s)), kc1 ＞, ph3 ＞))
                             (GIIO2 (c0 s) (c1 s) (enco1 (c0 s) (c1 s) kc1') (＜ ＜ label (c1 s) (fΦΦ3 (c0 s) (c1 s)), kc1 ＞, ph3 ＞))
                             (GIIO3 (c0 s) (c1 s) (enco1 (c0 s) (c1 s) kc1') (＜ ＜ label (c1 s) (fΦΦ3 (c0 s) (c1 s)), kc1 ＞, ph3 ＞)))
                       (τ1 (FGΦΦ5 (c0 s) (c1 s) ⫠ (enco1 (c0 s) (c1 s) kc1')) ≟ enco1 (c0 s) (c1 s) kc1')
                       (τ2 (FGΦΦ5 (c0 s) (c1 s) ⫠ (enco1 (c0 s) (c1 s) kc1')) ≟ enco1 (c0 s) (c1 s) kc1' )
                       (τ3 (FGΦΦ5 (c0 s) (c1 s) ⫠ (enco1 (c0 s) (c1 s) kc1')) ≟ enco1 (c0 s) (c1 s) kc1' )).
  unfold GIIO3. repeat rewrite decSimpl.
  rewrite (@If_eval (fun b3 =>  FIDO _ _ (If b3 Then _ Else _)) (fun b3 => FIDO _ _ (If b3 Then _ Else _))).
  rewrite If_true, If_false.
  unfold GIIO2. repeat rewrite decSimpl.
  rewrite (@If_eval (fun b2 => If _ Then FIDO _ (If b2 Then _ Else _) _ Else FIDO _ (If b2 Then _ Else _) _)
                    (fun b2 => If _ Then FIDO _ (If b2 Then _ Else _) _ Else FIDO _ (If b2 Then _ Else _) _)).
  rewrite If_true, If_false.
  unfold GIIO1. repeat rewrite decSimpl.
  rewrite (@If_eval (fun b1 => If _ Then If _ Then FIDO (If b1 Then _ Else _) _ _ Else FIDO (If b1 Then _ Else _) _ _
                                 Else If _ Then FIDO (If b1 Then _ Else _) _ _ Else FIDO (If b1 Then _ Else _) _ _ )
                    (fun b1 => If _ Then If _ Then FIDO (If b1 Then _ Else _) _ _ Else FIDO (If b1 Then _ Else _) _ _
                                 Else If _ Then FIDO (If b1 Then _ Else _) _ _ Else FIDO (If b1 Then _ Else _) _ _ )).
  rewrite If_true, If_false.

  unfold FIDO at 1 2 3 4 5 6 7. unfold isin.
  repeat rewrite Tau1Tri, Tau2Tri, Tau3Tri.
  repeat rewrite proj1pair.
  repeat rewrite proj2pair.
  repeat rewrite ceqeq.
  repeat rewrite If_true.
  repeat rewrite If_same.
  repeat rewrite If_true.
  repeat rewrite If_false.
  repeat rewrite If_same.
  repeat rewrite If_false.
  repeat rewrite If_same.


(* Right hand side *)
  rewrite (GuardAhead' (FIDO (GIO1 (c0 s) (c1 s) (enco1 (c0 s) (c1 s) kc1')) (GIO2 (c0 s) (c1 s) (enco1 (c0 s) (c1 s) kc1')) (GIO3 (c0 s) (c1 s) (enco1 (c0 s) (c1 s) kc1')))
                       (τ1 (FGΦΦ5 (c0 s) (c1 s) ⫠ (enco1 (c0 s) (c1 s) kc1')) ≟ (enco1 (c0 s) (c1 s) kc1'))
                       (τ2 (FGΦΦ5 (c0 s) (c1 s) ⫠ (enco1 (c0 s) (c1 s) kc1')) ≟ (enco1 (c0 s) (c1 s) kc1'))
                       (τ3 (FGΦΦ5 (c0 s) (c1 s) ⫠ (enco1 (c0 s) (c1 s) kc1')) ≟ (enco1 (c0 s) (c1 s) kc1'))).
  unfold GIO3.
  rewrite (@If_eval (fun b3 =>  FIDO _ _ (If b3 Then _ Else _)) (fun b3 => FIDO _ _ (If b3 Then _ Else _))).
  rewrite If_true, If_false.
  unfold GIO2.
  rewrite (@If_eval (fun b2 => If _ Then FIDO _ (If b2 Then _ Else _) _ Else FIDO _ (If b2 Then _ Else _) _)
                    (fun b2 => If _ Then FIDO _ (If b2 Then _ Else _) _ Else FIDO _ (If b2 Then _ Else _) _)).
  rewrite If_true, If_false.
  unfold GIO1.
  rewrite (@If_eval (fun b1 => If _ Then If _ Then FIDO (If b1 Then _ Else _) _ _ Else FIDO (If b1 Then _ Else _) _ _
                                 Else If _ Then FIDO (If b1 Then _ Else _) _ _ Else FIDO (If b1 Then _ Else _) _ _ )
                    (fun b1 => If _ Then If _ Then FIDO (If b1 Then _ Else _) _ _ Else FIDO (If b1 Then _ Else _) _ _
                                 Else If _ Then FIDO (If b1 Then _ Else _) _ _ Else FIDO (If b1 Then _ Else _) _ _ )).
  rewrite If_true, If_false.

  unfold FIDO at 2 3 4 5 6 7 8. unfold pchko.
  repeat rewrite Tau1Tri, Tau2Tri, Tau3Tri.
  repeat rewrite proj2pair.
  repeat rewrite ph2Neqph3.
  repeat rewrite If_false.
  repeat rewrite If_same.
  repeat rewrite If_false.
  repeat rewrite If_same.
  repeat rewrite If_false.
  repeat rewrite If_same.
  reflexivity.


  all: time ProveboolandContext. (* 11.55 secs *)

Qed.






(* *)
Lemma elim_isinkc1_after_CCA2 : forall s,
    (fun c0 c1 => ((fun enco1 => (fun o1 o2 o3 => FIDO o1 o2 o3) (GIO1 c0 c1 enco1)  (GIO2 c0 c1 enco1)  (GIO3 c0 c1 enco1))  (enco1 c0 c1 kc1'))
             = ((fun enco1 => (fun o1 o2 o3 => FDO o1 o2 o3)  (GIO1 c0 c1 enco1)  (GIO2 c0 c1 enco1)  (GIO3 c0 c1 enco1))  (enco1 c0 c1 kc1'))) (c0 s) (c1 s).
Proof.
  intros. simpl.
  unfold FIDO.

  assert (isin kc1 (＜ π2 (π1 GIO1 (c0 s) (c1 s) (enco1 (c0 s) (c1 s) kc1')), π2 (π1 GIO2 (c0 s) (c1 s) (enco1 (c0 s) (c1 s) kc1')), π2 (π1 GIO3 (c0 s) (c1 s) (enco1 (c0 s) (c1 s) kc1')) ＞) = FAlse).
    unfold isin.
    rewrite Tau1Tri, Tau2Tri, Tau3Tri.
    rewrite kc1FreshGIO1, kc1FreshGIO2, kc1FreshGIO3.
    repeat rewrite If_false.
    reflexivity.

  rewrite H; clear H.
  rewrite If_false. rewrite <- If_tf.
  reflexivity.
  unfold pchko. Provebool.
Qed.


(* *)

(* *)

(* *)



(* first we use CCA2 for the second encryption of the opening phase *)
Lemma prop26_formula15_helper:  forall s, (fun c0 c1 =>
     ((fun enco1 => (fun o1 o2 o3 =>
       [b0 c0; b1 c1; acc0 c0 c1 & acc1 c0 c1; bnlcheck c0 n0 (fΦΦ3 c0 c1); bnlcheck c1 n1 (fΦΦ3 c0 c1);
  ＜ ＜ e0 c0 c1 n0, e1 c0 c1 n1, dv (v1 c0 c1) (v2 c0 c1) (v3 c0 c1) (s26 c0 c1 (v3 c0 c1)) ＞,
  ＜ ⫠, enco1, Do o1 o2 o3 ＞ ＞]) (FGO1 c0 c1 ⫠ enco1 ) (FGO2 c0 c1 ⫠ enco1) (FGO3 c0 c1 ⫠ enco1)) (enco1 c0 c1 kc1))
 ~
    ((fun enco1 => (fun o1 o2 o3 =>
    [b0 c0; b1 c1; acc0 c0 c1 & acc1 c0 c1; bnlcheck c0 n0 (fΦΦ3 c0 c1); bnlcheck c1 n1 (fΦΦ3 c0 c1);
  ＜ ＜ e0 c0 c1 n0, e1 c0 c1 n1, dv (v1 c0 c1) (v2 c0 c1) (v3 c0 c1) (s26 c0 c1 (v3 c0 c1)) ＞,
  ＜ ⫠, enco1, FDO o1 o2 o3 ＞ ＞]) (GIO1 c0 c1 enco1) (GIO2 c0 c1 enco1) (GIO3 c0 c1 enco1)) (enco1 c0 c1 kc1'))) (c0 s) (c1 s).
Proof.
  intros s. simpl.

(* elim the isinkc1 check in Do, change Do to GIDO *)
  rewrite (elim_isinkc0_under_bcheck0_in_ELSE_branch s).


(* usc CCA2 to substitute (FGO enco0) to (FGIIO enco0') on the left hand side*)
  unfold FGO1.
  rewrite (decIfThenElse (＜ ＜ label (c1 s) (fΦΦ3 (c0 s) (c1 s)), kc1 ＞, ph3 ＞) 11 (τ1 (FGΦΦ5 (c0 s) (c1 s) ⫠ (enco1 (c0 s) (c1 s) kc1)))).
  unfold FGO2.
  rewrite (decIfThenElse (＜ ＜ label (c1 s) (fΦΦ3 (c0 s) (c1 s)), kc1 ＞, ph3 ＞) 11 (τ2 (FGΦΦ5 (c0 s) (c1 s) ⫠ (enco1 (c0 s) (c1 s) kc1)))).
  unfold FGO3.
  rewrite (decIfThenElse (＜ ＜ label (c1 s) (fΦΦ3 (c0 s) (c1 s)), kc1 ＞, ph3 ＞) 11 (τ3 (FGΦΦ5 (c0 s) (c1 s) ⫠ (enco1 (c0 s) (c1 s) kc1)))).
  pose (cca2 [nonce 6] [nonce 11]
            (fun enco1 => [b0 (c0 s); b1 (c1 s); acc0 (c0 s) (c1 s) & acc1 (c0 s) (c1 s);
                                   bnlcheck (c0 s) n0 (fΦΦ3 (c0 s) (c1 s)); bnlcheck (c1 s) n1 (fΦΦ3 (c0 s) (c1 s));
                                   ＜ ＜ e0 (c0 s) (c1 s) n0, e1 (c0 s) (c1 s) n1, dv (v1 (c0 s) (c1 s)) (v2 (c0 s) (c1 s)) (v3 (c0 s) (c1 s)) (s26 (c0 s) (c1 s) (v3 (c0 s) (c1 s))) ＞,
                                   ＜ ⫠,  enco1 , (FIDO (GIIO1 (c0 s) (c1 s) enco1 (＜ ＜ label (c1 s) (fΦΦ3 (c0 s) (c1 s)), kc1 ＞, ph3 ＞))
                                                       (GIIO2 (c0 s) (c1 s) enco1 (＜ ＜ label (c1 s) (fΦΦ3 (c0 s) (c1 s)), kc1 ＞, ph3 ＞)) (* shit, here should be FIIO2!!!*)
                                                       (GIIO3 (c0 s) (c1 s) enco1 (＜ ＜ label (c1 s) (fΦΦ3 (c0 s) (c1 s)), kc1 ＞, ph3 ＞)))＞＞])
             (＜ ＜ label (c1 s) (fΦΦ3 (c0 s) (c1 s)), kc1 ＞, ph3 ＞) (＜ ＜ label (c1 s) (fΦΦ3 (c0 s) (c1 s)), kc1' ＞, ph3 ＞)) as claim0; simpl in claim0.
  rewrite claim0. clear claim0.


(* reduce (FGIIO enco0') to (FGIO enco0')*)
  rewrite GIIO_GIO_equiv_under_FIDO.

(* change FIIO*)
  rewrite elim_isinkc1_after_CCA2.
  reflexivity.

  clear claim0.
  4: apply (CCA2Beforekc1_formula15).
  4: apply (CCA2Beforekc1'_formula15).
  4: apply CCA2AfterLemma26_formula15.

  all : ProveCCA2.
  ProveListFresh; try lia; constructor.

  apply PairLen.
  - apply PairLen.
    + reflexivity.
    + apply ComkLen.
  - reflexivity.
Qed.




(*  *)

(* formula 15  on page 40  *)
Proposition prop26_formula15 :
  (fun c0 c1 => ((fun enco1 => (fun o1 o2 o3 =>
       [b0 c0; b1 c1; acc0 c0 c1 & acc1 c0 c1; bnlcheck c0 n0 (fΦΦ3 c0 c1); bnlcheck c1 n1 (fΦΦ3 c0 c1);
  ＜ ＜ e0 c0 c1 n0, e1 c0 c1 n1, dv (v1 c0 c1) (v2 c0 c1) (v3 c0 c1) (s26 c0 c1 (v3 c0 c1)) ＞,
  ＜ ⫠, enco1, Do o1 o2 o3 ＞ ＞]) (FGO1 c0 c1 ⫠ enco1) (FGO2 c0 c1 ⫠ enco1) (FGO3 c0 c1 ⫠ enco1)) (enco1 c0 c1 kc1))) (c0 lhs) (c1 lhs)
 ~
   (fun c0 c1 => ((fun enco1 => (fun o1 o2 o3 =>
       [b0 c0; b1 c1; acc0 c0 c1 & acc1 c0 c1; bnlcheck c0 n0 (fΦΦ3 c0 c1); bnlcheck c1 n1 (fΦΦ3 c0 c1);
  ＜ ＜ e0 c0 c1 n0, e1 c0 c1 n1, dv (v1 c0 c1) (v2 c0 c1) (v3 c0 c1) (s26 c0 c1 (v3 c0 c1)) ＞,
  ＜ ⫠, enco1, Do o1 o2 o3 ＞ ＞]) (FGO1 c0 c1 ⫠ enco1) (FGO2 c0 c1 ⫠ enco1) (FGO3 c0 c1 ⫠ enco1)) (enco1 c0 c1 kc1))) (c0 rhs) (c1 rhs).

Proof.
  intros.
(* use prop26_lemma14_helper to change both sides from {Do FGO} to {FDO FIO} *)
  rewrite (prop26_formula15_helper lhs).
  rewrite (prop26_formula15_helper rhs).

(* use commitment hidding *)
   apply (@CompHidEx (fun lx => let c0 := Nth 0 lx in let c1 := Nth 1 lx in
         [b0 c0; b1 c1; acc0 c0 c1 & acc1 c0 c1; bnlcheck c0 n0 (fΦΦ3 c0 c1); bnlcheck c1 n1 (fΦΦ3 c0 c1);
          ＜ ＜ e0 c0 c1 n0, e1 c0 c1 n1, dv (v1 c0 c1) (v2 c0 c1) (v3 c0 c1) (s26 c0 c1 (v3 c0 c1)) ＞,
             ＜ ⫠, enco1 c0 c1 kc1',  FDO (GIO1 c0 c1 (enco1 c0 c1 kc1')) (GIO2 c0 c1 (enco1 c0 c1 kc1')) (GIO3 c0 c1 (enco1 c0 c1 kc1')) ＞ ＞])
                    vot0 vot1 0 1).
  apply voteLen.
  lia. ProveFresh.
  apply Freshc_kc0_Lemma26_15.
  ProveFresh.
  apply Freshc_kc1_Lemma26_15.
Qed.

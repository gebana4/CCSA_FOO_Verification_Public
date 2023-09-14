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


(*-------------------------------------------------------*)


(* The actual statement of formula14 in prop26 is at the end of file. *)

(* Notice that the proof idea of formula14 is quite similar to the lemma25. *)


(* In this proposition, we show that when the commitment key of the second voter is not sent out, isinkc1 check will fail. *)

Lemma elim_isinkc1_under_bcheck1_in_ELSE_branch : forall s,
  (fun c0 c1 => ((fun enco0 => (fun o1 o2 o3 => Do o1 o2 o3  ) (FGO1 c0 c1 enco0 ⫠) (FGO2 c0 c1 enco0 ⫠) (FGO3 c0 c1 enco0 ⫠)) (enco0 c0 c1 kc0))
           = ((fun enco0 => (fun o1 o2 o3 => GIDO o1 o2 o3) (FGO1 c0 c1 enco0 ⫠) (FGO2 c0 c1 enco0 ⫠) (FGO3 c0 c1 enco0 ⫠)) (enco0 c0 c1 kc0))) (c0 s) (c1 s).
Proof.
  intros; simpl.
  unfold Do.
  unfold isinkc.
  assert (isin kc1 (＜ π2 (π1 FGO1 (c0 s) (c1 s) (enco0 (c0 s) (c1 s) kc0) ⫠), π2 (π1 FGO2 (c0 s) (c1 s) (enco0 (c0 s) (c1 s) kc0) ⫠), π2 (π1 FGO3 (c0 s) (c1 s) (enco0 (c0 s) (c1 s) kc0) ⫠) ＞) = FAlse).
    unfold isin.
    rewrite Tau1Tri, Tau2Tri, Tau3Tri.
    rewrite Freshkc1FGO1, Freshkc1FGO2, Freshkc1FGO3.
    repeat rewrite If_false.
    reflexivity.
  rewrite H. clear H.
  rewrite If_false.
  reflexivity.
Qed.


(* This proposition is similar to lemma25_elim_bot_in_then_branch in lemma25, to show that two scenarios 
   "the plaintext sent from the second voter is ＜ ⫠, ph2 ＞,             and replaced with (＜＜label, kc0' ＞, ph3 ＞) by the attacker",
     and 
   "the plaintext sent from the second voter is ＜＜label, kc0 ＞, ph3 ＞, and replaced with (＜＜label, kc0' ＞, ph3 ＞) by the attacker",
   appear to be the same in the opening phase. *)

Lemma FIIO_FIO_equiv_under_GIDO: forall s,
    (fun c0 c1 => ((fun enco0 m => (fun o1 o2 o3 => GIDO o1 o2 o3) (FIIO1 c0 c1 enco0 m) (FIIO2 c0 c1 enco0 m) (FIIO3 c0 c1 enco0 m))
                                                            (enco0 c0 c1 kc0') (＜ ＜ label c0 (fΦΦ3 c0 c1), kc0 ＞, ph3 ＞))
             = ((fun enco0 =>   (fun o1 o2 o3 => GIDO o1 o2 o3) (FIO1 c0 c1 enco0)    (FIO2 c0 c1 enco0)    (FIO3 c0 c1 enco0))  (enco0 c0 c1 kc0'))) (c0 s) (c1 s).
Proof.
  intros. simpl.
  pose (ContextPhase5 s) as HH.
  pose (ContextEnco0 s) as HH0.
  pose (ContextPhase3 s) as HH1.

(* left hand side *)
  rewrite (GuardAhead' (GIDO (FIIO1 (c0 s) (c1 s) (enco0 (c0 s) (c1 s) kc0') (＜ ＜ label (c0 s) (fΦΦ3 (c0 s) (c1 s)), kc0 ＞, ph3 ＞))
    (FIIO2 (c0 s) (c1 s) (enco0 (c0 s) (c1 s) kc0') (＜ ＜ label (c0 s) (fΦΦ3 (c0 s) (c1 s)), kc0 ＞, ph3 ＞))
    (FIIO3 (c0 s) (c1 s) (enco0 (c0 s) (c1 s) kc0') (＜ ＜ label (c0 s) (fΦΦ3 (c0 s) (c1 s)), kc0 ＞, ph3 ＞)))
                       (τ1 (FGΦΦ5 (c0 s) (c1 s) (enco0 (c0 s) (c1 s) kc0') ⫠) ≟ enco0 (c0 s) (c1 s) kc0')
                       (τ2 (FGΦΦ5 (c0 s) (c1 s) (enco0 (c0 s) (c1 s) kc0') ⫠) ≟ enco0 (c0 s) (c1 s) kc0' )
                       (τ3 (FGΦΦ5 (c0 s) (c1 s) (enco0 (c0 s) (c1 s) kc0') ⫠) ≟ enco0 (c0 s) (c1 s) kc0' )).
  unfold FIIO3. repeat rewrite decSimpl.
  rewrite (@If_eval (fun b3 =>  GIDO _ _ (If b3 Then _ Else _)) (fun b3 => GIDO _ _ (If b3 Then _ Else _))).
  rewrite If_true, If_false.
  unfold FIIO2. repeat rewrite decSimpl.
  rewrite (@If_eval (fun b2 => If _ Then GIDO _ (If b2 Then _ Else _) _ Else GIDO _ (If b2 Then _ Else _) _)
                    (fun b2 => If _ Then GIDO _ (If b2 Then _ Else _) _ Else GIDO _ (If b2 Then _ Else _) _)).
  rewrite If_true, If_false.
  unfold FIIO1. repeat rewrite decSimpl.
  rewrite (@If_eval (fun b1 => If _ Then If _ Then GIDO (If b1 Then _ Else _) _ _ Else GIDO (If b1 Then _ Else _) _ _
                                 Else If _ Then GIDO (If b1 Then _ Else _) _ _ Else GIDO (If b1 Then _ Else _) _ _ )
                    (fun b1 => If _ Then If _ Then GIDO (If b1 Then _ Else _) _ _ Else GIDO (If b1 Then _ Else _) _ _
                                 Else If _ Then GIDO (If b1 Then _ Else _) _ _ Else GIDO (If b1 Then _ Else _) _ _ )).
  rewrite If_true, If_false.

  unfold GIDO at 1 2 3 4 5 6 7. unfold isin.
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
  rewrite (GuardAhead' (GIDO (FIO1 (c0 s) (c1 s) (enco0 (c0 s) (c1 s) kc0')) (FIO2 (c0 s) (c1 s) (enco0 (c0 s) (c1 s) kc0')) (FIO3 (c0 s) (c1 s) (enco0 (c0 s) (c1 s) kc0')))
                       (τ1 (FGΦΦ5 (c0 s) (c1 s) (enco0 (c0 s) (c1 s) kc0') ⫠) ≟ enco0 (c0 s) (c1 s) kc0')
                       (τ2 (FGΦΦ5 (c0 s) (c1 s) (enco0 (c0 s) (c1 s) kc0') ⫠) ≟ enco0 (c0 s) (c1 s) kc0' )
                       (τ3 (FGΦΦ5 (c0 s) (c1 s) (enco0 (c0 s) (c1 s) kc0') ⫠) ≟ enco0 (c0 s) (c1 s) kc0' )).
  unfold FIO3.
  rewrite (@If_eval (fun b3 =>  GIDO _ _ (If b3 Then _ Else _)) (fun b3 => GIDO _ _ (If b3 Then _ Else _))).
  rewrite If_true, If_false.
  unfold FIO2.
  rewrite (@If_eval (fun b2 => If _ Then GIDO _ (If b2 Then _ Else _) _ Else GIDO _ (If b2 Then _ Else _) _)
                    (fun b2 => If _ Then GIDO _ (If b2 Then _ Else _) _ Else GIDO _ (If b2 Then _ Else _) _)).
  rewrite If_true, If_false.
  unfold FIO1.
  rewrite (@If_eval (fun b1 => If _ Then If _ Then GIDO (If b1 Then _ Else _) _ _ Else GIDO (If b1 Then _ Else _) _ _
                                 Else If _ Then GIDO (If b1 Then _ Else _) _ _ Else GIDO (If b1 Then _ Else _) _ _ )
                    (fun b1 => If _ Then If _ Then GIDO (If b1 Then _ Else _) _ _ Else GIDO (If b1 Then _ Else _) _ _
                                 Else If _ Then GIDO (If b1 Then _ Else _) _ _ Else GIDO (If b1 Then _ Else _) _ _ )).
  rewrite If_true, If_false.

  unfold GIDO at 2 3 4 5 6 7 8. unfold pchko.
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

(* *)
  all: time ProveContext. (* 12.369 secs *)
  all : Provebool.
Qed.




(* *)

Lemma elim_isinkc0_after_CCA2 : forall s,
    (fun c0 c1 => ((fun enco0 => (fun o1 o2 o3 => GIDO o1 o2 o3) (FIO1 c0 c1 enco0)  (FIO2 c0 c1 enco0)  (FIO3 c0 c1 enco0))  (enco0 c0 c1 kc0'))
             = ((fun enco0 => (fun o1 o2 o3 => FDO o1 o2 o3)  (FIO1 c0 c1 enco0)  (FIO2 c0 c1 enco0)  (FIO3 c0 c1 enco0))  (enco0 c0 c1 kc0'))) (c0 s) (c1 s).
Proof.
  intros. simpl.
  unfold GIDO.

  assert (isin kc0 (＜ π2 (π1 FIO1 (c0 s) (c1 s) (enco0 (c0 s) (c1 s) kc0')), π2 (π1 FIO2 (c0 s) (c1 s) (enco0 (c0 s) (c1 s) kc0')), π2 (π1 FIO3 (c0 s) (c1 s) (enco0 (c0 s) (c1 s) kc0')) ＞) = FAlse).
    unfold isin.
    rewrite Tau1Tri, Tau2Tri, Tau3Tri.
    rewrite kc0FreshFIO1, kc0FreshFIO2, kc0FreshFIO3.
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
Lemma prop26_lemma14_helper:  forall s, (fun c0 c1 =>
     ((fun enco0 => (fun o1 o2 o3 =>
       [b0 c0; b1 c1; acc0 c0 c1 & acc1 c0 c1; bnlcheck c0 n0 (fΦΦ3 c0 c1); bnlcheck c1 n1 (fΦΦ3 c0 c1);
  ＜ ＜ e0 c0 c1 n0, e1 c0 c1 n1, dv (v1 c0 c1) (v2 c0 c1) (v3 c0 c1) (s26 c0 c1 (v3 c0 c1)) ＞,
  ＜ enco0, ⫠, Do o1 o2 o3 ＞ ＞]) (FGO1 c0 c1 enco0 ⫠) (FGO2 c0 c1 enco0 ⫠) (FGO3 c0 c1 enco0 ⫠)) (enco0 c0 c1 kc0))
 ~
    ((fun enco0 => (fun o1 o2 o3 =>
    [b0 c0; b1 c1; acc0 c0 c1 & acc1 c0 c1; bnlcheck c0 n0 (fΦΦ3 c0 c1); bnlcheck c1 n1 (fΦΦ3 c0 c1);
  ＜ ＜ e0 c0 c1 n0, e1 c0 c1 n1, dv (v1 c0 c1) (v2 c0 c1) (v3 c0 c1) (s26 c0 c1 (v3 c0 c1)) ＞,
  ＜ enco0, ⫠, FDO o1 o2 o3 ＞ ＞]) (FIO1 c0 c1 enco0) (FIO2 c0 c1 enco0) (FIO3 c0 c1 enco0)) (enco0 c0 c1 kc0'))) (c0 s) (c1 s).
Proof.
  intros s. simpl.

(* elim the isinkc1 check in Do, change Do to GIDO *)
  rewrite (elim_isinkc1_under_bcheck1_in_ELSE_branch s).


(* usc CCA2 to substitute (FGO enco0) to (FGIIO enco0') on the left hand side*)
  unfold FGO1.
  rewrite (decIfThenElse (＜ ＜ label (c0 s) (fΦΦ3 (c0 s) (c1 s)), kc0 ＞, ph3 ＞) 10 (τ1 (FGΦΦ5 (c0 s) (c1 s) (enco0 (c0 s) (c1 s) kc0) ⫠))).
  unfold FGO2.
  rewrite (decIfThenElse (＜ ＜ label (c0 s) (fΦΦ3 (c0 s) (c1 s)), kc0 ＞, ph3 ＞) 10 (τ2 (FGΦΦ5 (c0 s) (c1 s) (enco0 (c0 s) (c1 s) kc0) ⫠))).
  unfold FGO3.
  rewrite (decIfThenElse (＜ ＜ label (c0 s) (fΦΦ3 (c0 s) (c1 s)), kc0 ＞, ph3 ＞) 10 (τ3 (FGΦΦ5 (c0 s) (c1 s) (enco0 (c0 s) (c1 s) kc0) ⫠))).
  pose (cca2 [nonce 6] [nonce 10]
            (fun enco0 => [b0 (c0 s); b1 (c1 s); acc0 (c0 s) (c1 s) & acc1 (c0 s) (c1 s);
                                   bnlcheck (c0 s) n0 (fΦΦ3 (c0 s) (c1 s)); bnlcheck (c1 s) n1 (fΦΦ3 (c0 s) (c1 s));
                                   ＜ ＜ e0 (c0 s) (c1 s) n0, e1 (c0 s) (c1 s) n1, dv (v1 (c0 s) (c1 s)) (v2 (c0 s) (c1 s)) (v3 (c0 s) (c1 s)) (s26 (c0 s) (c1 s) (v3 (c0 s) (c1 s))) ＞,
                                   ＜ enco0 , ⫠, (GIDO (FIIO1 (c0 s) (c1 s) enco0 (＜ ＜ label (c0 s) (fΦΦ3 (c0 s) (c1 s)), kc0 ＞, ph3 ＞))
                                                       (FIIO2 (c0 s) (c1 s) enco0 (＜ ＜ label (c0 s) (fΦΦ3 (c0 s) (c1 s)), kc0 ＞, ph3 ＞)) (* shit, here should be FIIO2!!!*)
                                                       (FIIO3 (c0 s) (c1 s) enco0 (＜ ＜ label (c0 s) (fΦΦ3 (c0 s) (c1 s)), kc0 ＞, ph3 ＞)))＞＞])
             (＜ ＜ label (c0 s) (fΦΦ3 (c0 s) (c1 s)), kc0 ＞, ph3 ＞) (＜ ＜ label (c0 s) (fΦΦ3 (c0 s) (c1 s)), kc0' ＞, ph3 ＞)) as claim0; simpl in claim0.
  rewrite claim0. clear claim0.


(* reduce (FGIIO enco0') to (FGIO enco0')*)
  rewrite FIIO_FIO_equiv_under_GIDO.

(* change FIIO*)
  rewrite elim_isinkc0_after_CCA2.
  reflexivity.

  clear claim0.
  4: apply (CCA2Beforekc0_formula14).
  4: apply (CCA2Beforekc0'_formula14).
  4: apply CCA2AfterLemma26_formula14.

  all : ProveCCA2.
  ProveListFresh; try lia; constructor.

  apply PairLen.
  - apply PairLen.
    + reflexivity.
    + apply ComkLen.
  - reflexivity.
Qed.



(* formula 14 on page 40  *)
Proposition prop26_formula14 :
  (fun c0 c1 => ((fun enco0 => (fun o1 o2 o3 =>
       [b0 c0; b1 c1; acc0 c0 c1 & acc1 c0 c1; bnlcheck c0 n0 (fΦΦ3 c0 c1); bnlcheck c1 n1 (fΦΦ3 c0 c1);
  ＜ ＜ e0 c0 c1 n0, e1 c0 c1 n1, dv (v1 c0 c1) (v2 c0 c1) (v3 c0 c1) (s26 c0 c1 (v3 c0 c1)) ＞,
  ＜ enco0, ⫠, Do o1 o2 o3 ＞ ＞]) (FGO1 c0 c1 enco0 ⫠) (FGO2 c0 c1 enco0 ⫠) (FGO3 c0 c1 enco0 ⫠)) (enco0 c0 c1 kc0))) (c0 lhs) (c1 lhs)
 ~
   (fun c0 c1 => ((fun enco0 => (fun o1 o2 o3 =>
       [b0 c0; b1 c1; acc0 c0 c1 & acc1 c0 c1; bnlcheck c0 n0 (fΦΦ3 c0 c1); bnlcheck c1 n1 (fΦΦ3 c0 c1);
  ＜ ＜ e0 c0 c1 n0, e1 c0 c1 n1, dv (v1 c0 c1) (v2 c0 c1) (v3 c0 c1) (s26 c0 c1 (v3 c0 c1)) ＞,
  ＜ enco0, ⫠, Do o1 o2 o3 ＞ ＞]) (FGO1 c0 c1 enco0 ⫠) (FGO2 c0 c1 enco0 ⫠) (FGO3 c0 c1 enco0 ⫠)) (enco0 c0 c1 kc0))) (c0 rhs) (c1 rhs).

Proof.
  intros.
(* we use prop26_lemma14_helper to change both sides from {Do FGO} to {FDO FIO} *)
  rewrite (prop26_lemma14_helper lhs).
  rewrite (prop26_lemma14_helper rhs).

(* we use commitment hidding *)
   apply (@CompHidEx (fun lx => let c0 := Nth 0 lx in let c1 := Nth 1 lx in
         [b0 c0; b1 c1; acc0 c0 c1 & acc1 c0 c1; bnlcheck c0 n0 (fΦΦ3 c0 c1); bnlcheck c1 n1 (fΦΦ3 c0 c1);
          ＜ ＜ e0 c0 c1 n0, e1 c0 c1 n1, dv (v1 c0 c1) (v2 c0 c1) (v3 c0 c1) (s26 c0 c1 (v3 c0 c1)) ＞,
             ＜ enco0 c0 c1 kc0', ⫠, FDO (FIO1 c0 c1 (enco0 c0 c1 kc0')) (FIO2 c0 c1 (enco0 c0 c1 kc0')) (FIO3 c0 c1 (enco0 c0 c1 kc0')) ＞ ＞])
                     vot0 vot1 0 1).
  apply voteLen.
  lia.
  1, 3: ProveFresh.
  apply Freshc_kc0_Lemma26_14.
  apply Freshc_kc1_Lemma26_14.
Qed.

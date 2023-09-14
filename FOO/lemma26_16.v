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


(*  *)


(**)
Proposition prop26_formula16_isinkc_TRue: forall s,
  (fun c0 c1 =>
     isinkc kc0 kc1 (＜ π2 (π1 (FGO1 c0 c1 ⫠ ⫠)), π2 (π1 (FGO2 c0 c1 ⫠ ⫠)), π2 (π1 (FGO3 c0 c1 ⫠ ⫠)) ＞) = TRue) (c0 s) (c1 s).
Proof.
  intros.
  unfold isinkc.
  assert (isin kc0 (＜ π2 (π1 FGO1 (c0 s) (c1 s) ⫠ ⫠), π2 (π1 FGO2 (c0 s) (c1 s) ⫠ ⫠), π2 (π1 FGO3 (c0 s) (c1 s) ⫠ ⫠) ＞) = FAlse).
    unfold isin.
    rewrite Tau1Tri, Tau2Tri, Tau3Tri.
    rewrite Freshkc0FGO1_16, Freshkc0FGO2_16, Freshkc0FGO3_16.
    repeat rewrite If_false.
    reflexivity.
  assert (isin kc1 (＜ π2 (π1 FGO1 (c0 s) (c1 s) ⫠ ⫠), π2 (π1 FGO2 (c0 s) (c1 s) ⫠ ⫠), π2 (π1 FGO3 (c0 s) (c1 s) ⫠ ⫠) ＞) = FAlse).
    unfold isin.
    rewrite Tau1Tri, Tau2Tri, Tau3Tri.
    rewrite Freshkc1FGO1_16, Freshkc1FGO2_16, Freshkc1FGO3_16.
    repeat rewrite If_false.
    reflexivity.
  rewrite H. clear H.
  rewrite H0. clear H0.
  repeat rewrite If_false.
  reflexivity.
Qed.


(* When both encryptions are bot, neither isinkc0 nor isinkc1 will success,
   so using prop11, we can get rid of those process checks to reduce Do to FDO *)

Proposition prop26_formula16_Do_FDO : forall s,
  (fun c0 c1 =>
     [b0 c0; b1 c1; acc0 c0 c1 & acc1 c0 c1;
     bnlcheck c0 n0 (fΦΦ3 c0 c1); bnlcheck c1 n1 (fΦΦ3 c0 c1);
  ＜ ＜ e0 c0 c1 n0, e1 c0 c1 n1, dv (v1 c0 c1) (v2 c0 c1) (v3 c0 c1) (s26 c0 c1 (v3 c0 c1)) ＞,
     ＜ ⫠, ⫠, Do (FGO1 c0 c1 ⫠ ⫠) (FGO2 c0 c1 ⫠ ⫠) (FGO3 c0 c1 ⫠ ⫠) ＞ ＞]) (c0 s) (c1 s)
 ~
   (fun c0 c1 =>
      [b0 c0; b1 c1; acc0 c0 c1 & acc1 c0 c1;
      bnlcheck c0 n0 (fΦΦ3 c0 c1); bnlcheck c1 n1 (fΦΦ3 c0 c1);
  ＜ ＜ e0 c0 c1 n0, e1 c0 c1 n1, dv (v1 c0 c1) (v2 c0 c1) (v3 c0 c1) (s26 c0 c1 (v3 c0 c1)) ＞,
     ＜ ⫠, ⫠, FDO (FGO1 c0 c1 ⫠ ⫠) (FGO2 c0 c1 ⫠ ⫠) (FGO3 c0 c1 ⫠ ⫠) ＞ ＞]) (c0 s) (c1 s).
Proof.
  intros.
  simpl.
  unfold Do.
  rewrite (prop26_formula16_isinkc_TRue s).
  repeat rewrite <- If_tf.
  reflexivity.
  unfold pchko. Provebool.
Qed.


(* formula 16 on page 40  *)
Proposition prop26_formula16 :
  (fun c0 c1 =>
     [b0 c0; b1 c1; acc0 c0 c1 & acc1 c0 c1;
     bnlcheck c0 n0 (fΦΦ3 c0 c1); bnlcheck c1 n1 (fΦΦ3 c0 c1);
  ＜ ＜ e0 c0 c1 n0, e1 c0 c1 n1, dv (v1 c0 c1) (v2 c0 c1) (v3 c0 c1) (s26 c0 c1 (v3 c0 c1)) ＞,
     ＜ ⫠, ⫠, Do (FGO1 c0 c1 ⫠ ⫠) (FGO2 c0 c1 ⫠ ⫠) (FGO3 c0 c1 ⫠ ⫠) ＞ ＞]) (c0 lhs) (c1 lhs)
 ~
   (fun c0 c1 =>
      [b0 c0; b1 c1; acc0 c0 c1 & acc1 c0 c1;
      bnlcheck c0 n0 (fΦΦ3 c0 c1); bnlcheck c1 n1 (fΦΦ3 c0 c1);
  ＜ ＜ e0 c0 c1 n0, e1 c0 c1 n1, dv (v1 c0 c1) (v2 c0 c1) (v3 c0 c1) (s26 c0 c1 (v3 c0 c1)) ＞,
     ＜ ⫠, ⫠, Do (FGO1 c0 c1 ⫠ ⫠) (FGO2 c0 c1 ⫠ ⫠) (FGO3 c0 c1 ⫠ ⫠) ＞ ＞]) (c0 rhs) (c1 rhs).
Proof.
  intros. simpl.

(* First we need to get rid of the "isinkc" check in Do, namely change Do to FDO*)
  rewrite (prop26_formula16_Do_FDO lhs).
  rewrite (prop26_formula16_Do_FDO rhs).


(* use commitment hidding *)
  apply (@CompHidEx (fun lx => let c0 := Nth 0 lx in let c1 := Nth 1 lx in
         [b0 c0; b1 c1; acc0 c0 c1 & acc1 c0 c1; bnlcheck c0 n0 (fΦΦ3 c0 c1); bnlcheck c1 n1 (fΦΦ3 c0 c1);
          ＜ ＜ e0 c0 c1 n0, e1 c0 c1 n1, dv (v1 c0 c1) (v2 c0 c1) (v3 c0 c1) (s26 c0 c1 (v3 c0 c1)) ＞,
             ＜ ⫠, ⫠, FDO (FGO1 c0 c1 ⫠ ⫠) (FGO2 c0 c1 ⫠ ⫠) (FGO3 c0 c1 ⫠ ⫠) ＞ ＞])
                     vot0 vot1 0 1).
  apply voteLen. lia.
  1, 3: ProveFresh.
  apply Freshc_kc0_Lemma26_16.
  apply Freshc_kc1_Lemma26_16.
Qed.

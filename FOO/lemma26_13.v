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




(* The actual statement of formula 13 of Lemma26 is at the end.
   Generally speaking, the proof is divided into three parts:
   (1). In part One, we use CCA2 to swap the messages encrypted in the voting phase on the right hand side
   (2). In part Two, we use CCA2 to swap the messages encrypted in the opening phase on the right hand side
   (3). In part Three, we use Blindness and funcapp to swap the commitments in the blinding phase on the right hand side
  Finally we will combine those three parts together *)


(*--------------------------------------------------*)
(*---  Part One: A                               ---*)
(*--------------------------------------------------*)



(*  *)


(* In the following lemma, we show that "dv S26" and "dvS26" are equal if x0 and x1 are the
msg lhs and msg rhs or vice versa. This is because of the checks in dv that make sure that
 they either both appear or they both do not appear. *)


Lemma lemma26_13_dv_dvS26:
  forall msg0 msg1 c0 c1,
    ( msg0 = (m0 c0 c1 n0) /\  msg1 = (m1 c0 c1 n1))
    \/
    ( msg0 = (m1 c0 c1 n1) /\  msg1 = (m0 c0 c1 n0)) ->
    let x0 := (encS msg0 rd0) in
    let x1 := (encS msg1 rd1) in
    (fun v1 v2 v3 =>
       dv v1 v2 v3 (S26 c0 c1 x0 x1 v3)
    ) (V1 c0 c1 x0 x1) (V2 c0 c1 x0 x1) (V3 c0 c1 x0 x1)
    =
    (fun v3
     => dvS26 c0 c1 x0 x1 v3
    ) (V3 c0 c1 x0 x1).
Proof.
{ intros.
  simpl.
  (**)
  rewrite <-(@If_same ((τ1 (FΦΦ2 c0 c1 x0 x1)) ≟ x1)) at 1.
  unfold V1.
  rewrite (decGame (msg1) 8 (τ1 (FΦΦ2 c0 c1 x0 x1))).
  unfold S26.
  rewrite (@If_eval (fun tau1 => dv (If  tau1 Then _ Else _) _ _ (If _ &  tau1 Then _ Else ⫠))
                    (fun  tau1 => dv (If  tau1 Then _ Else _) _ _ (If _ &  tau1 Then _ Else ⫠))).
  rewrite <- If_tf, If_same, If_true.
  repeat rewrite If_false.
  unfold dv at 2. rewrite If_same.
  (**)
  rewrite <-(@If_same ((τ2 (FΦΦ2 c0 c1 x0 x1)) ≟ x0)) at 1.
  unfold V2.
  rewrite (decGame (msg0) 7 (τ2 (FΦΦ2 c0 c1 x0 x1))).
  rewrite (@If_eval (fun  tau2 => If _ Then dv _ (If tau2 Then _ Else _) _ (If tau2 Then _ Else ⫠) Else _)
                    (fun tau2 => If _ Then dv _ (If tau2 Then _ Else _) _ (If tau2 Then _ Else ⫠) Else _)).
  repeat rewrite If_true, If_false.
  unfold dv at 2.
  rewrite If_same.
  rewrite If_same.
  (**)
  rewrite <-(@If_same ((τ3 (FΦΦ2 c0 c1 x0 x1)) ≟ x0)
                      (dv msg1 msg0 (V3 c0 c1 x0 x1) (shufl (pv1 c0 c1 n1) (pv0 c0 c1 n0) (π1 V3 c0 c1 x0 x1)))).
  unfold V3 at 1.
  rewrite (decGame (msg0) 7 (τ3 (FΦΦ2 c0 c1 x0 x1))) at 1.
  rewrite (@If_eval (fun tau3 => dv _ _ (If tau3 Then _ Else _) _)  (fun tau3 => _)).
  rewrite If_true.
  assert ( dv msg1 msg0 msg0 (shufl (pv1 c0 c1 n1) (pv0 c0 c1 n0) (π1 V3 c0 c1 x0 x1)) = ⫠).
    unfold dv, dist.
    rewrite ceqeq, If_true.
    repeat rewrite If_same.
    repeat rewrite If_false.
    reflexivity.
  rewrite H0; clear H0.

  (**)
  rewrite <-(@If_same ((τ3 (FΦΦ2 c0 c1 x0 x1)) ≟ x1)
                     (dv msg1 msg0 (V3 c0 c1 x0 x1) (shufl (pv1 c0 c1 n1) (pv0 c0 c1 n0) (π1 V3 c0 c1 x0 x1)))) .
  unfold V3 at 1. rewrite (decGame (msg1) 8 (τ3 (FΦΦ2 c0 c1 x0 x1))) at 1.
  rewrite (@If_eval (fun tau3 => dv _ _ (If tau3 Then _ Else _) _)  (fun tau3 => _)).
  rewrite If_true.
  assert (dv msg1 msg0 msg1 (shufl (pv1 c0 c1 n1) (pv0 c0 c1 n0) (π1 V3 c0 c1 x0 x1)) = ⫠).
    unfold dv, dist.
    rewrite ceqeq, If_true, If_false.
    repeat rewrite If_same.
    repeat rewrite If_false.
    reflexivity.
  rewrite H0; clear H0.

  (*  *)

(**)
  unfold dvS26.
  destruct H. destruct H. unfold x0, x1. rewrite H, H0.
  reflexivity.

  destruct H. unfold x0, x1. rewrite H, H0.
  rewrite dv_perm12, shufl_perm12.
  reflexivity.
  all: (time ProveboolandContext). (*1.623 secs  *) }
Qed.



(* In order to make the context CCA2 compliant,
   we have to transform the decryption to something like "If _ Then Error Else decrytion"
   When we use CCA2 to replace the plaintext from voter0, then we should use lemma26_13_CCA2Game1n_x0
   when from voter1 we should use lemma26_13_CCA2Game1n_x1 *)

Lemma lemma26_13_CCA2Game1n_x0: forall c0 c1 x0 x1 ,
  (fun v3 => dvS26 c0 c1 x0 x1 v3) (V3 c0 c1 x0 x1)
 =
  (fun v3 => dvS26 c0 c1 x0 x1 v3) (fiv3 c0 c1 x0 x1).
Proof.
{ intros. simpl.
  unfold dvS26. unfold fiv3.
  rewrite (@If_eval (fun _ => _) (fun tau3 => If _ Then ⫠ Else dv _ _ (If tau3 Then _ Else _ ) (shufl _ _ (π1 (If tau3 Then Error Else _))))).
  repeat rewrite If_false.
  reflexivity. ProveContext. ProveContext.
  all : (time ProveboolandContext). (* 0.334 secs *) }
Qed.



(**)
Lemma lemma26_13_CCA2Game1n_x1: forall c0 c1 x0 x1 ,
  (fun v3 => dvS26 c0 c1 x0 x1 v3)  (V3 c0 c1 x0 x1)
 =
  (fun v3 => dvS26 c0 c1 x0 x1 v3)  (giv3 c0 c1 x0 x1).
Proof.
{ intros. simpl.
  unfold dvS26. unfold giv3.
  rewrite (@If_eval (fun _ => _) (fun tau3 => dv _ _ (If tau3 Then _ Else _ ) (shufl _ _ (π1 (If tau3 Then Error Else _))))).
  repeat rewrite If_false.
  reflexivity.
  all : (time ProveboolandContext). (* 0.303 secs *) }
Qed.






(*--------------------------------------------------*)
(*---  Part One: B :                             ---*)
(*--------------------------------------------------*)

(* after we change (dv s) to the form suitable for CCA2 using game1, we should also change the format of decryptions in the opening phase. *)

Lemma lemma26_13_CCA2Game2n_x0:
  forall c0 c1 x0 dvs,
    ContextTerm General Term (fun b3 : ppt => dvs) ->
    (x0 = (e0 (c0) (c1) n0) \/ x0 = (encS (m1 (c0) (c1) n1) rd0)) ->
    (fun x1 =>
       (fun o1 o2 o3 =>
          Do o1 o2 o3
       ) (O1 c0 c1 x0 x1 dvs) (O2 c0 c1 x0 x1 dvs) (O3 c0 c1 x0 x1 dvs)
    ) (e1 c0 c1 n1)
=
    (fun x1 =>
       (fun o1 o2 o3 =>
          Do o1 o2 o3
       ) (fiO1 (m0 c0 c1 n0) c0 c1 x0 x1 dvs) (fiO2 (m0 c0 c1 n0) c0 c1 x0 x1 dvs) (fiO3 (m0 c0 c1 n0) c0 c1 x0 x1 dvs)
    ) (e1 c0 c1 n1).
Proof.
{ intros. simpl.
  destruct H0; rewrite H0.

  (* when x = (e0 (c0 s) (c1 s) n0) we can use decGame *)
  unfold O1.
  rewrite (decGame (m0 (c0) (c1) n0) 7
                   (τ1 (fΦΦ5 c0 c1 (e0 (c0) (c1) n0) (e1 (c0) (c1) n1) dvs))).
  unfold O2.
  rewrite (decGame (m0 (c0) (c1) n0) 7
                   (τ2 (fΦΦ5 c0 c1 (e0 (c0) (c1) n0) (e1 (c0) (c1) n1) dvs))).
  unfold O3.
  rewrite (decGame (m0 (c0) (c1) n0) 7
                   (τ3 (fΦΦ5 c0 c1 (e0 (c0) (c1) n0) (e1 (c0) (c1) n1) dvs))).

  unfold fiO1, fiO2, fiO3. repeat rewrite decSimpl.
  reflexivity. all : Provebool.

  (* RHS *)
  unfold O1.
  rewrite (decGame (m1 (c0) (c1) n1) 7 (* should be 8 *)
                   (τ1 (fΦΦ5 c0 c1 (encS (m1 (c0) (c1) n1) rd0) (e1 (c0) (c1) n1) dvs ))).
  unfold O2.
  rewrite (decGame (m1 (c0) (c1) n1) 7
                   (τ2 (fΦΦ5 c0 c1 (encS (m1 (c0) (c1) n1) rd0) (e1 (c0) (c1) n1) dvs ))).
  unfold O3.
  rewrite (decGame (m1 (c0) (c1) n1) 7
                   (τ3 (fΦΦ5 c0 c1 (encS (m1 (c0) (c1) n1) rd0) (e1 (c0) (c1) n1) dvs ))).

  unfold Do.
  assert (forall b1 b2 b3 dec1 dec2 dec3 m, bppt b1 -> bppt b2 -> bppt b3 -> ((m = m0 (c0) (c1) n0) \/ (m = m1 (c0) (c1) n1)) ->
             pchko (＜ If b1 Then m Else dec1, If b2 Then m Else dec2,  If b3 Then m Else dec3 ＞)
           = If b1 Then FAlse Else If b2 Then FAlse Else If b3 Then FAlse Else (ph3 ≟ (π2 dec1)) & (ph3 ≟ (π2 dec2)) & (ph3 ≟ (π2 dec3))).
    intros.
    unfold pchko.
    rewrite Tau1Tri, Tau2Tri, Tau3Tri.
    repeat rewrite (@If_morph (fun x => (ph3 ≟ (π2 x)))).
    destruct H4; rewrite H4;
    unfold m0; unfold m1; repeat rewrite proj2pair;
    rewrite ph2Neqph3;
    rewrite AndGuard.
    reflexivity. auto. auto. auto. Provebool. Provebool. Provebool.
    1, 2, 3: ProveContext. reflexivity. Provebool. Provebool. Provebool. Provebool.
    ProveContext. ProveContext. ProveContext.
  (* When x = (e1 (c0 s) (c1 s) n1) we can use some equiv *)
  rewrite H1.

  rewrite (@If_morph (fun x => If _ & x & _ Then _ Else ⫠ )).
  rewrite If_false. rewrite If_same. rewrite If_false.
  rewrite (@If_eval (fun _ => _) (fun b1 => If dist (If b1 Then _ Else _) _ _ & _ &
                          isinkc kc0 kc1 (＜ π2 (π1 (If b1 Then _ Else  _)),  π2 (π1 _), π2 (π1 _) ＞)
                       Then shufl (π1 (If b1 Then _ Else  _)) (π1 _) (π1 _) Else ⫠ )).
  rewrite If_false.

  rewrite (@If_morph (fun x => If _ & x & _ Then _ Else ⫠ )).
  rewrite If_false. rewrite If_same. rewrite If_false.
  rewrite (@If_eval (fun _ => _) (fun b2 => If dist _ (If b2 Then _ Else _) _ & _ &
                          isinkc kc0 kc1 (＜ _ , π2 (π1 (If b2 Then _ Else  _)) , _ ＞)
                       Then shufl _ (π1 (If b2 Then _ Else  _)) _ Else ⫠ )).
  rewrite If_false.

  rewrite (@If_morph (fun x => If _ & x & _ Then _ Else ⫠ )).
  rewrite If_false. rewrite If_same. rewrite If_false.
  rewrite (@If_eval (fun _ => _) (fun b3 => If dist _ _ (If b3 Then _ Else _) & _ &
                          isinkc kc0 kc1 (＜ _ , _ , π2 (π1 (If b3 Then _ Else  _)) ＞)
                       Then shufl _ _ (π1 (If b3 Then _ Else _ )) Else ⫠ )).
  rewrite If_false.

  unfold fiO1, fiO2, fiO3. repeat rewrite decSimpl.

  rewrite H1.

  rewrite (@If_morph (fun x => If dist _ _ _ & x & _ Then _ Else ⫠ )
                     ((τ1 (fΦΦ5 c0 c1 (encS (m1 (c0) (c1) n1) rd0) (e1 (c0) (c1) n1) dvs)) ≟ (encS (m1 (c0) (c1) n1) rd0) )).
  rewrite If_false. rewrite If_same. rewrite If_false.
  rewrite (@If_eval (fun _ => _) (fun b1 => If dist (If b1 Then _ Else _) _ _ & _ &
                          isinkc kc0 kc1 (＜ π2 (π1 (If b1 Then _ Else  _)),  π2 (π1 _), π2 (π1 _) ＞)
                       Then shufl (π1 (If b1 Then _ Else  _)) (π1 _) (π1 _) Else ⫠ )).
  rewrite If_false.

  rewrite (@If_morph (fun x => If _ & x & _ Then _ Else ⫠ )
                     ((τ2 (fΦΦ5 c0 c1 (encS (m1 (c0) (c1) n1) rd0) (e1 (c0) (c1) n1) dvs)) ≟ (encS (m1 (c0) (c1) n1) rd0)) ).
  rewrite If_false. rewrite If_same. rewrite If_false.
  rewrite (@If_eval (fun _ => _) (fun b2 => If dist _ (If b2 Then _ Else _) _ & _ &
                          isinkc kc0 kc1 (＜ _ , π2 (π1 (If b2 Then _ Else  _)) , _ ＞)
                       Then shufl _ (π1 (If b2 Then _ Else  _)) _ Else ⫠ )).
  rewrite If_false.

  rewrite (@If_morph (fun x => If _ & x & _ Then _ Else ⫠ )
                     (τ3 (fΦΦ5 c0 c1 (encS (m1 c0 c1 n1) rd0) (e1 c0 c1 n1) dvs) ≟ encS (m1 c0 c1 n1) rd0)).
  rewrite If_false. rewrite If_same. rewrite If_false.
  rewrite (@If_eval (fun _ => _) (fun b3 => If dist _ _ (If b3 Then _ Else _) & _ &
                          isinkc kc0 kc1 (＜ _ , _ , π2 (π1 (If b3 Then _ Else  _)) ＞)
                       Then shufl _ _ (π1 (If b3 Then _ Else _ )) Else ⫠ )).
  rewrite If_false.

  reflexivity. ProveContext.

 all : pose (lemma26_13_part1_Φ5_Context c0 c1 dvs H); time ProveboolandContext. (* 16.637 secs  *)
  left; auto.
  right; auto. }
Qed.




(* *)

Lemma lemma26_13_CCA2Game2n_x1:
  forall c0 c1 x1 dvs,
    ContextTerm General Term (fun _ => dvs) ->
    (x1 = (encS (m0 c0 c1 n0) rd1) \/ x1 = (e1 c0 c1 n1)) ->
    (fun x0 =>
       (fun o1 o2 o3 =>
          Do o1 o2 o3
       ) (O1 c0 c1 x0 x1 dvs) (O2 c0 c1 x0 x1 dvs) (O3 c0 c1 x0 x1 dvs)
    ) (encS (m1 c0 c1 n1) rd0)
 =
    (fun x0 =>
       (fun o1 o2 o3 =>
          Do o1 o2 o3
       ) (giO1 (m0 c0 c1 n0) c0 c1 x0 x1 dvs) (giO2 (m0 c0 c1 n0) c0 c1 x0 x1 dvs) (giO3 (m0 c0 c1 n0) c0 c1 x0 x1 dvs)
    ) (encS (m1 c0 c1 n1) rd0).
Proof.
{ intros. simpl.
  destruct H0; rewrite H0.

  (* when x = (e0 (c0 s) (c1 s) n0) we can use decGame *)
  unfold O1.
   rewrite (decGame (m0 c0 c1 n0) 8
                   (τ1 (fΦΦ5 c0 c1 (encS (m1 c0 c1 n1) rd0) (encS (m0 c0 c1 n0) rd1) dvs))).
  unfold O2.
  rewrite (decGame (m0 c0 c1 n0) 8
                   (τ2 (fΦΦ5 c0 c1 (encS (m1 c0 c1 n1) rd0) (encS (m0 c0 c1 n0) rd1) dvs))).
  unfold O3.
  rewrite (decGame (m0 c0 c1 n0) 8
                   (τ3 (fΦΦ5 c0 c1 (encS (m1 c0 c1 n1) rd0) (encS (m0 c0 c1 n0) rd1) dvs))).

  unfold giO1, giO2, giO3. repeat rewrite decSimpl.
  reflexivity.
 all : Provebool.
  (* RHS *)
  unfold O1.
  rewrite (decGame (m1 c0 c1 n1) 8 (* should be 8 *)
                   (τ1 (fΦΦ5 c0 c1 (encS (m1 c0 c1 n1) rd0) (e1 c0 c1 n1) dvs))).
  unfold O2.
  rewrite (decGame (m1 c0 c1 n1) 8
                   (τ2 (fΦΦ5 c0 c1 (encS (m1 c0 c1 n1) rd0) (e1 c0 c1 n1) dvs))).
  unfold O3.
  rewrite (decGame (m1 c0 c1 n1) 8
                   (τ3 (fΦΦ5 c0 c1 (encS (m1 c0 c1 n1) rd0) (e1 c0 c1 n1) dvs))).

  unfold Do.
  assert (forall b1 b2 b3 dec1 dec2 dec3 m, bppt b1 -> bppt b2 -> bppt b3 -> ((m = m0 c0 c1 n0) \/ (m = m1 c0 c1 n1)) ->
             pchko (＜ If b1 Then m Else dec1, If b2 Then m Else dec2,  If b3 Then m Else dec3 ＞)
           = If b1 Then FAlse Else If b2 Then FAlse Else If b3 Then FAlse Else (ph3 ≟ (π2 dec1)) & (ph3 ≟ (π2 dec2)) & (ph3 ≟ (π2 dec3))).
    intros.
    unfold pchko.
    rewrite Tau1Tri, Tau2Tri, Tau3Tri.
    repeat rewrite (@If_morph (fun x => (ph3 ≟ (π2 x)))).
    destruct H4; rewrite H4;
    unfold m0; unfold m1; repeat rewrite proj2pair;
    rewrite ph2Neqph3;
    rewrite AndGuard. Provebool;
    reflexivity. all: Provebool.
  1, 2, 3: ProveContext. reflexivity. ProveContext.
  (* When x = (e1 c10 c11 n1) we can use some equiv *)
  rewrite H1.

  rewrite (@If_morph (fun x => If _ & x & _ Then _ Else ⫠ )).
  rewrite If_false. rewrite If_same. rewrite If_false.
  rewrite (@If_eval (fun _ => _) (fun b1 => If dist (If b1 Then _ Else _) _ _ & _ &
                          isinkc kc0 kc1 (＜ π2 (π1 (If b1 Then _ Else  _)),  π2 (π1 _), π2 (π1 _) ＞)
                       Then shufl (π1 (If b1 Then _ Else  _)) (π1 _) (π1 _) Else ⫠ )).
  rewrite If_false.

  rewrite (@If_morph (fun x => If _ & x & _ Then _ Else ⫠ )).
  rewrite If_false. rewrite If_same. rewrite If_false.
  rewrite (@If_eval (fun _ => _) (fun b2 => If dist _ (If b2 Then _ Else _) _ & _ &
                          isinkc kc0 kc1 (＜ _ , π2 (π1 (If b2 Then _ Else  _)) , _ ＞)
                       Then shufl _ (π1 (If b2 Then _ Else  _)) _ Else ⫠ )).
  rewrite If_false.

  rewrite (@If_morph (fun x => If _ & x & _ Then _ Else ⫠ )).
  rewrite If_false. rewrite If_same. rewrite If_false.
  rewrite (@If_eval (fun _ => _) (fun b3 => If dist _ _ (If b3 Then _ Else _) & _ &
                          isinkc kc0 kc1 (＜ _ , _ , π2 (π1 (If b3 Then _ Else  _)) ＞)
                       Then shufl _ _ (π1 (If b3 Then _ Else _ )) Else ⫠ )).
  rewrite If_false.

  unfold giO1, giO2, giO3. repeat rewrite decSimpl.

  rewrite H1.

  rewrite (@If_morph (fun x => If dist _ _ _ & x & _ Then _ Else ⫠ )
                     (τ1 (fΦΦ5 c0 c1 (encS (m1 c0 c1 n1) rd0) (e1 c0 c1 n1) dvs) ≟ e1 c0 c1 n1)).
  rewrite If_false. rewrite If_same. rewrite If_false.
  rewrite (@If_eval (fun _ => _) (fun b1 => If dist (If b1 Then _ Else _) _ _ & _ &
                          isinkc kc0 kc1 (＜ π2 (π1 (If b1 Then _ Else  _)),  π2 (π1 _), π2 (π1 _) ＞)
                       Then shufl (π1 (If b1 Then _ Else  _)) (π1 _) (π1 _) Else ⫠ )).
  rewrite If_false.

  rewrite (@If_morph (fun x => If _ & x & _ Then _ Else ⫠ )
                     (τ2 (fΦΦ5 c0 c1 (encS (m1 c0 c1 n1) rd0) (e1 c0 c1 n1) dvs) ≟ e1 c0 c1 n1) ).
  rewrite If_false. rewrite If_same. rewrite If_false.
  rewrite (@If_eval (fun _ => _) (fun b2 => If dist _ (If b2 Then _ Else _) _ & _ &
                          isinkc kc0 kc1 (＜ _ , π2 (π1 (If b2 Then _ Else  _)) , _ ＞)
                       Then shufl _ (π1 (If b2 Then _ Else  _)) _ Else ⫠ )).
  rewrite If_false.

  rewrite (@If_morph (fun x => If _ & x & _ Then _ Else ⫠ )
                     (τ3 (fΦΦ5 c0 c1 (encS (m1 c0 c1 n1) rd0) (e1 c0 c1 n1) dvs) ≟ e1 c0 c1 n1)).
  rewrite If_false. rewrite If_same. rewrite If_false.
  rewrite (@If_eval (fun _ => _) (fun b3 => If dist _ _ (If b3 Then _ Else _) & _ &
                          isinkc kc0 kc1 (＜ _ , _ , π2 (π1 (If b3 Then _ Else  _)) ＞)
                       Then shufl _ _ (π1 (If b3 Then _ Else _ )) Else ⫠ )).
  rewrite If_false.

  reflexivity.


  all : pose (lemma26_13_part1_Φ5_Context c0 c1 dvs H); time ProveboolandContext. (*16.479 secs *)
  left; auto.
  right; auto. }
Qed.




(*--------------------------------------------------*)
(*---  Part One: Final                           ---*)
(*--------------------------------------------------*)


(*  *)

(* we use CCA2 to swap the (m0 c10 c11 n0) to (m1 c10 c11 n1) *)

Proposition prop26_13_swap_m0_m1 :
  (fun x0 x1 =>
     (fun v1 v2 v3 =>
        (fun dvs =>
           [b0 c10; b1 c11; (acc0 c10 c11) & (acc1 c10 c11);
           (acc0 c10 c11) & (acc1 c10 c11) & (bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs)) & (bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs));
           If (acc0 c10 c11 & acc1 c10 c11) & (bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs)) & (bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs))
              Then ( ＜ ＜ x0, x1, dvs ＞,
                     ＜ (Enco0 c10 c11 x0 x1 dvs), (Enco1 c10 c11 x0 x1 dvs), Do (O1 c10 c11 x0 x1 dvs) (O2 c10 c11 x0 x1 dvs) (O3 c10 c11 x0 x1 dvs)＞ ＞)
              Else ⫠]
        ) (dv v1 v2 v3 (S26 c10 c11 x0 x1 v3))
     ) (V1 c10 c11 x0 x1) (V2 c10 c11 x0 x1) (V3 c10 c11 x0 x1)
   ) (encS (msg voter0 c10 c11) rd0) (encS (msg voter1 c10 c11) rd1)
   ~
   (fun x0 x1 =>
      (fun v1 v2 v3 =>
         (fun dvs =>
            [b0 c10; b1 c11; (acc0 c10 c11) & (acc1 c10 c11);
            (acc0 c10 c11) & (acc1 c10 c11) & (bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs)) & (bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs));
            If (acc0 c10 c11 & acc1 c10 c11) & (bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs)) & (bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs))
               Then ( ＜ ＜ x0, x1, dvs ＞,
                      ＜ (Enco0 c10 c11 x0 x1 dvs), (Enco1 c10 c11 x0 x1 dvs), Do (O1 c10 c11 x0 x1 dvs) (O2 c10 c11 x0 x1 dvs) (O3 c10 c11 x0 x1 dvs)＞ ＞)
               Else ⫠]
         ) (dv v1 v2 v3 (S26 c10 c11 x0 x1 v3))
      ) (V1 c10 c11 x0 x1) (V2 c10 c11 x0 x1) (V3 c10 c11 x0 x1)
   )  (encS (msg voter1 c10 c11) rd0) (encS (msg voter0 c10 c11) rd1).
Proof.
(* Here using prop25_CCA2Game1n and prop25_CCA2Game2n rewrite the terms so that CCA2 is applicable.  Then using CCA2, replace the nonce. *)
{ intros. unfold msg. simpl.

(*  −- CCA2 compliant. pkS := nonce 6, rd0 := nonce 7 *)
  rewrite (lemma26_13_CCA2Game2n_x0 c10 c11 (encS (m0 c10 c11 n0) rd0)).
  rewrite (lemma26_13_dv_dvS26 (m0 c10 c11 n0) (m1 c10 c11 n1)) at 1 2 3 4 5 6 7 8 9 10. (*1.8 secs*)
  repeat rewrite (lemma26_13_CCA2Game1n_x0).

assert (
      (fun x0 =>
             (fun x1 =>
                (fun dvs =>
                   [b0 c10; b1 c11;  acc0 c10 c11 & acc1 c10 c11;
                    acc0 c10 c11 & acc1 c10 c11 & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs);
                    If ((acc0 c10 c11 & acc1 c10 c11) & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs))
                      Then (＜ ＜ x0 , x1 , dvs ＞,
                        ＜ Enco0 c10 c11 x0 x1 dvs, Enco1 c10 c11 x0 x1 dvs,
                        Do (fiO1 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) (fiO2 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) (fiO3 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) ＞ ＞)
                      Else ⫠]
                ) (dvS26 c10 c11 x0 x1 (fiv3 c10 c11 x0 x1))
             ) (e1 c10 c11 n1)
          ) (encS (m0 c10 c11 n0) rd0)
      =
        (fun x0 =>
             (fun x1 =>
                (fun dvs =>
                   [b0 c10; b1 c11;  acc0 c10 c11 & acc1 c10 c11;
                    acc0 c10 c11 & acc1 c10 c11 & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs);
                    If ((acc0 c10 c11 & acc1 c10 c11) & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs))
                      Then (＜ ＜ x0 , x1 , dvs ＞,
                        ＜ Enco0 c10 c11 x0 x1 dvs, Enco1 c10 c11 x0 x1 dvs,
                        Do (fiO1 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) (fiO2 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) (fiO3 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) ＞ ＞)
                      Else ⫠]
                ) (dvS26 c10 c11 x0 x1 (fiv3 c10 c11 x0 x1))
             ) (e1 c10 c11 n1)
          ) (encS  (＜ ＜ c10, (If (acc0 c10 c11 & acc1 c10 c11) Then (ub c10 t bn0 (ti0 c10 c11)) Else ⫠ ) , n0 ＞, ph2 ＞) rd0)
    ). 
{
  repeat rewrite (UnfoldAnd (acc0 c10 c11 & acc1 c10 c11)).
  rewrite (@If_eval (fun acc => (fun x0 =>
             (fun x1 =>
                (fun dvs => 
                   If (bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs)) & (bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs))
                      Then (＜ ＜ x0 , x1 , dvs ＞,
                        ＜ Enco0 c10 c11 x0 x1 dvs, Enco1 c10 c11 x0 x1 dvs,
                        Do (fiO1 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) (fiO2 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) (fiO3 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) ＞ ＞)
                      Else ⫠
                ) (dvS26 c10 c11 x0 x1 (fiv3 c10 c11 x0 x1))
             ) (e1 c10 c11 n1)
          ) (encS  (＜ ＜ c10, (If acc Then _ Else ⫠ ) , n0 ＞, ph2 ＞) rd0)) (fun _ => _) (acc0 c10 c11 & acc1 c10 c11)). rewrite If_true.
  
  repeat rewrite <- AndAssoc with (A := acc0 c10 c11).
  rewrite (@If_eval (fun acc => bnlcheck _ _
    (FΦΦ3 _ _ (encS (＜ ＜ _, If acc Then _ Else ⫠, _ ＞, ph2 ＞) _) _
       (dvS26 _ _ (encS (＜ ＜ _, If acc Then _ Else ⫠, _ ＞, ph2 ＞) _) _
          (fiv3 c10 c11 (encS (＜ ＜ _, If acc Then _ Else ⫠, _ ＞, ph2 ＞) _) _))) &
  bnlcheck _ _
    (FΦΦ3 _ _ (encS (＜ ＜ _, If acc Then _ Else ⫠, _ ＞, ph2 ＞) _) _
       (dvS26 _ _ (encS (＜ ＜ _, If acc Then _ Else ⫠, _ ＞, ph2 ＞) _) _
          (fiv3 _ _ (encS (＜ ＜ _, If acc Then _ Else ⫠, _ ＞, ph2 ＞) _) _)))) (fun _ => _) (acc0 c10 c11 & acc1 c10 c11)). rewrite If_true.
  reflexivity.
  
  time (pose prop26_13_swap_m0_m1_cnxt1;
  pose prop26_13_swap_m0_m1_cnxt2; ProveContext). (*2.424 secs*) 
  1, 4: ProveContext.
  1, 3: unfold acc0; unfold acc1; Provebool.
  time (pose prop26_13_swap_m0_m1_cnxt1;
  pose prop26_13_swap_m0_m1_cnxt2; ProveContext). (*15.711 secs*)
}
  simpl in H. unfold e1. unfold e1 in H.
  rewrite H. clear H.





  pose (cca2
          [nonce 6]
          [nonce 7]
          (fun x0 =>
             (fun x1 =>
                (fun dvs =>
                   [b0 c10; b1 c11;  acc0 c10 c11 & acc1 c10 c11;
                    acc0 c10 c11 & acc1 c10 c11 & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs);
                    If ((acc0 c10 c11 & acc1 c10 c11) & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs))
                      Then (＜ ＜ x0 , x1 , dvs ＞,
                        ＜ Enco0 c10 c11 x0 x1 dvs, Enco1 c10 c11 x0 x1 dvs,
                        Do (fiO1 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) (fiO2 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) (fiO3 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) ＞ ＞)
                      Else ⫠]
                ) (dvS26 c10 c11 x0 x1 (fiv3 c10 c11 x0 x1))
             ) (e1 c10 c11 n1)
          )
          (＜ ＜ c10, (If (acc0 c10 c11 & acc1 c10 c11) Then (ub c10 t bn0 (ti0 c10 c11)) Else ⫠ ) , n0 ＞, ph2 ＞)
          (＜ ＜ c11, (If (acc0 c10 c11 & acc1 c10 c11) Then (ub c11 t bn1 (ti1 c10 c11)) Else ⫠ ) , n1 ＞, ph2 ＞)
       )
    as claim0. simpl in claim0.
  rewrite claim0. clear claim0.


assert (
      (fun x0 =>
             (fun x1 =>
                (fun dvs =>
                   [b0 c10; b1 c11;  acc0 c10 c11 & acc1 c10 c11;
                    acc0 c10 c11 & acc1 c10 c11 & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs);
                    If ((acc0 c10 c11 & acc1 c10 c11) & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs))
                      Then (＜ ＜ x0 , x1 , dvs ＞,
                        ＜ Enco0 c10 c11 x0 x1 dvs, Enco1 c10 c11 x0 x1 dvs,
                        Do (fiO1 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) (fiO2 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) (fiO3 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) ＞ ＞)
                      Else ⫠]
                ) (dvS26 c10 c11 x0 x1 (fiv3 c10 c11 x0 x1))
             ) (e1 c10 c11 n1)
          ) (encS (＜ ＜ c11, (If (acc0 c10 c11 & acc1 c10 c11) Then (ub c11 t bn1 (ti1 c10 c11)) Else ⫠ ) , n1 ＞, ph2 ＞) rd0)
      =
        (fun x0 =>
             (fun x1 =>
                (fun dvs =>
                   [b0 c10; b1 c11;  acc0 c10 c11 & acc1 c10 c11;
                    acc0 c10 c11 & acc1 c10 c11 & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs);
                    If ((acc0 c10 c11 & acc1 c10 c11) & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs))
                      Then (＜ ＜ x0 , x1 , dvs ＞,
                        ＜ Enco0 c10 c11 x0 x1 dvs, Enco1 c10 c11 x0 x1 dvs,
                        Do (fiO1 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) (fiO2 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) (fiO3 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) ＞ ＞)
                      Else ⫠]
                ) (dvS26 c10 c11 x0 x1 (fiv3 c10 c11 x0 x1))
             ) (e1 c10 c11 n1)
          ) (encS  (m1 c10 c11 n1) rd0)
  ).
   
{
  repeat rewrite (UnfoldAnd (acc0 c10 c11 & acc1 c10 c11)).
  rewrite (@If_eval (fun acc => (fun x0 =>
             (fun x1 =>
                (fun dvs => 
                   If (bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs)) & (bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs))
                      Then (＜ ＜ x0 , x1 , dvs ＞,
                        ＜ Enco0 c10 c11 x0 x1 dvs, Enco1 c10 c11 x0 x1 dvs,
                        Do (fiO1 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) (fiO2 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) (fiO3 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) ＞ ＞)
                      Else ⫠
                ) (dvS26 c10 c11 x0 x1 (fiv3 c10 c11 x0 x1))
             ) (e1 c10 c11 n1)
          ) (encS  (＜ ＜ c11, (If acc Then _ Else ⫠ ) , _ ＞, ph2 ＞) _)) (fun _ => _) (acc0 c10 c11 & acc1 c10 c11)). rewrite If_true.
  
  repeat rewrite <- AndAssoc with (A := acc0 c10 c11).
  rewrite (@If_eval (fun acc => bnlcheck _ _
    (FΦΦ3 _ _ (encS (＜ ＜ _, If acc Then _ Else ⫠, _ ＞, ph2 ＞) _) _
       (dvS26 _ _ (encS (＜ ＜ _, If acc Then _ Else ⫠, _ ＞, ph2 ＞) _) _
          (fiv3 c10 c11 (encS (＜ ＜ _, If acc Then _ Else ⫠, _ ＞, ph2 ＞) _) _))) &
  bnlcheck _ _
    (FΦΦ3 _ _ (encS (＜ ＜ _, If acc Then _ Else ⫠, _ ＞, ph2 ＞) _) _
       (dvS26 _ _ (encS (＜ ＜ _, If acc Then _ Else ⫠, _ ＞, ph2 ＞) _) _
          (fiv3 _ _ (encS (＜ ＜ _, If acc Then _ Else ⫠, _ ＞, ph2 ＞) _) _)))) (fun _ => _) (acc0 c10 c11 & acc1 c10 c11)). rewrite If_true.
  reflexivity.
  time (pose prop26_13_swap_m0_m1_cnxt3;
  pose prop26_13_swap_m0_m1_cnxt4; ProveContext). (*1.763 secs *) 
  1, 4: ProveContext.
  1, 3: unfold acc0; unfold acc1; Provebool.
  time (pose prop26_13_swap_m0_m1_cnxt3;
  pose prop26_13_swap_m0_m1_cnxt4; ProveContext). (*15.741 secs*)
}
  simpl in H. simpl. unfold e1. unfold e1 in H.
  rewrite H. clear H.



  rewrite <- (lemma26_13_CCA2Game2n_x0 c10 c11 (encS (m1 c10 c11 n1) rd0)).
  rewrite <- (lemma26_13_CCA2Game1n_x0). simpl.



(* −- CCA2 compliant. pkS := nonce 6, rd1 := nonce 8 *)
  rewrite (lemma26_13_CCA2Game2n_x1 c10 c11 (encS (m0 c10 c11 n0) rd1)).
  rewrite (lemma26_13_dv_dvS26 (m1 c10 c11 n1) (m0 c10 c11 n0) c10 c11).
  repeat rewrite (lemma26_13_CCA2Game1n_x1).
  assert (
      (fun x1 : ppt =>
         (fun x0 : ppt =>
            (fun dvs : ppt =>
               [b0 c10; b1 c11; acc0 c10 c11 & acc1 c10 c11;
                acc0 c10 c11 & acc1 c10 c11 & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs);
                If ((acc0 c10 c11 & acc1 c10 c11) & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs))
                  Then (＜ ＜ x0, x1, dvs ＞,
                    ＜ Enco0 c10 c11 x0 x1 dvs, Enco1 c10 c11 x0 x1 dvs,
                    Do (giO1 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) (giO2 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) (giO3 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) ＞ ＞)
                  Else ⫠]) (dvS26 c10 c11 x0 x1 (giv3 c10 c11 x0 x1))
         ) (encS (m1 c10 c11 n1) rd0)
      ) (encS (m0 c10 c11 n0) rd1)
      =
        (fun x1 : ppt =>
           (fun x0 : ppt =>
              (fun dvs : ppt =>
                 [b0 c10; b1 c11; acc0 c10 c11 & acc1 c10 c11;
                  acc0 c10 c11 & acc1 c10 c11 & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs);
                  If ((acc0 c10 c11 & acc1 c10 c11) & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs))
                    Then (＜ ＜ x0, x1, dvs ＞,
                      ＜ Enco0 c10 c11 x0 x1 dvs, Enco1 c10 c11 x0 x1 dvs,
                      Do (giO1 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) (giO2 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) (giO3 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) ＞ ＞)
                    Else ⫠]) (dvS26 c10 c11 x0 x1 (giv3 c10 c11 x0 x1))
           ) (encS (m1 c10 c11 n1) rd0)
        ) (encS  (＜ ＜ c10, (If (acc0 c10 c11 & acc1 c10 c11) Then (ub c10 t bn0 (ti0 c10 c11)) Else ⫠ ) , n0 ＞, ph2 ＞) rd1)
    ).
{
  repeat rewrite (UnfoldAnd (acc0 c10 c11 & acc1 c10 c11)).
  rewrite (@If_eval (fun acc => (fun x1 : ppt =>
           (fun x0 : ppt =>
              (fun dvs : ppt =>
                  If (bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs)) & (bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs))
                    Then (＜ ＜ x0, x1, dvs ＞,
                      ＜ Enco0 c10 c11 x0 x1 dvs, Enco1 c10 c11 x0 x1 dvs,
                      Do (giO1 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) (giO2 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) (giO3 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) ＞ ＞)
                    Else ⫠) (dvS26 c10 c11 x0 x1 (giv3 c10 c11 x0 x1))
           ) (encS (m1 c10 c11 n1) rd0)
        ) (encS  (＜ ＜ _, (If acc Then _ Else ⫠ ) , _ ＞, ph2 ＞) rd1)) (fun _ => _) (acc0 c10 c11 & acc1 c10 c11)). rewrite If_true.
  
  repeat rewrite <- AndAssoc with (A := acc0 c10 c11).
  rewrite (@If_eval (fun acc => bnlcheck c10 n0
    (FΦΦ3 _ _ _ (encS (＜ ＜ c10, If acc Then _ Else ⫠, n0 ＞, ph2 ＞) rd1)
       (dvS26 _ _ _ (encS (＜ ＜ c10, If acc Then _ Else ⫠, n0 ＞, ph2 ＞) rd1)
          (giv3 _ _ _ (encS (＜ ＜ c10, If acc Then _ Else ⫠, n0 ＞, ph2 ＞) rd1)))) &
  bnlcheck c11 n1
    (FΦΦ3 _ _ _  (encS (＜ ＜ c10, If acc Then _ Else ⫠, n0 ＞, ph2 ＞) rd1)
       (dvS26 _ _ _ (encS (＜ ＜ c10, If acc Then _ Else ⫠, n0 ＞, ph2 ＞) rd1)
          (giv3 _ _ _ (encS (＜ ＜ c10, If acc Then _ Else ⫠, n0 ＞, ph2 ＞) rd1))))) (fun _ => _) (acc0 c10 c11 & acc1 c10 c11)). rewrite If_true.
  reflexivity.
  time (pose prop26_13_swap_m0_m1_cnxt5;
  pose prop26_13_swap_m0_m1_cnxt6; ProveContext). (*2.176 secs*) 
  1, 4: ProveContext.
  1, 3: unfold acc0; unfold acc1; Provebool.
  time (pose prop26_13_swap_m0_m1_cnxt5;
  pose prop26_13_swap_m0_m1_cnxt6; ProveContext). (*16.201 secs*)
}

  simpl in H.
  rewrite H. clear H.
  

  pose (cca2
          [nonce 6]
          [nonce 8]
          (fun x1 =>
             (fun x0 =>
                (fun dvs =>
                   [b0 c10; b1 c11; acc0 c10 c11 & acc1 c10 c11;
                    acc0 c10 c11 & acc1 c10 c11 & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs);
                    If ((acc0 c10 c11 & acc1 c10 c11) & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs))
                      Then (＜ ＜ x0 , x1 , dvs ＞, ＜ Enco0 c10 c11 x0 x1 dvs, Enco1 c10 c11 x0 x1 dvs,
                        Do (giO1 (m0 c10 c11 n0) c10 c11  x0 x1 dvs) (giO2 (m0 c10 c11 n0) c10 c11  x0 x1 dvs) (giO3 (m0 c10 c11 n0) c10 c11  x0 x1 dvs) ＞ ＞)
                      Else ⫠]
                ) (dvS26 c10 c11 x0 x1 (giv3 c10 c11 x0 x1))
             ) (encS (m1 c10 c11 n1) rd0)
          )
          (＜ ＜ c10, (If (acc0 c10 c11 & acc1 c10 c11) Then (ub c10 t bn0 (ti0 c10 c11)) Else ⫠ ) , n0 ＞, ph2 ＞)
          (＜ ＜ c11, (If (acc0 c10 c11 & acc1 c10 c11) Then (ub c11 t bn1 (ti1 c10 c11)) Else ⫠ ), n1 ＞, ph2 ＞)) as claim1.
  
  simpl in claim1. 
  rewrite claim1. clear claim1.

 assert (
      (fun x1 : ppt =>
         (fun x0 : ppt =>
            (fun dvs : ppt =>
               [b0 c10; b1 c11; acc0 c10 c11 & acc1 c10 c11;
                acc0 c10 c11 & acc1 c10 c11 & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs);
                If ((acc0 c10 c11 & acc1 c10 c11) & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs))
                  Then (＜ ＜ x0, x1, dvs ＞,
                    ＜ Enco0 c10 c11 x0 x1 dvs, Enco1 c10 c11 x0 x1 dvs,
                    Do (giO1 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) (giO2 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) (giO3 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) ＞ ＞)
                  Else ⫠]) (dvS26 c10 c11 x0 x1 (giv3 c10 c11 x0 x1))
         ) (encS (m1 c10 c11 n1) rd0)
      ) (encS (m1 c10 c11 n1) rd1)
      =
        (fun x1 : ppt =>
           (fun x0 : ppt =>
              (fun dvs : ppt =>
                 [b0 c10; b1 c11; acc0 c10 c11 & acc1 c10 c11;
                  acc0 c10 c11 & acc1 c10 c11 & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs);
                  If ((acc0 c10 c11 & acc1 c10 c11) & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs))
                    Then (＜ ＜ x0, x1, dvs ＞,
                      ＜ Enco0 c10 c11 x0 x1 dvs, Enco1 c10 c11 x0 x1 dvs,
                      Do (giO1 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) (giO2 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) (giO3 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) ＞ ＞)
                    Else ⫠]) (dvS26 c10 c11 x0 x1 (giv3 c10 c11 x0 x1))
           ) (encS (m1 c10 c11 n1) rd0)
        ) (encS  (＜ ＜ c11, (If (acc0 c10 c11 & acc1 c10 c11) Then (ub c11 t bn1 (ti1 c10 c11)) Else ⫠ ), n1 ＞, ph2 ＞) rd1)
    ). 
 {
  repeat rewrite (UnfoldAnd (acc0 c10 c11 & acc1 c10 c11)).
  rewrite (@If_eval (fun acc => (fun x1 : ppt =>
           (fun x0 : ppt =>
              (fun dvs : ppt =>
                  If (bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs)) & (bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs))
                    Then (＜ ＜ x0, x1, dvs ＞,
                      ＜ Enco0 c10 c11 x0 x1 dvs, Enco1 c10 c11 x0 x1 dvs,
                      Do (giO1 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) (giO2 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) (giO3 (m0 c10 c11 n0) c10 c11 x0 x1 dvs) ＞ ＞)
                    Else ⫠) (dvS26 c10 c11 x0 x1 (giv3 c10 c11 x0 x1))
           ) (encS (m1 c10 c11 n1) rd0)
        ) (encS  (＜ ＜ _, (If acc Then _ Else ⫠ ) , _ ＞, ph2 ＞) rd1)) (fun _ => _) (acc0 c10 c11 & acc1 c10 c11)). rewrite If_true.
  
  repeat rewrite <- AndAssoc with (A := acc0 c10 c11).
  rewrite (@If_eval (fun acc => bnlcheck _ _
    (FΦΦ3 _ _ _ (encS (＜ ＜ _, If acc Then _ Else ⫠, _ ＞, ph2 ＞) rd1)
       (dvS26 _ _ _ (encS (＜ ＜ _, If acc Then _ Else ⫠, _ ＞, ph2 ＞) rd1)
          (giv3 _ _ _ (encS (＜ ＜ _, If acc Then _ Else ⫠, _ ＞, ph2 ＞) rd1)))) &
  bnlcheck c11 n1
    (FΦΦ3 _ _ _  (encS (＜ ＜ _, If acc Then _ Else ⫠, _ ＞, ph2 ＞) rd1)
       (dvS26 _ _ _ (encS (＜ ＜ _, If acc Then _ Else ⫠, _ ＞, ph2 ＞) rd1)
          (giv3 _ _ _ (encS (＜ ＜ _, If acc Then _ Else ⫠, _ ＞, ph2 ＞) rd1))))) (fun _ => _) (acc0 c10 c11 & acc1 c10 c11)). rewrite If_true.
  reflexivity.
  time (pose prop26_13_swap_m0_m1_cnxt7;
  pose prop26_13_swap_m0_m1_cnxt6; ProveContext). (*2.176 secs*) 
  1, 4: ProveContext.
  1, 3: unfold acc0; unfold acc1; Provebool.
  time (pose prop26_13_swap_m0_m1_cnxt7;
  pose prop26_13_swap_m0_m1_cnxt8; ProveContext). (*16.201 secs*)
}

  rewrite <- H. clear H.   
  rewrite <- (lemma26_13_CCA2Game2n_x1 c10 c11 (encS (m1 c10 c11 n1) rd1)).
  repeat rewrite <- (lemma26_13_CCA2Game1n_x1).

(**)
  reflexivity.

(**)
  1, 11, 13 , 23 : time ProveContext. (* 9.64 secs *)
  all : try auto.
  7  : { unfold m0 , m1.
  unfold pv0, pv1.
  apply PairLen.
  - apply TripleLen.
    + apply comLen.
      rewrite voteLen. reflexivity.
      all: ProveFresh.
    + unfold σ0, σ1.
      unfold acc0, acc1.
      apply ubLen.
      * apply comLen.
        rewrite voteLen. reflexivity. 
      all: ProveFresh.
      * ProveFresh.
      * ProveFresh.
      * unfold ti0.
        apply  UbNUDAttContListTerm.
        ProveContext.
        apply UbNUDContextConc. unfold b0. apply UbNUDBlindSign.
        ProveFresh. ProveFresh.
        unfold b1. 
        apply UbNUDContextConc. apply UbNUDAttContListTerm. ProveContext.
        apply UbNUDContextConc. apply UbNUDAttContListTerm. ProveContext.
        apply UbNUDContextConc. apply UbNUDAttContListTerm. ProveContext.
        apply  UbNUDFresh; ProveFresh. 
        apply  UbNUDFresh; ProveFresh.
        apply UbNUDContextConc. apply UbNUDAttContListTerm. ProveContext.
        apply  UbNUDFresh; ProveFresh. 
        apply  UbNUDFresh; ProveFresh. 
        apply  UbNUDFresh; ProveFresh.
      * unfold ti1.
        apply  UbNUDAttContListTerm.
        ProveContext.
        apply UbNUDContextConc. unfold b0.
        apply UbNUDAttContListTerm. ProveContext. 
        apply UbNUDContextConc. apply UbNUDAttContListTerm. ProveContext.
        apply UbNUDContextConc. apply UbNUDAttContListTerm. ProveContext.
        apply  UbNUDFresh; ProveFresh. 
        apply  UbNUDFresh; ProveFresh.
        apply UbNUDContextConc. apply UbNUDAttContListTerm. ProveContext.
        apply  UbNUDFresh; ProveFresh. 
        apply  UbNUDFresh; ProveFresh.
        apply UbNUDContextConc.
        unfold b1.
        apply UbNUDBlindSign.
        ProveFresh. ProveFresh.
        apply  UbNUDFresh; ProveFresh.         
  - reflexivity. }
  13 : {
    unfold m0 , m1.
  unfold pv0, pv1.
  apply PairLen.
  - apply TripleLen.
    + apply comLen.
      rewrite voteLen. reflexivity.
      all: ProveFresh.
    + unfold σ0, σ1.
      apply ubLen.
      * apply comLen.
        rewrite voteLen. reflexivity.
      all: ProveFresh.
      * ProveFresh.
      * ProveFresh.
      * unfold ti0.
        apply  UbNUDAttContListTerm.
        ProveContext.
        apply UbNUDContextConc. unfold b0. apply UbNUDBlindSign.
        ProveFresh. ProveFresh.
        unfold b1. 
        apply UbNUDContextConc. apply UbNUDAttContListTerm. ProveContext.
        apply UbNUDContextConc. apply UbNUDAttContListTerm. ProveContext.
        apply UbNUDContextConc. apply UbNUDAttContListTerm. ProveContext.
        apply  UbNUDFresh; ProveFresh. 
        apply  UbNUDFresh; ProveFresh.
        apply UbNUDContextConc. apply UbNUDAttContListTerm. ProveContext.
        apply  UbNUDFresh; ProveFresh. 
        apply  UbNUDFresh; ProveFresh. 
        apply  UbNUDFresh; ProveFresh.
      * unfold ti1.
        apply  UbNUDAttContListTerm.
        ProveContext.
        apply UbNUDContextConc. unfold b0.
        apply UbNUDAttContListTerm. ProveContext. 
        apply UbNUDContextConc. apply UbNUDAttContListTerm. ProveContext.
        apply UbNUDContextConc. apply UbNUDAttContListTerm. ProveContext.
        apply  UbNUDFresh; ProveFresh. 
        apply  UbNUDFresh; ProveFresh.
        apply UbNUDContextConc. apply UbNUDAttContListTerm. ProveContext.
        apply  UbNUDFresh; ProveFresh. 
        apply  UbNUDFresh; ProveFresh.
        apply UbNUDContextConc.
        unfold b1.
        apply UbNUDBlindSign.
        ProveFresh. ProveFresh.
        apply  UbNUDFresh; ProveFresh.     
  - reflexivity. }
  1, 2, 7, 8 : ProveNonceList.
  1, 5: ProveListFresh; try constructor; lia; constructor.
  1, 2, 4, 5: ProveCca2Before.
  apply lemma26_13_CCA2_m0_m1_after_voter1.
  apply lemma26_13_CCA2_m0_m1_after_voter0.
}
Qed.






(****************************************************)
(*--- Part Two                                   ---*)
(****************************************************)

(*  *) 

Lemma lemma26_13_part2_dou_bnlcheck_eval_enco0_up:
  let x0 := (encS (m1 c10 c11 n1) rd0) in
  let x1 := (encS (m0 c10 c11 n0) rd1) in
  let dvs := (dv (V1 c10 c11 x0 x1) (V2 c10 c11 x0 x1) (V3 c10 c11 x0 x1)) (S26 c10 c11 x0 x1 (V3 c10 c11 x0 x1)) in
  (forall msgo0 msgo1,
      ContextTerm General Term (fun x : ppt => msgo0) ->
      ContextTerm General Term (fun x : ppt => msgo1) ->
    ((fun y0 y1 =>
     [b0 c10; b1 c11; (acc0 c10 c11) & (acc1 c10 c11);
      (acc0 c10 c11) & (acc1 c10 c11) & (bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs)) & (bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs));
      If (acc0 c10 c11 & acc1 c10 c11) & (bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs)) & (bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs))
         Then ( ＜ ＜ x0, x1, dvs ＞, ＜ y0, y1 , Do (OO1 c10 c11 y0 y1)
                                                    (OO2 c10 c11 y0 y1)
                                                    (OO3 c10 c11 y0 y1)＞ ＞)
      Else ⫠])
    (encS (msgo0) rdd0) (encS (msgo1) rdd1))
      =
    ((fun y0 y1 =>
        [b0 c10; b1 c11; acc0 c10 c11 & acc1 c10 c11;
          acc0 c10 c11 & acc1 c10 c11 & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs);
          If (acc0 c10 c11 & acc1 c10 c11) & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs)
              Then ＜ ＜ x0, x1, dvs ＞,
       ＜ y0, y1,
       Do
         (If (τ1 (FFΦΦ5 c10 c11 y0 y1) ≟ y0) Then msgo0 Else (If (τ1 (FFΦΦ5 c10 c11 y0 y1) ≟ y0) Then Error Else decS (τ1 (FFΦΦ5 c10 c11 y0 y1))))
         (If (τ2 (FFΦΦ5 c10 c11 y0 y1) ≟ y0) Then msgo0 Else (If (τ2 (FFΦΦ5 c10 c11 y0 y1) ≟ y0) Then Error Else decS (τ2 (FFΦΦ5 c10 c11 y0 y1))))
         (If (τ3 (FFΦΦ5 c10 c11 y0 y1) ≟ y0) Then msgo0 Else (If (τ3 (FFΦΦ5 c10 c11 y0 y1) ≟ y0) Then Error Else decS (τ3 (FFΦΦ5 c10 c11 y0 y1)))) ＞ ＞ Else ⫠] )
     (encS (If (bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs)) Then (msgo0) Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd0)
     (encS (msgo1) rdd1))).
Proof.
  intros. simpl.
  repeat rewrite decSimpl.
  rewrite (AndComm (acc0 c10 c11 & acc1 c10 c11)).
  repeat rewrite (UnfoldAnd _ (acc0 c10 c11 & acc1 c10 c11)). 
  rewrite (@If_eval (fun x => If acc0 c10 c11 & acc1 c10 c11
       Then ＜ ＜ x0, x1, dvs ＞,
            ＜ encS (If x Then _ Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd0, _,
            Do
              (If τ1 (FFΦΦ5 c10 c11 (encS (If x Then _ Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd0) (_)) ≟ encS (If x Then _ Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd0 Then _
               Else decS (τ1 (FFΦΦ5 c10 c11 (encS (If x Then _ Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd0) (_))))
              (If τ2 (FFΦΦ5 c10 c11 (encS (If x Then _ Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd0) (_)) ≟ encS (If x Then _ Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd0 Then _
               Else decS (τ2 (FFΦΦ5 c10 c11 (encS (If x Then _ Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd0) (_))))
              (If τ3 (FFΦΦ5 c10 c11 (encS (If x Then _ Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd0) (_)) ≟ encS (If x Then _ Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd0 Then _
               Else decS (τ3 (FFΦΦ5 c10 c11 (encS (If x Then _ Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd0) (_)))) ＞
            ＞ Else ⫠)
          (fun x => _)).
  repeat rewrite If_true.
  rewrite <- (decGame msgo0 10 (τ1 (FFΦΦ5 c10 c11 (encS msgo0 rdd0) (encS msgo1 rdd1)))).
  rewrite <- (decGame msgo0 10 (τ2 (FFΦΦ5 c10 c11 (encS msgo0 rdd0) (encS msgo1 rdd1)))).
  rewrite <- (decGame msgo0 10 (τ3 (FFΦΦ5 c10 c11 (encS msgo0 rdd0) (encS msgo1 rdd1)))).
  reflexivity.

  2 : ProveboolandContext.
  2, 4 : unfold bnlcheck; ProveboolandContext; unfold ncheck; unfold isin; ProveboolandContext.
  2, 3, 4, 5 : unfold acc1; ProveboolandContext.

  apply prop26_13_enco0_up_cnxt2; auto. 
Qed.


(*--------------------------------------------------------------------------------------*)
(*  *)

Lemma lemma26_13_part2_dou_bnlcheck_eval_enco0_down:
  let x0 := (encS (m1 c10 c11 n1) rd0) in
  let x1 := (encS (m0 c10 c11 n0) rd1) in
  let dvs := (dv (V1 c10 c11 x0 x1) (V2 c10 c11 x0 x1) (V3 c10 c11 x0 x1)) (S26 c10 c11 x0 x1 (V3 c10 c11 x0 x1)) in
  (forall msgo0 msgo0' msgo1,
    ContextTerm General Term (fun _ : ppt => msgo0) ->
    ContextTerm General Term (fun _ : ppt => msgo0') ->
    ContextTerm General Term (fun _ : ppt => msgo1) ->
    ((fun y0 y1 =>
        [b0 c10; b1 c11; acc0 c10 c11 & acc1 c10 c11;
          acc0 c10 c11 & acc1 c10 c11 & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs);
          If (acc0 c10 c11 & acc1 c10 c11) & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs)
              Then ＜ ＜ x0, x1, dvs ＞,
       ＜ y0, y1,
       Do
         (If (τ1 (FFΦΦ5 c10 c11 y0 y1) ≟ y0) Then msgo0 Else (If (τ1 (FFΦΦ5 c10 c11 y0 y1) ≟ y0) Then Error Else decS (τ1 (FFΦΦ5 c10 c11 y0 y1))))
         (If (τ2 (FFΦΦ5 c10 c11 y0 y1) ≟ y0) Then msgo0 Else (If (τ2 (FFΦΦ5 c10 c11 y0 y1) ≟ y0) Then Error Else decS (τ2 (FFΦΦ5 c10 c11 y0 y1))))
         (If (τ3 (FFΦΦ5 c10 c11 y0 y1) ≟ y0) Then msgo0 Else (If (τ3 (FFΦΦ5 c10 c11 y0 y1) ≟ y0) Then Error Else decS (τ3 (FFΦΦ5 c10 c11 y0 y1)))) ＞ ＞ Else ⫠] )
     (encS (If (bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs)) Then (msgo0') Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd0)
     (encS (msgo1) rdd1))
      =
    ((fun y0 y1 =>
        [b0 c10; b1 c11; acc0 c10 c11 & acc1 c10 c11;
          acc0 c10 c11 & acc1 c10 c11 & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs);
          If (acc0 c10 c11 & acc1 c10 c11) & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs)
              Then ＜ ＜ x0, x1, dvs ＞,
       ＜ y0, y1,
       Do
         (If (τ1 (FFΦΦ5 c10 c11 y0 y1) ≟ y0) Then msgo0 Else (decS (τ1 (FFΦΦ5 c10 c11 y0 y1))))
         (If (τ2 (FFΦΦ5 c10 c11 y0 y1) ≟ y0) Then msgo0 Else (decS (τ2 (FFΦΦ5 c10 c11 y0 y1))))
         (If (τ3 (FFΦΦ5 c10 c11 y0 y1) ≟ y0) Then msgo0 Else (decS (τ3 (FFΦΦ5 c10 c11 y0 y1)))) ＞ ＞ Else ⫠] )
     (encS (msgo0') rdd0)
     (encS (msgo1) rdd1))).
Proof.
  intros. simpl.
  repeat rewrite decSimpl.
  rewrite (AndComm (acc0 c10 c11 & acc1 c10 c11)).
  repeat rewrite (UnfoldAnd _ (acc0 c10 c11 & acc1 c10 c11)). 
  rewrite (@If_eval (fun x => If acc0 c10 c11 & acc1 c10 c11
       Then ＜ ＜ x0, x1, dvs ＞,
            ＜ encS (If x Then _ Else _ ) rdd0, encS msgo1 rdd1,
            Do
              (If τ1 (FFΦΦ5 c10 c11 (encS (If x Then _ Else _) rdd0) (_))
                  ≟ encS (If x Then _ Else _) rdd0 Then _
               Else decS (τ1 (FFΦΦ5 c10 c11 (encS (If x Then _ Else _) rdd0) (_))))
              (If τ2 (FFΦΦ5 c10 c11 (encS (If x Then _ Else _) rdd0) (_))
                  ≟ encS (If x Then _ Else _) rdd0 Then _
               Else decS (τ2 (FFΦΦ5 c10 c11 (encS (If x Then _ Else _) rdd0) (_))))
              (If τ3 (FFΦΦ5 c10 c11 (encS (If x Then _ Else _) rdd0) (_))
                  ≟ encS (If x Then _ Else _) rdd0 Then _
               Else decS (τ3 (FFΦΦ5 c10 c11 (encS (If x Then _ Else _) rdd0) (_))))
            ＞ ＞ Else _)
          (fun x => _)).
  repeat rewrite If_true.
  reflexivity.
  2 : ProveboolandContext.
  2, 4 : unfold bnlcheck; ProveboolandContext; unfold ncheck; unfold isin; ProveboolandContext.
  2,3,4,5 : unfold acc1; ProveboolandContext.
  apply prop26_13_enco0_down_cnxt2; auto.
Qed.



(*--------------------------------------------------------------------------------------*)

(*  *)

Lemma lemma26_13_part2_dou_bnlcheck_eval_enco1_up:
  let x0 := (encS (m1 c10 c11 n1) rd0) in
  let x1 := (encS (m0 c10 c11 n0) rd1) in
  let dvs := (dv (V1 c10 c11 x0 x1) (V2 c10 c11 x0 x1) (V3 c10 c11 x0 x1)) (S26 c10 c11 x0 x1 (V3 c10 c11 x0 x1)) in
  (forall msgo0 msgo0' msgo1,
    ContextTerm General Term (fun _ : ppt => msgo0) ->
    ContextTerm General Term (fun _ : ppt => msgo0') ->
    ContextTerm General Term (fun _ : ppt => msgo1) ->
    ((fun y0 y1 =>
        [b0 c10; b1 c11; acc0 c10 c11 & acc1 c10 c11;
          acc0 c10 c11 & acc1 c10 c11 & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs);
          If (acc0 c10 c11 & acc1 c10 c11) & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs)
              Then ＜ ＜ x0, x1, dvs ＞,
       ＜ y0, y1,
       Do
         (If (τ1 (FFΦΦ5 c10 c11 y0 y1) ≟ y0) Then msgo0 Else (decS (τ1 (FFΦΦ5 c10 c11 y0 y1))))
         (If (τ2 (FFΦΦ5 c10 c11 y0 y1) ≟ y0) Then msgo0 Else (decS (τ2 (FFΦΦ5 c10 c11 y0 y1))))
         (If (τ3 (FFΦΦ5 c10 c11 y0 y1) ≟ y0) Then msgo0 Else (decS (τ3 (FFΦΦ5 c10 c11 y0 y1)))) ＞ ＞ Else ⫠] )
     (encS (msgo0') rdd0)
     (encS (msgo1) rdd1))
      =
    ((fun y0 y1 =>
        [b0 c10; b1 c11; acc0 c10 c11 & acc1 c10 c11;
          acc0 c10 c11 & acc1 c10 c11 & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs);
          If (acc0 c10 c11 & acc1 c10 c11) & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs)
              Then ＜ ＜ x0, x1, dvs ＞,
       ＜ y0, y1,
       Do
         (If (τ1 (FFΦΦ5 c10 c11 y0 y1) ≟ y0) Then msgo0 Else (If (τ1 (FFΦΦ5 c10 c11 y0 y1) ≟ y1) Then msgo1
                                             Else If (τ1 (FFΦΦ5 c10 c11 y0 y1) ≟ y1) Then Error Else decS (τ1 (FFΦΦ5 c10 c11 y0 y1))))
         (If (τ2 (FFΦΦ5 c10 c11 y0 y1) ≟ y0) Then msgo0 Else (If (τ2 (FFΦΦ5 c10 c11 y0 y1) ≟ y1) Then msgo1
                                             Else If (τ2 (FFΦΦ5 c10 c11 y0 y1) ≟ y1) Then Error Else decS (τ2 (FFΦΦ5 c10 c11 y0 y1))))
         (If (τ3 (FFΦΦ5 c10 c11 y0 y1) ≟ y0) Then msgo0 Else (If (τ3 (FFΦΦ5 c10 c11 y0 y1) ≟ y1) Then msgo1
                                             Else If (τ3 (FFΦΦ5 c10 c11 y0 y1) ≟ y1) Then Error Else decS (τ3 (FFΦΦ5 c10 c11 y0 y1)))) ＞ ＞ Else ⫠] )
     (encS (msgo0') rdd0)
     (encS (If (bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs)) Then (msgo1) Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd1))).
Proof.
  intros. simpl.
  repeat rewrite decSimpl.
  rewrite (AndComm (acc0 c10 c11 & acc1 c10 c11)).
  repeat rewrite (UnfoldAnd _ (acc0 c10 c11 & acc1 c10 c11)).
  rewrite (@If_eval (fun x => If acc0 c10 c11 & acc1 c10 c11
       Then ＜ ＜ x0, x1, dvs ＞,
            ＜ encS msgo0' rdd0, encS (If x Then msgo1 Else _) rdd1,
            Do
              (If τ1 (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS (If x Then msgo1 Else _) rdd1))
                  ≟ encS msgo0' rdd0 Then msgo0
               Else If τ1 (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS (If x Then msgo1 Else _) rdd1))
                       ≟ encS (If x Then msgo1 Else _) rdd1 Then msgo1
                    Else decS
                           (τ1 (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS (If x Then msgo1 Else _) rdd1))))
              (If τ2 (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS (If x Then msgo1 Else _) rdd1))
                  ≟ encS msgo0' rdd0 Then msgo0
               Else If τ2 (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS (If x Then msgo1 Else _) rdd1))
                       ≟ encS (If x Then msgo1 Else _) rdd1 Then msgo1
                    Else decS
                           (τ2 (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS (If x Then msgo1 Else _) rdd1))))
              (If τ3 (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS (If x Then msgo1 Else _) rdd1))
                  ≟ encS msgo0' rdd0 Then msgo0
               Else If τ3 (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS (If x Then msgo1 Else _) rdd1))
                       ≟ encS (If x Then msgo1 Else _) rdd1 Then msgo1
                    Else decS
                           (τ3 (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS (If x Then msgo1 Else _) rdd1))))
            ＞ ＞ Else _)
          (fun x => _)).
  repeat rewrite If_true.
  rewrite <- (decGame msgo1 11 (τ1 (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS msgo1 rdd1)))).
  rewrite <- (decGame msgo1 11 (τ2 (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS msgo1 rdd1)))).
  rewrite <- (decGame msgo1 11 (τ3 (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS msgo1 rdd1)))).
  reflexivity.
  2 : ProveboolandContext.
  2, 4 : unfold bnlcheck; ProveboolandContext; unfold ncheck; unfold isin; ProveboolandContext.
  2,3,4,5 : unfold acc1; ProveboolandContext.
  apply prop26_13_enco1_up_cnxt2; auto.
Qed.




(*--------------------------------------------------------------------------------------*)

(*  *)

Lemma lemma26_13_part2_dou_bnlcheck_eval_enco1_down:
  let x0 := (encS (m1 c10 c11 n1) rd0) in
  let x1 := (encS (m0 c10 c11 n0) rd1) in
  let dvs := (dv (V1 c10 c11 x0 x1) (V2 c10 c11 x0 x1) (V3 c10 c11 x0 x1)) (S26 c10 c11 x0 x1 (V3 c10 c11 x0 x1)) in
  (forall msgo0 msgo0' msgo1 msgo1',
    ContextTerm General Term (fun _ : ppt => msgo0) ->
    ContextTerm General Term (fun _ : ppt => msgo0') ->
    ContextTerm General Term (fun _ : ppt => msgo1) ->
    ContextTerm General Term (fun _ : ppt => msgo1') ->
    ((fun y0 y1 =>
        [b0 c10; b1 c11; acc0 c10 c11 & acc1 c10 c11;
          acc0 c10 c11 & acc1 c10 c11 & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs);
          If (acc0 c10 c11 & acc1 c10 c11) & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs)
              Then ＜ ＜ x0, x1, dvs ＞,
       ＜ y0, y1,
       Do
         (If (τ1 (FFΦΦ5 c10 c11 y0 y1) ≟ y0) Then msgo0 Else (If (τ1 (FFΦΦ5 c10 c11 y0 y1) ≟ y1) Then msgo1
                                             Else If (τ1 (FFΦΦ5 c10 c11 y0 y1) ≟ y1) Then Error Else decS (τ1 (FFΦΦ5 c10 c11 y0 y1))))
         (If (τ2 (FFΦΦ5 c10 c11 y0 y1) ≟ y0) Then msgo0 Else (If (τ2 (FFΦΦ5 c10 c11 y0 y1) ≟ y1) Then msgo1
                                             Else If (τ2 (FFΦΦ5 c10 c11 y0 y1) ≟ y1) Then Error Else decS (τ2 (FFΦΦ5 c10 c11 y0 y1))))
         (If (τ3 (FFΦΦ5 c10 c11 y0 y1) ≟ y0) Then msgo0 Else (If (τ3 (FFΦΦ5 c10 c11 y0 y1) ≟ y1) Then msgo1
                                             Else If (τ3 (FFΦΦ5 c10 c11 y0 y1) ≟ y1) Then Error Else decS (τ3 (FFΦΦ5 c10 c11 y0 y1)))) ＞ ＞ Else ⫠] )
     (encS (msgo0') rdd0)
     (encS (If (bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs)) Then (msgo1') Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd1))
      =
    ((fun y0 y1 =>
        [b0 c10; b1 c11; acc0 c10 c11 & acc1 c10 c11;
          acc0 c10 c11 & acc1 c10 c11 & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs);
          If (acc0 c10 c11 & acc1 c10 c11) & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs)
              Then ＜ ＜ x0, x1, dvs ＞,
       ＜ y0, y1,
       Do
         (If (τ1 (FFΦΦ5 c10 c11 y0 y1) ≟ y0) Then msgo0 Else (If (τ1 (FFΦΦ5 c10 c11 y0 y1) ≟ y1) Then msgo1
                                             Else decS (τ1 (FFΦΦ5 c10 c11 y0 y1))))
         (If (τ2 (FFΦΦ5 c10 c11 y0 y1) ≟ y0) Then msgo0 Else (If (τ2 (FFΦΦ5 c10 c11 y0 y1) ≟ y1) Then msgo1
                                             Else decS (τ2 (FFΦΦ5 c10 c11 y0 y1))))
         (If (τ3 (FFΦΦ5 c10 c11 y0 y1) ≟ y0) Then msgo0 Else (If (τ3 (FFΦΦ5 c10 c11 y0 y1) ≟ y1) Then msgo1
                                             Else decS (τ3 (FFΦΦ5 c10 c11 y0 y1)))) ＞ ＞ Else ⫠] )
     (encS (msgo0') rdd0)
     (encS (msgo1') rdd1))).
Proof.
  intros. simpl.
  repeat rewrite decSimpl.
  rewrite (AndComm (acc0 c10 c11 & acc1 c10 c11)).
  repeat rewrite (UnfoldAnd _ (acc0 c10 c11 & acc1 c10 c11)).
  rewrite (@If_eval (fun x => If acc0 c10 c11 & acc1 c10 c11
            Then ＜ ＜ x0, x1, dvs ＞,
                 ＜ encS msgo0' rdd0, encS (If x Then msgo1' Else _) rdd1,
                 Do
                   (If τ1 (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS (If x Then msgo1' Else _) rdd1))
                       ≟ encS msgo0' rdd0 Then msgo0
                    Else If τ1 (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS (If x Then msgo1' Else _) rdd1))
                            ≟ encS (If x Then msgo1' Else _) rdd1 Then msgo1
                         Else decS
                                (τ1
                                   (FFΦΦ5 c10 c11 (encS msgo0' rdd0)
                                      (encS (If x Then msgo1' Else _) rdd1))))
                   (If τ2 (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS (If x Then msgo1' Else _) rdd1))
                       ≟ encS msgo0' rdd0 Then msgo0
                    Else If τ2 (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS (If x Then msgo1' Else _) rdd1))
                            ≟ encS (If x Then msgo1' Else _) rdd1 Then msgo1
                         Else decS
                                (τ2
                                   (FFΦΦ5 c10 c11 (encS msgo0' rdd0)
                                      (encS (If x Then msgo1' Else _) rdd1))))
                   (If τ3 (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS (If x Then msgo1' Else _) rdd1))
                       ≟ encS msgo0' rdd0 Then msgo0
                    Else If τ3 (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS (If x Then msgo1' Else _) rdd1))
                            ≟ encS (If x Then msgo1' Else _) rdd1 Then msgo1
                         Else decS
                                (τ3
                                   (FFΦΦ5 c10 c11 (encS msgo0' rdd0)
                                      (encS (If x Then msgo1' Else _) rdd1)))) ＞ ＞ Else _)
          (fun x => _)).
  repeat rewrite If_true.
  reflexivity.
  2 : ProveboolandContext.
  2, 4 : unfold bnlcheck; ProveboolandContext; unfold ncheck; unfold isin; ProveboolandContext.
  2, 3, 4, 5 : unfold acc1; ProveboolandContext.
  apply prop26_13_enco1_down_cnxt2; auto.
Qed.




(*  we substitute (msgo0 c10 c11 kc0) with (msgo1 c10 c11 kc1') under the boolean guard of {bnlcheck0 & bnlcheck1}
    we substitute (msgo1 c10 c11 kc1) with (msgo0 c10 c11 kc0') under the boolean guard of {bnlcheck0 & bnlcheck1} *)

Lemma lemma26_13_part2_LHS:
   let x0 := (encS (m1 c10 c11 n1) rd0) in
   let x1 := (encS (m0 c10 c11 n0) rd1) in
   let dvs := (dv (V1 c10 c11 x0 x1) (V2 c10 c11 x0 x1) (V3 c10 c11 x0 x1)) (S26 c10 c11 x0 x1 (V3 c10 c11 x0 x1)) in
  ((fun y0 y1 =>
     [b0 c10; b1 c11; (acc0 c10 c11) & (acc1 c10 c11);
      (acc0 c10 c11) & (acc1 c10 c11) & (bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs)) & (bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs));
      If (acc0 c10 c11 & acc1 c10 c11) & (bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs)) & (bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs))
         Then ( ＜ ＜ x0, x1, dvs ＞, ＜ y0, y1 , Do (OO1 c10 c11 y0 y1)
                                                    (OO2 c10 c11 y0 y1)
                                                    (OO3 c10 c11 y0 y1)＞ ＞)
      Else ⫠])
   (encS (msgo voter0 c10 c11 kc0) rdd0) (encS (msgo voter1 c10 c11 kc1) rdd1))
 ~
   ((fun y0 y1 =>
     [b0 c10; b1 c11; (acc0 c10 c11) & (acc1 c10 c11);
      (acc0 c10 c11) & (acc1 c10 c11) & (bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs)) & (bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs));
      If (acc0 c10 c11 & acc1 c10 c11) & (bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs)) & (bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs))
         Then ( ＜ ＜ x0, x1, dvs ＞, ＜ y0, y1 , Do (gOO1 c10 c11 (msgo voter0 c10 c11 kc0) (msgo voter1 c10 c11 kc1) y0 y1)
                                                    (gOO2 c10 c11 (msgo voter0 c10 c11 kc0) (msgo voter1 c10 c11 kc1) y0 y1)
                                                    (gOO3 c10 c11 (msgo voter0 c10 c11 kc0) (msgo voter1 c10 c11 kc1) y0 y1)＞ ＞)
      Else ⫠])
   (encS (msgo voter1 c10 c11 kc1') rdd0) (encS (msgo voter0 c10 c11 kc0') rdd1)).
Proof.
  intros x0 x1 dvs.
{ intros. simpl.

(* we move bnlcheck0 & bnlcheck1 inside the first encryption(msgo0)  *)
  pose (lemma26_13_part2_dou_bnlcheck_eval_enco0_up (msgo0 c10 c11 kc0) (msgo1 c10 c11 kc1)) as e.
  simpl in e. fold x0 x1 in e. fold dvs in e.
  rewrite e. clear e.

(* −- CCA2 compliant. pkS := nonce 6, rdd0 := nonce 10 *)
  pose (cca2 [nonce 6] [nonce 10] (fun y0 =>
   [b0 c10; b1 c11; (acc0 c10 c11) & (acc1 c10 c11);
    acc0 c10 c11 & acc1 c10 c11 & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs);
  If (acc0 c10 c11 & acc1 c10 c11) & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs)
  Then ＜ ＜ x0, x1, dvs ＞,
       ＜ y0, encS (msgo1 c10 c11 kc1) rdd1,
       Do
         (If τ1 (FFΦΦ5 c10 c11 (y0) (encS (msgo1 c10 c11 kc1) rdd1)) ≟ y0 Then (msgo0 c10 c11 kc0)
          Else If τ1 (FFΦΦ5 c10 c11 (y0) (encS (msgo1 c10 c11 kc1) rdd1)) ≟ y0 Then Error
               Else decS (τ1 (FFΦΦ5 c10 c11 (y0) (encS (msgo1 c10 c11 kc1) rdd1))))
         (If τ2 (FFΦΦ5 c10 c11 (y0) (encS (msgo1 c10 c11 kc1) rdd1)) ≟ y0 Then (msgo0 c10 c11 kc0)
          Else If τ2 (FFΦΦ5 c10 c11 (y0) (encS (msgo1 c10 c11 kc1) rdd1)) ≟ y0 Then Error
               Else decS (τ2 (FFΦΦ5 c10 c11 (y0) (encS (msgo1 c10 c11 kc1) rdd1))))
         (If τ3 (FFΦΦ5 c10 c11 (y0) (encS (msgo1 c10 c11 kc1) rdd1)) ≟ y0 Then (msgo0 c10 c11 kc0)
          Else If τ3 (FFΦΦ5 c10 c11 (y0) (encS (msgo1 c10 c11 kc1) rdd1)) ≟ y0 Then Error
               Else decS (τ3 (FFΦΦ5 c10 c11 (y0) (encS (msgo1 c10 c11 kc1) rdd1)))) ＞ ＞ Else ⫠] )
             (If (bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs)) Then (msgo voter0 c10 c11 kc0) Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞ )
             (If (bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs)) Then (msgo voter1 c10 c11 kc1') Else  ＜ ＜ ⫠, ⫠ ＞, ph3 ＞ )
       ) as claim0;
  simpl in claim0; rewrite claim0; clear claim0.
  unfold msgo; simpl.

(*  *)
  pose (lemma26_13_part2_dou_bnlcheck_eval_enco0_down (msgo0 c10 c11 kc0) (msgo1 c10 c11 kc1') (msgo1 c10 c11 kc1)) as e.
  simpl in e. fold x0 x1 in e. fold dvs in e.
  rewrite e. clear e.

(*  *)
  pose (lemma26_13_part2_dou_bnlcheck_eval_enco1_up (msgo0 c10 c11 kc0) (msgo1 c10 c11 kc1') (msgo1 c10 c11 kc1)) as e.
  simpl in e. fold x0 x1 in e. fold dvs in e.
  rewrite e. clear e.


(* −- CCA2 compliant. pkS := nonce 6, rdd1 := nonce 11 *)
  pose (cca2 [nonce 6] [nonce 11] (fun y1 => [b0 c10; b1 c11; acc0 c10 c11 & acc1 c10 c11;
  acc0 c10 c11 & acc1 c10 c11 & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs);
  If (acc0 c10 c11 & acc1 c10 c11) & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs)
  Then ＜ ＜ x0, x1, dvs ＞,
       ＜ encS (msgo1 c10 c11 kc1') rdd0, y1,
       Do
         (If τ1 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) (y1)) ≟ encS (msgo1 c10 c11 kc1') rdd0 Then msgo0 c10 c11 kc0
          Else If τ1 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) (y1)) ≟ y1 Then msgo1 c10 c11 kc1
               Else If τ1 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) (y1)) ≟ y1 Then Error
                    Else decS (τ1 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) (y1))))
         (If τ2 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) (y1)) ≟ encS (msgo1 c10 c11 kc1') rdd0 Then msgo0 c10 c11 kc0
          Else If τ2 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) (y1)) ≟ y1 Then msgo1 c10 c11 kc1
               Else If τ2 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) (y1)) ≟ y1 Then Error
                    Else decS (τ2 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) (y1))))
         (If τ3 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) (y1)) ≟ encS (msgo1 c10 c11 kc1') rdd0 Then msgo0 c10 c11 kc0
          Else If τ3 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) (y1)) ≟ y1 Then msgo1 c10 c11 kc1
               Else If τ3 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) (y1)) ≟ y1 Then Error
                  Else decS (τ3 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) (y1)))) ＞ ＞ Else ⫠])
             (If (bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs)) Then (msgo voter1 c10 c11 kc1) Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞ )
             (If (bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs)) Then (msgo voter0 c10 c11 kc0') Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞ )) as claim0;
    simpl in claim0; rewrite claim0; clear claim0.

  (*  *)
  pose (lemma26_13_part2_dou_bnlcheck_eval_enco1_down (msgo0 c10 c11 kc0) (msgo1 c10 c11 kc1') (msgo1 c10 c11 kc1) (msgo0 c10 c11 kc0')) as e.
  simpl in e. fold x0 x1 in e. fold dvs in e.
  rewrite e. clear e.

  reflexivity.

(*  *)
  1, 2, 3, 4, 12, 13, 14, 15, 16, 17, 25, 26: pose prop26_13_phase3_cnxt; ProveContext.
  all : auto. all: Provebool.
  (* This looks not fishy now *)
  7 : {
    unfold bnlcheck. unfold msgo0, msgo1. simpl. fold x0 x1. fold dvs.
    repeat rewrite If_pair.
    apply PairLen.
      apply PairLen.
        repeat rewrite (@If_morph (fun x => | x |)).
    (*  *)
        rewrite LEN_prop26_13_helper.
        rewrite (@If_morph (fun x => If x Then | _  | Else |⫠| )).
        rewrite (@If_morph (fun x => If x Then | _  | Else |⫠ |)).
        repeat rewrite If_false.
        rewrite (@If_morph (fun x => If x Then | _ | Else |⫠| )).
        rewrite (@If_morph (fun x => If x Then | _ | Else |⫠| )).
        repeat rewrite If_false.
        fold (bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs)). fold (bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs)).
        rewrite (Eq_branch (| label c11 (FΦΦ3 c10 c11 x0 x1 dvs) |) llbl (fun x => x )) at 1.
        rewrite (Eq_branch (| label c10 (FΦΦ3 c10 c11 x0 x1 dvs) |) llbl (fun x => If | label c11 (FΦΦ3 c10 c11 x0 x1 dvs) | ≟ llbl Then x Else (| ⫠ |))).
        reflexivity.
        all : ProveboolandContext.
        all : ( unfold bcheck; unfold ncheck; unfold isin; Provebool).
        repeat rewrite (@If_morph (fun x => | x |)). simpl. rewrite (ComkLen 1 14).
        reflexivity.
        all : ProveContext.
   reflexivity.  }
  13 : {
    unfold bnlcheck. unfold msgo0, msgo1. simpl. fold x0 x1. fold dvs.
    repeat rewrite If_pair.
    apply PairLen.
      apply PairLen.
        repeat rewrite (@If_morph (fun x => | x |)).
    (*  *)
        rewrite LEN_prop26_13_helper.
        rewrite (@If_morph (fun x => If x Then | _  | Else |⫠| )).
        rewrite (@If_morph (fun x => If x Then | _  | Else |⫠ |)).
        repeat rewrite If_false.
        rewrite (@If_morph (fun x => If x Then | _ | Else |⫠| )).
        rewrite (@If_morph (fun x => If x Then | _ | Else |⫠| )).
        repeat rewrite If_false.
        fold (bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs)). fold (bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs)).
        rewrite (Eq_branch (| label c11 (FΦΦ3 c10 c11 x0 x1 dvs) |) llbl (fun x => x )) at 1.
        rewrite (Eq_branch (| label c10 (FΦΦ3 c10 c11 x0 x1 dvs) |) llbl (fun x => If | label c11 (FΦΦ3 c10 c11 x0 x1 dvs) | ≟ llbl Then x Else (| ⫠ |))).
        reflexivity.
        all : ProveboolandContext.
        1 ,2 ,3 ,4, 7, 8, 9, 10 : ( unfold bcheck; unfold ncheck; unfold isin; Provebool).
        repeat rewrite (@If_morph (fun x => | x |)). simpl. rewrite (ComkLen 0 15).
        reflexivity.
        all : ProveContext.
   reflexivity.  }

  1, 2, 7, 8: ProveNonceList.
  1, 5 : ProveListFresh; try lia; constructor.
  apply prop26_13_CCA2_kc1_kc0'_lhs_before1.
  apply prop26_13_CCA2_kc1_kc0'_lhs_before2.
  apply prop26_13_CCA2_kc1_kc0'_lhs_after1.
  apply prop26_13_CCA2_kc1_kc0'_lhs_before3.
  apply prop26_13_CCA2_kc1_kc0'_lhs_before4.
  apply prop26_13_CCA2_kc1_kc0'_lhs_after2. }
Qed.


(*--------------------------------*)

(*  *)


(*  we substitute (enco voter1 c10 c11 kc1) with (enco voter1 c10 c11 kc1')
    we substitute (enco voter0 c10 c11 kc0) with (enco voter0 c10 c11 kc0')*)

Lemma lemma26_13_part2_RHS:
  let x0 := (encS (msg voter1 c10 c11) rd0) in
  let x1 := (encS (msg voter0 c10 c11) rd1) in
  let dvs := (dv (V1 c10 c11 x0 x1) (V2 c10 c11 x0 x1) (V3 c10 c11 x0 x1)) (S26 c10 c11 x0 x1 (V3 c10 c11 x0 x1)) in
  ((fun y0 y1 =>
     [b0 c10; b1 c11; (acc0 c10 c11) & (acc1 c10 c11);
      (acc0 c10 c11) & (acc1 c10 c11) & (bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs)) & (bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs));
      If (acc0 c10 c11 & acc1 c10 c11) & (bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs)) & (bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs))
         Then ( ＜ ＜ x0, x1, dvs ＞, ＜ y0, y1 , Do (OO1 c10 c11 y0 y1)
                                                    (OO2 c10 c11 y0 y1)
                                                    (OO3 c10 c11 y0 y1)＞ ＞)
      Else ⫠])
   (encS (msgo voter1 c10 c11 kc1) rdd0) (encS (msgo voter0 c10 c11 kc0) rdd1))
 ~
   ((fun y0 y1 =>
     [b0 c10; b1 c11; (acc0 c10 c11) & (acc1 c10 c11);
      (acc0 c10 c11) & (acc1 c10 c11) & (bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs)) & (bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs));
      If (acc0 c10 c11 & acc1 c10 c11) & (bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs)) & (bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs))
         Then ( ＜ ＜ x0, x1, dvs ＞, ＜ y0, y1 , Do (gOO1 c10 c11 (msgo voter1 c10 c11 kc1) (msgo voter0 c10 c11 kc0) y0 y1)
                                                    (gOO2 c10 c11 (msgo voter1 c10 c11 kc1) (msgo voter0 c10 c11 kc0) y0 y1)
                                                    (gOO3 c10 c11 (msgo voter1 c10 c11 kc1) (msgo voter0 c10 c11 kc0) y0 y1)＞ ＞)
      Else ⫠])
   (encS (msgo voter1 c10 c11 kc1') rdd0) (encS (msgo voter0 c10 c11 kc0') rdd1)).
Proof.
{ intros. simpl.

  (**)
  unfold OO1. rewrite (decIfThenElse (msgo voter1 c10 c11 kc1) 10 (τ1 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1) rdd0) (encS (msgo0 c10 c11 kc0) rdd1)))).
  unfold OO2. rewrite (decIfThenElse (msgo voter1 c10 c11 kc1) 10 (τ2 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1) rdd0) (encS (msgo0 c10 c11 kc0) rdd1)))).
  unfold OO3. rewrite (decIfThenElse (msgo voter1 c10 c11 kc1) 10 (τ3 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1) rdd0) (encS (msgo0 c10 c11 kc0) rdd1)))).
  unfold msgo; simpl.

(* −- CCA2 compliant. pkS := nonce 6, rdd0 := nonce 10 *)
  pose (cca2 [nonce 6] [nonce 10] (fun y0 =>
  [b0 c10; b1 c11;  (acc0 c10 c11) & (acc1 c10 c11); acc0 c10 c11 & acc1 c10 c11 & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs);
  If (acc0 c10 c11 & acc1 c10 c11) & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs)
  Then ＜ ＜ x0, x1, dvs ＞,
       ＜ y0, encS (msgo0 c10 c11 kc0) rdd1,
       Do
         (If τ1 (FFΦΦ5 c10 c11 (y0) (encS (msgo0 c10 c11 kc0) rdd1)) ≟ y0 Then msgo1 c10 c11 kc1
          Else If τ1 (FFΦΦ5 c10 c11 (y0) (encS (msgo0 c10 c11 kc0) rdd1)) ≟ y0 Then Error
               Else decS (τ1 (FFΦΦ5 c10 c11 (y0) (encS (msgo0 c10 c11 kc0) rdd1))))
         (If τ2 (FFΦΦ5 c10 c11 (y0) (encS (msgo0 c10 c11 kc0) rdd1)) ≟ y0 Then msgo1 c10 c11 kc1
          Else If τ2 (FFΦΦ5 c10 c11 (y0) (encS (msgo0 c10 c11 kc0) rdd1)) ≟ y0 Then Error
               Else decS (τ2 (FFΦΦ5 c10 c11 (y0) (encS (msgo0 c10 c11 kc0) rdd1))))
         (If τ3 (FFΦΦ5 c10 c11 (y0) (encS (msgo0 c10 c11 kc0) rdd1)) ≟ y0 Then msgo1 c10 c11 kc1
          Else If τ3 (FFΦΦ5 c10 c11 (y0) (encS (msgo0 c10 c11 kc0) rdd1)) ≟ y0 Then Error
               Else decS (τ3 (FFΦΦ5 c10 c11 (y0) (encS (msgo0 c10 c11 kc0) rdd1)))) ＞ ＞ Else ⫠] )
             (msgo voter1 c10 c11 kc1) (msgo voter1 c10 c11 kc1')) as claim0.
  simpl in claim0; rewrite claim0; clear claim0.
  unfold msgo; simpl.
  repeat rewrite decSimpl.

  (**)
  rewrite (decIfThenElse (msgo voter0 c10 c11 kc0) 11 (τ1 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) (encS (msgo0 c10 c11 kc0) rdd1)))).
  rewrite (decIfThenElse (msgo voter0 c10 c11 kc0) 11 (τ2 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) (encS (msgo0 c10 c11 kc0) rdd1)))).
  rewrite (decIfThenElse (msgo voter0 c10 c11 kc0) 11 (τ3 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) (encS (msgo0 c10 c11 kc0) rdd1)))).
  unfold msgo; simpl.

(* −- CCA2 compliant. pkS := nonce 6, rdd1 := nonce 11 *)
  pose (cca2 [nonce 6] [nonce 11] (fun y1 =>
  [b0 c10; b1 c11; (acc0 c10 c11) & (acc1 c10 c11); acc0 c10 c11 & acc1 c10 c11 & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs);
  If (acc0 c10 c11 & acc1 c10 c11) & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs)
  Then ＜ ＜ x0, x1, dvs ＞,
       ＜ encS (msgo1 c10 c11 kc1') rdd0, y1,
       Do
         (If τ1 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) (y1)) ≟ encS (msgo1 c10 c11 kc1') rdd0 Then msgo1 c10 c11 kc1
          Else If τ1 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) (y1)) ≟ y1 Then msgo0 c10 c11 kc0
               Else If τ1 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) (y1)) ≟ y1 Then Error
                    Else decS (τ1 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) (y1))))
         (If τ2 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) (y1)) ≟ encS (msgo1 c10 c11 kc1') rdd0 Then msgo1 c10 c11 kc1
          Else If τ2 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) (y1)) ≟ y1 Then msgo0 c10 c11 kc0
               Else If τ2 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) (y1)) ≟ y1 Then Error
                    Else decS (τ2 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) (y1))))
         (If τ3 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) (y1)) ≟ encS (msgo1 c10 c11 kc1') rdd0 Then msgo1 c10 c11 kc1
          Else If τ3 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) (y1)) ≟ y1 Then msgo0 c10 c11 kc0
               Else If τ3 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) (y1)) ≟ y1 Then Error
                    Else decS (τ3 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) (y1)))) ＞ ＞ Else ⫠])
             (msgo voter0 c10 c11 kc0) (msgo voter0 c10 c11 kc0')) as claim0.
  simpl in claim0; rewrite claim0; clear claim0.
  repeat rewrite decSimpl.
  reflexivity.

(**)
  10 : {
    unfold msgo0.
    apply PairLen.
    - apply PairLen.
      + reflexivity.
      + apply ComkLen.
    - reflexivity. }
  19 : {
    unfold msgo0.
    apply PairLen.
    - apply PairLen.
      + reflexivity.
      + apply ComkLen.
    - reflexivity. }
  all : auto. all: Provebool.
  1, 2, 7, 8: ProveNonceList.
  1, 5 : ProveListFresh; try lia; constructor.
  apply prop26_13_CCA2_kc1_kc0'_rhs_before1.
  apply prop26_13_CCA2_kc1_kc0'_rhs_before2.
  apply prop26_13_CCA2_kc1_kc0'_rhs_after1.
  apply prop26_13_CCA2_kc1_kc0'_rhs_before3.
  apply prop26_13_CCA2_kc1_kc0'_rhs_before4.
  apply prop26_13_CCA2_kc1_kc0'_rhs_after2. }
Qed.


(*  *)

Lemma lemma26_13_part2_Do_equiv: forall c0 c1, c0 = c10 /\ c1 = c11 ->
   (fun y0 y1 =>
     (Do (gOO1 c0 c1 (msgo voter0 c0 c1 kc0) (msgo voter1 c0 c1 kc1) y0 y1)
         (gOO2 c0 c1 (msgo voter0 c0 c1 kc0) (msgo voter1 c0 c1 kc1) y0 y1)
         (gOO3 c0 c1 (msgo voter0 c0 c1 kc0) (msgo voter1 c0 c1 kc1) y0 y1)))
   (encS (msgo voter1 c0 c1 kc1') rdd0) (encS (msgo voter0 c0 c1 kc0') rdd1)
 =
   (fun y0 y1 =>
     (Do (gOO1 c0 c1 (msgo voter1 c0 c1 kc1) (msgo voter0 c0 c1 kc0) y0 y1)
         (gOO2 c0 c1 (msgo voter1 c0 c1 kc1) (msgo voter0 c0 c1 kc0) y0 y1)
         (gOO3 c0 c1 (msgo voter1 c0 c1 kc1) (msgo voter0 c0 c1 kc0) y0 y1)))
   (encS (msgo voter1 c0 c1 kc1') rdd0) (encS (msgo voter0 c0 c1 kc0') rdd1).
Proof.
{ intros. simpl.
  destruct H.

(**)
  unfold gOO1. repeat rewrite (@If_morph (fun x => Do x _ _)).

(**)
  unfold gOO2. repeat rewrite (@If_morph (fun x => Do _ x _)).
    repeat rewrite Do_dist12.
(**)
  unfold gOO3. time repeat rewrite (@If_morph (fun x => Do _ _ x)). (* 5.056 secs *)
    repeat rewrite Do_dist13.
    repeat rewrite Do_dist23.
    repeat rewrite If_same.
    repeat rewrite (lemma26_13_Do_equiv_Do_isinkc1 (msgo0 c0 c1 kc0) c0 c1).
    repeat rewrite (lemma26_13_Do_equiv_Do_isinkc1 (msgo1 c0 c1 kc1) c0 c1).
    repeat rewrite (lemma26_13_Do_equiv_Do_isinkc2 (msgo0 c0 c1 kc0) c0 c1).
    repeat rewrite (lemma26_13_Do_equiv_Do_isinkc2 (msgo1 c0 c1 kc1) c0 c1).
    repeat rewrite (lemma26_13_Do_equiv_Do_isinkc3 (msgo0 c0 c1 kc0) c0 c1).
    repeat rewrite (lemma26_13_Do_equiv_Do_isinkc3 (msgo1 c0 c1 kc1) c0 c1).
    repeat rewrite If_same.
    rewrite (Do_swap12 (msgo0 c0 c1 kc0) (msgo1 c0 c1 kc1) _).
    rewrite (Do_swap13 (msgo0 c0 c1 kc0) _ (msgo1 c0 c1 kc1)).
    rewrite (Do_swap23 (decS (τ1 (FFΦΦ5 c0 c1 (encS (msgo1 c0 c1 kc1') rdd0) (encS (msgo0 c0 c1 kc0') rdd1)))) (msgo0 c0 c1 kc0) (msgo1 c0 c1 kc1)).
    rewrite (Do_swap23 (decS (τ1 (FFΦΦ5 c0 c1 (encS (msgo1 c0 c1 kc1') rdd0) (encS (msgo0 c0 c1 kc0') rdd1)))) (msgo1 c0 c1 kc1) (msgo0 c0 c1 kc0)).
    reflexivity.

(**)
  all : auto.
  all  : ( rewrite H, H0;
  pose (prop26_13_Do_equiv_Φ5cnxt1);
  pose (prop26_13_Do_equiv_msgo1);
  pose (prop26_13_Do_equiv_msgo0);
  pose (prop26_13_Do_equiv_msgo1');
  pose (prop26_13_Do_equiv_msgo0');
  time ProveContext; try unfold dist; ProveContext). (*46.983 secs*)
}
Qed.

(* *)

(* *)


(* Notice the only difference between the RHS of {lemma26_13_part2_LHS, lemma26_13_part2_RHS} is gOOi under Do, so we need to prove their equivalence. *)
Lemma lemma26_13_part2_equiv: forall c0 c1, c0 = c10 /\ c1 = c11 ->
  let x0 := (encS (msg voter1 c0 c1) rd0) in
  let x1 := (encS (msg voter0 c0 c1) rd1) in
  let dvs := (dv (V1 c0 c1 x0 x1) (V2 c0 c1 x0 x1) (V3 c0 c1 x0 x1)) (S26 c0 c1 x0 x1 (V3 c0 c1 x0 x1)) in
   ((fun y0 y1 =>
     [b0 c0; b1 c1; (acc0 c0 c1) & (acc1 c0 c1);
      (acc0 c0 c1) & (acc1 c0 c1) & (bnlcheck c0 n0 (FΦΦ3 c0 c1 x0 x1 dvs)) & (bnlcheck c1 n1 (FΦΦ3 c0 c1 x0 x1 dvs));
      If (acc0 c0 c1 & acc1 c0 c1) & (bnlcheck c0 n0 (FΦΦ3 c0 c1 x0 x1 dvs)) & (bnlcheck c1 n1 (FΦΦ3 c0 c1 x0 x1 dvs))
         Then ( ＜ ＜ x0, x1, dvs ＞, ＜ y0, y1 , Do (gOO1 c0 c1 (msgo voter0 c0 c1 kc0) (msgo voter1 c0 c1 kc1) y0 y1)
                                                    (gOO2 c0 c1 (msgo voter0 c0 c1 kc0) (msgo voter1 c0 c1 kc1) y0 y1)
                                                    (gOO3 c0 c1 (msgo voter0 c0 c1 kc0) (msgo voter1 c0 c1 kc1) y0 y1)＞ ＞)
      Else ⫠])
   (encS (msgo voter1 c0 c1 kc1') rdd0) (encS (msgo voter0 c0 c1 kc0') rdd1))
 =
   ((fun y0 y1 =>
     [b0 c0; b1 c1;  (acc0 c0 c1) & (acc1 c0 c1);
      (acc0 c0 c1) & (acc1 c0 c1) & (bnlcheck c0 n0 (FΦΦ3 c0 c1 x0 x1 dvs)) & (bnlcheck c1 n1 (FΦΦ3 c0 c1 x0 x1 dvs));
      If (acc0 c0 c1 & acc1 c0 c1) & (bnlcheck c0 n0 (FΦΦ3 c0 c1 x0 x1 dvs)) & (bnlcheck c1 n1 (FΦΦ3 c0 c1 x0 x1 dvs))
         Then ( ＜ ＜ x0, x1, dvs ＞, ＜ y0, y1 , Do (gOO1 c0 c1 (msgo voter1 c0 c1 kc1) (msgo voter0 c0 c1 kc0) y0 y1)
                                                    (gOO2 c0 c1 (msgo voter1 c0 c1 kc1) (msgo voter0 c0 c1 kc0) y0 y1)
                                                    (gOO3 c0 c1 (msgo voter1 c0 c1 kc1) (msgo voter0 c0 c1 kc0) y0 y1)＞ ＞)
      Else ⫠])
   (encS (msgo voter1 c0 c1 kc1') rdd0) (encS (msgo voter0 c0 c1 kc0') rdd1)).
Proof.
{
  intros. simpl.
  pose (lemma26_13_part2_Do_equiv c0 c1); simpl in e; rewrite e; clear e.
  reflexivity. auto.
}
Qed.



(**)
Proposition prop26_13_swap_enco0_enco1 :
  let x0 := (encS (msg voter1 c10 c11) rd0) in
  let x1 := (encS (msg voter0 c10 c11) rd1) in
  let dvs := (dv (V1 c10 c11 x0 x1) (V2 c10 c11 x0 x1) (V3 c10 c11 x0 x1)) (S26 c10 c11 x0 x1 (V3 c10 c11 x0 x1)) in
  ((fun y0 y1 =>
     [b0 c10; b1 c11; (acc0 c10 c11) & (acc1 c10 c11);
      (acc0 c10 c11) & (acc1 c10 c11) & (bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs)) & (bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs));
      If (acc0 c10 c11 & acc1 c10 c11) & (bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs)) & (bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs))
      Then ( ＜ ＜ x0, x1, dvs ＞, ＜ y0, y1 , Do (OO1 c10 c11 y0 y1) (OO2 c10 c11 y0 y1) (OO3 c10 c11 y0 y1)＞ ＞)
      Else ⫠])
   (encS (msgo voter0 c10 c11 kc0) rdd0) (encS (msgo voter1 c10 c11 kc1) rdd1))
 ~
   ((fun y0 y1 =>
     [b0 c10; b1 c11;  (acc0 c10 c11) & (acc1 c10 c11);
      (acc0 c10 c11) & (acc1 c10 c11) & (bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs)) & (bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs));
      If (acc0 c10 c11 & acc1 c10 c11) & (bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs)) & (bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs))
      Then ( ＜ ＜ x0, x1, dvs ＞, ＜ y0, y1 , Do (OO1 c10 c11 y0 y1) (OO2 c10 c11 y0 y1) (OO3 c10 c11 y0 y1)＞ ＞)
      Else ⫠])
   (encS (msgo voter1 c10 c11 kc1) rdd0) (encS (msgo voter0 c10 c11 kc0) rdd1)).
Proof.
{ intros. simpl.
  unfold dvs. unfold x0. unfold x1.

(**)
  rewrite (lemma26_13_part2_LHS).

(**)
  rewrite (lemma26_13_part2_RHS).

(**)
  rewrite lemma26_13_part2_equiv.

(**)
  fold x0 x1; fold dvs.
  reflexivity.
  auto.

}
Qed.









(****************************************************)
(*--- Part Three                                 ---*)
(****************************************************)

(* In this part, we will use Blindness together with Ex-funcapp to swap the votings in the blinding phase, and *)


(*   *)


(*   *)

Lemma Blind_swap :
  let ti00 := t0 [b c00 t bn0; b c01 t bn1] in (**)
  let ti01 := t1 [b c00 t bn0; b c01 t bn1] in (**)
  let ti10 := t0 [b c10 t bn0; b c11 t bn1] in (**)
  let ti11 := t1 [b c10 t bn0; b c11 t bn1] in (**)
  [kc0; kc1; pkS; skS; rd0; rd1; n0; n1; rdd0; rdd1 ] ++ [b c00 t bn0; b c01 t bn1; acc c00 t bn0 ti00 & acc c01 t bn1 ti01 ;
                          If acc c00 t bn0 ti00 & acc c01 t bn1 ti01 Then ＜ ub c00 t bn0 ti00, ub c01 t bn1 ti01 ＞ Else (＜ ⫠, ⫠ ＞)]
 ~
  [kc1; kc0; pkS; skS; rd0; rd1; n1; n0; rdd0; rdd1 ] ++ [b c10 t bn0; b c11 t bn1; acc c10 t bn0 ti10 & acc c11 t bn1 ti11 ;
                          If acc c10 t bn0 ti10 & acc c11 t bn1 ti11 Then ＜ ub c11 t bn1 ti11, ub c10 t bn0 ti10 ＞ Else (＜ ⫠, ⫠ ＞)].
Proof.
 
  intros. simpl.

(* first we will use extended-funcapp to swap kc0 and kc1 on the left hand side  *)
  assert ([] ~ []) as H. reflexivity.
  (* add bn1 & bn1 : nonce (3) &  nonce (3)*)
  apply (FreshInd (nonce (3)) (nonce (3))) in H.
  (* add bn0 & bn0 : nonce (2) &  nonce (2)*)
  apply (FreshInd (nonce (2)) (nonce (2))) in H.
  (* add rdd1 & rdd1 : (Rand [nonce (11)]) &  (Rand [nonce (10)])*)
  apply (FreshInd (nonce (11)) (nonce (11))) in H.
  (* add rdd0 & rdd0 : (Rand [nonce (10)]) &  (Rand [nonce (11)])*)
  apply (FreshInd (nonce (10)) (nonce (10))) in H.
  (* add n1 & n0 : nonce (5) & nonce (4)*)
  apply (FreshInd (nonce (5)) (nonce (4))) in H.
  (* add n0 & n1 : nonce (4) & nonce (5)*)
  apply (FreshInd (nonce (4)) (nonce (5))) in H.
  (* add rd1 & rd1 : (Rand [nonce (8)]) &  (Rand [nonce (7)])*)
  apply (FreshInd (nonce (8)) (nonce (8))) in H.
  (* add rd0 & rd0 : (Rand [nonce (7)]) &  (Rand [nonce (8)])*)
  apply (FreshInd (nonce (7)) (nonce (7))) in H.
  (* add pkS & skS : (Pkey [nonce (6)]) & (Skey [nonce (6)])*)
  apply (FreshInd (nonce (6)) (nonce (6))) in H.
  (* add kc1 & kc0 : (nonce (1)) &  (nonce (0))*)
  apply (FreshInd (nonce (1)) (nonce (0))) in H.
  (* add kc0 & kc1 : (nonce (0)) &  (nonce (1))*)
  apply (FreshInd (nonce (0)) (nonce (1))) in H.
  apply (@cind_funcapp (fun lx =>
        [(Comk (Nth 0 lx)) ; (Comk (Nth 1 lx));  (Pkey [Nth 2 lx]); (Skey [Nth 2 lx]); (Rand [Nth 3 lx]); (Rand [Nth 4 lx]); (Nth 5 lx); (Nth 6 lx); (Rand [Nth 7 lx]); (Rand [Nth 8 lx])] ++
        [Brand (Nth 9 lx); Brand (Nth 10 lx) ])) in H;
    unfold Nth in H; simpl in H.

  (**)
  apply (@cind_funcapp (fun lx => let c0 := (com vot0 (Nth 0 lx)) in
                               let c1 := (com vot1 (Nth 1 lx)) in
                               let bn0 := (Nth 10 lx) in
                               let bn1 := (Nth 11 lx) in
                               let b0 := (b c0 t bn0) in
                               let b1 := (b c1 t bn1) in
                               let ti0 := t0 [b0; b1] in (**)
                               let ti1 := t1 [b0; b1] in (**)
                               let acc0 := acc c0 t bn0 ti0 in
                               let acc1 := acc c1 t bn1 ti1 in
                               let ub0 := ub c0 t bn0 ti0 in
                               let ub1 := ub c1 t bn1 ti1 in
        (firstn 10 lx) ++ [b0; b1; acc0 & acc1; If (acc0 & acc1) Then ＜ ub0, ub1 ＞ Else ＜ ⫠, ⫠ ＞])) in H;
    unfold Nth in H; simpl in H.
  unfold ti00. unfold ti01.
rewrite H. clear H.

(* Then we use prop21 to swap the c10 and c11 in the blinding phase *)
  unfold ti10, ti11.
  pose (@prop21 2 3 [kc1; kc0; pkS; skS; rd0; rd1; n1; n0; rdd0; rdd1] c11 c10 t
           (fun x => t0 x) (fun x => t1 x)). simpl in c.
   rewrite c.
  reflexivity.

(**)
  all : try ProveFresh.
  all : try ProveFreshC.  
  apply @cApp. ProveContext. simpl. ProveContext.
  all : try lia.
  Qed.


(**)


(**)

Proposition prop26_13_swap_c10_c11_blinding:
 ((fun c0 c1 =>
    (fun x0 x1 =>
       (fun v1 v2 v3 =>
          (fun dvs =>
  [b0 c0; b1 c1; (acc0 c0 c1) & (acc1 c0 c1);
  (acc0 c0 c1) & (acc1 c0 c1) & (bnlcheck c0 n0 (FΦΦ3 c0 c1 x0 x1 dvs)) & (bnlcheck c1 n1 (FΦΦ3 c0 c1 x0 x1 dvs));
   If (acc0 c0 c1 & acc1 c0 c1) & (bnlcheck c0 n0 (FΦΦ3 c0 c1 x0 x1 dvs)) & (bnlcheck c1 n1 (FΦΦ3 c0 c1 x0 x1 dvs))
   Then ( ＜ ＜ x0, x1, dvs ＞,
            ＜ (Enco0 c0 c1 x0 x1 dvs), (Enco1 c0 c1 x0 x1 dvs), Do (O1 c0 c1 x0 x1 dvs) (O2 c0 c1 x0 x1 dvs) (O3 c0 c1 x0 x1 dvs)＞ ＞)
              Else ⫠]
        ) (dv v1 v2 v3 (S26 c0 c1 x0 x1 v3))
     ) (V1 c0 c1 x0 x1) (V2 c0 c1 x0 x1) (V3 c0 c1 x0 x1)
   ) (encS (msg voter0 c0 c1) rd0) (encS (msg voter1 c0 c1) rd1)) c00 c01)
 ~
 ((fun c0 c1 =>
    (fun x0 x1 =>
      (fun dvs =>
        (fun y0 y1 =>
  [b0 c0; b1 c1; (acc0 c0 c1) & (acc1 c0 c1);
  (acc0 c0 c1) & (acc1 c0 c1) & (bnlcheck c0 n0 (FΦΦ3 c0 c1 x0 x1 dvs)) & (bnlcheck c1 n1 (FΦΦ3 c0 c1 x0 x1 dvs));
   If (acc0 c0 c1 & acc1 c0 c1) & (bnlcheck c0 n0 (FΦΦ3 c0 c1 x0 x1 dvs)) & (bnlcheck c1 n1 (FΦΦ3 c0 c1 x0 x1 dvs))
   Then ( ＜ ＜ x0, x1, dvs ＞,
             ＜ y0, y1 , Do (OO1 c0 c1 y0 y1) (OO2 c0 c1 y0 y1) (OO3 c0 c1 y0 y1)＞ ＞)
   Else ⫠]) (encS (msgo voter1 c0 c1 kc1) rdd0) (encS (msgo voter0 c0 c1 kc0) rdd1))
        ((dv (V1 c0 c1 x0 x1) (V2 c0 c1 x0 x1) (V3 c0 c1 x0 x1)) (S26 c0 c1 x0 x1 (V3 c0 c1 x0 x1))))
      (encS (msg voter1 c0 c1) rd0) (encS (msg voter0 c0 c1) rd1)) c10 c11).
Proof.
  simpl.
  fold (e0 c00 c01 n0) (e1 c00 c01 n1).

(* blinding phase, aka phase2 *)
  pose (Blind_swap). simpl in c.
  fold (b0 c00) (b1 c01) (b0 c10) (b1 c11) in c. (**)
  fold (ti0 c00 c01) (ti1 c10 c11) in c.  (**)
  fold (acc0 c00 c01) (acc1 c10 c11) in c.
    assert (acc c01 t bn1 (t1 [b0 c00; b1 c01]) = acc1 c00 c01). reflexivity. rewrite H in c. clear H. (**)
    assert (acc c10 t bn0 (t0 [b0 c10; b1 c11]) = acc0 c10 c11). reflexivity. rewrite H in c. clear H.
  fold (σ0 c00 c01) (σ1 c10 c11) in c.
    assert (ub c01 t bn1 (t1 [b0 c00; b1 c01]) = σ1 c00 c01). reflexivity. rewrite H in c. clear H. (**)
    assert (ub c10 t bn0 (t0 [b0 c10; b1 c11]) = σ0 c10 c11). reflexivity. rewrite H in c. clear H. (**)

  (* voting phase *)
  apply (@cind_funcapp (fun lx =>
               let sign := Nth 13 lx in
               let σ0 := π1 sign in
               let σ1 := π2 sign in
               let c0 := com vot0 (Nth 0 lx) in
               let c1 := com vot1 (Nth 1 lx) in
               let n0 := Nth 6 lx in
               let n1 := Nth 7 lx in
               let pv0 := (＜c0, σ0, n0＞) in
               let pv1 := (＜c1, σ1, n1＞) in
               let m0 := (＜ pv0, ph2 ＞) in
               let m1 := (＜ pv1, ph2 ＞) in
               let e0 := ❴ m0 ❵_ (Nth 2 lx) ＾ (Nth 4 lx) in
               let e1 := ❴ m1 ❵_ (Nth 2 lx) ＾ (Nth 5 lx) in
               let acc := Nth 12 lx in
               [Nth 10 lx; Nth 11 lx] ++ [ If acc Then e0 Else ⫠; If acc Then e1 Else ⫠] ++ [If acc Then (f2 [(Nth 10 lx);  (Nth 11 lx);  e0;  e1]) Else ⫠] ++
               [If acc Then pv0 Else ⫠; If acc Then pv1 Else ⫠] ++ (firstn 4 lx) ++ [Nth 6 lx; Nth 7 lx; Nth 8 lx; Nth 9 lx; Nth 12 lx])) in c. unfold Nth in c; simpl in c.
  (*  *)
  rewrite (@If_eval (fun acc => ＜ _, π1 If acc Then _ Else _, _ ＞) (fun _ => _)) in c.
  rewrite (@If_eval (fun acc => ＜ _, π1 If acc Then _ Else _, _ ＞) (fun _ => _)) in c.
  rewrite (@If_eval (fun acc => ＜ _, π2 If acc Then _ Else _, _ ＞) (fun _ => _)) in c.
  rewrite (@If_eval (fun acc => ＜ _, π2 If acc Then _ Else _, _ ＞) (fun _ => _)) in c.
  rewrite (@If_eval (fun acc => encS (＜ ＜ _, π1 If acc Then _ Else _, _ ＞, ph2 ＞) _) (fun _ => _)) in c.
  rewrite (@If_eval (fun acc => encS (＜ ＜ _, π1 If acc Then _ Else _, _ ＞, ph2 ＞) _) (fun _ => _)) in c.
  rewrite (@If_eval (fun acc => encS (＜ ＜ _, π2 If acc Then _ Else _, _ ＞, ph2 ＞) _) (fun _ => _)) in c.
  rewrite (@If_eval (fun acc => encS (＜ ＜ _, π2 If acc Then _ Else _, _ ＞, ph2 ＞) _) (fun _ => _)) in c.
  rewrite (@If_eval (fun acc => f2 [_; _; encS (＜ ＜ _, π1 If acc Then _ Else _, _ ＞, ph2 ＞) _; encS (＜ ＜ _, π2 If acc Then _ Else _, _ ＞, ph2 ＞) _]) (fun _ => _)) in c.
  rewrite (@If_eval (fun acc => f2 [_; _; encS (＜ ＜ _, π1 If acc Then _ Else _, _ ＞, ph2 ＞) _; encS (＜ ＜ _, π2 If acc Then _ Else _, _ ＞, ph2 ＞) _]) (fun _ => _)) in c.
  repeat rewrite If_true in c.
  repeat rewrite proj1pair, proj2pair in c.
  fold (pv0 c00 c01 n0) (pv1 c00 c01 n1) (pv0 c10 c11 n0) (pv1 c10 c11 n1) in c.
  fold (m0 c00 c01 n0) (m1 c00 c01 n1) (m0 c10 c11 n0) (m1 c10 c11 n1) in c.
  fold (e0 c00 c01 n0) (e1 c00 c01 n1) (* (e0 c10 c11 n0) (e1 c10 c11 n1) *) in c.
  fold (FΦΦ2 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)) (FΦΦ2 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1)) in c. (*   *)

(* Phase 3 *)
  apply (@cind_funcapp (fun lx =>
               let acc := Nth 15 lx in
               let pv0 := Nth 5 lx in
               let pv1 := Nth 6 lx in
               let e0 := Nth 2 lx in
               let e1 := Nth 3 lx in
               let fΦ2 := Nth 4 lx in
               let sk  := Nth 10 lx in
               let v1 := (Dec [(τ1 (fΦ2)); sk]) in
               let v2 := (Dec [(τ2 (fΦ2)); sk]) in
               let v3 := (Dec [(τ3 (fΦ2)); sk]) in
               let s26 := (If (((τ2 fΦ2) ≟ e0) & ((τ1 fΦ2) ≟ e1)) Then (shufl pv1 pv0 (π1 v3)) Else ⫠) in
               (firstn 4 lx) ++ [If acc Then (If (dist v1 v2 v3) & (pchkv (＜ v1, v2, v3 ＞)) Then s26 Else ⫠) Else (＜ ⫠, ⫠ ＞)] ++
               [If acc Then (f3 [(Nth 0 lx);  (Nth 1 lx);  (Nth 2 lx);  (Nth 3 lx); (If (dist v1 v2 v3) & (pchkv (＜ v1, v2, v3 ＞)) Then s26 Else ⫠)]) Else (＜ ⫠, ⫠ ＞)] ++
               [(Nth 7 lx); (Nth 8 lx); (Nth 9 lx); (Nth 10 lx); (Nth 11 lx); (Nth 12 lx); (Nth 13 lx); (Nth 14 lx); (Nth 15 lx)])) in c.
                 unfold Nth in c; simpl in c.
  (*  *)
  rewrite (@If_eval (fun acc => If dist (decS (τ1 (If acc Then _ Else ⫠))) (decS (τ2 (If acc Then _ Else ⫠))) (decS (τ3 (If acc Then _ Else ⫠))) &
              pchkv (＜ decS (τ1 (If acc Then _ Else ⫠)), decS (τ2 (If acc Then _ Else ⫠)), decS (τ3 (If acc Then _ Else ⫠)) ＞)
           Then If (τ2 (If acc Then _ Else ⫠) ≟ If acc Then _ Else ⫠) & (τ1 (If acc Then _ Else ⫠) ≟ If acc Then _ Else ⫠)
                Then shufl (If acc Then _ Else ⫠) (If acc Then _ Else ⫠) (π1 decS (τ3 (If acc Then _ Else ⫠))) Else ⫠ Else ⫠) (fun _ => _)) in c.
  rewrite (@If_eval (fun acc => If dist (decS (τ1 (If acc Then _ Else ⫠))) (decS (τ2 (If acc Then _ Else ⫠))) (decS (τ3 (If acc Then _ Else ⫠))) &
              pchkv (＜ decS (τ1 (If acc Then _ Else ⫠)), decS (τ2 (If acc Then _ Else ⫠)), decS (τ3 (If acc Then _ Else ⫠)) ＞)
           Then If (τ2 (If acc Then _ Else ⫠) ≟ If acc Then _ Else ⫠) & (τ1 (If acc Then _ Else ⫠) ≟ If acc Then _ Else ⫠)
                Then shufl (If acc Then _ Else ⫠) (If acc Then _ Else ⫠) (π1 decS (τ3 (If acc Then _ Else ⫠))) Else ⫠ Else ⫠) (fun _ => _)) in c.
  rewrite (@If_eval (fun acc => f3 [_ ; _ ; If acc Then _ Else ⫠; If acc Then _ Else ⫠;
                                 If dist (decS (τ1 (If acc Then _ Else ⫠))) (decS (τ2 (If acc Then _ Else ⫠))) (decS (τ3 (If acc Then _ Else ⫠))) &
                pchkv (＜ decS (τ1 (If acc Then _ Else ⫠)), decS (τ2 (If acc Then _ Else ⫠)), decS (τ3 (If acc Then _ Else ⫠)) ＞)
             Then If (τ2 (If acc Then _ Else ⫠) ≟ If acc Then _ Else ⫠) & (τ1 (If acc Then _ Else ⫠) ≟ If acc Then _ Else ⫠)
                  Then shufl (If acc Then _ Else ⫠) (If acc Then _ Else ⫠) (π1 decS (τ3 (If acc Then _ Else ⫠))) Else ⫠ Else ⫠]) (fun _ => _)) in c.
  rewrite (@If_eval (fun acc => f3 [_ ; _ ; If acc Then _ Else ⫠; If acc Then _ Else ⫠;
                                 If dist (decS (τ1 (If acc Then _ Else ⫠))) (decS (τ2 (If acc Then _ Else ⫠))) (decS (τ3 (If acc Then _ Else ⫠))) &
                pchkv (＜ decS (τ1 (If acc Then _ Else ⫠)), decS (τ2 (If acc Then _ Else ⫠)), decS (τ3 (If acc Then _ Else ⫠)) ＞)
             Then If (τ2 (If acc Then _ Else ⫠) ≟ If acc Then _ Else ⫠) & (τ1 (If acc Then _ Else ⫠) ≟ If acc Then _ Else ⫠)
                  Then shufl (If acc Then _ Else ⫠) (If acc Then _ Else ⫠) (π1 decS (τ3 (If acc Then _ Else ⫠))) Else ⫠ Else ⫠]) (fun _ => _)) in c.
  repeat rewrite If_true in c.
  fold (V1 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)) (V2 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)) (V3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)) in c.
  fold (V1 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1))
       (V2 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1))
       (V3 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1)) in c.
  fold (S26 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1) (V3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1))) in c.

(* Attention !!!  Before we fold S26 on the RHS, we have to swap the first and second parameters in the shuffle *)
  rewrite (shufl_perm12 (pv0 c10 c11 n0) (pv1 c10 c11 n1)) in c.

  fold (S26 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1) (V3 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1))) in c.
  fold (dv (V1 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)) (V2 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)) (V3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1))
           (S26 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1) (V3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)))) in c.
  fold (dv (V1 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1))
           (V2 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1))
           (V3 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1))
           (S26 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1) (V3 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1)))) in c.
  fold (FΦΦ3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)
        (dv (V1 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)) (V2 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1))
            (V3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1))
            (S26 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1) (V3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1))))) in c.
  fold (FΦΦ3 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1)
        (dv (V1 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1)) (V2 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1))
            (V3 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1))
            (S26 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1) (V3 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1))))) in c.

(*Phase 5*)
  apply (@cind_funcapp (fun lx =>
               let acc := Nth 14 lx in
               let kc0 := Nth 6 lx in
               let kc1 := Nth 7 lx in
               let c0 := (com vot0 kc0) in
               let c1 := (com vot1 kc1) in
               let n0 := Nth 10 lx in
               let n1 := Nth 11 lx in
               let fΦΦ3 := Nth 5 lx in
               let bnlcheck0 := bnlcheck c0 n0 fΦΦ3 in
               let bnlcheck1 := bnlcheck c1 n1 fΦΦ3 in
               let label0 := (label c0 fΦΦ3) in
               let label1 := (label c1 fΦΦ3) in
               let pkS := Nth 8 lx in
               let rdd0 := Nth 12 lx in
               let rdd1 := Nth 13 lx in
               let enco0 := ( ❴＜＜(label c0 fΦΦ3), kc0 ＞, ph3 ＞❵_pkS ＾ rdd0) in
               let enco1 := ( ❴＜＜(label c1 fΦΦ3), kc1 ＞, ph3 ＞❵_pkS ＾ rdd1) in
               let e0  := Nth 2 lx in
               let e1  := Nth 3 lx in
               let dvs := Nth 4 lx in
               (firstn 2 lx) ++ [acc; If acc Then (bnlcheck0 & bnlcheck1) Else FAlse] ++
               [e0 ; e1; dvs; If acc Then enco0 Else ⫠; If acc Then enco1 Else ⫠ ] ++
               [If acc Then (f5 [(Nth 0 lx);  (Nth 1 lx);  e0;  e1;  dvs ;   enco0;  enco1 ]) Else ⫠] ++
               [(Nth 6 lx); (Nth 7 lx); (Nth 9 lx)])) in c.
                 unfold Nth in c; simpl in c.
  (*  *)
  rewrite (@If_eval (fun acc => bnlcheck _ _ (If acc Then _ Else ＜ ⫠, ⫠ ＞) &
                             bnlcheck _ _ (If acc Then _ Else ＜ ⫠, ⫠ ＞)) (fun _ => _)) in c.
  rewrite (@If_eval (fun acc => bnlcheck _ _ (If acc Then _ Else ＜ ⫠, ⫠ ＞) &
                             bnlcheck _ _ (If acc Then _ Else ＜ ⫠, ⫠ ＞)) (fun _ => _)) in c.
  rewrite (@If_eval (fun acc => encS (＜ ＜ label _ (If acc Then _ Else ＜ ⫠, ⫠ ＞), _ ＞, ph3 ＞) _) (fun _ => _)) in c.
  rewrite (@If_eval (fun acc => encS (＜ ＜ label _ (If acc Then _ Else ＜ ⫠, ⫠ ＞), _ ＞, ph3 ＞) _) (fun _ => _)) in c.
  rewrite (@If_eval (fun acc => encS (＜ ＜ label _ (If acc Then _ Else ＜ ⫠, ⫠ ＞), _ ＞, ph3 ＞) _) (fun _ => _)) in c.
  rewrite (@If_eval (fun acc => encS (＜ ＜ label _ (If acc Then _ Else ＜ ⫠, ⫠ ＞), _ ＞, ph3 ＞) _) (fun _ => _)) in c.

  rewrite (@If_eval (fun acc => f5 [_; _; If acc Then _ Else ⫠; If acc Then _ Else ⫠; If acc Then _ Else ＜ ⫠, ⫠ ＞;
             encS (＜ ＜ label _ (If acc Then _ Else ＜ ⫠, ⫠ ＞), _ ＞, ph3 ＞) _ ;
             encS (＜ ＜ label _ (If acc Then _ Else ＜ ⫠, ⫠ ＞), _ ＞, ph3 ＞) _]) (fun _ => _)) in c.
  rewrite (@If_eval (fun acc => f5 [_; _; If acc Then _ Else ⫠; If acc Then _ Else ⫠; If acc Then _ Else ＜ ⫠, ⫠ ＞;
             encS (＜ ＜ label _ (If acc Then _ Else ＜ ⫠, ⫠ ＞), _ ＞, ph3 ＞) _ ;
             encS (＜ ＜ label _ (If acc Then _ Else ＜ ⫠, ⫠ ＞), _ ＞, ph3 ＞) _]) (fun _ => _)) in c.
  repeat rewrite If_true in c.
  fold (Enco0 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)
                       (dv (V1 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)) (V2 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)) (V3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1))
                           (S26 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1) (V3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)))))
       (Enco1 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)
                       (dv (V1 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)) (V2 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)) (V3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1))
                           (S26 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1) (V3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1))))) in c.
  fold (fΦΦ5 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)
                       (dv (V1 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)) (V2 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)) (V3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1))
                           (S26 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1) (V3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1))))) in c.
  assert (msgo1 c10 c11 kc1 = (＜ ＜ label c11
                    (FΦΦ3 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1)
                       (dv (V1 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1)) (V2 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1))
                          (V3 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1))
                          (S26 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1) (V3 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1))))), kc1 ＞, ph3 ＞)).
    reflexivity. rewrite <- H in c; clear H.
  assert (msgo0 c10 c11 kc0 = (＜ ＜ label c10
                    (FΦΦ3 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1)
                       (dv (V1 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1)) (V2 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1))
                          (V3 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1))
                          (S26 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1) (V3 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1))))), kc0 ＞, ph3 ＞)).
    reflexivity. rewrite <- H in c; clear H.
  assert ((FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1) rdd0) (encS (msgo0 c10 c11 kc0) rdd1)) =
           f5
             [b0 c10; b1 c11; encS (m1 c10 c11 n1) rd0; encS (m0 c10 c11 n0) rd1;
             dv (V1 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1)) (V2 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1))
               (V3 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1))
               (S26 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1) (V3 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1))); encS (msgo1 c10 c11 kc1) rdd0;
             encS (msgo0 c10 c11 kc0) rdd1]).
    reflexivity. rewrite <- H in c; clear H.

  rewrite (AndAsso (acc0 c00 c01) (acc1 c00 c01)) in c.
  rewrite (AndAsso (acc0 c10 c11) (acc1 c10 c11)) in c.


(* Phase 6 *)
  apply (@cind_funcapp (fun lx =>
               let acc := Nth 2 lx in
               let kc0 := Nth 10 lx in
               let kc1 := Nth 11 lx in
               let sk := Nth 12 lx in

               let e0 := Nth 4 lx in
               let e1 := Nth 5 lx in
               let dvs := Nth 6 lx in
               let enco0 := Nth 7 lx in
               let enco1 := Nth 8 lx in
               let fΦΦ5 := Nth 9 lx in

               let o1 := (Dec [(τ1 (fΦΦ5)); sk]) in
               let o2 := (Dec [(τ2 (fΦΦ5)); sk]) in
               let o3 := (Dec [(τ3 (fΦΦ5)); sk]) in
               let dist := (dist o1 o2 o3) in
               let pchko := (pchko (＜ o1, o2, o3 ＞)) in
               let isinkc := (isinkc kc0 kc1 (＜(π2 (π1 o1)), (π2 (π1 o2)), (π2 (π1 o3))＞)) in
               let shufl := (shufl (π1 o1) (π1 o2) (π1 o3)) in
               let Do := (If (dist & pchko & isinkc) Then shufl Else ⫠) in
      (firstn 3 lx) ++ [Nth 3 lx; If acc Then ＜ ＜ e0, e1, dvs ＞,  ＜ enco0 , enco1 , Do  ＞ ＞ Else ⫠])) in c.
                 unfold Nth in c; simpl in c.
  (*  *)
  rewrite (@If_eval (fun acc => ＜ ＜ If acc Then _ Else ⫠, If acc Then _ Else ⫠,  If acc Then _ Else ＜ ⫠, ⫠ ＞ ＞,
           ＜ If acc Then _ Else ⫠, If acc Then _ Else ⫠,
           If dist (decS (τ1 (If acc Then _ Else ⫠)))  (decS (τ2 (If acc Then _ Else ⫠))) (decS (τ3 (If acc Then _ Else ⫠))) &
              pchko (＜ decS (τ1 (If acc Then _ Else ⫠)), decS (τ2 (If acc Then _ Else ⫠)), decS (τ3 (If acc Then _ Else ⫠)) ＞) &
              isinkc kc0 kc1 (＜ π2 (π1 decS (τ1 (If acc Then _ Else ⫠))), π2 (π1 decS (τ2 (If acc Then _ Else ⫠))), π2 (π1 decS (τ3 (If acc Then _ Else ⫠))) ＞)
           Then shufl
                  (π1 decS (τ1 (If acc Then _ Else ⫠)))
                  (π1 decS (τ2 (If acc Then _ Else ⫠)))
                  (π1 decS (τ3 (If acc Then _ Else ⫠))) Else ⫠ ＞ ＞) (fun _ => _)) in c.

  rewrite (@If_eval (fun acc => ＜ ＜ If acc Then _ Else ⫠, If acc Then _ Else ⫠, If acc Then _ Else  ＜ ⫠, ⫠ ＞ ＞,
           ＜ If acc Then _ Else ⫠, If acc Then _ Else ⫠,
           If dist (decS (τ1 (If acc Then _ Else ⫠))) (decS (τ2 (If acc Then _ Else ⫠))) (decS (τ3 (If acc Then _ Else ⫠))) &
              pchko (＜ decS (τ1 (If acc Then _ Else ⫠)), decS (τ2 (If acc Then _ Else ⫠)), decS (τ3 (If acc Then _ Else ⫠)) ＞) &
              isinkc kc1 kc0 (＜ π2 (π1 decS (τ1 (If acc Then _ Else ⫠))),  π2 (π1 decS (τ2 (If acc Then _ Else ⫠))),  π2 (π1 decS (τ3 (If acc Then _ Else ⫠))) ＞)
           Then shufl (π1 decS (τ1 (If acc Then _ Else ⫠))) (π1 decS (τ2 (If acc Then _ Else ⫠))) (π1 decS (τ3 (If acc Then _ Else ⫠))) Else ⫠ ＞ ＞ ) (fun _ => _)) in c.
  repeat rewrite If_true in c.
  fold (O1 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)
            (dv (V1 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)) (V2 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)) (V3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1))
                (S26 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1) (V3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)))))
       (O2 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)
            (dv (V1 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)) (V2 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)) (V3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1))
                (S26 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1) (V3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)))))
       (O3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)
            (dv (V1 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)) (V2 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)) (V3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1))
               (S26 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1) (V3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)))))in c.
  fold (OO1 c10 c11 (encS (msgo1 c10 c11 kc1) rdd0) (encS (msgo0 c10 c11 kc0) rdd1))
       (OO2 c10 c11 (encS (msgo1 c10 c11 kc1) rdd0) (encS (msgo0 c10 c11 kc0) rdd1))
       (OO3 c10 c11 (encS (msgo1 c10 c11 kc1) rdd0) (encS (msgo0 c10 c11 kc0) rdd1)) in c.
  fold (Do
         (O1 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)
            (dv (V1 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)) (V2 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)) (V3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1))
               (S26 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1) (V3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)))))
         (O2 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)
            (dv (V1 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)) (V2 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)) (V3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1))
               (S26 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1) (V3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)))))
         (O3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)
            (dv (V1 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)) (V2 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)) (V3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1))
                (S26 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1) (V3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)))))) in c.

(* Attention!!! we change from {isinkc kc1 kc0 ...} to {isinkc kc0 kc1 ...} on the Right Hand Side *)
  rewrite <- isinkc_kc_swap in c.

  fold (Do (OO1 c10 c11 (encS (msgo1 c10 c11 kc1) rdd0) (encS (msgo0 c10 c11 kc0) rdd1)) (OO2 c10 c11 (encS (msgo1 c10 c11 kc1) rdd0) (encS (msgo0 c10 c11 kc0) rdd1))
         (OO3 c10 c11 (encS (msgo1 c10 c11 kc1) rdd0) (encS (msgo0 c10 c11 kc0) rdd1))) in c.

(*  *)
  apply (@cind_funcapp (fun lx => (firstn 4 lx) ++ [ If (Nth 3 lx) Then (Nth 4 lx ) Else ⫠ ])) in c. unfold Nth in c; simpl in c. (**)
  rewrite <-(AndAsso (acc0 c00 c01)) in c at 2.
  rewrite (@If_morph (fun x => If x Then If (acc0 c00 c01 & acc1 c00 c01) Then _ Else _ Else ⫠)) in c.
  rewrite If_false in c.
  rewrite (@If_eval (fun x => If _ & _ Then (If x Then ＜ ＜ _ , _,_ ＞,  ＜ _ , _ , _ ＞ ＞ Else ⫠ ) Else ⫠ ) (fun _ => _)) in c.
  rewrite If_true in c.
  pose (protocol := (fun x0 x1 => (fun dvs => (fun enco0 enco1 =>
                                           (＜ ＜ x0, x1, dvs ＞,
                                           ＜ enco0, enco1, Do (O1 c00 c01 x0 x1 dvs) (O2 c00 c01 x0 x1 dvs) (O3 c00 c01 x0 x1 dvs) ＞ ＞))
                                          (Enco0 c00 c01 x0 x1 dvs) (Enco1 c00 c01 x0 x1 dvs))
                                 (dv (V1 c00 c01 x0 x1) (V2 c00 c01 x0 x1) (V3 c00 c01 x0 x1) (S26 c00 c01 x0 x1 (V3 c00 c01 x0 x1))))
                      (e0 c00 c01 n0) (e1 c00 c01 n1)). simpl in protocol. fold protocol in c. fold protocol.
  rewrite <- (@If_false protocol ⫠ ) in c at 2.
  pose (@If_morph (fun x => If x Then protocol Else ⫠) (acc0 c00 c01 & acc1 c00 c01)
                (bnlcheck c00 n0
                (FΦΦ3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)
                   (dv (V1 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)) (V2 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)) (V3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1))
                      (S26 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1) (V3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1))))) &
                 bnlcheck c01 n1
                (FΦΦ3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)
                   (dv (V1 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)) (V2 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)) (V3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1))
                      (S26 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1) (V3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1))))))
                   (FAlse)) as d. simpl in d.
  rewrite <- d in c. clear d.

(*  *)
  rewrite c; clear c.

(* Attention !!! we use the symmetry of "&" on the Right Hand Side to swap {bnlcheck c11 ...} and {bnlcheck c10 ...} *)
  rewrite (AndComm (bnlcheck c11 n1 _)).

(*  *)
  rewrite <- (AndAsso (acc0 c10 c11)) at 2.
  rewrite (@If_morph (fun x => If x Then If acc0 c10 c11 & acc1 c10 c11 Then _ Else _ Else ⫠)).
  rewrite If_false.
  rewrite (@If_eval (fun x =>  If _ & _ Then If x Then _ Else ⫠ Else ⫠) (fun _ => _)).
  rewrite If_true.

  rewrite (@If_morph (fun x => If x Then ＜ _, _ ＞ Else ⫠) (acc0 c10 c11 & acc1 c10 c11)).
  rewrite If_false.

(*  *)
  reflexivity.


(*  *)
  clear protocol.
  3 ,8 ,10, 13, 15, 18, 22, 28, 31, 34, 37, 40, 43, 47, 50, 53, 56, 60, 63, 65, 66, 69, 71, 72, 74, 75, 77, 78, 80, 81, 83, 84, 86, 87: ProveContext.
  3, 8 , 11, 13, 16, 19, 21, 23, 25, 27, 29, 31, 34, 36, 38, 40, 43, 45, 46, 48, 49, 50, 51, 52, 53, 54 :  try ( Provebool; unfold acc1; ProveboolandContext).
  4, 5 : unfold bnlcheck; ProveboolandContext; unfold ncheck; unfold isin; ProveboolandContext.
  11, 24, 25, 26 : ProveContext.
  8: { apply @cApp. ProveContext. simpl. ProveContext.  }
  16 : { apply @cApp. ProveContext. apply @cApp. ProveContext. apply @cApp. ProveContext. apply @cApp. ProveContext. simpl. ProveContext.  }
  20 : { apply @cApp. ProveContext. apply @cApp. ProveContext. apply @cApp. ProveContext. ProveContext.  }
  20 : { apply @cApp. ProveContext. apply @cApp. ProveContext. apply @cApp. ProveContext. apply @cApp. ProveContext. apply @cApp. ProveContext. ProveContext.  }

  pose prop26_13_blinding_FΦΦ3_cnxt; pose prop26_13_blinding_FFΦΦ5_cnxt; time ProveContext. (* 6.146 secs *)
  pose prop26_13_blinding_FΦΦ3_cnxt; pose prop26_13_blinding_FFΦΦ5_cnxt; time ProveContext. (* 10.426 secs *)
  pose prop26_13_blinding_FΦΦ3_cnxt; pose prop26_13_blinding_FFΦΦ5_cnxt; time ProveContext. (* 5.154 secs *)
  clear c.
  pose prop26_13_blinding_FΦΦ3_cnxt'; pose prop26_13_blinding_FFΦΦ5_cnxt'; time ProveContext. (* 9.405 secs *)
  pose prop26_13_blinding_FΦΦ3_cnxt'; pose prop26_13_blinding_FFΦΦ5_cnxt'; time ProveContext. (* 12.545 secs  *)
  clear c.
  pose prop26_13_blinding_FΦΦ3_cnxt; pose prop26_13_blinding_FFΦΦ5_cnxt; time ProveContext. (* 5.85 secs *)
  clear c.
  pose prop26_13_blinding_FΦΦ3_cnxt'; pose prop26_13_blinding_FFΦΦ5_cnxt'; time ProveContext. (* 8.864 secs *)
  clear c.
  pose prop26_13_blinding_FΦΦ3_cnxt; pose prop26_13_blinding_FFΦΦ5_cnxt; time ProveContext. (* 5.263 secs *)
  clear c; pose prop26_13_blinding_FΦΦ3_cnxt'; pose prop26_13_blinding_FFΦΦ5_cnxt'; time ProveContext. (* 9.765 secs *)
  pose prop26_13_blinding_FΦΦ3_cnxt; pose prop26_13_blinding_FFΦΦ5_cnxt; time ProveContext. (* 0.814 secs *)
  pose prop26_13_blinding_FΦΦ3_cnxt; pose prop26_13_blinding_FFΦΦ5_cnxt; time ProveContext. (* 0.976 secs  *)
  clear c.
  pose prop26_13_blinding_FΦΦ3_cnxt'; time ProveContext. (* 0.613 secs *)
  clear c.
  pose prop26_13_blinding_FΦΦ3_cnxt'; time ProveContext. (* 0.655 secs *)
  clear c.
  pose prop26_13_blinding_FΦΦ3_cnxt; time ProveContext. (* 0.655 secs *)
  clear c.
  pose prop26_13_blinding_FΦΦ3_cnxt'; time ProveContext. (* 4.514 secs *)
  all : clear c; time ProveContext. (*11.57 secs*)
Qed.



(****************************************************)
(*--- Final proposition                          ---*)
(****************************************************)


(**)
Lemma prop26_formula13 :
  (fun c0 c1 =>
     (fun enco0 enco1 =>
        (fun o1 o2 o3 =>
           [b0 c0; b1 c1; acc0 c0 c1 & acc1 c0 c1;
           acc0 c0 c1 & acc1 c0 c1 & bnlcheck c0 n0 (fΦΦ3 c0 c1) & bnlcheck c1 n1 (fΦΦ3 c0 c1);
           If (acc0 c0 c1 & acc1 c0 c1) & bnlcheck c0 n0 (fΦΦ3 c0 c1) & bnlcheck c1 n1 (fΦΦ3 c0 c1)
              Then (＜ ＜ e0 c0 c1 n0, e1 c0 c1 n1, dv (v1 c0 c1) (v2 c0 c1) (v3 c0 c1) (s26 c0 c1 (v3 c0 c1)) ＞, ＜ enco0, enco1, Do o1 o2 o3 ＞ ＞)
              Else ⫠]
        )(FGO1 c0 c1 enco0 enco1) (FGO2 c0 c1 enco0 enco1) (FGO3 c0 c1 enco0 enco1)
     ) (enco0 c0 c1 kc0) (enco1 c0 c1 kc1)
  ) (c0 lhs) (c1 lhs)
~
  (fun c0 c1 =>
     (fun enco0 enco1 =>
        (fun o1 o2 o3 =>
           [b0 c0; b1 c1; acc0 c0 c1 & acc1 c0 c1;
           acc0 c0 c1 & acc1 c0 c1 & bnlcheck c0 n0 (fΦΦ3 c0 c1) & bnlcheck c1 n1 (fΦΦ3 c0 c1);
           If (acc0 c0 c1 & acc1 c0 c1) & bnlcheck c0 n0 (fΦΦ3 c0 c1) & bnlcheck c1 n1 (fΦΦ3 c0 c1)
              Then (＜ ＜ e0 c0 c1 n0, e1 c0 c1 n1, dv (v1 c0 c1) (v2 c0 c1) (v3 c0 c1) (s26 c0 c1 (v3 c0 c1)) ＞, ＜ enco0, enco1, Do o1 o2 o3 ＞ ＞)
              Else ⫠]
        ) (FGO1 c0 c1 enco0 enco1) (FGO2 c0 c1 enco0 enco1) (FGO3 c0 c1 enco0 enco1)
     ) (enco0 c0 c1 kc0) (enco1 c0 c1 kc1)
  ) (c0 rhs) (c1 rhs).
Proof.
(*  *)
  intros. simpl.

(* rewrite prop26_13_swap_m0_m1 ONLY on the Right Hand Side *)
  rewrite (prop26_13_swap_m0_m1).

(* rewrite prop26_13_swap_enco0_enco1 ONLY on the Right Hand Side *)
  rewrite (prop26_13_swap_enco0_enco1).

(* rewrite prop26_13_swap_c10_c11_blinding ONLY on one of the two sides  *)
  rewrite (prop26_13_swap_c10_c11_blinding).

  (**)
  reflexivity.
Qed.

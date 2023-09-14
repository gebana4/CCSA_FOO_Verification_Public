(************************************************************************)
(* Copyright (c) 2022, Gergei Bana, Rohit Chadha, Ajay Kumar Eeralla,   *)
(* Qianli Zhang                                                         *)
(*                                                                      *)
(* This work is licensed under the MIT license. The license is          *)
(* described in the file "LICENSE" available at the root of the source  *)
(* or at https://opensource.org/licenses/MIT                            *)
(************************************************************************)
 

Require Import Coq.micromega.Lia.
Require Export lemma26_13.
Require Export lemma26_14.
Require Export lemma26_15.
Require Export lemma26_16.
Import ListNotations.

(*  *)
Lemma lemma26_helper:  forall acc0acc1 bnl0 bnl1 case0 case1 case2 case3,
    bppt acc0acc1 ->
    bppt bnl0 ->
    bppt bnl1 -> 
  If acc0acc1 Then
     If bnl0
        Then If bnl1 Then case0
                     Else case1
        Else If bnl1 Then case2
                     Else case3 Else ⫠
 = 
        If acc0acc1 &  bnl0 &  bnl1 Then If acc0acc1 & bnl0 &  bnl1 Then case0 Else ⫠
   Else If acc0acc1 &  bnl0 & !bnl1 Then If acc0acc1 Then case1 Else ⫠
   Else If acc0acc1 & !bnl0 &  bnl1 Then If acc0acc1 Then case2 Else ⫠
   Else If acc0acc1 & !bnl0 & !bnl1 Then If acc0acc1 Then case3 Else ⫠ Else ⫠.
Proof.
  intros.
  rewrite AndComp.
  rewrite (@If_eval (fun acc => If bnl0
       Then If bnl1 Then If acc & bnl0 & bnl1 Then case0 Else ⫠
            Else If acc & bnl0 & ! bnl1 Then If acc Then case1 Else ⫠
                 Else If acc & ! bnl0 & bnl1 Then If acc Then case2 Else ⫠ Else If acc & ! bnl0 & ! bnl1 Then If acc Then case3 Else ⫠ Else ⫠
       Else If acc & bnl0 & ! bnl1 Then If acc Then case1 Else ⫠
            Else If acc & ! bnl0 & bnl1 Then If acc Then case2 Else ⫠ Else If acc & ! bnl0 & ! bnl1 Then If acc Then case3 Else ⫠ Else ⫠)
          (fun acc => If acc & bnl0 & ! bnl1 Then If acc Then case1 Else ⫠
       Else If acc & ! bnl0 & bnl1 Then If acc Then case2 Else ⫠ Else If acc & ! bnl0 & ! bnl1 Then If acc Then case3 Else ⫠ Else ⫠)).
  repeat rewrite If_false. repeat rewrite If_true.
  rewrite (@If_eval (fun bnl0 =>If bnl1 Then  If bnl0 & bnl1 Then case0 Else ⫠ Else If bnl0 & ! bnl1 Then case1 Else If ! bnl0 & bnl1 Then case2 Else If ! bnl0 & ! bnl1 Then case3 Else ⫠)
          (fun bnl0 => If bnl0 & ! bnl1 Then case1 Else If ! bnl0 & bnl1 Then case2 Else If ! bnl0 & ! bnl1 Then case3 Else ⫠)).
  repeat rewrite If_true. repeat rewrite If_false.
  rewrite (@If_eval (fun bnl1 => If bnl1 Then case0 Else ⫠ ) (fun bnl1 => If ! bnl1 Then case1 Else ⫠)).
  repeat rewrite If_false. repeat rewrite If_true.
  rewrite (@If_eval (fun bnl1 => _ ) (fun bnl1 => If ! bnl1 Then case3 Else ⫠)).
  repeat rewrite If_false. repeat rewrite If_true.

  reflexivity.

  all : ProveboolandContext.
Qed.


(**)
Proposition lemma26 :
  (fun c0 c1 =>
     (fun enco0 enco1 =>
        (fun o1 o2 o3 =>
           [b0 c0; b1 c1;
           If (acc0 c0 c1 & acc1 c0 c1)
              Then (＜ ＜ e0 c0 c1 n0, e1 c0 c1 n1, dv (v1 c0 c1) (v2 c0 c1) (v3 c0 c1) (s26 c0 c1 (v3 c0 c1)) ＞, ＜ enco0, enco1, Do o1 o2 o3 ＞ ＞)
              Else ⫠]
        )(FGO1 c0 c1 enco0 enco1) (FGO2 c0 c1 enco0 enco1) (FGO3 c0 c1 enco0 enco1)
     ) (If (bnlcheck c0 n0 (fΦΦ3 c0 c1)) Then (enco0 c0 c1 kc0) Else ⫠) (If (bnlcheck c1 n1 (fΦΦ3 c0 c1)) Then (enco1 c0 c1 kc1) Else ⫠)
  ) (c0 lhs) (c1 lhs)
~
  (fun c0 c1 =>
     (fun enco0 enco1 =>
        (fun o1 o2 o3 =>
           [b0 c0; b1 c1;
           If (acc0 c0 c1 & acc1 c0 c1)
              Then (＜ ＜ e0 c0 c1 n0, e1 c0 c1 n1, dv (v1 c0 c1) (v2 c0 c1) (v3 c0 c1) (s26 c0 c1 (v3 c0 c1)) ＞, ＜ enco0, enco1, Do o1 o2 o3 ＞ ＞)
              Else ⫠]
        ) (FGO1 c0 c1 enco0 enco1) (FGO2 c0 c1 enco0 enco1) (FGO3 c0 c1 enco0 enco1)
     ) (If (bnlcheck c0 n0 (fΦΦ3 c0 c1)) Then (enco0 c0 c1 kc0) Else ⫠) (If (bnlcheck c1 n1 (fΦΦ3 c0 c1)) Then (enco1 c0 c1 kc1) Else ⫠)
  ) (c0 rhs) (c1 rhs).
Proof.
  intros. simpl.

  
(* we case analysis bnlcheck0 and bnlcheck1 before the encryptions. 
   When both bnlcheck0 and bnlcheck1 are true, both encryptions will be sent out by the voter.
   When only one bnlcheck is true, the corresponding one encryption will be sent out.
   When none of the bnlcheck is true, none of the encryption will be sent out. *)
  
  rewrite (GuardAhead (＜ _,  _ ＞) (bnlcheck c00 n0 (fΦΦ3 c00 c01)) (bnlcheck c01 n1 (fΦΦ3 c00 c01))).
  rewrite (GuardAhead (＜ ＜ e0 c10 c11 n0, _ , _ ＞,  _ ＞) (bnlcheck c10 n0 (fΦΦ3 c10 c11)) (bnlcheck c11 n1 (fΦΦ3 c10 c11))).
  repeat rewrite (@If_eval (fun bnl1 => ＜ ＜ _ , _, _＞, ＜ _, ( If bnl1 Then _ Else ⫠) ,
                     Do (FGO1 _ _ _ (If bnl1 Then  _ Else ⫠))  (FGO2 _ _ _ (If bnl1 Then  _ Else ⫠)) (FGO3 _ _ _ (If bnl1 Then _ Else ⫠)) ＞ ＞)
           (fun bnl1 => ＜ ＜ _ , _, _＞, ＜ _, ( If bnl1 Then _ Else ⫠),
                     Do (FGO1 _ _ _ (If bnl1 Then  _ Else ⫠))  (FGO2 _ _ _ (If bnl1 Then  _ Else ⫠)) (FGO3 _ _ _ (If bnl1 Then _ Else ⫠)) ＞ ＞)).
  repeat rewrite If_true, If_false.    
  repeat rewrite (@If_eval (fun bnl0 =>  If _ Then ＜ ＜ _ , _, _＞, ＜ ( If bnl0 Then _ Else ⫠), _ ,
                               Do (FGO1 _ _ ( If bnl0 Then _ Else ⫠) _)  (FGO2 _ _ ( If bnl0 Then _ Else ⫠) _) (FGO3 _ _ ( If bnl0 Then _ Else ⫠) _) ＞ ＞
                                    Else ＜ ＜ _ , _, _＞, ＜ ( If bnl0 Then _ Else ⫠), _ ,
                               Do (FGO1 _ _ ( If bnl0 Then _ Else ⫠) _)  (FGO2 _ _ ( If bnl0 Then _ Else ⫠) _) (FGO3 _ _ ( If bnl0 Then _ Else ⫠) _) ＞ ＞)
           (fun bnl0 =>  If _ Then ＜ ＜ _ , _, _＞, ＜ ( If bnl0 Then _ Else ⫠), _ ,
                               Do (FGO1 _ _ ( If bnl0 Then _ Else ⫠) _)  (FGO2 _ _ ( If bnl0 Then _ Else ⫠) _) (FGO3 _ _ ( If bnl0 Then _ Else ⫠) _) ＞ ＞
                                    Else ＜ ＜ _ , _, _＞, ＜ ( If bnl0 Then _ Else ⫠), _ ,
                               Do (FGO1 _ _ ( If bnl0 Then _ Else ⫠) _)  (FGO2 _ _ ( If bnl0 Then _ Else ⫠) _) (FGO3 _ _ ( If bnl0 Then _ Else ⫠) _) ＞ ＞)).
  repeat rewrite If_true, If_false.
  
  
(* In Lemma26_13, we proved that if both encryptions are sent out by the challenger, 
   then the protocol will be indistinguishable from adversary's perspective *)
  
  rewrite (lemma26_helper (acc0 c00 c01 & acc1 c00 c01)).
  rewrite (lemma26_helper (acc0 c10 c11 & acc1 c10 c11)).
  apply (@IF_branch' [b0 c00; b1 c01] [b0 c10; b1 c11] _ _ _ _ _ _ ); simpl.
  repeat rewrite (AndAsso).
  pose (prop26_formula13) as c; simpl in c.
  repeat rewrite (AndAsso) in c.
  apply (@cind_funcapp (fun lx => (firstn 2 lx) ++ [Nth 3 lx; Nth 4 lx ])) in c; unfold Nth in c; simpl in c.
  apply c. clear c.
  ProveContext.

  
(*Lemma26_14*)

  apply (@IF_branch' [b0 c00; b1 c01; (acc0 c00 c01 & acc1 c00 c01) & bnlcheck c00 n0 (fΦΦ3 c00 c01) & bnlcheck c01 n1 (fΦΦ3 c00 c01)]
                     [b0 c10; b1 c11; (acc0 c10 c11 & acc1 c10 c11) & bnlcheck c10 n0 (fΦΦ3 c10 c11) & bnlcheck c11 n1 (fΦΦ3 c10 c11)] _ _ _ _ _ _ ); simpl.
  pose (prop26_formula14) as c; simpl in c.
  apply (@cind_funcapp (fun lx => let acc := Nth 2 lx in
                               let bnl0 := Nth 3 lx in
                               let bnl1 := Nth 4 lx in
                               let case1 := Nth 5 lx in
                          (firstn 2 lx) ++ [acc & bnl0 & bnl1; acc & bnl0 & ! bnl1 ; If acc Then case1 Else ⫠])) in c; unfold Nth in c; simpl in c.
  apply c; clear c.
  apply @cApp; ProveContext.

  
(*Lemma26_15*)

  apply (@IF_branch' [b0 c00; b1 c01; (acc0 c00 c01 & acc1 c00 c01) & bnlcheck c00 n0 (fΦΦ3 c00 c01) & bnlcheck c01 n1 (fΦΦ3 c00 c01);
                      (acc0 c00 c01 & acc1 c00 c01) & bnlcheck c00 n0 (fΦΦ3 c00 c01) & ! bnlcheck c01 n1 (fΦΦ3 c00 c01)]
                     [b0 c10; b1 c11; (acc0 c10 c11 & acc1 c10 c11) & bnlcheck c10 n0 (fΦΦ3 c10 c11) & bnlcheck c11 n1 (fΦΦ3 c10 c11);
                      (acc0 c10 c11 & acc1 c10 c11) & bnlcheck c10 n0 (fΦΦ3 c10 c11) & ! bnlcheck c11 n1 (fΦΦ3 c10 c11)] _ _ _ _ _ _ ); simpl.
  pose (prop26_formula15) as c; simpl in c.
  apply (@cind_funcapp (fun lx => let acc := Nth 2 lx in
                               let bnl0 := Nth 3 lx in
                               let bnl1 := Nth 4 lx in
                               let case2 := Nth 5 lx in
                          (firstn 2 lx) ++ [acc & bnl0 & bnl1; acc & bnl0 & ! bnl1 ; acc & !bnl0 & bnl1 ; If acc Then case2 Else ⫠])) in c; unfold Nth in c; simpl in c.
  apply c; clear c.
  apply @cApp; ProveContext.

  
(* In Lemma26_16, we proved that if none of the encryptions is sent out, 
   then because of the hiding property, the protocol will still be indistinguishable *)
  
  pose (prop26_formula16) as c; simpl in c.
  apply (@cind_funcapp (fun lx => let acc := Nth 2 lx in
                               let bnl0 := Nth 3 lx in
                               let bnl1 := Nth 4 lx in
                               let case3 := Nth 5 lx in
                               (firstn 2 lx) ++ [acc & bnl0 & bnl1; acc & bnl0 & ! bnl1 ; acc & !bnl0 & bnl1 ; If acc & !bnl0 & !bnl1 Then If acc Then case3 Else ⫠ Else ⫠ ])) in c;
    unfold Nth in c; simpl in c.
  apply c.
  apply @cApp; ProveContext.


(**)
  all : unfold bnlcheck; unfold ncheck; unfold isin; unfold acc0, acc1; Provebool.

  1, 2: pose lemma26_bnl0_Φ3_Cnxt_rhs; pose lemma26_bnl0_bot_Φ5_Cnxt_rhs; pose lemma26_bnl0_enco1_Φ5_Cnxt_rhs; time ProveContext. (* 9.698 secs *)
  1, 2: pose lemma26_bnl0_Φ3_Cnxt_lhs; pose lemma26_bnl0_bot_Φ5_Cnxt_lhs; pose lemma26_bnl0_enco1_Φ5_Cnxt_lhs; time ProveContext. (* 9.806 secs*)
  1, 2: pose lemma26_bnl0_Φ3_Cnxt_rhs; pose lemma26_bnl1_enco0_Φ5_Cnxt_rhs; time ProveContext. (* 10.968 secs *)
  1, 2: pose lemma26_bnl0_Φ3_Cnxt_lhs; pose lemma26_bnl1_enco0_Φ5_Cnxt_lhs; time ProveContext. (* 11.148 secs *)
Qed.

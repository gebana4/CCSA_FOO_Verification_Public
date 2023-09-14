(************************************************************************)
(* Copyright (c) 2022, Gergei Bana, Qianli Zhang                        *)
(*                                                                      *)
(* This work is licensed under the MIT license. The license is          *)
(* described in the file "LICENSE" available at the root of the source  *)
(* or at https://opensource.org/licenses/MIT                            *)
(*                                                                      *)
(* Special thanks to Dr. Eeralla                                        *)
(************************************************************************)


Require Import Coq.micromega.Lia.
Require Export auxiliary.
Import ListNotations.


(*  *)
Ltac UnfoldDef := try match goal with
                        [ |- CCA2AfterEncTerm _ _ _ Error _ _ (fun _ : ppt => ?X) ] => try unfold X
                      | [ |- PPT _ (fun _ : _ => ?X)] => try unfold X
                      | [ |- Freshc _ ?X] => try unfold X end.


(*   *)
Ltac ProveFreshC :=
  repeat
   ( auto;
     match goal with
     | |- ?c1 <<< ?c2 => ProveHag; auto
     | |- PPT ?hag ?f => ProvePPT; auto
     | |- Context ?hag ?tol ?f => ProveContext; auto
     | |- ContextTerm ?hag ?tol ?f => ProveContext; auto
     | |- Fresh _ _ => ProveFresh; auto
     | |- FreshTerm _ _ => ProveFresh; auto

     | |- Freshc _  (fun _ => []) => apply frcnil
     | |- Freshc _  (fun _ => _ :: _ ) => apply frcConc

     | |- FreshTermc _  (fun _ => nonce _ ) => apply frtcNN; lia
     | |- FreshTermc _  (fun _ => ConstInt ?f ?g ) => try (apply frtcCAdv; ProveContext)
     | |- FreshTermc _  ( Nth _ )=> try (apply frtcCAdv; ProveContext)

     | |- FreshTermc _  (fun _ => ?f _)=> first [apply frtcFAdv; ProveContext | unfold f]
     | |- FreshTermc _  (fun _ => ?f _ _)=> first [apply frtcFAdv; ProveContext | unfold f]
     | |- FreshTermc _  (fun _ => ?f _ _ _)=> first [apply frtcFAdv; ProveContext | unfold f]
     | |- FreshTermc _  (fun _ => ?f _ _ _ _)=> first [apply frtcFAdv; ProveContext | unfold f]
     | |- FreshTermc _  (fun _ => ?f _ _ _ _ _)=> first [apply frtcFAdv; ProveContext | unfold f]
     | |- FreshTermc _  (fun _ => ?f _ _ _ _ _ _)=> first [apply frtcFAdv; ProveContext | unfold f]
     | |- FreshTermc _  (fun _ => ?f _ _ _ _ _ _ _)=> first [apply frtcFAdv; ProveContext | unfold f]
     | |- FreshTermc _  ?c => first [apply frtcCAdv; ProveContext | unfold c]

     | |- Freshc _  (fun x => x)  => apply frcCAdv; ProveContext
     end).


Ltac ProveFreshCTerm :=
  repeat
   ( auto;
     match goal with
     | |- Nonce nonce ?n => unfold Nonce; exists n; auto
     | |- ?c1 <<< ?c2 => ProveHag; auto
     | |- PPT ?hag ?f => ProvePPT; auto
     | |- Context ?hag ?tol ?f => ProveContext; auto
     | |- ContextTerm ?hag ?tol ?f => ProveContext; auto
     | |- Fresh _ _ => ProveFresh; auto
     | |- FreshTerm _ _ => ProveFresh; auto

     | |- FreshcTerm _  (fun _ => []) => apply frctnil
     | |- FreshcTerm _  (fun _ => _ :: _ ) => apply frctConc

     | |- FreshTermcTerm _  (fun _ => nonce _ ) => apply frtctNN; lia
     | |- FreshTermcTerm _  (fun _ => ConstInt ?f ?g ) => try (apply frtctCAdv; ProveContext)
     | |- FreshTermcTerm _  ( Nth _ )=> try (apply frtctCAdv; ProveContext)

     | |- FreshTermcTerm _  (fun _ => ?f _)=> first [apply frtctFAdv; ProveContext | unfold f]
     | |- FreshTermcTerm _  (fun _ => ?f _ _)=> first [apply frtctFAdv; ProveContext | unfold f]
     | |- FreshTermcTerm _  (fun _ => ?f _ _ _)=> first [apply frtctFAdv; ProveContext | unfold f]
     | |- FreshTermcTerm _  (fun _ => ?f _ _ _ _)=> first [apply frtctFAdv; ProveContext | unfold f]
     | |- FreshTermcTerm _  (fun _ => ?f _ _ _ _ _)=> first [apply frtctFAdv; ProveContext | unfold f]
     | |- FreshTermcTerm _  (fun _ => ?f _ _ _ _ _ _)=> first [apply frtctFAdv; ProveContext | unfold f]
     | |- FreshTermcTerm _  (fun _ => ?f _ _ _ _ _ _ _)=> first [apply frtctFAdv; ProveContext | unfold f]

     | |- FreshTermcTerm _  (fun x => x)  => apply frtctCAdv; ProveContext
     | |- FreshTermcTerm _  (?f _)=> first [apply frtctFAdv; ProveContext | unfold f]
     | |- FreshTermcTerm _  (?f _ _)=> first [apply frtctFAdv; ProveContext | unfold f]
     | |- FreshTermcTerm _  (?f _ _ _)=> first [apply frtctFAdv; ProveContext | unfold f]
     | |- FreshTermcTerm _  (?f _ _ _ _)=> first [apply frtctFAdv; ProveContext | unfold f]
     | |- FreshTermcTerm _  (?f _ _ _ _ _)=> first [apply frtctFAdv; ProveContext | unfold f]
     | |- FreshTermcTerm _  (?f _ _ _ _ _ _)=> first [apply frtctFAdv; ProveContext | unfold f]
     | |- FreshTermcTerm _  (?f _ _ _ _ _ _ _)=> first [apply frtctFAdv; ProveContext | unfold f]
     | |- FreshTermcTerm _  ?c => first [apply frtcCAdv; ProveContext | unfold c]

     end).


(*   *)
Ltac ProveCca2Before :=
  repeat
   (intros; auto;
    match goal with
     | |- CCA2BeforeEncTerm _ ?Pk _ ?X _ (?Pk ?X) => apply CCA2Pkey
     | |- CCA2BeforeEncTerm _ _ _ _ _ nonce (_) => apply CCA2AttNonceTerm; ProveFresh; try lia
     | |- CCA2BeforeEncTerm ?D _ ?Sk ?X _ (?D [_; ?Sk ?X]) => apply CCA2DecOrac1
     | |- CCA2BeforeEncTerm _ _ _ _ _ ?X => try unfold X; first [ first [apply CCA2DecOrac1 | apply CCA2AttContListTerm; ProvePPT]
                                                             |  apply CCA2AttContListTerm with (f := fun _ => X) (tl := []); ProvePPT ] (*  *)
     | |- CCA2BeforeEnc _ _ _ _ _ (_ :: _) => try apply CCA2BeforeTermList
     | |- CCA2BeforeEnc _ _ _ _ _ [] => try apply CCA2BeforeTermNil
     end).


(*   *)
Ltac ProveCca2After :=
  repeat
   (intros; simpl; auto;
     match goal with
     | |- CCA2AfterEncTerm _ _ _ _ _ _ (fun x => x) => apply CCA2AttContId
     | |- CCA2AfterEncTerm _ ?Pk _ _ ?X _ (fun _ => ?Pk ?X) => apply CCA2PkeyCont
     | |- CCA2AfterEncTerm _ _ _ _ _ _ (fun _ => nonce (?N)) => apply CCA2AttNonceTermCont; ProveFresh; try lia
     | |- CCA2AfterEncTerm ?D _ ?Sk ?Er ?Nl _ (fun x => If _ Then ?Er Else ?D [_; ?Sk ?Nl]) => apply CCA2DecOrac2; ProvePPT
     | |- CCA2AfterEncTerm _ _ _ _ _ _ (fun _ => ?f ) => try unfold f; first
       [ first [apply CCA2DecOrac2; ProvePPT | apply CCA2AttBeforeToAfter; try ProveCca2Before] | apply CCA2AttContListTermFun; ProvePPT ]

     | |- CCA2AfterEncTerm _ _ _ _ _ _ (fun _ => ?f _ ) => try unfold f; first
       [ first [apply CCA2DecOrac2; ProvePPT | apply CCA2AttBeforeToAfter; try ProveCca2Before] | apply CCA2AttContListTermFun; ProvePPT ]
     | |- CCA2AfterEncTerm _ _ _ _ _ _ (fun _ => ?f _ _) => try unfold f; first
       [ first [apply CCA2DecOrac2; ProvePPT | apply CCA2AttBeforeToAfter; try ProveCca2Before] | apply CCA2AttContListTermFun; ProvePPT ]
     | |- CCA2AfterEncTerm _ _ _ _ _ _ (fun _ => ?f _ _ _) => try unfold f; first
       [ first [apply CCA2DecOrac2; ProvePPT | apply CCA2AttBeforeToAfter; try ProveCca2Before] | apply CCA2AttContListTermFun; ProvePPT ]
     | |- CCA2AfterEncTerm _ _ _ _ _ _ (fun _ => ?f _ _ _ _) => try unfold f; first
       [ first [apply CCA2DecOrac2; ProvePPT | apply CCA2AttBeforeToAfter; try ProveCca2Before] | apply CCA2AttContListTermFun; ProvePPT ]
     | |- CCA2AfterEncTerm _ _ _ _ _ _ (fun _ => ?f _ _ _ _ _) => try unfold f; first
       [ first [apply CCA2DecOrac2; ProvePPT | apply CCA2AttBeforeToAfter; try ProveCca2Before] | apply CCA2AttContListTermFun; ProvePPT ]
     | |- CCA2AfterEncTerm _ _ _ _ _ _ (fun _ => ?f _ _ _ _ _ _) => try unfold f; first
       [ first [apply CCA2DecOrac2; ProvePPT | apply CCA2AttBeforeToAfter; try ProveCca2Before] | apply CCA2AttContListTermFun; ProvePPT ]
     | |- CCA2AfterEncTerm _ _ _ _ _ _ (fun _ => ?f _ _ _ _ _ _ _) => try unfold f; first
       [ first [apply CCA2DecOrac2; ProvePPT | apply CCA2AttBeforeToAfter; try ProveCca2Before] | apply CCA2AttContListTermFun; ProvePPT ]


     | |- CCA2AfterEncTerm _ _ _ _ _ _ (?f _ _ _ _) => try (unfold f; first
       [ first [apply CCA2DecOrac2; ProvePPT | apply CCA2AttBeforeToAfter; try ProveCca2Before] | apply CCA2AttContListTermFun; ProvePPT ])
     | |- CCA2AfterEncTerm _ _ _ _ _ _ (?f _ _ _) => try (unfold f; first
       [ first [apply CCA2DecOrac2; ProvePPT | apply CCA2AttBeforeToAfter; try ProveCca2Before] | apply CCA2AttContListTermFun; ProvePPT ])
     | |- CCA2AfterEncTerm _ _ _ _ _ _ (?f _ _ ) => try (unfold f; first
       [ first [apply CCA2DecOrac2; ProvePPT | apply CCA2AttBeforeToAfter; try ProveCca2Before] | apply CCA2AttContListTermFun; ProvePPT ])


     | |- CCA2AfterEnc _ _ _ _ _ _ (fun _ => []) => try apply CCA2AfterTermNil
     | |- CCA2AfterEnc _ _ _ _ _ _ (fun _ => _ :: _) => try apply CCA2AfterTermList
     end).

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
Require Export axioms.
Import ListNotations.
Require Export Coq.Arith.PeanoNat.



(*  *)
Proposition cca2 : CCA2L Len Enc Dec Pkey Skey Rand Error.
Proof.
  pose cca_2.
  apply CCA2toCCA2L in c.
  auto.
  all : apply O.
Qed.


(*  *)
Lemma decGame: forall m r c,
(*-----------------------------------*)
    (decS c) = If (c ≟ (❴m❵_pkS ＾ (Rand [nonce r]))) Then m Else (decS c).
Proof.
  intros.
  rewrite <- (@If_same (c ≟ (❴m❵_pkS ＾ (Rand [nonce r]))) c) at 1.
  rewrite (@Eq_branch (c) (❴m❵_pkS ＾ (Rand [nonce r]))  (fun x => x) _ ).
  rewrite (@If_morph (fun x => decS x) (c ≟ (❴m❵_pkS ＾ (Rand [nonce r]))) _ _ ).
  rewrite decenc.
  reflexivity.
  all : ProveContext.
Qed.


Lemma decIfThenElse: forall m r c,
(*-----------------------------------*)
    (decS c)
    =
    If (c ≟ (❴m❵_pkS ＾ (Rand [nonce r])))
       Then m
       Else (If (c ≟ (❴m❵_pkS ＾ (Rand [nonce r])))
                Then Error
                Else decS c).
Proof.
  intros.
  rewrite (@If_eval (fun _ => _) (fun b => If b Then Error Else _) (c ≟ (❴m❵_pkS ＾ (Rand [nonce r])))).
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

(***************************************************************************************************)
(***************************************************************************************************)
(****************************          Axioms.v        *****************************************)
(***************************************************************************************************)
(***************************************************************************************************)

(*  *)

Proposition frccCont : forall n f t0, Freshc n t0 -> Freshc n f -> Freshc n (fun x : list ppt => t0 (f x)).
Proof.
  intros.
  apply (Freshc_mut (fun n tl =>  Freshc n f -> Freshc n (fun x : list ppt => tl (f x)))
           (fun n t  =>  Freshc n f -> FreshTermc n (fun x : list ppt => t (f x)))); intros; simpl; try ProveFreshC.
  - apply frcApp; auto.
  - apply frcFAdv; auto.
  - apply frcFAdv; auto.
Qed.

(*  *)
Proposition CompHidEx : forall t0 t1 t2 n1 n2,
    ( | t1 | = | t2 | ) ->
    n1 <> n2 ->
  Fresh (nonce n1) [t1; t2] -> Freshc (nonce n1) t0 ->
  Fresh (nonce n2) [t1; t2] -> Freshc (nonce n2) t0 ->
  t0 [(com t1 (Comk (nonce n1))); (com t2 (Comk (nonce n2)))]
 ~
  t0 [(com t2 (Comk (nonce n1))); (com t1 (Comk (nonce n2)))].
Proof.
  intros.
  pose (CompHid (fun x => t0 [Proj1 x ; Proj2 x] ) ⫠ t1 t2 n1 n2) as c.
  apply ceq_eq in H. unfold CompHid_prop in c. simpl in c. rewrite H in c. rewrite If_true in c.
  rewrite If_true in c. rewrite proj1pair in c. rewrite proj2pair in c.
  rewrite proj1pair in c. rewrite proj2pair in c.
  apply c. assumption. all: ProveFresh.
  apply (frccCont (nonce (n1)) (fun x => [Proj1 x; Proj2 x]) t0); auto. ProveFreshC.
  apply (frccCont (nonce (n2)) (fun x => [Proj1 x; Proj2 x]) t0); auto. ProveFreshC.
Qed.




(***************************************************************************************************)
(***************************************************************************************************)
(*********************************          Ltacs.v        *****************************************)
(***************************************************************************************************)
(***************************************************************************************************)

Ltac ProveFreshC_prop11 :=
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
 (*     | |- FreshTermc _  ?c => first [apply frtcCAdv; ProveContext | unfold c]  *)

     | |- Freshc _  (fun x => x)  => apply frcCAdv; ProveContext
     end).




(***************************************************************************************************)
(***************************************************************************************************)
(************************          Prop11.v        ************************************)
(***************************************************************************************************)
(***************************************************************************************************)



(* NonceListNewFresh states that, for any Nonce List {lx} with a nonce {nonce n} that is fresh in it, 
   we can always find another nonce {nonce n'} that  n ≠ n' and nonce n' is also fresh in lx. *)

Proposition NonceListNewFresh:
  forall lx n, NonceList lx -> Fresh nonce (n) lx -> exists n', n <> n' /\ Fresh nonce (n') lx.
Proof.
  intros.
  apply (nlN (nonce (n)) lx) in H.
  apply FreshExists in H.
  inversion H.
  inversion_clear H1.
  apply invfrtNN in H2.
  exists x.
  split.
  - lia.
  - auto.
  - unfold Nonce. exists n. auto.
Qed.

(* FreshNewFresh states that, if a nonce {nonce n} is fresh in a list of terms {lx}, 
   Then we can always find another nonce {nonce n'} that n ≠ n' and nonce n' is also fresh in lx. *)

Proposition FreshNewFresh:
  forall lx n, Fresh nonce (n) lx -> exists n', n <> n' /\ Fresh nonce (n') lx.
Proof.
  intros.
  apply FreshfromNonceList  in H.
  destruct H as [f [lx0 [cnxt [nl [fresh]]]]].
  apply (NonceListNewFresh lx0 n nl) in fresh.
  destruct fresh.
  destruct H0.
  exists x.
  split; auto.
  rewrite H.
  apply (FreshfromNonceList (nonce x) (f lx0)).
  exists f. exists lx0.
  split; auto.
Qed.

(* FreshFreshNewFresh states that, if a nonce {nonce n} is fresh in both term list lx0 and lx1, 
   Then we can always find a new nonce {nonce n'} that n ≠ n' and nonce n' is also fresh in lx0 and lx1 *)

Proposition FreshFreshNewFresh:
  forall lx0 lx1 n, Fresh nonce (n) lx0 -> Fresh nonce (n) lx1 ->
   exists n', n <> n' /\ Fresh nonce (n') lx0 /\ Fresh nonce (n') lx1.
Proof.
  intros.
  assert (Fresh (nonce n) (lx0 ++ lx1)).
    apply frlConc; auto.
  apply FreshNewFresh in H1.
  destruct H1.
  destruct H1.
  exists x.
  split.
  - auto.
  - apply invfrlConc in H2. destruct H2.
    split; auto.
Qed.

(* FreshFreshcNewFresh states that, if nonce {nonce n} is fresh in term t and ContextTerm t1, 
   then we can always find a new nonce {nonce n'} that n ≠ n' and nonce n' is also fresh in t and t1 *)

Proposition FreshFreshcNewFresh: forall n t t1,
  FreshTerm (nonce n) t ->   FreshTermcTerm (nonce n) t1 ->
  exists n', n' <> n  /\ FreshTerm  (nonce n') t /\  FreshTermcTerm (nonce n') t1.
Proof.
  intros n t t1 H0 H1.
  apply FreshTermfromNonceList in H0.
  destruct H0 as [f0 [lx0 [Cntx0 [Nl0 [Fresh0 H0]]]]].
  apply FreshTermcTermfromNonceList in H1.
  destruct H1 as [f1 [lx1 [Cntx1 [Nl1 [Fresh1 H1]]]]].
  apply (FreshFreshNewFresh lx0 lx1 n Fresh0) in Fresh1.
  destruct Fresh1 as [x [neq [Freshx0 Freshx1]]].
  exists x.
  split; auto.
  split.
  - rewrite H0. apply (FreshTermfromNonceList (nonce x) (f0 lx0)).
    exists f0. exists lx0.
    split; auto.
  - rewrite H1. apply (FreshTermcTermfromNonceList (nonce x) (fun x0 : ppt => f1 (x0 :: lx1))).
    exists f1. exists lx1.
    split; auto.
Qed.
  



(*  *)

Proposition Fresh2Freshc : forall n t,
  FreshTerm nonce (n) t -> FreshTermc nonce (n) (fun _ : list ppt => t).
Proof.
  intros.
  apply FreshTermfromNonceList in H.
  destruct H as [f [lx [cnxt [nl [fresh ]]]]].
  apply FreshTermcfromNonceList.
  rewrite H.
  exists (fun x => f (firstn (length lx) x)). exists lx.
  split; auto. ProveContext.
  split; auto.
  split; auto.
  assert ((fun x => f (firstn (length lx) (lx ++ x))) = (fun _ => f lx)).
    apply functional_extensionality.
    intros. rewrite firstn_app_exact.
    reflexivity.
    rewrite H0; clear H0.
    reflexivity.
Qed.


(*  *)

Proposition frtcCont: forall n f t0,
    FreshTermc (nonce n) t0 -> Freshc (nonce n) f -> FreshTermc (nonce n) (fun x : list ppt => t0 (f x)).
Proof.
  intros.
  apply frcConc with (tc := fun lx => []) in H.
  apply (frccCont (nonce n) f) in H.
  apply frtcFAdv with (t := fun lx => Nth 0 lx) in H.
  unfold Nth in H; simpl in H.
  all : auto.
  ProveContext.
  ProveFreshC_prop11.
Qed.


(*  *)

Proposition frfrtcCont: forall n f t0,
    FreshTermcTerm n t0 -> FreshTermc n f -> FreshTermc n (fun x : list ppt => t0 (f x)).
Proof.
  intros.
  apply (FreshTermcTerm_mut (fun nc t => nc = n -> Freshc nc (fun x : list ppt => t (f x)))
                            (fun nc t => nc = n -> FreshTermc nc (fun x : list ppt => t (f x)))); intros; ProveFreshC_prop11. (* we need to add nc = n as an assumption *)
  - assert (Nonce nc).
    apply (FreshTermcTermNonce) with (t := t). auto.
    inversion_clear H6.
    rewrite <- H7 in *.
    apply (frcConc x (fun x => t (f x)) (fun x => tc (f x))); auto.
  - assert (Nonce nc). apply FreshcTermNonce with (tl := tc1). auto.
    inversion_clear H6.
    rewrite <- H7 in *.
    apply (frcApp x (fun x0 : list ppt => tc1 (f x0)) (fun x0 : list ppt => tc2 (f x0))); auto.
  - assert (Nonce nc). apply FreshcTermNonce with (tl := tc). auto.
    inversion_clear H5.
    rewrite <- H6 in *.
    apply frcFAdv; auto.
  - assert (Nonce nc). apply FreshcTermNonce with (tl := tc). auto.
    inversion_clear H5.
    rewrite <- H6 in *.
    apply frtcFAdv; auto.
  - pose (frtcFAdv n0 (fun lx => t (Nth 0 lx)) (fun lx => [f lx])) as c. unfold Nth in c; simpl in c.
    apply c.
    assert ((fun lx : list ppt => t (nth 0 lx default)) = (fun lx : list ppt => t (Nth 0 lx))).
      apply functional_extensionality. intros. reflexivity.
    rewrite H3. clear H3.
    ProveContext.
    rewrite <- H2 in H0.
    ProveFreshC_prop11.
Qed.






(***************************************************************************************************)
(***************************************************************************************************)
(****************************          Lemma_21.v        *****************************************)
(***************************************************************************************************)
(***************************************************************************************************)


(* Not in the paper *)
Lemma AndGuard2 : forall {b1 b2 c} c' {d}, bppt b1 -> bppt b2 ->
    If (b1 & b2) Then c Else d = If (b1 & b2) Then (If b1 Then c Else c') Else d.
Proof.
  intros.
  rewrite (@If_morph (fun x => If x Then (If b1 Then c Else c') Else d)).
  rewrite (@If_eval (fun b1 => If b2 Then If b1 Then c Else c' Else d ) (fun _ => _)).
  rewrite (@If_morph (fun x => If x Then _ Else d)).
  rewrite If_true.
  repeat rewrite If_false.
  reflexivity.
  all : ProveContext.
Qed.



(***************************************************************************************************)
(***************************************************************************************************)
(****************************          Lemma_25.v        *****************************************)
(***************************************************************************************************)
(***************************************************************************************************)

Lemma c0EqVot : forall s, (com (vot s) kc0) = c0 s.
Proof.
  destruct s; reflexivity.
Qed.





(***************************************************************************************************)
(***************************************************************************************************)
(****************************          Lemma_26_A.v        *****************************************)
(***************************************************************************************************)
(***************************************************************************************************)

(* Properties of Dv *)

Lemma dv_perm12:
  forall v1 v2 v3 y,
    dv v1 v2 v3 y = dv v2 v1 v3 y.
Proof.
  { intros. unfold dv, dist.
    rewrite Example7_6.
    rewrite (AndComm (! (v1 ≟ v3)) (! (v2 ≟ v3))).
    unfold pchkv.
    repeat rewrite Tau1Tri, Tau2Tri, Tau3Tri.
    rewrite <- (AndAsso (ph2 ≟ (π2 v1))).
    rewrite <- (AndAsso (ph2 ≟ (π2 v2))).
    rewrite (AndComm ((ph2 ≟ (π2 v1)))).
    reflexivity. all : Provebool. }
Qed.

(* Properties of Dist check *)
Lemma dist_swap12: forall m1 m2 m3, dist m1 m2 m3 = dist m2 m1 m3.
  { intros. unfold dist. rewrite (Example7_6 m1 m2). rewrite (AndComm (! (m1 ≟ m3)) (! (m2 ≟ m3))). reflexivity. all : Provebool. }
Qed.

Lemma dist_swap13: forall m1 m2 m3, dist m1 m2 m3 = dist m3 m2 m1.
  { intros. unfold dist. rewrite (Example7_6 m2 m1). rewrite (Example7_6 m3 m1). rewrite (Example7_6 m3 m2). rewrite (AndComm (! (m1 ≟ m3)) (! (m2 ≟ m3))).
    rewrite <- AndAsso. rewrite (AndComm (! (m1 ≟ m2)) (! (m2 ≟ m3))). rewrite AndAsso. rewrite (AndComm (! (m1 ≟ m2)) (! (m1 ≟ m3))). reflexivity. all : Provebool. }
Qed.

Lemma dist_swap23: forall m1 m2 m3, dist m1 m2 m3 = dist m1 m3 m2.
  { intros. unfold dist. rewrite (Example7_6 m3 m2). rewrite <- AndAsso. rewrite (AndComm (! (m1 ≟ m2)) (! (m1 ≟ m3))). rewrite AndAsso. reflexivity. all : Provebool. }
Qed.


(* Properties of Pchko *)
Lemma pchko_swap12: forall m1 m2 m3, pchko (＜ m1, m2, m3 ＞) = pchko (＜ m2, m1, m3 ＞).
  { intros. unfold pchko. repeat rewrite Tau1Tri, Tau2Tri, Tau3Tri. rewrite <- AndAsso. rewrite (AndComm (ph3 ≟ (π2 m1)) (ph3 ≟ (π2 m2))). rewrite AndAsso. reflexivity. all : Provebool. }
Qed.

Lemma pchko_swap13: forall m1 m2 m3, pchko (＜ m1, m2, m3 ＞) = pchko (＜ m3, m2, m1 ＞).
  { intros. unfold pchko. repeat rewrite Tau1Tri, Tau2Tri, Tau3Tri. rewrite (AndComm (ph3 ≟ (π2 m3)) ((ph3 ≟ (π2 m2)) & (ph3 ≟ (π2 m1)))).
    rewrite (AndComm (ph3 ≟ (π2 m2)) (ph3 ≟ (π2 m1))). rewrite AndAsso. reflexivity. all : Provebool. }
Qed.

Lemma pchko_swap23: forall m1 m2 m3, pchko (＜ m1, m2, m3 ＞) = pchko (＜ m1, m3, m2 ＞).
  { intros. unfold pchko. repeat rewrite Tau1Tri, Tau2Tri, Tau3Tri. rewrite (AndComm (ph3 ≟ (π2 m3)) (ph3 ≟ (π2 m2))). reflexivity. all : Provebool.  }
Qed.

(* Properties of isinkc *)
Lemma isinkc_kc_swap: forall m1 m2 m3, isinkc kc0 kc1 (＜ π2 (π1 m1), π2 (π1 m2), π2 (π1 m3) ＞) = isinkc kc1 kc0 (＜ π2 (π1 m1), π2 (π1 m2), π2 (π1 m3) ＞).
  { intros.
    unfold isinkc. unfold isin. repeat rewrite Tau1Tri, Tau2Tri, Tau3Tri.
    rewrite xnor_comm.
    reflexivity. all : Provebool. }
Qed.

Lemma isinkc_swap12: forall m1 m2 m3, isinkc kc0 kc1 (＜ π2 (π1 m1), π2 (π1 m2), π2 (π1 m3) ＞) = isinkc kc0 kc1 (＜ π2 (π1 m2), π2 (π1 m1), π2 (π1 m3) ＞).
  { intros. unfold isinkc. unfold isin. repeat rewrite Tau1Tri, Tau2Tri, Tau3Tri. repeat rewrite OrAsso. rewrite (OrComm (kc0 ≟ (π2 (π1 m1))) _).
    rewrite (OrComm (kc1 ≟ (π2 (π1 m1))) _). reflexivity. all : Provebool. }
Qed.

Lemma isinkc_swap13: forall m1 m2 m3, isinkc kc0 kc1 (＜ π2 (π1 m1), π2 (π1 m2), π2 (π1 m3) ＞) = isinkc kc0 kc1 (＜ π2 (π1 m3), π2 (π1 m2), π2 (π1 m1) ＞).
 { intros. unfold isinkc. unfold isin. repeat rewrite Tau1Tri, Tau2Tri, Tau3Tri. rewrite (OrComm (kc0 ≟ (π2 (π1 m1))) _). rewrite (OrComm (kc1 ≟ (π2 (π1 m1))) _).
   repeat rewrite OrAsso.  rewrite (OrComm (kc0 ≟ (π2 (π1 m2))) _). rewrite (OrComm (kc1 ≟ (π2 (π1 m2))) _). reflexivity. all : Provebool. }
Qed.

Lemma isinkc_swap23: forall m1 m2 m3, isinkc kc0 kc1 (＜ π2 (π1 m1), π2 (π1 m2), π2 (π1 m3) ＞) = isinkc kc0 kc1 (＜ π2 (π1 m1), π2 (π1 m3), π2 (π1 m2) ＞).
 { intros. unfold isinkc. unfold isin. repeat rewrite Tau1Tri, Tau2Tri, Tau3Tri. rewrite (OrComm (kc0 ≟ (π2 (π1 m2))) _). rewrite (OrComm (kc1 ≟ (π2 (π1 m2))) _). reflexivity. all : Provebool. }
Qed.

(**)

(**)

(* Properties of Do *)

Lemma Do_swap12: forall m1 m2 m3, Do m1 m2 m3 = Do m2 m1 m3.
Proof.
{ intros. unfold Do. rewrite dist_swap12, pchko_swap12, isinkc_swap12, shufl_perm12. reflexivity. }
Qed.


Lemma Do_swap13: forall m1 m2 m3, Do m1 m2 m3 = Do m3 m2 m1.
Proof.
  { intros. unfold Do. rewrite dist_swap13, pchko_swap13, isinkc_swap13, shufl_perm13.
    reflexivity. }
Qed.

Lemma Do_swap23: forall m1 m2 m3, Do m1 m2 m3 = Do m1 m3 m2.
Proof.
  { intros. unfold Do. rewrite dist_swap23, pchko_swap23, isinkc_swap23, shufl_perm23.
    reflexivity. }
Qed.

Lemma Do_dist12: forall m1 m2, Do m1 m1 m2 = ⫠.
Proof.
  { intros. unfold Do, dist. rewrite ceqeq. rewrite If_true. repeat rewrite If_false.
    reflexivity. }
Qed.


Lemma Do_dist13: forall m1 m2, Do m1 m2 m1 = ⫠.
Proof.
  { intros. unfold Do, dist. rewrite ceqeq. rewrite If_true. rewrite If_false. rewrite If_same. repeat rewrite If_false.
    reflexivity. }
Qed.


Lemma Do_dist23: forall m1 m2, Do m2 m1 m1 = ⫠.
Proof.
  { intros. unfold Do, dist. rewrite ceqeq. rewrite If_true. repeat rewrite If_same. repeat rewrite If_false.
    reflexivity. }
Qed.

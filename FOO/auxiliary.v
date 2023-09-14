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
Require Export I_IfThenElseLogic.
Import ListNotations.
Require Export Coq.Arith.PeanoNat.
Require Export definitions.




(* Some axioms and propositions used in the FOO proof have been renamed. So we bridge that gap here *)

Notation "'Tau1Tri'" := Troj1Tri.
Notation "'Tau2Tri'" := Troj2Tri.
Notation "'Tau3Tri'" := Troj3Tri.
Notation "'proj1pair'" := Proj1Pair.
Notation "'proj2pair'" := Proj2Pair.

Notation "'AndAsso'" := AndAssoc.
Notation "'xnor_comm'" := XnorComm.



Proposition OrAsso :
  forall b1 b2 b3,
    b1 or b2 or b3 = (b1 or b2) or b3.
Proof.
  intros.
  rewrite OrAssoc.
  reflexivity.
Qed.  


(*  *)
Proposition LEN_prop26_13_helper : forall A B C D E F,
    bppt A -> bppt B -> bppt C -> bppt D -> bppt E -> bppt F ->
   (A & B & C) & (D & E & F) = ((A & B & C) & D & E & F) & (B & E).
Proof.
  intros.
  rewrite <- (AndDup B) at 1.
  rewrite <- (AndDup E) at 1.
  rewrite <- (AndAsso A).
  rewrite <- (AndAsso A).
  rewrite (AndComm A).
  rewrite (AndAsso B).
  rewrite (AndAsso B).
  rewrite (AndAsso A).
  rewrite <- (AndAsso D).
  rewrite <- (AndAsso D).
  rewrite (AndComm D).
  rewrite (AndAsso E).
  rewrite (AndAsso E).
  rewrite (AndAsso D).
  rewrite (AndComm E).
  rewrite (AndComm B).
  rewrite (AndAsso _ B).
  rewrite <- (AndAsso B).
  rewrite (AndComm B (D & E & F)).
  rewrite (AndAsso _ B).
  rewrite <- (AndAsso (A & B & C)).
  reflexivity.
  all : Provebool.
Qed.

Proposition If_pair : forall b A B C D, bppt b ->
    If b Then (＜ A, B ＞) Else ＜ C, D ＞
    =
    ＜ If b Then A Else C, If b Then B Else D ＞.
Proof.
  intros.
  rewrite (@If_morph (fun x => ＜ x, If b Then B Else D ＞ )).
  rewrite (@If_eval (fun b => ＜ A, If b Then B Else D ＞  )  (fun b => (＜ C, If b Then B Else D ＞ )  ) ).
  rewrite If_true, If_false.
  reflexivity.
  all : ProveboolandContext.
Qed.




(**)
Lemma GuardAhead: forall m b0 b1,
    m = If b0 Then If b1 Then m
                         Else m
              Else If b1 Then m
                         Else m.
Proof.
  intros.
  repeat rewrite If_same.
  reflexivity.
Qed.


(**)
Lemma GuardAhead': forall m b1 b2 b3,
    m = If b1 Then If b2 Then If b3 Then m Else m
                         Else If b3 Then m Else m
              Else If b2 Then If b3 Then m Else m
                         Else If b3 Then m Else m.
Proof.
  intros.
  repeat rewrite If_same.
  reflexivity.
Qed.









Lemma AndGuard : forall b1 b2 b3 c1 c2 c3,
    bppt b1 -> bppt b2 -> bppt b3 ->
    bppt c1 -> bppt c2 -> bppt c3 ->
    (If b1 Then FAlse Else c1) &
      (If b2 Then FAlse Else c2) &
      (If b3 Then FAlse Else c3)
      =
        If b1 Then FAlse Else If b2 Then FAlse Else If b3 Then FAlse Else c1 & c2 & c3.
Proof.
  intros.
  rewrite (@If_morph (fun x => x & _)). rewrite If_false.
  rewrite (@If_morph (fun x => c1 & x)). rewrite If_same.
  rewrite (@If_morph (fun x => x & _)). rewrite If_false.
  rewrite (@If_morph (fun x =>  c2 & c1 & x)). rewrite If_same. rewrite If_same.
  rewrite AndComm. rewrite AndAssoc. rewrite (AndComm c3 c2).
  reflexivity.
  all : ProveboolandContext.
Qed.




(* Notation "x '≠' y"    := ((x ≟ y) = FAlse) in definitions  *)
Proposition NeqIdem: forall f t t', ContextTerm General Term f
   -> (f t) ≠ (f t') -> t ≠ t'.
Proof.
  intros.
  rewrite (If_tf (t ≟ t')).
  rewrite <- (@ceqeq (f t)).
  rewrite <- H0 at 1.
  rewrite (@Eq_branch t t' (fun x => f t ≟ f x) _ ).
  rewrite If_same.
  auto.
  all : ProveboolandContext.
Qed.

(*  *)
Lemma FalseEq : forall x c,
    [x ≟ c] ~ [FAlse] -> (x ≠ c).
Proof.
  intros.
  apply Example7_2 in H.
  auto.
  ProveContext.
Qed.



(** Variants of If_branch **)

Theorem cind_len_rev : forall {lt1 lt2 : list ppt},
    (lt1 ~ lt2) -> length lt1 = length lt2.
Proof.
  intros.
  pose (@cind_len lt1 lt2).
  apply (MT (length lt1 <> length lt2) (~ lt1 ~ lt2)) in n.
  apply doubleneg_elim in n; auto.
  auto.
Qed.

(* *)
Theorem IF_branch_gen : forall (lz lz' z z' : list ppt) (x x' y y' b b' : ppt),
    lz ++ z ++ [b; x] ~ lz' ++ z' ++ [b'; x']
  -> lz ++ z ++ [b; y] ~ lz' ++ z' ++ [b'; y']
  -> lz ++ z ++ [If b Then x Else y] ~ lz' ++ z' ++ [If b' Then x' Else y'].
Proof.
  intros.
  repeat rewrite app_assoc in H, H0.
  pose (@IF_branch (lz ++ z) (lz'++z') x x' y y' b b' H H0).

(* |lz ++ z| = |lz' ++ z'|*)
  assert (H1:= H); auto.
  apply cind_len_rev in H1.
  rewrite app_length in H1. rewrite (app_length (lz' ++ z') [b'; x']) in H1. simpl in H1.
  rewrite Nat.add_comm in H1. rewrite (Nat.add_comm (length (lz' ++ z')) 2) in H1.
  apply Plus.plus_reg_l in H1.

(* *)
  repeat rewrite app_assoc.
  apply (@cind_funcapp (fun x => (firstn (length (lz ++ z)) x) ++ (skipn (1 + (length (lz ++ z))) x))) in c.
  rewrite H1 in c at 3 4.
  repeat rewrite firstn_app_exact in c.
  assert (forall (lz:list ppt) z b, lz ++ [z; b] = (lz ++ [z]) ++ [b]).
  { intros. induction lz0; auto. intros; simpl. rewrite IHlz0. auto. }
  repeat rewrite H2 in c. clear H2.
  rewrite skipn_app in c.
  rewrite last_length in c.
  assert (1 + length (lz ++ z) - S (length (lz ++ z)) = 0). lia.
  rewrite H2 in c.
  rewrite skipn_O in c. clear H2. clear H1.

  assert (forall lz z (b:ppt), (1 + length (lz ++ z)) = length ((lz ++ z) ++ [b])).
  { intros. rewrite (app_length (lz0 ++ z0) [b0]). simpl. lia. }
  rewrite (H1 lz z b) in c. rewrite (H1 lz' z' b') in c. clear H1.
  rewrite skipn_all in c.
  rewrite skpn in c.
  auto.

  ProveContext.
Qed.


Theorem IF_branch':  forall (lz lz' : list ppt) (x x' y y' b b' : ppt),
    lz ++ [b; x] ~ lz' ++ [b'; x']
  -> lz ++ [b; y] ~ lz' ++ [b'; y']
  -> lz ++ [If b Then x Else y] ~ lz' ++ [If b' Then x' Else y'].
Proof.
  intros.
  pose (@IF_branch_gen lz lz' [] [] x x' y y' b b' H H0).
  simpl in c.
  auto.
Qed.


Theorem IF_branch'' : forall (lz lz': list ppt) (z z' x x' y y' b b' : ppt),
    lz ++ [z; b; x] ~ lz' ++ [z'; b'; x']
  -> lz ++ [z; b; y] ~ lz' ++ [z'; b'; y']
  -> lz ++ [z; If b Then x Else y] ~ lz' ++ [z'; If b' Then x' Else y'].
Proof.
  intros.
  pose (@IF_branch_gen lz lz' [z] [z'] x x' y y' b b' H H0).
  auto.
Qed.


Theorem IF_branch''' : forall (lz lz' : list ppt) (z z' z1 z1' x x' y y' b b' : ppt),
    lz ++ [z; z1; b; x] ~ lz' ++ [z'; z1'; b'; x']
  -> lz ++ [z; z1; b; y] ~ lz' ++ [z'; z1'; b'; y']
  -> lz ++ [z; z1; If b Then x Else y] ~ lz' ++ [z'; z1'; If b' Then x' Else y'].
Proof.
  intros.
  pose (@IF_branch_gen lz lz' [z; z1] [z'; z1'] x x' y y' b b' H H0).
  auto.
Qed.


Theorem IF_branch'''' : forall (lz lz' : list ppt) (z z' z1 z1' z2 z2' x x' y y' b b' : ppt),
    lz ++ [z; z1; z2; b; x] ~ lz' ++ [z'; z1'; z2'; b'; x']
  -> lz ++ [z; z1; z2; b; y] ~ lz' ++ [z'; z1'; z2'; b'; y']
  -> lz ++ [z; z1; z2; If b Then x Else y] ~ lz' ++ [z'; z1'; z2'; If b' Then x' Else y'].
Proof.
  intros.
  pose (@IF_branch_gen lz lz' [z; z1; z2] [z'; z1'; z2'] x x' y y' b b' H H0).
  auto.
Qed.






Theorem If_else: forall {b u u' u''},
    bppt b -> If b Then u Else (If b Then u' Else u'') = If b Then u Else u''.
  intros. rewrite (@If_eval (fun _ => u) (fun x => If x Then u' Else u'') b). rewrite (@If_false u' u''). reflexivity. all: try ProveContext.
Qed.


Lemma If_morph_list :(*"<<<"*)  forall  {f}  , (*">>>"*)
  forall  {b x y} {u} ,
      (*"<<<"*)ContextTerm General List f -> bppt b -> (*">>>"*)
    (f (If b Then x Else y :: u))
                     = (If b Then (f (x :: u) ) Else (f (y :: u))).
Proof.
  intros.
  apply (ceq_transymm  (@If_same b (f (If b Then x Else y :: u)))).
  assert (ContextTerm General Term (fun b' : ppt => f (If b' Then x Else y :: u))). ProveContext.
  rewrite (@If_eval (fun b'=> f (If b' Then x Else y :: u)) (fun b' => f (If b' Then x Else y :: u)) b H1 H1).
  apply (@ceq_subeq (fun x' : ToL Term => If b
    Then (f (x' :: u))
    Else (f  (If FAlse Then x Else y :: u)))
    (fun x': ToL Term => (If b Then f (x :: u) Else f (y :: u))) x (If TRue
               Then x
               Else y)). ProveContext. ProveContext.
 apply ceq_symm. apply If_true.
 apply (@ceq_subeq (fun x': ToL Term => If b
    Then (f (x :: u))
    Else (f (x' :: u)))  (fun x': ToL Term  => (If b
      Then f (x :: u)
      Else f (y :: u))) y (If FAlse
               Then x
               Else y)). ProveContext. ProveContext.
 apply ceq_symm. apply If_false.
 apply ceq_ref. Provebool.
Qed.

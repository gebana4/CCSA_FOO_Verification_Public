
(************************************************************************)
(* Copyright (c) 2020-2021, Gergei Bana, Qianli Zhang                   *)
(*                                                                      *)
(* This work is licensed under the MIT license. The license is          *)
(* described in the file "LICENSE" available at the root of the source  *)
(* or at https://opensource.org/licenses/MIT                            *)
(************************************************************************)


Require Import Core.
Require Import GroupExponentiation.
Require Import Pair.


(*****************
 ** Example 7.1 **
 *****************)

Theorem Example7_1: forall {b x1 x2 y1 y2 t1 t2},
    ContextTerm General Term t1 -> ContextTerm General Term t2 -> bppt b ->
    (If b Then (t1 (If b Then x1 Else y1)) Else (t2 (If b Then x2 Else y2)))
  = (If b Then (t1 x1) Else (t2 y2)).
Proof.
  intros.
  apply @If_morph with t1 b  x1 y1 in H.
  apply (@If_morph t2 b  x2 y2) in  H0.
  rewrite H.
  rewrite H0.
  rewrite (@If_idemp b (t1 x1) (t1 y1) (t2 x2) (t2 y2)).
  reflexivity. all: Provebool. Qed.

Theorem If_same_if: forall {b x1 x2 y1 y2}, bppt b ->
    (If b Then (If b Then x1 Else y1) Else (If b Then x2 Else y2))
    = (If b Then x1 Else y2).
Proof.
  intros.
  apply  (@Example7_1 b x1 x2 y1 y2 id id).
  ProveContext.
  ProveContext.
  Provebool.
Qed.




(*****************
 ** Example 7.2 **
 *****************)

(* Use cind_restr from CCSACoreAxioms *)

Theorem Example7_2: forall {x c},
 [x] ~ [c] -> ContextTerm Adversarial List(fun lx => c) ->
  x = c.
Proof.
  intros.
  apply (@FuncApp (fun lx => [c])) in H.  simpl in H.
  apply (@cind_funcapp (fun lx => [EQ lx])) in H; simpl in H.
  apply ceq.
  rewrite H.
  apply ceq.
  reflexivity.
  ProveContext.
  ProveContext. Qed.



(*****************
 ** Example 7.3 **
 *****************)

Theorem Example7_3: forall {x1 x2 y},
  (If (EQ [x1 ; x2]) Then x1 Else y) = (If (EQ [x1 ; x2]) Then x2 Else y).
Proof.
  intros.
  assert (EQ [If (EQ [x1 ; x2]) Then x1 Else y ; If (EQ [x1 ; x2]) Then x2 Else y]
             =
             If EQ [x1 ; x2]
             Then EQ [ x1 ; If (EQ [x1 ; x2]) Then x2 Else y ]
             Else EQ [ y ; If (EQ [x1 ; x2]) Then x2 Else y ]).
  apply (@If_morph (fun x => EQ [ x ; If (EQ [x1 ; x2]) Then x2 Else y ])).
  Provebool. ProveContext.
  assert (H1 := (@Example7_1 (EQ [x1 ; x2]) x2 x2 y y (fun x => EQ [x1 ; x]) (fun x => EQ [y ; x])) ).
  simpl in H1.
  rewrite H1 in H.
  rewrite (@Example7_2 (EQ [y ; y ])  TRue) in H.
  rewrite (@If_eval (fun x => x) (fun x => TRue) (EQ [x1; x2])) in H.
  rewrite (@If_same (EQ [x1; x2]) TRue) in H.
  apply ceq. apply ceq_cind. apply H. all : ProveContext.
  all: Provebool.
  apply ceq.
  reflexivity.
Qed.



(*****************
 ** Example 7.4 **
 *****************)

Theorem Example7_4: forall b {x1 x2 y1 y2} t t', bppt b ->
ContextTerm General Term t ->
  ContextTerm General Term t' ->
     (If b Then x1 Else y1) = (If b Then x2 Else y2)
  -> (If b Then (t x1) Else (t' y1)) = (If b Then (t x2) Else (t' y2)).
Proof.
  intros.
  rewrite <- (@Example7_1 b x1 x1 y1 y1 t t' H0 H1).
  rewrite (ceq_funcapp H2). rewrite (ceq_funcapp H2).
  apply Example7_1; auto. Provebool. Qed.


Theorem Eq_branch : forall x1 x2 t t', ContextTerm General Term t ->
  (If (EQ [x1; x2]) Then (t x1) Else t') = (If (EQ [x1; x2]) Then (t x2) Else t').
Proof.
  intros.
  apply (@Example7_4 (EQ [x1; x2]) x1 x2 t' t' t (fun _ => t')).
  auto. Provebool. ProveContext. ProveContext. apply Example7_3. Qed.



(*****************
 ** Example 7.5 **
 *****************)

Theorem Example7_5:
  (EQ [TRue; FAlse]) = FAlse.
Proof.
  rewrite (@If_tf (EQ [TRue ;FAlse])).
  rewrite (@Example7_3 TRue FAlse FAlse).
  apply If_same. Provebool. Qed.



(*****************
 ** Example 7.6 **
 *****************)

Theorem Example7_6: forall x y,
  (EQ [x; y])  =  (EQ [y; x]).
Proof.
  intros.
  rewrite (@If_tf (EQ [x ;y])).
  rewrite <- (@If_eval (fun x=>x) (fun x=>FAlse) (EQ [x; y])).
  rewrite (Eq_branch x y  (fun _ => EQ [_ ; y]) FAlse).
  (*rewrite <- (Eq_branch x y (fun _ => EQ [y; _]) FAlse).*)
  rewrite <- (Eq_branch x y (fun _  => EQ [y; _ ]) FAlse).
(* this is a mystery why "(fun x => EQ [y; x])" does not work here.
"simpl." has to follow it. interesting...
 *)
  simpl.
  rewrite (@If_tf (EQ [y; x])) at 1.
  rewrite (@If_morph (fun c => If EQ [x; y] Then c Else FAlse) ).
  simpl.
  rewrite (@If_same (EQ [x; y]) FAlse).
  rewrite <- (If_tf (EQ [x; y])).
  rewrite <- (Eq_branch y x  (fun _ => EQ [_; y]) FAlse).
  rewrite (Eq_branch y x  (fun _ => EQ [y; _]) FAlse).
  rewrite (@If_eval (fun x=>x) (fun x=>FAlse) (EQ [y; x])).
  rewrite <- (If_tf (EQ [y; x])). reflexivity.
  all: ProveContext. all: Provebool. Qed.




(*****************
 ** Example 7.7 **
 *****************)

Theorem Example7_7: forall (n1 n2: nat),
  n1 <> n2 -> (EQ [(nonce n1); (Pair [(nonce n1) ;(nonce n2)])]) = FAlse.
Proof.
  intros.
  rewrite (@If_tf (EQ [(nonce n1); (Pair [(nonce n1) ;(nonce n2)])])).

  rewrite <- (@Example7_2 (EQ [nonce n2 ; nonce n2] ) TRue (ceq1 (@ceq_ref (nonce n2)))).
  rewrite <-  (@Proj2Pair (nonce n1) (nonce n2)) at 3.
  assert (H100 := ((Eq_branch (nonce n1) (Pair [(nonce n1) ;(nonce n2)])
                              (fun c => EQ [(nonce n2); (Proj2 [c])]) FAlse))); simpl in H100; rewrite <- H100.
  (*  rewrite  <- ((Eq_branch (nonce n1) (pair [(nonce n1) ;(nonce n2)])
                         (fun c => EQ [(nonce n2); (proj2 [c])]) FAlse)). *)
  enough (FreshTerm (nonce n2) (Proj2 [nonce n1])).
  rewrite (@Example7_2 (EQ [nonce n2; Proj2 [nonce n1]])
                       FAlse (@FreshNEq  (nonce n2) (Proj2 [nonce n1]) H0)).
  apply If_same.
  ProveContext. ProveFresh.
  all: ProveContext. Provebool.
Qed.



(*****************
 ** Example 7.8 **
 *****************)

Definition notb (b : ppt) := If b Then FAlse Else TRue.

Theorem Example7_8 :  forall b x y, bppt b ->
  (If (notb b) Then x Else y) = (If b Then y Else x).
Proof.
  intros.
  unfold notb.
  rewrite  (@If_morph (fun b' => If b' Then x Else y)).
  rewrite If_false.
  rewrite If_true.
  reflexivity. Provebool. ProveContext. Qed.



(******************
 ** Example 7.10 **
 ******************)

Theorem Example7_10: (DDH ggen Ring) -> forall (n n1 n2 n3 n5 :nat),
    n <> n1 -> n <> n2 -> n <> n3 -> n <> n5 -> n1 <> n2 -> n1 <> n3 -> n1 <> n5 -> n2 <> n3 -> n2 <> n5 -> n3 <> n5 ->
       [g n;
        g n ^^ R n1 ; g n ^^ R n2; g n ^^ R n3;
        g n ^^ R n1 ^^ R n2;  g n ^^ R n1 ^^ R n3;  g n ^^ R n2 ^^ R n3;
        g n ^^ R n1 ^^ R n2 ^^ R n3]
      ~
       [g n;
        g n ^^ R n1 ; g n ^^ R n2; g n ^^ R n3;
        g n ^^ R n1 ^^ R n2;  g n ^^ R n1 ^^ R n3;  g n ^^ R n2 ^^ R n3;
        g n ^^ R n5].
Proof.
  intros DDH. intros.


(* Step 1: Take a d with fresh(G,g,a,b,c,e,d).*)
  assert (exists d, (n <> d /\ n1 <> d /\ n2 <> d /\ n3 <> d /\ d <> n5)).
    exists (n + n1 + n2 + n3 + n5); lia.
    inversion_clear H9; rename x into n4;
    inversion_clear H10;  inversion_clear H11;
    inversion_clear H12;  inversion_clear H13.


  pose (DDH n n1 n2 n4 H H0 H9 H3 H10 H11) as D.

(* Step 3: *)
  apply (FreshInd (nonce n3) (nonce n3) [g n; g n ^^ R n1; g n ^^ R n2; g n ^^ R n1 ^^ R n2]
                        [g n; g n ^^ R n1; g n ^^ R n2; g n ^^ R n4]) in D.

(* Step 4: *)
  pose (f := (fun lc => let Rc := Ring [Nth 0 lc] in
                     ((Nth 1 lc) ^^ Rc) :: ((Nth 2 lc) ^^ Rc) :: ((Nth 3 lc) ^^ Rc) :: ((Nth 4 lc) ^^ Rc) :: nil)).
  apply (@FuncApp f
           [nonce n3; g n; g n ^^ R n1; g n ^^ R n2; g n ^^ R n1 ^^ R n2]
           [nonce n3; g n; g n ^^ R n1; g n ^^ R n2; g n ^^ R n4]) in D.
  unfold f in D; unfold Nth in D; unfold nth in D; simpl in D; clear f.
  (*better than simpl or compute in D*)
  assert (Ring [nonce n3] = R n3); auto; rewrite H13 in *;  clear H13.

(* Step 5: *)
  apply cind_restr in D.

(* Step 6: *)

  pose (DDH n n4 n3 n5 H9 H1 H2 (PeanoNat.Nat.neq_sym n3 n4 H12) H14 H8) as E.
 (* pose (l1 := [g n; g n ^^ R n4; g n ^^ R n3; g n ^^ R n4 ^^ R n3]).
  pose (l2 := [g n; g n ^^ R n4; g n ^^ R n3; g n ^^ R n5]).*)


(* Step 7: *)
  apply (FreshInd (nonce n2) (nonce n2) [g n; g n ^^ R n4; g n ^^ R n3; g n ^^ R n4 ^^ R n3]
                        [g n; g n ^^ R n4; g n ^^ R n3; g n ^^ R n5]) in E.
  apply (FreshInd (nonce n1) (nonce n1) ((nonce n2):: [g n; g n ^^ R n4; g n ^^ R n3; g n ^^ R n4 ^^ R n3])
                        ((nonce n2) :: [g n; g n ^^ R n4; g n ^^ R n3; g n ^^ R n5])) in E.

(* Step 8: *)
  pose (f := (fun lc =>
                     let Ra := Ring [Nth 0 lc] in
                     let Rb := Ring [Nth 1 lc] in
                     (Nth 2 lc ^^ Ra) :: (Nth 2 lc ^^ Rb) :: (Nth 4 lc ^^ Ra) :: (Nth 4 lc ^^ Rb) :: nil
                     )).
  apply (@FuncApp f
           [nonce n1; nonce n2; g n; g n ^^ R n4; g n ^^ R n3; g n ^^ R n4 ^^ R n3]
           [nonce n1; nonce n2; g n; g n ^^ R n4; g n ^^ R n3; g n ^^ R n5]) in E.
  unfold f in E; unfold Nth in E; simpl in E.
  clear f.
  assert (Ring [nonce n1] = R n1). auto. rewrite H13 in *. clear H13.
  assert (Ring [nonce n2] = R n2). auto. rewrite H13 in *. clear H13.


(* Step 9: *)
(*"Would be good to be able to remove rewID application"*)
  pose (@expcomm (g n) (R n3) (R n1)).
  pose (@expcomm (g n) (R n3) (R n2)).
  rewrite e in E. rewrite e0 in E. clear e e0.
  apply cind_restr in E. apply cind_restr in E.

  pose (f := (fun lc : list ppt =>
                       Nth 0 lc :: Nth 4 lc :: Nth 5 lc :: Nth 1 lc :: Nth 2 lc :: Nth 6 lc :: Nth 7 lc :: Nth 3 lc :: nil
                     )).
  apply (@cind_funcapp f) in E. unfold f in E; unfold Nth in E; simpl in E. clear f.

(* Step 10: *)
  rewrite E in D.
  clear E.

(* Step 11: *)
  pose (DDH n n1 n2 n4 H H0 H9 H3 H10 H11) as F.
  apply (FreshInd (nonce n5) (nonce n5) [g n; g n ^^ R n1; g n ^^ R n2; g n ^^ R n1 ^^ R n2]
                        [g n; g n ^^ R n1; g n ^^ R n2; g n ^^ R n4]) in F.

  apply (FreshInd (nonce n3) (nonce n3) [nonce n5; g n; g n ^^ R n1; g n ^^ R n2; g n ^^ R n1 ^^ R n2]
                        [nonce n5; g n; g n ^^ R n1; g n ^^ R n2; g n ^^ R n4]) in F.

(* Step 12: *)
  pose (f := (fun lc => let Rc := Ring [Nth 0 lc] in let Re := Ring [Nth 1 lc] in
                     (Nth 2 lc ^^ Rc) :: (Nth 2 lc ^^ Re) :: (Nth 3 lc ^^ Rc) :: (Nth 4 lc ^^ Rc) :: nil)).
  apply (@FuncApp f
           [nonce n3; nonce n5; g n; g n ^^ R n1; g n ^^ R n2; g n ^^ R n1 ^^ R n2]
           [nonce n3; nonce n5; g n; g n ^^ R n1; g n ^^ R n2; g n ^^ R n4]) in F.
  unfold f in F. unfold Nth in F.  simpl in F.
  clear f.
  assert (Ring [nonce n3] = R n3). auto.
  assert (Ring [nonce n5] = R n5). auto.
  rewrite H13 in *. rewrite H15 in *. clear H13 H15.

(* Step 13: *)
  pose (f := (fun lc : list ppt =>
                       Nth 2 lc :: Nth 3 lc :: Nth 4 lc :: Nth 5 lc :: Nth 6 lc :: Nth 8 lc :: Nth 9 lc :: Nth 7 lc :: nil
                     )).
  apply (@cind_funcapp f) in F. unfold f in F; unfold Nth in F; simpl in F. clear  f.

(* Step 14: *)
  rewrite <- F in D; clear F.
  pose (f := (fun lc : list ppt => Nth 0 lc :: Nth 1 lc :: Nth 2 lc :: Nth 4 lc :: Nth 3 lc :: Nth 5 lc :: Nth 6 lc:: Nth 7 lc:: nil)).
  apply (@cind_funcapp f) in D.
  unfold f in D; unfold Nth in D; simpl in D; clear f.
  rewrite D.
  reflexivity.

(* Epilogue *)
  all : try (unfold f; ProveContext).
  all : simpl; ProveFresh. Qed.






(******************
 ** Example 7.11 **
 ******************)

Theorem Example7_11: (DDH ggen Ring) -> forall (n n1 n2 n3 n4 :nat),
      n <> n1 -> n <> n2 -> n <> n3 -> n <> n4 -> n1 <> n2 -> n1 <> n3 -> n1 <> n4 -> n2 <> n3 -> n2 <> n4 -> n3 <> n4 ->
      forall {beta}, (ContextTerm Adversarial List beta) ->
       [g n; g n ^^ R n1 ; g n ^^ R n2; g n ^^ R n3;
         If (beta [g n; g n ^^ R n1 ; g n ^^ R n2; g n ^^ R n3])  Then (g n ^^ R n1 ^^ R n2) Else (g n ^^ R n2 ^^ R n3)]
      ~
       [g n; g n ^^ R n1 ; g n ^^ R n2; g n ^^ R n3; g n ^^ R n4].
Proof.
  intros DDH. intros.

  (* Step 1.0: pose DDH with n n1 n2 n4*)
  pose (DDH n n1 n2 n4 H H0 H2 H3 H5 H7) as D.
  (* Step 2.0: FreshInd n3*)
  apply (FreshInd (nonce n3) (nonce n3)) in D.
  (* Step 3.0: FuncAPP g^c and Restr to clean*)
  apply (@cind_funcapp (fun lc => ((Nth 1 lc) :: (Nth 2 lc) :: (Nth 3 lc) :: (Nth 1 lc ^^ (Ring [Nth 0 lc])) :: (Nth 4 lc) :: nil))) in D.
  unfold Nth in D; simpl in D.
  apply (@cind_funcapp (fun lc => let fst4 := (firstn 4 lc) in (fst4 ++ (beta fst4) :: (skipn 4 lc)))) in D. simpl in D.

  (* Step 1.1: pose DDH with n n2 n3 n4*)
  pose (DDH n n2 n3 n4 H0 H1 H2 H6 H7 H8) as E.
  (* Step 2.1: FreshInd n1*)
  apply (FreshInd (nonce n1) (nonce n1)) in E.
  (* Step 3.1: FuncAPP g^a and Restr to clean*)
  apply (@cind_funcapp (fun lc => ((Nth 1 lc) :: ((Nth 1 lc) ^^ (Ring [Nth 0 lc])) :: (skipn 2 lc)))) in E.
  unfold Nth in E; simpl in E.
  apply (@cind_funcapp (fun lc => let fst4 := (firstn 4 lc) in (fst4 ++ (beta fst4) :: (skipn 4 lc)))) in E. simpl in E.

  (* Step 4: If_branch*)
  assert (
        [g n; g n ^^ R n1; g n ^^ R n2; g n ^^ R n3]
         ++ (beta [g n; g n ^^ R n1; g n ^^ R n2; g n ^^ R n3])
         :: [(If beta [g n; g n ^^ R n1; g n ^^ R n2; g n ^^ R n3] Then (g n ^^ R n1 ^^ R n2) Else (g n ^^ R n2 ^^ R n3))]
       ~
        [g n; g n ^^ R n1; g n ^^ R n2; g n ^^ R n3]
         ++ (beta [g n; g n ^^ R n1; g n ^^ R n2; g n ^^ R n3])
         :: [(If beta [g n; g n ^^ R n1; g n ^^ R n2; g n ^^ R n3] Then (g n ^^ R n4) Else (g n ^^ R n4))]) as F.
  apply IF_branch; simpl; auto. simpl in F; clear D E.

  (* Step 5: If_same*)
  rewrite (@If_same (beta [g n; g n ^^ R n1 ; g n ^^ R n2; g n ^^ R n3]) (g n ^^ R n4)) in F. unfold id in F; simpl in F.

  apply (@cind_funcapp (fun lc: list ppt => (firstn 4 lc) ++ (skipn 5 lc))) in F.
  simpl in F. auto.

  all : ProveFresh.
  all : ProveContext.
  { apply cApp. ProveContext. ProveContext. }
  { apply cApp. ProveContext. ProveContext. }
Qed.

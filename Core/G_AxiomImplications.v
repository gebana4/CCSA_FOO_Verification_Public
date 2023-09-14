
(************************************************************************)
(* Copyright (c) 2020, Gergei Bana, Qianli Zhang                        *)
(*                                                                      *)
(* This work is licensed under the MIT license. The license is          *)
(* described in the file "LICENSE" available at the root of the source  *)
(* or at https://opensource.org/licenses/MIT                            *)
(************************************************************************)




Require Export F_Axioms.


Proposition ModusTollens :
      (* "meta-level quantification" *) forall P Q : Prop,
      (* "premise1:" *)     (P -> Q) ->
      (* "premise2:" *)     (not Q) ->
      (* "conclusion:" *)   (not P).
Proof. intros P Q. intros. unfold not. intros. apply H in H1.
contradiction.  Qed.




Proposition PBC (*Proof By Contradiction*) :
      (* "meta-level quantification" *) forall P : Prop,
      (* "premise:" *)     ((not P) -> False) ->
      (* "conclusion:" *)    P.
Proof. intros. apply doubleneg_elim. unfold not.
assumption. Qed.

Proposition LEM  (*Law of Excluded Middle*):
      (* "meta-level quantification" *) forall P : Prop,
      (* "conclusion:" *)    P \/ (not P).
Proof. intros P.  apply PBC.
intros. assert (P \/ (not P)). apply or_intror. unfold not.
intros. apply H.
apply or_introl. assumption.
apply H. assumption.  Qed.




(**)
Lemma MT: forall p q: Prop,
    (p -> q) -> not q -> not p.
Proof.
  auto.
Qed.



(**************************************************************************************)
(*********************************** Axioms for Equality ******************************)
(**************************************************************************************)


(* Just for convenient naming  *)

Proposition  ceq_ref :
    forall {x  : ppt} , x  = x .
Proof.
  reflexivity.
Qed.


Proposition  ceq_symm :
    forall {x y : ppt} , (x = y) -> (y = x).
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

Proposition  ceq_trans :
    forall {x y z : ppt}, (x = y) -> (y = z) -> (x = z).
Proof.
  intros.
  rewrite H.
  assumption.
Defined.


Proposition  ceq_transymm :
    forall {x y z : ppt }, (y = x) -> (y = z) -> (x = z).
Proof.
  intros.
  rewrite <- H.
  assumption. 
Defined.





Proposition  ceq_cind :
forall {x y : ppt}, x = y ->  [x] ~ [y].
Proof.
  intros.
  rewrite H.
  apply cind_ref.
Defined.


Proposition  ceq_funcapp :
  forall {lt :  ppt -> ppt} ,
  forall {x y : ppt},
    x = y ->  ((lt x) = (lt y)).
Proof.
  intros.
  rewrite H.
  reflexivity. 
Qed.


Proposition ceq1 :
  forall {x y} , x = y -> [EQ [x ; y]] ~ [TRue].
Proof.
  intros.
  apply ceq.
  assumption.
Qed.

Proposition ceq2 :
  forall {x y} , [EQ [x ; y]] ~ [TRue] -> x = y.
Proof.
  intros.
  apply ceq.
  assumption.
Qed.

Proposition  ceql_ref :
    forall {x  : list ppt} , x  = x .
Proof.
  reflexivity.
Qed.


Proposition  ceql_symm :
    forall {x y : list ppt} , (x = y) -> (y = x).
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

Proposition  ceql_trans :
    forall {x y z : list ppt}, (x = y) -> (y = z) -> (x = z).
Proof.
  intros.
  rewrite H.
  assumption.
Defined.

Proposition  ceq_subeq :
    (*"<<<"*) forall {lt1 :  ppt ->  ppt} {lt2 : ppt -> ppt}, (*">>>"*)
    forall {x y : ppt},
     x = y -> ((lt1 x) = (lt2 x)) -> ((lt1 y) = (lt2 y)).
Proof.
  intros.
  rewrite <- H.
  assumption. 
Qed.


(*******************************************************************************)
(*******************************************************************************)
(********************* Properties of our PPT functions *************************)
(*******************************************************************************)
(*******************************************************************************)


Proposition Func0Const :
  forall (hag : ComputationType) (c :  Symbols hag (narg 0)) (lx : list ppt),
    ConstInt hag c = FuncInt hag (narg 0) c lx.
Proof.
  intros.
  rewrite <- (Const0Func hag c).
  reflexivity.
Qed.


Proposition ConstHAG :
  forall hag hag' c ,
    PPT hag (FuncInt hag' (narg 0) c)
    -> PPT hag (fun _ : list ppt => ConstInt hag' c).
Proof.
  intros.
  rewrite  (Const0Func hag' c).
  assumption.
Qed.


Proposition nonceHonest :
  forall n ,
    (PPT Honest) (fun lx : list ppt => nonce n).
Proof.
  intros.
  simpl (nonce n).
  rewrite Const0Func.
  apply FunHAG.
Qed.


Proposition advAdversarial :
  forall n ,
    (PPT Adversarial) (adv n).
Proof.
  intros.
  simpl (adv n).
  apply FunHAG.
Qed.







(**************************************************************************************)
(**************************************************************************************)
(******************************** CORE  AXIOM IMPLICATIONS ****************************)
(**************************************************************************************)
(**************************************************************************************)







(**************************************************************************************)
(***************************** Properties of Indistinguishability ************************)
(**************************************************************************************)


Proposition FuncApp :
  forall {f : list ppt -> list ppt},
  forall {lx ly} ,
    (Context Adversarial List f )
    ->  lx ~ ly
    -> lx++f(lx) ~ ly++f(ly).
Proof.
  intros.
  assert (forall (f : list ppt -> list ppt) ,
             (Context Adversarial List f )
           -> (Context Adversarial List  (fun lx': list ppt => lx' ++ (f lx')))).
  intros.
  ProveContext.
  assert (lx ++(f lx) ~ ly ++(f ly)).
  apply (@cind_funcapp (fun lx' => lx' ++ (f lx')) lx ly).
  apply H1.
  assumption.
  assumption.
  assumption.
Qed.



(* If f is constant, and lx, ly are lists, then we can apply cind_funcapp for the constant function:*)
Proposition cind_funcapp0 :
  forall x0 :  ppt,
    PPT Adversarial (fun lx => x0)
    -> forall lx ly ,
      lx ~ ly
      -> lx ++ [x0] ~ ly ++ [x0].
Proof.
  intros.
  assert  (Context Adversarial List (fun lx => [x0])).
  ProveContext.
  apply (FuncApp H1).
  assumption.
Qed.



Proposition cind_restr :
  forall {l1 l2 t1 t2},
    ((t1 :: l1) ~ (t2 :: l2))
    -> (l1 ~ l2).
Proof.
  intros.
  assert (TL (t1 :: l1) ~ TL (t2 :: l2)).
  apply (@cind_funcapp TL). ProveContext.
  assumption.
    simpl in H0.
assumption. 
Qed.

Proposition cind_len_rev :
  forall {lt1 lt2 : list ppt},
    lt1 ~ lt2
    -> length lt1 = length lt2.
Proof.
  intros.
  apply doubleneg_elim.
  unfold not at 1.
  intros.
  apply cind_len in H0.
  contradiction.
Qed.





(**************************************************************************************)
(*************************************** Parametric Relations  ************************************)
(**************************************************************************************)






Add Parametric Relation : (list ppt) cind
  reflexivity proved by @cind_ref
  symmetry proved by @cind_sym
  transitivity proved by @cind_trans
  as cind_rel.










(**************************************************************************************)
(******************************** Lemmas for If_Then_Else_ ****************************)
(**************************************************************************************)

Proposition If_same :
  forall {b x} , (If b Then x Else x) = x.
Proof.
  intros.
  assert (x = If TRue Then x Else (If b Then x Else x)).
  rewrite If_true. reflexivity.
rewrite (@If_morph (fun t => If TRue Then x Else t)) in H. 
rewrite If_true in H. rewrite <- H. reflexivity.
ProveContext. 
Qed. 



(* TRue, FAlse are bools, EQ outputs bool, ITE outputs bool if its second and third inputs are bool *)
Proposition TRuebool : bppt TRue.
Proof.
  unfold bppt.
  rewrite If_true.
  reflexivity.
Qed.

Proposition FAlsebool : bppt FAlse.
Proof.
  unfold bppt.
  rewrite If_false.
  reflexivity.
Qed.





(*****************
 **    If_tf    **
 *****************)

(*  This his here just to match the papers. *)

Lemma If_tf :
  forall b , bppt b ->
    b = (If b Then TRue Else FAlse).
Proof.
  intros.
  unfold bppt in H. 
  assumption.
Qed.

(*****************
 **  If_on_tf   **
 *****************)

Lemma If_on_tf :
  forall b x y,
    If b Then x Else y = If (If b Then TRue Else FAlse) Then x Else y.
Proof.
  intros.
  rewrite (@If_morph (fun t => If t Then x Else y)).
  rewrite If_true.
  rewrite If_false.
  reflexivity.
  ProveContext.
Qed. 




(*****************
 **  If_eval   **
 *****************)

  
  
Lemma If_eval :
    (*"<<<"*) forall {tc1 tc2 : ppt -> ppt} ,  (*">>>"*)
forall {b} ,
(*"<<<"*) (ContextTerm General Term  tc1) ->  (ContextTerm General Term tc2) -> bppt b -> (*">>>"*)
     ( If b Then (tc1 b) Else (tc2 b) ) = ( If b Then (tc1 TRue) Else (tc2 FAlse) ).
Proof.
  intros.
  rewrite (If_tf b) at 2 3.
  rewrite (@If_morph (fun t => If b Then tc1 t Else tc2 t)).
  rewrite (@If_idemp b).
  reflexivity. 
  ProveContext.
  assumption.
Qed.









  
Proposition ITEbool :
  forall b x y,
    bppt x ->
    bppt y ->
    bppt (If b Then x Else y).
Proof.
  unfold bppt.
  intros.
  rewrite (@If_morph (fun x => If x Then TRue Else FAlse)). simpl. 
  rewrite <- H. rewrite <- H0.
  reflexivity.
  ProveContext.
Qed.   
  

  
Ltac Provebool :=
  repeat ( intros;
           match goal with
           |H : ?prop |- ?prop => apply H
           |    |- bppt ((FuncInt ?hag ?arg ?f) ?lx)  => unfold f; apply bool1001
           |    |- bppt (ConstInt ?hag ?f)  => unfold f; apply bool1001                                                                                            |    |- bppt (If ?b Then ?x Else ?y)  => apply ITEbool
           end).


Goal bppt FAlse.
  Provebool. 
Qed.

Goal forall x y , bppt y -> bppt (EQ [x ; y]).
  intros.  Provebool. 
Qed.


Goal forall x y z , bppt z -> bppt (If TRue
             Then (EQ [x ; y])
             Else (If FAlse
                     Then z
                     Else (EQ [FAlse ; default])  ) ).
Proof.
Provebool.   
Qed. 






Ltac ProveboolandContext :=
  try (Provebool ; ProveContext).

Proposition  ceq_eq :
    forall {x y : ppt} , x = y -> EQ [x ; y] = TRue.
Proof.
  intros. 
  apply ceq in H.
  apply (@FuncApp (fun lx => [TRue])) in H.  simpl in H.
  apply (@cind_funcapp (fun lx => [EQ lx])) in H; simpl in H.
  assert (H1 := (@ceq_ref TRue)).
  apply ceq in H1.
  apply ceq. 
  apply (cind_trans H H1). ProveContext. ProveContext.
Qed.




Proposition  ceqeq :
    forall {x : ppt} , EQ [x ; x] = TRue.
Proof.
  intros. 
  apply ceq_eq.
  reflexivity.
Qed.


Proposition FreshNEqeq :
      (*"<<<"*) forall nc x, FreshTerm nc x -> (*"<<<"*)
                EQ [nc ; x] = FAlse.
Proof.
  intros.
  apply  (FreshNEq nc x) in H.
  apply (@FuncApp (fun lx => [FAlse])) in H.  simpl in H.
  apply (@cind_funcapp (fun lx => [EQ lx])) in H; simpl in H.
  assert (H1 := (@ceq_ref FAlse)).
  apply ceq in H1.
  apply ceq. 
  apply (cind_trans H H1). ProveContext. ProveContext.
Qed.










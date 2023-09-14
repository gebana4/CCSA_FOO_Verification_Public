
(************************************************************************)
(* Copyright (c) 2020, Gergei Bana, Qianli Zhang                        *)
(*                                                                      *)
(* This work is licensed under the MIT license. The license is          *)
(* described in the file "LICENSE" available at the root of the source  *)
(* or at https://opensource.org/licenses/MIT                            *)
(************************************************************************)



Require Export C_ShallowEmbedding.



(*******************************************************************************)
(************************* Orderding on ComputationType ***************************)
(*******************************************************************************)

(* Reserved Notation "t0 << t1" (at level 80, no associativity).*)



Reserved Notation "t0 <<< t1" (at level 80, no associativity).

(*lt means less than*)
Inductive hag_lt : ComputationType -> ComputationType -> Prop :=
| Det_Hon : Deterministic <<< Honest
| Det_Adv : Deterministic <<< Adversarial
| Hon_Gen : Honest <<< General
| Adv_Gen : Adversarial <<< General
| hag_nil : forall {t}, t <<< t
| hag_trans : forall {t0 t1 t2}, t0 <<< t1 -> t1 <<< t2 -> t0 <<< t2
where "t0 <<< t1" := (hag_lt t0 t1).


Definition hag_ltb (t1 t2: ComputationType) : bool :=
  match t1 with
  | Deterministic => true
  | Honest => match t2 with
             | Deterministic => false
             | Adversarial => false
             | _ => true
             end
  | Adversarial => match t2 with
                   | Deterministic => false
                  | Honest => false
                  | _ => true
                  end
  | General => match t2 with
              | General => true
              | _ => false
              end
  end.

Lemma hag_ltb_lt : forall t1 t2, hag_ltb t1 t2 = true <-> t1 <<< t2.
  split; intros.
  destruct t1; destruct t2; try inversion H; try repeat constructor;
    match goal with
    | |-  Deterministic <<< General =>
      apply (@hag_trans Deterministic Honest General); try repeat constructor
    | |- ?t1 <<< ?t2 =>
      apply (@hag_trans t1 t2 t2); try repeat constructor
    end.
  induction H. all: auto.
  destruct t; auto.
 destruct t0; destruct t1; destruct t2; auto.
Qed.



Lemma hag_reflect : forall t1 t2, reflect (t1 <<< t2) (hag_ltb t1 t2).
  intros t1 t2.
  apply iff_reflect.
  apply (iff_sym (hag_ltb_lt t1 t2)).
Qed.

Ltac ProveHag :=
  match goal with
  | H: ?t0 <<< ?t2 , H0: ?t1 <<< ?t0  |- ?t1 <<< ?t2 => apply (@hag_trans t1 t0 t2)
  | |- ?t1 <<< ?t2 => assert (Prove_HAG := hag_reflect t1 t2); inversion Prove_HAG; auto ; clear Prove_HAG
  end.



Goal Deterministic <<< General.
ProveHag.
Defined.

Goal General <<< General.
  ProveHag.
Defined.

Theorem ppt_up
  : forall {t0 t1 f},
    t0 <<< t1 -> PPT t0 f -> PPT t1 f.
Proof.   intros.
  induction H.
  - apply DeterministicHonest; auto.
  - apply DeterministicAdversarial; auto.
  - apply HonestGeneral; auto.
  - apply AdversarialGeneral; auto.
  - auto.
  - apply IHhag_lt2. apply IHhag_lt1. auto.
Qed.






(**************************************************************************************)
(**************************************************************************************)
(*************************** Auxilliary Functions for Lists ***************************)
(**************************************************************************************)
(**************************************************************************************)



(* 0th entry, head of a list. nil is mappted to default *)
Definition HD (lx : list ppt) : ppt :=  hd default lx.

(* Tail of a list, taking off the first enrty *)
Definition TL (lx : list ppt) : list ppt :=  tl lx.

(* Mapping on the nth element. nil is mappted to default *)
Definition Nth (n : nat) (lx : list ppt) := nth n lx default.


(* Zeroth element and Head are the same *)
Lemma ZerothisHD :
      Nth 0 = HD.
Proof. apply functional_extensionality. intros. induction x. cbn.
 reflexivity. cbn. reflexivity. Qed.

(* S(n)th element and the nth of the tail are the same *)
Lemma SnthisnthTL :
      forall {n} ,
        (fun lx => Nth (S n) lx) = (fun lx => Nth  n (TL lx)).
Proof. intros. apply functional_extensionality. intros. induction x.
cbn. induction n. reflexivity. reflexivity. cbn. reflexivity. Qed.


(* concetanating the head and the tail is the identity map on non-nil. *)
Lemma IDisHDTL :
      forall {lx} ,
        lx <> [] -> lx = (HD lx) :: (TL lx).
Proof. intros. induction lx. destruct H. reflexivity. cbn. reflexivity. Qed.


(**************************************************************************************)
(**************************************************************************************)
(************************************** PPT Ltac **************************************)
(**************************************************************************************)
(**************************************************************************************)




Ltac ProvePPT :=
  repeat ( intros;
match goal with
|H : ?prop |- ?prop => apply H
| |- ?hag1 <<< ?hag2  => ProveHag
|   |- PPT _ (fun _ : list ppt => ConstInt _ _) => apply ConstHAG
      |   |- PPT ?hag (FuncInt ?hag ?arg ?f) => apply FunHAG
      |   |- PPT ?hag2 (FuncInt ?hag1 ?arg ?f) => apply (@ppt_up hag1 hag2)
      |H: PPT ?hag1 ?f  |- PPT ?hag2 ?f => apply (@ppt_up hag1 hag2)
  end).



(* Deterministic algorithms are in particular Honest, Adversarial and General *)
Proposition DeterministicHAG :
      forall {lf : list ppt -> ppt} ,
        (PPT Deterministic) lf
         -> forall (hag : ComputationType) , (PPT hag) lf.
Proof.
  intros. destruct hag. all: ProvePPT.
 Qed.




Proposition HAGGeneral :
      forall (hag : ComputationType) , forall {lf : list ppt -> ppt} ,
          (PPT hag) lf
            -> (PPT General) lf .
Proof.
  intros.
  destruct hag. all : ProvePPT.
Qed.


Proposition GeneralHAG :
      forall {f} {P : Prop} , (PPT General f -> P) ->
forall hag , (PPT hag f -> P).
Proof.
  intros. apply H.  apply (HAGGeneral hag). auto.
Qed.


Proposition HonestGeneral :
      forall {lf : list ppt -> ppt} ,
        (PPT Honest) lf
        -> (PPT General) lf.
Proof. ProvePPT. Qed.

Proposition AdversarialGeneral :
      forall {lf : list ppt -> ppt} ,
        (PPT Adversarial) lf
         -> (PPT General) lf.
Proof. ProvePPT. Qed.








(**************************************************************************************)
(**************************************************************************************)
(************************************** CONTEXTS **************************************)
(**************************************************************************************)
(**************************************************************************************)



(****************************** some auxiliary functions *****************************)


(* Labels to distinguish ppt and list ppt *)

Inductive TermOrList : Set :=
| Term
| List.

Definition ToL (tol : TermOrList) : Set :=
match tol with
| Term => ppt
| List => list ppt
end.



(* Id represents the identity function for ppt -> ppt and
  for list ppt -> list ppt. For ppt -> list ppt it assigns [x] to x, and
for list ppt -> ppt it assigns HD lx to lx*)

Definition Id (tol : TermOrList ) (tol' : TermOrList ) : (ToL tol) -> (ToL tol') :=
match tol with
| Term => match tol' with Term => (fun x : ppt => x) | List => (fun x : ppt => [x]) end
| List => match tol' with Term => (fun lx : list ppt => Nth 0 lx) | List => (fun lx : list ppt => lx) end
end.


Proposition IdNth :
forall tol, (fun x  => Id tol Term x ) = (fun x  => Nth 0 (Id tol List x )).
Proof. intros. destruct tol.
  - unfold Id at 2. unfold HD. simpl. auto.
  - unfold Id. auto.
Qed.








(**************************************************************************************)
(********************************* Context Definition *********************************)
(**************************************************************************************)


(* Context is something that is a term context created with our function symbols. Accordingly,
it has Deterministic, Honest, Adversarial, General versions. *)

Section Context.
(* Recursive definition of a Context outputting a list ppt and a ContextTerm outputting
a ppt. The input for both is (ToL tol), which is either ppt or list ppt.
for each hag Deterministic, Honest, Adversarial, General, contexts are defined.
 *)
(* Parameter ListContext : ComputationType -> (list ppt -> list ppt) -> Prop. *)
(* Parameter TermContext : ComputationType -> (ppt -> list ppt) -> Prop. *)
Variable hag : ComputationType.
(* Below ct is for ContextTerm variables, c is for Context variables *)

(* It might be useful to separate contexts with list operations and ID and those with function
symbols *)



Inductive Context (tol : TermOrList) : (ToL tol -> list ppt) -> Prop :=  (* metapredicate *)
| clength   :
      forall {c n} ,
        Context tol c
        -> Context  tol (fun x => (skipn ((length (c x)) - n) (c x)))
| cApp  :
      forall {c1 c2},
        Context tol c1
        -> Context tol c2
        -> Context tol  (fun x => (c1 x)++(c2 x))
| cNth :
      forall {c},
      (forall n, ContextTerm tol (fun x => (Nth n (c x)))) ->
      Context tol c
| cId  :
    Context tol (Id tol List)
with ContextTerm (tol : TermOrList)  : (ToL tol -> ppt) -> Prop :=
| ctId   :
      ContextTerm tol (Id tol Term)
| ctNth :
      forall {n c},
        Context tol c
          -> ContextTerm tol (fun x => (Nth n (c x)))
| ctCT:
      forall {f: list ppt -> ppt} {c : ToL tol -> list ppt} ,
        (PPT hag) f
        -> Context tol c
        -> ContextTerm tol  (fun x => (f (c x))).
End Context.




(**************************************************************************************)
(********************************* Mutual Induction *********************************)
(**************************************************************************************)


Scheme Context_mut := Minimality for Context Sort Prop
  with ContextTerm_mut := Minimality for ContextTerm Sort Prop.





(**************************************************************************************)
(********************************* Properties *********************************)
(**************************************************************************************)



Proposition Nth0_and_HD : forall lx, Nth 0 lx = HD lx.
  intros.
unfold HD.  unfold Nth.
induction lx.
auto.
simpl.
reflexivity.
Qed.


Proposition IdHD :
forall tol, (fun x  => Id tol Term x ) = (fun x  => HD (Id tol List x )).
Proof. intros. destruct tol.
  - unfold Id at 2. unfold HD. simpl. auto.
  - unfold Id. apply functional_extensionality.
    intros. rewrite Nth0_and_HD. auto.
Qed.



Proposition Nth_and_TL : forall lx n, Nth (S n) lx = Nth n (TL lx).
  intros.
  unfold TL.  unfold Nth.
  induction n.
induction lx.
simpl.
reflexivity.
simpl.
reflexivity.
induction lx. simpl.
reflexivity.
simpl.
reflexivity.
Qed.



Proposition ctHD  :
      forall {hag tol c} ,
        Context hag tol c
        -> ContextTerm  hag tol (fun x => (HD (c x))).
Proof.
  intros.
  assert ( (fun x : ToL tol => HD (c x)) =  (fun x : ToL tol => Nth 0 (c x)) ).
  apply functional_extensionality.
  intros.
  rewrite  Nth0_and_HD.
  reflexivity.
  rewrite H0.
  apply ctNth.
  assumption.
Qed.


(* ConstInt map of the right hag class is ContextTerm *)
Proposition ctPPT0 :
      forall {hag tol x0} ,
        (PPT hag) (fun lx => x0)
        -> ContextTerm hag tol (fun x => x0).
Proof. intros.   apply (@ctCT hag tol (fun lx : list ppt => x0) (Id tol List) H).
apply cId. Qed.






Proposition DetFSContext :
  forall arg  hag f,
    ContextTerm hag List (FuncInt Deterministic arg f).
Proof. intros.   apply ctCT. destruct hag ; ProvePPT. apply cId. Qed.



Proposition DetCSContext :
  forall c  hag tol,
    ContextTerm hag tol (fun lx => ConstInt Deterministic c).
Proof. intros.   apply ctPPT0.   destruct hag ; ProvePPT.
Qed.



Proposition ctl :
      forall  {hag tol c} ,
        ContextTerm hag tol c
        -> Context  hag tol (fun x => [c x]).
Proof.
  intros.
  apply cNth.
  intros.
  induction n.
unfold Nth.
simpl.
apply H.
unfold Nth.
induction n.
simpl.
apply DetCSContext.
simpl.
apply DetCSContext.
Qed.


Proposition cTL   :
      forall {hag tol c} ,
        Context hag tol c
        -> Context  hag tol (fun x => (TL (c x))).
Proof.
  intros.
  apply cNth.
  intros.
  assert ((fun x : ToL tol => Nth n (TL (c x))) = (fun x : ToL tol => Nth (S n)(c x))).
  apply functional_extensionality.
  intros.
  rewrite Nth_and_TL.
  reflexivity.
  rewrite H0.
apply ctNth.
assumption.
Qed.


Proposition Nth_and_firstn1 :
  forall lx n1 n2, n1 < n2 -> Nth n1 (firstn n2 lx) = Nth n1 lx.
Proof.
  intros lx.
  - induction lx.
    + intros.
      destruct n2.
      * simpl firstn.
        reflexivity.
      * simpl firstn.
        reflexivity.
    + intros.
      destruct n2.
      * assert (not (n1 < 0)).
        {  lia. }
        contradiction.
      *  simpl firstn.
         destruct n1.
         ** unfold Nth.
            simpl nth.
            reflexivity.
         ** unfold Nth.
            simpl nth.
            unfold Nth in IHlx.
            apply IHlx.
            lia.
Qed.



Proposition Nth_and_firstn2 :
  forall lx n1 n2,  n1 >= n2 -> Nth n1 (firstn n2 lx)  = default.
Proof.
  intros lx.
  - induction lx.
    + intros.
      destruct n2.
      * simpl firstn.
        unfold Nth.
        destruct n1.
        ** simpl nth.
           reflexivity.
        ** simpl nth.
           reflexivity.
      * simpl firstn.
        unfold Nth.
        destruct n1.
        ** simpl nth.
           reflexivity.
        ** simpl nth.
           reflexivity.
    + intros.
      destruct n2.
      * simpl firstn.
        unfold Nth.
        destruct n1.
        ** simpl nth.
           reflexivity.
        ** simpl nth.
           reflexivity.
      * simpl firstn.
        unfold Nth.
        destruct n1.
        ** assert (not (0 >= S n2)).
           { lia. }
           contradiction.
        ** simpl nth.
           unfold Nth in IHlx.
           apply IHlx.
           lia.
Qed.







Proposition cfirstn   :
      forall {hag tol c n} ,
        Context hag tol c
        -> Context  hag tol (fun x => (firstn n (c x))).
Proof.
  intros.
  apply cNth.
  intros.
  assert ((n0 < n) \/ (n0 >= n)).
  lia.
  destruct H0.
  assert ((fun x : ToL tol => Nth n0 (firstn n (c x))) = (fun x : ToL tol => Nth n0 (c x) )).
  apply functional_extensionality.
  intros.
  rewrite Nth_and_firstn1.
  reflexivity.
  assumption.
  rewrite H1.
  apply ctNth.
  assumption.
  assert ((fun x : ToL tol => Nth n0 (firstn n (c x))) = (fun x : ToL tol => default)).
  apply functional_extensionality.
  intros.
  rewrite Nth_and_firstn2.
  reflexivity.
  assumption.
  rewrite H1.
  apply DetCSContext.
Qed.


Proposition Nth_and_skipn :
  forall lx n1 n2, Nth n1 (skipn n2 lx) = Nth (n1 + n2) lx.
Proof.
  intros lx.
  - induction lx.
    + intros.
      destruct n2.
      * simpl skipn.
        assert (n1 + 0 =n1).
        { lia. }
        rewrite H.
        reflexivity.
      * simpl skipn.
        unfold Nth.
        destruct n1.
        ** assert (0 + S n2 = S n2).
           { lia. }
           simpl.
           reflexivity.
        ** assert (S n1 + S n2 = S (S (n1 + n2))).
           { lia. }
           simpl.
           reflexivity.
    + intros.
      destruct n2.
      * simpl skipn.
        assert (n1 + 0 =n1).
        { lia. }
        rewrite H.
        reflexivity.
      * simpl skipn.
        rewrite IHlx.
        assert ((n1 + S n2) = S (n1 + n2)).
        { lia. }
        rewrite H.
        unfold Nth.
        simpl.
        reflexivity.
Qed.




Proposition cskipn   :
      forall {hag tol c n} ,
        Context hag tol c
        -> Context  hag tol (fun x => (skipn n (c x))).
Proof.
  intros.
  apply cNth.
  intros.
  assert ((fun x : ToL tol => Nth n0 (skipn n (c x))) = (fun x : ToL tol => Nth (n0 + n) (c x))).
  apply functional_extensionality.
  { intros.
    apply Nth_and_skipn. }
  rewrite H0.
  apply ctNth.
  assumption.
Qed.




Proposition  cnil   :
      forall tol hag , Context  hag tol (fun x : ToL tol => nil).
Proof. intros. destruct tol. simpl. assert  ((fun (x : ppt) =>  []) = (fun (x: ppt)  => firstn 0 [x])).
apply functional_extensionality. unfold firstn. intros. auto.
rewrite H. apply @cfirstn. apply ctl. apply ctId.   assert  ((fun (x : list ppt) =>  []) = (fun (x: list ppt)  => firstn 0 x)).
apply functional_extensionality.  unfold firstn. intros. auto. simpl.   rewrite H. apply @cfirstn.
apply cId. Qed.



Proposition cCons  :
      forall tol hag {ct c},
        ContextTerm hag tol ct
        -> Context hag tol c
        -> Context hag tol (fun x => (ct x)::(c x)).
Proof. intros. assert ((fun x => (ct x)::(c x)) = (fun x => [ct x]++(c x))).
apply functional_extensionality. intros. rewrite <- (app_nil_l (c x )) at 1. apply app_comm_cons.
rewrite H1. apply cApp. apply ctl. auto. auto. Qed.


Proposition cCont   :
      forall hag tol {c1 c2 } ,
        Context hag List  c1
        -> Context hag tol c2
        -> Context hag tol (fun x   => (c1 (c2 x)) ).
Proof.
  Proof. intros.
         apply ( Context_mut  hag List (fun c =>   Context hag tol (fun x : ToL tol => c (c2 x)))
                   (fun c =>   ContextTerm hag tol (fun x : ToL tol => c (c2 x)))); try (intros; unfold Id; constructor; auto; constructor; auto).
Qed.



Proposition tcCont   :
      forall  hag tol {tc1 c2},
        Context hag  Term tc1
        -> ContextTerm hag  tol c2
        -> Context  hag tol (fun x => (tc1  (c2 x))).
 Proof. intros. apply (Context_mut hag   Term (fun c =>  Context  hag tol (fun x : ToL tol => c (c2 x)))
                         (fun c =>  ContextTerm  hag tol (fun x : ToL tol => c (c2 x)))) ; try (intros; unfold Id; constructor; auto; constructor; auto; apply ctl; auto).
  - unfold Id. auto.
Qed.








Theorem ctx_up1:
   forall tol c0 f,
        (Context c0 tol f -> forall c1, (c0 <<< c1) -> Context c1 tol f).
Proof. intros.
   apply (Context_mut c0 tol) with
      (P := fun  f =>  Context  c1 tol f)
      (P0 := fun f => ContextTerm  c1 tol f); intros;  try (intros; unfold Id; constructor; auto; constructor; auto; apply ctl; auto). apply ctCT; ProvePPT.
Qed.


Theorem ctx_up2:
           forall tol c0 f,
                (ContextTerm  c0 tol f -> forall c1, (c0 <<< c1) -> ContextTerm  c1 tol f).
Proof. intros.
   apply (ContextTerm_mut c0 tol) with
      (P := fun  f =>  Context  c1 tol f)
      (P0 := fun f => ContextTerm  c1 tol f); intros; try (intros; unfold Id; constructor; auto; constructor; auto; apply ctl; auto). apply ctCT; ProvePPT.
auto. Qed.






Theorem ctx_up:
            (forall tol c0 f,
                (Context c0 tol f -> forall c1, (c0 <<< c1) -> Context c1 tol f))
          /\ (forall tol c0 f,
                (ContextTerm  c0 tol f -> forall c1, (c0 <<< c1) -> ContextTerm  c1 tol f)).
Proof.
apply conj. apply ctx_up1. apply ctx_up2.
Qed.




Theorem ContextUp:
            forall c0 c1 tol f,
                c0 <<< c1 -> Context c0 tol f ->  Context c1 tol f.
Proof.
   intros. apply (ctx_up1 tol c0 f H0 c1). auto.
Qed.

Theorem ContextTermUp:
          forall c0 c1 tol  f,
                c0 <<< c1 -> ContextTerm c0 tol f ->  ContextTerm c1 tol f.
Proof.
   intros. apply (ctx_up2 tol c0 f H0 c1). auto.
Qed.



Goal (forall tol f, Context  Deterministic tol f -> Context Honest tol f).
Proof. intros tol f. apply ContextUp.
    ProveHag.
Qed.

Goal (forall tol f, Context  Deterministic tol f -> Context General tol f).
Proof. intros tol f. apply ContextUp.
    ProveHag.
Qed.





(*
(* [ ] makes a Context from ContextTerm*)
Proposition ctl :
      forall {hag tol ct},
        ContextTerm hag tol ct
        -> Context hag tol (fun x => [ (ct x)]).
Proof. intros. apply ctl. auto. Qed.*)


(* Various ways of combining two Contexts *)
Proposition ctlCont :
      forall {hag tol c1 c2},
        Context hag Term c1
        -> ContextTerm hag tol c2
        -> Context hag tol (fun x => (c1  (c2 x))).
Proof. intros. apply tcCont.   assumption. assumption. Qed.

Proposition cllCont :
      forall {hag tol c1 c2},
        Context hag List c1
        -> Context hag tol c2
        -> Context hag tol (fun x => (c1  (c2 x))).
Proof. intros. apply cCont.  assumption. assumption. Qed.

Proposition cttCont :
      forall {hag tol tc1 tc2},
        ContextTerm hag Term tc1
        -> ContextTerm hag tol tc2
        -> ContextTerm hag tol (fun x => (tc1  (tc2 x))).
Proof. intros. assert ((fun x : ToL tol => tc1 (tc2 x))= (fun x : ToL tol => HD [tc1 (tc2 x)])). simpl. reflexivity.
rewrite H1. apply ctHD.  apply (@ctlCont hag tol (fun x => [tc1 x]) tc2). apply ctl. assumption. assumption. Qed.

Proposition cltCont :
      forall {hag tol tc1 tc2},
        ContextTerm hag List tc1
        -> Context hag tol tc2
        -> ContextTerm hag tol (fun x => (tc1  (tc2 x))).
Proof. intros. assert ((fun x : ToL tol => tc1 (tc2 x))= (fun x : ToL tol => HD [tc1 (tc2 x)])). simpl. reflexivity.
rewrite H1. apply ctHD.  apply (@cllCont hag tol (fun x => [tc1 x]) tc2). apply ctl. assumption. assumption. Qed.




Proposition NthContext:
forall {hag n},
 ContextTerm hag List (Nth n).
Proof. intros. apply ctNth. apply cId. Qed.





Proposition HDContext:
forall {hag},
 ContextTerm hag List HD.
Proof. intros. apply ctHD. apply cId. Qed.



Proposition TLContext:
forall {hag},
 Context hag List TL.
Proof. intros. apply cTL. apply cId. Qed.

Proposition firstnContext:
forall {hag n},
 Context hag List (firstn n).
Proof. intros. apply cfirstn. apply cId. Qed.

Proposition skipnContext:
forall {hag n},
 Context hag List (skipn n).
Proof. intros. apply cskipn. apply cId. Qed.

Proposition lengthContext:
forall {hag n},
 Context hag List (fun x => (skipn ((length x) - n) x)).
Proof. intros. apply clength. apply cId. Qed.




Proposition HonFSContext :
  forall arg f,
    ContextTerm Honest List (FuncInt Honest arg f)
    /\ ContextTerm General List (FuncInt Honest arg f).
Proof. intros. repeat apply conj;   apply ctCT; ProvePPT; apply cId. Qed.

Proposition AdvFSContext :
  forall arg (f: Symbols Adversarial arg) ,
    ContextTerm Adversarial List (FuncInt Adversarial arg f)
    /\ ContextTerm General List (FuncInt Adversarial arg f).
Proof. intros. repeat apply conj;   apply ctCT; ProvePPT; apply cId. Qed.

Proposition GenFSContext :
  forall arg f,
    ContextTerm General List (FuncInt General  arg f).
Proof. intros.  apply ctCT. apply FunHAG. apply cId.  Qed.




Proposition HonCSContext :
  forall  c tol,
    ContextTerm Honest tol (fun lx => ConstInt Honest c)
    /\ ContextTerm General tol (fun lx => ConstInt Honest c).
Proof. intros.  repeat apply conj; apply ctPPT0; ProvePPT.  Qed.

Proposition AdvCSContext :
  forall c tol,
    ContextTerm Adversarial tol (fun lx => ConstInt Adversarial c)
    /\ ContextTerm General tol (fun lx => ConstInt Adversarial c).
Proof. intros.  repeat apply conj; apply ctPPT0; ProvePPT. Qed.


Proposition GenCSContext :
  forall c tol, ContextTerm General tol (fun lx => ConstInt General c).
Proof. intros.  apply ctPPT0. ProvePPT. Qed.



Proposition ctConstant :
      forall {x0 : ppt} {tol},
        ContextTerm General tol (fun x => x0).
Proof. intros. apply ctPPT0. apply ConstantGeneral. Qed.

Proposition cConstant :
  forall {x : list ppt}  {tol} ,
    Context General tol (fun _ : ToL tol => x).
Proof. intros. induction x. apply cnil. apply cCons.  apply ctConstant.  trivial. Qed.

(**************************************************************************************)
(***************************** Automated Check of Context *****************************)
(**************************************************************************************)


(* Automated proof that something is a context. *)
Ltac ProveContext :=
  repeat ( intros;
match goal with
      |H : ?prop |- ?prop => apply H
      |    |- ?c1 <<< ?c2  => ProveHag
      |    |- PPT ?hag ?f  => ProvePPT
      |H : Context Deterministic ?tol ?c |- Context ?hag ?tol ?c => apply (ContextUp Deterministic)
      |H : Context Honest ?tol ?c |- Context General ?tol ?c => apply (ContextUp Honest)
      |H : Context Adversarial ?tol ?c |- Context General ?tol ?c => apply (ContextUp Adversarial)
      |H : ContextTerm Deterministic ?tol ?c |- ContextTerm ?hag ?tol ?c => apply (ContextTermUp Deterministic)
      |H : ContextTerm Honest ?tol ?c |- ContextTerm General ?tol ?c => apply (ContextTermUp Honest)
      |H : ContextTerm Adversarial ?tol ?c |- ContextTerm General ?tol ?c => apply (ContextTermUp Adversarial)
 (*    |H : ComputationType |- _ => destruct H *)
  (*    |H : TermOrList  |- _ => destruct H *)
      |   |- Context _ List (fun lx  => lx) => apply @cId
      |   |- Context _ List id => apply @cId
      |   |- Context _ _ (fun x   => ?a :: ?m) => apply @cCons
      |   |- Context _ _ (fun x   => ?a ++ ?m) => apply @cApp
      |   |- Context _ List (cons ?a) => apply @cCons
      |   |- Context _ _ (fun x => [ ]) => apply @cnil
      |   |- Context _ _ TL => apply @TLContext
      |   |- Context _ _ (fun x   => TL ?t) => apply @cllCont
      |   |- Context _ _ (firstn ?n) => apply @firstnContext
      |   |- Context _ _ (fun x   => firstn ?n ?t) => apply @cllCont
      |   |- Context _ _ (skipn ((length ?t) - ?n)) => apply @lengthContext
      |   |- Context _ _ (fun x   => skipn ((length ?t) - ?n) ?t) => apply @lengthContext
      |   |- Context _ _ (skipn ?n) => apply @skipnContext
      |   |- Context _ _ (fun x   => skipn ?n ?t) => apply @cllCont
      |   |- ContextTerm _ Term (fun x  => x) => apply @ctId
      |   |- ContextTerm _ Term id => apply @ctId
   (*   |   |- ContextTerm _ _ (fun x => TRue) => apply @TRueContext
      |   |- ContextTerm _ _ (fun x => FAlse) => apply @FAlseContext
      |   |- ContextTerm _ _ (fun x => default) => apply @defaultContext*)
      |   |- ContextTerm _ _ (fun x => ConstInt Deterministic ?c) => apply @DetCSContext
      |   |- ContextTerm _ _ (fun x => ConstInt Honest ?c) => apply @HonCSContext
      |   |- ContextTerm _ _ (fun x => ConstInt Adversarial ?c) => apply @AdvCSContext
      |   |- ContextTerm _ _ (fun x => ConstInt General ?c) => apply @GenCSContext
  (*  |   |- ContextTerm _ _ (fun x => rbk ?n) => apply @rbkContext *)
      |   |- ContextTerm _ _ (Nth ?n) => apply @NthContext
      |   |- ContextTerm _ _ HD => apply @HDContext
      |   |- ContextTerm _ List (FuncInt Deterministic ?arg ?f) => apply @DetFSContext
      |   |- ContextTerm _ List (FuncInt Honest ?arg ?f) => apply @HonFSContext
      |   |- ContextTerm _ List (FuncInt Adversarial ?arg ?f) => apply @AdvFSContext
      |   |- ContextTerm _ List (FuncInt General ?arg ?f) => apply @GenFSContext
  (*    |   |- ContextTerm _ _ (adv _) => apply @advContext  *)
   (*   |   |- ContextTerm _ _ If_Then_Else_ => apply @ITEContext  *)
  (*    |   |- ContextTerm _ _ EQ => apply @EQContext *)
      |   |- ContextTerm _ _ (fun x   => HD ?t) => apply @cltCont
      |   |- ContextTerm _ _ (fun x  => Nth ?n ?t) => apply @cltCont
   (*   |   |- ContextTerm _ _ (fun x   => adv ?n ?t) => apply @cltCont *)
   (*   |   |- ContextTerm _ _ (fun x   => EQ ?t) => apply @cltCont *)
   (*   |   |- ContextTerm _ _ (fun x   => If_Then_Else_ ?t) => apply @cltCont *)
      |   |- ContextTerm _ _ (fun x  => (FuncInt ?hag' ?arg ?f) ?t) => apply @cltCont
      | H : Context _ List ?c  |- Context _ _ (fun lx => (?c ?t)) => apply (@cllCont _ _)
      | H : Context _ List ?c  |- Context _ List (fun lx : list ppt => (?c ?t)) => apply (@cllCont _ List)
      | H : Context _ List ?c  |- Context _ Term (fun x : ppt => (?c ?t)) => apply (@cllCont _ Term)
      | H : Context _ Term ?c  |- Context _ _ (fun x : ToL _ => (?c ?t)) => apply (@ctlCont _ _)
      | H : Context _ Term ?c  |- Context _ Term (fun x : ppt => (?c ?t)) => apply (@ctlCont _ Term)
      | H : Context _ Term ?c  |- Context _ List (fun lx : list ppt => (?c ?t)) => apply (@ctlCont _ List)
      | H : ContextTerm _ List ?c  |- ContextTerm _ _ (fun lx : ToL _ => (?c ?t)) => apply (@cltCont _ _)
      | H : ContextTerm _ List ?c  |- ContextTerm _ List (fun lx : list ppt => (?c ?t)) => apply (@cltCont _ List)
      | H : ContextTerm _ List ?c  |- ContextTerm _ Term (fun x : ppt => (?c ?t)) => apply (@cltCont _ Term)
      | H : ContextTerm _ Term ?c  |- ContextTerm _ _ (fun x : ToL _ => (?c ?t)) => apply (@cttCont _ _)
      | H : ContextTerm _ Term ?c  |- ContextTerm _ Term (fun x : ppt => (?c ?t)) => apply (@cttCont _ Term)
      | H : ContextTerm _ Term ?c  |- ContextTerm _ List (fun lx : list ppt => (?c ?t)) => apply (@cttCont _ List)
      | H : ContextTerm ?hag List (fun _  => ?t)   |- ContextTerm ?hag Term (fun _  => ?t) => apply (@cltCont H (@cId ?hag Term))
      |   |- ContextTerm _ _ (fun x => (?f ?t)) => apply @ctCT
      |   |- ContextTerm General _ (fun x => ?t) => apply @ctConstant
      |   |- Context General _ (fun x => ?t) => apply @cConstant
      |   |- ContextTerm _ _ (fun x  => ?t) => apply @ctPPT0
  end). (* Works quite well but needs to be extended. PPT _ _ goals should be skipped down. *)




(******************************** Testing the Automation ******************************)




(* TRue, FAlse, default, EQ, If Then Else are contexts *)
Parameter pairs : Symbols Deterministic (narg 2).

Notation "'pair'" := (FuncInt Deterministic (narg 2) pairs).

Goal forall (nl : list ppt), Context Adversarial List
  (fun lx : list ppt =>
   firstn (length nl) lx ++
   [pair [Nth (length nl + 0) lx; Nth (length nl + 1) lx];
   pair [Nth (length nl + 2) lx; Nth (length nl + 3) lx]]).
ProveContext. Defined.



Goal Deterministic <<< General. ProveContext. Defined.

Goal forall tol c , ContextTerm Adversarial tol c -> ContextTerm General tol c.
intros. ProveContext.  Defined.

Proposition defaultContext :
      forall {hag tol},
        ContextTerm hag tol (fun x => default).
Proof. ProveContext. Qed.

(*Proposition cTRue :
forall {hag tol},
    Context hag tol (fun x => [TRue]).
Proof. intros. apply ctl. apply TRueContext. Qed.*)
Proposition FAlseContext :
      forall {hag tol},
        ContextTerm hag tol (fun x => FAlse).
Proof. ProveContext. Qed.
(*Proposition cFAlse :
      forall {hag tol},
        Context hag tol (fun x => [FAlse]).
Proof. intros. apply ctl. apply FAlseContext.
Qed.*)

Proposition TRueContext :
      forall {hag tol},
        ContextTerm hag tol (fun x => TRue).
Proof. ProveContext. Qed.



Proposition nonceContext :
  forall n  tol ,
    ContextTerm Honest tol (fun x => nonce n)
    /\ ContextTerm General tol (fun x => nonce n) .
Proof.  intros. repeat apply conj ; ProveContext.    Qed.




Proposition ITEContext :
      forall {hag},
        ContextTerm hag List If_Then_Else_.
Proof. intros. destruct hag ; ProveContext.  Qed.


Proposition ctITE :
      forall {hag tol tc1 tc2 tc3},
        ContextTerm hag tol tc1
        -> ContextTerm hag tol tc2
        -> ContextTerm hag tol tc3
        -> ContextTerm hag tol (fun x => (If_Then_Else_ [(tc1 x); (tc2 x); (tc3 x)])).
Proof. ProveContext. Qed.

Proposition cITE :
      forall {hag tol tc1 tc2 tc3},
        ContextTerm hag tol tc1
        -> ContextTerm hag tol tc2
        -> ContextTerm hag tol tc3
        -> Context hag tol (fun x => [If_Then_Else_ [(tc1 x); (tc2 x); (tc3 x)]]).
Proof. ProveContext. Qed.






Proposition ctEQ :
      forall {hag tol tc1 tc2},
        ContextTerm hag tol tc1
        -> ContextTerm hag tol tc2
        -> ContextTerm hag tol (fun x => (EQ [(tc1 x) ; (tc2 x)])).
Proof. ProveContext. Qed.
Proposition cEQ :
      forall {hag tol tc1 tc2},
        ContextTerm hag tol tc1 ->ContextTerm hag tol tc2 -> Context hag tol (fun x =>  [EQ [(tc1 x) ; (tc2 x)]]).
Proof. intros. ProveContext. Qed.


Proposition EQContext :
      forall {hag},
        ContextTerm hag List EQ.
Proof. ProveContext. Qed.







Proposition FAlseContext2 :
      forall {hag tol},
        ContextTerm hag tol (fun x => FAlse).
Proof. ProveContext. Qed.






Proposition advContext :
  forall n  ,
    ContextTerm Adversarial List (adv  n)
    /\ ContextTerm General List (adv n) .
Proof. intros. repeat apply conj; ProveContext. Qed.



Proposition bla11 :
  Context Adversarial List (fun x0 : ToL List => x0).
Proof.  ProveContext. Qed.


Proposition  bla10: forall tc1 tc2 , ContextTerm Honest Term tc1 -> ContextTerm Honest Term tc2 -> Context Honest Term
  (fun x : ToL Term => [tc1 x; tc2 x]).
Proof.
 ProveContext. Qed.

Proposition bla : forall hag , ContextTerm hag Term (fun x : ToL Term => x).
Proof. ProveContext.  Qed.

Proposition bla0 : forall hag , ContextTerm hag List (fun x : ToL List => HD x ).
Proof.   ProveContext.  Qed.

Proposition bla2 :  forall hag  t1 t2 ,
(PPT hag (fun x => t1)) -> (PPT hag (fun x => t2)) ->
ContextTerm hag List (fun x : ToL List => (EQ [t1 ; t2])).
Proof. ProveContext.  Qed.

(* Proposition bla3 : forall t : ppt , ContextTerm General Term (fun x : ToL Term => (EQ [x ; t])).
Proof. ProveContext.  Qed.

Proposition bla4 : forall t1 t2 : ppt , ContextTerm General Term (fun x : ToL Term => (If x Then t1 Else t2)).
Proof. ProveContext. Qed.

Proposition bla5 : forall b (x1 : ppt) (y1:ppt) t1  , ContextTerm General Term
  (fun t2' : ToL Term =>
   If b
      Then If b
              Then t1 x1
              Else t1 y1
      Else t2').
Proof. ProveContext. Qed.


Proposition bla6 : Context General Term (fun x : ToL Term => [x;x]).
Proof. ProveContext.    Qed.


Proposition ite : ContextTerm General Term (fun x => If x Then x Else x).
Proof.   ProveContext.  Qed.
*)



(********************************* EXAMPLE: Projection ********************************)

Proposition proj02 :
      forall {hag} ,
        Context hag List (fun x => [HD x ; HD (TL (TL x))]).
Proof. ProveContext. Qed.



(****************** EXAMPLE: Permutation - using the nth, it's easier *****************)

Proposition perm021 :
      forall {hag } c , Context hag List c ->
        Context hag List (fun x => [Nth 0 (c x) ; Nth 2 x ; Nth 1 x ]).
Proof. ProveContext.  Qed.

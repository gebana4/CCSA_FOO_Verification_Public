
(************************************************************************)
(* Copyright (c) 2020, Gergei Bana                                      *)
(*                                                                      *)
(* This work is licensed under the MIT license. The license is          *)
(* described in the file "LICENSE" available at the root of the source  *)
(* or at https://opensource.org/licenses/MIT                            *)
(************************************************************************)



Require Export D_Contexts.



(* For a nonce "nc", "Fresh nc t" expresses that "t" is
made up of nonces and mixed function symbols, and "nc" does not
occur in "t". This will ensure that "nc" and "t" contain independent randomness
only. Note that Honest and Mixed function symbols must have
interpretations that ensure that different sections of the honest tape are used.
If other Honest, Mixed function symbols or contstants are added then this has to be
modified. *)



Inductive Fresh : ppt -> list ppt -> Prop := (* metapredicate *)
| frnil : forall n, Fresh (nonce n) nil
| frConc : forall nc (t : ppt) (tc : list ppt) ,
    (FreshTerm nc t)
    -> (Fresh nc tc)
    -> (Fresh nc (t :: tc))
with FreshTerm : ppt -> ppt -> Prop :=
| frtNN : forall (n m : nat) , n <> m
                        -> (FreshTerm (nonce n) (nonce m))
| frtFAdv: forall nc (t: list ppt -> ppt) (tc : list ppt) ,
    (ContextTerm Adversarial List t)
    -> Fresh nc tc
    -> FreshTerm nc (t tc)
| frtCAdv: forall n (t: ppt) ,
     (ContextTerm Adversarial List (fun x => t))
    -> FreshTerm (nonce n) t.




Definition Nonce (nc: ppt ) : Prop := exists n, nonce n = nc.


Lemma frtCAdvVar: forall nc (t: ppt) ,
    (ContextTerm Adversarial List (fun x => t))
    -> Nonce nc
    -> FreshTerm nc t.
Proof. intros. unfold Nonce in H0. inversion H0.
rewrite <- H1. apply frtCAdv.  ProveContext.  Qed.


Lemma frnilVar : forall nc,  Nonce nc -> Fresh nc nil.
Proof. intros. unfold Nonce in H; inversion H.
rewrite <- H0. apply frnil. Qed.

Lemma FreshIsNonce : forall nc tl, Fresh nc tl  -> Nonce nc.
Proof. intros. induction H. unfold Nonce.  exists n. auto. inversion IHFresh.
exists x. auto. Qed.


Scheme Fresh_mut := Minimality for Fresh Sort Prop
  with FreshTerm_mut := Minimality for FreshTerm Sort Prop.




Lemma FreshTermIsNonce : forall nc t, FreshTerm nc t  -> Nonce nc.
Proof. intros. apply (FreshTerm_mut  (fun nc t => Nonce nc)
(fun nc tl => Nonce nc)) in H. auto. intros. unfold Nonce. exists n.
auto . intros. auto. intros. unfold Nonce. exists n. auto.
intros. auto. intros. unfold Nonce. exists n. auto.
Qed.


Lemma invfrConc :
 forall nc (t : ppt) (tl : list ppt) ,
    (Fresh nc (t :: tl))
     -> ((FreshTerm nc t)
    /\ (Fresh nc tl)).
Proof.
intros. inversion H. apply conj. auto. auto.
Qed.



Lemma frFAdv :
forall nc (tl: list ppt -> list ppt) (tc : list ppt) ,
    (Context Adversarial List tl)
    -> Fresh nc tc
    -> Fresh nc (tl tc).
Proof. intros.
assert (exists (x : list ppt) , x = (tl tc)).
exists (tl tc). reflexivity. destruct H1. rewrite <- H1.
assert (exists tl1, Context Adversarial List tl1 /\ x = tl1 tc).
exists tl. auto. clear H1.
induction x. apply frnilVar. apply FreshIsNonce in H0.  auto. apply frConc.
inversion H2. assert (a = HD (x0 tc)). inversion_clear H1.
rewrite <- H4. unfold HD. simpl. reflexivity. rewrite H3.
apply (frtFAdv nc (fun lx => HD (x0 lx))). destruct H1.
ProveContext.    auto. auto.
apply IHx. inversion_clear H2. inversion_clear H1.
exists (fun lx => TL (x0 lx)). apply conj.
ProveContext. rewrite <- H3. unfold TL. simpl.  reflexivity.
Qed.


Lemma frlConc : forall nc (tl : list ppt) (tc : list ppt) ,
    (Fresh nc tl)
    -> (Fresh nc tc)
    -> (Fresh nc (tl ++ tc)).
Proof. intros. induction tl. simpl. auto.
rewrite <- app_comm_cons. apply frConc.
inversion H.
auto. apply IHtl. auto. inversion H.   auto.  Qed.


Lemma invfrlConc : forall nc (tl : list ppt) (tc : list ppt) ,
    (Fresh nc (tl ++ tc))
     -> ((Fresh nc tl)
    /\ (Fresh nc tc)).
Proof.
intros. induction tl. apply conj.  apply frnilVar. simpl in H. auto.
apply FreshIsNonce in H. auto.   simpl in H. auto.
apply conj. apply frConc.
rewrite <- app_comm_cons in H. inversion H.
auto. inversion H.
apply IHtl in H4.  destruct H4. auto.
rewrite <- app_comm_cons in H. inversion H.
apply IHtl in H4.  destruct H4. auto.
 Qed.








Ltac ProveFresh :=
  repeat ( intros; match goal with
      |    |- ?c1 <<< ?c2  => ProveHag ;auto
      |    |- PPT ?hag ?f  => ProvePPT ;auto
      |    |- Context ?hag ?tol ?f  => ProveContext ;auto
       |    |- ContextTerm ?hag ?tol ?f  => ProveContext ;auto
           |[ |- FreshTerm (nonce _) (nonce _)] => constructor; auto
           |[ |- Fresh (nonce ?n) []] => apply frnil; auto
           |H : Fresh ?nc ?tl |- Fresh ?nc [] => assert (temp :=  H) ; apply FreshIsNonce in temp;  apply frnilVar; auto
           |H : FreshTerm ?nc ?t |- Fresh ?nc [] =>  assert (temp :=  H) ; apply FreshTermIsNonce in temp;  apply frnilVar ; auto
           |  |- Fresh ?nc [] =>   apply frnilVar ; auto
           |[ |- Fresh _ (?h :: ?l) ] => apply frConc; auto
           |[ |- Fresh _ (?h ++ ?l) ] => apply frlConc; auto
           |[ |- Fresh _ (?c _) ] => apply frFAdv; auto
           |[ |- FreshTerm _ (?c _ ) ]=> apply frtFAdv; auto
           |[ |- FreshTerm (nonce ?n) ?t] => apply frtCAdv ; auto
           |H : Fresh ?nc ?tl |- FreshTerm ?nc ?t  => assert (temp :=  H) ; apply FreshIsNonce in temp; apply frtCAdvVar; auto
           |H : FreshTerm ?nc ?t' |- FreshTerm ?nc ?t  => assert (temp :=  H) ;  apply FreshTermIsNonce in temp; apply frtCAdvVar; auto
           |[ |- FreshTerm ?nc ?t] => apply frtCAdvVar; auto
                   end).




Proposition frtcAdv : forall (n : nat) (c : Symbols Adversarial (narg 0)) ,  FreshTerm (nonce n) (ConstInt Adversarial c).
   ProveFresh.
Defined.

Proposition frtTRue : forall (n : nat) ,  FreshTerm (nonce n) TRue.
   ProveFresh.
Defined.

Proposition frtTRueVar : forall nc , Nonce nc ->  FreshTerm nc TRue.
   ProveFresh.
Defined.


Proposition frTtoL : forall nc tc,
    FreshTerm nc tc -> Fresh nc [tc].
   ProveFresh.  Defined.

Proposition frConst : forall n (t : ppt) , PPT Adversarial (fun x => t) -> FreshTerm (nonce n) t.
   ProveFresh. Defined.

Proposition frConstVar : forall nc (t : ppt) , PPT Adversarial (fun x => t) -> Nonce nc -> FreshTerm nc t.
   ProveFresh. Defined.

Goal forall n, PPT Adversarial (fun x => nonce n) -> FreshTerm (nonce n) (nonce n).
  intros.
  pose (frConst n (nonce n)).
  apply f.
  auto.
Defined.



Proposition frTRue : forall (n : nat) ,  Fresh (nonce n) [TRue].
  ProveFresh.
Defined.



Proposition frTRueVar : forall nc , Nonce nc ->  Fresh nc [TRue].
  ProveFresh.
Defined.

Proposition frtFAlse : forall (n : nat) ,  FreshTerm (nonce n) FAlse.
ProveFresh.
Defined.

Proposition frFAlse : forall (n : nat) ,  Fresh (nonce n) [FAlse].
ProveFresh.
Defined.

Proposition frtEQ :  forall nc (t1 t2 : ppt) ,
    (FreshTerm nc t1)
    -> (FreshTerm nc t2)
    -> (FreshTerm nc (EQ [t1;t2])).
ProveFresh.
 Defined.

Proposition frEQ :  forall nc (t1 t2 : ppt) ,
    (FreshTerm nc t1)
    -> (FreshTerm nc t2)
    -> (Fresh nc [(EQ [t1;t2])]).
 ProveFresh. Defined.

Proposition frtITE : forall nc (t1 t2 t3: ppt) ,
    (FreshTerm nc t1)
    -> (FreshTerm nc t2)
    -> (FreshTerm nc t3)
    -> (FreshTerm nc (If_Then_Else_ [t1; t2; t3])).
 ProveFresh. Defined.

Proposition frITE : forall nc (t1 t2 t3: ppt) ,
    (FreshTerm nc t1)
    -> (FreshTerm nc t2)
    -> (FreshTerm nc t3)
    -> (Fresh nc [If_Then_Else_ [t1; t2; t3]]).
ProveFresh. Defined.




Goal forall (n : nat) (t : ppt) , PPT Adversarial (fun x => t) -> FreshTerm (nonce n) t.
  ProveFresh.
Defined.

Goal forall n m, n <> m -> FreshTerm (nonce n) (nonce m).
  ProveFresh. Defined.

Goal FreshTerm (nonce 3) (nonce 7).
  ProveFresh. Defined.

Goal Fresh (nonce 3) [(nonce 1); (nonce 4)].
  ProveFresh. Defined.

Goal forall (n : nat) ,  Fresh (nonce n) [TRue].
  ProveFresh. Defined.

Goal forall (n : nat) ,  Fresh (nonce n) [FAlse].
  ProveFresh. Defined.

Goal forall (n : nat) (t1 t2 : ppt) ,
    (FreshTerm (nonce n) t1)
    -> (FreshTerm (nonce n) t2)
    -> (Fresh (nonce n) [(EQ [t1;t2])]).
   ProveFresh. Defined.

Goal forall (n : nat) (t1 t2 t3: ppt) ,
    (FreshTerm (nonce n) t1)
    -> (FreshTerm (nonce n) t2)
    -> (FreshTerm (nonce n) t3)
    -> (Fresh (nonce n) [If_Then_Else_ [t1; t2; t3]]).
  ProveFresh. Defined.

Goal forall (n n' n'': nat) , n<> n' -> n<> n''
    -> (Fresh (nonce n) [(EQ [ EQ [nonce n' ; nonce n'']; If_Then_Else_ [TRue; nonce n' ;nonce n']])]).
   ProveFresh. Defined.






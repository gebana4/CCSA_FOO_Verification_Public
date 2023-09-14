
(************************************************************************)
(* Copyright (c) 2020, Gergei Bana, Qianli Zhang                        *)
(*                                                                      *)
(* This work is licensed under the MIT license. The license is          *)
(* described in the file "LICENSE" available at the root of the source  *)
(* or at https://opensource.org/licenses/MIT                            *)
(************************************************************************)


Require Export G_AxiomImplications.




(**************************************************************************************)
(******************************** Nonce Lists *****************************)
(**************************************************************************************)


Lemma NonceNonce : forall n , Nonce (nonce n).
Proof.
  intros. unfold Nonce. exists n. auto. Qed.


Inductive NonceList : list ppt ->  Prop :=
 |nlnil : NonceList []
 |nlN : forall nc lx, Nonce nc -> NonceList lx -> NonceList (nc :: lx).

Lemma nonce_inj :
  forall n m, nonce n = nonce m -> n = m.
Proof.
  intros.
  apply PBC.
  intros.
  apply frtNN in H0.
  apply FreshNEq in H0.
  apply ceq in H.
  rewrite H in H0.
  apply FTDist.
  assumption.
Qed.



Lemma NonceListNonce :
  forall n , NonceList [nonce n].
Proof.
  intros. constructor. apply NonceNonce. constructor. Qed.

Proposition nlComp :
  forall x y, NonceList x -> NonceList y -> NonceList (x++y).
Proof.
  intros. induction H. auto. simpl. constructor; auto. Qed.


Ltac ProveNonceList:=
  repeat (intros ;  match goal with
      |   |- Nonce (nonce ?n)  => apply NonceNonce ; auto
      |   |- NonceList [ ]  => constructor ; auto
      |   |- NonceList [nonce ?n] => apply NonceListNonce; auto
      |   |- NonceList [?x]  => apply nlN ; auto
      |   |- NonceList (?a :: ?m)  => apply nlN ; auto
      |   |- NonceList (?x ++ ?y)  => apply nlComp ; auto
          end).

Goal forall n m, NonceList ((nonce n) :: [nonce m]).
  ProveNonceList. Qed.




Inductive Bigger : nat -> list ppt -> Prop :=
| bgnil : forall n , Bigger n []
| bgN : forall n m l, m < n -> Bigger n l -> Bigger n ((nonce m) :: l).


Proposition Biggerthan :
  forall m n lx ,  Bigger m lx -> m < n -> Bigger n lx.
Proof.
  intros m n lx H. induction H.
  - constructor.
  - intros. constructor.
    + lia.
    + apply IHBigger. auto. Qed.


Proposition BiggerExists :
  forall lx , NonceList lx -> exists n, Bigger n lx.
Proof.
  intros. induction H.
  - exists 0. constructor.
  - inversion_clear H; rewrite <- H1; clear H1.
    inversion_clear IHNonceList.
    exists (1 + Nat.max x x0).
    constructor.
    + lia.
    + apply (Biggerthan x0).
      * auto.
      * lia. Qed.




(**************************************************************************************)
(******************************** Properties of Fresh *********************************)
(**************************************************************************************)

Scheme Fresh_mut' := Induction for Fresh Sort Prop
  with FreshTerm_mut' := Induction for FreshTerm Sort Prop.

Goal forall t lx, Fresh t lx -> Nonce t.
  apply (Fresh_mut' (fun p l => fun f4: (Fresh p l) => Nonce p)
                    (fun p l => fun f5: (FreshTerm p l) => Nonce p));
    intros; try (apply NonceNonce); auto. Defined.


Lemma FreshNonce: forall t lx, Fresh t lx -> Nonce t.
  intros p l.
  apply (Fresh_mut (fun p l => Nonce p)
                   (fun p l => Nonce p));
    intros; try (apply NonceNonce); auto. Defined.



Proposition NonceVsNonceList :  forall nc nl, Nonce nc -> NonceList nl ->
(forall n, not( Nth n nl = nc)) -> Fresh nc nl.
Proof. intros nc nl N NL FA. induction nl. inversion N.   rewrite <- H.  apply frnil.
inversion NL. apply frConc.
assert (a <> nc).
assert (B := (FA 0)). unfold Nth in B. simpl in B. auto. inversion N.
rewrite <- H4 in *. inversion H1. rewrite <- H5 in *.
unfold not in H3. apply frtNN. unfold not. intros.
assert (nonce x0 = nonce x). rewrite H6. auto. apply H3 in H7. auto.
apply IHnl. auto. intros.
assert (Nth (S n) (a :: nl) <> nc). apply FA.
unfold Nth in H3. simpl in H3. unfold Nth. auto.
Qed.


Proposition NonceVsNonceList' :  forall nc nl , Nonce nc -> NonceList nl ->
((exists n, Nth n nl = nc) \/ Fresh nc nl).
Proof. intros.
assert ((exists n, Nth n nl = nc) \/ not (exists n, Nth n nl = nc)).
apply LEM. destruct H1. auto.
assert (forall n, not( Nth n nl = nc)). intros. unfold not.
intros. assert (exists n : nat, Nth n nl = nc). exists n. auto. contradiction.
apply NonceVsNonceList in H2. auto. auto. auto.
Qed.


Proposition NonceInNonceList :
  forall {nc nl}, Nonce nc -> NonceList nl (*-> nl <> [] *) -> not (Fresh nc nl) -> exists n , Nth n nl = nc.
Proof.
  intros. apply (NonceVsNonceList' nc nl H) in H0.
  destruct H0.
  - auto.
  - apply H1 in H0. inversion H0.  Qed.
(* LEM in AxiomImplicationShallow should be used I think. I agree*)

(**************************************************************************************)
(******************************** Propositions for Fresh ******************************)
(**************************************************************************************)


Proposition BiggerFresh :
  forall n lx, Bigger n lx -> Fresh (nonce n) lx.
Proof.
  intros.
  induction H; ProveFresh.  lia. Qed.


Proposition FreshExists :
  forall lx, NonceList lx -> exists n,  Fresh (nonce n) lx.
Proof.
  intros. apply BiggerExists in H. inversion H.
apply BiggerFresh in H0. exists x. auto.
Qed.



Lemma fstn:  forall (x1 x2: list ppt), (firstn (length x1) (x1 ++ x2)) = x1.
  intros.
  induction x1.
  - auto.
  - simpl. rewrite IHx1. auto. Qed.

Lemma skpn: forall (x1 x2: list ppt), skipn (length x1) (x1 ++ x2) = x2.
  intros. induction x1; auto. Qed.




Proposition FreshfromNonceList : forall nc tl, Fresh nc tl <->
  exists f lx , Context Adversarial List f /\ NonceList lx /\ Fresh nc lx /\ tl = f lx.
Proof.
  split; intros.

  - apply  (Fresh_mut (fun nc tl => exists (f : ToL List -> list ppt) (lx : list ppt),
             Context Adversarial List f /\ NonceList lx /\ Fresh nc lx /\ tl = f lx)
                    (fun x t => exists (f : ToL List ->  ppt) (lx : list ppt),
             ContextTerm Adversarial List f /\ NonceList lx /\ Fresh x lx /\ t = f lx)); intros.
    + exists (fun _ => []).
      exists [].
    repeat split. ProveContext. ProveNonceList. ProveFresh.
    +
      inversion_clear H1 as [f  [lx0 [H6 [H7  [H8  H4]]]]].
      inversion_clear H3 as [fc [lx1 [H9 [H10 [H11 H5]]]]].
      rewrite H4. rewrite H5.
      exists (fun lx => (f (firstn (length lx0) lx)) :: fc (skipn (length lx0) lx)).
      exists (lx0++lx1).
      repeat split. ProveContext. ProveNonceList. ProveFresh.
      rewrite fstn. rewrite skpn. auto.
    +
      exists (fun x => HD x).
      exists ([nonce m]).
      repeat split. ProveContext. ProveNonceList. ProveFresh.
    +
      inversion_clear H2. inversion_clear H3.
      destruct H2. destruct H3. destruct H4.
      exists (fun lx => t (x lx)).
      exists x0.
      repeat split. ProveContext.  auto. auto. rewrite H5. auto.
    +
      exists (fun _ : ToL List => t). exists [].
      repeat split. ProveContext. ProveNonceList. ProveFresh.
    + auto.
  - inversion_clear H as [f [lx [H1 [H2 [H3 H4]]]]].
    rewrite H4.
    ProveFresh. Qed.



Proposition FreshTermfromNonceList : forall nc tl, FreshTerm nc tl <->
  exists f lx, ContextTerm Adversarial List f /\ NonceList lx /\ Fresh nc lx /\ tl = f lx.
Proof.
  split; intros.
  - assert (Fresh nc [tl]). ProveFresh.
    apply FreshfromNonceList in H0.
    inversion_clear H0 as [f [lx [H1 [H2 [H3 H4]]]]].
    exists (fun l => HD (f l)).
    exists lx.
    repeat split.
    + ProveContext.
    + auto.
    + auto.
    + rewrite <- H4. auto.
  - inversion_clear H as [f [lx [H1 [H2 [H3 H4]]]]].
    rewrite H4. ProveFresh. Qed.




(**************************************************************************************)
(******************************** List Freshness *****************************)
(**************************************************************************************)


Inductive ListFresh : list ppt -> list ppt -> Prop := (* metapredicate *)
| lfrnil :  forall lx, ListFresh [] lx
| lfrConc : forall nc nl lx, Fresh nc lx -> ListFresh nl lx -> ListFresh (nc::nl) lx.

Inductive ListFreshTerm : list ppt ->  ppt -> Prop := (* metapredicate *)
| lfrtnil :  forall lx, ListFreshTerm [] lx
| lfrtConc : forall nc nl lx, FreshTerm nc lx -> ListFreshTerm nl lx -> ListFreshTerm (nc::nl) lx.

Lemma FreshTermList: forall nc lx, ListFreshTerm nc lx -> ListFresh nc [lx].
  intros.
  induction H.
  - constructor.
  - constructor. ProveFresh.
    auto. Qed.

Lemma FreshList2Nonce : forall nl lx, ListFresh nl lx -> NonceList nl.
  intros.
  induction H.
  - constructor.
  - constructor. apply FreshNonce in H; auto. auto.
Qed.


Corollary NonceNeqDefault: forall a, Nonce a -> default <> a.
  unfold not; intros.
  assert (FreshTerm a default); ProveFresh.
  apply FreshNEq in H1; rewrite H0 in H1.
  assert (a = a). reflexivity. apply ceq in H2.
  rewrite H2 in H1; apply FTDist; auto. Qed.

Lemma NthApp:  forall {x nl a} tl, Nth x nl = a -> Nonce a -> Nth x nl = Nth x (nl ++ tl).
  induction x; unfold Nth in *; intros; simpl.
  - destruct nl; simpl.
    + simpl in H. apply NonceNeqDefault in H0. apply H0 in H. inversion H.
    + auto.
  - destruct nl; simpl.
    + simpl in H. apply NonceNeqDefault in H0. apply H0 in H. inversion H.
    + simpl in H. apply IHx with (tl := tl) in H. auto. auto. Qed.


Proposition ListFreshIndLeft :
      (*"<<<"*)  forall nl lx ly,  ListFresh nl lx  ->  ListFresh nl ly -> (*">>>"*)
               lx ~ ly -> (nl ++ lx) ~ (nl ++ ly).
Proof.
  intros nl lx ly LF1 LF2 lxy.
  induction nl. simpl. auto.
  pose (LEM (Fresh a nl)). destruct o.
  - inversion LF1. inversion LF2.         (* FreshInd *)
    assert (Fresh a (nl ++ lx)). apply frlConc; auto.
    assert (Fresh a (nl ++ ly)). apply frlConc; auto.
    simpl. apply FreshInd; auto.
  - assert (ListFresh (a :: nl) lx); auto. (* cind_funcapp *)
    apply FreshList2Nonce in H0. inversion H0.
    apply (NonceInNonceList H3 H4) in H. inversion H. (* NonceInNonceList should be used I think *)
    inversion LF1. inversion LF2. apply (IHnl H10) in H15.
    apply (@cind_funcapp (fun l => (Nth x l) :: l) (nl ++ lx) (nl ++ ly)) in H15; simpl in H15.
    assert (Nonce a); auto.
    apply (NthApp lx H5) in H3.
    apply (NthApp ly H5) in H16.
    rewrite <- H3 in H15. rewrite <- H16 in H15.
    rewrite H5 in H15. simpl. auto. ProveContext. Qed.


Proposition ListFreshIndRight :
      (*"<<<"*)  forall nl lx ly,  ListFresh nl lx  ->  ListFresh nl ly -> (*">>>"*)
               lx ~ ly -> (lx ++ nl) ~ (ly ++ nl).
Proof.
  intros nl lx ly LF1 LF2 lxy.
  assert (forall lz , lz ++ nl = (fun x =>  skipn (length nl) x  ++   firstn (length nl)  x) (nl ++ lz)   ).
  intros.   simpl. rewrite skipn_app. rewrite skipn_all.
  simpl. assert (length nl - length nl = 0). lia. rewrite H. rewrite skipn_O. rewrite firstn_app. rewrite firstn_all. rewrite H. rewrite firstn_O. rewrite app_nil_r.  auto.
 rewrite H. rewrite H. apply (@cind_funcapp (fun x =>  skipn (length nl) x  ++   firstn (length nl)  x) ). ProveContext. apply ListFreshIndLeft. auto. auto. auto. Qed.



Lemma ListFreshNonceList : forall nl xl, ListFresh nl xl -> NonceList nl.
Proof.
  intros. induction H. constructor. apply FreshIsNonce in H.
  apply nlN. auto. auto.
Qed.




Lemma ListFreshTermNonceList :
  forall nl xl, ListFreshTerm nl xl -> NonceList nl.
Proof.
  intros. induction H. constructor. apply nlN. auto. apply FreshTermIsNonce in H.
  auto. auto.
Qed.


Lemma lfrnilVar : forall nc,  NonceList nc -> ListFresh nc nil.
Proof. intros. induction H. constructor. apply lfrConc. ProveFresh. apply IHNonceList. Qed.

Lemma lfrlConc : forall nl (t : ppt) (tc : list ppt),
    NonceList nl
    -> (ListFreshTerm nl t)
    -> (ListFresh nl tc)
    -> (ListFresh nl (t :: tc)).
Proof.
  intros. induction nl. constructor. inversion H.
  apply lfrConc. apply frConc.
  rewrite <- H2 in *. inversion H0. auto.
  rewrite <- H2 in *. inversion H0. auto.
  inversion H1. auto.
  apply IHnl. auto. inversion H0. auto.
  inversion H1; auto. Qed.


Lemma lfrlnil : forall nl,
    NonceList nl -> ListFresh nl [].
Proof.
  intros. induction nl. constructor.
  inversion H. apply lfrConc. ProveFresh. apply IHnl. auto.
Qed.




Lemma lfrlllConc : forall nl1 nl2 (tc : list ppt),
    (ListFresh nl1 tc)
    -> (ListFresh nl2 tc)
    -> (ListFresh (nl1 ++ nl2) tc).
Proof.
  intros. induction H. simpl. auto.
rewrite <- app_comm_cons. apply lfrConc. auto. apply IHListFresh. auto.
 Qed.


Proposition invfrtNN: forall m n,
    FreshTerm (nonce m) (nonce n) -> m <> n.
Proof.
  intros.
  apply FreshNEq in H. unfold not. intros.
  assert (nonce m = nonce n). apply  ceq. rewrite H0. apply ceq. reflexivity.
  apply ceq in H1. rewrite H in H1. symmetry in H1. apply FTDist in H1.
  contradiction. Qed.


Proposition frttsymm : forall m n,
    FreshTerm (nonce m) (nonce n) -> FreshTerm (nonce n) (nonce m).
Proof.
  intros. apply invfrtNN in H. constructor. auto.
Qed.


Proposition frtlsymm : forall n nl,
    NonceList nl -> (Fresh (nonce n) nl) -> ListFreshTerm nl (nonce n).
Proof.
  intros.
  induction nl. constructor.
  inversion H. apply lfrtConc. inversion H0. unfold Nonce in H3.
  inversion H3.  rewrite <- H10 in *.
  apply frttsymm. auto. apply IHnl. inversion H. auto.
  inversion H0. auto. Qed.

Proposition invfrtlsymm : forall n nl,
    ListFreshTerm nl (nonce n) -> (Fresh (nonce n) nl).
Proof.
  intros.
  induction nl. constructor.
  assert (ListFreshTerm (a :: nl) (nonce n)). auto.
  apply ListFreshTermNonceList in H.
  inversion H. apply frConc. inversion H0. unfold Nonce in H3. inversion H3.
  rewrite <- H10 in *. apply frttsymm. auto.
  apply IHnl. inversion H0. auto. Qed.



Proposition frtllsymm : forall ml nl,
    NonceList nl -> ListFresh ml nl -> ListFresh nl ml.
Proof.
  intros.
  induction ml.
  apply lfrlnil. auto.
  inversion H0. apply lfrlConc. auto. apply FreshIsNonce in H3.
  unfold Nonce in H3. inversion H3. rewrite <- H6 in *. apply frtlsymm.
  auto. inversion H0. auto. apply IHml. auto. Qed.


Proposition invlfrlConc : forall nl t tc,
    ListFresh nl (t :: tc) -> (ListFreshTerm nl t /\ ListFresh nl tc).
Proof.
  intros.
  induction nl.
  apply conj. constructor. constructor.
  apply conj.
  assert (ListFresh (a :: nl) (t :: tc)); auto.
  apply ListFreshNonceList in H. inversion H.  apply lfrtConc.
  rewrite <- H1 in *. inversion H0. inversion H6.
  auto. inversion H0.  apply IHnl in H9.  destruct H9. auto.
  assert (ListFresh (a :: nl) (t :: tc)); auto.
  apply lfrConc. rewrite <- H1.  auto. apply IHnl in H15.  inversion H0.
  auto.
  inversion H13. auto. apply IHnl.
  inversion H0. auto. apply lfrConc. inversion H. inversion H2.
  auto. apply IHnl. inversion H. auto.
Qed.





Lemma lfrllConc : forall nl (tc1 : list ppt) (tc2 : list ppt),
    NonceList nl
    -> (ListFresh nl tc1)
    -> (ListFresh nl tc2)
    -> (ListFresh nl (tc1 ++ tc2)).
Proof.
  intros.
  induction tc1. simpl. auto.
  rewrite <- app_comm_cons. apply lfrlConc.
  auto. apply invlfrlConc in H0. destruct H0.
  auto. apply IHtc1.  apply invlfrlConc in H0. destruct H0.
  auto. Qed.


Lemma invlfrllConc :forall nl (tc1 : list ppt) (tc2 : list ppt),
    ListFresh nl (tc1 ++ tc2)
    -> (ListFresh nl tc1)
    -> (ListFresh nl tc2).
Proof.
  intros.
  induction nl. constructor.
  assert(ListFresh (a :: nl) (tc1 ++ tc2)); auto.
  inversion H. apply IHnl in H6. apply lfrConc. apply invfrlConc in H4.
  destruct H4. assumption. auto. inversion H0. auto.
Qed.





Lemma lfrtFAdv: forall nl (t: list ppt -> ppt) (tc : list ppt),
    NonceList nl ->
    (ContextTerm Adversarial List t)
    -> ListFresh nl tc
    -> ListFreshTerm nl (t tc).
Proof.
  intros.
  induction nl. constructor.
  inversion H. apply lfrtConc. ProveFresh. rewrite <- H2 in *.
  inversion H1. auto. apply IHnl. auto. inversion H1. auto.
Qed.

Lemma lfrFAdv: forall nl (tl: list ppt -> list ppt) (tc : list ppt),
    NonceList nl ->
    (Context Adversarial List tl)
    -> ListFresh nl tc
    -> ListFresh nl (tl tc).
Proof.  intros.
 induction nl. constructor.
inversion H. apply lfrConc. ProveFresh. rewrite <- H2 in *.
inversion H1. auto.  apply IHnl.  auto. inversion H1. auto.
 Qed.

Lemma lfrtCAdv: forall nl (t: ppt) ,
NonceList nl ->
    (ContextTerm Adversarial List (fun x => t))
    -> ListFreshTerm nl t.
Proof. intros.  induction H. constructor.
apply lfrtConc.  ProveFresh.  auto. Qed.





Ltac ProveListFresh :=
  repeat ( intros; match goal with
           |[ |- FreshTerm _ _ ] => ProveFresh; auto
           |[ |- Fresh _ _ ] => ProveFresh; auto
           |[ |- ListFreshTerm  ?nl (nonce ?n)] => apply frtlsymm; auto
           |[ |- ListFresh (?nc :: ?nl) ?t] => apply lfrConc; auto
           |[ |- ListFresh (?nc ++ ?nl) ?t] => apply lfrlllConc; auto
           |H : ListFresh ?nc ?tl |- ListFresh ?nc [] => assert (temp :=  H) ; apply ListFreshNonceList in temp;  apply lfrnilVar; auto
           |H : ListFreshTerm ?nc ?t |- ListFresh ?nc [] =>  assert (temp :=  H) ; apply ListFreshTermNonceList in temp;  apply lfrnilVar ; auto
           |  |- ListFresh ?nc [] =>   apply lfrnilVar ; auto
           |[ |- ListFresh _ (?h :: ?l) ] => apply lfrlConc; auto
           |[ |- ListFresh _ (?h ++ ?l) ] => apply lfrllConc; auto
           |[ |- ListFresh _ (?c _) ] => apply lfrFAdv; auto
           |[ |- ListFreshTerm _ (?c _ ) ]=> apply lfrtFAdv; ProveContext; auto
           |H : ListFresh ?nc ?tl |- ListFreshTerm ?nc ?t  => assert (temp :=  H); apply ListFreshNonceList in temp; apply lfrtCAdv; ProveContext; auto
        |H : ListFreshTerm ?nc ?t' |- ListFreshTerm ?nc ?t  => assert (temp :=  H) ;  apply ListFreshTermNonceList in temp; apply lfrtCAdv; ProveContext; auto
           |[ |- ListFreshTerm ?nc ?t] => apply lfrtCAdv; ProveContext; auto
                   end).



(**************************************************************************************)
(******************************** Context Freshness *****************************)
(**************************************************************************************)


Inductive FreshcTerm  : ppt -> (ppt -> list ppt) -> Prop := (* metapredicate *)
| frctnil : forall n,  FreshcTerm (nonce n) (fun x => nil)
| frctConc : forall nc (t :  ppt ->  ppt) (tc :  ppt ->  list ppt) ,
    (FreshTermcTerm nc t)
    -> (FreshcTerm nc tc)
    -> (FreshcTerm nc (fun x => ((t x):: (tc x))))
| frctApp : forall nc (tc1 tc2 :  ppt ->  list ppt) ,
    (FreshcTerm nc tc1)
    -> (FreshcTerm nc tc2)
    -> (FreshcTerm nc (fun x => ((tc1 x) ++ (tc2 x))))
| frctFAdv :
forall nc (tl: list ppt -> list ppt) (tc : ppt -> list ppt) ,
    (Context Adversarial List tl)
    -> FreshcTerm nc tc
    -> FreshcTerm nc (fun y => tl (tc y))
with FreshTermcTerm : ppt -> ( ppt -> ppt) -> Prop :=
| frtctNN : forall (n m : nat) , n <> m
                        -> (FreshTermcTerm (nonce n) (fun x => (nonce m)))
| frtctFAdv: forall nc (t: list ppt -> ppt) (tc :  ppt ->  list ppt) ,
    (ContextTerm Adversarial List t)
    -> FreshcTerm nc tc
    -> FreshTermcTerm nc (fun x =>  (t (tc x)))
| frtctCAdv: forall n (t:  ppt -> ppt) ,
    (ContextTerm Adversarial Term t)
    -> FreshTermcTerm (nonce n) t.





Proposition frtcCFresh : forall nc tl , Fresh nc tl -> FreshcTerm nc (fun x => tl).
Proof. intros. assert (Fresh nc tl); auto. apply FreshIsNonce in H0.
apply (Fresh_mut (fun nc tl => FreshcTerm nc (fun _ : ppt => tl) ) (fun nc t => FreshTermcTerm nc (fun _ : ppt => t) ) ) in H.
auto.  constructor.  intros. apply frctConc. auto. auto. intros. constructor. auto.
intros. constructor. auto. auto. intros. constructor.  assert (ppt = ToL Term). constructor.
assert ((fun _ : ppt => t) = (fun _ : ToL Term => t)). unfold ToL. auto.
auto. rewrite H3.  assert (Context Adversarial Term (fun x => [x])).
ProveContext. apply (cltCont H1 H4) . Qed.



Inductive ListMapList : (list ppt -> list ppt) -> Prop :=
| lmlnil : ListMapList (fun lx => [])
| lmlConc : forall (t : list ppt -> ppt) (lt : list ppt -> list ppt), ListMapList (fun lx => (t lx) :: (lt lx)).







Scheme FreshcTerm_mut := Minimality for FreshcTerm Sort Prop
  with FreshTermcTerm_mut := Minimality for FreshTermcTerm Sort Prop.






Inductive Freshc : ppt -> (list ppt -> list ppt) -> Prop := (* metapredicate *)
| frcnil : forall n, Freshc (nonce n) (fun lx => nil)
| frcConc : forall (n : nat) (t : list ppt ->  ppt) (tc : list ppt ->  list ppt) ,
    (FreshTermc (nonce n) t)
    -> (Freshc (nonce n) tc)
    -> (Freshc (nonce n) (fun lx => ((t lx):: (tc lx))))
| frcApp : forall (n : nat) (tc1 tc2 : list ppt ->  list ppt) ,
    (Freshc (nonce n) tc1)
    -> (Freshc (nonce n) tc2)
    -> (Freshc (nonce n) (fun lx => ((tc1 lx) ++ (tc2 lx))))
| frcFAdv :
forall n (tl: list ppt -> list ppt) (tc : list ppt -> list ppt) ,
    (Context Adversarial List tl)
    -> Freshc (nonce n) tc
    -> Freshc (nonce n) (fun lx =>  (tl (tc lx)))
| frcCAdv: forall n (t: list ppt -> list ppt) ,
    (Context Adversarial List t)
    -> Freshc (nonce n) t
with FreshTermc : ppt -> (list ppt -> ppt) -> Prop :=
| frtcNN : forall (n m : nat) , n <> m
                        -> (FreshTermc (nonce n) (fun lx => (nonce m)))
| frtcFAdv: forall n (t: list ppt -> ppt) (tc : list ppt ->  list ppt) ,
    (ContextTerm Adversarial List t)
    -> Freshc (nonce n) tc
    -> FreshTermc (nonce n) (fun lx =>  (t (tc lx)))
| frtcCAdv: forall n (t: list ppt -> ppt) ,
    (ContextTerm Adversarial List t)
    -> FreshTermc (nonce n) t.


Proposition frcapp: forall n lx ,
    NonceList lx -> Fresh (nonce n) lx ->
    Freshc (nonce n) (app lx).
Proof.
  intros.
  induction H.
  - apply frcCAdv.
    assert ((app [] ) = (fun x : list ppt  => x)).
    { auto. }
    rewrite H.
    ProveContext.
  - assert ((app (nc :: lx) = (fun x => nc :: (app lx x)))).
    { auto. }
    rewrite H2.
    apply  frcConc.
    + unfold Nonce in H.
      destruct H.
      rewrite <- H.
      apply frtcNN.
      inversion H0.
      rewrite <- H in H6.
      unfold not.
      intros.
      apply FreshNEq in H6.
      assert (nonce n = nonce x).
      { rewrite H8.
        reflexivity. }
      apply ceq in H9.
      rewrite H9 in H6.
      apply FTDist.
      assumption.
    + apply IHNonceList.
      inversion H0.
      assumption.
Qed.



Scheme Freshc_mut := Minimality for Freshc Sort Prop
  with FreshTermc_mut := Minimality for FreshTermc Sort Prop.





Inductive ListFreshcTerm : list  ppt -> (ppt -> list ppt) -> Prop := (* metapredicate *)
| lfrctnil :  forall lx, ListFreshcTerm [ ] lx
| lfrctConc : forall nc nl lx,
FreshcTerm nc lx ->
ListFreshcTerm nl lx ->
ListFreshcTerm (nc::nl) lx.





Inductive ListFreshTermcTerm : list  ppt ->  (ppt -> ppt) -> Prop := (* metapredicate *)
| lfrtctnil :  forall lx, ListFreshTermcTerm [ ] lx
| lfrtctConc : forall nc nl lx, FreshTermcTerm nc lx
                           -> ListFreshTermcTerm nl lx
                           -> ListFreshTermcTerm (nc::nl) lx.







Lemma lfrctlConc : forall (nl : list ppt) (t : ppt ->  ppt) (tc :  ppt ->  list ppt) ,
    NonceList nl ->
    (ListFreshTermcTerm nl t)
    -> (ListFreshcTerm nl tc)
    -> (ListFreshcTerm nl (fun lx => ((t lx):: (tc lx)))).
Proof.
  intros. induction nl. constructor. inversion H.
  apply lfrctConc. apply frctConc.
  rewrite <- H2 in *. inversion H0. auto.
  rewrite <- H2 in *. inversion H0. auto.
  inversion H1. auto.
  apply IHnl. auto. inversion H0. auto.
  inversion H1; auto. Qed.


Lemma lfrctlnil : forall nl,
    NonceList nl -> ListFreshcTerm nl (fun _ : ppt => []).
Proof.
  intros. induction nl. constructor.
  inversion H. apply lfrctConc.
  unfold Nonce in H2. inversion H2. rewrite <- H4 in *. apply frctnil.
  apply IHnl. auto.
Qed.



(**************************************************************************************)
(******************************* Freshness and Nonce Lists ****************************)
(**************************************************************************************)





(* This axiom says that if (fun x -> c (x :: nl1))  is fresh wrt nl, that is, it equals a function withut the
 nonces in nl, then nl1 can be changed to another list that does not contain nonces from nl.
This is computationally sound, and it can probably be derived with mutual induction on Context,
but it is tedious.
Soundness follows from that in nl1, one can replace the nonces that are also in nl with
any other, fresh nonces without affecting the value of c (x :: nl1).
 *)

Axiom FreshcTermRem :
  (*"<<<"*)  forall  nl c nl1,
              Context Adversarial List c -> NonceList nl1 ->
                 ListFreshcTerm nl (fun x => c (x :: nl1)) ->
exists nl2,( ListFresh nl nl2 /\  NonceList nl2 /\ (fun x => c (x :: nl1)) = (fun x => c (x :: nl2))). (*">>>"*)




Proposition FreshcTermFromFresh :
  forall nc tl, Fresh nc tl -> FreshcTerm nc (fun _ :  ppt => tl).
Proof.
  intros.
  apply (Fresh_mut
           (fun nc tl => FreshcTerm nc (fun _ : ppt => tl))
           (fun nc t => FreshTermcTerm nc (fun _ : ppt => t))).
  intros; constructor.
  intros.
  constructor.
  assumption.
  assumption.
  intros.
  constructor.
  assumption.
  intros.
  constructor.
  assumption.
  assumption.
  intros.
  constructor.
  apply (@cltCont  Adversarial Term (fun xl : list ppt => t) (fun x : ppt => [x])).
  assumption.
  ProveContext.
  assumption.
Qed.


  
Proposition ListFreshcTermFromListFresh :
  forall nl tl, ListFresh nl tl -> ListFreshcTerm nl (fun _ :  ppt => tl).
Proof.
  intros.
  induction nl.
  constructor.
  constructor.
  inversion H.
  apply FreshcTermFromFresh.
  assumption.
  apply IHnl.
  inversion H.
  assumption. 
Qed.
  








Proposition FreshRem :
  (*"<<<"*)  forall  nl c nl1,
              Context Adversarial List c -> NonceList nl1 ->
                 ListFresh nl (c nl1) -> exists nl2,( ListFresh nl nl2 /\  NonceList nl2 /\ c nl1 = c nl2). (*">>>"*)


Proof.
  intros.
  pose (FreshcTermRem nl (fun x => c (TL x)) nl1).
  simpl in e.
  assert (Context Adversarial List (fun x : list ppt => c (TL x))).
  ProveContext.
  apply e in H2.
  inversion H2.
  inversion H3.
  inversion H5.
  exists x.
  apply conj.
  assumption.
  apply conj.
  assumption.
  apply (equal_f H7 default).
  assumption.
  apply ListFreshcTermFromListFresh.
  assumption.
Qed.  



  
Proposition FreshTermRem :
  (*"<<<"*)  forall  nl c nl1,
              ContextTerm Adversarial List c -> NonceList nl1 ->
                 ListFreshTerm nl (c nl1) -> exists nl2,( ListFresh nl nl2 /\  NonceList nl2 /\ c nl1 = c nl2). (*">>>"*)
Proof.
  intros.
  pose (FreshRem nl (fun x => [c x]) nl1).
  assert (Context Adversarial List (fun x : ToL List => [c x])).
  ProveContext.
  apply e in H2.
  inversion H2.
  inversion H3.
  inversion H5.
  exists x.
  repeat split.
  assumption.
  assumption.
  assert (HD [c nl1] = HD  [c x]).
  rewrite H7.
  reflexivity.
  simpl in H8.
  assumption.
  assumption.
  pose H1.
  apply ListFreshTermNonceList in l.
  apply lfrlConc.
  assumption.
  assumption.
  apply lfrlnil.
  assumption.
Qed.









Proposition ListFreshfromNonceList : forall nl tl , nl <> [] -> (ListFresh nl tl <->
  exists f lx , Context Adversarial List f /\ NonceList lx /\ ListFresh nl lx /\ tl = f lx).
Proof.
  split; intros.
  induction H0.
  - contradiction.
  - induction nl.
    + apply (FreshfromNonceList nc lx) in H0.
      inversion H0. inversion H2.
      exists x. exists x0.
      destruct H3. destruct H4. destruct H5.
      apply conj; auto.  apply conj; auto. apply conj. apply lfrConc.
      auto. constructor. auto.
    + assert (a :: nl <> []).
      unfold not; intros. destruct nl; inversion H2.
      apply IHListFresh in H2. inversion H2. inversion H3.
      destruct H4. destruct H5. destruct H6.
      apply (lfrConc  nc (a :: nl) lx H0) in H1.
      rewrite H7 in H1.
      assert (ListFresh (nc :: a :: nl) (x x0)); auto.
      apply (FreshRem (nc :: a :: nl) x x0 H4 H5) in H1.
      inversion H1. destruct H9.
      exists x. exists x1.
      destruct H10. rewrite H11 in H7. auto.
  - intros. inversion H0. inversion H1. destruct H2. destruct H3.
    destruct H4.  rewrite H5. assert (tl = x x0). auto.
    apply lfrFAdv. assert (ListFresh nl x0); auto.
    apply ListFreshNonceList in H4.
    auto. auto.
  auto. Qed.



Proposition ListFreshTermfromNonceList: forall nl t, nl <> [] -> (ListFreshTerm nl t <->
   exists f lx , ContextTerm Adversarial List f /\ NonceList lx /\ ListFresh nl lx /\ t = f lx).
Proof.
  split; intros.
  - assert (ListFresh nl [t]).
    apply FreshTermList. auto.
    apply ListFreshfromNonceList in H1.
    inversion_clear H1 as [f [lx [H2 [H3 [H4 H5]]]]].
    exists (fun x => HD (f x)).
    exists lx.
    repeat split. ProveContext. auto. auto. rewrite <- H5. simpl. auto. auto.
  - inversion_clear H0 as [f [lx [H1 [H2 [H3 H4]]]]].
    rewrite H4. apply lfrtFAdv; auto.
    apply FreshList2Nonce in H3. auto.
Qed.


Proposition ListFreshTermfromNonceList' : forall nl t , nl <> [] -> (ListFreshTerm nl t
  <-> exists f lx , ContextTerm Adversarial List f /\ NonceList lx /\ ListFresh nl lx /\ t = f lx).
Proof.
  intros. split.
  - intros.
    induction H0.
    + contradiction.
    + induction nl.
      * apply (FreshTermfromNonceList nc lx) in H0. inversion H0. inversion H2.
        exists x. exists x0. destruct H3. destruct H4. destruct H5.
        apply conj; auto.  apply conj; auto. apply conj. apply lfrConc.
        auto. constructor. auto.
      * assert (a :: nl <> []).  unfold not.
        intros. inversion H2. apply IHListFreshTerm in H2. inversion H2.
        inversion H3. destruct H4. destruct H5. destruct H6.
        apply (lfrtConc  nc (a :: nl) lx H0) in H1. rewrite H7 in H1.
        assert (ListFreshTerm (nc :: a :: nl) (x x0)); auto.
        apply (FreshTermRem (nc :: a :: nl) x x0 H4 H5) in H1.
        inversion H1. destruct H9. exists x. exists x1.
        destruct H10. rewrite H11 in H7. auto.
  - intros. inversion H0. inversion H1. destruct H2. destruct H3.
    destruct H4.  rewrite H5.  assert (t = x x0). auto.
    apply lfrtFAdv. assert (ListFresh nl x0); auto.
    apply ListFreshNonceList in H4. auto. auto. auto. Qed.


Proposition ListFreshFunfromNonceList :  forall nl tl nl1,
    Nonce nl1 -> nl <> [] -> ListFresh nl (tl nl1)
    -> exists f nl2 , Context Adversarial List f /\ NonceList nl2 /\ ListFresh nl nl2 /\ tl nl1 = f (nl1 :: nl2).
Proof.
  intros nl tl nl1 N. intros H. intros LF.
assert ( forall lx,  ListFresh nl lx -> lx = (tl nl1) ->
exists
  (f : ToL List -> list ppt)
(nl2 : list ppt),
  Context Adversarial List f /\
  NonceList nl2 /\
  ListFresh nl nl2 /\
  lx = f (nl1 :: nl2)).
intros lx. intros H0.
 induction H0.
contradiction. induction nl. intros eq.  apply (FreshfromNonceList nc lx) in H0.
inversion H0. inversion H2.  exists (fun lx => x (TL lx))  . exists x0.
destruct H3. destruct H4. destruct H5.
apply conj; auto. ProveContext.  apply conj; auto. apply conj. apply lfrConc.
auto.  constructor. unfold TL.  simpl. auto.
intros eq.  assert (a :: nl <> []). unfold not.  intros. inversion H2.
apply IHListFresh in H2. inversion H2.  inversion H3.
destruct H4. destruct H5. destruct H6. apply (lfrConc  nc (a :: nl) lx H0) in H1.
rewrite H7 in H1.
assert (ListFresh (nc :: a :: nl)
       (x (nl1 :: x0))); auto. assert (NonceList (nl1 :: x0)).
ProveNonceList.
 apply  (FreshRem (nc :: a :: nl) x (nl1 :: x0) H4 H9) in H1.
inversion H1. destruct H10. exists (fun lx => x (TL lx)). exists x1.
destruct H11. rewrite H12 in H7. apply conj. ProveContext.
unfold TL; simpl.   auto. rewrite eq in H1.  auto. auto. apply H0.
auto. auto. Qed.






Lemma FreshcTermNonce : forall nc tl, FreshcTerm nc tl  -> Nonce nc.
Proof. intros.  induction   H. apply NonceNonce. auto. auto. auto.   Qed.


Lemma FreshTermcTermNonce : forall nc t, FreshTermcTerm nc t  -> Nonce nc.
Proof. intros.  inversion H. all: ProveNonceList. apply FreshcTermNonce in H1. auto.   Qed.




Lemma ListFreshcTermNonceList :
forall nl xl, ListFreshcTerm nl xl -> NonceList nl.
Proof. intros. induction H. constructor. apply FreshcTermNonce in H.
apply nlN. auto. auto.
Qed.






Lemma ListFreshTermcTermNonceList :
forall nl xl, ListFreshTerm nl xl -> NonceList nl.
Proof. intros. induction H. constructor. apply nlN. auto. apply FreshTermIsNonce in H.
auto. auto.
Qed.



Lemma ListFreshTermcTermNonceList' :
forall nl xl, ListFreshTermcTerm nl xl -> NonceList nl.
Proof. intros. induction H. constructor. apply nlN. auto. apply FreshTermcTermNonce in H.
auto. auto.
Qed.



Proposition  FreshTermcTermRem :
  (*"<<<"*)  forall  nl c nl1,
              ContextTerm Adversarial List c -> NonceList nl1 ->
                 ListFreshTermcTerm nl (fun x => c (x :: nl1)) ->
exists nl2,( ListFresh nl nl2 /\  NonceList nl2 /\ (fun x => c (x :: nl1)) = (fun x => c (x :: nl2))). (*">>>"*)
Proof.
  intros.
  pose (FreshcTermRem nl (fun x => [c x]) nl1).
  assert (Context Adversarial List (fun x : ToL List => [c x])).
  ProveContext.
  apply e in H2.
  inversion H2.
  inversion H3.
  inversion H5.
  exists x.
  repeat split.
  assumption.
  assumption.
  assert ((fun x : ppt => HD [c (x :: nl1)]) = (fun x0 : ppt => HD [c (x0 :: x)])).
  apply functional_extensionality.
  intros.
  assert (forall f g, f = (fun x : ppt => [c (x :: nl1)]) -> g = (fun x0 : ppt => [c (x0 :: x)]) -> f x0 = g x0).
  intros.
  rewrite <- H8 in H7.
  rewrite <- H9 in H7.
  rewrite H7.
  reflexivity.
  pose (H8 (fun x : ppt => [c (x :: nl1)]) (fun x0 : ppt => [c (x0 :: x)])).
  simpl in e0.
  rewrite e0.
  reflexivity.
  reflexivity.
  reflexivity.
  simpl in H8.
  assumption.
  assumption.
  pose H1.
  apply ListFreshTermcTermNonceList' in l.
  apply lfrctlConc.
  assumption.
  assumption.
  apply lfrctlnil.
  assumption.
Qed.















Proposition FreshTermcTermfromNonceList :
  forall nc tl ,
    FreshTermcTerm nc tl  <->
      exists f lx , ContextTerm Adversarial List f /\
                      NonceList lx /\
                      Fresh nc lx /\
                      tl = (fun x => f (x::lx)).
Proof.
  intros n.
  assert (forall nc tl ,
             FreshTermcTerm  nc tl ->
             exists (f : ToL List ->  ppt) (lx : list ppt),
               ContextTerm Adversarial List f /\
                 NonceList lx /\ Fresh nc lx /\
                 tl = (fun x => f (x::lx))).
  { apply  (FreshTermcTerm_mut
              (fun nc tl =>  exists (f : ToL List -> list ppt) (lx : list ppt),
                   Context Adversarial List f /\
                     NonceList lx /\ Fresh nc lx /\
                     tl = (fun x => f (x::lx)))
              (fun x t =>   exists (f : ToL List ->  ppt) (lx : list ppt),
                   ContextTerm Adversarial List f /\
                     NonceList lx /\
                     Fresh x lx /\
                     t = (fun x => f (x::lx))  )   ).
    - intros.
      exists (fun lx => []).
      exists [nonce (S n0)].
      repeat split.
      + ProveContext.
      + ProveNonceList.
      + ProveFresh.
    - intros.
      inversion_clear H0 as [f [lx [H3 [H4 [H5 H6]]]]].
      inversion_clear H2 as [fc [lc [H7 [H8 [H9 H10]]]]].
      rewrite H6.
      rewrite H10.
      simpl.
      exists (fun l => (f (firstn (1 + (length lx)) l)) :: (fc ((firstn 1 l)++(skipn (1+(length lx)) l)))).
      exists (lx ++ lc).
      repeat split.
      + ProveContext.
      + ProveNonceList.
      + ProveFresh.
      + simpl.
        rewrite fstn.
        rewrite skpn.
        auto.
    - intros.
inversion_clear H0 as [f [lx [H3 [H4 [H5 H6]]]]].
      inversion_clear H2 as [fc [lc [H7 [H8 [H9 H10]]]]].
      rewrite H6.
      rewrite H10.
      simpl.
      exists (fun l => (f (firstn (1 + (length lx)) l)) ++ (fc ((firstn 1 l)++(skipn (1+(length lx)) l)))).
      exists (lx ++ lc).
      repeat split.
      + ProveContext.
      + ProveNonceList.
      + ProveFresh.
      + simpl.
        rewrite fstn.
        rewrite skpn.
        auto.
    - intros.
      inversion_clear H1.
      inversion_clear H2.
      exists (fun lx => tl (x lx)).
      exists x0.
      inversion_clear H1.
      inversion_clear H3.
      inversion_clear H4.
      repeat split.
      + ProveContext.
      + assumption.
      + assumption.
      + rewrite H5.
        reflexivity.
    - exists (fun x => HD (TL x)).
      exists [nonce m].
      repeat split.
      + ProveContext.
      + ProveNonceList.
      + ProveFresh.
    - intros.
      inversion_clear H1.
      inversion_clear H2.
      exists (fun lx => t (x lx)).
      exists x0.
      inversion_clear H1.
      inversion_clear H3.
      inversion_clear H4.
      repeat split.
      + ProveContext.
      + assumption.
      + assumption.
      + rewrite H5.
        reflexivity.
    - intros.
      exists (fun x : ToL List => t (HD x)).
      exists [].
      repeat split.
      + ProveContext.
      + constructor.
      + ProveFresh.
  }
  intros.
  split.
  - intros.
    apply (H n tl).
    assumption.
  - intros.
    inversion H0.
    inversion H1.
    destruct H2.
    destruct H3.
    destruct H4.
    rewrite H5.
    assert (Fresh n x0); auto.
    apply FreshIsNonce in H6.
    unfold Nonce in H6.
    inversion H6.
    rewrite <- H7.
    apply (frtctFAdv (nonce x1) x).
    + assumption.
    + apply frctConc.
      * apply (frtctCAdv x1 id).
        ProveContext.
      * apply frtcCFresh.
        rewrite H7.
        assumption.
Qed.





Proposition FreshcTermfromNonceList :
 forall nc tl , FreshcTerm nc tl  <-> exists f lx , Context Adversarial List f /\
NonceList lx /\ Fresh nc lx /\ tl = (fun x => f (x::lx)).
Proof. intros n.
assert (forall nc tl , FreshcTerm  nc tl ->
exists (f : ToL List ->  list ppt) (lx : list ppt),
  Context Adversarial List f /\
  NonceList lx /\ Fresh nc lx /\ tl = (fun x => f (x::lx))).
{ apply  (FreshcTerm_mut (fun nc tl =>  exists (f : ToL List -> list ppt)
(lx : list ppt),
  Context Adversarial List f /\
  NonceList lx /\ Fresh nc lx /\ tl = (fun x => f (x::lx)))  (fun x t =>   exists (f : ToL List ->  ppt)
(lx : list ppt),
  ContextTerm Adversarial List f /\
  NonceList lx /\ Fresh x lx /\ t = (fun x => f (x::lx))  )   ).
- intros.  exists (fun lx => []). exists [nonce (S n0)]. apply conj.
ProveContext.  apply conj.  ProveNonceList.
 apply conj.  ProveFresh.
 reflexivity.
- intros.
inversion_clear H0 as [f [lx [H3 [H4 [H5 H6]]]]].
 inversion_clear H2 as [fc [lc [H7 [H8 [H9 H10]]]]].
 rewrite H6. rewrite H10. simpl.
 exists (fun l => (f (firstn (1 + (length lx)) l)) :: (fc ((firstn 1 l)++(skipn (1+(length lx)) l)))).
 exists (lx ++ lc). repeat split. ProveContext.
 ProveNonceList. ProveFresh. simpl. rewrite fstn. rewrite skpn. auto.
 - intros.
inversion_clear H0 as [f [lx [H3 [H4 [H5 H6]]]]].
 inversion_clear H2 as [fc [lc [H7 [H8 [H9 H10]]]]].
 rewrite H6. rewrite H10. simpl.
 exists (fun l => (f (firstn (1 + (length lx)) l)) ++ (fc ((firstn 1 l)++(skipn (1+(length lx)) l)))).
 exists (lx ++ lc). repeat split. ProveContext.
 ProveNonceList. ProveFresh. simpl. rewrite fstn. rewrite skpn. auto.
- intros.
inversion_clear H1. inversion_clear H2.   exists (fun lx => tl (x lx)).
exists x0. apply conj.  inversion_clear H1. ProveContext.  inversion_clear H1.
inversion_clear H3. inversion_clear H4. apply conj.
auto. apply conj. auto. rewrite H5. reflexivity.

- intros. exists (fun x => HD (TL x)).
exists [nonce m].  apply conj.  ProveContext. apply conj. ProveNonceList.
apply conj. ProveFresh. unfold HD. unfold TL; simpl.   reflexivity.
- intros.
inversion_clear H1. inversion_clear H2.   exists (fun lx => t (x lx)).
exists x0. apply conj.  inversion_clear H1. ProveContext.  inversion_clear H1.
inversion_clear H3. inversion_clear H4. apply conj.
auto. apply conj. auto. rewrite H5. reflexivity.
- intros.   exists (fun x : ToL List => t (HD x)). exists []. apply conj.
ProveContext.  apply conj. constructor. apply conj. ProveFresh. unfold HD. simpl. reflexivity.
} intros. split. intros.    apply (H n tl). auto.
 intros.  inversion H0. inversion H1. destruct H2. destruct H3.
destruct H4. rewrite H5.  assert (Fresh n x0); auto. apply FreshIsNonce in H6.
 unfold Nonce in H6.

inversion H6. rewrite <- H7.  apply (frctFAdv (nonce x1) x). auto. apply frctConc.
apply (frtctCAdv x1 id). ProveContext.
apply frtcCFresh. rewrite H7. auto. Qed.



Proposition ListFreshcTermfromNonceList :
 forall nl tl ,  nl <> [] -> ListFreshcTerm nl tl  -> exists f nl2 , Context Adversarial List f /\
NonceList nl2 /\ ListFresh nl nl2 /\ tl = (fun x => f (x :: nl2)).

Proof.  intros nl tl. intros H.   intros LF.
assert ( forall lx,  ListFreshcTerm nl lx ->
exists
  (f : ToL List -> list ppt)
(nl2 : list ppt),
  Context Adversarial List f /\
  NonceList nl2 /\
  ListFresh nl nl2 /\
  lx = (fun x => f (x :: nl2))).
intros lx. intros H0.
 induction H0.
contradiction. induction nl.    apply (FreshcTermfromNonceList nc lx) in H0.
inversion H0. inversion H2.   exists (fun lx => x  lx)  . exists x0.
destruct H3. destruct H4. destruct H5.
apply conj; auto. ProveContext.  apply conj; auto. apply conj. apply lfrConc.
auto.  constructor. unfold TL.  auto.
 assert (a :: nl <> []).  unfold not; intros.  inversion H2.
apply IHListFreshcTerm in H2. inversion H2.  inversion H3.
destruct H4. destruct H5. destruct H6.  apply (lfrctConc  nc (a :: nl) lx H0) in H1.
rewrite H7 in H1.
assert (ListFreshcTerm (nc :: a :: nl)
       (fun x1 : ppt => x (x1 :: x0))); auto.
apply  (FreshcTermRem (nc :: a :: nl) x x0 H4 H5) in H1.
inversion H1. destruct H9. exists (fun lx => x  lx). exists x1.
destruct H10. rewrite H11 in H7. apply conj. ProveContext. auto.
inversion LF. auto.
 apply H0.
auto. Qed.



(***********************    Property of FreshC   **********************)

(* given any {f: context adv} and {lx : nonce list} , we cannot construct to prove the existence of {f1: context adv} and {lx1 : nonce list} that
 (fun x : list ppt => f (lx ++ x)) = (fun x : list ppt => f1 (x ++ lx1))

but we can prove from the opposite direction,
 (fun x : list ppt => f (x ++ lx)) = (fun x : list ppt => f1 (lx1 ++ x)) *)

(*  *)

Proposition FreshTermcfromNonceList :
 forall nc tl , FreshTermc nc tl  <-> exists f lx , ContextTerm Adversarial List f /\
  NonceList lx /\ Fresh nc lx /\ tl = (fun x => f (lx ++ x)).
Proof.
  split; intros.

  - apply (FreshTermc_mut
    (fun nc tl => exists f lx , Context Adversarial List f /\ NonceList lx /\ Fresh nc lx /\ tl = (fun x => f (lx ++ x)))
    (fun nc tl => exists f lx , ContextTerm Adversarial List f /\ NonceList lx /\ Fresh nc lx /\ tl = (fun x => f (lx ++ x)))); intros; auto.
    + exists (fun _ => []). exists ([]).
      split. ProveContext.
      split. ProveNonceList.
      split.  ProveFresh.
      reflexivity.
    + destruct H1 as [ f1 [ lx1 [ H11 [ H12 [H13 ]]]]] . destruct H3 as [ f3 [ lx3 [ H31 [ H32 [H33 ]]]]] .
      rewrite H1, H3.
      exists (fun lx => (f1 ((firstn (length lx1) lx) ++ (skipn (length (lx1 ++ lx3)) lx))) :: (f3 (skipn (length lx1) lx))). exists (lx1 ++ lx3).
      split. ProveContext.
      split. apply nlComp; auto.
      split. apply frlConc; auto.
      apply functional_extensionality.
      * intros. rewrite <- app_assoc. rewrite firstn_app_exact.  rewrite app_assoc. rewrite skipn_app_exact.
        rewrite  <- app_assoc.  rewrite skipn_app_exact.
        reflexivity.
    + destruct H1 as [ f1 [ lx1 [ H11 [ H12 [H13 ]]]]] . destruct H3 as [ f3 [ lx3 [ H31 [ H32 [H33 ]]]]] .
      rewrite H1, H3.
      exists (fun lx => (f1 ((firstn (length lx1) lx) ++ (skipn (length (lx1 ++ lx3)) lx))) ++ (f3 (skipn (length lx1) lx))). exists (lx1 ++ lx3).
      split. ProveContext.
      split. apply nlComp; auto.
      split. apply frlConc; auto.
      apply functional_extensionality.
      * intros. rewrite <- app_assoc. rewrite firstn_app_exact.  rewrite app_assoc. rewrite skipn_app_exact.
        rewrite  <- app_assoc.  rewrite skipn_app_exact.
        reflexivity.
    + destruct H2 as [ f2 [ lx2 [ H21 [ H22 [H23 ]]]]] . rewrite H2.
      exists (fun x => tl0 (f2 x)). exists (lx2).
      split. ProveContext.
      split. auto.
      split.  auto.
      reflexivity.
    + exists (fun x => t x). exists [].
      split. ProveContext.
      split. ProveNonceList.
      split. ProveFresh.
      * simpl. reflexivity.
    + exists (fun x => Nth 0 x). exists [nonce (m)].
      split. ProveContext.
      split. ProveNonceList.
      split. ProveFresh.
      unfold Nth. unfold nth. simpl.
      reflexivity.
    + destruct H2 as [ f2 [ lx2 [ H21 [ H22 [H23 ]]]]] . rewrite H2.
      exists (fun x => t (f2 x)). exists lx2.
      split. ProveContext.
      split. auto.
      split. auto.
      reflexivity.
    + exists (fun x => t x). exists [].
      split. ProveContext.
      split. ProveNonceList.
      split. ProveFresh.
      reflexivity.

  - destruct H as [ f [ lx [ H1 [ H2 [H3 ]]]]] .
    rewrite H. assert (Fresh nc lx); auto. apply FreshNonce in H0. destruct H0.
    pose (frtcFAdv x f (fun x => lx ++ x)) as c. simpl in c. rewrite H0 in c. apply c.
    + auto.
    + pose (frcapp x lx) as d. rewrite H0 in d. apply d; auto.
Qed.



Proposition FreshcfromNonceList :
 forall nc tl , Freshc nc tl  <-> exists f lx , Context Adversarial List f /\
  NonceList lx /\ Fresh nc lx /\ tl = (fun x => f (lx ++ x)).
Proof.
  split; intros.

  - apply (Freshc_mut
    (fun nc tl => exists f lx , Context Adversarial List f /\ NonceList lx /\ Fresh nc lx /\ tl = (fun x => f (lx ++ x)))
    (fun nc tl => exists f lx , ContextTerm Adversarial List f /\ NonceList lx /\ Fresh nc lx /\ tl = (fun x => f (lx ++ x)))); intros; auto.
    + exists (fun _ => []). exists ([]).
      split. ProveContext.
      split. ProveNonceList.
      split.  ProveFresh.
      reflexivity.
    + destruct H1 as [ f1 [ lx1 [ H11 [ H12 [H13 ]]]]] . destruct H3 as [ f3 [ lx3 [ H31 [ H32 [H33 ]]]]] .
      rewrite H1, H3.
      exists (fun lx => (f1 ((firstn (length lx1) lx) ++ (skipn (length (lx1 ++ lx3)) lx))) :: (f3 (skipn (length lx1) lx))). exists (lx1 ++ lx3).
      split. ProveContext.
      split. apply nlComp; auto.
      split. apply frlConc; auto.
      apply functional_extensionality.
      * intros. rewrite <- app_assoc. rewrite firstn_app_exact.  rewrite app_assoc. rewrite skipn_app_exact.
        rewrite  <- app_assoc.  rewrite skipn_app_exact.
        reflexivity.
 + destruct H1 as [ f1 [ lx1 [ H11 [ H12 [H13 ]]]]] . destruct H3 as [ f3 [ lx3 [ H31 [ H32 [H33 ]]]]] .
      rewrite H1, H3.
      exists (fun lx => (f1 ((firstn (length lx1) lx) ++ (skipn (length (lx1 ++ lx3)) lx))) ++ (f3 (skipn (length lx1) lx))). exists (lx1 ++ lx3).
      split. ProveContext.
      split. apply nlComp; auto.
      split. apply frlConc; auto.
      apply functional_extensionality.
      * intros. rewrite <- app_assoc. rewrite firstn_app_exact.  rewrite app_assoc. rewrite skipn_app_exact.
        rewrite  <- app_assoc.  rewrite skipn_app_exact.
        reflexivity.
    + destruct H2 as [ f2 [ lx2 [ H21 [ H22 [H23 ]]]]] . rewrite H2.
      exists (fun x => tl0 (f2 x)). exists (lx2).
      split. ProveContext.
      split. auto.
      split.  auto.
      reflexivity.
    + exists (fun x => t x). exists [].
      split. ProveContext.
      split. ProveNonceList.
      split. ProveFresh.
      * simpl. reflexivity.
    + exists (fun x => Nth 0 x). exists [nonce (m)].
      split. ProveContext.
      split. ProveNonceList.
      split. ProveFresh.
      unfold Nth. unfold nth. simpl.
      reflexivity.
    + destruct H2 as [ f2 [ lx2 [ H21 [ H22 [H23 ]]]]] . rewrite H2.
      exists (fun x => t (f2 x)). exists lx2.
      split. ProveContext.
      split. auto.
      split. auto.
      reflexivity.
    + exists (fun x => t x). exists [].
      split. ProveContext.
      split. ProveNonceList.
      split. ProveFresh.
      reflexivity.

  - destruct H as [ f [ lx [ H1 [ H2 [H3 ]]]]] .
    rewrite H. assert (Fresh nc lx); auto. apply FreshNonce in H0. destruct H0.
    pose (frcFAdv x f (fun x => lx ++ x)) as c. simpl in c. rewrite H0 in c. apply c.
    + auto.
    + pose (frcapp x lx) as d. rewrite H0 in d. apply d; auto.
Qed.



Proposition NonceRename :
 (*"<<<"*)   forall {f :  ppt -> list ppt},
     forall {nc1 nc2 } ,  ListFreshcTerm [nc1 ; nc2] f  ->   (*">>>"*)
      (f nc1) ~ (f nc2).
Proof. intros.
assert ([nc1; nc2] <> []). unfold not; intros. inversion H0.
apply  (ListFreshcTermfromNonceList [nc1; nc2] f) in H0.
inversion H0. inversion H1. destruct H2. destruct H3.
destruct H4. rewrite H5. apply cind_funcapp. auto. apply FreshInd; auto.
inversion H4.  inversion H10. auto. auto.
inversion H4.  inversion H10. auto.
inversion H4.  inversion H10. auto. auto.
inversion H4.  inversion H10. auto. reflexivity.  auto.
 Qed.




(**************************************************************************************)
(****************************** Below here might be useless *****************************)
(**************************************************************************************)



(**************************************************************************************)
(******************************** List Freshness' *****************************)
(**************************************************************************************)









Inductive ListFresh' : list ppt -> list ppt -> Prop := (* metapredicate *)
| nilfrl' : forall t,  ListFresh' [ ] t
| lfrnil' : forall nl, NonceList nl -> ListFresh' nl [ ]
| lfrConc' : forall nl (t : ppt) (tc : list ppt) ,
    (ListFreshTerm' nl t)
    -> (ListFresh' nl tc)
    -> (ListFresh' nl (t :: tc))
with ListFreshTerm' : list ppt -> ppt -> Prop :=
| nilfrt' : forall t,  ListFreshTerm' [ ] t
| lfrtNN' :
forall nl nc t ,  FreshTerm nc t ->
(ListFreshTerm' nl t) ->
                         (ListFreshTerm' (nc :: nl) t)
| lfrtFAdv': forall nl (t: list ppt -> ppt) (tc : list ppt) ,
    (ContextTerm Adversarial List t)
    -> ListFresh' nl tc
    -> ListFreshTerm' nl (t tc)
| lfrtCAdv': forall nl (t: ppt) ,
    (ContextTerm Adversarial List (fun x => t))
    -> NonceList nl -> ListFreshTerm' nl t.


Proposition ListFresh'NonceList :
forall nl tl , ListFresh' nl tl -> NonceList nl.
Proof.  intros. induction H. constructor. auto. auto.
Qed.


Proposition ListFreshTerm'NonceList :
forall nl t , ListFreshTerm' nl t -> NonceList nl.
Proof.  intros. induction H. constructor.
apply nlN. apply FreshTermIsNonce in H.  auto. auto.
apply ListFresh'NonceList  in H0. auto. auto.
Qed.



Scheme ListFresh'_mut := Minimality for ListFresh' Sort Prop
  with ListFreshTerm'_mut := Minimality for ListFreshTerm' Sort Prop.






Proposition LF : forall nl tl, ListFresh' nl tl -> ListFresh nl tl.
Proof. intros.
apply (ListFresh'_mut (fun nl tl => ListFresh nl tl) (fun nl t => ListFreshTerm nl t)).
 constructor. intros.  apply lfrlnil. auto.
 intros. apply lfrlConc. apply ListFreshTermNonceList in H1. auto. auto. auto.
intros. constructor. intros.
apply lfrtConc. auto. auto.
intros. apply lfrtFAdv.  apply ListFreshNonceList in H2. auto. auto. auto.
intros.   apply lfrtCAdv. auto. ProveContext.  auto.
Qed.



Proposition LFT : forall nl t, ListFreshTerm' nl t -> ListFreshTerm nl t.
Proof. intros.
apply (ListFreshTerm'_mut (fun nl tl => ListFresh nl tl) (fun nl t => ListFreshTerm nl t)).
 constructor. intros.  apply lfrlnil. auto.
 intros. apply lfrlConc. apply ListFreshTermNonceList in H1. auto. auto. auto.
intros. constructor. intros.
apply lfrtConc. auto. auto.
intros. apply lfrtFAdv. apply ListFreshNonceList in H2. auto. auto. auto.
intros.   apply lfrtCAdv. auto. ProveContext.  auto.
Qed.


Proposition blabla : forall nc tl , Fresh nc tl ->   ListFresh' [nc] tl.
Proof. intros.  apply (Fresh_mut (fun nc tl =>  ListFresh' [nc]  tl)  (fun nc t =>  ListFreshTerm' [nc]  t)) in H.
auto. intros. apply lfrnil'.  ProveNonceList.
intros.   apply lfrConc'.  auto. auto.
intros.  apply lfrtNN'. ProveFresh. constructor. intros.
apply lfrtFAdv'. auto. auto. intros. apply lfrtCAdv'. auto.
ProveNonceList.
Qed.


Proposition invlfrConc' : forall t  nl tl,  ListFresh'  nl (t :: tl) -> (ListFreshTerm' nl  t /\ ListFresh' nl tl).
Proof. intros. inversion H. constructor. constructor. constructor. constructor.
auto. auto. Qed.

Proposition lfrlConc' : forall nc nl tl , Fresh  nc tl ->  ListFresh' nl tl ->   ListFresh' (nc :: nl) tl.
Proof. intros nc nl tl.  intros H.  intros LF1.
apply (Fresh_mut (fun nc tl =>  ListFresh' nl tl-> ListFresh' (nc :: nl) tl) (fun nc t =>  ListFreshTerm' nl  t ->  ListFreshTerm' (nc :: nl) t)) in H .
intros. auto. intros. constructor. ProveNonceList. apply LF in H0.   apply ListFreshNonceList in H0. auto. intros. apply lfrConc'.
  apply H1.
   apply invlfrConc' in H4. destruct H4.  auto. apply H3.  apply invlfrConc' in H4.
 destruct H4.  auto. intros.  apply lfrtNN'. ProveFresh. auto. intros. apply lfrtNN'. ProveFresh. auto.
intros. apply lfrtNN'. ProveFresh. auto. auto.
Qed.


Proposition FLT: forall nl t , ListFreshTerm nl t -> ListFreshTerm' nl t.
Proof. intros. induction H.  constructor. apply lfrtNN'.  auto. auto.
Qed.

Proposition FL: forall   nl tl , ListFresh nl tl -> ListFresh' nl tl.
Proof. intros.  induction H.  constructor. induction lx. constructor.
apply FreshIsNonce in H. ProveNonceList.  apply ListFreshNonceList in H0.
auto. apply lfrConc'.  apply lfrtNN'. inversion H. auto.  apply invlfrlConc in H0.
destruct IHListFresh. constructor.  destruct H0. apply FLT. apply H0.
destruct H0. apply FLT. auto. apply IHlx.
inversion H. auto.  apply invlfrlConc in H0.
destruct H0. auto. inversion IHListFresh . constructor. inversion IHListFresh . constructor; auto. auto.
Qed.



Proposition invlfrlConc' : forall nc nl tl, ListFresh' (nc :: nl) tl -> ( Fresh nc  tl /\ ListFresh'  nl tl).
Proof. intros. apply LF in H. inversion H. apply FL in H4. auto. Qed.





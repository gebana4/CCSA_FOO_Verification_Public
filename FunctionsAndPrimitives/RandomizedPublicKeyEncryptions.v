
(************************************************************************)
(* Copyright (c) 2021, Gergei Bana and Qianli Zhang                     *)
(*                                                                      *)
(* This work is licensed under the MIT license. The license is          *)
(* described in the file "LICENSE" available at the root of the source  *)
(* or at https://opensource.org/licenses/MIT                            *)
(************************************************************************)


Require Import Core.
Require Import BasicExamples. 





(*******************************************************************************)
(*******************************************************************************)
(**************************** IND-CCA2 SECURITY ********************************)
(*******************************************************************************)
(*******************************************************************************)


Section CCA2Game.
Variable (L enc dec pkey skey rand : list ppt -> ppt)  (error : ppt) (nl nl': list ppt).
(* Nonce lists used by the Challenger for key generation and encrption.  *)


(* Challenger - Attacker interacion before the encryption by Challenger *)

Inductive CCA2BeforeEncTerm : ppt -> Prop :=
| CCA2Pkey :                  (* Public key is put out by Challenger *)
    CCA2BeforeEncTerm    (pkey nl)
| CCA2AttNonceTerm :    (* Attacker can generate nonces other than "n" "n'" *)
    forall n,
      Fresh (nonce n) nl
      -> Fresh (nonce n)  nl'
      -> CCA2BeforeEncTerm  (nonce n)
| CCA2AttContListTerm :        (* Attacker can apply any of his contexts *)
    forall tl f ,
      PPT  Adversarial f
      -> CCA2BeforeEnc tl
      -> CCA2BeforeEncTerm (f tl)
| CCA2DecOrac1 :             (* Challenger decrypts *)
    forall u ,
      CCA2BeforeEncTerm u
      -> CCA2BeforeEncTerm  (dec [ u  ; skey nl] )
with CCA2BeforeEnc : list ppt -> Prop :=
| CCA2BeforeTermList :        (* Lists of CCA2 terms are CCA2 lists *)
    forall u ul ,
      CCA2BeforeEncTerm u
      -> CCA2BeforeEnc ul
      -> CCA2BeforeEnc (u :: ul)
| CCA2BeforeTermNil :  CCA2BeforeEnc []. (* [] should be in the Before context*)

(* Challenger - Attacker interacion after the encryption by Challenger
Encryption of the Challenger is read into the variable "x" *)


Inductive CCA2AfterEncTerm : (ppt -> ppt) -> Prop :=
| CCA2AttContId :
       CCA2AfterEncTerm (fun x => x)
| CCA2PkeyCont :                  (* Public key is put out by Challenger *)
    CCA2AfterEncTerm    (fun _ => (pkey nl))
| CCA2AttNonceTermCont :    (* Attacker can generate nonces other than "n" "n'" *)
    forall n,
      Fresh (nonce n) nl
      -> Fresh (nonce n)  nl'
      -> CCA2AfterEncTerm  (fun _ => (nonce n))
| CCA2DecOrac2 :             (* Challenger decrypts as long as it is not the output of the encryption challenge, which goes in "x" *)
    forall tl ,
      CCA2AfterEncTerm tl
      -> CCA2AfterEncTerm  (fun x => (If EQ [tl x ; x ] Then error Else (dec [ tl x ; skey nl] ) ) )
| CCA2AttBeforeToAfter : forall u , CCA2BeforeEncTerm u -> CCA2AfterEncTerm (fun x => u)  (* Attacker after gets the information from before *)
| CCA2AttContListTermFun :        (* Attacker can apply any of his functions *)
    forall  f tl,
      (PPT Adversarial f)
      -> CCA2AfterEnc tl
      -> CCA2AfterEncTerm (fun x => (f (tl x)))
with CCA2AfterEnc : (ppt -> list ppt) -> Prop :=
| CCA2AfterTermList :        (* Lists of CCA2 terms are CCA2 lists *)
    forall t tl ,
      CCA2AfterEncTerm t
      -> CCA2AfterEnc tl
      -> CCA2AfterEnc (fun x => (t x):: (tl x))
| CCA2AfterTermNil :  CCA2AfterEnc (fun _ => []). (* [] should be in the After context*)



Scheme CCA2AfterEnc_mut := Minimality for CCA2AfterEnc Sort Prop
  with CCA2AfterEncTerm_mut := Minimality for CCA2AfterEncTerm Sort Prop.



End CCA2Game.



Proposition CCA2AfterTermIsContextTermGeneral:
  forall dec pkey skey error nl nl' t,
    PPT General dec -> PPT General pkey -> PPT General skey ->
    CCA2AfterEncTerm dec pkey skey error nl nl' t -> ContextTerm General Term t.
Proof.
  intros.
  apply (CCA2AfterEncTerm_mut dec pkey skey error nl nl'
             (fun tl => Context General Term tl) (fun t => ContextTerm General Term t)
        ).
  all: ProveContext.
Qed.

Proposition CCA2AfterIsContextGeneral:
  forall dec pkey skey error nl nl' tl,
    PPT General dec -> PPT General pkey -> PPT General skey ->
    CCA2AfterEnc dec pkey skey error nl nl' tl -> Context General Term tl.
Proof.
  intros.
  apply (CCA2AfterEnc_mut dec pkey skey error nl nl'
             (fun tl => Context General Term tl) (fun t => ContextTerm General Term t)
        ).
  all: ProveContext.
Qed.



(* CCA2 security of an encryption scheme: *)
Definition CCA2 (L enc dec pkey skey rand : list ppt -> ppt) (error : ppt)  : Prop :=
  forall  (nl nl': list ppt) (t:  ppt -> list ppt) (u u' : ppt),
       NonceList nl -> NonceList nl' -> ListFresh nl nl'
    -> CCA2BeforeEncTerm dec pkey skey nl nl'  u
    -> CCA2BeforeEncTerm dec pkey skey nl nl'  u'
    -> CCA2AfterEnc dec pkey skey error  nl nl' t
    ->
       t (If EQ [L [u] ; L [u']] Then  enc [u  ; pkey nl; rand nl'] Else error)
     ~
       t (If EQ [L [u] ; L [u']] Then  enc [u' ; pkey nl; rand nl'] Else error).





(* It is usually possible to prove the length equality separately and hence remove the IfThenElse:  *)

Definition CCA2L (L enc dec pkey skey rand : list ppt -> ppt) (error : ppt) : Prop :=
  forall  (nl nl': list ppt) (t:  ppt -> list ppt) (u u' : ppt),
       NonceList nl -> NonceList nl' -> ListFresh nl nl'
    -> CCA2BeforeEncTerm dec pkey skey nl nl'  u
    -> CCA2BeforeEncTerm dec pkey skey nl nl'  u'
    -> CCA2AfterEnc dec pkey skey error nl nl' t
    -> L [u] = L [u']
    -> t ( enc [u  ; pkey nl; rand nl'] )
         ~
         t ( enc [u' ; pkey nl; rand nl'] ).






(* An encryption that satisfies the CCA2 property also satisfies the CCA2L property: *)

Proposition CCA2toCCA2L :
  forall (L enc dec pkey skey rand : list ppt -> ppt) (error : ppt),
    CCA2 L enc dec pkey skey rand error  -> CCA2L  L enc dec pkey skey rand error.
Proof.
  unfold CCA2L.
unfold CCA2.
intros.
apply (H nl nl' t u u') in  H0.
apply ceq_eq in H6.
rewrite H6 in H0.
repeat rewrite If_true in H0.
all : assumption.
Qed.


Definition ITEdec dec sk error m f c := 
  (If (f ≟ c)
     Then m
     Else (If (f ≟ c)
             Then error
             Else dec [f; sk])).



Lemma decIfThenElse1: forall  (dec : list ppt -> ppt) (c sk error m f : ppt),
    dec [c; sk] = m ->
    PPT General dec -> 
    dec [f; sk]    
    =
      If (f ≟ c)
        Then m
        Else  dec [f; sk].
Proof.
  intros.
  rewrite <- (@If_same (f ≟ c) f) at 1.
  rewrite (@Eq_branch (f) c  (fun x => x) _ ).
  rewrite (@If_morph (fun x => dec [x; sk]) (f ≟ c) _ _ ).
  simpl. rewrite H.
  reflexivity.
  all : ProveContext.
Qed.



(* Convert decryption to the form we can use for CCA: *) 
Lemma decIfThenElse:
  forall  (dec : list ppt -> ppt) (sk error m c f: ppt),
    dec [c; sk] = m ->
    PPT General dec ->
    (dec [f; sk])
    =
      If (f ≟ c)
        Then m
        Else (If (f ≟ c)
                Then error
                Else dec [f; sk]).
Proof.
  intros.
  rewrite (@If_eval (fun _ => _) (fun b => If b Then error Else _) (f ≟ c)).
  rewrite If_false.
  rewrite <- decIfThenElse1.
  reflexivity.
  all: ProveboolandContext.
Qed.



Lemma decIfThenElseErRem:
  forall  (dec : list ppt -> ppt) (sk error m f c: ppt),
    PPT General dec ->
    If (f ≟ c)
      Then m
      Else (If (f ≟ c)
                Then error
                Else dec [f; sk])
    =
      If (f ≟ c)
      Then m
      Else  (dec [f; sk]).
Proof.
  intros.
  rewrite (@If_eval (fun _ => _) (fun b => If b Then error Else _) (f ≟ c)).
  rewrite If_false.
  reflexivity.
  all: ProveboolandContext.
Qed.







(* Ltacs to check *) 

Ltac ProveCCA2Before :=
  repeat (intros; auto;
          match goal with
          | [ |- CCA2BeforeEncTerm  _ ?Pk _ ?X _ (?Pk ?X) ]
            => apply CCA2Pkey
          | [ |- CCA2BeforeEncTerm _ _ _  _ _ (nonce _) ]
            => apply CCA2AttNonceTerm; ProveFresh; try lia
          | [ |- CCA2BeforeEncTerm ?D _ ?Sk  ?X _ (?D [ _ ; ?Sk ?X]) ]
            => apply CCA2DecOrac1
          | [ |- CCA2BeforeEncTerm  _ _ _ _ _ (?X) ]
            => first [ apply CCA2AttContListTerm; ProvePPT | apply CCA2AttContListTerm with (f := fun _ => X) (tl := []); ProvePPT ]
          | [ |- CCA2BeforeEnc  _ _ _  _ _ (cons _ _) ]
            => try apply CCA2BeforeTermList
          | [ |- CCA2BeforeEnc _ _ _  _ _ nil ]
            => try apply CCA2BeforeTermNil
  end).

Ltac ProveCCA2After :=
  repeat  (intros; simpl; auto; (*add simpl here*)
           match goal with
           | [ |- CCA2AfterEncTerm _ _ _ _  _ _ (fun x => x) ]
             => apply CCA2AttContId
           | [ |- CCA2AfterEnc  _ _ _ _  _ _ (fun _ => cons _ _) ]
             => try apply CCA2AfterTermList
           | [ |- CCA2AfterEncTerm  _ ?Pk _ _ ?X _ (fun _ => ?Pk ?X)  ]
             => apply CCA2PkeyCont
           | [ |- CCA2AfterEncTerm _ _ _ _ _ _ (fun _ => nonce ?N ) ]
             => apply CCA2AttNonceTermCont; ProveFresh; try lia
           | [ |- CCA2AfterEncTerm ?D _ ?Sk ?Er  ?Nl _ (fun x
                                                        => If _ Then ?Er Else ?D [ _ ; ?Sk ?Nl]) ] => apply CCA2DecOrac2; ProvePPT
           | [ |- CCA2AfterEncTerm _ _ _ _ _ _ (fun _ => (?f _) ) ]
             => first [apply CCA2AttContListTermFun; ProvePPT | apply CCA2AttBeforeToAfter; try ProveCCA2Before]
           | [ |- CCA2AfterEnc _ _ _ _ _ _ (fun _ => nil) ]
             => try apply CCA2AfterTermNil
  end).

Ltac ProveCCA2 :=
  repeat  (intros; auto;
           match goal with
           | [ |- NonceList _ ]
             => ProveNonceList
           | [ |- ListFresh _ _ ]
             => ProveListFresh; constructor
           | [ |- CCA2BeforeEncTerm _ _ _ _ _ _ ]
             => ProveCCA2Before
           | [ |- CCA2BeforeEnc _ _ _ _ _ _ ]
             => ProveCCA2Before
           | [ |- CCA2AfterEnc _ _ _ _ _ _ _]
             => ProveCCA2After
           | [ |- CCA2AfterEncTerm _ _ _ _ _ _ _]
             => ProveCCA2After
           end).


(*******************************************************************************)
(*******************************************************************************)
(**************************** IND-CPA SECURITY ********************************)
(*******************************************************************************)
(*******************************************************************************)






Section CPAGame.
Variable  (L enc dec pkey skey rand : list ppt -> ppt) (error : ppt) (nl nl': list ppt).
(* Nonce lists "nl" and "nl'"used by the Challenger for key generation and encrption. *)



(* Challenger - Attacker interacion before the encryption by Challenger
I suspect that we cannot avoid mutual induction *)

Inductive CPABeforeEncTerm : ppt -> Prop :=
| CPAPkey :                  (* Public key is put out by Challenger *)
    CPABeforeEncTerm    (pkey nl)
| CPAAttNonceTerm :    (* Attacker can generate nonces other than "n" "n'" *)
    forall n,
      Fresh (nonce n) nl
      -> Fresh (nonce n) nl'
      -> CPABeforeEncTerm  (nonce n)
| CPAAttContListTerm :        (* Attacker can apply any of his contexts *)
    forall tl f ,
      PPT Adversarial f
      -> CPABeforeEnc tl
      -> CPABeforeEncTerm (f tl)
with CPABeforeEnc : list ppt -> Prop :=
| CPABeforeTermList :        (* Lists of CPA terms are CPA lists *)
    forall t tl ,
      CPABeforeEncTerm t
      -> CPABeforeEnc tl
      -> CPABeforeEnc (t :: tl)
| CPABeforeTermNil :  CPABeforeEnc [].

Scheme CPABeforeEnc_mut := Minimality for CPABeforeEnc Sort Prop
  with CPABeforeEncTerm_mut := Minimality for CPABeforeEncTerm Sort Prop.


(* Challenger - Attacker interacion after the encryption by Challenger
Encryption of the Challenger is read into the variable "x" *)

Inductive CPAAfterEncTerm : (ppt -> ppt) -> Prop :=
| CPAAttContId :
       CPAAfterEncTerm (fun x => x)
| CPAPkeyCont :                  (* Public key is put out by Challenger *)
    CPAAfterEncTerm    (fun x => (pkey nl))
| CPAAttNonceTermCont :    (* Attacker can generate nonces other than "n" "n'" *)
    forall n,
      Fresh (nonce n) nl
      -> Fresh (nonce n) nl'
      -> CPAAfterEncTerm  (fun x => (nonce n))
| CPAAttContListTermFun :        (* Attacker can apply any of his contexts *)
    forall tl f ,
      PPT Adversarial f
      -> CPAAfterEnc tl
      -> CPAAfterEncTerm (fun x => (f (tl x)))
with CPAAfterEnc : (ppt -> list ppt) -> Prop :=
| CPAAfterTermList :        (* Lists of CPA terms are CPA lists *)
    forall t tl ,
      CPAAfterEncTerm t
      -> CPAAfterEnc tl
      -> CPAAfterEnc (fun x => (t x):: (tl x))
| CPAAfterTermNil :  CPAAfterEnc (fun _ => []).
 (* Here we do not need after Attacker gets the information from before because there is nothing
before Attacker can do that the after attacker cannot. *)


Scheme CPAAfterEnc_mut := Minimality for CPAAfterEnc Sort Prop
  with CPAAfterEncTerm_mut := Minimality for CPAAfterEncTerm Sort Prop.



End CPAGame.



(*IND-CPA security of an encryption scheme *)
Definition CPA  (L enc pkey rand: list ppt -> ppt) (er : ppt) : Prop :=
  forall (nl nl' : list ppt) (t:  ppt -> list ppt) (u u' : ppt),
    NonceList nl -> NonceList nl' -> ListFresh nl nl'
    -> CPABeforeEncTerm  pkey nl nl' u
    -> CPABeforeEncTerm  pkey nl nl' u'
    -> CPAAfterEnc   pkey nl nl' t
    ->
    t (If EQ [L [u] ; L [u']] Then  enc [u  ; pkey nl; rand nl'] Else er)
   ~
    t (If EQ [L [u] ; L [u']] Then  enc [u' ; pkey nl; rand nl'] Else er).



(* It is usually possible to prove the length equality separately and hence remove the IfThenElse:  *)

Definition CPAL (L enc pkey rand: list ppt -> ppt) : Prop :=
  forall (nl nl' : list ppt) (t:  ppt -> list ppt) (u u' : ppt),
    NonceList nl -> NonceList nl' -> ListFresh nl nl'
    -> CPABeforeEncTerm  pkey nl nl' u
    -> CPABeforeEncTerm  pkey nl nl' u'
    -> CPAAfterEnc   pkey nl nl' t
    -> L [u] = L [u']
    ->
    t ( enc [u  ; pkey nl; rand nl'] )
   ~
    t ( enc [u' ; pkey nl; rand nl'] ).



(* An encryption that satisfies the CCA2 property also satisfies the CCA2L property: *)

Proposition CPAtoCPAL :
  forall (L enc pkey rand : list ppt -> ppt) (error : ppt)  (kl rl : nat),
    CPA L enc pkey rand error  -> CPAL  L enc pkey  rand.
Proof.
  unfold CPA.
unfold CPAL.
intros.
apply (H nl nl' t u u') in  H0.
apply ceq_eq in H6.
rewrite H6 in H0.
repeat rewrite If_true in H0.
all : assumption.
Qed.



(* Ltacs to be defined *)



(*******************************************************************************)
(*******************************************************************************)
(**************************** IND-CCA2 implies IND-CPA *************************)
(*******************************************************************************)
(*******************************************************************************)


Lemma CPABeforeIsCCA2Before :
  forall (L dec pkey skey rand : list ppt -> ppt) (u error : ppt)  (nl nl' : list ppt),
    CPABeforeEncTerm  pkey nl nl' u ->
    CCA2BeforeEncTerm dec pkey skey nl nl' u.
Proof.
  intros.
  apply (CPABeforeEncTerm_mut  pkey nl nl'
           (fun lu => CCA2BeforeEnc dec pkey skey nl nl' lu)
           (fun u => CCA2BeforeEncTerm dec pkey skey nl nl' u)).
  all: ProveCCA2Before.   
Qed.

 
Lemma CPAAfterIsCCA2After :
  forall (L dec pkey skey rand : list ppt -> ppt) (error : ppt)  (nl nl' : list ppt) (tl : ppt -> list ppt),
    CPAAfterEnc pkey nl nl' tl ->
    CCA2AfterEnc dec pkey skey error nl nl' tl.
Proof.
  intros.
  apply (CPAAfterEnc_mut  pkey nl nl'
           (fun tl => CCA2AfterEnc dec pkey skey error nl nl' tl)
           (fun t => CCA2AfterEncTerm dec pkey skey error nl nl' t)).
  all: ProveCCA2After.
Qed.


Theorem CCA2ImpliesCPA :
  forall (L enc dec pkey skey rand : list ppt -> ppt) (error : ppt),
    CCA2 L enc dec pkey skey rand error  ->
    CPA L enc pkey rand error.
Proof.
  intros.
  unfold CCA2 in H.
  unfold CPA.
  intros.
  apply H.
  all: try assumption. 
  - apply  CPABeforeIsCCA2Before; assumption.
  - apply  CPABeforeIsCCA2Before; assumption.
  - apply CPAAfterIsCCA2After; assumption.
Qed.     





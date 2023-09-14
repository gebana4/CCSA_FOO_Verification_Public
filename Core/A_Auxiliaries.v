Require Export Coq.Lists.List.
Require Export Coq.micromega.Lia.
Require Export Coq.Init.Nat.
Export ListNotations.



(* About the built-in "if then else" function *)

Lemma iteinv :
  forall (A : Type) (a : bool) (b c: A)  ,
    not (b = c)
    -> (if a then b else c) = b
    -> a = true.
Proof.
  intros.
  assert (not  (a = false)).
  { unfold not.
    intros.
    assert   ((if a then b else c) = c).
    { destruct a. discriminate H1. auto. }
    rewrite H0 in H2.  auto. }
  destruct a.
  - auto.
  - contradiction.
Qed.



Lemma TnF :
  not (True = False).
Proof.
  unfold not.
  intros.
  rewrite <- H.
  auto.
Qed.

Lemma TFiteinv :
  forall (a : bool) ,
    (if a then True else False)
    -> a = true.
Proof.
  intros.
  assert (H1 := TnF).
  apply (iteinv Prop a True False).
  - auto.
  - destruct a.
    + auto.
    + contradiction.
Qed.






(* About lists *)

(* For "T : Set", "P : T -> Prop", "ls : list T" (N long list "ls")
"listforall P ls" is the proposition "(P ls1) /\ (P ls2) /\ ... /\ (P lsN)". *)

Section listforall.

  Context  {T : Set}.
  Variable P : T -> Prop.

  Fixpoint listforall (ls : list T) : Prop :=
    match ls with
    | nil => True
    | cons h t => P h /\ listforall t
    end.

End listforall.


Lemma unfold_listforall :
  forall (T : Set) (P : T -> Prop) (t : T) (tl : list T),
    listforall P (cons t  tl) = (P t /\ listforall P tl).
Proof.
  auto.
Qed.


(* For sets "T" and "T'", function "F : T -> T'" and "ls : list T",
maplist T T' F ls *)

Section maplist.

  Context {T T' : Set}.
  Variable F : T -> T'.

  Fixpoint maplist (ls : list T) : list T' :=
    match ls with
    | nil => nil
    | cons h t => cons (F h) (maplist t)
    end.

End maplist.

Lemma unfold_maplist:
  forall (T T' : Set) (F : T -> T') (h : T) (ls : list T),
    maplist F (h :: ls) = (F h) :: (maplist F ls).
Proof.
  auto.
Qed.



(* About Naturals *)

Lemma n_minus_n :
  forall (n : nat),
    n - n = 0.
Proof.
  lia.
Qed.



(* "inb n m" is defined for "n" and "m" naturals,
and it gives "true" if "n=m" and gives "false" otherwise. "=?" is infix notation *)

(* "inb n ln" gives "true : bool" if "n" is in the list "ln", while gives "false : bool"
if "n" is not in "ln" *)
Fixpoint inb (n: nat) (ln: list nat) : bool :=
    match ln with
      | nil => false
      | n' :: ln' => eqb n n' || inb n ln'
    end.
(* "orb : bool -> bool -> bool" is the boolean or, with "||" infix notation *)

Lemma unfold_inb:
  forall n n' ln',
    inb n (n' :: ln') = orb (eqb n n') (inb n ln').
Proof.
  auto.
Qed.



(* "max n m" is defined for "n" and "m" naturals,
and is the maximum of the two. When they are equal, m is the output. *)

(* "listmax ln" is the maximum of the list of naturals.
When there are several instances of the maxial, it delivers the last. *)
Fixpoint listmax  (ln: list nat) : nat :=
    match ln with
      | nil => 0
      | n' :: ln' => max n' (listmax ln')
    end.


(* This proposition is useful in rewriting the right as the left. *)
Lemma unfold_listmax:
  forall n' ln',
    listmax (n' :: ln') = max n' (listmax ln').
Proof.
  auto.
Qed.



(* The first "length l1" number of elements of
"l1 ++ l2" is "l1" *)
Lemma firstn_app_exact :
  forall {A : Type} (l1 l2 : list A),
    @firstn A (length l1) (l1 ++ l2) = l1.
Proof.
  intros.
  rewrite firstn_app.
  rewrite n_minus_n.
  rewrite firstn_O.
  rewrite firstn_all.
  rewrite app_nil_r.
  reflexivity.
Qed.

(* The skipping "length l1" number of elements of
"l1 ++ l2" is "l2" *)
Lemma skipn_app_exact :
  forall {A : Type}  (l1 l2 : list A),
    @skipn A (length l1) (l1 ++ l2) = l2.
Proof.
  intros.
  rewrite skipn_app.
  rewrite n_minus_n.
  rewrite skipn_O.
  rewrite skipn_all.
  rewrite app_nil_l.
  reflexivity.
Qed.

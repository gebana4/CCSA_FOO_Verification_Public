
(************************************************************************)
(* Copyright (c) 2020, Gergei Bana                                      *)
(*                                                                      *)
(* This work is licensed under the MIT license. The license is          *)
(* described in the file "LICENSE" available at the root of the source  *)
(* or at https://opensource.org/licenses/MIT                            *)
(************************************************************************)


Require Export E_Freshness.



(**************************************************************************************)
(***************************** Classical Logic ************************)
(**************************************************************************************)



Axiom doubleneg_elim:
      (* "meta-level quantification" *) forall P : Prop,
      (* "premise:" *)      not (not P) ->
      (* "conclusion:" *)   P.



Proposition LEM  (*Law of Excluded Middle*):
      (* "meta-level quantification" *) forall P : Prop,
      (* "conclusion:" *)    P \/ (not P).
Proof. intros P.  apply doubleneg_elim. unfold not. intros.
assert  (not P).
  { unfold not. intros.
    assert (P \/ (not P)).
    { apply or_introl. assumption. }
    apply H in H1. assumption. }
assert (P \/ (not P)).
  { apply or_intror. assumption. }
apply H in H1. assumption.
Qed.



Axiom axiom_of_choice :
  forall (A B : Set) (R : A -> B -> Prop),
    (forall x : A, exists y : B, R x y) ->
    (exists f : A->B, forall x : A, R x (f x)).

Notation "'AC'" := axiom_of_choice.





(**************************************************************************************)
(**************************************************************************************)
(************************************ CORE  AXIOMS ************************************)
(**************************************************************************************)
(**************************************************************************************)



(**************************************************************************************)
(***************************** Axioms for Indistinguishability ************************)
(**************************************************************************************)



(* Here in "cind_len" we have to be careful that = is not in our languaGe. This is a constraint.
Our axiom schema is:
"For all lt1 and lt2 lists lists of terms, if they have different length, then lt1 ~ lt2 -> False"
For that reason we put the constraint part between (*"<<<"*)  (*">>>"*).
We write lt1 lt2 for two lists of terms not x y because it is not genuine FOL quantification
*)

Axiom cind_len :
    (*"<<<"*) forall {lt1 lt2 : list ppt}, length lt1 <> length lt2 -> (*">>>"*)
    not (lt1 ~ lt2).                                                              (* Lists with different lengths are distinguishable*)

Axiom cind_ref :
    forall {lx}, lx ~ lx.          (* Indistinguishability is reflexive*)

Axiom cind_sym :
    forall {lx ly}, lx ~ ly -> ly ~ lx.     (* Indistinguishability is symmetric*)

Axiom cind_trans :
    forall {lx ly lz}, lx ~ ly -> ly ~ lz -> lx ~ lz.   (* Indistinguishability is transitive *)

Axiom cind_funcapp :
    (*"<<<"*) forall {f : list ppt -> list ppt},   (*">>>"*)
          forall {lx ly} ,
          (*"<<<"*) (Context Adversarial List f ) ->  (*">>>"*)
     lx ~ ly -> (f lx) ~ (f ly).        (*
                                                        This axiom actually implies the restr
                                                        axiom because if we set f to be p. *)




Axiom FTDist :
     [TRue] ~ [FAlse] -> False.




(**************************************************************************************)
(******************************** Axioms for Equality  ****************************)
(**************************************************************************************)



Axiom ceq : forall  {x y} , [ (EQ [x ; y ]) ] ~ [ TRue ] <-> x = y.



(**************************************************************************************)
(******************************** Axioms for If_Then_Else_ ****************************)
(**************************************************************************************)



Axiom If_true :
    forall {x y} , (If TRue Then x Else y ) = x.

Axiom If_false :
  forall {x y} , ( If FAlse Then x Else y ) = y.


Axiom If_idemp :
  forall { b x1 y1 x2 y2 } ,
    (If b Then (If b Then x1 Else y1) Else (If b Then x2 Else y2)) = (If b Then x1 Else y2).



Axiom If_morph : forall {f} , forall  {b x y},
    ContextTerm General Term f ->
    (f (If b Then x Else y)) = (If b Then (f x) Else (f y)).




(* This should be derived from the other *)
Axiom IF_branch : forall {lz lz' x x' y y'} ,  forall {b b' : ppt} ,
      lz ++ b :: [x] ~ lz' ++ b' :: [x']
      -> lz ++ b :: [y] ~ lz' ++ b' :: [y']
      -> lz ++ b :: [(If b Then x Else y)] ~ lz' ++ b' :: [(If b' Then x' Else y')].

Axiom If_branch : forall {lz lz' lx lx' ly ly': list ppt} , forall {b b' : ppt} ,
      lz ++ [b] ++ lx ~ lz' ++ [b'] ++ lx' /\  lz ++ [b] ++ ly ~ lz' ++ [b'] ++ ly'
      -> lz ++ [b] ++ (IF b THEN lx ELSE ly) ~ lz' ++ [b'] ++ (IF b' THEN lx' ELSE ly').






(**************************************************************************************)
(************************************ Axioms for Nonces *******************************)
(**************************************************************************************)



Axiom FreshInd :
      (*"<<<"*)  forall nc1 nc2 lx ly,  Fresh nc1 lx  -> Fresh nc2 ly -> (*">>>"*)
              lx ~ ly -> (nc1 :: lx) ~ (nc2 :: ly).

Axiom FreshNEq :
      (*"<<<"*) forall nc x, FreshTerm nc x -> (*"<<<"*)
                [EQ [nc ; x]] ~ [FAlse].

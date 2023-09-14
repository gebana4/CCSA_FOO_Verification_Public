
(************************************************************************)
(* Copyright (c) 2021, Gergei Bana                                      *)
(*                                                                      *)
(* This work is licensed under the MIT license. The license is          *)
(* described in the file "LICENSE" available at the root of the source  *)
(* or at https://opensource.org/licenses/MIT                            *)
(* Special thanks to Qianli and Ajay K. Eeralla                         *)
(************************************************************************)

Require Export B_Symbols.


(**************************************************************************************)
(**************************************************************************************)
(************************************ SHALLOW EMBEDDING ********************************)
(**************************************************************************************)
(**************************************************************************************)


(* Here we carry out the shallow embedding, that is, we represent the syntax and semantics of
our logic in Coq. *)


(**************************************************************************************)
(***************************************** DOMAIN *************************************)
(**************************************************************************************)


(* We introduce the type "ppt" representing equivalence classes of 
PPT algorithms, where the equivalence is taken to be difference with at most negligible probability.
ppt is  our domain of interpretation.
Its interpretation [[ppt]] is the set of equivalence classes of PPT
algorithms with input 1^\eta where
eta is the security parameter. 
The equivalence classes are taken with respect to "#" where "a#b" means that the 
outputs of "a" and "b" as random variables can differ only by negligible probability.
ppt is the combination of the bool and message types of the paper 
We take it to be Parameter, otherwise we would need a new equality, causing numerous inconveniences *)

Parameter  ppt: Set.






(**************************************************************************************)
(************************** SHALLOW EMBEDDING OF FUNCTION SYMBOLS **************************)
(**************************************************************************************)


(* With the introduction of "ppt", Coq delivers for us the "list ppt" type, that is a representaton of
all finite lists of elements in "ppt". When we embed the above function symbols of "Symbols",
as function symbols of Coq, all of them are interpreted as of type "list ppt -> ppt".
This turns out to be less notation-heavy than
if we defined them on products. E.g. EQ is ppt x ppt -> ppt, but we represent it as list ppt -> ppt. However,
we will require that function symbols of arity "arg n" output default when the input list is shorter, and
drops the rest of the list when it is longer than "arg n".
Constants (nullary function symbols) are also embedded as elements in "ppt" and the obvious link is
established between the two embeddings *)


(* FOR THE COMPUTATIONAL SEMANTICS OF EACH FUNCTION SYMBOL AS PPT ALGORITHMS, IT MUST BE ENSURED THAT THEY
ALL USE DISJOINT SEGMENTS OF THE HONEST RANDOM TAPE *)




(* Here to each function symbol symbol in "Symbols", "FuncInt" assigns a function symbol of
type "list ppt -> ppt"*)

Parameter FuncInt :
  forall (hag : ComputationType) (arg : arity),
    Symbols hag arg -> list ppt -> ppt.

(* Here to each constant symbol symbol in "Symbols hag (narg 0)", "ConstInt" assigns a function symbol
of type "ppt"*)

Definition ConstInt (hag : ComputationType) (c : Symbols hag (narg 0)) : ppt :=
  FuncInt hag (narg 0) c [].


(* Function symbols output default if input length is less than arity *)

Axiom ArityMatchLess :
  forall (hag  : ComputationType) (n : nat) (f : Symbols hag (narg n)) (lx : list ppt),
    length lx  < n
    ->  FuncInt  hag (narg n) f lx  = (ConstInt Deterministic defaults).

(* Function symbols output only depends on the initial segment of the input list matching arity. *)

Axiom ArityMatchGreater :
  forall (hag  : ComputationType) (n : nat) (f : Symbols hag (narg n)) (lx ly : list ppt),
    length lx = n
    -> FuncInt hag (narg n) f (lx ++ ly) =  FuncInt hag (narg n) f lx.


(* We introduce the following notations for the above specific function symbols *)

Notation "'default'" := (ConstInt Deterministic  defaults).
Notation "'TRue'" := (ConstInt Deterministic  TRues).
Notation "'FAlse'" := (ConstInt Deterministic  FAlses).
Notation "'EQ'" := (FuncInt Deterministic (narg 2) EQs).
Notation "'If_Then_Else_'" := (FuncInt Deterministic (narg 3) ITEs).
Notation "'If' c1 'Then' c2 'Else' c3" := (FuncInt Deterministic (narg 3) ITEs [c1; c2; c3])
  (at level 55, right associativity).
Notation "'adv' n" := (FuncInt Adversarial arbarg (advs n)) (at level 0).
Notation "'nonce' n" :=  (ConstInt Honest (nonces n)) (at level 0).

Notation " c1 '≟' c2" := (EQ [c1; c2]) (at level 101, left associativity).

(* The semantics [[EQ]] is the PPT algorithm that on
interpretations [[x]], [[y]] of x and y assigns the PPT algorithm [[E(x,y)]]
that outputs true when the outputs of its inputs [[x]] and [[y]] are the
same and outputs false otherwise. *)



(* The semantics of  [[If_Then_Else_]] on input
PPT algorithms [[b]], [[x]], [[y]], it assigns the PPT algorithm
 [[If_Then_Else_(b,x,y)]] that outputs the output of [[x]] when
  the output of [[b]] is true; outputs the output of [[y]] when
the output of [[b]] is false; outputs an error otherwise *)







(* We need to be able to distinguish those functions of type "list ppt -> ppt" that come from
our syntax, and any general function of type "list ppt -> ppt" because many of our axioms only work
for those coming from our syntax. For this we use the metapredicate (not in our original language) "PPT"*)


(* "PPT" creates the ensembles within type list ppt -> ppt corresponding
to Honest, Deterministic, Adversarial and General function symbols. For example for
"f : list ppt -> ppt", the proposition "(PPT Adversarial) f" states that
f is an adversarial computation coming from our syntax. Note that our CCSA logic is very limited
and we do not have a domain for "list ppt -> ppt". On the other hand, we
can use the rich language of Coq to reason about such maps. Hence
"PPT Adversarial" is a "metapredicate", it is
a predicate in Coq, but it is not a predicate of our logic *)
(*deterministic PPT is also honest and adversarial, and honest and adversarial are also general, so after
embedding these are not disjoint any more. *)

(* "PPT" maybe be removable by redifining "Context" *)







(* It is probably unnecessary to make this inductive: *)


Inductive  PPT: ComputationType -> ((list ppt -> ppt) -> Prop) :=
| FunHAG :
      forall (hag : ComputationType) (arg : arity) (f : Symbols hag arg) ,
        (PPT hag) (FuncInt  hag arg f)
| DeterministicHonest :
      forall {lf : list ppt -> ppt} ,
        (PPT Deterministic) lf
         -> (PPT Honest) lf
| DeterministicAdversarial :
      forall {lf : list ppt -> ppt} ,
        (PPT Deterministic) lf
         -> (PPT Adversarial) lf
| HonestGeneral :
      forall {lf : list ppt -> ppt} ,
        (PPT Honest) lf
        -> (PPT General) lf
| AdversarialGeneral :
      forall {lf : list ppt -> ppt} ,
        (PPT Adversarial) lf
         -> (PPT General) lf.


(* That is, Deterinistic PPT are those that come from Deterministic symbols, 
Honest are those that come from either Honest or Deterministic symbols etc.*)


Axiom ConstantGeneral :
      forall {x0 :  ppt} ,
        (PPT General) (fun x => x0).

(* This axiom implies that for all elements x0 in ppt, (fun x => x0)  have a representation 
as  a FuncInt General 0 f *)




(**************************************************************************************)
(************************************** PREDICATE *************************************)
(**************************************************************************************)


(************************* Computational Indistinguishability *************************)



(* We have a single predicate symbol, computational indistinguishability *)
(* "x ~ y" means that the output distributions
of [[x]] and [[y]] are indistinguishable for all
PPT algorithms*)

Parameter cind : list ppt -> list ppt -> Prop.
Notation "x ~ y" := (cind x y) (at level 75, no associativity): type_scope.




(* The definitions of Syntax and Shallow Embedding end here *)


(**************************************************************************************)
(**************************************************************************************)
(**************************************************************************************)
(**************************************************************************************)
(**************************************************************************************)
(**************************************************************************************)
(**************************************************************************************)
(**************************************************************************************)
(**************************************************************************************)








(* Below there are some further notations and some propositions that follow from the above *)





(**************************************************************************************)
(**************************************************************************************)
(*********************************** ABBREVIATIONS ************************************)
(**************************************************************************************)
(**************************************************************************************)

(******************************* If Then Else on lists ********************************)



(*The following defines "IF b THEN x ELSE y " for x y lists.
Works on entry by entry:
E.g. IF b THEN [x1, x2] ELSE [y1, y2] =
[ If b Then x1 Else y1 , If b Then x2 Else y2 ] - Prove it
If x is shorter then y, then the rest of y simply does not appear in the result:
E.g. IF b THEN [x1, x2] ELSE [y1, y2, y3] =
[ If b Then x1 Else y1 , If b Then x2 Else y2 ] - Prove it
If x is longer than y the rest of x does not appear:
E.g. IF b THEN [x1, x2, x3] ELSE [y1, y2 ] =
[ If b Then x1 Else y1 , If b Then x2 Else y2 ] - Prove it
*)


(* "Better change this to inductive:" *)

Fixpoint IF_THEN_ELSE_ (b: ppt) (lx : list ppt) (lx' : list ppt) : list ppt :=
match lx with
| nil  => nil
| a :: m => match lx' with
            | nil => nil
            | a' :: m' => (If_Then_Else_ [b; a; a']) :: (IF_THEN_ELSE_ b m m')
            end
end.

Notation "'IF' c1 'THEN' c2 'ELSE' c3" := (IF_THEN_ELSE_ c1 c2 c3)
  (at level 200, right associativity).






(*******************************************************************************)
(*******************************************************************************)
(********************* Properties of our PPT functions *************************)
(*******************************************************************************)
(*******************************************************************************)


Proposition Const0Func :
  forall hag  c , (fun lx : list ppt => ConstInt hag c) = FuncInt hag (narg 0) c.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold ConstInt.
  assert (x = [ ] ++ x).
  auto. 
  rewrite H.
  rewrite ArityMatchGreater.
  reflexivity.
  auto.
Qed.



Proposition Func0Const :
forall (hag : ComputationType) (c :  Symbols hag (narg 0)) (lx : list ppt), ConstInt hag c = FuncInt hag (narg 0) c lx.
Proof.
  intros.
  rewrite <- (Const0Func hag c).
  auto.
Qed.


Proposition ConstHAG : forall hag hag' c , PPT hag (FuncInt hag' (narg 0) c) -> PPT hag (fun _ : list ppt => ConstInt hag' c).
Proof.
  intros.
  rewrite  (Const0Func hag' c).
  auto.
Qed.


Proposition nonceHonest :
      forall n , (PPT Honest) (fun lx : list ppt => nonce n).
Proof.
  intros.
  simpl (nonce n).
  rewrite Const0Func.
  apply FunHAG.
Qed.


Proposition advAdversarial :
      forall n , (PPT Adversarial) (adv n).
Proof.
  intros.
  simpl (adv n).
  apply FunHAG.
Qed.

(*******************************************************************************)
(*******************************************************************************)
(************************ Algorithms with bool output **************************)
(*******************************************************************************)
(*******************************************************************************)


(* We take bools to be a subset of ppt: *) 
Definition bppt (b : ppt) : Prop :=  (b = (If b Then TRue Else FAlse)). 


(* We declair that certain function symbols are used for bools : *) 
Axiom bool1001 : forall hag lx arg nl, bppt ((FuncInt hag arg (symbols hag arg (1 :: 0 :: 0 :: 1 :: nl) )) lx).

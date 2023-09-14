
(************************************************************************)
(* Copyright (c) 2021, Gergei Bana                                      *)
(*                                                                      *)
(* This work is licensed under the MIT license. The license is          *)
(* described in the file "LICENSE" available at the root of the source  *)
(* or at https://opensource.org/licenses/MIT                            *)
(* Special thanks to Qianli Zhang and Ajay K. Eeralla                   *)
(************************************************************************)

Require Export Coq.Init.Logic.
Require Export Coq.Init.Peano.
Require Export Coq.Arith.EqNat.
Require Export Setoid.
Require Export FunctionalExtensionality.
Require Export Coq.Bool.Bool.
Require Export A_Auxiliaries.




(* For now we set up our logic for shallow embedding *)


(**************************************************************************************)
(**************************************************************************************)
(********************* CCSA SYNTAX WITH SHALLOW EMBEDDING ****************************)
(**************************************************************************************)
(**************************************************************************************)





(**************************************************************************************)
(*************************** FUNCTION SYMBOLS IN GENERAL **************************)
(**************************************************************************************)





(* Our set of function symbols is "Symbols" this set is divided into 4 disjoint groups,
"Deterministic", "Honest", "Adversarial", and "General" symbols, which are further divied into
infinite number of subsets by "Arity". For each "n" natural number we have an arity "narg n"
where "narg" stands for number of arguments. Furthermore, we have a division "arbarg", which stands
for arbitrary arguments, meaning that we do no pre-specify the arity.
  - "Deterministic" function symbols represent computation that does not use randomness
  - "Honest" function symbols represent computation that uses honest randomness only
  - "Adversarial" function symbols represent computation that uses adversarial randomness only
  - "General" function symbols
 *)
Inductive ComputationType (* set *) : Set :=
| Deterministic  
| Honest
| Adversarial
| General.


(* "narg" assignes arity to any natural number whil "arbarg" means arbitrary (unspecified) number of arguments 
*)
Inductive arity : Set  :=
|narg : nat -> arity
|arbarg.

(* Our set of function symbols 
*)
Inductive Symbols (hag : ComputationType) (arg : arity) :  Set :=
| symbols  : list nat -> Symbols hag arg.   



(**************************************************************************************)
(*************************** PREDICATE SYMBOLS IN GENERAL **************************)
(**************************************************************************************)

(* Since we only have the indistinguishability predicate and we do not allow at this point
to add further predicate symbols, we do not need types for predicates similar to what we did for
function symbols. If that were to change, it should be done here. *)



(**************************************************************************************)
(*************************** SPECIFIC FUNCTION SYMBOLS **************************)
(**************************************************************************************)


(* Some specific function symbols *)

(* They could also be just parameters, at least so far we have not used that they are fixed  *)


(* Here the "s" at the end stands for symbol *)       

(* constants *)

(* Symbol for identically Error algorithm 
*)
Definition defaults : Symbols Deterministic (narg 0) :=
  symbols Deterministic (narg 0) [0].


(* Symbol for identically True algorithm
*)
Definition TRues : Symbols Deterministic (narg 0) :=
  symbols Deterministic (narg 0) [1; 0; 0 ; 1; 1].   


(* Symbol for identically False algorithm
*)
Definition FAlses : Symbols Deterministic (narg 0) :=
  symbols Deterministic (narg 0) [1; 0; 0 ; 1; 0].


  (* Non-zero arity function symbols for equality and tests*)




(* Symbol for the algorithm that outputs True when the outputs of the algorithms corresponding to two arguments are equal, False when not equal
*)
Definition EQs : Symbols Deterministic (narg 2) :=
  symbols Deterministic (narg 2) [1; 0; 0 ; 1; 0].


(* Symbol for the algorithm that outputs the output of the algorithm corresponding to the second argument when the output of the algorithm corresponding 
to the first arguments is True, outputs the output of the algorithm corresponding to the second argument otherwise.
*)
Definition ITEs : Symbols Deterministic (narg 3) :=
  symbols Deterministic (narg 3) [0].





(*Functions symbols for the adversary. These symbols have no pre-specified number of
arguments*)


Definition  advs (n: nat) : Symbols Adversarial arbarg :=
  symbols Adversarial arbarg [n].




(*************************************** RANDOM BLOCKS ***************************************)


(* nonces stand for disjoint random blocks of the honest tape, each with equal length *)

Definition nonces (n: nat) : Symbols Honest (narg 0) :=
  symbols Honest (narg 0) [n].


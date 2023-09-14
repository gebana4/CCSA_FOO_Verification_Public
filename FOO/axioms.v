(************************************************************************)
(* Copyright (c) 2022, Gergei Bana, Qianli Zhang                        *)
(*                                                                      *)
(* This work is licensed under the MIT license. The license is          *)
(* described in the file "LICENSE" available at the root of the source  *)
(* or at https://opensource.org/licenses/MIT                            *)
(*                                                                      *)
(* Special thanks to Dr. Eeralla                                        *)
(************************************************************************)


Require Import Coq.micromega.Lia.
Require Export ltacs.
Import ListNotations.


(* --------------------------------------------- *)
(*  phase identifiers are not the same *)

Axiom ph2Neqph3 : ph3 ≠ ph2.

Axiom  decenc :
      forall {m : ppt} {n n'},
        Dec [❴ m ❵_(Pkey [n]) ＾ (Rand [n']);  (Skey [n])] = m.

(*  *)
Axiom cca_2 : (CCA2 Len Enc Dec Pkey Skey Rand Error).



(* --------------------------------------------- *)
(*  *)
(* aka proposition 20 *)

Axiom CompHid : CompHid_prop Len Commitment Commitkey.

(*  *)
Axiom CompBind: CompBind_prop Commitment.


(* --------------------------------------------- *)

(*  *)
Axiom Blindness: Blindness_prop Blinding BlindRand Accept Unblinding ⫠.

(*  *)
Axiom UbNotUndefined: UbNotUndefined_prop Blinding BlindRand Accept Unblinding ⫠.




(* --------------------------------------------- *)
(*  *)
Axiom shufl_perm12: forall v1 v2 v3, shufl v1 v2 v3 = shufl v2 v1 v3.
Axiom shufl_perm13: forall v1 v2 v3, shufl v1 v2 v3 = shufl v3 v2 v1.
Axiom shufl_perm23: forall v1 v2 v3, shufl v1 v2 v3 = shufl v1 v3 v2.


(*  *)
Axiom KeyNEq: forall nc x : ppt, FreshTerm nc x -> [Comk (nc) ≟ x] ~ [FAlse].
(* Is this not derivable? *)



(*   *)
Axiom ComplLen: forall t, | compl t | = | t |.


(* Assumptions on length preservation *)

Axiom voteLen : (| vot0 |) = (| vot1 |).

Axiom NonceLen : forall n m , (| nonce n |) = (| nonce m |).

Axiom ComkLen :  forall n m , (| Comk (nonce n) |) = (| Comk (nonce m) |).
Axiom BrandLen :  forall n m , (| Brand (nonce n) |) = (| Brand (nonce m) |).




Axiom ubLen :
  forall x y n m t t1 t2 , (| x |) = (| y |)
                           -> Fresh (nonce n) [t; x]
                           -> Fresh (nonce m) [t; y]                                                 
                           -> UbNUDContextTerm (nonce n) Blinding BlindRand t1
                           -> UbNUDContextTerm (nonce m) Blinding BlindRand t2
                           -> (| If (acc x t (Brand (nonce n)) t1) & (acc y t (Brand (nonce m)) t2) Then (ub x t (Brand (nonce n)) t1) Else ⫠ |)
                            = (| If (acc x t (Brand (nonce n)) t1) & (acc y t (Brand (nonce m)) t2) Then (ub y t (Brand (nonce m)) t2) Else ⫠ |).



Axiom comLen :
  forall x y n m , (| x |) = (| y |)
                   -> FreshTerm (nonce n) x
                   -> FreshTerm (nonce n) y
                   -> FreshTerm (nonce m) x                                
                   -> FreshTerm (nonce m) y
                   -> (| com x (Comk (nonce n)) |) =  (| com y (Comk (nonce m)) |).



Axiom PairLen :
    forall (x x' y y': ppt) , (| x |) = (| x' |) ->  (| y |) = (| y' |) ->  (| Pair [x ; y ] |) = (| Pair [x' ; y' ] |).


Axiom TripleLen :
    forall (x x' y y' z z': ppt) , (| x |) = (| x' |) ->  (| y |) = (| y' |) ->  (| Triple [x ; y ; z] |) = (| Triple [x' ; y' ; z' ] |).

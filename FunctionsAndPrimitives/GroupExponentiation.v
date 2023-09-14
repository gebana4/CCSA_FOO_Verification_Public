
(************************************************************************)
(* Copyright (c) 2020, Gergei Bana                                      *)
(*                                                                      *)
(* This work is licensed under the MIT license. The license is          *)
(* described in the file "LICENSE" available at the root of the source  *)
(* or at https://opensource.org/licenses/MIT                            *)
(************************************************************************)


Require Import Core.



(* Domains should be treated properly later*)

(**************************************************************************************)
(**************************************************************************************)
(********************************* Commutative Groups *********************************)
(**************************************************************************************)
(**************************************************************************************)







(* Group multiplication *)


Parameter gms : Symbols Deterministic (narg 2).

Notation "'gm'" := (FuncInt Deterministic (narg 2) gms).


Notation " g '**' g' " := (gm [ g ; g' ])
                         (at level 52, right associativity).

(* We assume that g includes the information which G group. If there is a mismatch, 
the multiplication defaults. *)


(* Commutativity *)

Axiom  gmcomm :
      forall {g g' : ppt} ,
         g ** g' =   g' ** g.


(* Associativity *)
Axiom  gmass :
      forall {g g' g'' : ppt} ,
       g ** (g' ** g'') = ( g ** g') ** g''.



(*
(* Identity element *)
Parameter gids : Symbols Deterministic (narg 0).

Notation "'gid'" := (ConstInt Deterministic gids).


(* Multiplication with identity *)
Axiom  gmidentr :
      forall {g : ppt} ,
        g ** gid = g.

Axiom  gmidentl :
      forall {g : ppt} ,
        gid ** g = g.


(* Inverse *)
Parameter ginvs : Symbols Deterministic (narg 1).

Notation "'ginv'" := (FuncInt Deterministic (narg 1) ginvs).



(* Multiplication with inverse *)
 Axiom  gminvr :
      forall {g : ppt} ,
        g ** (ginv [g]) = gid.

Axiom  gminvl :
      forall {g : ppt} ,
       (ginv [g]) ** g = gid.
*)


(**************************************************************************************)
(**************************************************************************************)
(********************************* Commutative Rings **********************************)
(**************************************************************************************)
(**************************************************************************************)




(* Ring multiplication *)

Parameter rms : Symbols Deterministic (narg 2).

Notation "'rm'" := (FuncInt Deterministic (narg 2) rms).




Notation "a '^*^' b" := (rm [ a ; b ])
                         (at level 36, left associativity).


(* Commutativity *)

Axiom  rmcomm :
      forall {a b : ppt} ,
        a ^*^ b = b ^*^ a.


(* Associativity *)
Axiom  rmass :
      forall {a b c: ppt} ,
        a ^*^ (b ^*^ c) = (a ^*^ b) ^*^ c.


(*(* Identity element *)
Parameter rids : Symbols.

Notation "'rid'" := (ConstantSymbol Deterministic rids).


(* Multiplication with identity *)
Axiom  rmidentr :
      forall {a : ppt} ,
        a ^*^ rid = a .

Axiom  rmidentl :
      forall {a : ppt} ,
        rid ^*^ a = a.
*)


(* Ring addition *)

Parameter ras : Symbols Deterministic (narg 2).

Notation "'ra'" := (FuncInt Deterministic (narg 2) ras).



Notation "a '^+^' b" := (ra [ a ; b ])
                         (at level 37, left associativity).


(* Commutativity *)

Axiom  racomm :
      forall {a b : ppt} ,
        a ^+^ b = b ^+^ a.


(* Associativity *)
Axiom  raass :
      forall {a b c: ppt} ,
        a ^+^ (b ^+^ c) = (a ^+^ b) ^+^ c.


(*
(* Zero element *)
Parameter rzeros : Symbols.

Notation "'rzero'" := (ConstantSymbol Deterministic rzeros).


(* Addition with zero *)
Axiom  razeror :
      forall {a : ppt} ,
        a ^+^ rzero = a .

Axiom  razerol :
      forall {a : ppt} ,
        rzero ^*^ a = a.

(* Inverse *)
Parameter rnegs : Symbols.

Notation "'rneg'" := (FunctionSymbol Deterministic rnegs).



(* Multiplication with inverse *)
 Axiom  rainvl :
      forall {a : ppt} ,
        (rneg [a]) ** a = rzero.


Axiom  rainvr :
      forall {a : ppt} ,
        a ^+^ (rneg [a]) = rzero.
*)


(* Distributivity *)
 Axiom  rdists :
      forall {a b c : ppt} ,
        a ^*^ (b ^+^ c) = (a ^*^ b) ^+^ (a ^*^ c).





(**************************************************************************************)
(**************************************************************************************)
(********************************** Exponentiation ************************************)
(**************************************************************************************)
(**************************************************************************************)


Parameter exps : Symbols Deterministic (narg 2).

Notation "'exp'" := (FuncInt Deterministic (narg 2) exps).



Notation "g '^^' r" := (exp [ g ; r ])
                         (at level 38, left associativity).


Axiom  expa :
      forall {g a b : ppt} ,
        (g ^^ a)  **  (g ^^ b )   =    g ^^ (b ^+^ a).


Axiom  expm :
      forall {g a b : ppt} ,
        (g ^^ a) ^^ b    =    g ^^ (b ^+^ a).


(*
Axiom  expi :
      forall {g a : ppt} ,
        ginv [g ^^ a]    =    g ^^ (rneg [a]).

*)


Lemma bla35: forall x y  u w , x=u -> y=w -> [exp [x;y]; x] = [exp [u;w]; x].
Proof. intros.  rewrite H. rewrite H0.  reflexivity. Qed.

Proposition   expcomm :
      forall {g a b : ppt} ,
        g ^^ a ^^ b  = g ^^ b ^^ a.
Proof. intros. rewrite (@expm g a b). rewrite  (@expm g b a).
rewrite racomm. reflexivity. Qed.

(*Proposition   expid :
      forall {g a b c: ppt} ,
        g ^^ rzero  = gid.
Proof. intros. rewrite <- (@rainvr rzero).  rewrite <- expa.
 rewrite <- (@expi g rzero). rewrite  gmcomm.  apply gminvr.
 Qed.*)



(*Axiom  expcomm :
      forall {g a b : ppt} ,
        (g ^^ a ^^ b) = (g ^^ b ^^ a).*)





(**************************************************************************************)
(**************************************************************************************)
(**************************** Randomized Exponentiation *******************************)
(**************************************************************************************)
(**************************************************************************************)



Parameter ggens : Symbols Deterministic (narg 1).


Notation "'ggen'" := (FuncInt Deterministic (narg 1) ggens).

Definition g (n : nat) : ppt := ggen [nonce n].







Axiom ggenUniform :
      forall {x : ppt} {n : nat} ,
        FreshTerm (nonce n) x
        ->  [ggen [nonce n]] ~ [x ** (ggen [nonce n])].







Parameter Rings : Symbols Deterministic (narg 1).


Notation "'Ring'" := (FuncInt Deterministic (narg 1) Rings).

Definition R (n : nat) : ppt := Ring [nonce n].





Axiom RingUniform :
      forall {x : ppt} {n : nat} ,
        FreshTerm (nonce n) x
        ->  [Ring [nonce n]] ~ [x ^+^ (Ring [nonce n])].


Axiom ggenRingUniform :
      forall {x : ppt} {n n': nat} nl , NonceList nl ->
        FreshTerm (nonce n) x -> Fresh (nonce n)  ((nonce n') :: nl )
        ->  nonce n':: ggen [nonce n']^^ Ring [nonce n] :: nl  ~ nonce n':: x ** (ggen [nonce n'])^^ Ring [nonce n] :: nl.





Goal forall n n' n'',
      n <> n'
      -> n <> n''
      -> FreshTerm (nonce n)  ((g n') ^^ (R n'')).
  intros. ProveFresh. Qed.


Definition DDH (gg rr: list ppt -> ppt) : Prop :=
forall (n1 n2 n3 n4 : nat) , n1 <> n2 -> n1 <> n3 -> n1 <> n4 -> n2 <> n3 -> n2 <> n4 -> n3 <> n4 ->
        [(gg [nonce n1]) ; (gg [nonce n1])^^(rr [nonce n2]) ; (gg [nonce n1])^^(rr [nonce n3]) ; (gg [nonce n1])^^(rr [nonce n2])^^(rr [nonce n3])]
       ~
        [(gg [nonce n1]) ; (gg [nonce n1])^^(rr [nonce n2]) ; (gg [nonce n1])^^(rr [nonce n3]) ; (gg [nonce n1])^^(rr [nonce n4])].


(*Axiom DDH :  forall {n n1 n2 n3 : nat} , n <> n1 -> n <> n2 -> n <> n3 -> n1 <> n2 -> n1 <> n3 -> n2 <> n3 ->
        [(g n) ; (g n)^^(R n1) ; (g n)^^(R n2) ; (g n)^^(R n1)^^(R n2)]
       ~
        [(g n) ; (g n)^^(R n1) ; (g n)^^(R n2) ; (g n)^^(R n3)].*)

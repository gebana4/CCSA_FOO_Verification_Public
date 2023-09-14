(************************************************************************)
(* Copyright (c) 2022, Gergei Bana, Rohit Chadha, Ajay Kumar Eeralla,   *)
(* Qianli Zhang                                                         *)
(*                                                                      *)
(* This work is licensed under the MIT license. The license is          *)
(* described in the file "LICENSE" available at the root of the source  *)
(* or at https://opensource.org/licenses/MIT                            *)
(************************************************************************)


Require Import Coq.micromega.Lia.
Require Export auxiliary2.
(* Require Export contexts. *)
Import ListNotations.


(*  *)

(* Prop11 claims that, the adversary cannot extract the commitment key from a commitment if his computational power is limited.
 Note that x ≠ y is a notation for EQ(x, y) = false. Note also that
 the lhs and rhs of Comk (nonce n)) ≠ (t1 ((com t (Comk (nonce n)))) are reversed in the paper.
*)

Proposition prop11 : forall {t1 : ppt -> ppt} {t : ppt} {n : nat},
                FreshTerm  (nonce n) t ->
                FreshTermcTerm (nonce n) t1 ->
   (Comk (nonce n)) ≠ (t1 ((com t (Comk (nonce n))))).
Proof.
  intros t1 t n H3 H4.
  assert (exists n', n' <> n /\ FreshTerm  (nonce n') t /\  FreshTermcTerm (nonce n') t1).
    apply FreshFreshcNewFresh; auto.
  destruct H as [n' [neq [fresnn' freshtn']]].
  pose (kc := (Comk nonce (n))).
  pose (kc' := (Comk nonce (n'))).
  fold kc kc'.

  
(* we can substitute the variable x with either (t) or (compl t) in (com x kc ≟ com t (t1 (com x kc))) on different sides of the indistinguishable equivalence,
   thanks to the CompHid property of a commitment scheme *)
  
  pose (CompHidEx (fun lx => [t ; compl t; Nth 0 lx] ++ [t1 (Nth 0 lx)]) t (compl t) n n') as c;
    fold kc kc' in c.
  apply (@cind_funcapp (fun x => [EQ [Nth 2 x ; com (Nth 0 x)  (Nth 3 x)]])) in c.
  unfold Nth in c; simpl in c.

  
(* Since (compl t) ≠ (t), we can reduce expression (com (compl t) kc ≟ com t (t1 (com (compl t) kc))) to FAlse,
   thanks to the CompBind property of a commitment scheme *)
  
  rewrite <- (CompBind (compl t) (t) kc (t1 (com (compl t) kc))) in c.
  rewrite (ComplNeq t) in c.
  rewrite If_same in c.
  apply FalseEq in c.


(* Using NeqIdem, we can infer that (kc ≠ t1 (com t kc)) from (com t kc ≠ com t (t1 (com t kc))) *)
  
  apply (NeqIdem (fun x => com t x) kc (t1 (com t kc))); auto.
  ProveContext.

(*   *)
  apply Fresh2Freshc in H3.
  apply Fresh2Freshc in fresnn'.
  all : ProveContext.
  rewrite ComplLen.
  reflexivity.
  lia.
  ProveFresh.
  simpl. apply Fresh2Freshc in H3. ProveFreshC_prop11. apply (frfrtcCont (nonce n) (fun lx => Nth 0 lx) t1); auto. ProveFreshC_prop11.
  ProveFresh.
  simpl. apply Fresh2Freshc in fresnn'. ProveFreshC_prop11. apply (frfrtcCont (nonce n') (fun lx => Nth 0 lx) t1); auto. ProveFreshC_prop11.
Qed.

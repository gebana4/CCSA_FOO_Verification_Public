(************************************************************************)
(* Copyright (c) 2022, Gergei Bana, Qianli Zhang                        *)
(*                                                                      *)
(* This work is licensed under the MIT license. The license is          *)
(* described in the file "LICENSE" available at the root of the source  *)
(* or at https://opensource.org/licenses/MIT                            *)
(************************************************************************)

Require Import Coq.micromega.Lia.
Require Export prop11.
(* Require Export auxiliary2. *)
Import ListNotations.



(***************************************************************************************************)
(***************************************************************************************************)
(****************************          Lemma_25.v        *******************************************)
(***************************************************************************************************)
(***************************************************************************************************)


(*----------------------------------------      game1n                         --------------------------------------*)



Lemma lemma25_game1n_ContextfFΦ2b3: forall side n m0,  ContextTerm General Term (fun _ => m0) ->
    ContextTerm General Term
    (fun b3 : ppt => (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n))).
Proof.
  intros. destruct side; simpl; ProveContext.
Qed.


Lemma lemma25_game1n_ContextfFΦ3b3: forall side n m0,  ContextTerm General Term (fun _ => m0) ->
    ContextTerm General Term
    (fun b3 : ppt => (fFΦ3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) (decS (τ1 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n))))
               (decS (τ2 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n))))
               (If b3 Then m0 Else If b3 Then Error Else decS (τ3 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n)))))).
Proof.
  intros.
  pose (lemma25_game1n_ContextfFΦ2b3 side n m0 H).
  time (destruct side; simpl; ProveContext). (* (*3.224 secs*)*)
Qed.


Lemma lemma25_game1n_ContextfFΦ5b3: forall side n m0,  ContextTerm General Term (fun _ => m0) ->
    ContextTerm General Term
    (fun b3 : ppt => (fFΦ5 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) (decS (τ1 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n))))
                        (decS (τ2 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n))))
                        (If b3 Then m0 Else If b3 Then Error Else decS (τ3 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n)))))).
Proof.
  intros.
  pose (lemma25_game1n_ContextfFΦ2b3 side n m0 H).
  pose (lemma25_game1n_ContextfFΦ3b3 side n m0 H).
 time (destruct side; simpl; ProveContext). (*2.916 secs*)
Qed.


Lemma lemma25_game1n_ContextfFΦ3b2: forall side n m0,  ContextTerm General Term (fun _ => m0) ->
    ContextTerm General Term
    (fun b2 : ppt => (fFΦ3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) (decS (τ1 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n))))
               (If b2 Then m0 Else If b2 Then Error Else decS (τ2 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n)))) (Fiv3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) m0))).
Proof.
  intros.
  pose (lemma25_game1n_ContextfFΦ2b3 side n m0 H).
  time (destruct side; simpl; ProveContext). (* 1.841 secs*)
Qed.

Lemma lemma25_game1n_ContextfFΦ5b2: forall side n m0,  ContextTerm General Term (fun _ => m0) ->
    ContextTerm General Term
    (fun b2 : ppt => (fFΦ5 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) (decS (τ1 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n))))
                              (If b2 Then m0 Else If b2 Then Error Else decS (τ2 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n))))
                              (Fiv3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) m0))).
Proof.
  intros.
  pose (lemma25_game1n_ContextfFΦ2b3 side n m0 H).
  pose (lemma25_game1n_ContextfFΦ3b2 side n m0 H).
time (destruct side; simpl; ProveContext). (*3.742 secs *)
Qed.

Lemma lemma25_game1n_ContextfFΦ3b1: forall side n m0,  ContextTerm General Term (fun _ => m0) ->
    ContextTerm General Term
    (fun b1 : ppt => (fFΦ3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) (If b1 Then m0 Else If b1 Then Error Else decS (τ1 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n))))
               (Fiv2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) m0) (Fiv3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) m0))).
Proof.
  intros.
  pose (lemma25_game1n_ContextfFΦ2b3 side n m0 H).
  time (destruct side; simpl; ProveContext). (* 2.933 secs*)
Qed.

Lemma lemma25_game1n_ContextfFΦ5b1: forall side n m0,  ContextTerm General Term (fun _ => m0) ->
    ContextTerm General Term
    (fun b1 : ppt => (fFΦ5 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n)
                                   (If b1 Then m0 Else If b1 Then Error Else decS (τ1 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n))))
                                   (Fiv2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) m0) (Fiv3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) m0))).
Proof.
  intros.
  pose (lemma25_game1n_ContextfFΦ2b3 side n m0 H).
  pose (lemma25_game1n_ContextfFΦ3b1 side n m0 H).
  time (destruct side; simpl; ProveContext). (*4.888 secs *)
Qed.

Lemma lemma25_game1n_context1: forall side n m0,  ContextTerm General Term (fun _ => m0) ->
    ContextTerm General Term
    (fun b3 : ppt =>
     ＜ ＜ e0 (c0 side) (c1 side) n, e1 (c0 side) (c1 side) n1,
       dv (decS (τ1 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n)))) (decS (τ2 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n))))
         (If b3 Then m0 Else If b3 Then Error Else decS (τ3 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n))))
         (s (decS (τ1 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n)))) (decS (τ2 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n))))
            (If b3 Then m0 Else If b3 Then Error Else decS (τ3 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n)))) ) ＞,
     ＜ Fl0 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) (decS (τ1 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n))))
         (decS (τ2 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n)))) (If b3 Then m0 Else If b3 Then Error Else decS (τ3 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n)))),
     Fl1 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) (decS (τ1 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n))))
       (decS (τ2 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n)))) (If b3 Then m0 Else If b3 Then Error Else decS (τ3 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n)))),
     Fido (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) (decS (τ1 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n))))
       (decS (τ2 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n)))) (If b3 Then m0 Else If b3 Then Error Else decS (τ3 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n)))) n0 ＞
       ＞).
Proof.
  intros.
  pose (lemma25_game1n_ContextfFΦ2b3 side n m0 H).
  pose (lemma25_game1n_ContextfFΦ3b3 side n m0 H).
  pose (lemma25_game1n_ContextfFΦ5b3 side n m0 H).
  time (destruct side; simpl;  ProveContext).  (*18.171 secs*)
Qed.




Lemma lemma25_game1n_context2: forall side n m0,  ContextTerm General Term (fun _ => m0) ->
  ContextTerm General Term (fun b2 : ppt =>
    If τ3 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n)) ≟ e0 (c0 side) (c1 side) n Then ⫠
    Else (＜ ＜ e0 (c0 side) (c1 side) n, e1 (c0 side) (c1 side) n1,
            dv (decS (τ1 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n))))
              (If b2 Then m0 Else If b2 Then Error Else decS (τ2 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n)))) (Fiv3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) m0)
              (s (decS (τ1 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n))))
                 (If b2 Then m0 Else If b2 Then Error Else decS (τ2 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n)))) (Fiv3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) m0) ) ＞,
          ＜ Fl0 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) (decS (τ1 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n))))
              (If b2 Then m0 Else If b2 Then Error Else decS (τ2 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n)))) (Fiv3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) m0),
          Fl1 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) (decS (τ1 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n))))
            (If b2 Then m0 Else If b2 Then Error Else decS (τ2 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n)))) (Fiv3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) m0),
          Fido (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) (decS (τ1 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n))))
            (If b2 Then m0 Else If b2 Then Error Else decS (τ2 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n)))) (Fiv3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) m0) n0 ＞ ＞)).
Proof.
  intros.
  unfold Fido. unfold Fio1.
  pose (lemma25_game1n_ContextfFΦ2b3 side n m0 H).
  pose (lemma25_game1n_ContextfFΦ3b2 side n m0 H).
  pose (lemma25_game1n_ContextfFΦ5b2 side n m0 H).
time (destruct side; simpl;  ProveContext).  (*20.023 secs *)
Qed.




Lemma lemma25_game1n_context3: forall side n m0,  ContextTerm General Term (fun _ => m0) ->
ContextTerm General Term
   (fun b1 : ppt =>
    If τ2 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n)) ≟ e0 (c0 side) (c1 side) n Then ⫠
    Else If τ3 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n)) ≟ e0 (c0 side) (c1 side) n Then ⫠
         Else (＜ ＜ e0 (c0 side) (c1 side) n, e1 (c0 side) (c1 side) n1,
                 dv (If b1 Then m0 Else If b1 Then Error Else decS (τ1 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n)))) (Fiv2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) m0)
                   (Fiv3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) m0)
                   (s (If b1 Then m0 Else If b1 Then Error Else decS (τ1 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n))))
                      (Fiv2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) m0) (Fiv3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) m0) ) ＞,
               ＜ Fl0 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) (If b1 Then m0 Else If b1 Then Error Else decS (τ1 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n))))
                   (Fiv2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) m0) (Fiv3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) m0),
               Fl1 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) (If b1 Then m0 Else If b1 Then Error Else decS (τ1 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n))))
                 (Fiv2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) m0) (Fiv3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) m0),
               Fido (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) (If b1 Then m0 Else If b1 Then Error Else decS (τ1 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n))))
                 (Fiv2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) m0) (Fiv3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) m0) n0 ＞ ＞)).
Proof.
 intros.
  pose (lemma25_game1n_ContextfFΦ2b3 side n m0 H).
  pose (lemma25_game1n_ContextfFΦ3b1 side n m0 H).
  pose (lemma25_game1n_ContextfFΦ5b1 side n m0 H).
time (destruct side; simpl;  ProveContext).  (*15.23 secs*)
Qed.





(*----------------------------------------      game2n       ---------------------------------------------*)



Lemma lemma25_game2n_fFΦ3 : forall side n, ContextTerm General Term
    (fun _ : ppt =>
  (fFΦ3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) (Fv1 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n)) (Fv2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n))
               (Fv3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n)))).
Proof.
  intros.
  time (destruct side; simpl;  ProveContext).  (*4.02 secs*)
Qed.

Lemma lemma25_game2n_fFΦ5 : forall side n, ContextTerm General Term
    (fun _ : ppt => (fFΦ5 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n) (Fv1 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n)) (Fv2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n))
                       (Fv3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n)))).
Proof.
  intros.
  pose (lemma25_game2n_fFΦ3 side n).
  time (destruct side; simpl;  ProveContext).  (**)
Qed.



(*----------------------------------------   Using CCA2 to substitute n0 to n0'       ---------------------------------------------*)
(**)







Lemma lemma25_CCA2_n0_n0'_AfterΦ3: forall side,
 CCA2AfterEncTerm Dec Pkey Skey Error [nonce (6)] [nonce (7)]
   (fun x0 : ppt => (fFΦ3 (c0 side) (c1 side) x0 (Fiv1 (c0 side) (c1 side) x0 (m0 (c0 side) (c1 side) n0)) (Fiv2 (c0 side) (c1 side) x0 (m0 (c0 side) (c1 side) n0))
                       (Fiv3 (c0 side) (c1 side) x0 (m0 (c0 side) (c1 side) n0)))).
Proof.
  intros.
  time (destruct side; ProveCca2After). (* 11.028 secs  *)
Qed.



Lemma lemma25_CCA2_n0_n0'_AfterΦ5 : forall side,
 CCA2AfterEncTerm Dec Pkey Skey Error [nonce (6)] [nonce (7)]
   (fun x0 : ppt => (fFΦ5 (c0 side) (c1 side) x0 (Fiv1 (c0 side) (c1 side) x0 (m0 (c0 side) (c1 side) n0)) (Fiv2 (c0 side) (c1 side) x0 (m0 (c0 side) (c1 side) n0))
                       (Fiv3 (c0 side) (c1 side) x0 (m0 (c0 side) (c1 side) n0)))).
Proof.
  intros.
  pose (lemma25_CCA2_n0_n0'_AfterΦ3 side).
  time (destruct side; ProveCca2After). (*13.625 secs*)
Qed.



Lemma lemma25_CCA2_n0_n0'_AfterCnxt : forall side,
 CCA2AfterEnc Dec Pkey Skey Error [nonce (6)] [nonce (7)]
    (fun x0 : ppt =>
     [b0 (c0 side); b1 (c1 side);
     If acc0 (c0 side) (c1 side) & acc1 (c0 side) (c1 side)
     Then If (τ1 (fFΦ2 (c0 side) (c1 side) x0) ≟ x0) or (τ2 (fFΦ2 (c0 side) (c1 side) x0) ≟ x0) or (τ3 (fFΦ2 (c0 side) (c1 side) x0) ≟ x0) Then ⫠
          Else ＜ ＜ x0, e1 (c0 side) (c1 side) n1,
                 dv (Fiv1 (c0 side) (c1 side) x0 (m0 (c0 side) (c1 side) n0)) (Fiv2 (c0 side) (c1 side) x0 (m0 (c0 side) (c1 side) n0))
                   (Fiv3 (c0 side) (c1 side) x0 (m0 (c0 side) (c1 side) n0))
                   (s (Fiv1 (c0 side) (c1 side) x0 (m0 (c0 side) (c1 side) n0)) (Fiv2 (c0 side) (c1 side) x0 (m0 (c0 side) (c1 side) n0))
                      (Fiv3 (c0 side) (c1 side) x0 (m0 (c0 side) (c1 side) n0)) ) ＞,
               ＜ Fl0 (c0 side) (c1 side) x0 (Fiv1 (c0 side) (c1 side) x0 (m0 (c0 side) (c1 side) n0)) (Fiv2 (c0 side) (c1 side) x0 (m0 (c0 side) (c1 side) n0))
                   (Fiv3 (c0 side) (c1 side) x0 (m0 (c0 side) (c1 side) n0)),
               Fl1 (c0 side) (c1 side) x0 (Fiv1 (c0 side) (c1 side) x0 (m0 (c0 side) (c1 side) n0)) (Fiv2 (c0 side) (c1 side) x0 (m0 (c0 side) (c1 side) n0))
                 (Fiv3 (c0 side) (c1 side) x0 (m0 (c0 side) (c1 side) n0)),
               Fido (c0 side) (c1 side) x0 (Fiv1 (c0 side) (c1 side) x0 (m0 (c0 side) (c1 side) n0)) (Fiv2 (c0 side) (c1 side) x0 (m0 (c0 side) (c1 side) n0))
                 (Fiv3 (c0 side) (c1 side) x0 (m0 (c0 side) (c1 side) n0)) n0 ＞ ＞ Else ⫠]).
Proof.
  intros.
  pose (lemma25_CCA2_n0_n0'_AfterΦ3 side).
  pose (lemma25_CCA2_n0_n0'_AfterΦ5 side).
  time (destruct side; ProveCca2After). (**)
Qed.






(*----------------------------------------   neutralize encryption from voter1 in the opening phase       ---------------------------------------------*)

Lemma lemma25_ininkc0_false_Φ3: forall side,
  FreshTermcTerm nonce (0) (fun x : ppt =>
    (fFΦ3 x (c1 side) (e0 x (c1 side) n0') (Fv1 x (c1 side) (e0 x (c1 side) n0'))
                            (Fv2 x (c1 side) (e0 x (c1 side) n0')) (Fv3 x (c1 side) (e0 x (c1 side) n0')))).
Proof.
  intros. destruct side; simpl; ProveFreshCTerm.
Qed.

Lemma lemma25_ininkc0_false_FreshC_τ1: forall side,
    FreshTermcTerm nonce (0)
    (fun x : ppt =>
     π2 (π1 decS
              (τ1
                 (f5
                    [b0 x; b1 (c1 side); e0 x (c1 side) n0'; e1 x (c1 side) n1;
                    dv (Fv1 x (c1 side) (e0 x (c1 side) n0')) (Fv2 x (c1 side) (e0 x (c1 side) n0'))
                      (Fv3 x (c1 side) (e0 x (c1 side) n0'))
                      (s (Fv1 x (c1 side) (e0 x (c1 side) n0')) (Fv2 x (c1 side) (e0 x (c1 side) n0') )
                         (Fv3 x (c1 side) (e0 x (c1 side) n0')) ); ⫠;
                    Fl1 x (c1 side) (e0 x (c1 side) n0') (Fv1 x (c1 side) (e0 x (c1 side) n0'))
                    (Fv2 x (c1 side) (e0 x (c1 side) n0')) (Fv3 x (c1 side) (e0 x (c1 side) n0'))])))).
Proof.
  intros.
  pose (lemma25_ininkc0_false_Φ3 side).
  time (destruct side; simpl; ProveFreshCTerm).  (* 3.885 secs *)
Qed.


Lemma lemma25_ininkc0_false_FreshC_τ2: forall side,
    FreshTermcTerm nonce (0)
    (fun x :  ppt =>
     π2 (π1 decS
              (τ2
                 (f5
                    [b0 x; b1 (c1 side); e0 x (c1 side) n0'; e1 x (c1 side) n1;
                    dv (Fv1 x (c1 side) (e0 x (c1 side) n0')) (Fv2 x (c1 side) (e0 x (c1 side) n0'))
                      (Fv3 x (c1 side) (e0 x (c1 side) n0'))
                      (s (Fv1 x (c1 side) (e0 x (c1 side) n0')) (Fv2 x (c1 side) (e0 x (c1 side) n0'))
                         (Fv3 x (c1 side) (e0 x (c1 side) n0')) ); ⫠;
                    Fl1 x (c1 side) (e0 x (c1 side) n0') (Fv1 x (c1 side) (e0 x (c1 side) n0'))
                    (Fv2 x (c1 side) (e0 x (c1 side) n0')) (Fv3 x (c1 side) (e0 x (c1 side) n0'))])))).
Proof.
  intros.
  pose (lemma25_ininkc0_false_Φ3 side).
  time (destruct side; simpl; ProveFreshCTerm).  (* 3.885 secs *)
Qed.


Lemma lemma25_ininkc0_false_FreshC_τ3: forall side,
    FreshTermcTerm nonce (0)
    (fun x : ppt =>
     π2 (π1 decS
              (τ3
                 (f5
                    [b0 x; b1 (c1 side); e0 x (c1 side) n0'; e1 x (c1 side) n1;
                    dv (Fv1 x (c1 side) (e0 x (c1 side) n0')) (Fv2 x (c1 side) (e0 x (c1 side) n0'))
                      (Fv3 x (c1 side) (e0 x (c1 side) n0'))
                      (s (Fv1 x (c1 side) (e0 x (c1 side) n0')) (Fv2 x (c1 side) (e0 x (c1 side) n0'))
                         (Fv3 x (c1 side) (e0 x (c1 side) n0')) ); ⫠;
                    Fl1 x (c1 side) (e0 x (c1 side) n0') (Fv1 x (c1 side) (e0 x (c1 side) n0'))
                    (Fv2 x (c1 side) (e0 x (c1 side) n0')) (Fv3 x (c1 side) (e0 x (c1 side) n0'))])))).
Proof.
  intros.
  pose (lemma25_ininkc0_false_Φ3 side).
  time (destruct side; simpl; ProveFreshCTerm).  (* 3.885 secs *)
Qed.






(*----------------------------------------   Using CCA2 to substitute kc1 to kc1'     ---------------------------------------------*)

Lemma lemma25_CCA2_kc1_kc1'_BeforeΦ3 : forall side : Sides,
  CCA2BeforeEncTerm Dec Pkey Skey [nonce (6)] [nonce (11)] (fFΦ3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0') (Fv1 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0')) (Fv2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0'))
                                                                 (Fv3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0'))).
Proof.
  time (destruct side; simpl; ProveCca2Before). (*7.995 secs*)
Qed.

Lemma lemma25_CCA2_kc1_kc1'_M1 : forall side,
    CCA2BeforeEncTerm Dec Pkey Skey [nonce (6)] [nonce (11)] (M1 (c0 side) (c1 side) kc1).
Proof.
  intros.
  pose (lemma25_CCA2_kc1_kc1'_BeforeΦ3 side).
  time (destruct side; simpl; ProveCca2Before).
Qed.


Lemma lemma25_CCA2_kc1_kc1'_M1' : forall side,
    CCA2BeforeEncTerm Dec Pkey Skey [nonce (6)] [nonce (11)] (M1 (c0 side) (c1 side) kc1').
Proof.
  intros.
  pose (lemma25_CCA2_kc1_kc1'_BeforeΦ3 side).
  time (destruct side; simpl; ProveCca2Before).
Qed.

(* *)


Lemma lemma25_CCA2_kc1_kc1'_AfterΦ5 : forall side, CCA2AfterEncTerm Dec Pkey Skey Error [nonce (6)] [nonce (11)]
   (fun y1 : ppt => (FFΦ5 (c0 side) (c1 side) y1)).
Proof.
  intros.
  unfold FFΦ5.
  pose (lemma25_CCA2_kc1_kc1'_BeforeΦ3 side).
  time (destruct side; simpl; ProveCca2After). (*8.347 sec*)
Qed.

Lemma lemma25_CCA2_kc1_kc1'_Φ5 : forall side,
 CCA2AfterEnc Dec Pkey Skey Error [nonce (6)] [nonce (11)]
   (fun y1 : ppt =>
    [b0 (c0 side); b1 (c1 side);
    If acc0 (c0 side) (c1 side) & acc1 (c0 side) (c1 side)
    Then If (τ1 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0')) ≟ e0 (c0 side) (c1 side) n0')
            or (τ2 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0')) ≟ e0 (c0 side) (c1 side) n0')
               or (τ3 (fFΦ2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0')) ≟ e0 (c0 side) (c1 side) n0') Then ⫠
         Else (＜ ＜ e0 (c0 side) (c1 side) n0', e1 (c0 side) (c1 side) n1,
                 dv (Fv1 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0')) (Fv2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0')) (Fv3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0'))
                   (shufl (π1 Fv1 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0')) (π1 Fv2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0'))
                      (π1 Fv3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0'))) ＞,
                 ＜ ⫠, FL1 (c0 side) (c1 side) y1, FIDO (FiiO1 (c0 side) (c1 side) y1) (FiiO2 (c0 side) (c1 side) y1) (FiiO3 (c0 side) (c1 side) y1) ＞ ＞) Else ⫠]).
Proof.
  intros.
  pose (lemma25_CCA2_kc1_kc1'_BeforeΦ3 side).
  pose (lemma25_CCA2_kc1_kc1'_M1 side).
  pose (lemma25_CCA2_kc1_kc1'_M1' side).
  pose (lemma25_CCA2_kc1_kc1'_AfterΦ5 side).
  time (destruct side; simpl; ProveCca2After). (*10.879 secs *)
Qed.



(* -----------------------------  lemma25_elim_kc1_in_then_branch  ------------------------------------------------ *)

Lemma lemma25_elim_kc1_freshcΦ3 : forall side,
    FreshTermcTerm (nonce 1) (fun x : ppt => (fFΦ3 (c0 side) x (e0 (c0 side) x n0') (Fv1 (c0 side) x (e0 (c0 side) x n0')) (Fv2 (c0 side) x (e0 (c0 side) x n0'))
               (Fv3 (c0 side) x (e0 (c0 side) x n0')))).
Proof.
  intros.
  time (destruct side; simpl; ProveFreshCTerm). (* 3.349 secs *)
Qed.

Lemma lemma25_elim_kc1_freshcΦ5 : forall side,
    FreshTermcTerm (nonce 1) (fun x : ppt => let c := x in (FFΦ5 (c0 side) c (E1 (c0 side) c kc1'))).
Proof.
  intros.
  pose (lemma25_elim_kc1_freshcΦ3 side).
  destruct side. simpl. ProveFreshCTerm.
  time (simpl; ProveFreshCTerm). (*3.48 secs *)
Qed.


Lemma lemma25_elim_kc1_cnxtΦ3: forall side, ContextTerm General Term
                          (fun b3 : ppt =>
(fFΦ3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0') (Fv1 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0')) (Fv2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0'))
      (Fv3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0')))).
Proof.
  intros.
  time (destruct side; simpl; ProveContext). (*4.388 secs*)
Qed.


Lemma lemma25_elim_kc1_cnxtΦ5: forall side, ContextTerm General Term
                          (fun b3 : ppt => (FFΦ5 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1'))).
Proof.
  intros.
  pose (lemma25_elim_kc1_cnxtΦ3 side).
  time (destruct side; simpl; ProveContext). (*4.388 secs*)
Qed.



Lemma lemma25_elim_kc1_freshc1: forall side,
  FreshTermcTerm nonce (1) (fun x : ppt => π2 (π1 decS (τ1 (FFΦ5 (c0 side) x (E1 (c0 side) x kc1'))))).
Proof.
  intros.
  pose (lemma25_elim_kc1_freshcΦ3 side).
  pose (lemma25_elim_kc1_freshcΦ5 side).
  pose (lemma25_elim_kc1_cnxtΦ3 side).
  pose (lemma25_elim_kc1_cnxtΦ5 side).
  time (destruct side; simpl; ProveFreshCTerm).
Qed.

Lemma lemma25_elim_kc1_freshc2: forall side,
  FreshTermcTerm nonce (1) (fun x : ppt => π2 (π1 decS (τ2 (FFΦ5 (c0 side) x (E1 (c0 side) x kc1'))))).
Proof.
  intros.
  pose (lemma25_elim_kc1_freshcΦ3 side).
  pose (lemma25_elim_kc1_freshcΦ5 side).
  pose (lemma25_elim_kc1_cnxtΦ3 side).
  pose (lemma25_elim_kc1_cnxtΦ5 side).
  time (destruct side; simpl; ProveFreshCTerm).
Qed.

Lemma lemma25_elim_kc1_freshc3: forall side,
  FreshTermcTerm nonce (1) (fun x : ppt => π2 (π1 decS (τ3 (FFΦ5 (c0 side) x (E1 (c0 side) x kc1'))))).
Proof.
  intros.
  pose (lemma25_elim_kc1_freshcΦ3 side).
  pose (lemma25_elim_kc1_freshcΦ5 side).
  pose (lemma25_elim_kc1_cnxtΦ3 side).
  pose (lemma25_elim_kc1_cnxtΦ5 side).
  time (destruct side; simpl; ProveFreshCTerm).
Qed.



(* -----------------------------  lemma25_elim_kc1_in_then_branch  ------------------------------------------------ *)

Lemma lemma25_ininkc1_Freshkc1_Φ3: forall side, FreshTermcTerm (nonce 1) (fun x : ppt => let c := x in  (fFΦ3 (c0 side) c (e0 (c0 side) c n0') (Fv1 (c0 side) c (e0 (c0 side) c n0')) (Fv2 (c0 side) c (e0 (c0 side) c n0'))
               (Fv3 (c0 side) c (e0 (c0 side) c n0')))).
Proof.
  intros. unfold Fv1.
  time (destruct side; simpl; ProveFreshCTerm). (*3.231 secs*)
Qed.

Lemma lemma25_ininkc1_Freshkc1_Φ5: forall side, FreshTermcTerm (nonce 1) (fun x : ppt => let c := x in
                                                                  (FFΦ5 (c0 side) c (E1 (c0 side) c kc1'))).
Proof.
  intros.
  pose (lemma25_ininkc1_Freshkc1_Φ3 side).
  time (destruct side; simpl; ProveFreshCTerm). (*2.912 secs*)
Qed.



(* -----------------------------  lemma25_elim_bot_in_then_branch  ------------------------------------------------ *)

Lemma lemma25_elim_bot_cnxtΦ3: forall side, ContextTerm General Term
                          (fun b3 : ppt =>
(fFΦ3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0') (Fv1 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0')) (Fv2 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0'))
      (Fv3 (c0 side) (c1 side) (e0 (c0 side) (c1 side) n0')))).
Proof.
  intros.
  time (destruct side; simpl; ProveContext). (*4.388 secs*)
Qed.

Lemma lemma25_elim_bot_cnxtΦ5: forall side, ContextTerm General Term
                          (fun b3 : ppt => (FFΦ5 (c0 side) (c1 side) (E1 (c0 side) (c1 side) kc1'))).
Proof.
  intros.
  pose (lemma25_elim_bot_cnxtΦ3 side).
  time (destruct side; simpl; ProveContext). (*4.388 secs*)
Qed.

(* ---------------------------------------  lemma25  -------------------------------------------------- *)

Lemma lemma25_freshcΦ3kc0:
  Freshc (nonce 0) (fun lx => let c0 := Nth 0 lx in let c1 := Nth 1 lx in
                                           [fFΦ3 c0 c1 (e0 c0 c1 n0') (Fv1 c0 c1 (e0 c0 c1 n0')) (Fv2 c0 c1 (e0 c0 c1 n0')) (Fv3 c0 c1 (e0 c0 c1 n0'))]).
Proof.
  simpl. time ProveFreshC. (* 1.057 secs  *)
Qed.

Lemma lemma25_freshcΦ3kc1:
  Freshc (nonce 1) (fun lx => let c0 := Nth 0 lx in let c1 := Nth 1 lx in
                                           [fFΦ3 c0 c1 (e0 c0 c1 n0') (Fv1 c0 c1 (e0 c0 c1 n0')) (Fv2 c0 c1 (e0 c0 c1 n0')) (Fv3 c0 c1 (e0 c0 c1 n0'))]).
Proof.
  simpl. time ProveFreshC. (* 1.057 secs  *)
Qed.


Lemma lemma25_freshcΦ5kc0:
  Freshc (nonce 0) (fun lx => let c0 := Nth 0 lx in let c1 := Nth 1 lx in
                                           [FFΦ5 c0 c1 (E1 c0 c1 kc1')]).
Proof.
  pose lemma25_freshcΦ3kc0.
  simpl. time ProveFreshC. (*  1.231 secs  *)
Qed.



Lemma lemma25_freshcΦ5kc1:
  Freshc (nonce 1) (fun lx => let c0 := Nth 0 lx in let c1 := Nth 1 lx in
                                           [FFΦ5 c0 c1 (E1 c0 c1 kc1')]).
Proof.
  pose lemma25_freshcΦ3kc1.
  simpl. time ProveFreshC. (*  1.157 secs  *)
Qed.
















(***************************************************************************************************)
(***************************************************************************************************)
(****************************          Lemma_26_13.v        ****************************************)
(***************************************************************************************************)
(***************************************************************************************************)




(*----------------------------------------  Lemma_26_13.v Part_One  ----------------------------------------*)

Lemma lemma26_13_part1_Φ5_Context : forall c0 c1 dvs, ContextTerm General Term (fun _ : ppt => dvs) ->
     ContextTerm General Term (fun b3 : ppt => (fΦΦ5 c0 c1  (encS (m1 c0 c1 n1) rd0) (e1 c0 c1 n1) dvs)).
Proof.
  intros.
  time ProveContext. (*  0.636 secs  *)
Qed.




Lemma lemma26_13_CCA2_m0_m1_afterΦ3_voter1 :  CCA2AfterEncTerm Dec Pkey Skey Error [nonce (6)] [nonce (8)]
  (fun x1 : ppt => (FΦΦ3 c10 c11 (encS (m1 c10 c11 n1) rd0) x1 (dvS26 c10 c11 (encS (m1 c10 c11 n1) rd0) x1 (giv3 c10 c11 (encS (m1 c10 c11 n1) rd0) x1)))).
Proof.
  time ProveCca2After. (*1.657 secs*)
Qed.


Lemma lemma26_13_CCA2_m0_m1_afterΦ5_voter1 :  CCA2AfterEncTerm Dec Pkey Skey Error [nonce (6)] [nonce (8)]
  (fun x1 : ppt => fΦΦ5 c10 c11 (encS (m1 c10 c11 n1) rd0) x1 (dvS26 c10 c11 (encS (m1 c10 c11 n1) rd0) x1 (giv3 c10 c11 (encS (m1 c10 c11 n1) rd0) x1))).
Proof.
  pose lemma26_13_CCA2_m0_m1_afterΦ3_voter1.
  time ProveCca2After. (*2.517 secs*)
Qed.

Lemma lemma26_13_CCA2_m0_m1_after_voter1 :  CCA2AfterEnc Dec Pkey Skey Error [nonce (6)] [nonce (8)]
    (fun x1 : ppt =>
     [b0 c10; b1 c11; acc0 c10 c11 & acc1 c10 c11;
     acc0 c10 c11 &
     acc1 c10 c11 &
     bnlcheck c10 n0 (FΦΦ3 c10 c11 (encS (m1 c10 c11 n1) rd0) x1 (dvS26 c10 c11 (encS (m1 c10 c11 n1) rd0) x1 (giv3 c10 c11 (encS (m1 c10 c11 n1) rd0) x1))) &
     bnlcheck c11 n1 (FΦΦ3 c10 c11 (encS (m1 c10 c11 n1) rd0) x1 (dvS26 c10 c11 (encS (m1 c10 c11 n1) rd0) x1 (giv3 c10 c11 (encS (m1 c10 c11 n1) rd0) x1)));
     If ( acc0 c10 c11 & acc1 c10 c11 ) &
        bnlcheck c10 n0 (FΦΦ3 c10 c11 (encS (m1 c10 c11 n1) rd0) x1 (dvS26 c10 c11 (encS (m1 c10 c11 n1) rd0) x1 (giv3 c10 c11 (encS (m1 c10 c11 n1) rd0) x1))) &
        bnlcheck c11 n1 (FΦΦ3 c10 c11 (encS (m1 c10 c11 n1) rd0) x1 (dvS26 c10 c11 (encS (m1 c10 c11 n1) rd0) x1 (giv3 c10 c11 (encS (m1 c10 c11 n1) rd0) x1)))
     Then ＜ ＜ encS (m1 c10 c11 n1) rd0, x1, dvS26 c10 c11 (encS (m1 c10 c11 n1) rd0) x1 (giv3 c10 c11 (encS (m1 c10 c11 n1) rd0) x1) ＞,
          ＜ Enco0 c10 c11 (encS (m1 c10 c11 n1) rd0) x1 (dvS26 c10 c11 (encS (m1 c10 c11 n1) rd0) x1 (giv3 c10 c11 (encS (m1 c10 c11 n1) rd0) x1)),
          Enco1 c10 c11 (encS (m1 c10 c11 n1) rd0) x1 (dvS26 c10 c11 (encS (m1 c10 c11 n1) rd0) x1 (giv3 c10 c11 (encS (m1 c10 c11 n1) rd0) x1)),
          Do (giO1 (m0 c10 c11 n0) c10 c11 (encS (m1 c10 c11 n1) rd0) x1 (dvS26 c10 c11 (encS (m1 c10 c11 n1) rd0) x1 (giv3 c10 c11 (encS (m1 c10 c11 n1) rd0) x1)))
            (giO2 (m0 c10 c11 n0) c10 c11 (encS (m1 c10 c11 n1) rd0) x1 (dvS26 c10 c11 (encS (m1 c10 c11 n1) rd0) x1 (giv3 c10 c11 (encS (m1 c10 c11 n1) rd0) x1)))
            (giO3 (m0 c10 c11 n0) c10 c11 (encS (m1 c10 c11 n1) rd0) x1 (dvS26 c10 c11 (encS (m1 c10 c11 n1) rd0) x1 (giv3 c10 c11 (encS (m1 c10 c11 n1) rd0) x1))) ＞ ＞ Else ⫠]).
Proof.
  pose lemma26_13_CCA2_m0_m1_afterΦ3_voter1.
  pose lemma26_13_CCA2_m0_m1_afterΦ5_voter1.
  time ProveCca2After. (* 24.706 secs *)
Qed.



Lemma lemma26_13_CCA2_m0_m1_afterΦ3_voter0 :  CCA2AfterEncTerm Dec Pkey Skey Error [nonce (6)] [nonce (7)]
  (fun x0 : ppt => (FΦΦ3 c10 c11 x0 (e1 c10 c11 n1) (dvS26 c10 c11 x0 (e1 c10 c11 n1) (fiv3 c10 c11 x0 (e1 c10 c11 n1))))).
Proof.
  time ProveCca2After. (*1.657 secs*)
Qed.


Lemma lemma26_13_CCA2_m0_m1_afterΦ5_voter0 :  CCA2AfterEncTerm Dec Pkey Skey Error [nonce (6)] [nonce (7)]
  (fun x0 : ppt => (fΦΦ5 c10 c11 x0 (e1 c10 c11 n1) (dvS26 c10 c11 x0 (e1 c10 c11 n1) (fiv3 c10 c11 x0 (e1 c10 c11 n1))))).
Proof.
  pose lemma26_13_CCA2_m0_m1_afterΦ3_voter0.
  time ProveCca2After. (*2.31 secs*)
Qed.


Lemma lemma26_13_CCA2_m0_m1_after_voter0:
 CCA2AfterEnc Dec Pkey Skey Error [nonce (6)] [nonce (7)]
   (fun x0 : ppt =>
    [b0 c10; b1 c11; acc0 c10 c11 & acc1 c10 c11;
    acc0 c10 c11 &
    acc1 c10 c11 &
    bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 (e1 c10 c11 n1) (dvS26 c10 c11 x0 (e1 c10 c11 n1) (fiv3 c10 c11 x0 (e1 c10 c11 n1)))) &
    bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 (e1 c10 c11 n1) (dvS26 c10 c11 x0 (e1 c10 c11 n1) (fiv3 c10 c11 x0 (e1 c10 c11 n1))));
    If (acc0 c10 c11 & acc1 c10 c11) &
       bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 (e1 c10 c11 n1) (dvS26 c10 c11 x0 (e1 c10 c11 n1) (fiv3 c10 c11 x0 (e1 c10 c11 n1)))) &
       bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 (e1 c10 c11 n1) (dvS26 c10 c11 x0 (e1 c10 c11 n1) (fiv3 c10 c11 x0 (e1 c10 c11 n1))))
    Then ＜ ＜ x0, e1 c10 c11 n1, dvS26 c10 c11 x0 (e1 c10 c11 n1) (fiv3 c10 c11 x0 (e1 c10 c11 n1)) ＞,
         ＜ Enco0 c10 c11 x0 (e1 c10 c11 n1) (dvS26 c10 c11 x0 (e1 c10 c11 n1) (fiv3 c10 c11 x0 (e1 c10 c11 n1))),
         Enco1 c10 c11 x0 (e1 c10 c11 n1) (dvS26 c10 c11 x0 (e1 c10 c11 n1) (fiv3 c10 c11 x0 (e1 c10 c11 n1))),
         Do (fiO1 (m0 c10 c11 n0) c10 c11 x0 (e1 c10 c11 n1) (dvS26 c10 c11 x0 (e1 c10 c11 n1) (fiv3 c10 c11 x0 (e1 c10 c11 n1))))
           (fiO2 (m0 c10 c11 n0) c10 c11 x0 (e1 c10 c11 n1) (dvS26 c10 c11 x0 (e1 c10 c11 n1) (fiv3 c10 c11 x0 (e1 c10 c11 n1))))
           (fiO3 (m0 c10 c11 n0) c10 c11 x0 (e1 c10 c11 n1) (dvS26 c10 c11 x0 (e1 c10 c11 n1) (fiv3 c10 c11 x0 (e1 c10 c11 n1)))) ＞ ＞ Else ⫠]).
Proof.
  pose lemma26_13_CCA2_m0_m1_afterΦ3_voter0.
  pose lemma26_13_CCA2_m0_m1_afterΦ5_voter0.
  time ProveCca2After. (*9.569 secs*)
Qed.




(*----------------------------------------  Lemma_26_13.v Part_Two  ----------------------------------------*)

(*--------------------------------*)
Lemma prop26_13_enco0_up_cnxt1 : forall msgo0 msgo1,
    ContextTerm General Term (fun _ : ppt => msgo0) ->
    ContextTerm General Term (fun _ : ppt => msgo1) ->
  ContextTerm General Term
    (fun x : ppt => (FFΦΦ5 c10 c11 (encS (If x Then msgo0 Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd0) (encS msgo1 rdd1))).
Proof.
  time ProveContext. (* 2.949 secs *)
Qed.

Lemma prop26_13_enco0_up_cnxt2 :  forall msgo0 msgo1,
    ContextTerm General Term (fun _ : ppt => msgo0) ->
    ContextTerm General Term (fun _ : ppt => msgo1) ->
    let x0 := encS (m1 c10 c11 n1) rd0 in
    let x1 := encS (m0 c10 c11 n0) rd1 in
    let dvs := dv (V1 c10 c11 x0 x1) (V2 c10 c11 x0 x1) (V3 c10 c11 x0 x1) (S26 c10 c11 x0 x1 (V3 c10 c11 x0 x1)) in
ContextTerm General Term
    (fun x : ppt =>
     If acc0 c10 c11 & acc1 c10 c11
     Then ＜ ＜ encS (m1 c10 c11 n1) rd0, encS (m0 c10 c11 n0) rd1,
            dv (V1 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1)) (V2 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1))
              (V3 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1))
              (S26 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1) (V3 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1))) ＞,
          ＜ encS (If x Then msgo0 Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd0, encS msgo1 rdd1,
          Do
            (If τ1 (FFΦΦ5 c10 c11 (encS (If x Then msgo0 Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd0) (encS msgo1 rdd1)) ≟ encS (If x Then msgo0 Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd0 Then msgo0
             Else decS (τ1 (FFΦΦ5 c10 c11 (encS (If x Then msgo0 Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd0) (encS msgo1 rdd1))))
            (If τ2 (FFΦΦ5 c10 c11 (encS (If x Then msgo0 Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd0) (encS msgo1 rdd1)) ≟ encS (If x Then msgo0 Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd0 Then msgo0
             Else decS (τ2 (FFΦΦ5 c10 c11 (encS (If x Then msgo0 Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd0) (encS msgo1 rdd1))))
            (If τ3 (FFΦΦ5 c10 c11 (encS (If x Then msgo0 Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd0) (encS msgo1 rdd1)) ≟ encS (If x Then msgo0 Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd0 Then msgo0
                Else decS (τ3 (FFΦΦ5 c10 c11 (encS (If x Then msgo0 Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd0) (encS msgo1 rdd1)))) ＞ ＞ Else ⫠).
Proof.
  intros.
  pose (prop26_13_enco0_up_cnxt1 msgo0 msgo1 H H0). (* *)
  time ProveContext. (* 5.935 secs  *)
Qed.


(*--------------------------------*)

Lemma prop26_13_enco0_down_cnxt1 :  forall msgo0 msgo0' msgo1,
    ContextTerm General Term (fun _ : ppt => msgo0) ->
    ContextTerm General Term (fun _ : ppt => msgo0') ->
    ContextTerm General Term (fun _ : ppt => msgo1) ->
    let x0 := encS (m1 c10 c11 n1) rd0 in
    let x1 := encS (m0 c10 c11 n0) rd1 in
    let dvs := dv (V1 c10 c11 x0 x1) (V2 c10 c11 x0 x1) (V3 c10 c11 x0 x1) (S26 c10 c11 x0 x1 (V3 c10 c11 x0 x1)) in
    ContextTerm General Term
                (fun x : ppt => (FFΦΦ5 c10 c11 (encS (If x Then msgo0' Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd0) (encS msgo1 rdd1))).
Proof.
  intros.
  time ProveContext. (* 2.786 secs   *)
Qed.


(*  *)
Lemma prop26_13_enco0_down_cnxt2 :  forall msgo0 msgo0' msgo1,
    ContextTerm General Term (fun _ : ppt => msgo0) ->
    ContextTerm General Term (fun _ : ppt => msgo0') ->
    ContextTerm General Term (fun _ : ppt => msgo1) ->
    let x0 := encS (m1 c10 c11 n1) rd0 in
    let x1 := encS (m0 c10 c11 n0) rd1 in
    let dvs := dv (V1 c10 c11 x0 x1) (V2 c10 c11 x0 x1) (V3 c10 c11 x0 x1) (S26 c10 c11 x0 x1 (V3 c10 c11 x0 x1)) in
  ContextTerm General Term
  (fun x : ppt =>
    If acc0 c10 c11 & acc1 c10 c11
    Then ＜ ＜ x0, x1, dvs ＞,
         ＜ encS (If x Then msgo0' Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd0, encS msgo1 rdd1,
         Do
           (If τ1 (FFΦΦ5 c10 c11 (encS (If x Then msgo0' Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd0) (encS msgo1 rdd1)) ≟ encS (If x Then msgo0' Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd0 Then msgo0
            Else decS (τ1 (FFΦΦ5 c10 c11 (encS (If x Then msgo0' Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd0) (encS msgo1 rdd1))))
           (If τ2 (FFΦΦ5 c10 c11 (encS (If x Then msgo0' Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd0) (encS msgo1 rdd1)) ≟ encS (If x Then msgo0' Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd0 Then msgo0
            Else decS (τ2 (FFΦΦ5 c10 c11 (encS (If x Then msgo0' Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd0) (encS msgo1 rdd1))))
           (If τ3 (FFΦΦ5 c10 c11 (encS (If x Then msgo0' Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd0) (encS msgo1 rdd1)) ≟ encS (If x Then msgo0' Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd0 Then msgo0
               Else decS (τ3 (FFΦΦ5 c10 c11 (encS (If x Then msgo0' Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd0) (encS msgo1 rdd1)))) ＞ ＞ Else ⫠).
Proof.
  intros.
  pose (prop26_13_enco0_down_cnxt1 msgo0 msgo0' msgo1 H H0 H1). (* *)
  time ProveContext. (* 2.77 secs  *)
Qed.




(*--------------------------------*)

(*  *)
Lemma prop26_13_enco1_up_cnxt1 :  forall msgo0 msgo0' msgo1,
    ContextTerm General Term (fun _ : ppt => msgo0) ->
    ContextTerm General Term (fun _ : ppt => msgo0') ->
    ContextTerm General Term (fun _ : ppt => msgo1) ->
    let x0 := encS (m1 c10 c11 n1) rd0 in
    let x1 := encS (m0 c10 c11 n0) rd1 in
    let dvs := dv (V1 c10 c11 x0 x1) (V2 c10 c11 x0 x1) (V3 c10 c11 x0 x1) (S26 c10 c11 x0 x1 (V3 c10 c11 x0 x1)) in
 ContextTerm General Term
    (fun x : ppt =>(FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS (If x Then msgo1 Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd1))).
Proof.
  intros.
  time ProveContext. (* 2.737 secs    *)
Qed.


(*  *)
Lemma prop26_13_enco1_up_cnxt2 :  forall msgo0 msgo0' msgo1,
    ContextTerm General Term (fun _ : ppt => msgo0) ->
    ContextTerm General Term (fun _ : ppt => msgo0') ->
    ContextTerm General Term (fun _ : ppt => msgo1) ->
    let x0 := encS (m1 c10 c11 n1) rd0 in
    let x1 := encS (m0 c10 c11 n0) rd1 in
    let dvs := dv (V1 c10 c11 x0 x1) (V2 c10 c11 x0 x1) (V3 c10 c11 x0 x1) (S26 c10 c11 x0 x1 (V3 c10 c11 x0 x1)) in
  ContextTerm General Term
    (fun x : ppt =>
     If acc0 c10 c11 & acc1 c10 c11
     Then ＜ ＜ x0, x1, dvs ＞,
          ＜ encS msgo0' rdd0, encS (If x Then msgo1 Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd1,
          Do
            (If τ1 (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS (If x Then msgo1 Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd1)) ≟ encS msgo0' rdd0 Then msgo0
             Else If τ1 (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS (If x Then msgo1 Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd1)) ≟ encS (If x Then msgo1 Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd1 Then msgo1
                  Else decS (τ1 (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS (If x Then msgo1 Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd1))))
            (If τ2 (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS (If x Then msgo1 Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd1)) ≟ encS msgo0' rdd0 Then msgo0
             Else If τ2 (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS (If x Then msgo1 Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd1)) ≟ encS (If x Then msgo1 Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd1 Then msgo1
                  Else decS (τ2 (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS (If x Then msgo1 Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd1))))
            (If τ3 (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS (If x Then msgo1 Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd1)) ≟ encS msgo0' rdd0 Then msgo0
             Else If τ3 (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS (If x Then msgo1 Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd1)) ≟ encS (If x Then msgo1 Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd1 Then msgo1
             Else decS (τ3 (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS (If x Then msgo1 Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd1)))) ＞ ＞ Else ⫠).
Proof.
  intros.
  pose (prop26_13_enco1_up_cnxt1 msgo0 msgo0' msgo1 H H0 H1). (* *)
  time ProveContext. (* 8.053 secs   *)
Qed.






(*--------------------------------*)

Lemma prop26_13_enco1_down_cnxt1 :  forall msgo0 msgo0' msgo1 msgo1',
    ContextTerm General Term (fun _ : ppt => msgo0) ->
    ContextTerm General Term (fun _ : ppt => msgo0') ->
    ContextTerm General Term (fun _ : ppt => msgo1) ->
    ContextTerm General Term (fun _ : ppt => msgo1') ->
    let x0 := encS (m1 c10 c11 n1) rd0 in
    let x1 := encS (m0 c10 c11 n0) rd1 in
    let dvs := dv (V1 c10 c11 x0 x1) (V2 c10 c11 x0 x1) (V3 c10 c11 x0 x1) (S26 c10 c11 x0 x1 (V3 c10 c11 x0 x1)) in
  ContextTerm General Term
    (fun x : ppt => (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS (If x Then msgo1' Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd1))).
Proof.
  intros.
  time ProveContext. (* 3.022 secs  *)
Qed.

(*  *)
Lemma prop26_13_enco1_down_cnxt2 :  forall msgo0 msgo0' msgo1 msgo1',
    ContextTerm General Term (fun _ : ppt => msgo0) ->
    ContextTerm General Term (fun _ : ppt => msgo0') ->
    ContextTerm General Term (fun _ : ppt => msgo1) ->
    ContextTerm General Term (fun _ : ppt => msgo1') ->
    let x0 := encS (m1 c10 c11 n1) rd0 in
    let x1 := encS (m0 c10 c11 n0) rd1 in
    let dvs := dv (V1 c10 c11 x0 x1) (V2 c10 c11 x0 x1) (V3 c10 c11 x0 x1) (S26 c10 c11 x0 x1 (V3 c10 c11 x0 x1)) in
  ContextTerm General Term
    (fun x : ppt =>
     If acc0 c10 c11 & acc1 c10 c11
     Then ＜ ＜ x0, x1, dvs ＞,
          ＜ encS msgo0' rdd0, encS (If x Then msgo1' Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd1,
          Do
            (If τ1 (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS (If x Then msgo1' Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd1)) ≟ encS msgo0' rdd0 Then msgo0
             Else If τ1 (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS (If x Then msgo1' Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd1)) ≟ encS (If x Then msgo1' Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd1 Then msgo1
                  Else decS (τ1 (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS (If x Then msgo1' Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd1))))
            (If τ2 (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS (If x Then msgo1' Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd1)) ≟ encS msgo0' rdd0 Then msgo0
             Else If τ2 (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS (If x Then msgo1' Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd1)) ≟ encS (If x Then msgo1' Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd1 Then msgo1
                  Else decS (τ2 (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS (If x Then msgo1' Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd1))))
            (If τ3 (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS (If x Then msgo1' Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd1)) ≟ encS msgo0' rdd0 Then msgo0
             Else If τ3 (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS (If x Then msgo1' Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd1)) ≟ encS (If x Then msgo1' Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd1 Then msgo1
                  Else decS (τ3 (FFΦΦ5 c10 c11 (encS msgo0' rdd0) (encS (If x Then msgo1' Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞) rdd1)))) ＞ ＞ Else ⫠).
Proof.
  intros.
  pose (prop26_13_enco1_down_cnxt1 msgo0 msgo0' msgo1 msgo1' H H0 H1 H2). (* *)
  time ProveContext. (* 4.497 secs *)
Qed.



(*--------------------------------*)

Lemma prop26_13_CCA2_kc1_kc0'_lhs_beforeΦ3_voter1:
  CCA2BeforeEncTerm Dec Pkey Skey [nonce (6)] [nonce (11)]
  (FΦΦ3 c10 c11 (encS (msg voter1 c10 c11) rd0) (encS (msg voter0 c10 c11) rd1)
              (dv (V1 c10 c11 (encS (msg voter1 c10 c11) rd0) (encS (msg voter0 c10 c11) rd1)) (V2 c10 c11 (encS (msg voter1 c10 c11) rd0) (encS (msg voter0 c10 c11) rd1))
                 (V3 c10 c11 (encS (msg voter1 c10 c11) rd0) (encS (msg voter0 c10 c11) rd1))
                 (S26 c10 c11 (encS (msg voter1 c10 c11) rd0) (encS (msg voter0 c10 c11) rd1) (V3 c10 c11 (encS (msg voter1 c10 c11) rd0) (encS (msg voter0 c10 c11) rd1))))).
Proof.
  time ProveCca2Before. (*2.797 secs*)
Qed.

(*  *)
 Lemma prop26_13_CCA2_kc1_kc0'_lhs_before1:
  let x0 := (encS (msg voter1 c10 c11) rd0) in
  let x1 := (encS (msg voter0 c10 c11) rd1) in
  let dvs := (dv (V1 c10 c11 x0 x1) (V2 c10 c11 x0 x1) (V3 c10 c11 x0 x1)) (S26 c10 c11 x0 x1 (V3 c10 c11 x0 x1)) in
  CCA2BeforeEncTerm Dec Pkey Skey [nonce (6)] [nonce (11)] (If bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs) Then msgo1 c10 c11 kc1 Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞).
Proof.
  pose prop26_13_CCA2_kc1_kc0'_lhs_beforeΦ3_voter1.
  time ProveCca2Before. (*  *)
Qed.

Lemma prop26_13_CCA2_kc1_kc0'_lhs_before2:
  let x0 := (encS (msg voter1 c10 c11) rd0) in
  let x1 := (encS (msg voter0 c10 c11) rd1) in
  let dvs := (dv (V1 c10 c11 x0 x1) (V2 c10 c11 x0 x1) (V3 c10 c11 x0 x1)) (S26 c10 c11 x0 x1 (V3 c10 c11 x0 x1)) in
  CCA2BeforeEncTerm Dec Pkey Skey [nonce (6)] [nonce (11)] (If bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs) Then msgo0 c10 c11 kc0' Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞).
Proof.
  pose prop26_13_CCA2_kc1_kc0'_lhs_beforeΦ3_voter1.
  time ProveCca2Before. (* *)
Qed.

Lemma prop26_13_CCA2_kc1_kc0'_lhs_afterΦ5_voter1:
  CCA2AfterEncTerm Dec Pkey Skey Error [nonce (6)] [nonce (11)]
   (fun y1 : ppt => (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) y1)).
Proof.
  pose prop26_13_CCA2_kc1_kc0'_lhs_beforeΦ3_voter1.
  time ProveCca2After. (* 5.686 secs *)
Qed.


Lemma prop26_13_CCA2_kc1_kc0'_lhs_after1:
  let x0 := (encS (msg voter1 c10 c11) rd0) in
  let x1 := (encS (msg voter0 c10 c11) rd1) in
  let dvs := (dv (V1 c10 c11 x0 x1) (V2 c10 c11 x0 x1) (V3 c10 c11 x0 x1)) (S26 c10 c11 x0 x1 (V3 c10 c11 x0 x1)) in
 CCA2AfterEnc Dec Pkey Skey Error [nonce (6)] [nonce (11)]
   (fun y1 : ppt =>
    [b0 c10; b1 c11; acc0 c10 c11 & acc1 c10 c11; acc0 c10 c11 & acc1 c10 c11 & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs);
    If (acc0 c10 c11 & acc1 c10 c11) & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs)
    Then ＜ ＜ x0, x1, dvs ＞,
         ＜ encS (msgo1 c10 c11 kc1') rdd0, y1,
         Do
           (If τ1 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) y1) ≟ encS (msgo1 c10 c11 kc1') rdd0 Then msgo0 c10 c11 kc0
            Else If τ1 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) y1) ≟ y1 Then msgo1 c10 c11 kc1
                 Else If τ1 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) y1) ≟ y1 Then Error Else decS (τ1 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) y1)))
           (If τ2 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) y1) ≟ encS (msgo1 c10 c11 kc1') rdd0 Then msgo0 c10 c11 kc0
            Else If τ2 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) y1) ≟ y1 Then msgo1 c10 c11 kc1
                 Else If τ2 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) y1) ≟ y1 Then Error Else decS (τ2 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) y1)))
           (If τ3 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) y1) ≟ encS (msgo1 c10 c11 kc1') rdd0 Then msgo0 c10 c11 kc0
            Else If τ3 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) y1) ≟ y1 Then msgo1 c10 c11 kc1
                 Else If τ3 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) y1) ≟ y1 Then Error Else decS (τ3 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) y1))) ＞ ＞ Else ⫠]).
Proof.
  simpl.
  pose prop26_13_CCA2_kc1_kc0'_lhs_beforeΦ3_voter1.
  pose prop26_13_CCA2_kc1_kc0'_lhs_before1.
  pose prop26_13_CCA2_kc1_kc0'_lhs_before2.
  pose prop26_13_CCA2_kc1_kc0'_lhs_afterΦ5_voter1.
  time ProveCca2After. (* 64.684 secs ??? *)
Qed.


Lemma prop26_13_CCA2_kc1_kc0'_lhs_beforeΦ3_voter0:
  CCA2BeforeEncTerm Dec Pkey Skey [nonce (6)] [nonce (10)]
  (FΦΦ3 c10 c11 (encS (msg voter1 c10 c11) rd0) (encS (msg voter0 c10 c11) rd1)
              (dv (V1 c10 c11 (encS (msg voter1 c10 c11) rd0) (encS (msg voter0 c10 c11) rd1)) (V2 c10 c11 (encS (msg voter1 c10 c11) rd0) (encS (msg voter0 c10 c11) rd1))
                 (V3 c10 c11 (encS (msg voter1 c10 c11) rd0) (encS (msg voter0 c10 c11) rd1))
                 (S26 c10 c11 (encS (msg voter1 c10 c11) rd0) (encS (msg voter0 c10 c11) rd1) (V3 c10 c11 (encS (msg voter1 c10 c11) rd0) (encS (msg voter0 c10 c11) rd1))))).
Proof.
  time ProveCca2Before. (*2.708 secs*)
Qed.

Lemma prop26_13_CCA2_kc1_kc0'_lhs_before3:
  let x0 := (encS (msg voter1 c10 c11) rd0) in
  let x1 := (encS (msg voter0 c10 c11) rd1) in
  let dvs := (dv (V1 c10 c11 x0 x1) (V2 c10 c11 x0 x1) (V3 c10 c11 x0 x1)) (S26 c10 c11 x0 x1 (V3 c10 c11 x0 x1)) in
  CCA2BeforeEncTerm Dec Pkey Skey [nonce (6)] [nonce (10)] (If bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs) Then msgo0 c10 c11 kc0 Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞).
Proof.
  pose prop26_13_CCA2_kc1_kc0'_lhs_beforeΦ3_voter0.
  time ProveCca2Before. (* *)
Qed.


Lemma prop26_13_CCA2_kc1_kc0'_lhs_before4:
  let x0 := (encS (msg voter1 c10 c11) rd0) in
  let x1 := (encS (msg voter0 c10 c11) rd1) in
  let dvs := (dv (V1 c10 c11 x0 x1) (V2 c10 c11 x0 x1) (V3 c10 c11 x0 x1)) (S26 c10 c11 x0 x1 (V3 c10 c11 x0 x1)) in
  CCA2BeforeEncTerm Dec Pkey Skey [nonce (6)] [nonce (10)] (If bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs) Then msgo1 c10 c11 kc1' Else ＜ ＜ ⫠, ⫠ ＞, ph3 ＞).
Proof.
  pose prop26_13_CCA2_kc1_kc0'_lhs_beforeΦ3_voter0.
  time ProveCca2Before. (* *)
Qed.


Lemma prop26_13_CCA2_kc1_kc0'_lhs_afterΦ5_voter0:
  CCA2AfterEncTerm Dec Pkey Skey Error [nonce (6)] [nonce (10)]
   (fun y0 : ppt => (FFΦΦ5 c10 c11 y0 (encS (msgo1 c10 c11 kc1) rdd1))).
Proof.
  pose prop26_13_CCA2_kc1_kc0'_lhs_beforeΦ3_voter0.
  time ProveCca2After. (* 5.686 secs *)
Qed.


Lemma prop26_13_CCA2_kc1_kc0'_lhs_after2:
  let x0 := (encS (msg voter1 c10 c11) rd0) in
  let x1 := (encS (msg voter0 c10 c11) rd1) in
  let dvs := (dv (V1 c10 c11 x0 x1) (V2 c10 c11 x0 x1) (V3 c10 c11 x0 x1)) (S26 c10 c11 x0 x1 (V3 c10 c11 x0 x1)) in
 CCA2AfterEnc Dec Pkey Skey Error [nonce (6)] [nonce (10)]
   (fun y0 : ppt =>
    [b0 c10; b1 c11; acc0 c10 c11 & acc1 c10 c11; acc0 c10 c11 & acc1 c10 c11 & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs);
    If (acc0 c10 c11 & acc1 c10 c11) & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs)
    Then ＜ ＜ x0, x1, dvs ＞,
         ＜ y0, encS (msgo1 c10 c11 kc1) rdd1,
         Do
           (If τ1 (FFΦΦ5 c10 c11 y0 (encS (msgo1 c10 c11 kc1) rdd1)) ≟ y0 Then msgo0 c10 c11 kc0
            Else If τ1 (FFΦΦ5 c10 c11 y0 (encS (msgo1 c10 c11 kc1) rdd1)) ≟ y0 Then Error Else decS (τ1 (FFΦΦ5 c10 c11 y0 (encS (msgo1 c10 c11 kc1) rdd1))))
           (If τ2 (FFΦΦ5 c10 c11 y0 (encS (msgo1 c10 c11 kc1) rdd1)) ≟ y0 Then msgo0 c10 c11 kc0
            Else If τ2 (FFΦΦ5 c10 c11 y0 (encS (msgo1 c10 c11 kc1) rdd1)) ≟ y0 Then Error Else decS (τ2 (FFΦΦ5 c10 c11 y0 (encS (msgo1 c10 c11 kc1) rdd1))))
           (If τ3 (FFΦΦ5 c10 c11 y0 (encS (msgo1 c10 c11 kc1) rdd1)) ≟ y0 Then msgo0 c10 c11 kc0
            Else If τ3 (FFΦΦ5 c10 c11 y0 (encS (msgo1 c10 c11 kc1) rdd1)) ≟ y0 Then Error Else decS (τ3 (FFΦΦ5 c10 c11 y0 (encS (msgo1 c10 c11 kc1) rdd1)))) ＞ ＞ Else ⫠]).
Proof.
  simpl.
  pose prop26_13_CCA2_kc1_kc0'_lhs_beforeΦ3_voter0.
  pose prop26_13_CCA2_kc1_kc0'_lhs_before3.
  pose prop26_13_CCA2_kc1_kc0'_lhs_before4.
  pose prop26_13_CCA2_kc1_kc0'_lhs_afterΦ5_voter0.
  time ProveCca2After. (* 13.386 secs ??? *)
Qed.


Lemma prop26_13_phase3_cnxt:
  ContextTerm General Term (fun _ : ppt => (FΦΦ3 c10 c11 (encS (msg voter1 c10 c11) rd0) (encS (msg voter0 c10 c11) rd1)
              (dv (V1 c10 c11 (encS (msg voter1 c10 c11) rd0) (encS (msg voter0 c10 c11) rd1)) (V2 c10 c11 (encS (msg voter1 c10 c11) rd0) (encS (msg voter0 c10 c11) rd1))
                 (V3 c10 c11 (encS (msg voter1 c10 c11) rd0) (encS (msg voter0 c10 c11) rd1))
                 (S26 c10 c11 (encS (msg voter1 c10 c11) rd0) (encS (msg voter0 c10 c11) rd1) (V3 c10 c11 (encS (msg voter1 c10 c11) rd0) (encS (msg voter0 c10 c11) rd1)))))).
Proof.
  time ProveContext. (*2.629 secs*)
Qed.


(*--------------------------------*)

Lemma prop26_13_CCA2_kc1_kc0'_rhs_beforeΦ3_voter1:
 CCA2BeforeEncTerm Dec Pkey Skey [nonce (6)] [nonce (11)]
    (FΦΦ3 c10 c11 (encS (msg voter1 c10 c11) rd0) (encS (msg voter0 c10 c11) rd1)
              (dv (V1 c10 c11 (encS (msg voter1 c10 c11) rd0) (encS (msg voter0 c10 c11) rd1)) (V2 c10 c11 (encS (msg voter1 c10 c11) rd0) (encS (msg voter0 c10 c11) rd1))
                 (V3 c10 c11 (encS (msg voter1 c10 c11) rd0) (encS (msg voter0 c10 c11) rd1))
                 (S26 c10 c11 (encS (msg voter1 c10 c11) rd0) (encS (msg voter0 c10 c11) rd1) (V3 c10 c11 (encS (msg voter1 c10 c11) rd0) (encS (msg voter0 c10 c11) rd1))))).
Proof.
  time ProveCca2Before. (* 3.501 secs  *)
Qed.

Lemma prop26_13_CCA2_kc1_kc0'_rhs_before1:
  CCA2BeforeEncTerm Dec Pkey Skey [nonce (6)] [nonce (11)] (msgo0 c10 c11 kc0).
Proof.
  pose prop26_13_CCA2_kc1_kc0'_rhs_beforeΦ3_voter1.
  time ProveCca2Before. (*  *)
Qed.


Lemma prop26_13_CCA2_kc1_kc0'_rhs_before2:
  CCA2BeforeEncTerm Dec Pkey Skey [nonce (6)] [nonce (11)] (msgo0 c10 c11 kc0').
Proof.
  pose prop26_13_CCA2_kc1_kc0'_rhs_beforeΦ3_voter1.
  time ProveCca2Before. (*  *)
Qed.


Lemma prop26_13_CCA2_kc1_kc0'_rhs_afterΦ5_voter1:
 CCA2AfterEncTerm Dec Pkey Skey Error [nonce (6)] [nonce (11)]
   (fun y1 : ppt => (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) y1)).
Proof.
  pose prop26_13_CCA2_kc1_kc0'_rhs_beforeΦ3_voter1.
  time ProveCca2After. (*6.847 secs*)
Qed.


Lemma prop26_13_CCA2_kc1_kc0'_rhs_after1:
  let x0 := (encS (msg voter1 c10 c11) rd0) in
  let x1 := (encS (msg voter0 c10 c11) rd1) in
  let dvs := (dv (V1 c10 c11 x0 x1) (V2 c10 c11 x0 x1) (V3 c10 c11 x0 x1)) (S26 c10 c11 x0 x1 (V3 c10 c11 x0 x1)) in
 CCA2AfterEnc Dec Pkey Skey Error [nonce (6)] [nonce (11)]
   (fun y1 : ppt =>
    [b0 c10; b1 c11; acc0 c10 c11 & acc1 c10 c11; acc0 c10 c11 & acc1 c10 c11 & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs);
    If (acc0 c10 c11 & acc1 c10 c11) & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs)
    Then ＜ ＜ x0, x1, dvs ＞,
         ＜ encS (msgo1 c10 c11 kc1') rdd0, y1,
         Do
           (If τ1 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) y1) ≟ encS (msgo1 c10 c11 kc1') rdd0 Then msgo1 c10 c11 kc1
            Else If τ1 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) y1) ≟ y1 Then msgo0 c10 c11 kc0
                 Else If τ1 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) y1) ≟ y1 Then Error Else decS (τ1 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) y1)))
           (If τ2 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) y1) ≟ encS (msgo1 c10 c11 kc1') rdd0 Then msgo1 c10 c11 kc1
            Else If τ2 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) y1) ≟ y1 Then msgo0 c10 c11 kc0
                 Else If τ2 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) y1) ≟ y1 Then Error Else decS (τ2 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) y1)))
           (If τ3 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) y1) ≟ encS (msgo1 c10 c11 kc1') rdd0 Then msgo1 c10 c11 kc1
            Else If τ3 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) y1) ≟ y1 Then msgo0 c10 c11 kc0
            Else If τ3 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) y1) ≟ y1 Then Error Else decS (τ3 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) y1))) ＞ ＞ Else ⫠]).
Proof.
  simpl.
  pose prop26_13_CCA2_kc1_kc0'_rhs_beforeΦ3_voter1.
  pose prop26_13_CCA2_kc1_kc0'_rhs_before1.
  pose prop26_13_CCA2_kc1_kc0'_rhs_before2.
  pose prop26_13_CCA2_kc1_kc0'_rhs_afterΦ5_voter1.
  time ProveCca2After. (* 52.499 secs ??? *)
Qed.


Lemma prop26_13_CCA2_kc1_kc0'_rhs_beforeΦ3_voter0:
 CCA2BeforeEncTerm Dec Pkey Skey [nonce (6)] [nonce (10)]
    (FΦΦ3 c10 c11 (encS (msg voter1 c10 c11) rd0) (encS (msg voter0 c10 c11) rd1)
              (dv (V1 c10 c11 (encS (msg voter1 c10 c11) rd0) (encS (msg voter0 c10 c11) rd1)) (V2 c10 c11 (encS (msg voter1 c10 c11) rd0) (encS (msg voter0 c10 c11) rd1))
                 (V3 c10 c11 (encS (msg voter1 c10 c11) rd0) (encS (msg voter0 c10 c11) rd1))
                 (S26 c10 c11 (encS (msg voter1 c10 c11) rd0) (encS (msg voter0 c10 c11) rd1) (V3 c10 c11 (encS (msg voter1 c10 c11) rd0) (encS (msg voter0 c10 c11) rd1))))).
Proof.
  time ProveCca2Before. (* 3.501 secs  *)
Qed.



Lemma prop26_13_CCA2_kc1_kc0'_rhs_before3:
  CCA2BeforeEncTerm Dec Pkey Skey [nonce (6)] [nonce (10)] (msgo1 c10 c11 kc1).
Proof.
  pose prop26_13_CCA2_kc1_kc0'_rhs_beforeΦ3_voter0.
  time ProveCca2Before.
Qed.

Lemma prop26_13_CCA2_kc1_kc0'_rhs_before4:
  CCA2BeforeEncTerm Dec Pkey Skey [nonce (6)] [nonce (10)] (msgo1 c10 c11 kc1').
Proof.
  pose prop26_13_CCA2_kc1_kc0'_rhs_beforeΦ3_voter0.
  time ProveCca2Before.
Qed.


Lemma prop26_13_CCA2_kc1_kc0'_rhs_afterΦ5_voter0:
 CCA2AfterEncTerm Dec Pkey Skey Error [nonce (6)] [nonce (10)]
   (fun y0 : ppt => (FFΦΦ5 c10 c11 y0 (encS (msgo0 c10 c11 kc0) rdd1))).
Proof.
  pose prop26_13_CCA2_kc1_kc0'_rhs_beforeΦ3_voter0.
  time ProveCca2After. (*5.531 secs*)
Qed.

Lemma prop26_13_CCA2_kc1_kc0'_rhs_after2:
  let x0 := (encS (msg voter1 c10 c11) rd0) in
  let x1 := (encS (msg voter0 c10 c11) rd1) in
  let dvs := (dv (V1 c10 c11 x0 x1) (V2 c10 c11 x0 x1) (V3 c10 c11 x0 x1)) (S26 c10 c11 x0 x1 (V3 c10 c11 x0 x1)) in
 CCA2AfterEnc Dec Pkey Skey Error [nonce (6)] [nonce (10)]
   (fun y0 : ppt =>
    [b0 c10; b1 c11; acc0 c10 c11 & acc1 c10 c11; acc0 c10 c11 & acc1 c10 c11 & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs);
    If (acc0 c10 c11 & acc1 c10 c11) & bnlcheck c10 n0 (FΦΦ3 c10 c11 x0 x1 dvs) & bnlcheck c11 n1 (FΦΦ3 c10 c11 x0 x1 dvs)
    Then ＜ ＜ x0, x1, dvs ＞,
         ＜ y0, encS (msgo0 c10 c11 kc0) rdd1,
         Do
           (If τ1 (FFΦΦ5 c10 c11 y0 (encS (msgo0 c10 c11 kc0) rdd1)) ≟ y0 Then msgo1 c10 c11 kc1
            Else If τ1 (FFΦΦ5 c10 c11 y0 (encS (msgo0 c10 c11 kc0) rdd1)) ≟ y0 Then Error Else decS (τ1 (FFΦΦ5 c10 c11 y0 (encS (msgo0 c10 c11 kc0) rdd1))))
           (If τ2 (FFΦΦ5 c10 c11 y0 (encS (msgo0 c10 c11 kc0) rdd1)) ≟ y0 Then msgo1 c10 c11 kc1
            Else If τ2 (FFΦΦ5 c10 c11 y0 (encS (msgo0 c10 c11 kc0) rdd1)) ≟ y0 Then Error Else decS (τ2 (FFΦΦ5 c10 c11 y0 (encS (msgo0 c10 c11 kc0) rdd1))))
           (If τ3 (FFΦΦ5 c10 c11 y0 (encS (msgo0 c10 c11 kc0) rdd1)) ≟ y0 Then msgo1 c10 c11 kc1
            Else If τ3 (FFΦΦ5 c10 c11 y0 (encS (msgo0 c10 c11 kc0) rdd1)) ≟ y0 Then Error Else decS (τ3 (FFΦΦ5 c10 c11 y0 (encS (msgo0 c10 c11 kc0) rdd1)))) ＞ ＞ Else ⫠]).
Proof.
  simpl.
  pose prop26_13_CCA2_kc1_kc0'_rhs_beforeΦ3_voter0.
  pose prop26_13_CCA2_kc1_kc0'_rhs_before3.
  pose prop26_13_CCA2_kc1_kc0'_rhs_before4.
  pose prop26_13_CCA2_kc1_kc0'_rhs_afterΦ5_voter0.
  time ProveCca2After. (* 13.396 secs *)
Qed.



(*--------------------------------*)



Lemma lemma26_13_Do_equiv_Freshkc1Msgo0 : forall c0 c1, (c0 = c10 /\ c1 = c11) ->
   kc1 ≠ (π2 (π1 msgo0 c0 c1 kc0)).
Proof.
  intros.
  pose (@prop11 (fun x => (π2 (π1 msgo0 c0 x kc0))) vot0 1) as cont.
    destruct H. rewrite H, H0 in *.
    apply cont.
  ProveFresh.
  time ProveFreshCTerm.
Qed.

Lemma lemma26_13_Do_equiv_Freshkc0Msgo1 : forall c0 c1, (c0 = c10 /\ c1 = c11) ->
   kc0 ≠ (π2 (π1 msgo1 c0 c1 kc1)).
Proof.
  intros.
  pose (@prop11 (fun x => (π2 (π1 msgo1 x c1 kc1))) vot1 0) as cont.
    destruct H. rewrite H, H0 in *.
    apply cont.
  ProveFresh.
  simpl. time ProveFreshCTerm. (*13.108 secs*)
Qed.

Lemma lemma26_13_Do_equiv_Freshkc1o1: forall c0 c1, (c0 = c10 /\ c1 = c11) ->
   kc1 ≠ (π2 (π1 decS (τ1 (FFΦΦ5 c0 c1 (encS (msgo1 c0 c1 kc1') rdd0) (encS (msgo0 c0 c1 kc0') rdd1))))).
Proof.
  intros.
  pose (@prop11 (fun x => (π2 (π1 decS (τ1 (FFΦΦ5 c0 x (encS (msgo1 c0 x kc1') rdd0) (encS (msgo0 c0 x kc0') rdd1)))))) vot0 1) as cont.
    destruct H. rewrite H, H0 in *.
    apply cont.
  ProveFresh.
  simpl. time ProveFreshCTerm. (*34.459 secs *)
Qed.

Lemma lemma26_13_Do_equiv_Freshkc1o2: forall c0 c1, (c0 = c10 /\ c1 = c11) ->
   kc1 ≠ (π2 (π1 decS (τ2 (FFΦΦ5 c0 c1 (encS (msgo1 c0 c1 kc1') rdd0) (encS (msgo0 c0 c1 kc0') rdd1))))).
Proof.
  intros.
  pose (@prop11 (fun x => (π2 (π1 decS (τ2 (FFΦΦ5 c0 x (encS (msgo1 c0 x kc1') rdd0) (encS (msgo0 c0 x kc0') rdd1)))))) vot0 1) as cont.
    destruct H. rewrite H, H0 in *.
    apply cont.
  ProveFresh.
  simpl. time ProveFreshCTerm. (*24.363 secs *)
Qed.

Lemma lemma26_13_Do_equiv_Freshkc1o3: forall c0 c1, (c0 = c10 /\ c1 = c11) ->
   kc1 ≠ (π2 (π1 decS (τ3 (FFΦΦ5 c0 c1 (encS (msgo1 c0 c1 kc1') rdd0) (encS (msgo0 c0 c1 kc0') rdd1))))).
Proof.
  intros.
  pose (@prop11 (fun x => (π2 (π1 decS (τ3 (FFΦΦ5 c0 x (encS (msgo1 c0 x kc1') rdd0) (encS (msgo0 c0 x kc0') rdd1)))))) vot0 1) as cont.
    destruct H. rewrite H, H0 in *.
    apply cont.
  ProveFresh.
  time ProveFreshCTerm. (*23.789 secs *)
Qed.

Lemma lemma26_13_Do_equiv_Freshkc0o1: forall c0 c1, (c0 = c10 /\ c1 = c11) ->
   kc0 ≠ (π2 (π1 decS (τ1 (FFΦΦ5 c0 c1 (encS (msgo1 c0 c1 kc1') rdd0) (encS (msgo0 c0 c1 kc0') rdd1))))).
Proof.
  intros.
  pose (@prop11 (fun x => (π2 (π1 decS (τ1 (FFΦΦ5 x c1 (encS (msgo1 x c1 kc1') rdd0) (encS (msgo0 x c1 kc0') rdd1)))))) vot1 0) as cont.
    destruct H. rewrite H, H0 in *.
    apply cont.
  ProveFresh.
  simpl. time ProveFreshCTerm. (*23.561 secs  *)
Qed.

Lemma lemma26_13_Do_equiv_Freshkc0o2: forall c0 c1, (c0 = c10 /\ c1 = c11) ->
   kc0 ≠ (π2 (π1 decS (τ2 (FFΦΦ5 c0 c1 (encS (msgo1 c0 c1 kc1') rdd0) (encS (msgo0 c0 c1 kc0') rdd1))))).
Proof.
  intros.
  pose (@prop11 (fun x => (π2 (π1 decS (τ2 (FFΦΦ5 x c1 (encS (msgo1 x c1 kc1') rdd0) (encS (msgo0 x c1 kc0') rdd1)))))) vot1 0) as cont.
    destruct H. rewrite H, H0 in *.
    apply cont.
  ProveFresh.
  simpl. time ProveFreshCTerm. (*23.561 secs  *)
Qed.

Lemma lemma26_13_Do_equiv_Freshkc0o3: forall c0 c1, (c0 = c10 /\ c1 = c11) ->
   kc0 ≠ (π2 (π1 decS (τ3 (FFΦΦ5 c0 c1 (encS (msgo1 c0 c1 kc1') rdd0) (encS (msgo0 c0 c1 kc0') rdd1))))).
Proof.
  intros.
  pose (@prop11 (fun x => (π2 (π1 decS (τ3 (FFΦΦ5 x c1 (encS (msgo1 x c1 kc1') rdd0) (encS (msgo0 x c1 kc0') rdd1)))))) vot1 0) as cont.
    destruct H. rewrite H, H0 in *.
    apply cont.
  ProveFresh.
  simpl. time ProveFreshCTerm. (*23.561 secs  *)
Qed.

Lemma lemma26_13_Do_equiv_Do_isinkc1: forall m c0 c1, m = (msgo0 c0 c1 kc0) \/ m = (msgo1 c0 c1 kc1) ->  c0 = c10 /\ c1 = c11 ->
   Do m (decS (τ2 (FFΦΦ5 c0 c1 (encS (msgo1 c0 c1 kc1') rdd0) (encS (msgo0 c0 c1 kc0') rdd1))))
        (decS (τ3 (FFΦΦ5 c0 c1 (encS (msgo1 c0 c1 kc1') rdd0) (encS (msgo0 c0 c1 kc0') rdd1)))) = ⫠.
Proof.
  intros. simpl.
  unfold Do. unfold isinkc.
  destruct H; rewrite H.
(* isinkc1 check fails *)
  { assert (isin kc1
          (＜ π2 (π1 msgo0 c0 c1 kc0), π2 (π1 decS (τ2 (FFΦΦ5 c0 c1 (encS (msgo1 c0 c1 kc1') rdd0) (encS (msgo0 c0 c1 kc0') rdd1)))),
           π2 (π1 decS (τ3 (FFΦΦ5 c0 c1 (encS (msgo1 c0 c1 kc1') rdd0) (encS (msgo0 c0 c1 kc0') rdd1)))) ＞) = FAlse).
      unfold isin.
      rewrite Tau1Tri, Tau2Tri, Tau3Tri.
      rewrite lemma26_13_Do_equiv_Freshkc1Msgo0. rewrite lemma26_13_Do_equiv_Freshkc1o2. rewrite lemma26_13_Do_equiv_Freshkc1o3.
      repeat rewrite If_false.
      reflexivity.
      all : auto.
    rewrite H1; clear H1.
    rewrite If_false.
    unfold isin; rewrite Tau1Tri;
    unfold msgo0 at 7; rewrite proj1pair; rewrite proj2pair; rewrite ceqeq; repeat rewrite If_true; repeat rewrite If_same; rewrite If_false;
      reflexivity. }
(* isinkc0 check fails *)
  { assert (isin kc0
        (＜ π2 (π1 msgo1 c0 c1 kc1), π2 (π1 decS (τ2 (FFΦΦ5 c0 c1 (encS (msgo1 c0 c1 kc1') rdd0) (encS (msgo0 c0 c1 kc0') rdd1)))),
         π2 (π1 decS (τ3 (FFΦΦ5 c0 c1 (encS (msgo1 c0 c1 kc1') rdd0) (encS (msgo0 c0 c1 kc0') rdd1)))) ＞) = FAlse).
      unfold isin.
      rewrite Tau1Tri, Tau2Tri, Tau3Tri.
      rewrite lemma26_13_Do_equiv_Freshkc0Msgo1. rewrite lemma26_13_Do_equiv_Freshkc0o2. rewrite lemma26_13_Do_equiv_Freshkc0o3.
      repeat rewrite If_false.
      reflexivity.
      all : auto.
    rewrite H1; clear H1.
    rewrite If_false.
    unfold isin; rewrite Tau1Tri;
    unfold msgo1 at 7; rewrite proj1pair; rewrite proj2pair; rewrite ceqeq; repeat rewrite If_true; repeat rewrite If_same; rewrite If_false;
      reflexivity. }
Qed.

Lemma lemma26_13_Do_equiv_Do_isinkc2: forall m c0 c1, m = (msgo0 c0 c1 kc0) \/ m = (msgo1 c0 c1 kc1) -> c0 = c10 /\ c1 = c11 ->
   Do (decS (τ1 (FFΦΦ5 c0 c1 (encS (msgo1 c0 c1 kc1') rdd0) (encS (msgo0 c0 c1 kc0') rdd1)))) m
      (decS (τ3 (FFΦΦ5 c0 c1 (encS (msgo1 c0 c1 kc1') rdd0) (encS (msgo0 c0 c1 kc0') rdd1)))) = ⫠.
Proof.
  intros. simpl.
  unfold Do. unfold isinkc.
  destruct H; rewrite H.
(* isinkc1 check fails *)
  { assert (isin kc1
          (＜ π2 (π1 decS (τ1 (FFΦΦ5 c0 c1 (encS (msgo1 c0 c1 kc1') rdd0) (encS (msgo0 c0 c1 kc0') rdd1)))), π2 (π1 msgo0 c0 c1 kc0),
           π2 (π1 decS (τ3 (FFΦΦ5 c0 c1 (encS (msgo1 c0 c1 kc1') rdd0) (encS (msgo0 c0 c1 kc0') rdd1)))) ＞) = FAlse).
      unfold isin.
      rewrite Tau1Tri, Tau2Tri, Tau3Tri.
      rewrite lemma26_13_Do_equiv_Freshkc1Msgo0. rewrite lemma26_13_Do_equiv_Freshkc1o1. rewrite lemma26_13_Do_equiv_Freshkc1o3.
      repeat rewrite If_false.
      reflexivity.
      all : auto.
    rewrite H1; clear H1.
    rewrite If_false.
    unfold isin. rewrite Tau2Tri.
    unfold msgo0 at 10. rewrite proj1pair; rewrite proj2pair. rewrite ceqeq. repeat rewrite If_true. repeat rewrite If_same. rewrite If_true. repeat rewrite If_same. rewrite If_false.
    reflexivity. }
(* isinkc0 check fails *)
  { assert (isin kc0
        (＜ π2 (π1 decS (τ1 (FFΦΦ5 c0 c1 (encS (msgo1 c0 c1 kc1') rdd0) (encS (msgo0 c0 c1 kc0') rdd1)))), π2 (π1 msgo1 c0 c1 kc1),
         π2 (π1 decS (τ3 (FFΦΦ5 c0 c1 (encS (msgo1 c0 c1 kc1') rdd0) (encS (msgo0 c0 c1 kc0') rdd1)))) ＞) = FAlse).
      unfold isin.
      rewrite Tau1Tri, Tau2Tri, Tau3Tri.
      rewrite lemma26_13_Do_equiv_Freshkc0Msgo1. rewrite lemma26_13_Do_equiv_Freshkc0o1. rewrite lemma26_13_Do_equiv_Freshkc0o3.
      repeat rewrite If_false.
      reflexivity.
      all : auto.
    rewrite H1; clear H1.
    rewrite If_false.
    unfold isin. rewrite Tau2Tri.
    unfold msgo1 at 10. rewrite proj1pair; rewrite proj2pair. rewrite ceqeq. repeat rewrite If_true. repeat rewrite If_same. rewrite If_true. repeat rewrite If_same. rewrite If_false.
    reflexivity. }
Qed.

Lemma lemma26_13_Do_equiv_Do_isinkc3: forall m c0 c1, m = (msgo0 c0 c1 kc0) \/ m = (msgo1 c0 c1 kc1) -> c0 = c10 /\ c1 = c11 ->
   Do (decS (τ1 (FFΦΦ5 c0 c1 (encS (msgo1 c0 c1 kc1') rdd0) (encS (msgo0 c0 c1 kc0') rdd1))))
      (decS (τ2 (FFΦΦ5 c0 c1 (encS (msgo1 c0 c1 kc1') rdd0) (encS (msgo0 c0 c1 kc0') rdd1)))) m = ⫠.
Proof.
intros. simpl.
  unfold Do. unfold isinkc.
  destruct H; rewrite H.
(* isinkc1 check fails *)
  { assert (isin kc1
          (＜ π2 (π1 decS (τ1 (FFΦΦ5 c0 c1 (encS (msgo1 c0 c1 kc1') rdd0) (encS (msgo0 c0 c1 kc0') rdd1)))),
           π2 (π1 decS (τ2 (FFΦΦ5 c0 c1 (encS (msgo1 c0 c1 kc1') rdd0) (encS (msgo0 c0 c1 kc0') rdd1)))), π2 (π1 msgo0 c0 c1 kc0) ＞) = FAlse).
      unfold isin.
      rewrite Tau1Tri, Tau2Tri, Tau3Tri.
      rewrite lemma26_13_Do_equiv_Freshkc1Msgo0. rewrite lemma26_13_Do_equiv_Freshkc1o1. rewrite lemma26_13_Do_equiv_Freshkc1o2.
      repeat rewrite If_false.
      reflexivity.
      all : auto.
    rewrite H1; clear H1.
    rewrite If_false.
    unfold isin. rewrite Tau3Tri.
    unfold msgo0 at 13. rewrite proj1pair; rewrite proj2pair. rewrite ceqeq. repeat rewrite If_true. repeat rewrite If_same. rewrite If_true. repeat rewrite If_same. rewrite If_false.
    reflexivity. }
(* isinkc0 check fails *)
  { assert (isin kc0
        (＜ π2 (π1 decS (τ1 (FFΦΦ5 c0 c1 (encS (msgo1 c0 c1 kc1') rdd0) (encS (msgo0 c0 c1 kc0') rdd1)))),
         π2 (π1 decS (τ2 (FFΦΦ5 c0 c1 (encS (msgo1 c0 c1 kc1') rdd0) (encS (msgo0 c0 c1 kc0') rdd1)))), π2 (π1 msgo1 c0 c1 kc1) ＞) = FAlse).
      unfold isin.
      rewrite Tau1Tri, Tau2Tri, Tau3Tri.
      rewrite lemma26_13_Do_equiv_Freshkc0Msgo1. rewrite lemma26_13_Do_equiv_Freshkc0o1. rewrite lemma26_13_Do_equiv_Freshkc0o2.
      repeat rewrite If_false.
      reflexivity.
      all : auto.
    rewrite H1; clear H1.
    rewrite If_false.
    unfold isin. rewrite Tau3Tri.
    unfold msgo1 at 13. rewrite proj1pair; rewrite proj2pair. rewrite ceqeq. repeat rewrite If_true. repeat rewrite If_same. rewrite If_true. repeat rewrite If_same. rewrite If_false.
    reflexivity. }
Qed.



(*----------------------------------------*)

Lemma prop26_13_Do_equiv_Φ5cnxt1 :
  ContextTerm General Term  (fun x : ToL Term => (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) (encS (msgo0 c10 c11 kc0') rdd1))).
Proof.
  time ProveContext. (* 26.861 secs*)
Qed.

Lemma prop26_13_Do_equiv_msgo1 :
  ContextTerm General Term  (fun x : ToL Term => (msgo1 c10 c11 kc1)).
Proof.
  time ProveContext. (* 10.785 secs*)
Qed.


Lemma prop26_13_Do_equiv_msgo0 :
  ContextTerm General Term  (fun x : ToL Term => (msgo0 c10 c11 kc0)).
Proof.
  time ProveContext. (* 10.785 secs*)
Qed.

Lemma prop26_13_Do_equiv_msgo1' :
  ContextTerm General Term  (fun x : ToL Term => (msgo1 c10 c11 kc1')).
Proof.
  time ProveContext. (* 10.785 secs*)
Qed.


Lemma prop26_13_Do_equiv_msgo0' :
  ContextTerm General Term  (fun x : ToL Term => (msgo0 c10 c11 kc0')).
Proof.
  time ProveContext. (* 10.785 secs*)
Qed.

(**)

Lemma prop26_13_Do_equiv_cnxt1 :
  ContextTerm General Term  (fun x : ToL Term =>
  Do (decS (τ1 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) (encS (msgo0 c10 c11 kc0') rdd1)))) (decS (τ2 (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1') rdd0) (encS (msgo0 c10 c11 kc0') rdd1)))) x).
Proof.
  pose (prop26_13_Do_equiv_Φ5cnxt1).
  pose (prop26_13_Do_equiv_msgo1).
  pose (prop26_13_Do_equiv_msgo0).
  time ProveContext; try unfold dist; ProveContext.
Qed.



Lemma prop26_13_Do_equiv_cnxt2 :
  ContextTerm General Term (fun x : ToL Term => Do (msgo0 c10 c11 kc0) (msgo1 c10 c11 kc1) x).
Proof.
  pose (prop26_13_Do_equiv_Φ5cnxt1).
  pose (prop26_13_Do_equiv_msgo1).
  pose (prop26_13_Do_equiv_msgo0).
  time ProveContext; try unfold dist; ProveContext.
Qed.



(*  *)



(*----------------------------------------  Lemma_26_13.v Part_Three  --------------------------------------*)

(*  *)

Lemma prop26_13_blinding_FΦΦ3_cnxt:
 ContextTerm General Term
    (fun _ : ppt =>
     FΦΦ3 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1)
       (dv (V1 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1)) (V2 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1))
          (V3 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1))
          (S26 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1) (V3 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (m0 c10 c11 n0) rd1))))).
Proof.
  simpl.
  time ProveContext. (* 2.412 secs *)
Qed.

Lemma prop26_13_blinding_FFΦΦ5_cnxt:
 ContextTerm General Term
    (fun x : ToL Term => (FFΦΦ5 c10 c11 (encS (msgo1 c10 c11 kc1) rdd0) (encS (msgo0 c10 c11 kc0) rdd1))).
Proof.
  pose prop26_13_blinding_FΦΦ3_cnxt.
  time ProveContext. (* 4.069 secs *)
Qed.


Lemma prop26_13_blinding_FΦΦ3_cnxt':
 ContextTerm General Term
   (fun x : ppt => (FΦΦ3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)
            (dv (V1 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)) (V2 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)) (V3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1))
               (S26 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1) (V3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)))))).
Proof.
  time ProveContext. (* 3.323 secs *)
Qed.



Lemma prop26_13_blinding_FFΦΦ5_cnxt':
 ContextTerm General Term
   (fun x : ppt =>(fΦΦ5 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)
                          (dv (V1 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)) (V2 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)) (V3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1))
                             (S26 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1) (V3 c00 c01 (e0 c00 c01 n0) (e1 c00 c01 n1)))))).
Proof.
  pose prop26_13_blinding_FΦΦ3_cnxt'.
  time ProveContext. (* 3.342 secs *)
Qed.

(*--------------------------------------*)




Lemma prop26_13_swap_m0_m1_cnxt1 : 
ContextTerm General Term
    (fun acc : ppt =>
       (FΦΦ3 c10 c11 (encS (＜ ＜ c10, If acc Then ub c10 t bn0 (ti0 c10 c11) Else ⫠, n0 ＞, ph2 ＞) rd0) (e1 c10 c11 n1)
          (dvS26 c10 c11 (encS (＜ ＜ c10, If acc Then ub c10 t bn0 (ti0 c10 c11) Else ⫠, n0 ＞, ph2 ＞) rd0) (e1 c10 c11 n1)
                 (fiv3 c10 c11 (encS (＜ ＜ c10, If acc Then ub c10 t bn0 (ti0 c10 c11) Else ⫠, n0 ＞, ph2 ＞) rd0) (e1 c10 c11 n1))))).
Proof.
  ProveContext.
Qed.

Lemma prop26_13_swap_m0_m1_cnxt2 :
 ContextTerm General Term
   (fun acc : ppt => (fΦΦ5 c10 c11 (encS (＜ ＜ c10, If acc Then ub c10 t bn0 (ti0 c10 c11) Else ⫠, n0 ＞, ph2 ＞) rd0) (e1 c10 c11 n1)
                                    (dvS26 c10 c11 (encS (＜ ＜ c10, If acc Then ub c10 t bn0 (ti0 c10 c11) Else ⫠, n0 ＞, ph2 ＞) rd0) (e1 c10 c11 n1)
                                       (fiv3 c10 c11 (encS (＜ ＜ c10, If acc Then ub c10 t bn0 (ti0 c10 c11) Else ⫠, n0 ＞, ph2 ＞) rd0) (e1 c10 c11 n1))))).
Proof.
  pose prop26_13_swap_m0_m1_cnxt1.
  ProveContext.
Qed.

Lemma prop26_13_swap_m0_m1_cnxt3 :
 ContextTerm General Term
    (fun acc : ppt => (FΦΦ3 c10 c11 (encS (＜ ＜ c11, If acc Then ub c11 t bn1 (ti1 c10 c11) Else ⫠, n1 ＞, ph2 ＞) rd0) (e1 c10 c11 n1)
          (dvS26 c10 c11 (encS (＜ ＜ c11, If acc Then ub c11 t bn1 (ti1 c10 c11) Else ⫠, n1 ＞, ph2 ＞) rd0) (e1 c10 c11 n1)
             (fiv3 c10 c11 (encS (＜ ＜ c11, If acc Then ub c11 t bn1 (ti1 c10 c11) Else ⫠, n1 ＞, ph2 ＞) rd0) (e1 c10 c11 n1))))).
Proof.
  ProveContext.
Qed.
  

Lemma prop26_13_swap_m0_m1_cnxt4 :
 ContextTerm General Term
   (fun acc : ppt =>fΦΦ5 c10 c11 (encS (＜ ＜ c11, If acc Then ub c11 t bn1 (ti1 c10 c11) Else ⫠, n1 ＞, ph2 ＞) rd0) (e1 c10 c11 n1)
                          (dvS26 c10 c11 (encS (＜ ＜ c11, If acc Then ub c11 t bn1 (ti1 c10 c11) Else ⫠, n1 ＞, ph2 ＞) rd0) (e1 c10 c11 n1)
                             (fiv3 c10 c11 (encS (＜ ＜ c11, If acc Then ub c11 t bn1 (ti1 c10 c11) Else ⫠, n1 ＞, ph2 ＞) rd0) (e1 c10 c11 n1)))).
Proof.
  pose prop26_13_swap_m0_m1_cnxt3.
  ProveContext.
Qed.


Lemma prop26_13_swap_m0_m1_cnxt5 :
  ContextTerm General Term
    (fun acc : ppt => (FΦΦ3 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (＜ ＜ c10, If acc Then ub c10 t bn0 (ti0 c10 c11) Else ⫠, n0 ＞, ph2 ＞) rd1)
          (dvS26 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (＜ ＜ c10, If acc Then ub c10 t bn0 (ti0 c10 c11) Else ⫠, n0 ＞, ph2 ＞) rd1)
                 (giv3 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (＜ ＜ c10, If acc Then ub c10 t bn0 (ti0 c10 c11) Else ⫠, n0 ＞, ph2 ＞) rd1))))).
Proof.
  ProveContext.
Qed.

Lemma prop26_13_swap_m0_m1_cnxt6 :
 ContextTerm General Term
   (fun acc : ppt => fΦΦ5 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (＜ ＜ c10, If acc Then ub c10 t bn0 (ti0 c10 c11) Else ⫠, n0 ＞, ph2 ＞) rd1)
                          (dvS26 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (＜ ＜ c10, If acc Then ub c10 t bn0 (ti0 c10 c11) Else ⫠, n0 ＞, ph2 ＞) rd1)
                             (giv3 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (＜ ＜ c10, If acc Then ub c10 t bn0 (ti0 c10 c11) Else ⫠, n0 ＞, ph2 ＞) rd1)))).
Proof.
  pose prop26_13_swap_m0_m1_cnxt5.
  ProveContext.
Qed.

Lemma prop26_13_swap_m0_m1_cnxt7 :
ContextTerm General Term
    (fun acc : ppt => (FΦΦ3 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (＜ ＜ c11, If acc Then ub c11 t bn1 (ti1 c10 c11) Else ⫠, n1 ＞, ph2 ＞) rd1)
          (dvS26 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (＜ ＜ c11, If acc Then ub c11 t bn1 (ti1 c10 c11) Else ⫠, n1 ＞, ph2 ＞) rd1)
             (giv3 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (＜ ＜ c11, If acc Then ub c11 t bn1 (ti1 c10 c11) Else ⫠, n1 ＞, ph2 ＞) rd1))))).
Proof.
  ProveContext.
Qed.


  
Lemma prop26_13_swap_m0_m1_cnxt8 :
 ContextTerm General Term
   (fun acc : ppt => fΦΦ5 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (＜ ＜ c11, If acc Then ub c11 t bn1 (ti1 c10 c11) Else ⫠, n1 ＞, ph2 ＞) rd1)
                          (dvS26 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (＜ ＜ c11, If acc Then ub c11 t bn1 (ti1 c10 c11) Else ⫠, n1 ＞, ph2 ＞) rd1)
                             (giv3 c10 c11 (encS (m1 c10 c11 n1) rd0) (encS (＜ ＜ c11, If acc Then ub c11 t bn1 (ti1 c10 c11) Else ⫠, n1 ＞, ph2 ＞) rd1)))).
Proof.
  pose prop26_13_swap_m0_m1_cnxt7.
  ProveContext.
Qed.














(***************************************************************************************************)
(***************************************************************************************************)
(****************************          Lemma_26_14.v        ****************************************)
(***************************************************************************************************)
(***************************************************************************************************)






(**)

(*****************************************************************************************************************************************)

(*   *)

(* kc1 := Comk (nonce 1) *)
Lemma FreshCΦΦ5kc1_14: forall s, FreshTermcTerm (nonce (1)) (fun c => (FGΦΦ5 (c0 s) c (enco0 (c0 s) c kc0) ⫠)).
Proof.
  intros.
  time (destruct s; simpl; ProveFreshCTerm). (* 12.786 secs  *)
Qed.

Goal forall s, kc1 ≠ (π2 (π1 FGO1 (c0 s) (c1 s) (enco0 (c0 s) (c1 s) kc0) ⫠)).
Proof.
  intros.
  assert ((com (vot (op s)) kc1) = c1 s).
    destruct s; reflexivity.
  pose (@prop11 (fun x => (π2 (π1 FGO1 (c0 s) x (enco0 (c0 s) x kc0) ⫠))) (vot (op s)) 1) as cont.
    rewrite H in cont.
    apply cont.
  destruct s; simpl; ProvePPT; ProveFresh.
  pose (FreshCΦΦ5kc1_14 s); destruct s; simpl; ProveFreshCTerm.
Qed.



(**)
Lemma Freshkc1FGO1 : forall s, kc1 ≠ (π2 (π1 FGO1 (c0 s) (c1 s) (enco0 (c0 s) (c1 s) kc0) ⫠)).
Proof.
  intros.
  assert ((com (vot (op s)) kc1) = c1 s).
    destruct s; reflexivity.
  pose (@prop11 (fun x => (π2 (π1 FGO1 (c0 s) x (enco0 (c0 s) x kc0) ⫠))) (vot (op s)) 1) as cont.
    rewrite H in cont.
    apply cont.
  destruct s; simpl; ProvePPT; ProveFresh.
  pose (FreshCΦΦ5kc1_14 s); destruct s; simpl; ProveFreshCTerm.
Qed.

(**)
Lemma Freshkc1FGO2 : forall s, kc1 ≠ (π2 (π1 FGO2 (c0 s) (c1 s) (enco0 (c0 s) (c1 s) kc0) ⫠)).
Proof.
  intros.
  assert ((com (vot (op s)) kc1) = c1 s).
    destruct s; reflexivity.
  pose (@prop11 (fun x => (π2 (π1 FGO2 (c0 s) x (enco0 (c0 s) x kc0) ⫠))) (vot (op s)) 1) as cont.
    rewrite H in cont.
  apply cont.
  destruct s; simpl; ProvePPT; ProveFresh.
  pose (FreshCΦΦ5kc1_14 s).
  (destruct s; simpl; ProveFreshCTerm).
Qed.

(**)
Lemma Freshkc1FGO3 : forall s, kc1 ≠ (π2 (π1 FGO3 (c0 s) (c1 s) (enco0 (c0 s) (c1 s) kc0) ⫠)).
Proof.
  intros.
  assert ((com (vot (op s)) kc1) = c1 s).
    destruct s; reflexivity.
  pose (@prop11 (fun x => (π2 (π1 FGO3 (c0 s) x (enco0 (c0 s) x kc0) ⫠))) (vot (op s)) 1) as cont.
    rewrite H in cont.
  apply cont.
  destruct s; simpl; ProvePPT; ProveFresh.
  pose (FreshCΦΦ5kc1_14 s).
  (destruct s; simpl; time ProveFreshCTerm).
Qed.



(*--------------------------------------*)

Lemma ContextPhase5: forall s, ContextTerm General Term
    (fun b1 : ppt => (FGΦΦ5 (c0 s) (c1 s) (enco0 (c0 s) (c1 s) kc0') ⫠)).
Proof.
  time ProveContext. (*8.314 secs *)
Qed.

Lemma ContextEnco0 : forall s, ContextTerm General Term
                                      (fun b1 : ppt => (enco0 (c0 s) (c1 s) kc0')).
Proof.
  time ProveContext. (*7.289 secs*)
Qed.

Lemma ContextPhase3 : forall s, ContextTerm General Term
    (fun b1 : ppt => (fΦΦ3 (c0 s) (c1 s))).
Proof.
  time ProveContext. (*1.206*)
Qed.



(* kc0 := (Comk nonce (0)) *)
Lemma FreshCencokc0_14: forall s, FreshTermcTerm (nonce 0) (fun c => (enco0 c (c1 s) kc0')).
Proof.
  intros.
  time (destruct s; simpl; ProveFreshCTerm). (* 11.708 secs *)
Qed.

(*  *)
Lemma FreshCΦΦ5kc0_14: forall s, FreshTermcTerm (nonce 0) (fun c => (FGΦΦ5 c (c1 s) (enco0 c (c1 s) kc0') ⫠)).
Proof.
  intros.
  pose (FreshCencokc0_14 s).
  time (destruct s; simpl; ProveFreshCTerm). (* 1.944 secs   *)
Qed.

(*  *)
Lemma kc0FreshFIO1 : forall s,
    (kc0 ≠ (π2 (π1 FIO1 (c0 s) (c1 s) (enco0 (c0 s) (c1 s) kc0')))).
Proof.
  intros.
  assert ((com (vot s) kc0) = c0 s). destruct s; reflexivity.
  pose (@prop11 (fun x => (π2 (π1 FIO1 x (c1 s) (enco0 x (c1 s) kc0')))) (vot s) 0) as cont.
    rewrite H in cont. apply cont.
  destruct s; simpl; ProvePPT; ProveFresh.
  pose (FreshCencokc0_14 s).
  pose (FreshCΦΦ5kc0_14 s).
  time (destruct s; simpl; ProveFreshCTerm).
Qed.

(*  *)
Lemma kc0FreshFIO2 : forall s,
    (kc0 ≠ (π2 (π1 FIO2 (c0 s) (c1 s) (enco0 (c0 s) (c1 s) kc0')))).
Proof.
  intros.
  assert ((com (vot s) kc0) = c0 s). destruct s; reflexivity.
  pose (@prop11 (fun x => (π2 (π1 FIO2 x (c1 s) (enco0 x (c1 s) kc0')))) (vot s) 0) as cont.
    rewrite H in cont. apply cont.
  destruct s; simpl; ProvePPT; ProveFresh.
  pose (FreshCencokc0_14 s).
  pose (FreshCΦΦ5kc0_14 s).
  time (destruct s; simpl; ProveFreshCTerm).
Qed.

Lemma kc0FreshFIO3 : forall s,
    (kc0 ≠ (π2 (π1 FIO3 (c0 s) (c1 s) (enco0 (c0 s) (c1 s) kc0')))).
Proof.
  intros.
  assert ((com (vot s) kc0) = c0 s). destruct s; reflexivity.
  pose (@prop11 (fun x => (π2 (π1 FIO3 x (c1 s) (enco0 x (c1 s) kc0')))) (vot s) 0) as cont.
    rewrite H in cont. apply cont.
  destruct s; simpl; ProvePPT; ProveFresh.
  pose (FreshCencokc0_14 s).
  pose (FreshCΦΦ5kc0_14 s).
  time (destruct s; simpl; ProveFreshCTerm).
Qed.


(*  *)
Lemma CCA2BeforeΦ2: forall s, CCA2BeforeEncTerm Dec Pkey Skey [nonce (6)] [nonce (10)] (fΦ2 (c0 s) (c1 s)).
Proof.
  intros.
  time (destruct s; simpl; ProveCca2Before). (* 0.188 secs  *)
Qed.

(*  *)
Lemma CCA2BeforeΦ3: forall s, CCA2BeforeEncTerm Dec Pkey Skey [nonce (6)] [nonce (10)] (fΦΦ3 (c0 s) (c1 s)).
Proof.
  intros.
  pose (CCA2BeforeΦ2 s).
  time (destruct s; simpl; ProveCca2Before).  (* 5.541 secs => 0.973 secs *)
Qed.


(*  *)
Lemma CCA2Beforekc0_formula14: forall s, CCA2BeforeEncTerm Dec Pkey Skey [nonce (6)] [nonce (10)] (＜ ＜ label (c0 s) (fΦΦ3 (c0 s) (c1 s)), kc0 ＞, ph3 ＞).
Proof.
  intros.
  pose (CCA2BeforeΦ2 s).
  pose (CCA2BeforeΦ3 s).
  time (destruct s; simpl; ProveCca2Before). (*0.122 secs*)
Qed.

(*  *)
Lemma CCA2Beforekc0'_formula14: forall s, CCA2BeforeEncTerm Dec Pkey Skey [nonce (6)] [nonce (10)] (＜ ＜ label (c0 s) (fΦΦ3 (c0 s) (c1 s)), kc0' ＞, ph3 ＞).
Proof.
  intros.
  pose (CCA2BeforeΦ2 s).
  pose (CCA2BeforeΦ3 s).
  time (destruct s; simpl; ProveCca2Before). (*0.125 secs*)
Qed.

(*  *)
Lemma CCA2AfterΦ5: forall s, CCA2AfterEncTerm Dec Pkey Skey Error [nonce (6)] [nonce (10)]
   (fun enco0 : ppt => (FGΦΦ5 (c0 s) (c1 s) enco0 ⫠)).
Proof.
  intros. simpl.
  pose (CCA2BeforeΦ2 s) as H.
  pose (CCA2BeforeΦ3 s) as H0.
  time (destruct s; simpl; ProveCca2After).  (*0.796 secs*)
Qed.


(*  *)
Lemma CCA2AfterLemma26_formula14 : forall s, CCA2AfterEnc Dec Pkey Skey Error [nonce (6)] [nonce (10)]
   (fun enco0 : ppt =>
    [b0 (c0 s); b1 (c1 s); acc0 (c0 s) (c1 s) & acc1 (c0 s) (c1 s); bnlcheck (c0 s) n0 (fΦΦ3 (c0 s) (c1 s)); bnlcheck (c1 s) n1 (fΦΦ3 (c0 s) (c1 s));
    ＜ ＜ e0 (c0 s) (c1 s) n0, e1 (c0 s) (c1 s) n1, dv (v1 (c0 s) (c1 s)) (v2 (c0 s) (c1 s)) (v3 (c0 s) (c1 s)) (s26 (c0 s) (c1 s) (v3 (c0 s) (c1 s))) ＞,
    ＜ enco0, ⫠,
    GIDO (FIIO1 (c0 s) (c1 s) enco0 (＜ ＜ label (c0 s) (fΦΦ3 (c0 s) (c1 s)), kc0 ＞, ph3 ＞)) (FIIO2 (c0 s) (c1 s) enco0 (＜ ＜ label (c0 s) (fΦΦ3 (c0 s) (c1 s)), kc0 ＞, ph3 ＞))
      (FIIO3 (c0 s) (c1 s) enco0 (＜ ＜ label (c0 s) (fΦΦ3 (c0 s) (c1 s)), kc0 ＞, ph3 ＞)) ＞ ＞]).
Proof.
  intros. simpl.
  pose (CCA2BeforeΦ2 s) as H.
  pose (CCA2BeforeΦ3 s) as H0.
  pose (CCA2AfterΦ5 s) as H1.
  time (destruct s; simpl; ProveCca2After). (* 6.767 secs*)
Qed.



(*  *)
Lemma Freshc_kc0_enco0_14:
  FreshTermc (nonce 0)
    (fun lx : list ppt =>
     let c0 := Nth 0 lx in
     let c1 := Nth 1 lx in enco0 c0 c1 kc0').
Proof.
  simpl.
  time ProveFreshC. (*4.595 secs*)
Qed.


(*  *)
Lemma Freshc_kc0_phase5_14:
  FreshTermc (nonce 0)
    (fun lx : list ppt =>
     let c0 := Nth 0 lx in
     let c1 := Nth 1 lx in (FGΦΦ5 (Nth 0 lx) (Nth 1 lx) (enco0 (Nth 0 lx) (Nth 1 lx) kc0') ⫠)).
Proof.
  simpl.
  pose Freshc_kc0_enco0_14.
  time ProveFreshC. (*0.756 secs*)
Qed.


(*  *)
Lemma Freshc_kc0_Lemma26_14:
  Freshc (nonce 0)
    (fun lx : list ppt =>
     let c0 := Nth 0 lx in
     let c1 := Nth 1 lx in
     [b0 c0; b1 c1; acc0 c0 c1 & acc1 c0 c1; bnlcheck c0 n0 (fΦΦ3 c0 c1); bnlcheck c1 n1 (fΦΦ3 c0 c1);
     ＜ ＜ e0 c0 c1 n0, e1 c0 c1 n1, dv (v1 c0 c1) (v2 c0 c1) (v3 c0 c1) (s26 c0 c1 (v3 c0 c1)) ＞,
     ＜ enco0 c0 c1 kc0', ⫠, FDO (FIO1 c0 c1 (enco0 c0 c1 kc0')) (FIO2 c0 c1 (enco0 c0 c1 kc0')) (FIO3 c0 c1 (enco0 c0 c1 kc0')) ＞ ＞]).
Proof.
  simpl.
  pose (Freshc_kc0_enco0_14).
  pose (Freshc_kc0_phase5_14).
  time ProveFreshC. (*24.831 secs *)
Qed.


(*  *)
Lemma Freshc_kc1_enco0_14:
  FreshTermc (nonce 1)
    (fun lx : list ppt =>
     let c0 := Nth 0 lx in
     let c1 := Nth 1 lx in enco0 c0 c1 kc0').
Proof.
  simpl.
  time ProveFreshC. (*4.372 secs*)
Qed.


(*  *)
Lemma Freshc_kc1_phase5_14:
  FreshTermc (nonce 1)
    (fun lx : list ppt =>
     let c0 := Nth 0 lx in
     let c1 := Nth 1 lx in (FGΦΦ5 (Nth 0 lx) (Nth 1 lx) (enco0 (Nth 0 lx) (Nth 1 lx) kc0') ⫠)).
Proof.
  simpl.
  pose Freshc_kc1_enco0_14.
  time ProveFreshC. (*0.756 secs*)
Qed.


(*  *)
Lemma Freshc_kc1_Lemma26_14:
 Freshc (nonce 1)
   (fun lx : list ppt =>
    let c0 := Nth 0 lx in
    let c1 := Nth 1 lx in
    [b0 c0; b1 c1; acc0 c0 c1 & acc1 c0 c1; bnlcheck c0 n0 (fΦΦ3 c0 c1); bnlcheck c1 n1 (fΦΦ3 c0 c1);
    ＜ ＜ e0 c0 c1 n0, e1 c0 c1 n1, dv (v1 c0 c1) (v2 c0 c1) (v3 c0 c1) (s26 c0 c1 (v3 c0 c1)) ＞,
    ＜ enco0 c0 c1 kc0', ⫠, FDO (FIO1 c0 c1 (enco0 c0 c1 kc0')) (FIO2 c0 c1 (enco0 c0 c1 kc0')) (FIO3 c0 c1 (enco0 c0 c1 kc0')) ＞ ＞]).
Proof.
  simpl.
  pose (Freshc_kc1_enco0_14).
  pose (Freshc_kc1_phase5_14).
  time ProveFreshC. (*23.742 secs *)
Qed.
















(***************************************************************************************************)
(***************************************************************************************************)
(****************************          Lemma_26_15.v        ****************************************)
(***************************************************************************************************)
(***************************************************************************************************)




(*  *)
Lemma FreshCΦΦ5kc0_15: forall s, FreshTermcTerm (nonce 0) (fun c => (FGΦΦ5 c (c1 s) ⫠ (enco1 c (c1 s) kc1))).
Proof.
  intros.
  time (destruct s; simpl; ProveFreshCTerm). (* 12.786 secs  *)
Qed.

(*  *)
Lemma Freshkc0FGO1_15 : forall s, kc0 ≠ (π2 (π1 FGO1 (c0 s) (c1 s) ⫠ (enco1 (c0 s) (c1 s) kc1))).
Proof.
  intros.
  assert ((com (vot s) kc0) = c0 s).
    destruct s; reflexivity.
  pose (@prop11 (fun x => (π2 (π1 FGO1 x (c1 s) ⫠ (enco1 x (c1 s) kc1)))) (vot s) 0) as cont.
    rewrite H in cont.
  apply cont.
  destruct s; simpl; ProvePPT; ProveFresh.
  pose (FreshCΦΦ5kc0_15 s).
  (destruct s; simpl; ProveFreshCTerm).
Qed.


(*  *)
Lemma Freshkc0FGO2_15 : forall s, kc0 ≠ (π2 (π1 FGO2 (c0 s) (c1 s) ⫠ (enco1 (c0 s) (c1 s) kc1))).
Proof.
  intros.
  assert ((com (vot s) kc0) = c0 s).
    destruct s; reflexivity.
  pose (@prop11 (fun x => (π2 (π1 FGO2 x (c1 s) ⫠ (enco1 x (c1 s) kc1)))) (vot s) 0) as cont.
    rewrite H in cont.
  apply cont.
  destruct s; simpl; ProvePPT; ProveFresh.
  pose (FreshCΦΦ5kc0_15 s).
  (destruct s; simpl; ProveFreshCTerm).
Qed.


(*  *)
Lemma Freshkc0FGO3_15 : forall s, kc0 ≠ (π2 (π1 FGO3 (c0 s) (c1 s) ⫠ (enco1 (c0 s) (c1 s) kc1))).
Proof.
  intros.
  assert ((com (vot s) kc0) = c0 s).
    destruct s; reflexivity.
  pose (@prop11 (fun x => (π2 (π1 FGO3 x (c1 s) ⫠ (enco1 x (c1 s) kc1)))) (vot s) 0) as cont.
    rewrite H in cont.
  apply cont.
  destruct s; simpl; ProvePPT; ProveFresh.
  pose (FreshCΦΦ5kc0_15 s).
  (destruct s; simpl; ProveFreshCTerm).
Qed.


(*  *)
Lemma ContextPhase5_15: forall s, ContextTerm General Term
    (fun b1 : ppt => (FGΦΦ5 (c0 s) (c1 s) ⫠ (enco1 (c0 s) (c1 s) kc1'))).
Proof.
  time ProveContext. (*4.972 secs *)
Qed.

(*  *)
Lemma ContextEnco1 : forall s, ContextTerm General Term
     (fun b1 : ppt => (enco1 (c0 s) (c1 s) kc1')).
Proof.
  time ProveContext. (* 4.154 secs*)
Qed.

(**)
Lemma ContextPhase3_15 : forall s, ContextTerm General Term
    (fun b1 : ppt => (fΦΦ3 (c0 s) (c1 s))).
Proof.
  time ProveContext. (*1.206*)
Qed.

(*  *)
Lemma FreshCencokc1_15: forall s, FreshTermcTerm (nonce 1) (fun c => (enco1 (c0 s) c kc1')).
Proof.
  intros.
  time (destruct s; simpl; ProveFreshCTerm). (* 11.163 secs *)
Qed.


(*  *)
Lemma FreshCΦΦ5kc1_15: forall s, FreshTermcTerm (nonce 1) (fun c  => (FGΦΦ5 (c0 s) c ⫠ (enco1 (c0 s) c kc1'))).
Proof.
  intros.
  pose (FreshCencokc1_15 s).
  time (destruct s; simpl; ProveFreshCTerm). (* 1.944 secs   *)
Qed.

(*  *)
Lemma kc1FreshGIO1 : forall s,
    (kc1 ≠ (π2 (π1 GIO1 (c0 s) (c1 s) (enco1 (c0 s) (c1 s) kc1')))).
Proof.
  intros.
  assert ((com (vot (op s)) kc1) = c1 s). destruct s; reflexivity.
  pose (@prop11 (fun x => (π2 (π1 GIO1 (c0 s) x (enco1 (c0 s) x kc1')))) (vot (op s)) 1) as cont.
    rewrite H in cont. apply cont.
  destruct s; simpl; ProvePPT; ProveFresh.
  pose (FreshCencokc1_15 s).
  pose (FreshCΦΦ5kc1_15 s).
  (destruct s; simpl; ProveFreshCTerm).
Qed.

(*  *)
Lemma kc1FreshGIO2 : forall s,
    (kc1 ≠ (π2 (π1 GIO2 (c0 s) (c1 s) (enco1 (c0 s) (c1 s) kc1')))).
Proof.
  intros.
  assert ((com (vot (op s)) kc1) = c1 s). destruct s; reflexivity.
  pose (@prop11 (fun x => (π2 (π1 GIO2 (c0 s) x (enco1 (c0 s) x kc1')))) (vot (op s)) 1) as cont.
    rewrite H in cont. apply cont.
  destruct s; simpl; ProvePPT; ProveFresh.
  pose (FreshCencokc1_15 s).
  pose (FreshCΦΦ5kc1_15 s).
  (destruct s; simpl; ProveFreshCTerm).
Qed.

(*  *)
Lemma kc1FreshGIO3 : forall s,
    (kc1 ≠ (π2 (π1 GIO3 (c0 s) (c1 s) (enco1 (c0 s) (c1 s) kc1')))).
Proof.
  intros.
  assert ((com (vot (op s)) kc1) = c1 s). destruct s; reflexivity.
  pose (@prop11 (fun x => (π2 (π1 GIO3 (c0 s) x (enco1 (c0 s) x kc1')))) (vot (op s)) 1) as cont.
    rewrite H in cont. apply cont.
  destruct s; simpl; ProvePPT; ProveFresh.
  pose (FreshCencokc1_15 s).
  pose (FreshCΦΦ5kc1_15 s).
  (destruct s; simpl; ProveFreshCTerm).
Qed.

(*  *)
Lemma CCA2BeforeΦ2_15: forall s, CCA2BeforeEncTerm Dec Pkey Skey [nonce (6)] [nonce (11)] (fΦ2 (c0 s) (c1 s)).
Proof.
  intros.
  time (destruct s; simpl; ProveCca2Before). (* 0.188 secs  *)
Qed.

(*  *)
Lemma CCA2BeforeΦ3_15: forall s, CCA2BeforeEncTerm Dec Pkey Skey [nonce (6)] [nonce (11)] (fΦΦ3 (c0 s) (c1 s)).
Proof.
  intros.
  pose (CCA2BeforeΦ2_15 s).
  time (destruct s; simpl; ProveCca2Before).  (* 0.973 secs *)
Qed.

Lemma CCA2Beforekc1_formula15: forall s, CCA2BeforeEncTerm Dec Pkey Skey [nonce (6)] [nonce (11)] (＜ ＜ label (c1 s) (fΦΦ3 (c0 s) (c1 s)), kc1 ＞, ph3 ＞).
Proof.
  intros.
  pose (CCA2BeforeΦ2_15 s).
  pose (CCA2BeforeΦ3_15 s).
  time (destruct s; simpl; ProveCca2Before). (*0.122 secs*)
Qed.

Lemma CCA2Beforekc1'_formula15: forall s, CCA2BeforeEncTerm Dec Pkey Skey [nonce (6)] [nonce (11)] (＜ ＜ label (c1 s) (fΦΦ3 (c0 s) (c1 s)), kc1' ＞, ph3 ＞).
Proof.
  intros.
  pose (CCA2BeforeΦ2_15 s).
  pose (CCA2BeforeΦ3_15 s).
  time (destruct s; simpl; ProveCca2Before). (*0.125 secs*)
Qed.



(*  *)
Lemma CCA2AfterΦ5_15: forall s, CCA2AfterEncTerm Dec Pkey Skey Error [nonce (6)] [nonce (11)]
   (fun enco1 : ppt => (FGΦΦ5 (c0 s) (c1 s) ⫠ enco1)).
Proof.
  intros. simpl.
  pose (CCA2BeforeΦ2_15 s) as H.
  pose (CCA2BeforeΦ3_15 s) as H0.
  time (destruct s; simpl; ProveCca2After).  (*0.796 secs*)
Qed.

(*  *)
Lemma CCA2AfterLemma26_formula15 : forall s, CCA2AfterEnc Dec Pkey Skey Error [nonce (6)] [nonce (11)]
   (fun enco1 : ppt =>
    [b0 (c0 s); b1 (c1 s); acc0 (c0 s) (c1 s) & acc1 (c0 s) (c1 s); bnlcheck (c0 s) n0 (fΦΦ3 (c0 s) (c1 s)); bnlcheck (c1 s) n1 (fΦΦ3 (c0 s) (c1 s));
    ＜ ＜ e0 (c0 s) (c1 s) n0, e1 (c0 s) (c1 s) n1, dv (v1 (c0 s) (c1 s)) (v2 (c0 s) (c1 s)) (v3 (c0 s) (c1 s)) (s26 (c0 s) (c1 s) (v3 (c0 s) (c1 s))) ＞,
    ＜ ⫠, enco1,
    FIDO (GIIO1 (c0 s) (c1 s) enco1 (＜ ＜ label (c1 s) (fΦΦ3 (c0 s) (c1 s)), kc1 ＞, ph3 ＞)) (GIIO2 (c0 s) (c1 s) enco1 (＜ ＜ label (c1 s) (fΦΦ3 (c0 s) (c1 s)), kc1 ＞, ph3 ＞))
      (GIIO3 (c0 s) (c1 s) enco1 (＜ ＜ label (c1 s) (fΦΦ3 (c0 s) (c1 s)), kc1 ＞, ph3 ＞)) ＞ ＞]).
Proof.
  intros. simpl.
  pose (CCA2BeforeΦ2_15 s) as H.
  pose (CCA2BeforeΦ3_15 s) as H0.
  pose (CCA2AfterΦ5_15 s) as H1.
  time (destruct s; simpl; ProveCca2After). (* 13.334  secs*)
Qed.


(* use cmd + shift + L *)
Lemma Freshc_kc1_enco1_15:
  FreshTermc (nonce 1)
    (fun lx : list ppt =>
     let c0 := Nth 0 lx in
     let c1 := Nth 1 lx in enco1 c0 c1 kc1').
Proof.
  simpl.
  time ProveFreshC. (*4.24 secs*)
Qed.

(*  *)
Lemma Freshc_kc1_phase5_15:
  FreshTermc (nonce 1)
    (fun lx : list ppt =>
     let c0 := Nth 0 lx in
     let c1 := Nth 1 lx in (FGΦΦ5 (Nth 0 lx) (Nth 1 lx) ⫠ (enco1 (Nth 0 lx) (Nth 1 lx) kc1'))).
Proof.
  simpl.
  pose Freshc_kc1_enco1_15.
  time ProveFreshC. (*0.756 secs*)
Qed.

(*  *)
Lemma Freshc_kc1_Lemma26_15:
  Freshc (nonce 1)
    (fun lx : list ppt =>
     let c0 := Nth 0 lx in
     let c1 := Nth 1 lx in
     [b0 c0; b1 c1; acc0 c0 c1 & acc1 c0 c1; bnlcheck c0 n0 (fΦΦ3 c0 c1); bnlcheck c1 n1 (fΦΦ3 c0 c1);
     ＜ ＜ e0 c0 c1 n0, e1 c0 c1 n1, dv (v1 c0 c1) (v2 c0 c1) (v3 c0 c1) (s26 c0 c1 (v3 c0 c1)) ＞,
     ＜ ⫠, enco1 c0 c1 kc1', FDO (GIO1 c0 c1 (enco1 c0 c1 kc1')) (GIO2 c0 c1 (enco1 c0 c1 kc1')) (GIO3 c0 c1 (enco1 c0 c1 kc1')) ＞ ＞]).
Proof.
  simpl.
  pose (Freshc_kc1_enco1_15).
  pose (Freshc_kc1_phase5_15).
  time ProveFreshC. (* 25.956 secs *)
Qed.

(*  *)
Lemma Freshc_kc0_enco1_15:
  FreshTermc (nonce 0)
    (fun lx : list ppt =>
     let c0 := Nth 0 lx in
     let c1 := Nth 1 lx in enco1 c0 c1 kc1').
Proof.
  simpl.
  time ProveFreshC. (*4.372 secs*)
Qed.

(*  *)
Lemma Freshc_kc0_phase5_15:
  FreshTermc (nonce 0)
    (fun lx : list ppt =>
     let c0 := Nth 0 lx in
     let c1 := Nth 1 lx in (FGΦΦ5 (Nth 0 lx) (Nth 1 lx) ⫠ (enco1 (Nth 0 lx) (Nth 1 lx) kc1'))).
Proof.
  simpl.
  pose Freshc_kc0_enco1_15.
  time ProveFreshC. (*0.783 secs *)
Qed.

(*  *)
Lemma Freshc_kc0_Lemma26_15:
 Freshc (nonce 0)
   (fun lx : list ppt =>
    let c0 := Nth 0 lx in
    let c1 := Nth 1 lx in
    [b0 c0; b1 c1; acc0 c0 c1 & acc1 c0 c1; bnlcheck c0 n0 (fΦΦ3 c0 c1); bnlcheck c1 n1 (fΦΦ3 c0 c1);
    ＜ ＜ e0 c0 c1 n0, e1 c0 c1 n1, dv (v1 c0 c1) (v2 c0 c1) (v3 c0 c1) (s26 c0 c1 (v3 c0 c1)) ＞,
    ＜ ⫠, enco1 c0 c1 kc1', FDO (GIO1 c0 c1 (enco1 c0 c1 kc1')) (GIO2 c0 c1 (enco1 c0 c1 kc1')) (GIO3 c0 c1 (enco1 c0 c1 kc1')) ＞ ＞]).
Proof.
  simpl.
  pose (Freshc_kc0_enco1_15).
  pose (Freshc_kc0_phase5_15).
  time ProveFreshC. (*30.506 secs  *)
Qed.
























(***************************************************************************************************)
(***************************************************************************************************)
(****************************          Lemma_26_16.v        ****************************************)
(***************************************************************************************************)
(***************************************************************************************************)



(****************************************************************************************************************************************)
(*  *)
Lemma FreshCΦΦ5kc0_16: forall s, FreshTermcTerm (nonce 0) (fun c => (FGΦΦ5 c (c1 s) ⫠ ⫠)).
Proof.
  intros.
  time (destruct s; simpl; ProveFreshCTerm). (* 2.032 secs *)
Qed.

(*  *)
Lemma Freshkc0FGO1_16 : forall s, kc0 ≠ (π2 (π1 FGO1 (c0 s) (c1 s) ⫠ ⫠)).
Proof.
  intros.
  assert ((com (vot s) kc0) = c0 s).
    destruct s; reflexivity.
  pose (@prop11 (fun x => (π2 (π1 FGO1 x (c1 s) ⫠ ⫠))) (vot s) 0) as cont.
    rewrite H in cont.
  apply cont.
  destruct s; simpl; ProvePPT; ProveFresh.
  pose (FreshCΦΦ5kc0_16 s).
  (destruct s; simpl; ProveFreshCTerm).
Qed.


(*  *)
Lemma Freshkc0FGO2_16 : forall s, kc0 ≠ (π2 (π1 FGO2 (c0 s) (c1 s) ⫠ ⫠)).
Proof.
  intros.
  assert ((com (vot s) kc0) = c0 s).
    destruct s; reflexivity.
  pose (@prop11 (fun x => (π2 (π1 FGO2 x (c1 s) ⫠ ⫠))) (vot s) 0) as cont.
    rewrite H in cont.
  apply cont.
  destruct s; simpl; ProvePPT; ProveFresh.
  pose (FreshCΦΦ5kc0_16 s).
  (destruct s; simpl; ProveFreshCTerm).
Qed.


(*  *)
Lemma Freshkc0FGO3_16 : forall s, kc0 ≠ (π2 (π1 FGO3 (c0 s) (c1 s) ⫠ ⫠)).
Proof.
  intros.
  assert ((com (vot s) kc0) = c0 s).
    destruct s; reflexivity.
  pose (@prop11 (fun x => (π2 (π1 FGO3 x (c1 s) ⫠ ⫠))) (vot s) 0) as cont.
    rewrite H in cont.
  apply cont.
  destruct s; simpl; ProvePPT; ProveFresh.
  pose (FreshCΦΦ5kc0_16 s).
  (destruct s; simpl; ProveFreshCTerm).
Qed.



(*-----------------------------------------*)

(* *)
Lemma FreshCΦΦ5kc1_16: forall s, FreshTermcTerm (nonce (1)) (fun c => (FGΦΦ5 (c0 s) c ⫠ ⫠)).
Proof.
  intros.
  time (destruct s; simpl; ProveFreshCTerm). (* 2.312 secs  *)
Qed.

(**)
Lemma Freshkc1FGO1_16 : forall s, kc1 ≠ (π2 (π1 FGO1 (c0 s) (c1 s) ⫠ ⫠)).
Proof.
  intros.
  assert ((com (vot (op s)) kc1) = c1 s).
    destruct s; reflexivity.
  pose (@prop11 (fun x => (π2 (π1 FGO1 (c0 s) x ⫠ ⫠))) (vot (op s)) 1) as cont.
    rewrite H in cont.
    apply cont.
  destruct s; simpl; ProvePPT; ProveFresh.
  pose (FreshCΦΦ5kc1_16 s); destruct s; simpl; ProveFreshCTerm.
Qed.

(**)
Lemma Freshkc1FGO2_16 : forall s, kc1 ≠ (π2 (π1 FGO2 (c0 s) (c1 s) ⫠ ⫠)).
Proof.
  intros.
  assert ((com (vot (op s)) kc1) = c1 s).
    destruct s; reflexivity.
  pose (@prop11 (fun x => (π2 (π1 FGO2 (c0 s) x ⫠ ⫠))) (vot (op s)) 1) as cont.
    rewrite H in cont.
  apply cont.
  destruct s; simpl; ProvePPT; ProveFresh.
  pose (FreshCΦΦ5kc1_16 s).
  (destruct s; simpl; ProveFreshCTerm).
Qed.

(**)
Lemma Freshkc1FGO3_16 : forall s, kc1 ≠ (π2 (π1 FGO3 (c0 s) (c1 s) ⫠ ⫠)).
Proof.
  intros.
  assert ((com (vot (op s)) kc1) = c1 s).
    destruct s; reflexivity.
  pose (@prop11 (fun x => (π2 (π1 FGO3 (c0 s) x ⫠ ⫠))) (vot (op s)) 1) as cont.
    rewrite H in cont.
  apply cont.
  destruct s; simpl; ProvePPT; ProveFresh.
  pose (FreshCΦΦ5kc1_16 s).
  (destruct s; simpl; time ProveFreshCTerm).
Qed.

(*-----------------------------------------*)

(*  *)
Lemma Freshc_kc0_phase5_16:
  FreshTermc (nonce 0)
    (fun lx : list ppt =>
     let c0 := Nth 0 lx in
     let c1 := Nth 1 lx in (FGΦΦ5 (Nth 0 lx) (Nth 1 lx) ⫠ ⫠)).
Proof.
  simpl.
  time ProveFreshC. (*0.756 secs*)
Qed.

Lemma Freshc_kc0_Lemma26_16:
  Freshc nonce (0)
    (fun lx : list ppt =>
     let c0 := Nth 0 lx in
     let c1 := Nth 1 lx in
     [b0 c0; b1 c1; acc0 c0 c1 & acc1 c0 c1; bnlcheck c0 n0 (fΦΦ3 c0 c1); bnlcheck c1 n1 (fΦΦ3 c0 c1);
     ＜ ＜ e0 c0 c1 n0, e1 c0 c1 n1, dv (v1 c0 c1) (v2 c0 c1) (v3 c0 c1) (s26 c0 c1 (v3 c0 c1)) ＞, ＜ ⫠, ⫠, FDO (FGO1 c0 c1 ⫠ ⫠) (FGO2 c0 c1 ⫠ ⫠) (FGO3 c0 c1 ⫠ ⫠) ＞ ＞]).
Proof.
  simpl.
  pose (Freshc_kc0_phase5_16).
  time ProveFreshC. (* 27.2 secs *)
Qed.


(*  *)
Lemma Freshc_kc1_phase5_16:
  FreshTermc (nonce 1)
    (fun lx : list ppt =>
     let c0 := Nth 0 lx in
     let c1 := Nth 1 lx in (FGΦΦ5 (Nth 0 lx) (Nth 1 lx) ⫠ ⫠)).
Proof.
  simpl.
  time ProveFreshC. (*0.756 secs*)
Qed.


Lemma Freshc_kc1_Lemma26_16:
 Freshc nonce (1)
   (fun lx : list ppt =>
    let c0 := Nth 0 lx in
    let c1 := Nth 1 lx in
    [b0 c0; b1 c1; acc0 c0 c1 & acc1 c0 c1; bnlcheck c0 n0 (fΦΦ3 c0 c1); bnlcheck c1 n1 (fΦΦ3 c0 c1);
    ＜ ＜ e0 c0 c1 n0, e1 c0 c1 n1, dv (v1 c0 c1) (v2 c0 c1) (v3 c0 c1) (s26 c0 c1 (v3 c0 c1)) ＞, ＜ ⫠, ⫠, FDO (FGO1 c0 c1 ⫠ ⫠) (FGO2 c0 c1 ⫠ ⫠) (FGO3 c0 c1 ⫠ ⫠) ＞ ＞]).
Proof.
  simpl.
  pose (Freshc_kc1_phase5_16).
  time ProveFreshC. (*23.742 secs *)
Qed.
























(***************************************************************************************************)
(***************************************************************************************************)
(****************************          Lemma_26.v        *******************************************)
(***************************************************************************************************)
(***************************************************************************************************)


(***********************************************************************************************************************************************************)
Lemma lemma26_bnl0_Φ3_Cnxt_rhs: 
  ContextTerm General Term
              (fun bnl0 : ppt => (fΦΦ3 c10 c11)).
Proof.
  time ProveContext. (* 1.279 secs *)
Qed.


Lemma lemma26_bnl0_bot_Φ5_Cnxt_rhs: 
  ContextTerm General Term
    (fun bnl0 : ppt => (FGΦΦ5 c10 c11 (If bnl0 Then enco0 c10 c11 kc0 Else ⫠) ⫠)).
Proof.
  pose lemma26_bnl0_Φ3_Cnxt_rhs.
  time ProveContext. (* 1.366 secs *)
Qed.


Lemma lemma26_bnl0_enco1_Φ5_Cnxt_rhs: 
ContextTerm General Term
    (fun bnl0 : ppt =>(FGΦΦ5 c10 c11 (If bnl0 Then enco0 c10 c11 kc0 Else ⫠) (enco1 c10 c11 kc1))).
Proof.
  simpl.
  pose lemma26_bnl0_Φ3_Cnxt_rhs.
  time ProveContext. (* 72.488 secs *)
Qed.


(*---------------------------------*)
  
Lemma lemma26_bnl0_Φ3_Cnxt_lhs: 
  ContextTerm General Term
              (fun bnl0 : ppt => (fΦΦ3 c00 c01)).
Proof.
  time ProveContext. (* 1.279 secs *)
Qed.


Lemma lemma26_bnl0_bot_Φ5_Cnxt_lhs: 
  ContextTerm General Term
    (fun bnl0 : ppt => (FGΦΦ5 c00 c01 (If bnl0 Then enco0 c00 c01 kc0 Else ⫠) ⫠)).
Proof.
  pose lemma26_bnl0_Φ3_Cnxt_lhs.
  time ProveContext. (* 1.366 secs *)
Qed.


Lemma lemma26_bnl0_enco1_Φ5_Cnxt_lhs: 
ContextTerm General Term
    (fun bnl0 : ppt =>(FGΦΦ5 c00 c01 (If bnl0 Then enco0 c00 c01 kc0 Else ⫠) (enco1 c00 c01 kc1))).
Proof.
  simpl.
  pose lemma26_bnl0_Φ3_Cnxt_lhs.
  time ProveContext. (* 1.397 *)
Qed.

(*---------------------------------*)

Lemma lemma26_bnl1_enco0_Φ5_Cnxt_rhs: 
ContextTerm General Term
    (fun bnl1 : ppt => (FGΦΦ5 c10 c11
                (If bcheck c10 n0 &
                    (| label c10 (fΦΦ3 c10 c11) | ≟ llbl) &
                    ((n0 ≟ τ1 (＜ τ3 (π2 τ1 (fΦΦ3 c10 c11)), τ3 (π2 τ2 (fΦΦ3 c10 c11)), τ3 (π2 τ3 (fΦΦ3 c10 c11)) ＞))
                     or (n0 ≟ τ2 (＜ τ3 (π2 τ1 (fΦΦ3 c10 c11)), τ3 (π2 τ2 (fΦΦ3 c10 c11)), τ3 (π2 τ3 (fΦΦ3 c10 c11)) ＞))
                        or (n0 ≟ τ3 (＜ τ3 (π2 τ1 (fΦΦ3 c10 c11)), τ3 (π2 τ2 (fΦΦ3 c10 c11)), τ3 (π2 τ3 (fΦΦ3 c10 c11)) ＞))) Then enco0 c10 c11 kc0 Else ⫠)
                (If bnl1 Then enco1 c10 c11 kc1 Else ⫠))).
Proof.
  simpl.
  pose lemma26_bnl0_Φ3_Cnxt_rhs.
  time ProveContext. (*2.054 secs *)
Qed.

(*---------------------------------*)
Lemma lemma26_bnl1_enco0_Φ5_Cnxt_lhs: 
ContextTerm General Term
    (fun bnl1 : ppt => (FGΦΦ5 c00 c01
               (If bcheck c00 n0 &
                   (| label c00 (fΦΦ3 c00 c01) | ≟ llbl) &
                   ((n0 ≟ τ1 (＜ τ3 (π2 τ1 (fΦΦ3 c00 c01)), τ3 (π2 τ2 (fΦΦ3 c00 c01)), τ3 (π2 τ3 (fΦΦ3 c00 c01)) ＞))
                    or (n0 ≟ τ2 (＜ τ3 (π2 τ1 (fΦΦ3 c00 c01)), τ3 (π2 τ2 (fΦΦ3 c00 c01)), τ3 (π2 τ3 (fΦΦ3 c00 c01)) ＞))
                       or (n0 ≟ τ3 (＜ τ3 (π2 τ1 (fΦΦ3 c00 c01)), τ3 (π2 τ2 (fΦΦ3 c00 c01)), τ3 (π2 τ3 (fΦΦ3 c00 c01)) ＞))) Then enco0 c00 c01 kc0 Else ⫠)
               (If bnl1 Then enco1 c00 c01 kc1 Else ⫠))).
Proof.
  simpl.
  pose lemma26_bnl0_Φ3_Cnxt_lhs.
  time ProveContext. (*2.054 secs *)
Qed.

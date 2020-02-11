Lemma hilbertS (A B C : Prop) :  (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
intro abc.
intro ab.
intro a.
apply abc.
  - exact a.
  - apply ab.
    exact a.
Qed.

Lemma q2 (A B : Prop) :  A -> (B -> A).
Proof.
intro a.
intro b.
exact a.
Qed.

Lemma q3 (A B : Prop) :  A -> (~A -> B).
Proof.
intro a.
intro na.
destruct na.
exact a.
Qed.

Lemma q31 (A B : Prop) :  A -> (~A -> B).
Proof.
intro a.
intro na.
exfalso.
apply na.
exact a.
Qed.

Lemma q4 (A B C : Prop) :  (A -> B) -> ((B -> C) -> (A -> C)).
Proof.
intro ab.
intro bc.
intro a.
apply bc.
apply ab.
exact a.
Qed.

Lemma q5 (A B : Prop) :  (A -> B) -> (~B -> ~A).
Proof.
intro ab.
intro nb.
intro a.
apply nb.
apply ab.
exact a.
Qed.

Require Import Classical.


Lemma tiersexclus (A : Prop) : A \/ ~A.
Proof.
apply NNPP.
intro nonAOuNonA.
apply nonAOuNonA.
right.
intro a.
apply nonAOuNonA.
left.
exact a.
Qed.


Lemma bottom_c (A : Prop) : (~A -> False) -> A.
Proof.
intro afalse.
apply NNPP.
intro na.
apply afalse.
exact na.
Qed.

Lemma q8 (A B : Prop) : (~B -> ~A) -> (A -> B).
Proof.
intro nbna.
intro a.
apply NNPP.
intro nb.
apply nbna.
- exact nb.
- exact a.
Qed.

Lemma q9 (A : Prop) : ~~A <-> A.
Proof.
split.
  - intro a.
    apply NNPP.
    exact a.
  - intro a.
    intro na.
    apply na.
    exact a.
Qed.

Lemma q10 (A : Prop) :  (A /\ ~A) <-> False.
Proof.
split.
  - intro ana.
    apply ana.
    destruct ana as [a na].
    exact a.
  - intro f.
    split.
      * destruct f.
      * destruct f. 
Qed.

Lemma q11 (A B : Prop) :  (A \/ B) <-> ~(~A /\ ~B).
Proof.
(*split.
  - intro a_ou_b.
    intro na_et_nb.
    destruct a_ou_b as [a | b].
      * destruct na_et_nb as [na nb].
        apply na.
        exact a.
      * destruct na_et_nb as [na nb].
        apply nb.
        exact b.
  - intro nna_et_nb.(*
    left.
    apply NNPP.
    intro na.
    destruct nna_et_nb.
    split.
      * exact na.
      *
*)*)
split.
  - intro a_ou_b.
    intro na_et_nb.
    destruct na_et_nb as [na nb].
    destruct a_ou_b as [a|b].
      * apply na.
        exact a.
      * apply nb.
        exact b.
  - intro nna_et_nb.
    apply NNPP.
    intro n_a_ou_b.
    apply nna_et_nb.
    split.
      * intro a.
        apply n_a_ou_b.
        left.
        exact a.
      * intro b.
        apply n_a_ou_b.
        right.
        exact b.
Qed.


Lemma q12 (A : Prop) :  ~A <-> (A -> False).
Proof.
split.
  - intro na.
    intro a.
    apply na.
    exact a.
  - intro a_imp_f.
    intro a.
    apply a_imp_f.
    exact a.
Qed.

Lemma q13 (A B : Prop) :  (A <-> B) <-> (A -> B) /\ (B -> A).
Proof.
split.
  - split.
    * intro a.
      apply H.
      exact a.
    * intro b.
      apply H.
      exact b.
  - split.
    * intro a.
      apply H.
      exact a.
    * intro b.
      apply H.
      exact b.
Qed.

Lemma q14 (A B C : Prop) :  (A /\ B -> C) <-> (A -> B -> C).
Proof.
split.
  - intro a_et_b_imp_c.
    intro a.
    intro b.
    apply a_et_b_imp_c.
    split.
      * exact a.
      * exact b.
  - intro a_imp_b_imp_c.
    intro a_et_b.
    destruct a_et_b as [a b].
    apply a_imp_b_imp_c.
      * exact a.
      * exact b.
Qed.

Lemma q15 (A B C : Prop) :  (C -> A)\/ (C -> B) <-> (C -> A \/ B).
Proof.
split.
  - intro c_imp_a_ou_c_imp_b.
    destruct c_imp_a_ou_c_imp_b as [c_imp_a | c_imp_b].
      * intro c.
        left.
        apply c_imp_a.
        exact c.
      * intro c.
        right.
        apply c_imp_b.
        exact c.
  - intro c_imp_a_ou_b.
    apply NNPP.
    intro x.
    apply x.
    left.
    intro c.
    destruct c_imp_a_ou_b.
      * exact c.
      * exact H.
      * apply NNPP.
        intro na.
        apply x.
        right.
        intro c2.
        exact H.
Qed.

Lemma q16 (X : Type) (A B : X -> Prop) : ((forall x, A x) \/ (forall x, B x)) -> forall x, A x \/ B x.
Proof.
intro z.
destruct z as [lp | rp].
  - intro pX.
    left.
    apply lp.
  - intro pX.
    right.
    apply rp.
Qed.

Lemma q17 (X : Type) (A B : X -> Prop) : (exists x, A x /\ B x) -> ((exists x, A x) /\ (exists x, B x)).
Proof.
intro z. (*Il existe un x tq Ax et Bx*)
destruct z as [pX a_ou_b]. (*on nomme ce x*)
split.
  - destruct a_ou_b as [a b].
    exists pX.
    exact a.
  - destruct z a
Qed.

Lemma q18 (A B : Prop) : ~ (A /\ B) -> (~ A \/ ~ B).
Proof.
Qed.

Lemma q19 (X : Type) : forall (x1 x2 : X), x1 = x2 -> x2 = x1.
Proof.
Qed.

Lemma q20 (X : Type) : forall (x1 x2 x3 : X), x1 = x2 /\ x2 = x3 -> x1 = x3.
Proof.
Qed.


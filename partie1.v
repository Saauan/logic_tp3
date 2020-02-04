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

(*
Lemma tiersexclus (A : Prop) : A \/ ~A.
Proof.
apply NNPP.
intro a.
apply a.
apply NNPP.
Qed.
*)

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

Qed.

Lemma q10 (A : Prop) :  (A /\ ~A) <-> False.
Proof.
Qed.

Lemma q11 (A B : Prop) :  (A \/ B) <-> ~(~A /\ ~B).
Proof.
Qed.

Lemma q12 (A : Prop) :  ~A <-> (A -> False).
Proof.
Qed.

Lemma q13 (A B : Prop) :  (A <-> B) <-> (A -> B) /\ (B -> A).
Proof.
Qed.

Lemma q14 (A B C : Prop) :  (A /\ B -> C) <-> (A -> B -> C).
Proof.
Qed.

Lemma q15 (A B C : Prop) :  (C -> A)\/ (C -> B) <-> (C -> A \/ B).
Proof.
Qed.

Lemma q16 (X : Type) (A B : X -> Prop) : ((forall x, A x) \/ (forall x, B x)) -> forall x, A x \/ B x.
Proof.
Qed.

Lemma q17 (X : Type) (A B : X -> Prop) : (exists x, A x /\ B x) -> ((exists x, A x) /\ (exists x, B x)).
Proof.
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


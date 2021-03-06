Definition faux := forall (P : Prop), P.
Definition non (A : Prop) := forall (P : Prop), ((A -> faux) -> P) -> P.
Definition et (A B : Prop) := forall (P : Prop), (A -> B -> P) -> P.
Definition ou (A B : Prop) := forall (P : Prop), ((A -> P) -> (B -> P) -> P).
Definition existe (A : Type) (P : A -> Prop) := forall (Q : Prop), (forall a, P a -> Q) -> Q.
Definition egal (A : Type) (a a' : A) := forall (P : A -> Prop), P a -> P a'.


Lemma bottom_e (A : Prop) : faux -> A.
Proof.
intro f.
apply f.
Qed.


Lemma non_intro (A : Prop) : (A -> faux) -> non A.
Proof.
intro a_imp_f.
intro x.
intro a_imp_f_imp_x.
apply a_imp_f_imp_x.
now simpl.
Qed.


Lemma non_elim (A : Prop) : A -> non A -> faux.
Proof.
intro a.
intro na.
apply na.
intro a_imp_f.
apply a_imp_f.
now simpl.
Qed.


Lemma et_intro (A B : Prop) : A -> B -> et A B.
Proof.
intro a.
intro b.
intro x.
intro a_imp_b_imp_x.
apply a_imp_b_imp_x.
  - now simpl.
  - now simpl.
Qed.


Lemma et_elim_g (A B : Prop) : et A B -> A.
Proof.
intro et_a_b.
apply et_a_b.
intro a.
intro b.
exact a.
Qed.


Lemma et_elim_d (A B : Prop) : et A B -> B.
Proof.
intro et_a_b.
apply et_a_b.
intro a.
intro b.
exact b.
Qed.


Lemma ou_intro_g (A B : Prop) : A -> ou A B.
Proof.
intro a.
intro x.
intro a_imp_x.
intro b_imp_x.
apply a_imp_x.
exact a.
Qed.


Lemma ou_intro_d (A B : Prop) : B -> ou A B.
Proof.
intro b.
intro x.
intro a_imp_x.
intro b_imp_x.
apply b_imp_x.
exact b.
Qed.


Lemma ou_elim (A B C : Prop) : ou A B -> (A -> C) -> (B -> C) -> C.
Proof.
intro ou_a_b.
intro a_imp_c.
intro b_imp_c.
apply ou_a_b.
  - exact a_imp_c.
  - exact b_imp_c. 
Qed.


Lemma existe_intro (A : Type) (P : A -> Prop) : forall x : A, P x -> existe A P.
Proof.
intro a.
intro p_a.
intro x.
(*Pour tout a, P(a) implique x*)
intro fa_a_pa_imp_x.
(*On a a... donc on a x*)
apply (fa_a_pa_imp_x a).
(*... donc P(a) est vraie*)
exact p_a.
Qed.


Lemma existe_elim (A : Type) (P : A -> Prop) (Q : Prop) : existe A P -> (forall x : A, P x -> Q) -> Q.
Proof.
intro ex.
intro fa.
apply ex.
exact fa.
Qed.


Lemma faux_false : faux <-> False.
Proof.
split.
  - intro f.
    apply bottom_e.
    now simpl.
  - intro f.
    now simpl.
Qed.


Lemma non_not (A : Prop) : non A <-> ~A.
Proof.
split.
  - intro na.
    intro a.
    apply (non_elim A).
      * exact a.
      * exact na.
  - intro na.
    apply non_intro.
    intro a.
    intro x.
    destruct na.
      * exact a.
Qed.


Lemma et_and (A B : Prop) : et A B <-> A /\ B.
Proof.
split.
  - intro et_a_b.
    split.
      * apply et_a_b.
        intro a.
        intro b.
        exact a.
      * apply et_a_b.
        intro a.
        intro b.
        exact b.
  - intro a_et_b.
    intro x.
    destruct a_et_b as [a b].
    apply et_intro.
      * exact a.
      * exact b.
Qed.

Lemma ou_or (A B : Prop) : ou A B <-> A \/ B.
Proof.
split.
  - intro ou_a_b.
    apply (ou_elim A B).
      * exact ou_a_b.
      * intro a.
        left.
        exact a.
      * intro b.
        right.
        exact b. 
  - intro a_or_b.
    destruct a_or_b as [a|b].
      * apply (ou_intro_g A B).
        exact a.
      * apply (ou_intro_d A B).
        exact b.
Qed.

Lemma existe_exists (A : Type) (P : A -> Prop) : existe A P <-> exists a, P a.
Proof.
split.
  - intro ex_a_p.
    apply (existe_elim A P).
      * exact ex_a_p.
      * intro a.
        intro pa.
        exists a. (*Obscure...*)
        exact pa. 
  - intro ex_a_ap_a.
    destruct ex_a_ap_a as [a pa].
    apply (existe_intro A P a).
    now simpl.
Qed.

Lemma egal_eq (A : Type) (a a' : A) : egal _ a a' <-> a = a'.
Proof.
split.
  - intro x.
    apply x.
    now simpl.
  - intro y.
    intro z.
    intro za.
    rewrite <- y.
    exact za.
Qed.

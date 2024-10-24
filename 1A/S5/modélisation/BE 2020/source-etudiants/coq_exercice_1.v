Require Import Naturelle.
Section Session1_2020_Logique_Exercice_1.

Variable A B C : Prop.

Theorem Exercice_1_Naturelle :  ((A -> C) \/ (B -> C)) -> ((A /\ B) -> C).
Proof.
I_imp H0.
I_imp H1.
E_imp (A).
E_ou (A->C) (B->C).
Hyp H0.
I_imp H2.
Hyp H2.
I_imp H3.
I_imp H4.
E_imp(B).
Hyp H3.
E_et_d(A).
Hyp H1.
E_et_g(B).
Hyp H1.
Qed.
Theorem Exercice_1_Coq : ((A -> C) \/ (B -> C)) -> ((A /\ B) -> C).
Proof.
intros.
cut A.
destruct H as [HA|HB].
exact HA.
intro.
cut (B).
exact HB.
cut(A/\B).
intro H22.
elim H22.
intros H22A H22B.
exact H22B.
exact H0.
destruct H0 as (HA,HB).
exact HA.
Qed.

End Session1_2020_Logique_Exercice_1.


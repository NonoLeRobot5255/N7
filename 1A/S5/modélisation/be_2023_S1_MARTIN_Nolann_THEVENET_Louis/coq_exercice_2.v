Require Import Naturelle.
Section Session1_2023_Logique_Exercice_2.

Variable A B : Prop.

Theorem Exercice_2_Naturelle : ((A -> B) -> A) -> A.
Proof.
I_imp H.
absurde H1.
I_antiT (A->B).
I_imp H2.
E_antiT.
I_antiT (A).
Hyp H2.
Hyp H1.

I_non H3.
I_antiT (A).
E_imp (A->B).
Hyp H.
Hyp H3.
Hyp H1.
Qed.

Theorem Exercice_2_Coq : ((A -> B) -> A) -> A.
Proof.
intro.
cut (A \/ ~A).
intro H2.
elim H2.
intros.
exact H0.
intros.
cut False.
intros .
contradiction.
Admitted.
End Session1_2023_Logique_Exercice_2.
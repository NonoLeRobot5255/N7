Require Import Naturelle.
Section Session1_2023_Logique_Exercice_1.

Variable A B : Prop.

Theorem Exercice_1_Naturelle :  ((A \/ B) /\ (~A)) -> (B /\ (~A)).
Proof.
I_imp H.
I_et.
E_ou A B.
E_et_g (~A).
Hyp H.
I_imp H1.
E_antiT.
E_non A.
Hyp H1.
E_et_d (A \/B).
Hyp H.
I_imp H1.
Hyp H1.
E_et_d (A \/B).
Hyp H.
Qed.

Theorem Exercice_1_Coq : ((A \/ B) /\ (~A)) -> (B /\ (~A)).
Proof.

intros.
destruct H as (H1,H2).



split.
elim H1.
intro.

cut False.
intro H3.
contradiction.
absurd A.
exact H2.
exact H.
intro.
exact H.
exact H2.
Qed.

End Session1_2023_Logique_Exercice_1.


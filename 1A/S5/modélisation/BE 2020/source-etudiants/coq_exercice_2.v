Require Import Naturelle.
Section Session1_2020_Logique_Exercice_2.

Variable A B : Prop.

Theorem Exercice_2_Naturelle : (A -> B) -> ((~A) \/ B).
Proof.
I_imp H.
E_ou (A) (~A).
TE.
I_imp H1.
I_ou_d.
E_imp A.
Hyp H.
Hyp H1.
I_imp H1.
I_ou_g.
Hyp H1.

Qed.

Theorem Exercice_2_Coq : (A -> B) -> ((~A) \/ B).
Proof.
intro.
cut (A\/ ~A).
intros.
destruct H0 as [H0A|H0B].
right.
cut (A).
exact H.
exact H0A.

left.
exact H0B.
apply (classic A).

Qed.

End Session1_2020_Logique_Exercice_2.


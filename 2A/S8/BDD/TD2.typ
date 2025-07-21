*On procède par étapes:*
+ *Lister tout les attributs (sans classification)*
+ *Lister les dépendances Fonctionnelles*
+ *Décomposition en FNBC*

= Liste des attributs:

pseudo_j, mdp, nom_joueur, pr_joueur, nationalité, $"@"$, dernier paiement VIP, echéan_VIP, score_j, note_jeu_joueur, nom_b, valeur_badge, intitulé_badge, date_badge, nom_jeu, date_enregis_jeu, texte_comm, note_comm, date_comm


= Liste DFs:

+ $"pseudo_j" -> "mdp, nom_j, prenom_j, nationalité, @, date_dernier_paiement, date_echéan_VIP, score_joueur"$
+ $"nom_b" -> "valeur_b, intitulé_b, nom_jeu, date_enreg_j"$
+ $"nom_b, pseudo_j" -> "date_b"$
+ $"pseudo_j, nom_jeu, date_enreg" -> "note_jeu"$
+ $"date_comm, pseudo_j" -> "texte_comm, nnote_comm, nom_jeu, date_enreg_j"$

= Decomposition en FNBC:

On a la relation originale:

R(#underline[pseudo_j], mdp, nom_joueur, pr_joueur, nationalité, $"@"$, dernier paiement VIP, echéan_VIP, score_j, note_jeu_joueur, #underline[nom_b], valeur_badge, intitulé_badge, date_badge, nom_jeu, date_enregis_jeu, texte_comm, note_comm, #underline[date_comm])

Ceci VIOLE la BC.


Donc on va la décomposer via les DF identifiés précédemment: (comme il n'y aura plus d'ambiguité sur les attributs, on peut changer les noms)

Pour cela, on vérifie que la DF i soit feuille (je sais plus ce que ça veut dire)

#h(3mm)

1) (bien feuille), donc on utilise le théorème de décomposition $=>$ Joueur(#underline[pseudo], mdp, mdp, nom, prenom, $"@"$, nation, score, date_paie_VIP, date_fin_VIP) + un reste:

R(#underline[pseudo_j], note_jeu_joueur, #underline[nom_b], valeur_badge, intitulé_badge, date_badge, nom_jeu, date_enregis_jeu, texte_comm, note_comm, #underline[date_comm])


2) (n'est pas encore feuille, donc on passe sur le 3)


3) (bien feuille), on applique le théorème de décomposition $=>$ Obtention_badge(#underline[nom_b, pseudo], date) + Reste:


R(#underline[pseudo_j], note_jeu_joueur, #underline[nom_b], valeur_badge, intitulé_badge, nom_jeu, date_enregis_jeu, texte_comm, note_comm, #underline[date_comm])

4) (bien feuille) on applique le théorème de décomposition $=>$ Note_jeu(#underline[pseudo_j, nom_jeu, date_enregis_jeu], note) + Reste:

R(#underline[pseudo_j], #underline[nom_b], valeur_badge, intitulé_badge, nom_jeu, date_enregis_jeu, texte_comm, note_comm, #underline[date_comm])

2) (maintenant, 2 est bien feuille, on peut le faire) : $=>$ Badge(#underline[nom], nom_jeu, date_jeu, valeur, intitulé) + Reste:


R(#underline[pseudo_j], #underline[nom_b], texte_comm, note_comm, #underline[date_comm])


5) (bien feuille) $=>$ Commentaire(#underline[date,joueur], texte, note, nom_jeu, date_jeu) + Reste:

S(#underline[pseudo_j, nom_b, date_comm])

*Ce sont des dépendances multivaluées:* 

6) $"pseudo" -> "nom_b" | "date_comm"$

On utilise le théorème de décomposition:  S se découpe alors en 2 relations: 

- (#underline[pseudo, nom_b]), *redondance avec Obtention_badge*
- et (#underline[pseudo, date_comm]) *redondance ave Commentaire*

Comme ils sont redontants, on peut simplement les enlever.







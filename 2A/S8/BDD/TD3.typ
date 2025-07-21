*On procède par étapes:*
+ *Lister tout les attributs (sans classification)*
+ *Lister les dépendances Fonctionnelles*
+ *Décomposition en FNBC*

= Liste des attributs:


nature_pt, coords_pt, nom_av, attributs_av, \@int_jou, nom_jou, prenom_jou, nom_obj, id_obj, divers_obj, capa_max_lieu, capa_max_jou, unique_renc, pt_renaissance,


Pour objects_c et avacars_c => c'est trop prématuré pour dire que ce sont des attributs.
Les monstres seront modélisé par un avatar où les attributs qui lieraient à un joueur sont NULL.

= Dépendances Fonctionnelles:

+ coord_pt_a -> capa_max_lieu, nature_pt, capa_max_av

+ nom_av -> attributs_av, coords_jou, capa_max, pt_renaissance, unique_renc

+ \@int_jou -> nom/prenom_jou

+ id_obj -> divers_obj, nom_obj, pt_obj_pose, nom_av *UN Des 2 est forcément à NULL*


= Décomposition en FNBC

R ( #underline[coords_pt_A], nature_pt, capa_obj, capa_av, pt_renaissance, nom_av, stats_av, coords_pt_B, \@jou, nom/prenom_jou, #underline[id_obj], nom_obj, divers_obj, pt_ou_posé)


(1) est feuille., on applique le Théo de Décomposition: Point(#underline[coords, nature, capacité_obj, capacité_avatar]) 

+Rest: R(coords_pt_A, coords_pt_B, $cancel("nature, capa"\_"obj, capa"\_"av")$ pt_renaissance, nom_av, stats_av,  \@jou, nom/prenom_jou, id_obj, nom_obj, divers_obj, pt_ou_posé)

(2) n'est pas feuille

(3) Theo de Décomposition: Joueur(#underline[\@], nom, prénom)

+Reste :Rest: R(coords_pt_A,, pt_renaissance, nom_av, stats_av,$cancel( \@"jou, nom/prenom")$, id_obj, nom_obj, divers_obj, pt_ou_posé)

(2) + TD: Avatar(#underline[nom], stats, renaissance, \@ joueur)

+Reste: R($cancel("pt"\_"renaissance, nom"\_"av, stats"\_"av")$, id_obj, nom_obj, divers_obj, pt_ou_posé)

(4) forcépment feuille car c'est le dernier.

Objet(#underline[id], nom, divers, pt où posé, av_détiens)

+Reste: R(id_obj,coords_pt_A, coords_pt_B) => C'est bon car il ne reste plus que les clés de base.

On remarque que ce reste porte l'info du passage vers une case avec un objet.

MAIS IL MANQUE L'INFO SUR QUI.
DONC ON RAJJOUTE l'avatar.

Dépendance mulit-variée:

(5) nom_av -> pt_A, pt_B | id_obj

_exemple: Héraclès est allé aux enfers avec la massue X_

#h(14mm) _Héraclès est allé à Anguras avec la tunique Y_

Ceci donne: _Héraclès Enfers avec la tunique_ => valide car il n'avait pas forcément la tunique qd il est allé aux enfers.

Donc:

(5) + TD (DMV) => Est_passé( #underline[avatar, ptA, ptB]) + (avatar, #underline[obj])



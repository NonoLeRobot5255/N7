= dernier CM

== graphe plannaire 

graphe plannaire = dessiner dans un plan (les arrêtes ne se croisent pas a part aux sommets)

graphe isomorphe = graphes qui peuvent coincider par déformation

face = région délimitée par des arrêtes

frontière = ensemble des arrêtes qui délimitent une face

deux phases adjacentes = deux faces qui ont une arrête en commun

le degrès minimal d'un graphe non plannaire est 5, en dessous, on est toujours plannaire

=== Théorème de Kuratowski

Un graphe est plannaire si et seulement si il ne contient pas de sous graphe homéomorphe à K5 ou K3,3

K5 = graphe complet à 5 sommets
K3,3 = graphe biparti complet à 3 sommets

== Coloration de graphe

Deux types de coloration pour graphe G=(X,A) :

- coloration de sommets : on attribue une couleur à chaque sommet de telle sorte que deux sommets adjacents n'aient pas la même couleur

- coloration d'arêtes : on attribue une couleur à chaque arrête de telle sorte que deux arrêtes incidentes à un même sommet n'aient pas la même couleur

nombre chromatique = nombre minimal de couleurs nécessaires pour colorer un graphe

ensemble stable = ensemble de sommets qui ne sont pas adjacents en terme de coloration

nombre de stabilité = cardinal maximal d'un ensemble stable dans un graphe il sera noté $alpha (G)$, avec $gamma (G)$ nombre de chromatique et N(G) le nombre de sommets :

$alpha (G) + gamma (G) >= N(G)$

On en déduit :

$gamma (G) >= N(G) / (alpha (G))$

il existe 6 bornes (voir cours) et avec ces 6 bornes, si on regarde les bornes inférieures, on sait le minimum théorique mais on est pas sûr de l'atteindre.

clique = ensemble de sommets qui sont tous adjacents (egraphe complet)

=== Algorithme de Welsh et Powell

a ecrire avec le cours 

Mais en gros : on prend le sommet de degré maximal, on le colorie avec une couleur, on colorie de la même couleur les sommets qui ne sont pas adjacents à ce sommet, on prend le sommet de degré maximal parmi les sommets non coloriés et on recommence. (Je crois)
= Cours de Emmanuel Chaput sur MPLS en interco 

MPLS  = Circuit virtuel sur paquet IP

IP = cool car simple mais pas cool car gestion de congestion (fais par TCP en PLS)

vu que circuit virtuel( LSP = Label Switched Path) on peut faire un semblant de connexion sur IP. Et MPLS permet aussi de commuté sans faire du routage et connecté les réseaux entre eux et faire transité plusieurs types de données dessus.

On peut choisir de prendre un tuyaux ou un autre et ça c'est les humains qui gèrent.

On peut différencier les trafics et leurs besoins en faisant différent LSP (par exemple un LSP pour la voie et un pour la viédo) et on identifie les trafics par un numéro de LSP. Ce mécanisme fait aussi de la QoS. On peut même faire deux communications pareil (par exemple deux fois la voix) ce qui permet de différencier les trafics d'une même communication, le trucs c'est juste de bien identifier nos trafics.

MPLS = issu de la "fusion" de ATM et IP. Beaucoup utilisé pour l'ingénierie de trafic.

#figure(table(columns: 2,
[TERME], [DÉFINITION],
[LSR], [Label Switch Router],
[LSP], [Label Switched Path],
[Label], [numéro qui identifie un LSP],
[FEC], [Forwarding Equivalence Class],
[PHP], [Penultimate Hop Popping],
[TTL], [Time To Live],
[NHLFE], [Next Hop Label Forwarding Entry],
[ILM], [Incoming Label Map],))

On peut avoir plusieurs LSP sur un même lien et donc on traite avec celui qui est en sommet de pile.

PHP = on enlève le label juste avant d'envoyer le paquet sur le lien final car le dernier LSR n'as pas besoin de label, on décapsule donc sur l'avant dernier LSR.

TTL = on le décrémente à chaque LSR pour éviter les boucles infinies.Champs TTL dans l'identifiant du LSP. Mais problème car si plusieurs LSP sur un même lien, on peut avoir un TTL qui est pas cohérent, on fait donc une copie du TTL actuel quand on dépile de LSP.

NHLFE = table de routage MPLS, on a une table de comutation pour chaque LSP.

ILM = table de correspondance entre les labels entrant et les labels sortant.

FTL = Forwarding Table, table de routage MPLS.

*_apartée sur comment créer les tables de rotages MPLS et tout, 255 au total dont 252 utilisables. A voir dans le cour pour les manipulations justemento _*
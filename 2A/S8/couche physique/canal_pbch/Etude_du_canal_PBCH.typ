#import "../../../../template/template_2A.typ": *

#show : project.with( title: "Étude du canal PBCH", year: "2024-2025", profondeur: 1, authors: ("MARTIN Nolann",), teachers: ("ESCRIG Benoit",) )

= Introduction

Dans cette étude, nous allons nous intéresser au canal PBCH (Physical Broadcast CHannel). Les canaux (ou channel en anglais) sont des divisions en temps et fréquences de la bande passante afin de séparer des tâches ou des fonctions précises. @noauthor_physical_nodate 

Nous allons étudier les caractéristiques du canal PBCH et quelle est son activité dédiée. Nous utiliserons dans ce rapport des références bibliographiques citées dans la section dédiée à cet effet ainsi que des références tout au long du document pour appuyer nos propos. Nous utiliserons par ailleurs la norme IEEE pour la bibliographie.

= Information transmise par le canal PBCH

Le canal PBCH est un canal de diffusion qui est utilisé pour transmettre des informations de synchronisation et de configuration. Le PBCH transporte une partie des informations système nécessaires aux terminaux pour accéder au réseau. @noauthor_physical_nodate @kamath_decoding_nodate

Il y a besoin d'avoir un canal dédié à la synchronisation pour que l'utilisateur puisse se connecter au réseau. L'utilisateur sonde le canal PBCH pour obtenir les informations nécessaires pour se connecter au réseau. @noauthor_physical_nodate

Il transporte donc les informations nécessaires, le MIB (Master Information Block) qui est constitué, pour le principal, de :

- System Frame Number (SFN) : Porte le numéro de trame système de la trame actuelle utile pour la synchronisation ;
- Bande passante descendante : Indique la bande passante descendante à utiliser ;
- Nombre d'antennes d'émission : Indique le nombre d'antennes d'émission qu'utilise la station de base, pour la technique MIMO (Multiple Input Multiple Output) ; @coulon_slide_nodate
- Subcarrier Spacing common (SSC) : Définit l'espacement des sous-porteuses à utiliser pour la réception ;
- Cell barred : Indique si la cellule est interdite ou non ;
- IntraFreqReselection : Indique si la cellule est autorisée pour la re-sélection intra-fréquence (c'est-à-dire changer de cellule si la réception n'est pas assez bonne). @noauthor_5g_nodate @riz_exploring_2024 @flaunay_re-selection_2024

= Nécessité d'utiliser le canal PBCH pour ces informations

Le canal PBCH est un canal de broadcast, c'est-à-dire qu'il n'envoie pas d'informations spécifiques à un utilisateur mais à tous les utilisateurs. Comme vu précédemment, il est le canal qui permet de partager des informations de synchronisation et de connexion, il ne donne donc aucune information spécifique aux utilisateurs de données ou de signalisation, c'est pour cela qu'avoir un canal de diffusion est nécessaire. @kamath_decoding_nodate

De plus, si un utilisateur se connecte au réseau, il doit d'abord se synchroniser avec le réseau. Ainsi, le canal PBCH est le canal le plus adapté pour transmettre ces informations à des utilisateurs qui ne sont pas encore enregistrés auprès de l'antenne. Pour les utilisateurs qui sont déjà connectés, il permet de se resynchroniser en cas de perte de synchronisation ou bien pour les utilisateurs changeant d'antenne (handover).

C'est pour cela que le PBCH est un canal de diffusion très robuste. Il utilise pour cela une modulation de type QPSK (Quadrature Phase Shift Keying), qui est une modulation très robuste, ainsi qu'une suite de Codes de Redondance Cyclique (CRC) afin d'assurer un décodage correct des informations. Le fait que le PBCH soit toujours codé de la même manière fait que l'utilisateur n'a pas à connaître au préalable d'informations sur l'antenne à laquelle il essaie de se connecter et donc peut facilement accéder au réseau sans connaissance préalable. Il est aussi brouillé : l'utilisateur essaie donc, en se connectant, différents masques (que des 0, que des 1 ou une alternance de 0 et de 1) pour trouver le bon masque et ainsi démoduler les informations. Cela aide à la robustesse dans différentes conditions de réception en aidant à différencier la séquence du bruit et aussi des autres signaux transmis en même temps. Cela peut différer légèrement en fonction de si nous utilisons la 4G, 5G,... @noauthor_4g_nodate @kamath_decoding_nodate @noauthor_5g_nodate-1

= Transmission de ces informations dans une trame OFDM

Le canal PBCH est transmis dans une trame OFDM (Orthogonal Frequency Division Multiplexing), qui est une technique de modulation numérique permettant de transmettre des informations sur plusieurs sous-porteuses en même temps. Pour notre SSB (Synchronization Signal Block), il y a 240 sous-porteuses et 4 symboles par sous-porteuse. @noauthor_pbch_2020

Nous pouvons voir sur la figure ci-dessous la structure d'une trame OFDM.

#figure(image("./screen/OFDM.png", width: 70%), caption: [structure du signal de synchronisation @noauthor_pbch_2020])

Nous pouvons en déduire que le canal PBCH est transmis sur les symboles 2 et 4 de cette trame OFDM. Il est transmis sur plusieurs symboles pour augmenter la robustesse de la transmission. Il est d'ailleurs aussi partagé avec le DMRS (Demodulation Reference Signals) qui est un signal pour aider à la démodulation en conditions difficiles de réception. On transmet PBCH sur plusieurs symboles car si un symbole est perdu ou mal réceptionné, il reste encore deux symboles pour décoder les informations. De plus, il y a 240 sous-porteuses afin d'améliorer encore la robustesse de la transmission, effectivement, en augmentant le nombre de sous-porteuses on rend le canal moins sélectif en fréquence et donc plus robuste face aux perturbations.

Nous pouvons notamment voir le PSS (Primary Synchronization Signal) et le SSS (Secondary Synchronization Signal) qui sont des signaux de synchronisation qui permettent de synchroniser les terminaux avec le réseau. C'est pour cela que le bloc entier s'appelle SSB (Synchronization Signal Block). Les 0 présents sur la sous-porteuse 1 sont là pour empêcher les interférences avec les autres signaux transmis en même temps.

= Pertinence de transmettre ces informations sur ces fréquences OFDM

La transmission de ces informations sur des fréquences OFDM est pertinente pour plusieurs raisons. Tout d'abord, la modulation OFDM est une modulation très robuste face aux perturbations. En effet, elle permet de transmettre des informations sur plusieurs sous-porteuses en même temps, ce qui permet de répartir les informations sur plusieurs fréquences et donc de réduire les effets de la sélectivité en fréquence du canal. De plus, la modulation OFDM permet de transmettre des informations sur des fréquences très rapprochées sans interférences entre les sous-porteuses. Il y a ce qu'on appel du beamforming qui permet de diriger le signal vers un point précis, ce qui permet de réduire les interférences entre les antennes, ce beamforming permet justement de réduire les interférences entre les antennes et ainsi augmenter notre robustesse. Pour que notre canal PBCH soit bien réceptionné, il est préférable de le transmettre sur deux fréquences différentes afin que l'angle de réception soit bon et que le signal soit bien réceptionné. 

L'OFDM permet aussi une meilleure utilisation de notre spectre, car il permet de transmettre des informations sur des fréquences très rapprochées sans interférences entre les sous-porteuses. Cela permet donc de transmettre plus d'informations sur une même bande passante et ainsi avoir une meilleure éfficacité spectrale.
@noauthor_5g_nodate-1 @noauthor_pbch_2020 @noauthor_beamforming_nodate

= Conclusion

Pour conclure nous avons pu voir que le canal PBCH est un canal très utile pour la connexion au réseau, son rôle est d'envoyer périodiquement des informations de synchronisation et de connexion aux utilisateurs. Il transporte le MIB, où nous avons vu qu'il contient les informations importantes.

Nous avons donc vu tout au long de ce rapport que le canal PBCH est un canal de diffusion très robuste, qui utilise une modulation QPSK, des CRC et une transmission sur plusieurs symboles pour assurer une bonne réception des informations. Nous avons aussi vu que la transmission de ces informations sur des fréquences OFDM est pertinente pour augmenter la robustesse de la transmission. Ainsi que le placement des sous-porteuses et des symboles pour augmenter la robustesse de la transmission. 

Donc le canal PCBH est fait pour être un canal à la fois robuste et simple d'accès pour les utilisateurs, il est donc très important pour la connexion au réseau. 

#pagebreak()

#bibliography("biblio.bib", style : "ieee", title: "Bibliographie/Sitographie")
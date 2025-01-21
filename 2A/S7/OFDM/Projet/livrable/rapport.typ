#import "../../../../template/template_2A.typ": *

#show: project.with(
  
  title: "Rapport du bureau d'étude sur l'OFDM",
  authors: (
    "MARTIN Nolann",  ),
  teachers: (
    "BOUCHERET Marie-Laure", 
  ),
  year : "2024-2025",
  profondeur : 2,
)


= Intro 

Le but de ce projet est de réaliser une étude sur l'OFDM (Orthogonal Frequency Division Multiplexing) et de mettre en place un système de communication numérique basé sur cette technologie.

Nous serons dans un contexte de canal sélectif en fréquence et nous serons la plupart du temps sur un canal sans bruit et sur un mapping BPSK, sauf sur la dérnière partie où nous étudierons l'impact du bruit sur la transmission avec une modulation QPSK.

= Implantation de la chaine de transmission OFDM sans canal

Dans cette partie nous implentons Une chaine de transmission OFDM sans canal. Pour étudier le comportement nous n'activeront que certaines porteuses. Nous distingueront 3 cas :

== Emission

=== Premier cas : 1 porteuse active 

#figure(
  image("../screen_rapport/porteuse 1 active.png",width: 80%), 
  caption: [Porteuse 1 active seulement]
  )

#figure(
  image("../screen_rapport/porteuse 4 active.png",width: 80%), 
  caption: [Porteuse 4 active seulement]
  )

Nous voyons que la porteuse active créer un "pic" sur notre DSP, ce qui est normal car nous avons une fréquence porteuse qui est active.
#pagebreak()
=== Deuxième cas : 2 porteuses actives.

#figure(
  image("../screen_rapport/porteuse 1 et 3 actives.png",width: 80%), 
  caption: [Porteuse 1 et 3 actives ]
  )

#figure(
  image("../screen_rapport/porteuse 4 et 5 actives.png",width: 80%), 
  caption: [Porteuse 4 et 5 actives]
  )

Nous voyons que les deux porteuses actives créent un "pic" sur notre DSP, le placement des pics étant déterminé par le nombre et le placement des porteuses actives. De plus on peut voir que si les deux porteuses sont côte à côte, les "pics" se rejoignent pour former un seul "pic".

=== troisème cas : 8 porteuses du milieu actives

#figure(
  image("../screen_rapport/8porteusesdumilieu.png",width: 80%), 
  caption: [Porteuse])


Nous voyons que les 8 porteuses du milieu étant actives, elles créent une sorte de palier du au fait qu'elles sont actives et que les autres porteuses sont inactives.

=== explication 

Nous avons parler de pics et de palier, ce qui se cache dans ces termes est le fait que la densité spectrale de puissance est plus élevée à ces endroits là. Cela est du au fait que les porteuses actives vont créer des "pics" de puissance à ces endroits là. D'où le terme de pic.

== Réception sans canal

Dans cette partie nous vérifions qu'à la récéption notre TEB(Taux d'Erreur Binaire) sera nul. Pour cela les 16 porteuses seront actives. 

#figure(
  image("../screen_rapport/TEB+toutes_actives.png",width: 80%), 
  caption: [DSP des 16 porteuses actives et TEB]
  )

Nous vérifions bien que notre TEB est nul, ce qui est normal car nous n'avons pas de canal et que les 16 porteuses sont actives.

= Implantation de la chaine de transmission OFDM avec canal multi-trajets, sans bruit

Dans cette partie nous étudierons l'impact d'un canal sans bruit dont le canal multi-trajet est de la forme suivante :

$y(t)= 0.407x(t) + 0.815x(t - "Ts" ) + 0.407x(t - 2"Ts" )$

== Implantation sans intervalle de garde

Nous pouvons voir que en ayant ce filtre la réponse impulsionelle de notre filtre sera de la forme suivante :

$h (t) = 0,404delta(t) + 0,815delta(t-"Ts") + 0,407delta(t-2"Ts")$

Nous pouvons a présent tracer le module et la phase en fréquence du canal de propagation : 

#figure(
  image("../screen_rapport/phase et frequence.png",width: 80%), 
  caption: [Module et phase du canal de propagation]
  )

Nous pouvons voir à partir de ces figures qu'il y a une aténuration du signal sur la porteuse 8.

Ainsi nous pouvons observer l'effet qu'à ce canal sur notre densité spectrale de puissance :

#figure(
  image("../screen_rapport/dsp canal.png",width: 80%), 
  caption: [densité spectrale de puissance en sortie du canal]
  )

Nous pouvons constater que le canal a un effet sur notre DSP. En effet, la porteuse 8 est atténuée, ce qui correspond bien à nos attentes. En OFDM, nous utilisons un rectangle pour la mise en forme des symboles. Lorsqu’il traverse le canal de propagation, notre signal subit la réponse en fréquence de ce dernier, ce qui modifie sa mise en forme et entraîne l’atténuation observée.

Les constellations des symboles reçus peuvent être intéressantes à observés, nous pouvons donc tracer les constellations des porteuses 6 et 15 :

#figure(
  image("../screen_rapport/const 6 et 15.png",width: 80%), 
  caption: [constellation de la porteuse 6 et 15]
  )

Nous pouvons voir que la constellation de la porteuse 6 est déformée, ce qui est normal car elle est atténuée, il y a une superposition des bits ce qui amène des fausses décisions et un TEB supérieur à 0. La constellation de la porteuse 15 est quant à elle inchangée ou casiment, il y a quand même un nuage mais aucun bit ne se superpose. Nous voyons d'ailleurs une rotation induite par le canal.

Malheuresement, pour notre TEB, il n'est plus nul dans ce cas là comme dit précedemment, nous avons par exemple sur cette simulation un TEB de 0.3609, nous voyons ça car même si nous n'avons pas de bruit, le canal créer de l'intérference inter symbole (ISI) car le filtre de notre canal prend en compte ce qu'il se passe à l'instant -Ts et -2Ts.

Dans la suite nous utiliserons un nombre de bits par porteuses égal à 10000 afin d'avoir des constellations mieux dessinés.

== Implantation avec intervalle de garde composé de zéros

Dans cette partie, nous allons ajouter un intervalle de garde composé de zéros devant chaque symbole
OFDM transmis avant passage dans le canal de propagation.

Nous devons tout d'abord déterminer la longueur de l'intervalle de garde nécessaire pour éviter le recouvrement des symboles dans le canal. Pour cela, nous devons déterminer la durée $tau_max$ qui est le retard maximal. 

Nous voyons que notre filtre prend en compte jusque l'instant $2"Ts"$, Nous pouvons donc en déduire que $tau_max = 2$. Nous devons donc avoir un IG tel que $"IG">=2$, nous prendrons donc $"IG"=2$.


Avec cet IG nous avons maitenant une intérférence inter symbole égal à 0, mais nous avons maintenant de l'intérference inter porteuse (ICI) qui arrive dû à la perte de l'orthogonalité de notre signal et de l'intérference intra symbole. 

Nous pouvons observer les constellations sur les porteuses 6 et 15 :

#figure(image("../screen_rapport/const 6 et 15 IG0.png",width: 80%),
caption: [constellation de la porteuse 6 et 15 avec IG composé de 0])

Ce qu'on voit sur les constellations, c'est que nos deux nuages sont maintenant plus distinct, l'intervalle de garde à supprimer l'ISI, même si cela demande donc de la bande passante supplémentaire afin de transmettre. Et que nous avons en même temps toujours de l'intérference intra symbole qui fait que notre TEB est supérieur à 0. 

== Implantation avec préfixe cyclique

Dans cette partie, nous allons ajouter un préfixe cyclique devant chaque symbole OFDM transmis avant passage dans le canal de propagation. Cela devrait permettre de supprimer l'interférence inter-symbole et l'interférence inter-porteuse. Ainsi, nous devrions théoriquement avoir pour constellations sur nos différentes porteuses des points, du fait de la convolution circulaire. Qui va s'opérer entre le préfixe et le symbole dont il est issus. 


#figure(image("../screen_rapport/const 6 et 15 IGCP + TEB.png",width: 80%),
caption: [constellation de la porteuse 6 et 15 avec CP et TEB])

En visualiant les constellations des porteuses 6 et 15, seulement deux points sont visibles, c'est dû au fait que le préfixe cyclique a permis de supprimer l'interférence inter-symbole et l'interférence inter-porteuse. Mais nous voyons qu'ils ne sont pas sur -1 +1 pour la porteuse 6, c'est la cause du canal qui atténue et amplifie les bits. Par contre pour notre porteuse 15, les points sont bien sur -1 +1, ce qui est normal car elle n'est pas atténuée ou amplifié, nous le voyons sur la DSP ou sur la réponse en module de notre filtre que la porteuse 15 ne subit pas ce phénomène. 

D'un autre côtés nous voyons un TEB supérieur à 0, ce qui pourrait parraitre étrange, mais c'est normal, sans égalisation, le canal va atténuer ou amplifier les bits, ce qui va créer des erreurs de décisions.

== Implantation avec préfixe cyclique et égalisation

Dans cette partie, nous allons ajouter un égaliseur à notre récepteur. Cela devrait permettre de compenser les effets du canal de propagation et ainsi d'avoir un TEB nul.
Nous étudierons deux types d'égaliseurs : l'égaliseur ZF (Zero Forcing) et l'égaliseur ML (Maximum Likelihood).

=== Egaliseur ZFE

L'égaliseur ZF est de la forme suivante : 

$H = [H(0)H(1)...H(N-1)]$ avec $H(k) = 1/C(k)$ pour $k=0$ à $N-1$

Nous pouvons observer les constellations des porteuses 6 et 15 ainsi que la valeur du TEB:

#figure(image("../screen_rapport/Egalisation_1surCK.png",width: 80%),
caption: [constellation de la porteuse 6 et 15 avec égalisation ZF et TEB])

Nous pourrions penser qu'il y a plusieurs points et que donc notre constellation n'est plus bonne, mais si nous regardons l'échelle de $10^(-16)$, nous pouvons déduire que dans les deux cas les points sont sur -1 +1, ce qui est normal en BPSK. De plus nous voyons que le TEB est égal à 0 ce qui est une très bonne nouvelle, l'égalisateur de type ZF a bien fonctionné et parfaitement égalisé notre signal. La rotation de nos constellation a aussi été supprimer par notre égaliseur.

=== Egaliseur ML

L'égaliseur ML est de la forme suivante :

$H = [H(0)H(1)...H(N-1)]$ avec $H(k) = C^*(k)$ pour $k=0$ à $N-1$

Nous pouvons observer les constellations des porteuses 6 et 15 ainsi que la valeur du TEB:

#figure(image("../screen_rapport/Egalisation_conjCK.png",width: 80%),
caption: [constellation de la porteuse 6 et 15 avec égalisation ML et TEB])

Nous pouvons voir que cette fois ci les constellations sont sur $[-0.3;0;3]$ et $[-2;2]$ avec une échelle à $10^(-16)$ prés. Mais que nous gardons quand même un TEB à 0 ce qui est un comportement attendu.

=== différences entre ML et ZFE

Nous pouvons voir que le ZFE est un égalisateur linéaire, ce qui le rend simple à implanter. Malheuresement, il est sensible au bruit et à l'interférence. L'égaliseur ML est quant à lui un égaliseur non linéaire, ce qui le rend plus complexe à implanter. Mais il est moins sensible au bruit et à l'interférence.

Dans les deux cas, nous voyons tout de même que le TEB tombe à 0 ce qui est le comportement voulu. Mais nous utiliserions ces égalisateur dans des circonstances différentes, le ZFE pour des systèmes avec peu de bruit ou un système où nous n'avons pas besoin d'une grande précision. Le ML pour des systèmes avec beaucoup de bruit ou un système où nous avons besoin d'une grande précision.

= Impact d'une erreur de synchronisation horloge

Dans cette partie,nous allons étudier l'impact d'une erreur de synchronisation horloge, nous allons donc échantillonner notre signal à différent instant affin de voir ce qu'il advient de nos constellation et pouvoir en comprendre le sens et l'impact. Nous utiliserons donc un intervalle de garde plus grand, de taille 6 afin de pouvoir parfaitement simulé nos 3 cas. Et nous garderons un égalisateur de la forme ZFE.

Pour ce faire nous prendrons 3 cas de figure distinct: 

== Premier cas : synchronisation dans l'intervalle de synchronisation

Nous prendrons dans ce cas le début de l'échantillonage dans la période de synchronisation, ce qui ne laisse pas le temps à nos bit de bien se synchroniser et ainsi nous devrions obtenir une constellation qui ne sera pas deux points et qui aura une rotation.

Dans la courbe qui suit nous prenons notre début d'échantillonage à $T = 2$ ce qui en'est pas dans notre intervalle $[3;6]$ notre intervalle optimal de synchronisation.
#figure(image("../screen_rapport/erreur syncho inf.png",width: 80%),
caption: [constellation de la porteuse 6 et 15 avec erreur de synchronisation dans l'intervalle de synchronisation])

Nous voyons bien qu'il n'y a pas simplement deux points et que la constellation est tournée, ce qui est normal car les bits n'ont pas eu le temps de se synchroniser. De plus nous voyons que le TEB est supérieur à 0, ce qui est normal car les bits ne sont pas bien synchronisés et donc les décisions sont fausses.

== Deuxième cas : synchronisation dans l'intervalle de garde 

Nous prendrons dans ce cas le début de l'échantillonage dans la période de garde, ce qui laisse le temps à nos bit de bien se synchroniser et ainsi nous devrions obtenir une constellation qui sera deux points et qui n'aura pas ou très peu de rotation. 

Dans la courbe qui suit nous prenons notre début d'échantillonage à $T = 3$ ce qui est  dans notre intervalle $[3;6]$ notre intervalle optimal de synchronisation.

#figure(image("../screen_rapport/erreur syncho egale.png",width: 80%)) 

Nous voyons bien que les constellations sont deux points et qu'il n'y a pas de rotation, ce qui est normal car les bits ont eu le temps de se synchroniser. De plus nous voyons que le TEB est différent de 0 ce qui s'explique par le fait que nous ne somme pas parfaitement dans l'instant optimal de synchronisation qui est à $T = 6$.

== Troisième cas : synchronisation en dehors de l'intervalle de garde 

Nous prendrons dans ce cas le début de l'échantillonage en dehors de la période de garde, c'est à dire que nous prendrons l'échantillonage après la fin de l'intervalle de garde, et qu'ainsi nous obtiendrons une constellation qui sera des nuages de points ainsi que de la rotation.

Dans la courbe qui suit nous prenons notre début d'échantillonage à $T = 8$ ce qui est en dehors de notre intervalle $[3;6]$ notre intervalle optimal de synchronisation.

#figure(image("../screen_rapport/erreur syncho sup.png",width: 80%),
caption: [constellation de la porteuse 6 et 15 avec erreur de synchronisation en dehors de l'intervalle de garde])

Nous voyons bien le nuage de point et la rotation, ce qui est normal car l'intervalle de garde n'est plus réélement pris en compte car nous échantillonons en dehors de l'intervalle de garde. Nous n'avons pas calculé le TEB du fait que nous avons redimensionner la matrice à la réception pour échantillonner à l'instant $T = 8$. Mais nous pouvons simplement affirmer que notre TEB sera supéerieur à 0.

== Conclusion sur la synchronisation

Nous voyons que la synchronisation est donc un facteur important de notre transmission, si nous ne sommes pas bien synchronisé, nous aurons des erreurs de décisions et donc un TEB supérieur à 0. Nous devons donc être bien synchronisé pour avoir un TEB nul. De plus nos constellations aussi ne seront pas bonnes de ce que nous avons vu ce qui est quelque chose de très important pour la transmission de nos bits afin de les échantillonner au mieux possible.

= Implantation de la chaine de transmission OFDM avec canal à bruit additif blanc et gaussien

Nous utilisons maintenant une modulation QPSK pour notre mapping et nous ajoutons du bruit pour voir le comportement de notre modulation OFDM comparé au TEB théorique de la modulation QPSK. Pour ce fair nous utiliserons ces paramètres :

- Puissance du bruit sur chaque voie : $sigma_I^2=sigma_Q^2= P_x_e/(2log_2 (M) E_b/N_0)$
- Nombre de bits par porteuse : 1000000
- Nombre de bits total : 16000000
- Valeur du $E_b/N_0$ : $[0;8]$ avec pas de 0.5


Nous pouvons observer le TEB théorique et simulé en fonction de $E_b/N_0$ : 

#figure(image("../screen_rapport/TEB_simule et theo.png",width: 80%),
caption: [TEB théorique et simulé en fonction de $E_b/N_0$ pour $E_b/N_0$ de 0 à 8])

Nous pouvons voir que dans uen configuration classqiue d'ofdm sans canal, le TEB est meilleur que la modualtion QPSK théorique, cela est dû au fait que l'OFDM est une modulation plus robuste que la QPSK. Du fait qu'elle enlève ou diminue la séléctivité en fréquence du canal de propagation. 

= Conclusion

Nous avons montré, tout au long de ce rapport, que la modulation OFDM est à la fois intéressante et relativement simple à implémenter. Grâce à l'utilisation de la FFT et de l’IFFT, il est possible de moduler et de démoduler efficacement le signal, en s'appuyant sur le filtre de mise en forme.

Nous avons également démontré que l’ajout d’un intervalle de garde, en particulier sous la forme d’un préfixe cyclique, est une solution efficace pour limiter les interférences introduites par les filtres. Par ailleurs, l’égalisation se révèle être une méthode performante pour traiter les interférences intersymboles provenant d’un même canal. La synchronisation de cet intervalle de garde joue également un rôle crucial, car elle garantit un échantillonnage correct des bits transmis.

Enfin, nous avons souligné que l’OFDM est plus robuste que la modulation QPSK, notamment grâce à sa résistance aux sélectivités en fréquence, ce qui en fait un choix privilégié dans de nombreux systèmes de communication modernes.
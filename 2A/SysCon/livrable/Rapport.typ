= Rapport du projet de système concurrent


== Résumé de ce qui a été fait

Dans ce projet de système concurent ce qui a été fait est :

+ Ajout de l'exclusion mutuelle afin de ne pas avoir de conflit dans les tubes
+ Ajout de la signalisation et diffusion de messages afin que les processuses en attentes soient reveillés au bon moment 
+ Ajout de sifnalisation/diffusion quand un processus attent mais qu'il n'a pas de message et que c'est un lecteur ou que c'est un écrivain et que le tube est plein 
+ Ajout d'un ordonnanceur/basculeur de tache  pour les processus afin qu'il n'y est pas un seul lecteur qui monopolise le tube ou un seul écrivain qui monopolise le tube

== Quel version de l'exclusion mutuelle ai-je implémenté ?

Dans cette version de l'exclusion mutuelle j'ai implémenté la version bloquante de l'exclusion mutuelle. C'est à dire que si un processus veut accéder à une section critique et qu'il ne peut pas y accéder alors il est bloqué jusqu'à ce qu'il puisse y accéder et recevra un signalement pour savoir qu'il peut y accéder.

== Comment aurais je pu implanter la version non bloquante de l'exclusion mutuelle ?

Pour implanter la version non bloquante de l'exclusion mutuelle j'aurais pu simplement faire se terminer des processus qui ne peuvent pas accéder à la section critique. Ce qui est aussi faisable, c'est d'ailleurs ce que je fais quand un processus attent mais qu'il n'a pas de message et que c'est un lecteur ou que c'est un écrivain et que le tube est plein.


== Points à améliorer 

Pour améliorer mes tubes je pourrais essayer de corrigé un problème qui vient quand je met l'ordonanceur qui est que les processus ne récupèrent plus la totalité du message mais qu'une partie, ce qui le coupe en deux ou plus et qui ne parait pas être un comportement voulu d'un tube.

== Conclusion

Pour conclure, ce projet de système concurent est une bonne façon de voir comment implémenter des méchanisme d'exclusion mutuelle dans un système déjà établi que nous devons comprendre pour modifier. C'est une bonne façon de voir comment les processus peuvent communiquer entre eux et comment ils peuvent se synchroniser pour ne pas avoir de conflit. 



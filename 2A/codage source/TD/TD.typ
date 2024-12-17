= Exo 1

== 1. Soit une source discrète émettant 2 messages de probabilités respectives p et q.
Quelle est l’expression de son entropie ? On la notera H(p,q).

$H(x) = E(i(x)) = -sum(p(x)log_2(p(x))) = -p*log_p (p)- q*log_2(q)$ 

== 2. Évaluer l’entropie de la source binaire pour p=0, p=1/2, p=1. Commentaires.

- $H(0,1)=0 "bit"$

- $H(1/2,1/2)=-(1/2)*log_2 (1/2) *2 = 1 "bit"$

- $H(1,0)=0 "bit"$

== 3. Quelle est l’entropie d’une source à N messages équiprobables ? Application pour N=8.

$H(x) = -sum(p(x)log_2(p(x))) = -sum_(k=1)^N ((1/N)*log_2(1/N)) = log_2 (N)$

Pour N = 8 : $H(x) = log_2(8)= 3 "bits"$

= Exo 2 
== Soit une source à 3 messages de probabilités : P(a) = 0.6 ; P(b) = 0.3 ; P(c) = 0.1.

== 1- Calculer l’entropie de la source.

$H(x) = -0.6 * log_2(0.6) - 0.3 * log_2(0.3) - 0.1 * log_2(0.1) = 1.29$

== 2- Quelle est l’efficacité d’un code binaire à longueur fixe ?

$E_"fixe" = H(x)/2 = 65%$



== 3- Quelle est l’efficacité d’un code binaire d’Huffman ?

code de Huffman : cf j'ai la flemme

$n = 1* 0.6 + 2 * (0.3+0.1) = 1.4$

$E_"Huffman" = H(x)/n = 1.29/1.4 = 92% $


== 4- Comment peut-on augmenter cette efficacité ?

On code le messages par blocs de 2 messages.

$n = 1 * 0.36+3*0.18*2+4*(0.09+0.06+0.06) = 2.67$

$n_"moy" = n/2 = 1.335$

$E = 97.38%$

= Exo 3

== 1- Calculer la matrice prédite et la matrice d’erreur de prédiction

matrice de prédiction :

$ mat(
  100, 102, 106, 92;
  98, 100, 103, 98;
  70, 85, 92, 96;
  72, 76, 84, 9;
)$

matrice d'erreur de prédiction :

$ mat(
  0, 0, 0, 0;
  0, 0, 1, 2;
  0, -5, 0, 2;
  0, 0, 0, -1;
)$
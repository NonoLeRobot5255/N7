#import "../../../../../template/template_2A.typ": *

#show: project.with(
  title: "Rapport des TP d'égalisation de canal",
  authors: ("MARTIN Nolann", "LESCOP Antoine"),
  teachers: ("POULLIAT Charly","MICHON Arthur"),
  year : "2024-2025",
  profondeur: 2,
)

= Introduction
Dans ces TP nous avons étudié l'égalisation de canal. Dans un premier temps nous avons étudié l'égalisation temporelle, puis dans un second temps l'égalisation fréquentielle. Nous allons restracé dans ce rendu les différentes étapes ainsi que les résultats obtenus.

Dans ces TP nous avons utilisé une modulation de type QPSK et un bruit blanc additif gaussien. Et nous étudierons 4 canaux diférents :

- $h_c = [1 0.8*exp(1i*pi/3) 0.3*exp(1i*pi/6)]$
- $h_c = [1 0.8*exp(1i*pi/3) 0.3*exp(1i*pi/6) 0.1*exp(1i*pi/12)]$
- $h_c=[0.04, -0.05, 0.07, -0.21, -0.5, 0.72, 0.36, 0, 0.21, 0.03, 0.07]$
- $h_c=[1 -a] $ avec $a=1.2$
= Transmission sur canal sélectif en fréquence : égalisation temporelle

== Canal de transmission

Dans cette première partie nous allons étudier le canal de transmission et comprendre comment le filtre du canal affecte nos données en sortie.

Nous pouvons dans un premier temps comprendre théoriquement ce qu'il va advenir de nos bits en sortie de canal, pour cela nous savons que le modèle en réception est le suivant :

- $y[n] = h*x[n] + b[n]$

avec $h$ le canal de transmission, $x$ les bits en entrée et $b$ le bruit additif gaussien. Nous pouvons donc estimer que même sans bruit, nous ne pourrons pas avoir un TEB nul car le canal ce que nous allons vérifier dans la suite.

=== Symboles sans bruit

Dans cette partie nous allons étudier les symboles en sortie de canal, en regardant nos constellations de sortie.

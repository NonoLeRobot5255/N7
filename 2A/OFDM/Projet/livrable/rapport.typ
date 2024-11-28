#import "../../../../template/template_2A.typ": *

#show: project.with(
  
  title: "Rapport du bureau d'étude sur l'OFDM",
  authors: (
    "MARTIN Nolann", ),
  teachers: (
    "BOUCHERET Marie-Laure", 
  ),
  year : "2024-2025",
)


= Intro 

Le but de ce projet est de réaliser une étude sur l'OFDM (Orthogonal Frequency Division Multiplexing) et de mettre en place un système de communication numérique basé sur cette technologie.

Nous serons dans un contexte de canal sélectif en fréquence et nous serons la plupart du temps sur un canal sans bruit et sur un mapping BPSK, sauf sur la dérnière partie où nous étudierons l'impact du bruit sur la transmission avec une modulation QPSK.

= Implantation de la chaine de transmission OFDM sans canal


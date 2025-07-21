#import "@preview/fletcher:0.5.6"  as fletcher: diagram, node, edge
#import fletcher.shapes: diamond

#let citation(term, name, date)={
  box(
    stroke: none,
    fill: rgb("#fcdefc"),
    width: 160mm,
    inset: 1em,
    radius: 20pt
  )[*#emoji.sparkles #emoji.ribbon Citation inspirante #emoji.ribbon #emoji.sparkles:  #linebreak() *#emph[#term] #align(right, [#emph[#emoji.flower.tulip #emoji.flower #name #emoji.butterfly #date #emoji.flower #emoji.flower.tulip]])]
}

= Normalisation : cartes de randonnées

*Si on fait + que demandé, on fait du hors sujet*


#diagram(
     node((0,0), table(
        columns: 1,
        [lieu],
        [- #underline[n° id] ;
      - nom ;
      - description;
      - n° tel.])
   ),
   node((5,0), table(
        columns: 1,
        [Symbole],
        [- #underline[*GPS (PK)*] ;
      - hebergement ;
      - point de vue ;
      - .])
   ),

   node((2.5,0), "Représente", stroke : 0.1em, shape : diamond),
   
//   node((2.5,5), table( columns: 1, [Ligne],[- #underline[point de départ] ; - nom ; -  ; -.]) ),

//   node((1.75,2.5), "point départ", stroke : 0.1em, shape : diamond),


   
   edge((0,0), (2.5,0),"<|-", label : $1.1$ ),
   edge((2.5,0), (5,0), label : $1.n$),
   
 )


#v(40mm)

#diagram(
     node((0,0), table(
        columns: 1,
        [ligne],
        [- #underline[*GPS*] ;
      - nature (lieu ou source);
      - description;
      - nom])
   ),
   node((5,0), table(
        columns: 1,
        [Point],
        [- #underline[*GPS (PK)*] ;
      -  ;
      -  ;
      - .])
   ),
   node((2.5,0), "Compose", stroke : 0.1em, shape : diamond),
   edge((0,0), (2.5,0),"<|-", label : $0.*$ ),
   edge((2.5,0), (5,0), label : $1.*$),
   edge((2.5,0), (2.5,0.5), label : $"Numéro d'ordre"$),   
 )

 Une ligne possède au moins 1 point et peut en avoir plusieurs.
 Un point peut appartenir à 0 ligne, ou à plusieurs lignes.


 == Schéma Relationnel

 Normalement chaque entité se transforme en relation:
 === Schéma 1:
 - Représente est une association 1.n, donc elle peu être représentée dans un des 2 autres entités. On le mets dans le coté où il y a 1.1 car il n'y en aura toujours qu'un.
 - Symbole(#underline[GPS], valeur)
 - Lieu(#underline[GPS], nom, description, num tél, Représente, _GPS_symbole (FK)_)


=== Schéma 2:

- Ligne(#underline[GPS], nature, nom, description)
- Point(#underline[GPS]) $=>$ Pas de grand interet à l'ecrire (redondance donc à éviter)
- Compose(GPS ligne, GPS point, num d'ordre) *on mets les PK des entités qu'il lie*
    - La clé #underline[(GPS ligne, GPS point] est valable mais pas folle (on pourra pas passer 2 fois par le même point)
    - On peut faire #underline[GPS ligne, num d'ordre] qui est une meilleure idée (je sais plus pk)
    - On peut aussi le mettre qu'un seul attribut comme clé, ici si on l'explique un minumum, on peut mettre uniquement #underline[num ordre]



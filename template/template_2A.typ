// The project function defines how your document looks.
// It takes your content and some metadata and formats it.
// Go ahead and customize it to your liking!
#let project(title: "", authors: (),teachers: (), annee : "", body) = {
  // Set the document's basic properties.
  set document(author: authors, title: title)
  set page(numbering: "1", number-align: right)
  set text(font: "New Computer Modern", lang: "fr")

  // Title row.
  align(right)[
   #box( figure(
  image("ENSEEIHT_logo.png",width: 20%)
))
#line(length: 95%, stroke: black)
  ]
  align(center)[
    #block(text(weight: 700, 1.75em, title))
  ]

  // Author information.
  pad(
    top: 0.5em,
    x: 2em,
    align(text("Auteur"+ if authors.len()>1 {"s"} + " : ", size: 1.25em),center),
  )
  pad(
    bottom: 0.5em,
    x: 2em,
    grid(
      
      columns: (1fr,) * calc.min(2, authors.len()),
      gutter: 1em,
      
      ..authors.map(author => align(center, strong(author))),
    ),
  )
  pad(
    top: 0.5em,
    x: 2em,
    align(text("professeur"+ if teachers.len()>1 {"s"} + " : ", size: 1.25em),center),
  )
  pad(
    bottom: 0.5em,
    x: 2em,
    grid(
      
      columns: (1fr,) * calc.min(2, teachers.len()),
      gutter: 1em,
      
      ..teachers.map(teacher => align(center, strong(teacher))),
    ),
  )
  pad(
    top: 0.5em,
    x: 10em,
    grid(
    columns: 2, 
    gutter: 20%, 
    [#text("Projet de deuxième année de SN", size: 0.75em)],

    [#text("année : " + annee, size: 0.75em)]
  )
)

  align(line(length: 95%, stroke: black),right)

  align(text("",size : 23pt),center)
  pagebreak()

  outline( depth: 4 , indent : 2em )

  pagebreak()
  // Main body.
  set par(justify: true)
  body
  
}


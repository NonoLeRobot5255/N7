#let project(title: "", authors: (),teachers: (), year : "",profondeur: int, body) = { //modulable design
  set document(author: authors, title: title)
  set page(numbering: "1", number-align: right)
  set heading(numbering: "1.1.")
  set text(font: "New Computer Modern", lang: "fr")

  // ENSEEIHT logo.
  grid(
  columns: (2.5fr, auto),
  gutter: 4.5em,
  [
    #box(figure(image("INP.jpeg", width: 10em))),
    
  ],
  [

    #box(figure(image("ENSEEIHT_logo.png", width: 11em)))
    
  ]
)
  align(right)[
  // here we open the block and write the title and thematic
  #line(length: 95%, stroke: black)
  ]
  align(center)[
    #block(text(weight: 700, 1.75em, title))
  ]

  // Author(s)
  pad(
    top: 0.5em,
    x: 2em,
    align(text("Auteur"+ if authors.len()>1 {"s"} + " : ", size: 1.25em),center),
  )
  // here I write all the authors
  pad(
    bottom: 0.5em,
    x: 2em,
    grid(
      
      columns: (1fr,) * calc.min(2, authors.len()),
      gutter: 1em,
      
      ..authors.map(author => align(center, strong(author))),
    ),
  )
  // Teacher(s)
  pad(
    top: 0.5em,
    x: 2em,
    align(text("professeur"+ if teachers.len()>1 {"s"} + " : ", size: 1.25em),center),
  )
  // here I write all the teachers
  pad(
    bottom: 0.5em,
    x: 2em,
    grid(
      
      columns: (1fr,) * calc.min(2, teachers.len()),
      gutter: 1em,
      
      ..teachers.map(teacher => align(center, strong(teacher))),
    ),
  )
  // here I write the year and my grade
  pad(
    top: 0.5em,
    x: 10em,
    grid(
    columns: 2, 
    gutter: 20%, 
    [#text("Projet de deuxième année de SN", size: 0.75em)],

    [#text("année : " + year, size: 0.75em)]
  )
)

  align(line(length: 95%, stroke: black),right)

  align(text("",size : 23pt),center)
  pagebreak()
  // table of contents.
  outline( depth: profondeur , indent : 2em )

  pagebreak()
  // main body.
  set par(justify: true)
  body
  
}


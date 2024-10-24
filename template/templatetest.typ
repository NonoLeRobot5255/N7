// The project function defines how your document looks.
// It takes your content and some metadata and formats it.
// Go ahead and customize it to your liking!
#let project(title: "", authors: (), body) = {
  // Set the document's basic properties.
  set document(author: authors, title: title)
  set page(numbering: "1", number-align: center)
  set text(font: "Linux Libertine", lang: "fr")

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
    bottom: 0.5em,
    x: 2em,
    grid(
      columns: (1fr,) * calc.min(3, authors.len()),
      gutter: 1em,
      ..authors.map(author => align(center, strong(author))),
    ),
  )
  align(text("Projet de première année de SN"),center)
  align(line(length: 95%, stroke: black),right)

  align(text("",size : 23pt),center)
  pagebreak()

  outline( depth: 4 , indent : 2em )

  pagebreak()
  // Main body.
  set par(justify: true)
  body
  
}


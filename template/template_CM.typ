#let th(theoreme,n) = {
  context(
    box(
      block(
        fill: rgb("#7FB3D5"),
        inset: 8pt,
        radius: 4pt,
        strong("Définition ") + strong(str(n)) + strong(" :\n") + align(center, theoreme)
      )
    )
  )
}


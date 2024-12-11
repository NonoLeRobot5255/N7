#let n_th = state("n_th", 1)

#let th(theoreme) = {
  n_th.update( + 1) // Met à jour la valeur de n_th
  context(
    box(
      block(
        fill: rgb("#7FB3D5"),
        inset: 8pt,
        radius: 4pt,
        "Théorème " + str(n_th.get(2)) + "\n" + align(center, theoreme)
      )
    )
  )
}

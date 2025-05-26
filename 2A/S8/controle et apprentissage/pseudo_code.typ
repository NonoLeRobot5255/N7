#import "@preview/algorithmic:0.1.0"
#import algorithmic: algorithm


#box(
  inset: 8pt,
  fill: luma(95%),
  radius: 6pt,
  stroke: (thickness: 1pt, paint: luma(70%)),
  [
    #strong("Algorithme : Thompson Sampling")
    #algorithm({
      import algorithmic: *
      Function("Thompson Sampling", args: ($B(mu_1)$, $B(mu_2), B(mu_3)$), {
        Cmt[On initialise les variables]
      })
    })
  ]
)


#box(
  inset: 8pt,
  fill: luma(95%),
  radius: 6pt,
  stroke: (thickness: 1pt, paint: luma(70%)),
  [
    #strong("Algorithme : UCB algorithm")
    #algorithm({
      import algorithmic: *
      Function("UCB_algo", args: (), {
        Cmt[On initialise les variables]
      })
    })
  ]
)
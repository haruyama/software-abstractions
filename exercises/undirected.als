module exercises/undirected
sig Node {adjs: set Node}
pred acyclic () {
  adjs = ~adjs
  no iden & adjs
  all n : Node | Node in n.^adjs
  all n : Node | all disj x, y: n.adjs | x.^(adjs - x -> n) & y.^(adjs - y -> n) = none
}

run acyclic for exactly 5 Node

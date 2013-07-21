module exercises/tree

sig Node {}
pred isTree ( r : Node -> Node) {
	one root : Node | Node in root.*r
	no n : Node | n in n.^r
	all n : Node | lone r.n
	}
run isTree for 4

module exercises/spanning_tree
sig Node {}
pred isTree ( r : Node -> Node) {
	one root : Node | Node in root.*r
	no n : Node | n in n.^r
	all n : Node | lone r.n
	}

fun nodes ( r : Node -> Node) : set Node {
	Node.r + r.Node
--	Node.r
}
pred spans ( r1, r2 : Node -> Node) {
	nodes[r1] = nodes[r2]
	r1 in r2
}
pred show (r, r1, r2 : Node -> Node) {
	spans [r1, r] and isTree[r1]
	spans [r2, r] and isTree[r2]
	r1 != r2
}
run show for 3

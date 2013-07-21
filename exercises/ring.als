module exercises/ring
sig Node {next: set Node}
pred isRing () {
	all n: Node | Node in n.^next
--  all n: Node | #n.next = 1
}

run isRing for exactly 4 Node

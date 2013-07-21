module exercises/distribution
sig Node {}

assert union {
	all s: set Node, p, q: Node -> Node | s.(p + q) = s.p + s.q
}
check union for 10

assert minus {
	all s: set Node, p, q: Node -> Node | s.(p - q) = s.p - s.q
}
check minus for 2

assert intersection {
	all s: set Node, p, q: Node -> Node | s.(p & q) = s.p & s.q
}
check intersection for 2

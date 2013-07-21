module exercises/handshake

sig Person {
	partner: one Person,
	handshake: set Person
	}

one sig Alice extends Person {}
one sig Bob extends Person {}

fact {
	Alice.partner = Bob

	~partner in partner
	no iden & partner
	
	~handshake in handshake
	no iden & handshake

  no p: Person | p.partner in p.handshake

	let person = Person - Alice |
		all disj p,q: person | #p.handshake != #q.handshake
}

run {} for 10 but exactly 4 Person

run {} for 10 but exactly 6 Person

run {} for 20 but exactly 10 Person

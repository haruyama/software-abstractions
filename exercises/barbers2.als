module exercises/barbers2

abstract sig Person {}
sig Woman extends Person {}
sig Man extends Person {shaves: set Man}
one sig Barber in Person {}

fact {
	Barber in Man => Barber.shaves = {m: Man | m not in m.shaves}
	}

run {} for 2

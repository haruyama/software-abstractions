module exercises/barbers

sig Man {shaves: set Man}
one sig Barber extends Man {}

fact {
	Barber.shaves = {m: Man | m not in m.shaves}
	}

run {} for 10

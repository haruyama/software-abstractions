module exercises/barbers3

sig Man {shaves: set Man}
sig Barber extends Man {}

fact {
	Barber.shaves = {m: Man | m not in m.shaves}
	}

run {} for 10

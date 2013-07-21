module exercises/barbers4

sig Man {shaves: set Man}
some sig Barber extends Man {}

fact {
	Barber.shaves = {m: Man | m not in m.shaves}
	}

run {} for 10

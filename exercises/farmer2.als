module exercises/farmer2
open util/ordering [Time]


-- one sig Farmer extends Performer {}
abstract sig Pickup {}
one sig Goat extends Pickup {}
one sig Cabbage extends Pickup {}
one sig Wolf extends Pickup {}

abstract sig Place {}

one sig A extends Place {}
one sig B extends Place {}

sig Time {
	farmer_place : Place,
	pickup: Pickup -> Place
}

pred init (t: Time) {
  t.farmer_place = A 
	all x: Pickup, y : x.(t.pickup) | y = A 
}

pred final (t: Time) {
  t.farmer_place = B
	all x: Pickup, y : x.(t.pickup) | y = B
}

pred move(t, t': Time) {
	t.pickup = t'.pickup
	t.farmer_place = A 
		implies {
		  t'.farmer_place = B
    }	
		else {
		  t'.farmer_place = A
		}
}


pred carry (t, t': Time) {
	t.farmer_place = A 
		implies {
		  t'.farmer_place = B
			one x: Pickup, y : x.(t.pickup) | y = A && t'.pickup = t.pickup - (x -> A) + (x -> B) 
    }	
		else {
		  t'.farmer_place = A
	    one x: Pickup, y : x.(t.pickup) | y = B && t'.pickup = t.pickup - (x -> B) + (x -> A) 
		}
}

pred goatEatsCabbage (t : Time) {
	t.farmer_place != Goat.(t.pickup)
	Goat.(t.pickup) = Cabbage.(t.pickup)
}

pred wolfEatsGoat (t: Time) {
	t.farmer_place != Wolf.(t.pickup)
	Goat.(t.pickup) = Wolf.(t.pickup)
}

fact {
	all t : Time | #t.pickup = 3 and not goatEatsCabbage[t] and not wolfEatsGoat[t]
	#Pickup = 3
	init [first]
  final [last]
	not init [Time - first]
	not final [Time - last]
  all t: Time - last | let t' = next [t] | carry[t, t'] or move[t, t']
}


run {} for 8

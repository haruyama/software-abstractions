module exercises/farmer
open util/ordering [Action]


-- one sig Farmer extends Performer {}
abstract sig Pickup {}
one sig Goat extends Pickup {}
one sig Cabbage extends Pickup {}
one sig Wolf extends Pickup {}

abstract sig Place {}

one sig A extends Place {}
one sig B extends Place {}

sig Action {
	farmer_place : Place,
	pickup: Pickup -> Place
}

pred init (a: Action) {
  a.farmer_place = A 
	all x: Pickup, y : x.(a.pickup) | y = A 
}

pred final (a: Action) {
  a.farmer_place = B
	all x: Pickup, y : x.(a.pickup) | y = B
}

pred move(a, a': Action) {
	a.pickup = a'.pickup
	a.farmer_place = A 
		implies {
		  a'.farmer_place = B
    }	
		else {
		  a'.farmer_place = A
		}
}


pred carry (a, a': Action) {
	a.farmer_place = A 
		implies {
		  a'.farmer_place = B
			one x: Pickup, y : x.(a.pickup) | y = A && a'.pickup = a.pickup - (x -> A) + (x -> B) 
    }	
		else {
		  a'.farmer_place = A
	    one x: Pickup, y : x.(a.pickup) | y = B && a'.pickup = a.pickup - (x -> B) + (x -> A) 
		}
}

pred goatEatsCabbage (a : Action) {
	a.farmer_place != Goat.(a.pickup)
	Goat.(a.pickup) = Cabbage.(a.pickup)
}

pred wolfEatsGoat (a: Action) {
	a.farmer_place != Wolf.(a.pickup)
	Goat.(a.pickup) = Wolf.(a.pickup)
}

fact {
	all a : Action | #a.pickup = 3 and not goatEatsCabbage[a] and not wolfEatsGoat[a]
	#Pickup = 3
	init [first]
  final [last]
	not init [Action - first]
	not final [Action - last]
  all a: Action - last | let a' = next [a] | carry[a, a'] or move[a, a']

}



run {} for 8

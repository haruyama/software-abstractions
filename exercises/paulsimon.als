module exercises/paulsimon

open util/ordering [Platform]

sig Man {
--	ceiling: lone Platform,
	ceiling: lone Platform,
	floor : Platform
	}

sig Platform {}

fact {
--	one disj a, b: Man | one a.ceiling => a.ceiling = b.floor
	all a: Man | some b: Man | a.ceiling = b.floor
--	all a: Man | some b: Man | one a.ceiling =>  a.ceiling = b.floor
--	all a: Man | lt[a.floor, a.ceiling]
	}

run {} for 10

assert floorIsCeiling {
  all a: Man | some b: Man | a.floor = b.ceiling

}

check floorIsCeiling

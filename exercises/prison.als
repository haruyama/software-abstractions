module exercises/prison

sig Gang {members: set Inmate}
sig Inmate {room: Cell}
sig Cell {}

pred safe () {
	all disj a, b : Gang, am: a.members, bm: b.members | am.room != bm.room
	}

run safe for 3 but exactly 2 Gang

run { not safe} for 3 but exactly 2 Gang

pred happy () {
	all a: Gang | no a.members.room & (Inmate - a.members).room 
	
  }

run happy for 3 but exactly 2 Gang

assert safeIsHappy {
	safe => happy
}

check safeIsHappy for 5

/*
fact {
	safe => happy
}
*/

pred safe2 {

	happy
}

run safe2 for 3 but exactly 2 Gang

assert safe2IsHappy {
	safe2 => happy
}

check safe2IsHappy for 5

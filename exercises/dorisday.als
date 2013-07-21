module exercises/dorisday

sig Person {
	love: set Person
}


fact {
	one he, i : Person | love.he = Person && he.love = i 

}

run {}

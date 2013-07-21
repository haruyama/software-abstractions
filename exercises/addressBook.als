module exercises/addressBook

abstract sig Name {
	address: set Addr+Name
}

sig Alias, Group extends Name { }

sig Addr { }

fact {
	no n: Name | n in n.^address
--  all n: Name | some a: Addr | a in n.^address

  all a: Alias | lone a.address
}

pred show {
	some n : Name | some n.address.address
	some g : Group | not g.address = none

  some g : Group | g.address = none
	some a: Alias | some a
}
/*
Name.address & Name
Group - address.(Addr + Name)
-- Group - address.(Group.address)
^address & Alias -> Addr
address - Name -> Name

*/

run show for 3

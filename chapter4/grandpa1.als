module language/grandpa1
abstract sig Person {
	father: lone Man,
	mother: lone Woman
	}
sig Man extends Person {
	wife: lone Woman
	}
sig Woman extends Person {
	husband: lone Man
	}

fact {
	no p: Person | p in p.^(mother + father)
	wife = ~husband
	no (husband + wife) & ^(mother + father)
}

assert NoSelfFather {
	no m: Man | m = m.father
}
check NoSelfFather

fun grandpas (p: Person): set Person {
--	p.(mother + father).father
	let parent = mother + father + father.wife + mother.husband |
		p.parent.parent & Man
	}

pred ownGrandpa (p: Person) {
	p in grandpas [p]
	}
run ownGrandpa for 10

assert NoSelfGrandpa {
	no p: Person | p in grandpas [p]
	}
check NoSelfGrandpa for 4 Person

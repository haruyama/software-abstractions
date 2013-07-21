module exercises/properties
open util/relation

run {
	some r: univ -> univ {
		some r
		r.r in r
--   	no iden & r
		~r in r
  	~r.r in iden
  	r.~r in iden
		univ in r.univ
		univ in univ.r
		}
	} for 4 

assert ReformulateNonEmptinessOK {
	all r: univ -> univ |
		some r iff (some x, y : univ | x -> y in r)
	}
check ReformulateNonEmptinessOK

assert TransitivenessOK {
	all r: univ -> univ |
--		r.r in r iff (all x, y, z: univ | x -> y in r && y -> z in r => x -> z in r)
	r.r in r iff (all x: univ, y : x.r, z: y.r| x -> z in r)
  }
check TransitivenessOK

assert IrreflexiveOK {
	all r: univ -> univ |
		no iden & r iff (no x : univ | x -> x in r)
  }
check IrreflexiveOK

assert SymmetricOK {
	all r: univ -> univ |
		~r in r iff (all x, y : univ | x -> y in r => y -> x in r)
  }
check SymmetricOK

assert FunctionalOK {
	all r: univ -> univ |
--		~r.r in iden iff (all x, y: univ | x -> y in r =>
--			 y -> y in ~r.r and (no z: univ | y -> z in ~r.r and y != z) and
--			 (no a: univ | a -> y in ~r.r and a != y))

		~r.r in iden iff (all x, y, z: univ | x -> y in r && x -> z in r => y =z)
	} 

check FunctionalOK

assert InjectiveOK {
	all r: univ -> univ |
/*
		r.~r in iden iff (all x, y: univ | x -> y in r =>
			 x -> x in r.~r and (no z: univ | x -> z in r.~r and x != z) and
			 (no a: univ | a -> x in r.~r and a != x))
*/
	r.~r in iden iff (all x, y, z: univ | x -> y in r && z -> y in r => x =z)
	} 

check InjectiveOK

assert TotalOK {
	all r: univ -> univ |
			univ in r.univ iff all x: univ | some x.r
  }
check TotalOK

assert OntoOK {
	all r: univ -> univ |
		univ in univ.r iff all x: univ | some r.x
  }
check OntoOK



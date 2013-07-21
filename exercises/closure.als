module exercises/closure

pred transCover (R, r: univ -> univ) {
	r in R
  (all x, y, z: univ | x -> y in R && y -> z in R => x -> z in R)
  }

pred transClosure(R, r: univ -> univ) {
	transCover[R, r]
--   no a, b : univ | a -> b in R && transCover[R - (a -> b), r]
    all a: univ, b : a.R | not transCover[R - (a -> b), r]
  }

assert Equivalence {
	all R, r: univ -> univ | transClosure [R, r] iff R = ^r
	}
check Equivalence for 3


pred transClosure' (R, r: univ -> univ, C: univ -> univ -> univ) {
	transCover[R - iden,r]
    all x: univ | x in x.R


	all x, y, z, u: univ {
		x -> x -> y not in C
		x -> y -> u in C and y -> z -> u in C => x -> z -> u in C
		x -> y -> y in C and y -> z -> z in C and x != z => x -> z -> z in C
		x -> y in R and x != y => x -> y -> y in C
		x -> y -> y in C => some v : univ | x -> v in R and x -> v -> y in C
		x -> y -> z in C and y != z => y -> z -> z in C
		}
	}

assert Equivalence' {
	all R, r: univ -> univ, C: univ -> univ -> univ |
  	transClosure'[R, r, C] iff R = *r
	}
	

check Equivalence' for 3
	

module exercises/addressBook2

sig Addr, Name {}

sig Book {
	addr: Name -> (Name + Addr)
	}

pred inv (b: Book) {
	let addr = b.addr |
		all n : Name {
			n not in n.^addr
			some addr.n => some n.^addr & Addr
			}
	}

pred add(b, b' : Book, n : Name, t: Name + Addr) {
	t in Name => some t.^(b.addr) & Addr && t in ^(b.addr).t 
	b'.addr = b.addr + n -> t
	}

pred del(b, b' : Book, n: Name, t: Name + Addr) {
/*
  n in (b.addr - n -> t).Name => some n.^(b.addr - n -> t) & Addr
  not n in Name.(b.addr - n -> t) => all p : b.addr.n |  some p.^(b.addr - n -> t) & Addr
*/
	let address = b.addr - n -> t | {
		n in Name.address => some n.^address & Addr
		not n in Name.address => all p : b.addr.n | some p.^address & Addr
		}
	b'.addr = b.addr - n -> t
	}

fun lookup(b: Book, n: Name) : set Addr {
	n.^(b.addr) & Addr
	}


run inv for 3

pred notInv (b: Book) {
	not inv[b]
}
	
run notInv for 3

pred showAdd (b, b' : Book, n: Name, t: Name + Addr) {
	not b in b'
	add [b, b', n, t]
	#Name.(b'.addr) > 1
	}

run showAdd for 3 but 2 Book

pred showDel (b, b' : Book, n: Name, t: Name + Addr) {
	not b in b'
	del [b, b', n, t]
	#Name.(b.addr) > 1
	}

run showDel for 3 but  2 Book


pred addResultIsNotInv(b, b' : Book, n: Name, t: Name + Addr) {
	not b in b'
	inv[b]
	add [b, b', n, t]
	#Name.(b'.addr) > 1
	notInv[b']
	}

run addResultIsNotInv for 1 but 2 Book
run addResultIsNotInv for 5 but 2 Book

pred delResultIsNotInv(b, b' : Book, n: Name, t: Name + Addr) {
	not b in b'
	inv[b]
	del [b, b', n, t]
	#Name.(b.addr) > 1
	notInv[b']
	}

run delResultIsNotInv for 2 but 2 Book
run delResultIsNotInv for 5 but 2 Book

module exercises/phones

sig Phone {
	requests: set Phone,
	connects: lone Phone,
	}

fact {
	connects in requests
	~connects.connects in iden
	connects.~connects in iden
	all p : Phone, q : p.connects | no q.connects
	no ~connects & connects

}

pred show {
	no iden & requests
  no iden & connects

	some connects
	some requests
  }

run show for 4

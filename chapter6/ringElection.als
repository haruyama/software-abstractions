module chapter6/ringElection

open util/ordering[Time]
open util/ordering[Process]

sig Time {}

sig Process {
	succ: Process,
	toSend: Process -> Time,
	elected: set Time
	}

fact Ring { all p: Process | Process in p.^succ}

pred init (t: Time) {all p: Process | p.toSend.t = p }

pred step (t, t': Time, p: Process) {
	let from = p.toSend, to = p.succ.toSend |
		some id: from.t {
			from.t' = from.t - id
			to.t' = to.t + (id - p.succ.prevs)
			}
  }

fact DefineElected {
	no elected.first
	all t: Time - first |
		elected.t = {p: Process | p in p.toSend.t - p.toSend.(t.prev) }
	}

fact Traces {
	first.init
	all t: Time - last | let t' = t.next |
		all p: Process |
			step [t, t', p] or step [t, t', succ.p] or skip[t,t',p]
	}

pred skip (t, t': Time, p: Process) {
	p.toSend.t = p.toSend.t'
	}

pred show {
	some elected
	}

run show for 3 Process, 4 Time

assert AtMostOneElected {
	lone elected.Time
	}

check AtMostOneElected for 3 Process, 7 Time

pred progress {
	all t: Time - last |
		some Process.toSend.t =>
			some p: Process | not skip[t, t.next, p]
	}

assert AtLeastOneElected {
	progress => some t:Time | some elected.t
	}

check AtLeastOneElected for 3 Process, 7 Time

pred looplessPath {
	no disj t, t':Time | toSend.t = toSend.t'
	}

run looplessPath for 3 Process, 12 Time

run looplessPath for 3 Process, 13 Time

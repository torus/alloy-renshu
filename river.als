open util/ordering[Time]

sig Time {}
abstract sig Position {}
one sig Left, Right extends Position {}

abstract sig Actor {}

one sig Goat, Wolf, Cabbege, Man extends Actor {}

one sig State {
	pos: Position -> set Actor -> Time
}

pred init (t: Time) {
	State.pos[Left].t = Actor
	no State.pos[Right].t
}

fact Traces {
	first.init
	all t: Time - last |
		(one obj: Actor - Man, p: Position | deliver [t, obj, p])
		or (one p: Position | justMove [t, p])
}

pred deliver (t: Time, obj: Actor - Man, p: Position) {
	let t' = t.next, p' = Position - p |
		(Man + obj) in State.pos[p].t
		and State.pos[p].t' = State.pos[p].t - (Man + obj)
		and State.pos[p'].t' = State.pos[p'].t + Man + obj
}

pred justMove (t: Time, p: Position) {
	let t' = t.next, p' = Position - p |
		Man in State.pos[p].t
		and State.pos[p].t' = State.pos[p].t - Man
		and State.pos[p'].t' = State.pos[p'].t + Man
}

pred doNotEat {
	no t: Time |
		(State.pos.t.Wolf = State.pos.t.Goat
		and State.pos.t.Goat != State.pos.t.Man)
		or (State.pos.t.Cabbege = State.pos.t.Goat
		and State.pos.t.Goat != State.pos.t.Man)
}

pred finish (t: Time) {
	State.pos[Right].t = Actor
	no State.pos[Left].t
}

pred doNotRepeat {
	no disj t, t': Time | State.pos.t = State.pos.t'
}

pred alldone {
	doNotEat
	doNotRepeat
	last.finish
}

run alldone for 8

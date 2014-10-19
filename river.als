open util/ordering[Time]

sig Time {}
abstract sig Position {pos: set Actor -> Time}
one sig Left, Right extends Position {}

abstract sig Actor {}

one sig Goat, Wolf, Cabbege, Man extends Actor {}

pred init (t: Time) {
    pos[Left].t = Actor
    no pos[Right].t
}

fact Traces {
    first.init
    all t: Time - last |
        (one obj: Actor - Man, p: Position | deliver [t, obj, p])
        or (one p: Position | justMove [t, p])
}

pred deliver (t: Time, obj: Actor - Man, p: Position) {
    let t' = t.next, p' = Position - p |
        (Man + obj) in pos[p].t
        and pos[p].t' = pos[p].t - (Man + obj)
        and pos[p'].t' = pos[p'].t + Man + obj
}

pred justMove (t: Time, p: Position) {
    let t' = t.next, p' = Position - p |
        Man in pos[p].t
        and pos[p].t' = pos[p].t - Man
        and pos[p'].t' = pos[p'].t + Man
}

pred doNotEat {
    no t: Time |
        (pos.t.Wolf = pos.t.Goat
        and pos.t.Goat != pos.t.Man)
        or (pos.t.Cabbege = pos.t.Goat
        and pos.t.Goat != pos.t.Man)
}

pred finish (t: Time) {
    pos[Right].t = Actor
    no pos[Left].t
}

pred doNotRepeat {
    no disj t, t': Time | pos.t = pos.t'
}

pred alldone {
    doNotEat
    doNotRepeat
    last.finish
}

run alldone for 8

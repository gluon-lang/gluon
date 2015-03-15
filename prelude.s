
data Option a = Some(a) | None()

trait Eq a {
    eq : (a, a) -> Bool;
}

impl Eq for Int {
    eq : (Int, Int) -> Bool;
    eq = \l r -> {
        l == r
    }
}

impl Eq for Float {
    eq : (Float, Float) -> Bool;
    eq = \l r -> {
        l == r
    }
}

impl <Eq a> Eq for Option a {
    eq : (Option a, Option a) -> Bool;
    eq = \l r -> {
        match l {
            Some(l_val) => {
                match r {
                    Some(r_val) => { eq(l_val, r_val) }
                    None() => { false }
                }
            }
            None() => {
                match r {
                    Some(_) => { false }
                    None() => { true }
                }
            }
        }
    }
}

impl <Eq a> Eq for [a] {
    eq : ([a], [a]) -> Bool;
    eq = \l r -> {
        let ii = 0;
        let length = array_length(l);
        if length == array_length(r) {
            let result = true;
            while ii < length {
                if eq(l[ii], r[ii]) { }
                else {
                    result = false;
                }
                ii = ii + 1;
            }
            result
        }
        else {
            false
        }
    }
}

data Ordering = LT | EQ | GT

trait Ord a {
    compare : (a, a) -> Ordering;
}

impl Ord for Int {
    compare : (Int, Int) -> Ordering;
    compare = \l r -> {
        if l < r {
            LT()
        }
        else if l == r {
            EQ()
        }
        else {
            GT()
        }
    }
}

impl Ord for Float {
    compare : (Float, Float) -> Ordering;
    compare = \l r -> {
        if l < r {
            LT()
        }
        else if l == r {
            EQ()
        }
        else {
            GT()
        }
    }
}
impl <Ord a> Ord for Option a {
    compare : (Option a, Option a) -> Ordering;
    compare = \l r -> {
        match l {
            Some(l_val) => {
                match r {
                    Some(r_val) => { compare(l_val, r_val) }
                    None() => { LT() }
                }
            }
            None() => {
                match r {
                    Some(r_val) => { GT() }
                    None() => { EQ() }
                }
            }
        }
    }
}


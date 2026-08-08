use prusti_contracts::*;

fn main() {}

// TODO: Consider overflows in these tests

#[ensures(result == old(*x))]
fn immref_arg(x: &i32) -> i32 {
    *x
}

#[ensures(*result == old(*x))]
fn immref_reborrow(x: &i32) -> &i32 {
    let y = x;
    let z = &(*y);
    z
}

#[ensures(result)]
fn immref_call(mut k: i32) -> bool {
    let x = &k;

    let j = immref_arg(x);
    let y = immref_reborrow(x);

    if j != *y {
        return false;
    }

    k += 1;

    k > j
}

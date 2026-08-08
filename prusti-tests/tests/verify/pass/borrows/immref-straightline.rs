use prusti_contracts::*;

fn main() {}

// TODO: Consider overflows in these tests

#[ensures(result == old(k) * 3)]
fn immref_reborrow(k: i32) -> i32 {
    // Borrow
    let x = &k;
    // Re-borrow
    let y = &(*x);
    // Copy ref (BorrowFlow edge)
    let z = y;

    *x + *y + *z
}

#[ensures(result == old(k) + 5)]
fn immref_release(mut k: i32) -> i32 {
    let x = &k;
    let j = *x;
    if j == k {
        k += 5;
    }

    if k > j {
        k
    } else {
        j
    }
}

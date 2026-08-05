use prusti_contracts::*;

fn main() {}

#[ensures(result == old(k))]
fn immref_straightline(k: i32) -> i32 {
    // Borrow
    let x = &k;
    // Re-borrow
    let y = &(*x);
    // Copy ref (BorrowFlow edge)
    let z = y;

    prusti_assert_eq!(1, 0);
    // prusti_assert_eq!({ *x }, { *y });
    // prusti_assert_eq!(*x, *z);
    // prusti_assert_eq!(*x, k);

    *x
}

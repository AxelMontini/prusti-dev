use prusti_contracts::*;

#[ensures(result == 1)]
fn client() -> i32 {
    let mut a = 0;
    let b = &mut a;
    *b = 1;
    let c = &a;
    *c
}

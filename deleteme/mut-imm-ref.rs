use prusti_contracts::*;

#[ensures(result == 21)]
pub fn simple_mixed() -> i32 {
    let mut x = 0;
    let y = &mut x;
    *y = 21;
    let z = &x;
    *z
}

#[ensures(result == (*x == 5))]
#[ensures(old(*x) == *x)]
fn is_cool_mut(x: &mut i32) -> bool {
    *x == 5
}

#[ensures(result == (old(*x) == 5))]
fn is_cool(x: &i32) -> bool {
    *x == 5
}

#[ensures(result == true)]
pub fn lend() -> bool {
    let mut x = 123;
    let z = is_cool_mut(&mut x);
    let y = is_cool(&x);
    y == z
}

#[ensures(result == 4)]
pub fn borrow_slice() -> i32 {
    let x = 1;
    let y = 2;

    let s = &[&x, &x, &y];

    *s[0] + *s[1] + *s[2]
}

#[pure]
#[requires(count >= 0 && count <= 10)]
#[ensures(result == *v * count)]
pub fn recurse(v: &i32, count: i32) -> i32 {
    if count == 0 {
        0
    } else {
        *v + recurse(v, count - 1)
    }
}

pub fn use_recurse() {
    let mut x = 5;

    let m = recurse(&x, 5);

    assert_eq!(m, 25);

    let y = &mut x;
    *y = 0;

    assert_eq!(x, 0);
}

/*
// Ofc this snipped does not compile.
// Prusti's encoding for immrefs MUST (assuming this would compile) result in a program that fails to verify
// due to missing permissions at `&mut x`, since thief is still live and has some permission to `p_Int_i32(x)`.
struct Thief<'a> {
    x: &'a i32,
}

pub fn theft() {
    let mut x = 0;

    let t = Thief {x: &x};

    let y = &mut x;

    let z = *t.x;
}
*/

pub fn reborrow_write() {
    let mut x = 0;

    let y = reborrower(true, &x, &x);

    let z = *y;

    x = 1; // here we should get back full access to x

    assert_ne!(x, z);
}

#[ensures(if which { *result == *x } else { *result == *y })]
pub fn reborrower<'a>(which: bool, x: &'a i32, y: &'a i32) -> &'a i32 {
    if which {
        x
    } else {
        y
    }
}

#[after_expiry(before_expiry(*result) == *x)]
pub fn reborrower_mut(x: &mut i32) -> &mut i32 {
    x
}

#[ensures(*x == 1)]
pub fn simple_mut(x: &mut i32) {
    *x = 1;
    // Should give back permissions with wand
}

pub fn how_to_generics() {
    let x = Some(0i32);

    let y = &x;

    let z = *y;
}

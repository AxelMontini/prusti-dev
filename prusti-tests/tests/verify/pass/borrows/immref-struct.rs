use prusti_contracts::*;

fn main() {}

#[derive(Copy, Clone)]
struct Foo {
    x: u32,
    y: u32,
}

struct Bar<'x> {
    x: &'x u32,
    y: u32,
}

#[requires(f.x == 5)]
fn immref_struct_straightline(mut f: Foo) {
    let x = &f.x;
    let z = x;
    let f_ref = &f;
    // f_ref expires, now can mutate f.y

    f.y = 5;

    // tuples work?
    let a = (&f.x, &f.y);
    assert_eq!(*a.0, *a.1);

    // what happens when copying a struct?
    let f2 = f;
    let j = *a.0; // keep the ref alive
}

#[ensures(old(f.x) == result)]
fn immref_struct_arg(f: &Foo) -> u32 {
    f.x
}

#[ensures(old(f.x) == *result)]
fn immref_struct_reborrow(f: &Foo) -> &u32 {
    let x = &f.x;
    let y = x;
    y
}

// TODO: Axel: this currently fails because the struct perm field initializer is very naive and does not init
// "nested" perm fields such as for immrefs.
// fn immref_struct_lifetime<'x>(b: Bar<'x>) -> &'x u32 {
//     b.x
// }

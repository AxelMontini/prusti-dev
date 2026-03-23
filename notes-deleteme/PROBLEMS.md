# Some problems

## Immref creation and usage, partial permissions.

`make_concrete_*` and `make_generic_*` need to acquire/release some access to the resource.
Otherwise, one could create an immref and immediately after a mutable ref and the program would still verify.

Currently, `make_generic_*` takes `write` access to the resource, which isn't correct in the immref case.
How to overwrite these methods in the immref case?
It seems that `make_generic_Int_i32` is always called when instantiating a mutref, and for the immref it
could take an extra parameter `p: Perm`, or it could halve the ref's `immutable_perm` field as a postcondition.
<!-- THIS DOES NOT WORK, WAY TOO HARD TO IMPLEMENT, MOST MIR WOULD NEED TO BE TRANSFORMED
:: Another way would be to instead keep `make_generic` the same (full access), but then only let `make_concrete` take
partial permissions to the `p_Param` predicate. But then, how to create multiple immrefs pointing to the same variable? -->

Files: casters.rs and similar handle the `make_(concrete|generic)_*`.

Solution (probably): add perm parameter to `make_generic_*` and `make_concrete_*`. For most types,
this will take perm 1/1, but not for immrefs. Code changes should be minimal and mostly limited to `casters.rs` and `use_casters.rs`.

Other problem. We want to keep track of the permission each immref holds to the value it refs to.
Easily done by introducing `field p_Ref_immutable_perm: Perm` on each immrer `Ref` (`p_Ref_immutable(...)` holds write access to said field).
When creating an immref, we do:
- unfold the predicate to get access to the field.
- set the perm field to `perm(p_Ref_to_Pred(_target))/2`.
- make `target` generic (throgh dereferencing the immref) with permission `p_Ref_immutable_perm`: this takes the same amount of access
  away from `p_Ref_to_Pred(_target)`, so effectively it reduces `perm(...)` too, and gives us some access to `p_Param(...)`, which allows one
  to actually use the immref.
- fold the predicate

To then use it:
- Get the current amount of perm `p` held using function `p_Ref_immutable_current_perm`, which unfolds pred and returns field value.
- Concretize the value with the returned perm (requires access `p` to Param predicate and ensures `acc(p_Ref_to_Pred(_target), p)`).

TODO: Like for mutrefs, ensure access to `p_Param()` to be able to re-obtain full permissions at the caller site.

TODO: How to pure?
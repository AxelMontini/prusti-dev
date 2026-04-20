use crate::encoders::{
    TyUsePureEnc,
    ty::{
        RustImmRef, RustTyDatas,
        data::TyData,
        impure::{PredicateBuilder, TyImpureEnc, TyImpureImmRef, TyImpureImmRefData},
        pure::{AdtBuilder, TyPureEnc, TyPureImmRef, TyPureImmRefData},
    },
};
use task_encoder::{EncodeFullError, TaskEncoderDependencies};
use vir::CastType;

pub(crate) fn ty_pure<'vir>(
    task_key: &TyData<'vir, RustTyDatas>,
    data: &RustImmRef<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, TyPureEnc>,
    builder: &mut AdtBuilder<'vir>,
) -> Result<TyPureImmRef<'vir>, EncodeFullError<'vir, TyPureEnc>> {
    // // force encoding of s_Param
    // deps.require_ref::<TyUsePureEnc>(data.decompose(task_key.params))?;

    let (field_snaps_to_snap, field_access) =
        builder.constructor("", (vir::TYPE_REF, vir::TYPE_PSNAP), None);

    Ok(TyPureImmRefData {
        prim_to_snap: field_snaps_to_snap,
        deref_access: field_access[0].downcast_ty(),
        value_access: field_access[1].downcast_ty(),
    })
}

pub(crate) fn ty_impure<'vir>(
    data: &(&RustImmRef<'vir>, &TyPureImmRef<'vir>),
    _deps: &mut TaskEncoderDependencies<'vir, TyImpureEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<TyImpureImmRef<'vir>, EncodeFullError<'vir, TyImpureEnc>> {
    let snap_type = builder.csnap_type();
    let ref_param = builder.vcx.mk_local_decl("r", vir::TYPE_REF);
    let ref_param_ex = builder.vcx.mk_local_ex(ref_param);
    // TODO: Is this really needed? Can be done with just an expression...
    let current_value = builder.inner.function(
        "current_value",
        vir::TYPE_REF,
        snap_type,
        (ref_param,),
        &[],
        &[vir::expr! {
            ([data.1.deref_access](result: [snap_type])) == ([ref_param_ex])
        }],
        None,
    );

    let ref_self_decl = builder.ref_self_decl();
    let ref_self = builder.vcx.mk_local_ex(ref_self_decl);
    let perm_field = builder.field("perm", vir::TYPE_PERM);

    // Permission predicate: access the permission field
    let params = (
        ref_self_decl,
        builder.vcx.alloc_slice(builder.params.ty_decls()),
        builder.vcx.alloc_slice(builder.params.const_decls()),
    );
    let pred = vir::expr! {
        acc([builder.ref_to_pred](ref_self, [..[builder.params.ty_exprs()]], [..[builder.params.const_exprs()]]))
    };
    // XXX: THERE IS NO WAY THERE ISN'T A mk_fraction OR SIMILAR ANYWHERE
    let zero_perm = builder.vcx.mk_no_perm();
    let write_perm = builder.vcx.mk_full_perm();
    let post = vir::expr! {
        ((zero_perm) < (result: Perm)) && ((result: Perm) < (write_perm))
    };
    let expr = vir::expr! {
        unfolding ([builder.ref_to_pred](ref_self, [..[builder.params.ty_exprs()]], [..[builder.params.const_exprs()]])) in ([perm_field](ref_self))
    };
    let csnap = builder.vcx.alloc_slice(&[snap_type]);
    let current_perm = builder.function(
        "current_perm",
        (vir::TYPE_REF, &[vir::TYPE_TYVAL][..], csnap),
        vir::TYPE_PERM,
        params,
        &[pred],
        &[post],
        Some(expr),
    );

    // fields
    let ref_field = builder.field("val", snap_type);

    // main predicate
    builder.mk_predicate(
        "",
        Some(vir::expr! {
            ( acc((ref_self).[ref_field]) ) && (
                ( acc((ref_self).[perm_field]) )
                && (
                    ( (zero_perm) < ([perm_field](ref_self)) ) && ( ([perm_field](ref_self)) < (write_perm) )
                )
            )
            // TODO: pure typeof assertions do not currently work
            // && (([generic_typeof]([data.1.value_access]([ref_field](ref_self)))) == ([builder.params.ty_exprs()[0]]))
        }), // TODO: use generic args?
    );

    let arbitrary_value = builder.inner.function(
        "arbitrary_value",
        vir::TYPE_REF,
        snap_type,
        (ref_param,),
        &[],
        &[vir::expr! {
            ([data.1.deref_access](result: [snap_type])) == ([ref_param_ex])
        }],
        None,
    );

    // Ref-to-snap
    builder.mk_snap_function(Some(vir::expr! { [ref_field](ref_self) }));

    Ok(TyImpureImmRefData {
        current_value,
        current_perm,
        arbitrary_value,
        pure: *data.1,
    })
}

use crate::encoders::{
    TyUseImpureEnc, TyUsePureEnc,
    ty::{
        RustImmRef, RustTyDatas,
        data::TyData,
        generics::{AliasUtils, AliasUtilsEnc, GParams},
        impure::{PredicateBuilder, TyImpureEnc, TyImpureImmRef, TyImpureImmRefData},
        pure::{AdtBuilder, PureTyDatas, TyPureEnc, TyPureImmRef, TyPureImmRefData},
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
    let ty = data.metadata.decompose(task_key.params);
    let metadata = deps.require_ref::<TyUsePureEnc>(ty)?.snapshot.downcast_ty();

    let ty = data.referent.decompose(task_key.params);
    let referent = deps.require_ref::<TyUsePureEnc>(ty)?.snapshot.downcast_ty();

    let (field_snaps_to_snap, field_access) =
        builder.constructor("", (vir::TYPE_REF, vir::TYPE_REF, metadata, referent), None);

    // TODO: Move back to immutable code only
    let shadow_for = {
        let blocked_decl = builder.vcx.mk_local_decl("blocked", vir::TYPE_REF);
        let perm_decl = builder.vcx.mk_local_decl("perm_seed", vir::TYPE_PERM);
        builder.function(
            "shadow_for",
            (blocked_decl.ty, perm_decl.ty),
            vir::TYPE_REF,
            (blocked_decl, perm_decl),
            &[],
            &[],
            None,
        )
    };

    Ok(TyPureImmRefData {
        prim_to_snap: field_snaps_to_snap,
        deref_access: field_access[0].downcast_ty(),
        blocked_access: field_access[1].downcast_ty(),
        metadata_access: field_access[2].downcast_ty(),
        value_access: field_access[3].downcast_ty(),
        shadow_for,
    })
}

pub(crate) fn ty_impure<'vir>(
    task_key: &TyData<'vir, (RustTyDatas, PureTyDatas)>,
    data: &(&RustImmRef<'vir>, &TyPureImmRef<'vir>),
    deps: &mut TaskEncoderDependencies<'vir, TyImpureEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<TyImpureImmRef<'vir>, EncodeFullError<'vir, TyImpureEnc>> {
    let pure = data.1.clone();
    let snap_type = builder.csnap_type();

    let metadata_type = data.0.metadata.decompose(task_key.0.params);
    deps.require_dep::<TyUseImpureEnc>(metadata_type)?;
    let inner_type = data.0.referent.decompose(task_key.0.params);
    deps.require_dep::<TyUseImpureEnc>(inner_type)?;

    let ref_self_decl = builder.ref_self_decl();
    let ref_self = builder.vcx.mk_local_ex(ref_self_decl);

    let AliasUtils { perm_field } = deps.require_dep::<AliasUtilsEnc>(())?;
    tracing::info!(referent=?data.0.referent, "Referent of immref");
    let d = data.0.referent.decompose(task_key.0.params);
    let generic = deps.require_ref::<TyImpureEnc>(d.ty)?;

    // Functions
    let arbitrary_value = {
        let blocked_param_decl = builder.vcx.mk_local_decl("blocked", vir::TYPE_REF);
        let blocked_param = builder.vcx.mk_local_ex(blocked_param_decl);
        let perm_param_decl = builder.vcx.mk_local_decl("perm_seed", vir::TYPE_PERM);
        let perm_param = builder.vcx.mk_local_ex(perm_param_decl);
        let metadata_decl = builder.vcx.mk_local_decl("metadata", vir::TYPE_PSNAP);
        let metadata = builder.vcx.mk_local_ex(metadata_decl);
        let shadow = pure.shadow_for.call()(blocked_param, perm_param);
        builder.inner.function(
            "arbitrary_value",
            (vir::TYPE_REF, vir::TYPE_PSNAP, vir::TYPE_PERM),
            snap_type,
            (blocked_param_decl, metadata_decl, perm_param_decl),
            &[],
            &[vir::expr! {
                (([data.1.blocked_access](result: [snap_type])) == ([blocked_param])) &&
                    ((([data.1.deref_access](result: [snap_type])) == ([shadow])) &&
                    (([data.1.metadata_access](result: [snap_type])) == ([metadata])))
            }],
            None,
        )
    };

    // fields
    let ref_field = builder.field("val", snap_type);
    // let ever_changing_shadow_field = builder.field("ever_changing_shadow", vir::TYPE_REF); //
    // This is added once per function

    // main predicate
    builder.mk_predicate(
        "",
        Some(vir::expr! {
            acc((ref_self).[ref_field])

            // TODO: pure typeof assertions do not currently work
            // && (([generic_typeof]([data.1.value_access]([ref_field](ref_self)))) == ([builder.params.ty_exprs()[0]]))
        }), // TODO: use generic args?
    );

    // Ref-to-snap
    builder.mk_snap_function(Some(vir::expr! { [ref_field](ref_self) }));

    // Methods
    let ref_target_decl = builder.vcx.mk_local_decl("target", vir::TYPE_REF);
    let ref_target = builder.vcx.mk_local_ex(ref_target_decl);
    let ref_source_decl = builder.vcx.mk_local_decl("source", vir::TYPE_REF);
    let ref_source = builder.vcx.mk_local_ex(ref_source_decl);
    // `source.perm_field`. Beware! `old(source.perm_field)` (using this) is not the same as
    // `old(souce).perm_field`!
    let source_perm_field = builder.vcx.mk_field_expr(ref_source, perm_field);
    let target_perm_field = builder.vcx.mk_field_expr(ref_target, perm_field);
    let acc_perm_field_source = builder.vcx.mk_acc_field_expr(ref_source, perm_field, None);
    let acc_perm_field_target = builder.vcx.mk_acc_field_expr(ref_target, perm_field, None);

    // param snap of shadow of ImmRef == param snap of old source (deref Immref)
    let same_snap = builder.vcx.mk_eq_expr(
        (generic.ref_to_snap)(
            ref_target,
            builder.params.ty_exprs(),
            builder.params.const_exprs(),
        ),
        builder.vcx.mk_old_expr((generic.ref_to_snap)(
            ref_source,
            builder.params.ty_exprs(),
            builder.params.const_exprs(),
        )),
    );
    // PRE bounds of perm field, none < perm <= write
    let perm_field_bounds = |field_expr, gt_expr, le_expr| {
        builder.vcx.mk_conj(&[
            builder
                .vcx
                .mk_bin_op_expr(vir::BinOpKind::CmpLt, gt_expr, field_expr)
                .downcast_ty(),
            builder
                .vcx
                .mk_bin_op_expr(vir::BinOpKind::CmpLe, field_expr, le_expr)
                .downcast_ty(),
        ])
    };
    let source_perm_field_bounds_none_write = perm_field_bounds(
        source_perm_field,
        builder.vcx.mk_no_perm(),
        builder.vcx.mk_full_perm(),
    );
    let source_perm_field_bounds_none_onehalf = perm_field_bounds(
        source_perm_field,
        builder.vcx.mk_no_perm(),
        builder.vcx.mk_perm::<1, 2>(),
    );
    let target_perm_field_bounds_none_onehalf = perm_field_bounds(
        target_perm_field,
        builder.vcx.mk_no_perm(),
        builder.vcx.mk_perm::<1, 2>(),
    );
    // 1/2 of source.perm_field
    let half_source_perm_field = builder
        .vcx
        .mk_bin_op_expr(
            vir::BinOpKind::PermPermDiv,
            source_perm_field,
            builder.vcx.mk_perm::<2, 1>(),
        )
        .downcast_ty();

    let half_source_param = builder.vcx.mk_predicate_app_expr((generic.ref_to_pred)(
        ref_source,
        builder.params.ty_exprs(),
        builder.params.const_exprs(),
    )(Some(half_source_perm_field)));

    let source_param = builder.vcx.mk_predicate_app_expr((generic.ref_to_pred)(
        ref_source,
        builder.params.ty_exprs(),
        builder.params.const_exprs(),
    )(Some(source_perm_field)));

    let source_param_with_old_target_field = builder.vcx.mk_predicate_app_expr((generic
        .ref_to_pred)(
        ref_source,
        builder.params.ty_exprs(),
        builder.params.const_exprs(),
    )(Some(
        builder.vcx.mk_old_expr(target_perm_field),
    )));

    let target_param = builder.vcx.mk_predicate_app_expr((generic.ref_to_pred)(
        ref_target,
        builder.params.ty_exprs(),
        builder.params.const_exprs(),
    )(Some(target_perm_field)));

    let post_perm_field_value = builder.vcx.mk_conj(&[
        builder.vcx.mk_eq_expr(
            builder.vcx.mk_old_expr(half_source_perm_field),
            source_perm_field,
        ),
        builder.vcx.mk_eq_expr(source_perm_field, target_perm_field),
    ]);

    // Wand to obtain back permission to original value.
    let tmp_perm_decl = builder.vcx.mk_local_decl("tmp", vir::TYPE_PERM);
    let tmp_perm = builder.vcx.mk_local_ex(tmp_perm_decl);
    let tmp_perm_value_half_source: vir::ExprPerm<'_> = builder
        .vcx
        .mk_bin_op_expr(
            vir::BinOpKind::PermPermDiv,
            builder.vcx.mk_old_expr(source_perm_field),
            builder.vcx.mk_perm::<2, 1>(),
        )
        .downcast_ty();
    let post_wand = builder.vcx.mk_wand(
        builder.vcx.mk_predicate_app_expr((generic.ref_to_pred)(
            ref_target,
            builder.params.ty_exprs(),
            builder.params.const_exprs(),
        )(Some(tmp_perm))),
        builder.vcx.mk_predicate_app_expr((generic.ref_to_pred)(
            ref_source,
            builder.params.ty_exprs(),
            builder.params.const_exprs(),
        )(Some(tmp_perm))),
    );
    let post_wand_with_old_field_value = builder.vcx.mk_let_expr(
        tmp_perm_decl,
        tmp_perm_value_half_source,
        builder.vcx.mk_wand_expr(post_wand),
    );
    let post_wand_with_target_field_value = builder.vcx.mk_let_expr(
        tmp_perm_decl,
        target_perm_field,
        builder.vcx.mk_wand_expr(post_wand),
    );

    // Binds &T `ref_target` to its shadow, which is snapshot-equal to `ref_source`
    let bind_block = builder.inner.method(
        "bind_block",
        (
            ref_target.ty(),
            ref_source.ty(),
            builder.params.ty_args(),
            builder.params.const_args(),
        ),
        &[],
        (
            ref_target_decl,
            ref_source_decl,
            builder.params.ty_decls(),
            builder.params.const_decls(),
        ),
        &[
            acc_perm_field_source,
            source_perm_field_bounds_none_write,
            half_source_param,
        ],
        &[
            acc_perm_field_source,
            acc_perm_field_target,
            post_perm_field_value,
            target_param,
            same_snap,
            post_wand_with_old_field_value,
        ],
    );

    let old_perm_field_sum = builder
        .vcx
        .mk_bin_op_expr(
            vir::BinOpKind::PermAdd,
            builder.vcx.mk_old_expr(source_perm_field),
            builder.vcx.mk_old_expr(target_perm_field),
        )
        .downcast_ty();
    let source_perm_field_equals_sum = builder
        .vcx
        .mk_eq_expr(source_perm_field, old_perm_field_sum);

    let unbind_unblock = builder.inner.method(
        "unbind_unblock",
        (
            ref_target.ty(),
            ref_source.ty(),
            builder.params.ty_args(),
            builder.params.const_args(),
        ),
        &[],
        (
            ref_target_decl,
            ref_source_decl,
            builder.params.ty_decls(),
            builder.params.const_decls(),
        ),
        &[
            acc_perm_field_source,
            acc_perm_field_target,
            source_perm_field_bounds_none_onehalf,
            target_perm_field_bounds_none_onehalf,
            target_param,
            post_wand_with_target_field_value,
        ],
        &[
            acc_perm_field_source,
            source_perm_field_equals_sum,
            source_param_with_old_target_field,
        ],
    );

    Ok(TyImpureImmRefData {
        pure,
        bind_block,
        unbind_unblock,
        arbitrary_value,
    })
}

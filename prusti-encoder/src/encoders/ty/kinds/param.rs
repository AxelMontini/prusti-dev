use crate::encoders::ty::{
    RustParam,
    impure::{PredicateBuilder, TyImpureEnc, TyImpureParam, TyImpureParamData},
    pure::{DomainBuilder, TyPureEnc, TyPureParam},
};
use task_encoder::{EncodeFullError, TaskEncoderDependencies};
use vir::CastType;

pub(crate) fn ty_pure<'vir>(
    _data: &RustParam<'vir>,
    _deps: &mut TaskEncoderDependencies<'vir, TyPureEnc>,
    _builder: &mut DomainBuilder<'vir>,
) -> Result<TyPureParam<'vir>, EncodeFullError<'vir, TyPureEnc>> {
    Ok(())
}

pub(crate) fn ty_impure<'vir>(
    data: &(&RustParam<'vir>, &TyPureParam<'vir>),
    deps: &mut TaskEncoderDependencies<'vir, TyImpureEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<TyImpureParam<'vir>, EncodeFullError<'vir, TyImpureEnc>> {
    super::opaque::set_opaque(builder);

    // Fields
    let perm_field = builder.field("perm_owned", vir::TYPE_PERM);

    // Methods
    let ref_source_decl: vir::LocalDeclRef<'vir> =
        builder.vcx.mk_local_decl("source", vir::TYPE_REF);
    let ref_source: &vir::ExprGenData<'_, (), !, vir::Ref> =
        builder.vcx.mk_local_ex(ref_source_decl);
    let ref_target_decl = builder.vcx.mk_local_decl("target", vir::TYPE_REF);
    let ref_target: &vir::ExprGenData<'_, (), !, vir::Ref> =
        builder.vcx.mk_local_ex(ref_target_decl);

    // snap of target is the same as snap of old source
    let same_snap = builder.vcx.mk_eq_expr(
        (builder.ref_to_snap)(
            ref_target,
            builder.params.ty_exprs(),
            builder.params.const_exprs(),
        ),
        builder.vcx.mk_old_expr((builder.ref_to_snap)(
            ref_source,
            builder.params.ty_exprs(),
            builder.params.const_exprs(),
        )),
    );
    let source_perm_field = builder.vcx.mk_field_expr(ref_source, perm_field);
    let target_perm_field = builder.vcx.mk_field_expr(ref_target, perm_field);
    let acc_perm_field_source = builder.vcx.mk_acc_field_expr(ref_source, perm_field, None);
    let acc_perm_field_target = builder.vcx.mk_acc_field_expr(ref_target, perm_field, None);

    let perm_field_bounds = builder.vcx.mk_conj(&[
        builder
            .vcx
            .mk_bin_op_expr(
                vir::BinOpKind::CmpLt,
                builder.vcx.mk_no_perm(),
                source_perm_field,
            )
            .downcast_ty(),
        builder
            .vcx
            .mk_bin_op_expr(
                vir::BinOpKind::CmpLe,
                source_perm_field,
                builder.vcx.mk_full_perm(),
            )
            .downcast_ty(),
    ]);

    let half_source_perm = builder
        .vcx
        .mk_bin_op_expr(
            vir::BinOpKind::DivRational,
            source_perm_field,
            builder
                .vcx
                .mk_const_expr(vir::ConstData::Int(2))
                .downcast_ty(),
        )
        .downcast_ty();

    let half_source_param = builder.vcx.mk_predicate_app_expr((builder.ref_to_pred)(
        ref_source,
        builder.params.ty_exprs(),
        builder.params.const_exprs(),
    )(Some(half_source_perm)));

    let target_param = builder.vcx.mk_predicate_app_expr((builder.ref_to_pred)(
        ref_target,
        builder.params.ty_exprs(),
        builder.params.const_exprs(),
    )(Some(
        builder.vcx.mk_field_expr(ref_target, perm_field),
    )));

    let post_perm_field_value = builder.vcx.mk_conj(&[
        builder
            .vcx
            .mk_eq_expr(builder.vcx.mk_old_expr(half_source_perm), source_perm_field),
        builder.vcx.mk_eq_expr(source_perm_field, target_perm_field),
    ]);

    let share = builder.inner.method(
        "share",
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
        &[acc_perm_field_source, perm_field_bounds, half_source_param],
        &[
            acc_perm_field_source,
            acc_perm_field_target,
            post_perm_field_value,
            target_param,
            same_snap,
        ],
    );

    Ok(TyImpureParamData { perm_field, share })
}

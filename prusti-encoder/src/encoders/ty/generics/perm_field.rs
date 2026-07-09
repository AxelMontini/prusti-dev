use std::convert::Infallible;

use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::CastType;

pub struct AliasUtilsEnc;

/// Fractional access utilities.
#[derive(Debug, Clone, Copy)]
pub struct AliasUtils<'vir> {
    pub perm_field: vir::FieldPerm<'vir>,
    //     /// Args: `(target, source, ...generics)`
    //     ///
    //     /// Halves `source.perm_field`, takes away that amount of access from `p_Param(source, ...)` and
    //     /// gives the same amount to `p_Param(target, ...)`. Also ensures snapshot equality between
    //     /// `target` and `source`. `target`'s perm field must not exist yet.
    //     pub bind_block: vir::MethodIdn<'vir, (vir::Ref, vir::Ref, vir::ManyTyVal, vir::ManyCSnap)>,
    //     /// Args: `(target, source, ...generics)`
    //     ///
    //     /// Reverses `bind_block`. It requires the same wand ensured when binding,
    //     /// and transfers permissions back to source. It also adds the permission field of `target` to `source`,
    //     /// and exhales all access to the target perm field.
    //     pub unbind_unblock: vir::MethodIdn<'vir, (vir::Ref, vir::Ref, vir::ManyTyVal, vir::ManyCSnap)>,
}

impl<'vir> task_encoder::OutputRefAny for AliasUtils<'vir> {}

impl<'vir> AliasUtils<'vir> {
    /// Generate `acc(self_ref.perm_field, p)`. Default `p` is `write`.
    pub fn acc_perm_field(
        &self,
        self_ref: vir::ExprRef<'vir>,
        p: Option<vir::ExprPerm<'vir>>,
    ) -> vir::ExprBool<'vir> {
        vir::with_vcx(|vcx| vcx.mk_acc_field_expr(self_ref, self.perm_field, p))
    }

    /// Expr: the permission field of the current value.
    /// Note that, for a Reference, this *isn't* the permission field of the aliased value,
    /// but of the reference itself. In other words, this returns `y.perm_field`, not `(*y).perm_field`.
    /// For all owned values that are not borrowed, the permission field must have value `write`.
    pub fn perm_field(&self, self_ref: vir::ExprRef<'vir>) -> vir::ExprPerm<'vir> {
        vir::with_vcx(|vcx| vcx.mk_field_expr(self_ref, self.perm_field))
    }
}

#[derive(Clone, Debug)]
pub struct AliasUtilsLocal<'vir> {
    // methods: Vec<vir::Method<'vir>>,
    perm_field: vir::FieldPerm<'vir>,
}

impl TaskEncoder for AliasUtilsEnc {
    task_encoder::encoder_cache!(AliasUtilsEnc);
    const ENCODER_NAME: &'static str = "aliasing utilities encoder";
    /// This should always be p_Param.
    /// You can encode_normalize your type to obtain it.
    /// As such, this encoder only runs once, as all p_Param are the same.
    type TaskDescription<'vir> = ();

    // TODO: Axel: Makes sense to be ref? This can probably be omitted
    type OutputRef<'vir> = AliasUtils<'vir>;
    type OutputFullDependency<'vir> = AliasUtils<'vir>;
    type OutputFullLocal<'vir> = AliasUtilsLocal<'vir>;

    type EncodingError = Infallible;

    fn task_to_key<'vir>(_task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {}

    #[tracing::instrument(skip(deps), ret, err(Debug))]
    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        // let ty = task_key;
        // let generic = deps.require_ref::<TyImpureEnc>(ty)?;
        // let params = deps.require_dep::<GenericParamsEnc>(ty.params)?;

        vir::with_vcx(|vcx| {
            let perm_field = vcx.mk_field("perm_field", vir::TYPE_PERM);

            // // Methods
            // let ref_target_decl = vcx.mk_local_decl("target", vir::TYPE_REF);
            // let ref_target = vcx.mk_local_ex(ref_target_decl);
            // let ref_source_decl = vcx.mk_local_decl("source", vir::TYPE_REF);
            // let ref_source = vcx.mk_local_ex(ref_source_decl);
            // // `source.perm_field`. Beware! `old(source.perm_field)` (using this) is not the same as
            // // `old(souce).perm_field`!
            // let source_perm_field = vcx.mk_field_expr(ref_source, perm_field);
            // let target_perm_field = vcx.mk_field_expr(ref_target, perm_field);
            // let acc_perm_field_source = vcx.mk_acc_field_expr(ref_source, perm_field, None);
            // let acc_perm_field_target = vcx.mk_acc_field_expr(ref_target, perm_field, None);
            //
            // // param snap of shadow of ImmRef == param snap of old source (deref Immref)
            // let same_snap = vcx.mk_eq_expr(
            //     (generic.ref_to_snap)(ref_target, params.ty_exprs(), params.const_exprs()),
            //     vcx.mk_old_expr((generic.ref_to_snap)(
            //         ref_source,
            //         params.ty_exprs(),
            //         params.const_exprs(),
            //     )),
            // );
            // // PRE bounds of perm field, none < perm <= write
            // let perm_field_bounds = |field_expr, gt_expr, le_expr| {
            //     vcx.mk_conj(&[
            //         vcx.mk_bin_op_expr(vir::BinOpKind::CmpLt, gt_expr, field_expr)
            //             .downcast_ty(),
            //         vcx.mk_bin_op_expr(vir::BinOpKind::CmpLe, field_expr, le_expr)
            //             .downcast_ty(),
            //     ])
            // };
            // let source_perm_field_bounds_none_write =
            //     perm_field_bounds(source_perm_field, vcx.mk_no_perm(), vcx.mk_full_perm());
            // let source_perm_field_bounds_none_onehalf =
            //     perm_field_bounds(source_perm_field, vcx.mk_no_perm(), vcx.mk_perm::<1, 2>());
            // let target_perm_field_bounds_none_onehalf =
            //     perm_field_bounds(target_perm_field, vcx.mk_no_perm(), vcx.mk_perm::<1, 2>());
            // // 1/2 of source.perm_field
            // let half_source_perm_field = vcx
            //     .mk_bin_op_expr(
            //         vir::BinOpKind::DivRational,
            //         source_perm_field,
            //         vcx.mk_const_expr(vir::ConstData::Int(2)).downcast_ty(),
            //     )
            //     .downcast_ty();
            //
            // let half_source_param =
            //     vcx.mk_predicate_app_expr((generic.ref_to_pred)(
            //         ref_source,
            //         params.ty_exprs(),
            //         params.const_exprs(),
            //     )(Some(half_source_perm_field)));
            //
            // let source_param = vcx.mk_predicate_app_expr((generic.ref_to_pred)(
            //     ref_source,
            //     params.ty_exprs(),
            //     params.const_exprs(),
            // )(Some(source_perm_field)));
            //
            // let source_param_with_old_target_field = vcx.mk_predicate_app_expr((generic
            //     .ref_to_pred)(
            //     ref_source,
            //     params.ty_exprs(),
            //     params.const_exprs(),
            // )(Some(
            //     vcx.mk_old_expr(target_perm_field),
            // )));
            //
            // let target_param = vcx.mk_predicate_app_expr((generic.ref_to_pred)(
            //     ref_target,
            //     params.ty_exprs(),
            //     params.const_exprs(),
            // )(Some(target_perm_field)));
            //
            // let post_perm_field_value = vcx.mk_conj(&[
            //     vcx.mk_eq_expr(vcx.mk_old_expr(half_source_perm_field), source_perm_field),
            //     vcx.mk_eq_expr(source_perm_field, target_perm_field),
            // ]);
            //
            // // Wand to obtain back permission to original value.
            // let tmp_perm_decl = vcx.mk_local_decl("tmp", vir::TYPE_PERM);
            // let tmp_perm = vcx.mk_local_ex(tmp_perm_decl);
            // let tmp_perm_value_half_source: vir::ExprPerm<'_> = vcx
            //     .mk_bin_op_expr(
            //         vir::BinOpKind::DivRational,
            //         vcx.mk_old_expr(source_perm_field),
            //         vcx.mk_const_expr(vir::ConstData::Int(2)).downcast_ty(),
            //     )
            //     .downcast_ty();
            // let post_wand = vcx.mk_wand(
            //     vcx.mk_predicate_app_expr((generic.ref_to_pred)(
            //         ref_target,
            //         params.ty_exprs(),
            //         params.const_exprs(),
            //     )(Some(tmp_perm))),
            //     vcx.mk_predicate_app_expr((generic.ref_to_pred)(
            //         ref_source,
            //         params.ty_exprs(),
            //         params.const_exprs(),
            //     )(Some(tmp_perm))),
            // );
            // let post_wand_with_old_field_value = vcx.mk_let_expr(
            //     tmp_perm_decl,
            //     tmp_perm_value_half_source,
            //     vcx.mk_wand_expr(post_wand),
            // );
            // let post_wand_with_target_field_value = vcx.mk_let_expr(
            //     tmp_perm_decl,
            //     target_perm_field,
            //     vcx.mk_wand_expr(post_wand),
            // );
            //
            // // Binds &T `ref_target` to its shadow, which is snapshot-equal to `ref_source`
            // let bind_block_idn = MethodIdn::new(
            //     ViperIdent::new("bind_block"),
            //     (
            //         ref_target.ty(),
            //         ref_source.ty(),
            //         params.ty_args(),
            //         params.const_args(),
            //     ),
            // );
            // let bind_block = vcx.mk_method(
            //     bind_block_idn,
            //     (
            //         ref_target_decl,
            //         ref_source_decl,
            //         params.ty_decls(),
            //         params.const_decls(),
            //     ),
            //     &[],
            //     vcx.alloc_slice(&[
            //         acc_perm_field_source,
            //         source_perm_field_bounds_none_write,
            //         half_source_param,
            //     ]),
            //     vcx.alloc_slice(&[
            //         acc_perm_field_source,
            //         acc_perm_field_target,
            //         post_perm_field_value,
            //         target_param,
            //         same_snap,
            //         post_wand_with_old_field_value,
            //     ]),
            //     None, // TODO: Axel: Body for proof of correctness?
            // );
            //
            // let old_perm_field_sum = vcx
            //     .mk_bin_op_expr(
            //         vir::BinOpKind::Add,
            //         vcx.mk_old_expr(source_perm_field),
            //         vcx.mk_old_expr(target_perm_field),
            //     )
            //     .downcast_ty();
            // let source_perm_field_equals_sum =
            //     vcx.mk_eq_expr(source_perm_field, old_perm_field_sum);
            //
            // let unbind_unblock_idn = MethodIdn::new(
            //     ViperIdent::new("unbind_unblock"),
            //     (
            //         ref_target.ty(),
            //         ref_source.ty(),
            //         params.ty_args(),
            //         params.const_args(),
            //     ),
            // );
            // let unbind_unblock = vcx.mk_method(
            //     unbind_unblock_idn,
            //     (
            //         ref_target_decl,
            //         ref_source_decl,
            //         params.ty_decls(),
            //         params.const_decls(),
            //     ),
            //     &[],
            //     vcx.alloc_slice(&[
            //         acc_perm_field_source,
            //         acc_perm_field_target,
            //         source_perm_field_bounds_none_onehalf,
            //         target_perm_field_bounds_none_onehalf,
            //         target_param,
            //         post_wand_with_target_field_value,
            //     ]),
            //     vcx.alloc_slice(&[
            //         acc_perm_field_source,
            //         source_perm_field_equals_sum,
            //         source_param_with_old_target_field,
            //     ]),
            //     None,
            // );

            let local = AliasUtilsLocal {
                // methods: vec![bind_block, unbind_unblock],
                perm_field,
            };
            let full = AliasUtils {
                perm_field,
                // unbind_unblock: unbind_unblock_idn,
                // bind_block: bind_block_idn,
            };

            deps.emit_output_ref(*task_key, full)?;
            Ok((local, full))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in Self::all_outputs_local_no_errors(program) {
            program.add_field(output.perm_field.upcast_ty());
            // for method in output.methods {
            //     program.add_method(method);
            // }
        }
    }
}

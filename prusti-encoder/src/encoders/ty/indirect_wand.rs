use pcg::borrow_pcg::region_projection::{
    ExtractRegionsCtxt as _, LifetimeProjection, PcgRegion, Region,
};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, Reify};

use crate::encoders::{
    TyUseImpureEnc,
    ty::{
        RustTyDecomposition,
        indirect::{IndirectPredicatesEnc, PrustiPcgCtxt},
    },
};

use super::{
    data::{StructData, TySpecifics},
    rust_ty::RustTyDatas,
    use_pure::{TyUsePureEnc, UsePureTyDatas},
};

pub struct IndirectPredicatesWandLhsEnc;

type LhsExprInput<'vir> = (vir::ExprSnap<'vir>, vir::ExprPerm<'vir>);
type LhsExprOutput<'vir> = vir::ExprGenBool<'vir, LhsExprInput<'vir>, vir::ExprKind<'vir>>;

#[derive(Clone)]
pub struct IndirectPredicatesWandLhsEncOutputRef<'vir> {
    pub predicate_applications: Vec<LhsExprOutput<'vir>>,
}

impl<'vir> IndirectPredicatesWandLhsEncOutputRef<'vir> {
    pub fn new(predicate_applications: Vec<LhsExprOutput<'vir>>) -> Self {
        Self {
            predicate_applications,
        }
    }
}

fn projection_region<'tcx>(
    proj: &LifetimeProjection<'tcx, RustTyDecomposition<'tcx>, Region>,
) -> PcgRegion<'tcx> {
    let regions = PrustiPcgCtxt.extract_regions(proj.base());
    regions[proj.region_idx()]
}

impl<'vir> task_encoder::OutputRefAny for IndirectPredicatesWandLhsEncOutputRef<'vir> {}

impl TaskEncoder for IndirectPredicatesWandLhsEnc {
    task_encoder::encoder_cache!(IndirectPredicatesWandLhsEnc);
    const ENCODER_NAME: &'static str = "indirect predicates encoder";

    type TaskDescription<'vir> = LifetimeProjection<'vir, RustTyDecomposition<'vir>>;

    type TaskKey<'tcx> = Self::TaskDescription<'tcx>;

    type EncodingError = ();

    type OutputFullDependency<'vir> = IndirectPredicatesWandLhsEncOutputRef<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    #[tracing::instrument(skip(deps))]
    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        vir::with_vcx(|vcx| {
            let task_region = projection_region(task_key);
            let ty = task_key.base();
            let self_ty_enc = deps.require_dep::<TyUsePureEnc>(ty)?;
            let combined = ty.ty.zip(self_ty_enc);
            let mut predicate_applications = vec![];
            // Collects (accessor, indirect_predicate) pairs for the fields of a
            // struct-like (used for structs and enum variants).
            let collect_field_predicates = |struct_data: StructData<
                'vir,
                (RustTyDatas, UsePureTyDatas),
            >,
                                            deps: &mut TaskEncoderDependencies<
                'vir,
                IndirectPredicatesWandLhsEnc,
            >| {
                let mut result = vec![];
                for (field_ty, accessor) in struct_data.fields {
                    let field_ty = field_ty.decompose_context(ty.ty.params, ty.args);
                    if let Some(new_projection) =
                        LifetimeProjection::new(field_ty, task_region, None, PrustiPcgCtxt)
                    {
                        let field_indirect =
                            deps.require_dep::<IndirectPredicatesWandLhsEnc>(new_projection)?;
                        for inner_expr in field_indirect.predicate_applications {
                            result.push((accessor, inner_expr));
                        }
                    }
                }
                Ok(result)
            };

            let indirect_predicates = deps
                .require_dep::<IndirectPredicatesEnc>(*task_key)
                .unwrap()
                .predicate_applications;

            // no point in encoding wand if node has no resources associated
            if !indirect_predicates.is_empty() {
                // transform lazy `ref -> expr` to `(ref, _perm) -> expr`
                // and append to preds
                predicate_applications.extend(indirect_predicates.into_iter().map(|p| {
                    vcx.mk_lazy_expr(
                        "testtest",
                        vir::TYPE_BOOL,
                        Box::new(move |vcx, (self_expr, _perm)| p.reify(vcx, self_expr).kind),
                    )
                }));

                match combined.specifics {
                    // Optimisation: if there are no type arguments, there cannot be
                    // anything behind a ref inside (except for 'static, which we
                    // ignore for now). Plus it skips unsupported types if they
                    // don't have lifetimes.
                    _ if ty.args.args().is_empty() => (),
                    // TODO: it's not valid to have nothing for these. We should fix
                    // this by using an opaque predicate to represent potential
                    // indirect stuff. For example:
                    // fn foo<'a, T: Trait<'a>>(x: T) -> &'a mut i32 { x.get() }
                    // Here, `T` could be instantiated as `&'a mut i32` in which
                    // case we would want a wand with `i32(result) --* opaque_behind_a(x)`.
                    // This is why we should return `opaque_behind_a(x)` here.
                    TySpecifics::Param(_) | TySpecifics::Opaque(_) | TySpecifics::ArrayLike(_) => {
                        ()
                    }
                    TySpecifics::ImmRef((data, ref_domain)) => {
                        // TODO: De-duplicate immref and mutref code? Almost the same except perms
                        // TODO: USE PROPER PERMISSIONS!!! Not write
                        assert_eq!(ty.args.args().len(), 2);
                        let immref_impure = deps.require_dep::<TyUseImpureEnc>(ty)?.expect_immref();
                        let inner_ty = data.decompose_context(ty.ty.params, ty.args);
                        let inner_impure = deps.require_dep::<TyUseImpureEnc>(inner_ty)?;
                        let ref_region = PcgRegion::from(ty.args.args()[0].expect_region());
                        tracing::debug!(
                            ?task_key,
                            ?task_region,
                            ?ref_region,
                            "Task and ref region what?"
                        );
                        if ref_region == task_region {
                            // LHS
                            predicate_applications.push(vcx.mk_lazy_expr(
                                "perm_field_eq_post",
                                vir::TYPE_BOOL,
                                Box::new(
                                    move |vcx,
                                          (self_expr, perm): (
                                        vir::ExprSnap<'vir>,
                                        vir::ExprPerm<'vir>,
                                    )| {
                                        let addr = ref_domain.deref_access(self_expr.downcast_ty());
                                        let expr =
                                            vcx.mk_eq_expr(immref_impure.perm_field(addr), perm);
                                        expr.kind
                                    },
                                ),
                            ));
                        }
                        // if let Some(new_projection) =
                        //     LifetimeProjection::new(inner_ty, task_key.region(()), None, ())
                        // {
                        //     let inner_indirect =
                        //         deps.require_dep::<IndirectPredicatesWandLhsEnc>(new_projection)?;
                        //     predicate_applications.extend(
                        //         inner_indirect
                        //             .predicate_applications
                        //             .into_iter()
                        //             .map(|inner_expr| {
                        //                 vcx.mk_lazy_expr(
                        //                     "ref_inner_indirect",
                        //                     vir::TYPE_BOOL,
                        //                     Box::new(move |vcx, self_expr: vir::ExprGenSnap<_, _>| {
                        //                         let expr = inner_expr
                        //                             .reify(
                        //                                 vcx,
                        //                                 inner_impure.ref_to_snap(
                        //                                     ref_domain
                        //                                         .deref_access(self_expr.downcast_ty()),
                        //                                 ),
                        //                             )
                        //                             .kind;
                        //                         tracing::debug!(
                        //                             ?expr,
                        //                             "Instantiated ref_inner_indirect lazy expr"
                        //                         );
                        //                         expr
                        //                     }),
                        //                 )
                        //             }),
                        //     );
                        // }
                    }
                    TySpecifics::StructLike(data) => {
                        // TODO: invalid recursion here if the defined struct is
                        // recursive!
                        for (accessor, inner_expr) in collect_field_predicates(data, deps)? {
                            predicate_applications.push(vcx.mk_lazy_expr(
                                "struct_field_indirect",
                                vir::TYPE_BOOL,
                                Box::new(
                                    move |vcx,
                                          (self_expr, perm): (
                                        vir::ExprSnap<'vir>,
                                        vir::ExprPerm<'vir>,
                                    )| {
                                        inner_expr
                                            .reify(
                                                vcx,
                                                (accessor.read(self_expr.downcast_ty()), perm),
                                            )
                                            .kind
                                    },
                                ),
                            ));
                        }
                    }
                    TySpecifics::EnumLike(data) => {
                        let snap_to_discr_snap = data.data.1.snap_to_discr_snap;

                        let variant_preds = data
                            .variants
                            .into_iter()
                            .map(|variant| {
                                let fields = collect_field_predicates(variant.inner, deps)?;
                                Ok((variant.data.1.discr, fields))
                            })
                            .collect::<Result<Vec<_>, _>>()?;

                        if variant_preds.is_empty() {
                            return Ok(((), IndirectPredicatesWandLhsEncOutputRef::new(vec![])));
                        }

                        predicate_applications.push(vcx.mk_lazy_expr(
                            "enum_variant_indirect",
                            vir::TYPE_BOOL,
                            Box::new(
                                move |vcx,
                                      (self_expr, perm): (
                                    vir::ExprSnap<'vir>,
                                    vir::ExprPerm<'vir>,
                                )| {
                                    let self_csnap = self_expr.downcast_ty();
                                    let self_discr = snap_to_discr_snap.call()(self_csnap);
                                    let variant_conjs: Vec<_> = variant_preds
                                        .iter()
                                        .map(|(discr, fields)| {
                                            let preds: Vec<_> = fields
                                                .iter()
                                                .map(|(acc, expr)| {
                                                    expr.reify(vcx, (acc.read(self_csnap), perm))
                                                })
                                                .collect();
                                            (discr, vcx.mk_conj(&preds))
                                        })
                                        .collect();
                                    let (first, rest) = variant_conjs.split_first().unwrap();
                                    rest.iter()
                                        .fold(first.1, |else_, (discr, conj)| {
                                            vcx.mk_ternary_expr(
                                                vir::expr! { ([self_discr]) == ([*discr]) },
                                                *conj,
                                                else_,
                                            )
                                        })
                                        .kind
                                },
                            ),
                        ));
                    }
                    _ => (),
                };
            }
            Ok((
                (),
                IndirectPredicatesWandLhsEncOutputRef::new(predicate_applications),
            ))
        })
    }
}

pub struct IndirectPredicatesWandRhsEnc;

type RhsExprInput<'vir> = (vir::ExprSnap<'vir>, vir::ExprPerm<'vir>);
type RhsExprOutput<'vir> = vir::ExprGenBool<'vir, RhsExprInput<'vir>, vir::ExprKind<'vir>>;

#[derive(Clone)]
pub struct IndirectPredicatesWandRhsEncOutputRef<'vir> {
    pub predicate_applications: Vec<RhsExprOutput<'vir>>,
}

impl<'vir> IndirectPredicatesWandRhsEncOutputRef<'vir> {
    pub fn new(predicate_applications: Vec<RhsExprOutput<'vir>>) -> Self {
        Self {
            predicate_applications,
        }
    }
}

impl<'vir> task_encoder::OutputRefAny for IndirectPredicatesWandRhsEncOutputRef<'vir> {}

impl TaskEncoder for IndirectPredicatesWandRhsEnc {
    task_encoder::encoder_cache!(IndirectPredicatesWandRhsEnc);
    const ENCODER_NAME: &'static str = "indirect predicates encoder";

    type TaskDescription<'vir> = LifetimeProjection<'vir, RustTyDecomposition<'vir>>;

    type TaskKey<'tcx> = Self::TaskDescription<'tcx>;

    type EncodingError = ();

    type OutputFullDependency<'vir> = IndirectPredicatesWandRhsEncOutputRef<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    #[tracing::instrument(skip(deps))]
    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        vir::with_vcx(|vcx| {
            let ty = task_key.base();
            let task_region = projection_region(task_key);
            let self_ty_enc = deps.require_dep::<TyUsePureEnc>(ty)?;
            let combined = ty.ty.zip(self_ty_enc);
            let mut predicate_applications = vec![];
            // Collects (accessor, indirect_predicate) pairs for the fields of a
            // struct-like (used for structs and enum variants).
            let collect_field_predicates = |struct_data: StructData<
                'vir,
                (RustTyDatas, UsePureTyDatas),
            >,
                                            deps: &mut TaskEncoderDependencies<
                'vir,
                IndirectPredicatesWandRhsEnc,
            >| {
                let mut result = vec![];
                for (field_ty, accessor) in struct_data.fields {
                    let field_ty = field_ty.decompose_context(ty.ty.params, ty.args);
                    if let Some(new_projection) =
                        LifetimeProjection::new(field_ty, task_region, None, PrustiPcgCtxt)
                    {
                        let field_indirect =
                            deps.require_dep::<IndirectPredicatesWandRhsEnc>(new_projection)?;
                        for inner_expr in field_indirect.predicate_applications {
                            result.push((accessor, inner_expr));
                        }
                    }
                }
                Ok(result)
            };
            let indirect_predicates = deps
                .require_dep::<IndirectPredicatesEnc>(*task_key)
                .unwrap()
                .predicate_applications;

            // no point in encoding wand if node has no resources associated
            if !indirect_predicates.is_empty() {
                // transform lazy `ref -> expr` to `(ref, _perm) -> expr`
                // and append to preds
                predicate_applications.extend(indirect_predicates.into_iter().map(|p| {
                    vcx.mk_lazy_expr(
                        "testtest",
                        vir::TYPE_BOOL,
                        Box::new(move |vcx, (self_expr, _perm)| p.reify(vcx, self_expr).kind),
                    )
                }));
                match combined.specifics {
                    // Optimisation: if there are no type arguments, there cannot be
                    // anything behind a ref inside (except for 'static, which we
                    // ignore for now). Plus it skips unsupported types if they
                    // don't have lifetimes.
                    _ if ty.args.args().is_empty() => (),
                    // TODO: it's not valid to have nothing for these. We should fix
                    // this by using an opaque predicate to represent potential
                    // indirect stuff. For example:
                    // fn foo<'a, T: Trait<'a>>(x: T) -> &'a mut i32 { x.get() }
                    // Here, `T` could be instantiated as `&'a mut i32` in which
                    // case we would want a wand with `i32(result) --* opaque_behind_a(x)`.
                    // This is why we should return `opaque_behind_a(x)` here.
                    TySpecifics::Param(_) | TySpecifics::Opaque(_) | TySpecifics::ArrayLike(_) => {
                        ()
                    }
                    TySpecifics::ImmRef((data, ref_domain)) => {
                        // TODO: De-duplicate immref and mutref code? Almost the same except perms
                        // TODO: USE PROPER PERMISSIONS!!! Not write
                        assert_eq!(ty.args.args().len(), 2);
                        let immref_impure = deps.require_dep::<TyUseImpureEnc>(ty)?.expect_immref();
                        let inner_ty = data.decompose_context(ty.ty.params, ty.args);
                        let inner_impure = deps.require_dep::<TyUseImpureEnc>(inner_ty)?;
                        let ref_region = PcgRegion::from(ty.args.args()[0].expect_region());
                        tracing::debug!(
                            ?task_key,
                            ?task_region,
                            ?ref_region,
                            "Task and ref region what?"
                        );
                        if ref_region == task_region {
                            // RHS
                            predicate_applications.push(vcx.mk_lazy_expr(
                                "perm_field_eq_perm",
                                vir::TYPE_BOOL,
                                Box::new(
                                    move |vcx,
                                          (self_expr, perm): (
                                        vir::ExprSnap<'vir>,
                                        vir::ExprPerm<'vir>,
                                    )| {
                                        let addr = ref_domain.deref_access(self_expr.downcast_ty());
                                        let perm_field = immref_impure.perm_field(addr);
                                        let expr = vcx.mk_eq_expr(perm, perm_field);
                                        expr.kind
                                    },
                                ),
                            ));
                        }
                        // if let Some(new_projection) =
                        //     LifetimeProjection::new(inner_ty, task_key.region(()), None, ())
                        // {
                        //     let inner_indirect =
                        //         deps.require_dep::<IndirectPredicatesWandRhsEnc>(new_projection)?;
                        //     predicate_applications.extend(
                        //         inner_indirect
                        //             .predicate_applications
                        //             .into_iter()
                        //             .map(|inner_expr| {
                        //                 vcx.mk_lazy_expr(
                        //                     "ref_inner_indirect",
                        //                     vir::TYPE_BOOL,
                        //                     Box::new(move |vcx, self_expr: vir::ExprGenSnap<_, _>| {
                        //                         let expr = inner_expr
                        //                             .reify(
                        //                                 vcx,
                        //                                 inner_impure.ref_to_snap(
                        //                                     ref_domain
                        //                                         .deref_access(self_expr.downcast_ty()),
                        //                                 ),
                        //                             )
                        //                             .kind;
                        //                         tracing::debug!(
                        //                             ?expr,
                        //                             "Instantiated ref_inner_indirect lazy expr"
                        //                         );
                        //                         expr
                        //                     }),
                        //                 )
                        //             }),
                        //     );
                        // }
                    }
                    TySpecifics::StructLike(data) => {
                        // TODO: invalid recursion here if the defined struct is
                        // recursive!
                        for (accessor, inner_expr) in collect_field_predicates(data, deps)? {
                            predicate_applications.push(vcx.mk_lazy_expr(
                                "struct_field_indirect",
                                vir::TYPE_BOOL,
                                Box::new(
                                    move |vcx,
                                          (self_expr, perm): (
                                        vir::ExprSnap<'vir>,
                                        vir::ExprPerm<'vir>,
                                    )| {
                                        inner_expr
                                            .reify(
                                                vcx,
                                                (accessor.read(self_expr.downcast_ty()), perm),
                                            )
                                            .kind
                                    },
                                ),
                            ));
                        }
                    }
                    TySpecifics::EnumLike(data) => {
                        let snap_to_discr_snap = data.data.1.snap_to_discr_snap;

                        let variant_preds = data
                            .variants
                            .into_iter()
                            .map(|variant| {
                                let fields = collect_field_predicates(variant.inner, deps)?;
                                Ok((variant.data.1.discr, fields))
                            })
                            .collect::<Result<Vec<_>, _>>()?;

                        if variant_preds.is_empty() {
                            return Ok(((), IndirectPredicatesWandRhsEncOutputRef::new(vec![])));
                        }

                        predicate_applications.push(vcx.mk_lazy_expr(
                            "enum_variant_indirect",
                            vir::TYPE_BOOL,
                            Box::new(
                                move |vcx,
                                      (self_expr, perm): (
                                    vir::ExprSnap<'vir>,
                                    vir::ExprPerm<'vir>,
                                )| {
                                    let self_csnap = self_expr.downcast_ty();
                                    let self_discr = snap_to_discr_snap.call()(self_csnap);
                                    let variant_conjs: Vec<_> = variant_preds
                                        .iter()
                                        .map(|(discr, fields)| {
                                            let preds: Vec<_> = fields
                                                .iter()
                                                .map(|(acc, expr)| {
                                                    expr.reify(vcx, (acc.read(self_csnap), perm))
                                                })
                                                .collect();
                                            (discr, vcx.mk_conj(&preds))
                                        })
                                        .collect();
                                    let (first, rest) = variant_conjs.split_first().unwrap();
                                    rest.iter()
                                        .fold(first.1, |else_, (discr, conj)| {
                                            vcx.mk_ternary_expr(
                                                vir::expr! { ([self_discr]) == ([*discr]) },
                                                *conj,
                                                else_,
                                            )
                                        })
                                        .kind
                                },
                            ),
                        ));
                    }
                    _ => (),
                };
            }
            Ok((
                (),
                IndirectPredicatesWandRhsEncOutputRef::new(predicate_applications),
            ))
        })
    }
}

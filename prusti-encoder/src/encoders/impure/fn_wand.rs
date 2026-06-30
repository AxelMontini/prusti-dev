use crate::encoders::{
    ImpureEncVisitor, MirLocalDefEncOutput, MirSpecEnc, TyUseImpureEnc,
    pure::spec::{EncodedPledge, MirSpecEncMode, PledgeArgs, PledgeExpr},
    ty::{
        RustTyDecomposition,
        generics::GParams,
        indirect::{IndirectPredicatesEnc, projection_for_generalized_idx},
        indirect_wand::{IndirectPredicatesWandLhsEnc, IndirectPredicatesWandRhsEnc},
    },
};
use pcg::borrow_pcg::{
    FunctionData, FunctionShape, FunctionShapeInput, FunctionShapeNode, FunctionShapeOutput,
    MakeFunctionShapeError, region_projection::Generalized, state::BorrowsState,
    unblock_graph::UnblockGraph,
};
use prusti_interface::PrustiError;
use prusti_rustc_interface::{
    data_structures::fx::FxHashSet,
    middle::{mir, ty},
    span::def_id::DefId,
};
use task_encoder::{EncodeFullError, EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, HasType, LocalDeclPerm};

/// Encodes the magic wands given a function signature.
pub struct WandEnc;

#[derive(Clone, Debug)]
pub enum WandEncError {
    Unsupported(#[allow(dead_code)] String),
}

impl<'vir, E: TaskEncoder> ImpureEncVisitor<'vir, '_, E> {
    #[tracing::instrument(skip(self), fields(?self.def_id), ret)]
    pub fn package_wands(
        &mut self,
        final_borrow_state: &BorrowsState<'_, 'vir>,
    ) -> Result<Vec<vir::Stmt<'vir>>, EncodeFullError<'vir, E>> {
        let mut wand_packages = Vec::new();
        let label = self.new_label("package_post");
        let result = self.local_defs.locals[mir::RETURN_PLACE].impure_snap;
        let result = self.vcx.mk_local_labelled_old_expr(result, label);
        let args = self
            .local_defs
            .args()
            .map(|a| self.vcx.mk_old_expr(a.impure_snap));
        let args = PledgeExpr::pledge_args(result, args);
        let mut decl_generator = (0..).map(|i| {
            self.vcx.mk_local_decl(
                vir::vir_format!(self.vcx, "_wb_{label}_{i}"),
                vir::TYPE_PERM,
            )
        });

        for wand_data in self.wands.viper_wands() {
            let Some((wand, lhs_perms, rhs_perms)) = self.wands.mk_wand(
                &wand_data,
                args,
                None,
                &mut decl_generator,
                self.vcx,
                self.deps,
            ) else {
                continue;
            };
            // Prepend wand bindings
            for (d, e) in rhs_perms {
                wand_packages.push(
                    self.vcx
                        .mk_local_decl_stmt(d, Some(self.vcx.mk_old_expr(e))),
                );
            }
            for (d, e) in lhs_perms {
                wand_packages.push(self.vcx.mk_local_decl_stmt(d, Some(e)));
            }

            tracing::debug!(?wand_data, "Wand Data for UnblockGraph");
            let mut package_script = Vec::new();
            for rhs in wand_data.rhs.iter() {
                let ug = UnblockGraph::for_node(
                    mir::Place::from(rhs.mir_local()),
                    final_borrow_state,
                    self.pcg_ctxt(),
                );
                let fbr_formatted = format!("{final_borrow_state:#?}");
                tracing::debug!(
                    ?ug,
                    ?rhs,
                    final_borrow_state = fbr_formatted,
                    "UnblockGraph"
                );
                let actions = ug.actions(self.pcg_ctxt()).unwrap();
                tracing::debug!(?actions, "UnblockGraph Actions");
                let unblock = self.block(|visitor| {
                    visitor.pcs_unblock_actions(final_borrow_state, &actions, Some(label))
                })?;
                package_script.extend(unblock);
            }

            for EncodedPledge {
                expiry_postcondition,
                ..
            } in &wand_data.pledges
            {
                let span = expiry_postcondition.span();
                self.vcx.with_span(span, |vcx| {
                    vcx.handle_error("exhale.failed:assertion.false", move |_| {
                        Some(vec![PrustiError::verification(
                            "pledge postcondition might not hold",
                            span.into(),
                        )])
                    });
                    package_script.push(vcx.mk_exhale_stmt(expiry_postcondition.expr(args)));
                });
            }
            // Add
            wand_packages.push(
                self.vcx
                    .mk_package_stmt(wand, self.vcx.alloc_slice(&package_script)),
            );
        }
        Ok(wand_packages)
    }
}

type EncodedPledges<'vir> = Vec<EncodedPledge<'vir>>;

/// Not tied to a caller or callee context. `indirect_pres`, `indirect_posts`,
/// `wand_posts`, and `package_wands` are identity-substituted and intended for
/// use in the callee's own contract; `apply_wands` is for caller use and
/// re-substitutes via a [`WandCallContext`].
#[derive(Clone)]
pub struct WandEncOutput<'vir> {
    /// Information about the corresponding function.
    function_data: FunctionData<'vir>,

    /// The lifetime projections of all arguments to the function.
    inputs: Vec<FunctionShapeInput<Generalized>>,

    /// The lifetime projections of all function outputs (according to the
    /// corresponding [`FunctionShape`]). This *includes* lifetime projections
    /// of nested lifetimes in the function arguments.
    outputs: Vec<FunctionShapeOutput<Generalized>>,

    /// Encoded VIR expressions for the magic wands.
    wands: Vec<WandData<'vir>>,
}

/// Substitution context for instantiating a wand at a call site. When `None`,
/// the wand is encoded using the callee's identity substitution (appropriate
/// when emitting wands inside the function being defined). When `Some`, the
/// wand is re-encoded with the call-site substitutions and the caller's
/// generic parameters, so that placeholders like `Self` or other callee
/// generics are replaced by concrete types from the caller's perspective.
#[derive(Debug, Clone, Copy)]
pub struct WandCallContext<'vir> {
    pub caller_substs: ty::GenericArgsRef<'vir>,
    pub caller_g_params: GParams<'vir>,
}

impl<'vir> WandEncOutput<'vir> {
    pub(crate) fn fn_sig(
        &self,
        vcx: &'vir vir::VirCtxt<'vir>,
        call_ctx: Option<WandCallContext<'vir>>,
    ) -> ty::FnSig<'vir> {
        match call_ctx {
            Some(ctx) => self.function_data.fn_sig(vcx.tcx(), ctx.caller_substs),
            None => self.function_data.identity_fn_sig(vcx.tcx()),
        }
    }

    pub(crate) fn g_params(
        &self,
        vcx: &'vir vir::VirCtxt<'vir>,
        call_ctx: Option<WandCallContext<'vir>>,
    ) -> GParams<'vir> {
        match call_ctx {
            Some(ctx) => ctx.caller_g_params,
            None => GParams::new(
                self.function_data.identity_substs(vcx.tcx()),
                self.function_data.param_env(vcx.tcx()),
                false,
            ),
        }
    }

    /// Similar to [`encode_predicates_for_function_shape_node`], but it adds extra
    /// predicates on top of the indirect representation of nodes.
    /// Also it needs to know whether we're encoding the LHS or RHS of a wand,
    /// as the generated expressions might differ.
    #[tracing::instrument(skip(deps, vcx, self, snap))]
    fn encode_predicates_for_wand_node(
        &self,
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, impl TaskEncoder>,
        g: impl Into<FunctionShapeNode<Generalized>> + core::fmt::Debug,
        call_ctx: Option<WandCallContext<'vir>>,
        mut snap: impl FnMut(mir::Local) -> vir::ExprSnap<'vir>,
        is_lhs: bool,
    ) -> Option<
        impl FnOnce(Option<vir::LocalDeclPerm<'vir>>) -> (vir::ExprBool<'vir>, vir::ExprPerm<'vir>),
    > {
        use vir::Reify;
        let g = g.into();
        let fn_sig = self.fn_sig(vcx, call_ctx);
        let arg_ty = g.ty(fn_sig);
        let decomp = RustTyDecomposition::from_ty(arg_ty, self.g_params(vcx, call_ctx));
        let region_proj =
            projection_for_generalized_idx(arg_ty, g.region_idx(), decomp, vcx.tcx())?;
        let data = deps.require_dep::<TyUseImpureEnc>(decomp).unwrap();

        let predicates = if is_lhs {
            deps.require_dep::<IndirectPredicatesWandLhsEnc>(region_proj)
                .unwrap()
                .predicate_applications
        } else {
            deps.require_dep::<IndirectPredicatesWandRhsEnc>(region_proj)
                .unwrap()
                .predicate_applications
        };

        if predicates.is_empty() {
            // There are no resources associated with this node, skip.
            return None;
        }

        tracing::debug!(
            ?g,
            ?decomp,
            ?region_proj,
            ?predicates,
            "Encoded predicates for wand node"
        );

        let local = g.mir_local();
        let local_snap = snap(local);
        let out = move |perm: Option<LocalDeclPerm<'vir>>| {
            let perm_expr = perm
                .map(|decl| vcx.mk_local_ex(decl))
                .unwrap_or_else(|| vcx.mk_full_perm());
            let perm_value = match data.specifics {
                crate::encoders::ty::TySpecifics::ImmRef(data) => {
                    data.perm_field(data.deref_access_snap(local_snap.downcast_ty(), None))
                }
                _ => vcx.mk_no_perm(),
            };
            (
                vcx.mk_conj(
                    &predicates
                        .iter()
                        .map(|p| p.reify(vcx, (local_snap, perm_expr)))
                        .collect::<Vec<_>>(),
                ),
                perm_value,
            )
        };

        Some(out)
    }

    fn encode_predicates_for_function_shape_node(
        &self,
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, impl TaskEncoder>,
        g: impl Into<FunctionShapeNode<Generalized>>,
        call_ctx: Option<WandCallContext<'vir>>,
        mut snap: impl FnMut(mir::Local) -> vir::ExprSnap<'vir>,
    ) -> Option<vir::ExprBool<'vir>> {
        use vir::Reify;
        let g = g.into();
        let arg_ty = g.ty(self.fn_sig(vcx, call_ctx));
        let decomp = RustTyDecomposition::from_ty(arg_ty, self.g_params(vcx, call_ctx));
        let region_proj =
            projection_for_generalized_idx(arg_ty, g.region_idx(), decomp, vcx.tcx())?;
        let predicates = deps
            .require_dep::<IndirectPredicatesEnc>(region_proj)
            .unwrap()
            .predicate_applications;

        if predicates.is_empty() {
            // There are no resources associated with this node, skip.
            return None;
        }

        let local = g.mir_local();
        let local_snap = snap(local);
        Some(
            vcx.mk_conj(
                &predicates
                    .iter()
                    .map(|p| p.reify(vcx, local_snap))
                    .collect::<Vec<_>>(),
            ),
        )
    }

    pub fn indirect_pres<'a, E: TaskEncoder>(
        &'a self,
        vcx: &'vir vir::VirCtxt<'vir>,
        local_defs: &'a MirLocalDefEncOutput<'vir>,
        deps: &'a mut TaskEncoderDependencies<'vir, E>,
    ) -> impl Iterator<Item = vir::ExprBool<'vir>> + 'a {
        self.inputs().filter_map(|g| {
            self.encode_predicates_for_function_shape_node(vcx, deps, g, None, |i| {
                local_defs[i].impure_snap
            })
        })
    }

    pub fn indirect_posts<'a, E: TaskEncoder>(
        &'a self,
        vcx: &'vir vir::VirCtxt<'vir>,
        local_defs: &'a MirLocalDefEncOutput<'vir>,
        deps: &'a mut TaskEncoderDependencies<'vir, E>,
    ) -> impl Iterator<Item = vir::ExprBool<'vir>> + 'a {
        // The encoded predicates for the input lifetime projections that are
        // not blocked by any of the result lifetime projections. These will be
        // encoded as part of the postcondition of the function (in contrast,
        // the predicates for the blocked inputs will appear on the right-hand
        // side of a magic wand in the postcondition).
        let unblocked_input_posts = self
            .inputs()
            .filter(|i| !self.blocked_inputs().contains(i))
            .filter_map(|lp| {
                self.encode_predicates_for_function_shape_node(vcx, deps, lp, None, |i| {
                    vcx.mk_old_expr(local_defs[i].impure_snap)
                })
            })
            .collect::<Vec<_>>()
            .into_iter();

        let output_posts = self.outputs().filter_map(|g| {
            self.encode_predicates_for_function_shape_node(vcx, deps, g, None, |i| {
                local_defs[i].impure_snap
            })
        });
        unblocked_input_posts.chain(output_posts)
    }

    pub fn wand_posts<'a, E: TaskEncoder>(
        &'a self,
        vcx: &'vir vir::VirCtxt<'vir>,
        local_defs: &'a MirLocalDefEncOutput<'vir>,
        deps: &'a mut TaskEncoderDependencies<'vir, E>,
    ) -> impl Iterator<Item = vir::ExprBool<'vir>> + 'a {
        let wand_result =
            vcx.mk_local_decl("wand_result", local_defs[mir::RETURN_PLACE].local_snap.ty());
        let wand_result_expr = vcx.mk_local_ex(wand_result);
        let args = local_defs
            .args()
            .map(|arg| vcx.mk_old_expr(arg.impure_snap));
        let args = PledgeExpr::pledge_args(wand_result_expr, args);

        // TODO: wands for late-bound regions
        self.viper_wands().into_iter().filter_map(move |wand_data| {
            let decl_generator = (0..)
                .map(|i| vcx.mk_local_decl(vir::vir_format!(vcx, "_wb_let_{i}"), vir::TYPE_PERM));
            let (wand, lhs_perms, rhs_perms) =
                self.mk_wand(&wand_data, args, None, decl_generator, vcx, deps)?;
            let wand_expr = vcx.mk_wand_expr(wand);
            let expr = rhs_perms.into_iter().fold(wand_expr, |expr, (decl, val)| {
                vcx.mk_let_expr(decl, vcx.mk_old_expr(val), expr)
            });
            let expr = lhs_perms
                .into_iter()
                .fold(expr, |expr, (decl, val)| vcx.mk_let_expr(decl, val, expr));

            Some(vcx.mk_let_expr(wand_result, local_defs[mir::RETURN_PLACE].impure_snap, expr))
        })
    }

    pub fn apply_wands<E: TaskEncoder>(
        &self,
        arguments: &[vir::ExprSnap<'vir>],
        label_pre: &'vir str,
        label_post: &'vir str,
        call_ctx: WandCallContext<'vir>,
        visitor: &mut ImpureEncVisitor<'vir, '_, E>,
    ) {
        let result = visitor
            .vcx
            .mk_local_labelled_old_expr(arguments[mir::RETURN_PLACE.as_usize()], label_post);
        let args = (1..arguments.len()).map(|l| {
            visitor
                .vcx
                .mk_local_labelled_old_expr(arguments[l], label_pre)
        });
        let args = PledgeExpr::pledge_args(result, args);
        let mut decl_generator = (0..).map(|i| {
            visitor.vcx.mk_local_decl(
                vir::vir_format!(visitor.vcx, "_wb_{label_post}_{i}"),
                vir::TYPE_PERM,
            )
        });
        for wand_data in self.viper_wands() {
            let Some((wand, lhs_perms, rhs_perms)) = self.mk_wand(
                &wand_data,
                args,
                Some(call_ctx),
                &mut decl_generator,
                visitor.vcx,
                visitor.deps,
            ) else {
                continue;
            };
            for (d, e) in rhs_perms {
                visitor.stmt(visitor.vcx.mk_local_decl_stmt(
                    d,
                    Some(visitor.vcx.mk_old(e, vir::OldLabel::Label(label_pre))),
                ));
            }
            for (d, e) in lhs_perms {
                visitor.stmt(visitor.vcx.mk_local_decl_stmt(d, Some(e)));
            }
            visitor.stmt(visitor.vcx.mk_apply_stmt(wand));
        }
    }

    /// Used to encode a magic wand, which may contain references to yet-undeclared variables.
    /// It may return a non-empty perm-expr vector if needed (e.g. when permission fields are
    /// involved).
    /// The returned closure takes
    fn mk_wand<'a, E: TaskEncoder>(
        &'a self,
        wand_data: &WandData<'vir>,
        pledge_args: PledgeArgs<'vir>,
        call_ctx: Option<WandCallContext<'vir>>,
        mut decl_generator: impl Iterator<Item = vir::LocalDeclPerm<'vir>>,
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, E>,
    ) -> Option<(
        vir::Wand<'vir>,
        Vec<(vir::LocalDeclPerm<'vir>, vir::ExprPerm<'vir>)>,
        Vec<(vir::LocalDeclPerm<'vir>, vir::ExprPerm<'vir>)>,
    )> {
        debug_assert!(!wand_data.lhs.is_empty());
        // TODO: Deduplicate. Immref wands are a bit more involved than regular ones,
        // and they introduce some perm field expressions.
        // TODO: What if rhs is blocked by multiple lhs? We need multiple perm let bindings and
        // stuff
        let rhs = wand_data
            .rhs
            .iter()
            .zip(&mut decl_generator)
            .filter_map(|(g, decl)| {
                self.encode_predicates_for_wand_node(
                    vcx,
                    deps,
                    *g,
                    call_ctx,
                    |i| pledge_args[i],
                    false,
                )
                .map(|f| f(Some(decl)))
                .map(|(expr, perm)| (expr, (decl, perm)))
            });
        let (mut rhs, rhs_perm_exprs): (Vec<_>, Vec<_>) = rhs.unzip();
        rhs.extend(
            wand_data
                .pledges
                .iter()
                .map(|pledge| pledge.expiry_postcondition.expr(pledge_args)),
        );
        if rhs.is_empty() {
            // We skip emitting the wand when there is nothing on the RHS, i.e.,
            // nothing would be unblocked by applying this wand, nor are there
            // any pledge postconditions.
            return None;
        }
        let rhs = vcx.mk_conj(&rhs);
        let lhs = wand_data
            .lhs
            .iter()
            .zip(decl_generator)
            .filter_map(|(g, decl)| {
                self.encode_predicates_for_wand_node(
                    vcx,
                    deps,
                    *g,
                    call_ctx,
                    |i| pledge_args[i],
                    true,
                )
                .map(|f| f(Some(decl)))
                .map(|(expr, perm)| (expr, (decl, perm)))
            });
        let (mut lhs, lhs_perm_exprs): (Vec<_>, Vec<_>) = lhs.unzip();
        lhs.extend(
            wand_data
                .pledges
                .iter()
                .filter_map(|pledge| pledge.expiry_obligation)
                .map(|expr| expr.expr(pledge_args)),
        );
        let lhs = vcx.mk_conj(&lhs);
        Some((vcx.mk_wand(lhs, rhs), lhs_perm_exprs, rhs_perm_exprs))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct WandEncTask<'tcx> {
    pub data: FunctionData<'tcx>,
}

impl<'tcx> WandEncTask<'tcx> {
    pub fn def_id(&self) -> DefId {
        self.data.def_id()
    }

    pub fn function_shape(
        &self,
        vcx: &vir::VirCtxt<'tcx>,
    ) -> Result<FunctionShape<Generalized>, MakeFunctionShapeError> {
        self.data.shape(vcx.tcx())
    }
}

pub type WandRhsKey = FunctionShapeInput<Generalized>;
pub type WandLhsKey = FunctionShapeNode<Generalized>;

#[derive(Clone, Debug)]
pub struct WandData<'vir> {
    /// Lifetime projections on the right-hand side of the wand. Guaranteed to be
    /// non-empty.
    rhs: Vec<WandRhsKey>,
    /// Lifetime projections on the left-hand side of the wand. Guaranteed to be
    /// non-empty.
    lhs: Vec<WandLhsKey>,
    pledges: EncodedPledges<'vir>,
}

impl<'vir> WandData<'vir> {
    pub fn new(lhs: Vec<WandLhsKey>, rhs: Vec<WandRhsKey>, pledges: EncodedPledges<'vir>) -> Self {
        debug_assert!(!lhs.is_empty());
        debug_assert!(!rhs.is_empty());
        Self { rhs, lhs, pledges }
    }
}

impl TaskEncoder for WandEnc {
    task_encoder::encoder_cache!(WandEnc);

    type TaskDescription<'vir> = WandEncTask<'vir>;

    type TaskKey<'vir> = WandEncTask<'vir>;

    type OutputFullDependency<'vir> = WandEncOutput<'vir>;

    type EncodingError = WandEncError;

    const ENCODER_NAME: &'static str = "wand encoder";

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        task.clone()
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(task_key.clone(), ())?;
        vir::with_vcx(|vcx| {
            let def_id = task_key.def_id();

            let shape = task_key.function_shape(vcx).map_err(|e| {
                EncodeFullError::EncodingError(
                    WandEncError::Unsupported(format!("function shape: {e:?}")),
                    None,
                )
            })?;

            let coupled_edges = shape.coupled_edges();

            tracing::debug!(?def_id, ?shape, "Function shape");

            let (inputs, outputs) = shape.take_inputs_and_outputs();
            let spec = deps.require_dep::<MirSpecEnc>((def_id, def_id, MirSpecEncMode::Impure))?;
            tracing::debug!(?def_id, ?spec, "Function spec");
            if coupled_edges.is_empty() {
                assert!(spec.pledges.is_empty());
                return Ok((
                    (),
                    WandEncOutput {
                        function_data: task_key.data,
                        inputs,
                        outputs,
                        wands: vec![],
                    },
                ));
            }
            let pledges = spec.pledges;
            if pledges.len() > 1 && coupled_edges.len() > 1 {
                return Err(EncodeFullError::EncodingError(
                    WandEncError::Unsupported(format!(
                        "multiple pledges: {pledges:?}, coupled edges: {coupled_edges:?}"
                    )),
                    None,
                ));
            }
            let wands: Vec<WandData<'vir>> = coupled_edges
                .into_iter()
                .filter_map(|hyper_edge| {
                    let (sources, mut targets) = hyper_edge.into_tuple();
                    // We don't want to emit an identity wand, like P --* P. This can happen when
                    // PCG returns self-edges, like for fn(x: &'a mut &'b i32) where 'b is in
                    // invariant position and we therefore have an edge x|'b -> x|'b.
                    // Currently, these edges also prevent us from emitting indirect postconditions.
                    // TODO: we might want to emit these identity wands in the future to attach functional
                    // specifications to them. We still need to emit the resources on the wand's LHS.
                    let mut sources_as_nodes = sources
                        .iter()
                        .map(|&s| s.to_function_shape_node())
                        .collect::<Vec<_>>();
                    sources_as_nodes.sort();
                    targets.sort();
                    if sources_as_nodes == targets {
                        return None;
                    }
                    Some(WandData::new(targets, sources, pledges.clone()))
                })
                .collect();
            tracing::debug!(?def_id, ?wands, "Function wands");
            let output: WandEncOutput<'vir> = WandEncOutput {
                function_data: task_key.data,
                inputs,
                outputs,
                wands,
            };
            Ok(((), output))
        })
    }
}

impl<'vir> WandEncOutput<'vir> {
    pub fn viper_wands(&self) -> Vec<WandData<'vir>> {
        self.wands.clone()
    }

    /// All lifetime projections in the arguments that are blocked by any of the
    /// lifetime projections in the function's result.
    pub fn blocked_inputs(&self) -> FxHashSet<FunctionShapeInput<Generalized>> {
        self.wands
            .iter()
            .flat_map(|wand| wand.rhs.iter().copied())
            .collect()
    }

    pub fn inputs(&self) -> impl Iterator<Item = FunctionShapeInput<Generalized>> + '_ {
        self.inputs.iter().copied()
    }

    pub fn outputs(&self) -> impl Iterator<Item = FunctionShapeOutput<Generalized>> + '_ {
        self.outputs.iter().copied()
    }
}

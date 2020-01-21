/- UNUSED ARGUMENTS: -/

-- tactic/where.lean
#print where.where_cmd /- argument 1: (_x : interactive.decl_meta_info) -/

-- tactic/tfae.lean
#print tactic.interactive.tfae_have /- argument 5: (discharger : opt_param (tactic unit) tactic.solve_by_elim) -/

-- tactic/ring2.lean
#print tactic.ring2.horner_expr.inv /- argument 1: (e : tactic.ring2.horner_expr) -/

-- tactic/restate_axiom.lean
#print restate_axiom_cmd /- argument 1: (meta_info : interactive.decl_meta_info) -/

-- tactic/replacer.lean
#print tactic.def_replacer_cmd /- argument 1: (meta_info : interactive.decl_meta_info) -/

-- tactic/reassoc_axiom.lean
#print tactic.calculated_Prop /- argument 3: (hh : α) -/

-- tactic/norm_num.lean
#print norm_num.prove_lt /- argument 1: (simp : expr → tactic (expr × expr)) -/

-- tactic/monotonicity/interactive.lean
#print tactic.interactive.mono_aux /- argument 2: (cfg : opt_param tactic.interactive.mono_cfg {unify := ff}) -/
#print tactic.interactive.match_ac /- argument 2: (unif : bool) -/

-- tactic/monotonicity/basic.lean
#print tactic.interactive.monotoncity.check /- argument 2: (prio : ℕ), argument 3: (persistent : bool) -/
#print tactic.interactive.monotoncity.check_rel /- argument 1: (xs : list expr) -/

-- tactic/localized.lean
#print localized_cmd /- argument 1: (meta_info : interactive.decl_meta_info) -/
#print open_locale_cmd /- argument 1: (meta_info : interactive.decl_meta_info) -/

-- tactic/local_cache.lean
#print tactic.local_cache.internal.save_data /- argument 3: [_inst_2 : has_reflect α] -/
#print tactic.local_cache.internal.load_data /- argument 3: [_inst_2 : has_reflect α] -/

-- tactic/linarith.lean
#print linarith.mul_eq /- argument 6: (hb : b > 0) -/

-- tactic/core.lean
#print tactic.symmetry_hyp /- argument 2: (md : opt_param tactic.transparency semireducible) -/

-- tactic/converter/interactive.lean
#print old_conv.istep /- argument 3: (col0 : ℕ) (duplicate) -/

-- tactic/converter/binders.lean
#print binder_eq_elim.check_eq /- argument 1: (b : binder_eq_elim) -/

-- tactic/chain.lean
#print tactic.trace_output /- argument 2: [_inst_1 : has_to_string (tactic.tactic_script α)] -/

-- set_theory/zfc.lean
#print Set.map_definable_aux /- argument 2: [H : pSet.definable 1 f] -/

-- set_theory/surreal.lean
#print pgame.add_lt_add /- argument 5: (ow : pgame.numeric w), argument 6: (ox : pgame.numeric x) -/
#print pgame.numeric.lt_move_right /- argument 2: (o : pgame.numeric x) -/
#print pgame.numeric.move_left_lt /- argument 2: (o : pgame.numeric x) -/

-- set_theory/ordinal_notation.lean
#print onote.oadd_lt_oadd_2 /- argument 7: (h₂ : onote.NF (onote.oadd e n₂ o₂)) -/
#print onote.oadd_lt_oadd_1 /- argument 8: (h₂ : onote.NF (onote.oadd e₂ n₂ o₂)) -/
#print onote.oadd_lt_oadd_3 /- argument 5: (h₁ : onote.NF (onote.oadd e n a₁)), argument 6: (h₂ : onote.NF (onote.oadd e n a₂)) -/

-- set_theory/ordinal.lean
#print principal_seg.top_lt_top /- argument 7: [_inst_1 : is_trans β s] -/
#print principal_seg.trans_top /- argument 7: [_inst_1 : is_trans β s] -/

-- ring_theory/unique_factorization_domain.lean
#print associates.factor_set /- argument 3: [_inst_5 : unique_factorization_domain α] -/
#print associates.unique' /- argument 4: [_inst_3 : decidable_eq (associates α)] -/
#print associates.factor_set.coe_add /- argument 4: [_inst_3 : decidable_eq (associates α)] -/
#print unique_factorization_domain.exists_mem_factors_of_dvd /- argument 4: [_inst_3 : decidable_eq (associates α)] -/
#print associates.factors' /- argument 4: [_inst_3 : decidable_eq (associates α)] -/
#print associates.factor_set.prod /- argument 4: [_inst_3 : decidable_eq (associates α)] -/

-- ring_theory/power_series.lean
#print power_series.mk /- argument 2: [_inst_1 : add_monoid α] -/

-- ring_theory/polynomial.lean
#print polynomial.of_subring /- argument 3: [_inst_2 : decidable_eq R] -/
#print ideal.of_polynomial /- argument 3: [_inst_2 : decidable_eq R] -/
#print polynomial.degree_le /- argument 3: [_inst_2 : decidable_eq R] -/

-- ring_theory/multiplicity.lean
#print multiplicity.finite_mul_aux /- argument 3: [_inst_2 : decidable_rel has_dvd.dvd] -/

-- ring_theory/localization.lean
#print localization.r /- argument 4: [_inst_2 : is_submonoid S] -/
#print localization.fraction_ring.eq_zero_of_ne_zero_of_mul_eq_zero /- argument 3: [_inst_4 : decidable_eq β] -/

-- ring_theory/ideal_operations.lean
#print ideal.map /- argument 6: [_inst_3 : is_ring_hom f] -/

-- ring_theory/algebra.lean
#print algebra.comap.ring /- argument 7: [_inst_4 : algebra R S], argument 8: [_inst_5 : algebra S A] -/
#print algebra.comap.has_scalar /- argument 7: [_inst_4 : algebra R S] -/
#print algebra.comap.comm_ring /- argument 7: [_inst_9 : algebra R S], argument 8: [_inst_10 : algebra S A] -/

-- ring_theory/adjoin.lean
#print algebra.adjoin_singleton_eq_range /- argument 6: [_inst_4 : decidable_eq R], argument 7: [_inst_5 : decidable_eq A] -/
#print algebra.adjoin_eq_range /- argument 7: [_inst_4 : decidable_eq R], argument 8: [_inst_5 : decidable_eq A] -/

-- order/filter/filter_product.lean
#print filter.filter_product.of_seq_zero /- argument 5: (f : α → β) -/
#print filter.filter_product.of_seq_one /- argument 5: (f : α → β) -/
#print filter.filter_product.abs_def /- argument 7: (y : filter.filterprod β φ) (duplicate) -/

-- number_theory/pell.lean
#print pell.x_sub_y_dvd_pow_lem /- argument 2: (a1 : a > 1) -/
#print pell.az /- argument 2: (a1 : a > 1) -/

-- measure_theory/measure_space.lean
#print measure_theory.measure' /- argument 4: (m0 : m ∅ is_measurable.empty = 0) -/

-- linear_algebra/matrix.lean
#print linear_equiv_matrix /- argument 14: [_inst_13 : decidable_eq κ] -/

-- linear_algebra/finsupp.lean
#print linear_map.map_finsupp_total /- argument 11: [_inst_6 : fintype ι] -/
#print finsupp.supported_eq_span_single /- argument 6: [_inst_3 : module R M], argument 7: [_inst_4 : has_one M] -/

-- linear_algebra/basis.lean
#print linear_independent_monoid_hom /- argument 2: [_inst_1 : ring R] -/
#print pi.linear_independent_std_basis /- argument 8: [_inst_4 : fintype η] -/
#print constr_smul /- argument 8: [_inst_9 : module R M], argument 14: {b : M} -/

-- group_theory/subgroup.lean
#print is_add_subgroup.mem_trivial /- argument 2: [_inst_1 : add_group α] (duplicate) -/
#print is_group_hom.ker /- argument 6: [_inst_3 : is_group_hom f] -/
#print is_subgroup.normalizer_is_subgroup /- argument 4: [_inst_2 : is_subgroup s] -/
#print is_add_subgroup.normalizer_is_add_subgroup /- argument 4: [_inst_2 : is_add_subgroup s] -/
#print is_add_group_hom.ker /- argument 6: [_inst_3 : is_add_group_hom f] -/
#print is_subgroup.mem_trivial /- argument 2: [_inst_1 : group α] (duplicate) -/

-- group_theory/perm/sign.lean
#print equiv.perm.sign_cycle /- argument 3: [_inst_2 : fintype α] (duplicate) -/
#print equiv.perm.is_cycle_swap /- argument 3: [_inst_2 : fintype α] -/
#print equiv.perm.eq_swap_of_is_cycle_of_apply_apply_eq_self /- argument 3: [_inst_2 : fintype α] -/
#print equiv.perm.card_support_swap /- argument 3: [_inst_2 : fintype α] (duplicate) -/
#print equiv.perm.is_cycle_swap_mul_aux₁ /- argument 3: [_inst_2 : fintype α] -/
#print equiv.perm.support_swap /- argument 3: [_inst_2 : fintype α] (duplicate) -/

-- group_theory/order_of_element.lean
#print card_subgroup_dvd_card /- argument 4: [_inst_3 : decidable_eq α] -/
#print exists_gpow_eq_one /- argument 4: [_inst_3 : decidable_eq α] -/
#print card_trivial /- argument 3: [_inst_2 : fintype α], argument 4: [_inst_3 : decidable_eq α] -/
#print quotient_group.fintype /- argument 4: [_inst_3 : decidable_eq α] -/

-- group_theory/eckmann_hilton.lean
#print eckmann_hilton.comm_group /- argument 7: (h₂ : eckmann_hilton.is_unital m₂ e₂) -/

-- group_theory/coset.lean
#print quotient_group.eq_class_eq_left_coset /- argument 2: [_inst_1 : group α] (duplicate) -/
#print quotient_group.inhabited /- argument 2: [_inst_1 : group α] (duplicate) -/
#print normal_of_eq_cosets /- argument 4: [_inst_2 : is_subgroup s] -/
#print normal_of_eq_add_cosets /- argument 4: [_inst_2 : is_add_subgroup s] -/
#print quotient_add_group.eq_class_eq_left_coset /- argument 2: [_inst_1 : add_group α] (duplicate) -/
#print quotient_add_group.inhabited /- argument 2: [_inst_1 : add_group α] (duplicate) -/

-- group_theory/abelianization.lean
#print abelianization.lift.unique /- argument 8: [_inst_4 : is_group_hom g] -/

-- field_theory/splitting_field.lean
#print polynomial.splits /- argument 6: [_inst_4 : is_ring_hom i] -/

-- field_theory/perfect_closure.lean
#print perfect_closure.has_inv /- argument 4: [_inst_2 : prime p], argument 5: [_inst_3 : char_p α p] -/
#print perfect_closure.eq_iff' /- argument 4: [_inst_2 : prime p], argument 5: [_inst_3 : char_p α p] -/

-- field_theory/mv_polynomial.lean
#print mv_polynomial.R /- argument 3: [_inst_1 : fintype σ] -/
#print mv_polynomial.evalₗ /- argument 4: [_inst_2 : fintype α], argument 5: [_inst_3 : fintype σ] -/

-- field_theory/finite.lean
#print subgroup_units_cyclic /- argument 3: [_inst_2 : decidable_eq α] -/

-- data/vector2.lean
#print vector.traverse_def /- argument 4: [_inst_3 : is_lawful_applicative F] -/

-- data/seq/wseq.lean
#print wseq.think_congr /- argument 4: (a : α) -/

-- data/seq/computation.lean
#print computation.map_congr /- argument 3: (R : α → α → Prop), argument 4: (S : β → β → Prop) -/

-- data/real/cau_seq.lean
#print cau_seq.lim_zero /- argument 6: [_inst_3 : is_absolute_value abv] -/

-- data/prod.lean
#print prod.lex.decidable /- argument 4: [_inst_2 : decidable_eq β] -/

-- data/polynomial.lean
#print polynomial.eval₂_zero /- argument 7: [_inst_3 : is_semiring_hom f] -/
#print polynomial.map_injective /- argument 8: (p : polynomial α) -/

-- data/pnat/basic.lean
#print pnat.div_exact /- argument 3: (h : k ∣ m) -/

-- data/pequiv.lean
#print pequiv.trans_single_of_eq_none /- argument 4: [_inst_1 : decidable_eq α] -/

-- data/padics/padic_numbers.lean
#print padic_seq /- argument 2: [_inst_1 : prime p] -/

-- data/padics/padic_norm.lean
#print padic_norm.neg /- argument 2: [hp : prime p] -/

-- data/num/basic.lean
#print cast_pos_num /- argument 2: [_inst_1 : has_zero α] -/

-- data/multiset.lean
#print multiset.length_ndinsert_of_mem /- argument 2: [_inst_1 : decidable_eq α] (duplicate) -/
#print multiset.length_ndinsert_of_not_mem /- argument 2: [_inst_1 : decidable_eq α] (duplicate) -/
#print multiset.le_inf /- argument 3: [_inst_2 : decidable_eq α] -/
#print multiset.sup_le /- argument 3: [_inst_2 : decidable_eq α] -/
#print multiset.pi.empty /- argument 2: [_inst_1 : decidable_eq α] -/

-- data/mllist.lean
#print tactic.mllist.m_of_list /- argument 2: [_inst_1 : alternative m] -/
#print tactic.mllist.head /- argument 2: [_inst_1 : alternative m] (duplicate) -/
#print tactic.mllist.force /- argument 2: [_inst_1 : alternative m] -/
#print tactic.mllist.enum_from /- argument 2: [_inst_1 : alternative m] -/
#print tactic.mllist.map /- argument 2: [_inst_1 : alternative m] -/
#print tactic.mllist.filter /- argument 2: [_inst_1 : alternative m] -/
#print tactic.mllist.of_list /- argument 2: [_inst_1 : alternative m] -/
#print tactic.mllist.uncons /- argument 2: [_inst_1 : alternative m] -/
#print tactic.mllist.mmap /- argument 2: [_inst_1 : alternative m] -/
#print tactic.mllist.filter_map /- argument 2: [_inst_1 : alternative m] -/
#print tactic.mllist.monad_lift /- argument 2: [_inst_1 : alternative m] -/
#print tactic.mllist.join /- argument 2: [_inst_1 : alternative m] -/
#print tactic.mllist.mfirst /- argument 2: [_inst_1 : alternative m] (duplicate) -/
#print tactic.mllist.take /- argument 2: [_inst_1 : alternative m] -/
#print tactic.mllist.mfilter /- argument 2: [_inst_1 : alternative m] (duplicate) -/
#print tactic.mllist.append /- argument 2: [_inst_1 : alternative m] -/
#print tactic.mllist.mfilter_map /- argument 2: [_inst_1 : alternative m] (duplicate) -/

-- data/matrix/pequiv.lean
#print pequiv.matrix_mul_apply /- argument 7: [_inst_6 : decidable_eq l] -/
#print pequiv.mul_matrix_apply /- argument 9: [_inst_8 : decidable_eq n] -/
#print pequiv.to_matrix /- argument 5: [_inst_7 : decidable_eq m] -/
#print pequiv.single_mul_single_right /- argument 10: [_inst_6 : decidable_eq l] -/

-- data/matrix/basic.lean
#print matrix /- argument 3: [_inst_1 : fintype m], argument 4: [_inst_2 : fintype n] -/

-- data/list/sigma.lean
#print list.mem_ext /- argument 3: [_inst_1 : decidable_eq α] -/

-- data/list/basic.lean
#print list.func.length_neg /- argument 2: [_inst_1 : inhabited α] -/
#print list.func.get_neg /- argument 2: [_inst_1 : inhabited α] -/

-- data/list/alist.lean
#print alist.disjoint /- argument 3: [_inst_1 : decidable_eq α] -/
#print alist.foldl /- argument 3: [_inst_1 : decidable_eq α] -/

-- data/int/basic.lean
#print int.div_eq_div_of_mul_eq_mul /- argument 5: (H1 : b ∣ a) -/
#print int.eq_mul_div_of_mul_eq_mul_of_dvd_left /- argument 6: (hd : d ≠ 0) -/

-- data/hash_map.lean
#print hash_map.mk_as_list /- argument 3: [_inst_1 : decidable_eq α] -/

-- data/fp/basic.lean
#print fp.div_nat_lt_two_pow /- argument 1: [C : fp.float_cfg] -/

-- data/fintype.lean
#print fintype.bij_inv /- argument 5: [_inst_3 : fintype β] -/
#print fintype.choose_x /- argument 3: [_inst_2 : decidable_eq α] -/

-- data/finset.lean
#print finset.lt_wf /- argument 2: [_inst_1 : decidable_eq α] -/

-- data/finmap.lean
#print finmap.disjoint /- argument 3: [_inst_1 : decidable_eq α] -/
#print finmap.foldl /- argument 3: [_inst_1 : decidable_eq α] -/

-- data/fin.lean
#print fin.add_nat_val /- argument 4: (h : m ≤ i.val) -/

-- data/dfinsupp.lean
#print dfinsupp.subtype_domain_sum /- argument 3: [_inst_1 : decidable_eq ι], argument 6: [_inst_3 : Π (i : ι), decidable_pred (eq 0)] -/
#print dfinsupp.map_range_def /- argument 8: [_inst_7 : Π (i : ι), decidable_pred (eq 0)] -/
#print dfinsupp.decidable_eq /- argument 3: [_inst_1 : decidable_eq ι] (duplicate) -/
#print dfinsupp.map_range_single /- argument 7: [_inst_6 : Π (i : ι), decidable_pred (eq 0)], argument 8: [_inst_7 : Π (i : ι), decidable_pred (eq 0)] -/
#print dfinsupp.sum_apply /- argument 3: [_inst_1 : decidable_eq ι] -/
#print dfinsupp.zip_with_def /- argument 5: [_inst_3 : Π (i : ι), decidable_pred (eq 0)] -/

-- data/complex/exponential.lean
#print is_cau_series_of_abv_le_cau /- argument 5: [_inst_3 : archimedean α] -/
#print abv_sum_le_sum_abv /- argument 5: [_inst_3 : archimedean α] -/

-- data/analysis/topology.lean
#print ctop.realizer.nhds_F /- argument 4: (m : α → β) -/
#print ctop.realizer.nhds_σ /- argument 4: (m : α → β) -/
#print compact.realizer /- argument 3: (R : ctop.realizer α) -/

-- computability/turing_machine.lean
#print turing.TM1to1.supports_stmt_write /- argument 7: [_inst_4 : fintype Γ] -/
#print turing.TM2to1.st_run /- argument 5: [_inst_2 : inhabited Λ] -/
#print turing.TM1to1.tr_tape_drop_right /- argument 2: [_inst_1 : inhabited Γ] -/
#print turing.TM1to1.step_aux_write /- argument 10: (enc0 : enc (default Γ) = vector.repeat ff n), argument 11: (encdec : ∀ (a : Γ), dec (enc a) = a) -/
#print turing.TM1to1.supports_stmt_move /- argument 8: [_inst_4 : fintype Γ] -/
#print turing.TM2.stmts₁ /- argument 6: [_inst_2 : inhabited Λ], argument 7: [_inst_3 : inhabited σ], argument 8: [_inst_4 : fintype K], argument 9: [_inst_5 : Π (k : K), fintype (Γ k)], argument 10: [_inst_6 : fintype σ] -/
#print turing.TM0.machine.map_step /- argument 15: (ss : turing.TM0.supports M S) -/
#print turing.TM1.stmts₁ /- argument 5: [_inst_2 : inhabited Λ], argument 6: [_inst_3 : inhabited σ], argument 7: [_inst_4 : fintype Γ] -/
#print turing.TM2to1.tr_stk /- argument 5: [_inst_2 : inhabited Λ], argument 7: [_inst_3 : inhabited σ], argument 8: (M : Λ → turing.TM2.stmt Γ Λ σ) -/
#print turing.TM1to1.tr_tape' /- argument 2: [_inst_1 : inhabited Γ] -/
#print turing.TM1to1.step_aux_move /- argument 9: (enc0 : enc (default Γ) = vector.repeat ff n) -/
#print turing.TM1to0.Λ' /- argument 4: [_inst_2 : inhabited Λ], argument 6: [_inst_3 : inhabited σ], argument 7: (M : Λ → turing.TM1.stmt Γ Λ σ) -/
#print turing.TM2to1.tr_stmts₁ /- argument 8: (M : Λ → turing.TM2.stmt Γ Λ σ), argument 9: [_inst_4 : fintype K], argument 10: [_inst_5 : Π (k : K), fintype (Γ k)], argument 11: [_inst_6 : fintype σ] -/
#print turing.TM1.supports_stmt /- argument 5: [_inst_2 : inhabited Λ], argument 6: [_inst_3 : inhabited σ], argument 7: [_inst_4 : fintype Γ] -/
#print turing.TM2.supports_stmt /- argument 6: [_inst_2 : inhabited Λ], argument 7: [_inst_3 : inhabited σ], argument 8: [_inst_4 : fintype K], argument 9: [_inst_5 : Π (k : K), fintype (Γ k)], argument 10: [_inst_6 : fintype σ] -/
#print turing.TM0.machine.map_respects /- argument 17: [_inst_6 : turing.pointed_map g₁] -/
#print turing.TM1to0.tr_eval /- argument 8: [_inst_4 : fintype Γ], argument 9: [_inst_5 : fintype σ] -/
#print turing.TM0.machine /- argument 4: [_inst_2 : inhabited Λ] -/

-- category_theory/single_obj.lean
#print category_theory.single_obj /- argument 1: (α : Type u) -/

-- category_theory/monad/limits.lean
#print category_theory.monad.forget_creates_limits.γ /- argument 8: [_inst_2 : category_theory.limits.has_limit (D ⋙ category_theory.monad.forget T)] -/

-- category_theory/limits/types.lean
#print category_theory.limits.types.types_colimit_pre /- argument 7: (g : (category_theory.limits.types.colimit (E ⋙ F)).X) -/

-- category_theory/full_subcategory.lean
#print category_theory.induced_category /- argument 3: [𝒟 : category_theory.category D], argument 4: (F : C → D) -/

-- category_theory/category/Kleisli.lean
#print category_theory.Kleisli /- argument 2: [_inst_1 : monad m] -/
#print category_theory.Kleisli.comp_def /- argument 3: [_inst_2 : is_lawful_monad m] -/
#print category_theory.Kleisli.id_def /- argument 3: [_inst_2 : is_lawful_monad m] -/

-- category/traversable/instances.lean
#print list.comp_traverse /- argument 5: [_inst_3 : is_lawful_applicative F] -/
#print sum.traverse_map /- argument 4: [_inst_4 : is_lawful_applicative G] -/
#print sum.comp_traverse /- argument 6: [_inst_3 : is_lawful_applicative F] -/
#print option.comp_traverse /- argument 5: [_inst_3 : is_lawful_applicative F] -/

-- category/traversable/derive.lean
#print tactic.interactive.traverse_field /- argument 2: (appl_inst : expr) (duplicate) -/
#print tactic.interactive.traverse_constructor /- argument 6: (β : expr) (duplicate) -/

-- category/monad/writer.lean
#print writer_t.ext /- argument 3: [_inst_1 : monad m] -/
#print writer_t.monad_map /- argument 4: [_inst_2 : monad m], argument 5: [_inst_3 : monad m'] -/
#print writer_t.monad_except /- argument 3: [_inst_1 : monad m] (duplicate) -/

-- category/monad/cont.lean
#print writer_t.monad_cont /- argument 2: [_inst_1 : monad m] (duplicate) -/
#print state_t.mk_label /- argument 2: [_inst_1 : monad m] -/

-- category/fold.lean
#print traversable.mfoldl.unop_of_free_monoid /- argument 5: [_inst_2 : is_lawful_monad m] -/

-- category/bitraversable/instances.lean
#print const.bitraverse /- argument 2: [_inst_2 : applicative F], argument 8: (f' : β → F β') -/

-- analysis/calculus/times_cont_diff.lean
#print times_cont_diff.times_cont_diff_fderiv_apply /- argument 11: {s : set E} -/

-- algebra/ordered_ring.lean
#print with_top.has_one /- argument 3: [_inst_2 : decidable_eq α] -/
#print with_top.coe_eq_zero /- argument 4: [_inst_3 : partial_order α] -/
#print with_top.zero_ne_top /- argument 4: [_inst_3 : partial_order α] -/
#print with_top.canonically_ordered_comm_semiring /- argument 2: [_inst_1 : canonically_ordered_comm_semiring α] (duplicate), argument 3: [_inst_2 : decidable_eq α] (duplicate) -/
#print with_top.top_ne_zero /- argument 4: [_inst_3 : partial_order α] -/
#print with_top.coe_zero /- argument 4: [_inst_3 : partial_order α] -/

-- algebra/direct_sum.lean
#print direct_sum /- argument 2: [_inst_1 : decidable_eq ι] -/

-- algebra/direct_limit.lean
#print module.direct_limit.totalize /- argument 12: [_inst_8 : module.directed_system G f] -/
#print module.direct_limit /- argument 12: [_inst_8 : module.directed_system G f] -/
#print ring.direct_limit /- argument 9: [_inst_7 : ∀ (i j : ι) (hij : i ≤ j), is_ring_hom (f i j hij)], argument 10: [_inst_8 : directed_system G f] -/

-- algebra/big_operators.lean
#print finset.prod_ite /- argument 5: [_inst_2 : comm_monoid γ] -/
#print finset.sum_ite /- argument 5: [_inst_2 : add_comm_monoid γ] -/

/- DEFINITIONS ARE MISSING DOCUMENTATION STRINGS: -/

-- topology/uniform_space/uniform_embedding.lean
#print uniform_inducing /- constant missing doc string -/
#print uniform_embedding /- constant missing doc string -/

-- topology/uniform_space/separation.lean
#print uniform_space.separation_quotient.lift /- def missing doc string -/
#print separated /- def missing doc string -/
#print uniform_space.separation_setoid /- def missing doc string -/
#print uniform_space.separation_quotient /- def missing doc string -/
#print uniform_space.separation_quotient.map /- def missing doc string -/

-- topology/uniform_space/completion.lean
#print Cauchy.extend /- def missing doc string -/
#print uniform_space.completion.extension₂ /- def missing doc string -/
#print Cauchy.gen /- def missing doc string -/
#print uniform_space.completion.map₂ /- def missing doc string -/
#print uniform_space.completion.completion_separation_quotient_equiv /- def missing doc string -/
#print uniform_space.completion.cpkg /- def missing doc string -/

-- topology/uniform_space/basic.lean
#print uniform_continuous₂ /- def missing doc string -/
#print uniform_space.of_core /- def missing doc string -/
#print uniform_continuous /- def missing doc string -/
#print uniform_space.mk' /- def missing doc string -/
#print uniform_space.core.mk' /- def missing doc string -/
#print uniform_space.of_core_eq /- def missing doc string -/

-- topology/sheaves/stalks.lean
#print Top.presheaf.stalk_pushforward /- def missing doc string -/

-- topology/sheaves/presheaf.lean
#print Top.presheaf.pushforward_eq /- def missing doc string -/
#print Top.presheaf.pushforward.comp /- def missing doc string -/
#print Top.presheaf.pushforward /- def missing doc string -/
#print Top.presheaf.pushforward.id /- def missing doc string -/
#print Top.presheaf /- def missing doc string -/

-- topology/sequences.lean
#print is_seq_closed /- def missing doc string -/

-- topology/opens.lean
#print topological_space.opens.is_basis /- def missing doc string -/
#print topological_space.opens.interior /- def missing doc string -/
#print topological_space.opens.gi /- def missing doc string -/
#print continuous.comap /- def missing doc string -/

-- topology/metric_space/premetric_space.lean
#print premetric_space /- constant missing doc string -/

-- topology/metric_space/gromov_hausdorff_realized.lean
#print Gromov_Hausdorff.candidates_b_dist /- def missing doc string -/

-- topology/metric_space/gromov_hausdorff.lean
#print Gromov_Hausdorff.aux_gluing_struct /- constant missing doc string -/
#print Gromov_Hausdorff.aux_gluing /- def missing doc string -/
#print Gromov_Hausdorff.GH_dist /- def missing doc string -/

-- topology/metric_space/gluing.lean
#print metric.sum.dist /- def missing doc string -/
#print metric.to_glue_l /- def missing doc string -/
#print metric.to_glue_r /- def missing doc string -/
#print metric.glue_premetric /- def missing doc string -/
#print metric.glue_space /- def missing doc string -/

-- topology/metric_space/emetric_space.lean
#print has_edist /- constant missing doc string -/

-- topology/metric_space/basic.lean
#print metric_space.induced /- def missing doc string -/
#print metric_space.replace_uniformity /- def missing doc string -/

-- topology/maps.lean
#print is_closed_map /- def missing doc string -/
#print inducing /- constant missing doc string -/
#print is_open_map /- def missing doc string -/

-- topology/homeomorph.lean
#print homeomorph.trans /- def missing doc string -/
#print homeomorph.prod_comm /- def missing doc string -/
#print homeomorph.homeomorph_of_continuous_open /- def missing doc string -/
#print homeomorph.symm /- def missing doc string -/
#print homeomorph.sigma_prod_distrib /- def missing doc string -/
#print homeomorph.refl /- def missing doc string -/
#print homeomorph.prod_assoc /- def missing doc string -/
#print homeomorph.prod_congr /- def missing doc string -/

-- topology/compact_open.lean
#print continuous_map.coev /- def missing doc string -/
#print continuous_map.compact_open.gen /- def missing doc string -/
#print continuous_map.induced /- def missing doc string -/
#print continuous_map /- def missing doc string -/
#print continuous_map.ev /- def missing doc string -/

-- topology/category/UniformSpace.lean
#print CpltSepUniformSpace.to_UniformSpace /- def missing doc string -/

-- topology/category/Top/opens.lean
#print topological_space.opens.map_id /- def missing doc string -/
#print topological_space.opens.to_Top /- def missing doc string -/
#print topological_space.opens.map_iso /- def missing doc string -/
#print topological_space.opens.map_comp /- def missing doc string -/

-- topology/category/Top/open_nhds.lean
#print topological_space.open_nhds.inclusion_map_iso /- def missing doc string -/
#print topological_space.open_nhds /- def missing doc string -/
#print topological_space.open_nhds.map /- def missing doc string -/
#print topological_space.open_nhds.inclusion /- def missing doc string -/

-- topology/category/Top/limits.lean
#print Top.colimit_is_colimit /- def missing doc string -/
#print Top.limit /- def missing doc string -/
#print Top.limit_is_limit /- def missing doc string -/
#print Top.colimit /- def missing doc string -/

-- topology/bounded_continuous_function.lean
#print bounded_continuous_function.const /- def missing doc string -/

-- topology/algebra/uniform_ring.lean
#print uniform_space.sep_quot_equiv_ring_quot /- def missing doc string -/

-- topology/algebra/uniform_group.lean
#print topological_add_group.to_uniform_space /- def missing doc string -/
#print add_comm_group.is_Z_bilin /- constant missing doc string -/

-- topology/algebra/ring.lean
#print ideal.closure /- def missing doc string -/

-- topology/algebra/open_subgroup.lean
#print open_add_subgroup /- def missing doc string -/
#print open_subgroup.prod /- def missing doc string -/
#print open_add_subgroup.sum /- def missing doc string -/

-- topology/algebra/infinite_sum.lean
#print option.cases_on' /- def missing doc string -/

-- topology/algebra/group.lean
#print homeomorph.add_left /- def missing doc string -/
#print homeomorph.add_right /- def missing doc string -/
#print homeomorph.mul_left /- def missing doc string -/
#print homeomorph.mul_right /- def missing doc string -/
#print homeomorph.neg /- def missing doc string -/
#print homeomorph.inv /- def missing doc string -/

-- tactic/wlog.lean
#print tactic.wlog /- def missing doc string -/

-- tactic/where.lean
#print where.where_cmd /- def missing doc string -/
#print lean.parser.get_variables /- def missing doc string -/
#print where.trace_namespace /- def missing doc string -/
#print where.trace_variables /- def missing doc string -/
#print where.strip_namespace /- def missing doc string -/
#print where.mk_flag /- def missing doc string -/
#print where.sort_variable_list /- def missing doc string -/
#print where.trace_nl /- def missing doc string -/
#print where.collect_implicit_names /- def missing doc string -/
#print where.get_def_variables /- def missing doc string -/
#print where.get_includes_core /- def missing doc string -/
#print lean.parser.get_includes /- def missing doc string -/
#print where.trace_includes /- def missing doc string -/
#print where.get_namespace_core /- def missing doc string -/
#print where.strip_pi_binders /- def missing doc string -/
#print where.collect_by_aux /- def missing doc string -/
#print lean.parser.get_namespace /- def missing doc string -/
#print where.resolve_vars /- def missing doc string -/
#print where.trace_opens /- def missing doc string -/
#print where.find_var /- def missing doc string -/
#print where.get_opens /- def missing doc string -/
#print where.trace_end /- def missing doc string -/
#print where.get_variables_core /- def missing doc string -/
#print where.resolve_var /- def missing doc string -/
#print where.is_in_namespace_nonsynthetic /- def missing doc string -/
#print where.binder_priority /- def missing doc string -/
#print where.binder_less_important /- def missing doc string -/
#print where.trace_where /- def missing doc string -/
#print where.inflate /- def missing doc string -/
#print where.is_variable_name /- def missing doc string -/
#print where.fetch_potential_variable_names /- def missing doc string -/
#print where.resolve_vars_aux /- def missing doc string -/
#print where.format_variable /- def missing doc string -/
#print where.strip_pi_binders_aux /- def missing doc string -/
#print where.get_all_in_namespace /- def missing doc string -/
#print where.compile_variable_list /- def missing doc string -/
#print where.collect_by /- def missing doc string -/
#print where.select_for_which /- def missing doc string -/

-- tactic/transport.lean
#print tactic.transport_with_prefix_fun /- def missing doc string -/
#print tactic.transport_with_prefix_dict /- def missing doc string -/

-- tactic/transfer.lean
#print transfer.compute_transfer /- def missing doc string -/
#print transfer.analyse_decls /- def missing doc string -/
#print tactic.transfer /- def missing doc string -/

-- tactic/tidy.lean
#print tactic.tidy.ext1_wrapper /- def missing doc string -/
#print tactic.tidy.name_to_tactic /- def missing doc string -/
#print tactic.tidy_hole_cmd /- def missing doc string -/
#print tactic.tidy /- def missing doc string -/
#print tactic.tidy.default_tactics /- def missing doc string -/
#print tactic.tidy.cfg /- constant missing doc string -/
#print tactic.tidy.tidy_attribute /- def missing doc string -/
#print tactic.tidy.core /- def missing doc string -/
#print tactic.tidy.run_tactics /- def missing doc string -/

-- tactic/tfae.lean
#print tactic.tfae.mk_implication /- def missing doc string -/
#print tactic.interactive.parse_list /- def missing doc string -/
#print tactic.tfae.mk_name /- def missing doc string -/
#print tactic.tfae.arrow /- constant missing doc string -/

-- tactic/tauto.lean
#print tactic.tautology /- def missing doc string -/
#print tactic.symm_eq /- def missing doc string -/
#print tactic.root /- def missing doc string -/
#print tactic.assumption_symm /- def missing doc string -/
#print tactic.tauto_state /- def missing doc string -/
#print tactic.contradiction_with /- def missing doc string -/
#print tactic.add_symm_proof /- def missing doc string -/
#print tactic.add_edge /- def missing doc string -/
#print tactic.assumption_with /- def missing doc string -/
#print tactic.modify_ref /- def missing doc string -/
#print tactic.contradiction_symm /- def missing doc string -/
#print tactic.find_eq_type /- def missing doc string -/
#print tactic.add_refl /- def missing doc string -/

-- tactic/suggest.lean
#print tactic.library_search_hole_cmd /- def missing doc string -/
#print tactic.suggest.decl_data /- constant missing doc string -/

-- tactic/subtype_instance.lean
#print tactic.derive_field_subtype /- def missing doc string -/

-- tactic/squeeze.lean
#print tactic.interactive.record_lit /- def missing doc string -/
#print tactic.interactive.squeeze_simp /- def missing doc string -/
#print tactic.interactive.arg.to_tactic_format /- def missing doc string -/
#print tactic.interactive.erase_simp_arg /- def missing doc string -/
#print tactic.interactive.rec.to_tactic_format /- def missing doc string -/
#print tactic.interactive.squeeze_simpa /- def missing doc string -/
#print loc.to_string_aux /- def missing doc string -/
#print tactic.interactive.auto_simp_lemma /- def missing doc string -/
#print loc.to_string /- def missing doc string -/
#print tactic.interactive.parse_config /- def missing doc string -/

-- tactic/split_ifs.lean
#print tactic.find_if_cond_at /- def missing doc string -/
#print tactic.find_if_cond /- def missing doc string -/
#print tactic.split_ifs /- def missing doc string -/
#print tactic.split_if1 /- def missing doc string -/
#print tactic.reduce_ifs_at /- def missing doc string -/

-- tactic/slice.lean
#print conv.repeat_with_results /- def missing doc string -/
#print conv.slice /- def missing doc string -/
#print conv.slice_lhs /- def missing doc string -/
#print conv.slice_rhs /- def missing doc string -/
#print tactic.repeat_count /- def missing doc string -/
#print tactic.repeat_with_results /- def missing doc string -/
#print conv.repeat_count /- def missing doc string -/

-- tactic/scc.lean
#print tactic.prove_eqv_target /- def missing doc string -/

-- tactic/ring2.lean
#print tactic.ring2.horner_expr.inv /- def missing doc string -/
#print tactic.ring2.horner_expr.mul /- def missing doc string -/
#print tactic.ring2.horner_expr.to_string /- def missing doc string -/
#print tactic.ring2.horner_expr.mul_aux /- def missing doc string -/
#print conv.interactive.ring2 /- def missing doc string -/
#print tactic.ring2.horner_expr.pow /- def missing doc string -/
#print tactic.ring2.horner_expr.add /- def missing doc string -/
#print tactic.ring2.horner_expr.neg /- def missing doc string -/
#print tactic.ring2.horner_expr.add_aux /- def missing doc string -/
#print tactic.ring2.horner_expr.add_const /- def missing doc string -/
#print tactic.ring2.horner_expr.mul_const /- def missing doc string -/

-- tactic/ring.lean
#print tactic.ring.normalize_mode /- constant missing doc string -/
#print tactic.ring.eval_mul /- def missing doc string -/
#print tactic.ring.add_atom /- def missing doc string -/
#print tactic.ring.horner /- def missing doc string -/
#print tactic.ring.horner_expr.refl_conv /- def missing doc string -/
#print tactic.ring.horner_expr.to_string /- def missing doc string -/
#print tactic.ring.eval_pow /- def missing doc string -/
#print tactic.interactive.ring.mode /- def missing doc string -/
#print tactic.ring.eval_const_mul /- def missing doc string -/
#print tactic.ring.normalize /- def missing doc string -/
#print tactic.ring.ring_m.mk_app /- def missing doc string -/
#print tactic.ring.cache /- constant missing doc string -/
#print tactic.ring.eval /- def missing doc string -/
#print tactic.ring.eval_add /- def missing doc string -/
#print tactic.ring.ring_m.run /- def missing doc string -/
#print tactic.ring.horner_expr /- constant missing doc string -/
#print tactic.ring.get_atom /- def missing doc string -/
#print tactic.ring.cache.cs_app /- def missing doc string -/
#print tactic.ring.get_cache /- def missing doc string -/
#print tactic.ring.get_transparency /- def missing doc string -/
#print tactic.ring.ring_m /- def missing doc string -/
#print tactic.ring.horner_expr.pp /- def missing doc string -/
#print tactic.ring.horner_expr.e /- def missing doc string -/
#print tactic.ring.eval' /- def missing doc string -/
#print tactic.ring.lift /- def missing doc string -/
#print tactic.ring.eval_neg /- def missing doc string -/
#print conv.interactive.ring /- def missing doc string -/
#print tactic.ring.eval_horner /- def missing doc string -/
#print tactic.ring.horner_expr.xadd' /- def missing doc string -/
#print tactic.ring.eval_atom /- def missing doc string -/

-- tactic/rewrite_all/default.lean
#print tactic.all_rewrites_using /- def missing doc string -/
#print tactic.perform_nth_rewrite /- def missing doc string -/
#print tactic.get_nth_rewrite /- def missing doc string -/

-- tactic/rewrite_all/congr.lean
#print tactic.rewrite_all.congr.expr_lens.to_tactic_string /- def missing doc string -/
#print tactic.rewrite_all.congr.expr_lens.to_sides /- def missing doc string -/
#print tactic.rewrite_all.congr.app_map /- def missing doc string -/
#print tactic.rewrite_all.congr.rewrite_all_lazy /- def missing doc string -/
#print tactic.rewrite_all.congr.expr_lens /- constant missing doc string -/
#print tactic.rewrite_all.congr.rewrite_is_of_entire /- def missing doc string -/
#print tactic.rewrite_all.congr.rewrite_without_new_mvars /- def missing doc string -/
#print tactic.rewrite_all.congr.rewrite_all /- def missing doc string -/
#print tactic.rewrite_all.congr.rewrite_at_lens /- def missing doc string -/
#print tactic.rewrite_all.congr.expr_lens.replace /- def missing doc string -/
#print tactic.mk_congr_arg_using_dsimp' /- def missing doc string -/
#print tactic.rewrite_all.congr.expr_lens.congr /- def missing doc string -/

-- tactic/rewrite_all/basic.lean
#print side /- constant missing doc string -/
#print tactic.rewrite_all.tracked_rewrite.replace_target_rhs /- def missing doc string -/
#print tactic.rewrite_all.tracked_rewrite.replace_target_lhs /- def missing doc string -/
#print tactic.rewrite_all.cfg /- constant missing doc string -/
#print tactic.rewrite_all.tracked_rewrite /- constant missing doc string -/
#print tactic.rewrite_all.tracked_rewrite.eval /- def missing doc string -/
#print side.other /- def missing doc string -/
#print side.to_string /- def missing doc string -/
#print tactic.rewrite_all.tracked_rewrite.replace_target /- def missing doc string -/

-- tactic/rewrite.lean
#print tactic.mk_assoc_pattern' /- def missing doc string -/
#print tactic.assoc_refl /- def missing doc string -/
#print tactic.assoc_rewrite_intl /- def missing doc string -/
#print tactic.match_assoc_pattern /- def missing doc string -/
#print tactic.assoc_root /- def missing doc string -/
#print tactic.match_assoc_pattern' /- def missing doc string -/
#print tactic.enum_assoc_subexpr /- def missing doc string -/
#print tactic.assoc_refl' /- def missing doc string -/
#print tactic.fill_args /- def missing doc string -/
#print tactic.mk_assoc_pattern /- def missing doc string -/
#print tactic.enum_assoc_subexpr' /- def missing doc string -/
#print tactic.assoc_rewrite /- def missing doc string -/
#print tactic.assoc_rewrite_hyp /- def missing doc string -/
#print tactic.mk_assoc /- def missing doc string -/
#print tactic.mk_assoc_instance /- def missing doc string -/
#print tactic.chain_eq_trans /- def missing doc string -/
#print tactic.flatten /- def missing doc string -/
#print tactic.unify_prefix /- def missing doc string -/
#print tactic.mk_eq_proof /- def missing doc string -/
#print tactic.assoc_rewrite_target /- def missing doc string -/
#print tactic.match_fn /- def missing doc string -/

-- tactic/restate_axiom.lean
#print restate_axiom_cmd /- def missing doc string -/

-- tactic/replacer.lean
#print tactic.replacer /- def missing doc string -/
#print tactic.unprime /- def missing doc string -/
#print tactic.mk_replacer₂ /- def missing doc string -/
#print tactic.mk_replacer /- def missing doc string -/
#print tactic.replacer_core /- def missing doc string -/
#print tactic.replaceable_attr /- def missing doc string -/
#print tactic.mk_replacer₁ /- def missing doc string -/
#print tactic.replacer_attr /- def missing doc string -/
#print tactic.valid_types /- def missing doc string -/

-- tactic/reassoc_axiom.lean
#print tactic.calculated_Prop /- def missing doc string -/
#print tactic.derive_reassoc_proof /- def missing doc string -/

-- tactic/rcases.lean
#print tactic.rcases.process_constructors /- def missing doc string -/
#print tactic.rintro_hint /- def missing doc string -/
#print tactic.rcases_hint.process_constructors /- def missing doc string -/
#print tactic.rcases_hint /- def missing doc string -/
#print tactic.rcases_patt.format /- def missing doc string -/
#print tactic.rcases_patt.merge /- def missing doc string -/
#print tactic.rcases_patt_inverted.format_list /- def missing doc string -/
#print tactic.rcases_patt.name /- def missing doc string -/
#print tactic.rcases_patt /- constant missing doc string -/
#print tactic.ext_parse /- def missing doc string -/
#print tactic.rintro_parse /- def missing doc string -/
#print tactic.rcases_patt.invert_many /- def missing doc string -/
#print tactic.rintro /- def missing doc string -/
#print tactic.interactive.obtain_parse /- def missing doc string -/
#print tactic.rcases_hint_core /- def missing doc string -/
#print tactic.rcases_parse_depth /- def missing doc string -/
#print tactic.merge_list /- def missing doc string -/
#print tactic.rcases_hint.continue /- def missing doc string -/
#print tactic.rcases_patt_inverted.format /- def missing doc string -/
#print tactic.rcases_patt.invert /- def missing doc string -/
#print tactic.rcases_patt_parse /- def missing doc string -/
#print tactic.goals /- def missing doc string -/
#print tactic.rcases.continue /- def missing doc string -/
#print tactic.rcases_patt_inverted.invert /- def missing doc string -/
#print tactic.rcases_patt.invert_list /- def missing doc string -/
#print tactic.list_Sigma /- def missing doc string -/
#print tactic.ext_patt /- def missing doc string -/
#print tactic.rcases_patt_parse_core /- def missing doc string -/
#print tactic.rcases_patt.invert' /- def missing doc string -/
#print tactic.rcases_patt_inverted.invert_list /- def missing doc string -/
#print tactic.rcases_core /- def missing doc string -/
#print tactic.list_Pi /- def missing doc string -/
#print tactic.rcases_patt_parse_list /- def missing doc string -/

-- tactic/push_neg.lean
#print push_neg.normalize_negations /- def missing doc string -/
#print push_neg.whnf_reducible /- def missing doc string -/
#print push_neg.push_neg_at_goal /- def missing doc string -/
#print push_neg.push_neg_at_hyp /- def missing doc string -/

-- tactic/pi_instances.lean
#print tactic.derive_field /- def missing doc string -/
#print tactic.interactive.pi_instance /- def missing doc string -/

-- tactic/omega/term.lean
#print omega.term.mul /- def missing doc string -/
#print omega.term.add /- def missing doc string -/
#print omega.term.fresh_index /- def missing doc string -/
#print omega.term.div /- def missing doc string -/
#print omega.term.neg /- def missing doc string -/
#print omega.term.val /- def missing doc string -/
#print omega.term.sub /- def missing doc string -/
#print omega.term.to_string /- def missing doc string -/
#print omega.terms.fresh_index /- def missing doc string -/
#print omega.term /- def missing doc string -/

-- tactic/omega/prove_unsats.lean
#print omega.prove_unsat_ef /- def missing doc string -/
#print omega.prove_neg /- def missing doc string -/
#print omega.prove_unsats /- def missing doc string -/
#print omega.prove_forall_mem_eq_zero /- def missing doc string -/
#print omega.prove_unsat_lin_comb /- def missing doc string -/
#print omega.prove_unsat /- def missing doc string -/

-- tactic/omega/nat/sub_elim.lean
#print omega.nat.preterm.sub_subst /- def missing doc string -/
#print omega.nat.is_diff /- def missing doc string -/
#print omega.nat.preterm.sub_terms /- def missing doc string -/
#print omega.nat.form.sub_terms /- def missing doc string -/
#print omega.nat.form.sub_subst /- def missing doc string -/
#print omega.nat.sub_fresh_index /- def missing doc string -/
#print omega.nat.sub_elim_core /- def missing doc string -/
#print omega.nat.sub_elim /- def missing doc string -/

-- tactic/omega/nat/preterm.lean
#print omega.nat.canonize /- def missing doc string -/
#print omega.nat.preterm.add_one /- def missing doc string -/
#print omega.nat.preterm.induce /- def missing doc string -/
#print omega.nat.preterm.sub_free /- def missing doc string -/
#print omega.nat.preterm.val /- def missing doc string -/
#print omega.nat.preterm.repr /- def missing doc string -/
#print omega.nat.preterm.fresh_index /- def missing doc string -/
#print omega.nat.preterm /- constant missing doc string -/

-- tactic/omega/nat/neg_elim.lean
#print omega.nat.nnf /- def missing doc string -/
#print omega.nat.neg_elim /- def missing doc string -/
#print omega.nat.neg_elim_core /- def missing doc string -/
#print omega.nat.push_neg /- def missing doc string -/
#print omega.nat.is_nnf /- def missing doc string -/

-- tactic/omega/nat/main.lean
#print omega.nat.prove_unsat_sub_free /- def missing doc string -/
#print omega.nat.to_preterm /- def missing doc string -/
#print omega.nat.to_form_core /- def missing doc string -/
#print omega.nat.prove_neg_free /- def missing doc string -/
#print omega.nat.prove_univ_close /- def missing doc string -/
#print omega.nat.prove_lna /- def missing doc string -/
#print omega.nat.preterm.prove_sub_free /- def missing doc string -/
#print omega_nat /- def missing doc string -/
#print omega.nat.prove_sub_free /- def missing doc string -/
#print omega.nat.desugar /- def missing doc string -/
#print omega.nat.to_form /- def missing doc string -/
#print omega.nat.prove_unsat_neg_free /- def missing doc string -/

-- tactic/omega/nat/form.lean
#print omega.nat.form.holds /- def missing doc string -/
#print omega.nat.form.unsat /- def missing doc string -/
#print omega.nat.form.sub_free /- def missing doc string -/
#print omega.nat.form /- constant missing doc string -/
#print omega.nat.form.implies /- def missing doc string -/
#print omega.nat.form.equiv /- def missing doc string -/
#print omega.nat.form.repr /- def missing doc string -/
#print omega.nat.form.neg_free /- def missing doc string -/
#print omega.nat.form.induce /- def missing doc string -/
#print omega.nat.form.fresh_index /- def missing doc string -/
#print omega.nat.univ_close /- def missing doc string -/
#print omega.nat.form.valid /- def missing doc string -/
#print omega.nat.form.sat /- def missing doc string -/

-- tactic/omega/nat/dnf.lean
#print omega.nat.dnf_core /- def missing doc string -/
#print omega.nat.nonneg_consts /- def missing doc string -/
#print omega.nat.term.vars /- def missing doc string -/
#print omega.nat.term.vars_core /- def missing doc string -/
#print omega.nat.terms.vars /- def missing doc string -/
#print omega.nat.dnf /- def missing doc string -/
#print omega.nat.nonneg_consts_core /- def missing doc string -/
#print omega.nat.bools.or /- def missing doc string -/
#print omega.nat.nonnegate /- def missing doc string -/

-- tactic/omega/misc.lean
#print omega.update_zero /- def missing doc string -/
#print omega.update /- def missing doc string -/

-- tactic/omega/main.lean
#print omega.is_lna_term /- def missing doc string -/
#print omega.is_lia_form /- def missing doc string -/
#print omega.preprocess /- def missing doc string -/
#print omega.goal_domain /- def missing doc string -/
#print omega.clear_unused_hyps /- def missing doc string -/
#print omega.clear_unused_hyp /- def missing doc string -/
#print omega.rev_lna /- def missing doc string -/
#print omega.rev_lia /- def missing doc string -/
#print omega.revert_cond_all /- def missing doc string -/
#print omega.form_wf /- def missing doc string -/
#print omega.term_domain /- def missing doc string -/
#print omega.type_domain /- def missing doc string -/
#print omega.form_domain /- def missing doc string -/
#print omega.goal_domain_aux /- def missing doc string -/
#print omega.select_domain /- def missing doc string -/
#print omega.is_lna_form /- def missing doc string -/
#print omega.revert_cond /- def missing doc string -/
#print omega.is_lia_term /- def missing doc string -/

-- tactic/omega/lin_comb.lean
#print omega.lin_comb /- def missing doc string -/
#print omega.unsat_lin_comb /- def missing doc string -/

-- tactic/omega/int/preterm.lean
#print omega.int.preterm.val /- def missing doc string -/
#print omega.int.canonize /- def missing doc string -/
#print omega.int.preterm.add_one /- def missing doc string -/
#print omega.int.preterm /- constant missing doc string -/
#print omega.int.preterm.repr /- def missing doc string -/
#print omega.int.preterm.fresh_index /- def missing doc string -/

-- tactic/omega/int/main.lean
#print omega.int.to_form /- def missing doc string -/
#print omega.int.desugar /- def missing doc string -/
#print omega.int.to_preterm /- def missing doc string -/
#print omega.int.to_form_core /- def missing doc string -/
#print omega.int.prove_univ_close /- def missing doc string -/
#print omega.int.prove_lia /- def missing doc string -/
#print omega_int /- def missing doc string -/

-- tactic/omega/int/form.lean
#print omega.int.form.sat /- def missing doc string -/
#print omega.int.form.implies /- def missing doc string -/
#print omega.int.univ_close /- def missing doc string -/
#print omega.int.form.induce /- def missing doc string -/
#print omega.int.form.fresh_index /- def missing doc string -/
#print omega.int.form.holds /- def missing doc string -/
#print omega.int.form.repr /- def missing doc string -/
#print omega.int.form /- constant missing doc string -/
#print omega.int.form.unsat /- def missing doc string -/
#print omega.int.form.equiv /- def missing doc string -/
#print omega.int.form.valid /- def missing doc string -/

-- tactic/omega/int/dnf.lean
#print omega.int.nnf /- def missing doc string -/
#print omega.int.push_neg /- def missing doc string -/
#print omega.int.neg_free /- def missing doc string -/
#print omega.int.dnf_core /- def missing doc string -/
#print omega.int.is_nnf /- def missing doc string -/
#print omega.int.neg_elim /- def missing doc string -/
#print omega.int.dnf /- def missing doc string -/

-- tactic/omega/find_scalars.lean
#print omega.elim_var /- def missing doc string -/
#print omega.trisect /- def missing doc string -/
#print omega.elim_var_aux /- def missing doc string -/
#print omega.find_neg_const /- def missing doc string -/
#print omega.find_scalars /- def missing doc string -/
#print omega.find_scalars_core /- def missing doc string -/

-- tactic/omega/find_ees.lean
#print omega.elim_eqs /- def missing doc string -/
#print omega.add_ee /- def missing doc string -/
#print omega.ee_commit /- def missing doc string -/
#print omega.find_min_coeff_core /- def missing doc string -/
#print omega.get_eqs /- def missing doc string -/
#print omega.eqelim /- def missing doc string -/
#print omega.factor /- def missing doc string -/
#print omega.set_ees /- def missing doc string -/
#print omega.find_ees /- def missing doc string -/
#print omega.run /- def missing doc string -/
#print omega.elim_eq /- def missing doc string -/
#print omega.ee_state /- constant missing doc string -/
#print omega.get_les /- def missing doc string -/
#print omega.set_eqs /- def missing doc string -/
#print omega.abort /- def missing doc string -/
#print omega.gcd /- def missing doc string -/
#print omega.get_gcd /- def missing doc string -/
#print omega.get_ees /- def missing doc string -/
#print omega.set_les /- def missing doc string -/
#print omega.find_min_coeff /- def missing doc string -/
#print omega.head_eq /- def missing doc string -/

-- tactic/omega/eq_elim.lean
#print omega.sym_sym /- def missing doc string -/
#print omega.symdiv /- def missing doc string -/
#print omega.cancel /- def missing doc string -/
#print omega.coeffs_reduce /- def missing doc string -/
#print omega.sgm /- def missing doc string -/
#print omega.rhs /- def missing doc string -/
#print omega.eq_elim /- def missing doc string -/
#print omega.subst /- def missing doc string -/
#print omega.ee.repr /- def missing doc string -/
#print omega.symmod /- def missing doc string -/
#print omega.ee /- constant missing doc string -/

-- tactic/omega/coeffs.lean
#print omega.coeffs.val_except /- def missing doc string -/
#print omega.coeffs.val_between /- def missing doc string -/
#print omega.coeffs.val /- def missing doc string -/

-- tactic/omega/clause.lean
#print omega.clause /- def missing doc string -/
#print omega.clauses.unsat /- def missing doc string -/
#print omega.clause.sat /- def missing doc string -/
#print omega.clause.unsat /- def missing doc string -/
#print omega.clause.holds /- def missing doc string -/
#print omega.clauses.sat /- def missing doc string -/
#print omega.clause.append /- def missing doc string -/

-- tactic/norm_num.lean
#print tactic.refl_conv /- def missing doc string -/
#print norm_num.eval_pow /- def missing doc string -/
#print norm_num.prove_non_prime /- def missing doc string -/
#print norm_num.eval_ineq /- def missing doc string -/
#print norm_num.prove_lt /- def missing doc string -/
#print norm_num.prove_pos /- def missing doc string -/
#print norm_num.eval_div_ext /- def missing doc string -/
#print conv.interactive.norm_num /- def missing doc string -/
#print tactic.interactive.apply_normed /- def missing doc string -/
#print norm_num.derive1 /- def missing doc string -/
#print norm_num.derive /- def missing doc string -/
#print norm_num.prove_min_fac /- def missing doc string -/
#print tactic.trans_conv /- def missing doc string -/
#print norm_num.min_fac_helper /- def missing doc string -/
#print norm_num.eval_prime /- def missing doc string -/
#print conv.interactive.norm_num1 /- def missing doc string -/

-- tactic/norm_cast.lean
#print norm_cast.test_result.to_string /- def missing doc string -/
#print norm_cast.test_result /- constant missing doc string -/
#print norm_cast.get_second /- def missing doc string -/
#print norm_cast.aux /- def missing doc string -/
#print norm_cast.make_guess /- def missing doc string -/
#print norm_cast.label.of_string /- def missing doc string -/
#print norm_cast.get_label /- def missing doc string -/
#print conv.interactive.norm_cast /- def missing doc string -/
#print norm_cast.test_classifiers /- def missing doc string -/
#print norm_cast.label.to_string /- def missing doc string -/
#print norm_cast.test_cache /- constant missing doc string -/
#print norm_cast.get_first /- def missing doc string -/
#print norm_cast.get_decl /- def missing doc string -/
#print norm_cast.test_decl /- def missing doc string -/

-- tactic/monotonicity/interactive.lean
#print tactic.interactive.ac_refine /- def missing doc string -/
#print tactic.interactive.find_rule /- def missing doc string -/
#print tactic.interactive.mk_fun_app /- def missing doc string -/
#print tactic.interactive.fold_assoc /- def missing doc string -/
#print tactic.interactive.find_lemma /- def missing doc string -/
#print tactic.interactive.hide_meta_vars' /- def missing doc string -/
#print tactic.interactive.side_conditions /- def missing doc string -/
#print tactic.interactive.assert_or_rule /- def missing doc string -/
#print tactic.interactive.pi_head /- def missing doc string -/
#print tactic.interactive.parse_ac_mono_function' /- def missing doc string -/
#print tactic.interactive.delete_expr /- def missing doc string -/
#print tactic.interactive.unify_with_instance /- def missing doc string -/
#print tactic.interactive.check_ac /- def missing doc string -/
#print tactic.interactive.match_prefix /- def missing doc string -/
#print tactic.interactive.as_goal /- def missing doc string -/
#print tactic.interactive.mk_pattern /- def missing doc string -/
#print tactic.interactive.ac_mono_ctx'.traverse /- def missing doc string -/
#print tactic.interactive.parse_assoc_chain' /- def missing doc string -/
#print tactic.interactive.parse_assoc_chain /- def missing doc string -/
#print tactic.interactive.mk_congr_args /- def missing doc string -/
#print tactic.interactive.parse_ac_mono_function /- def missing doc string -/
#print tactic.interactive.match_ac' /- def missing doc string -/
#print tactic.interactive.ac_mono_ctx_ne /- def missing doc string -/
#print tactic.interactive.match_rule /- def missing doc string -/
#print tactic.interactive.bin_op_left /- def missing doc string -/
#print tactic.interactive.mono_aux /- def missing doc string -/
#print tactic.interactive.mono_function.to_tactic_format /- def missing doc string -/
#print tactic.interactive.rep_arity /- constant missing doc string -/
#print tactic.interactive.bin_op /- def missing doc string -/
#print tactic.interactive.mono_law.to_tactic_format /- def missing doc string -/
#print tactic.interactive.apply_rel /- def missing doc string -/
#print tactic.interactive.repeat_until /- def missing doc string -/
#print tactic.interactive.list.minimum_on /- def missing doc string -/
#print tactic.interactive.solve_mvar /- def missing doc string -/
#print tactic.interactive.mk_congr_law /- def missing doc string -/
#print tactic.interactive.match_chaining_rules /- def missing doc string -/
#print tactic.interactive.match_ac /- def missing doc string -/
#print tactic.interactive.mono_law /- constant missing doc string -/
#print tactic.interactive.ac_mono_ctx.to_tactic_format /- def missing doc string -/
#print tactic.interactive.same_function_aux /- def missing doc string -/
#print tactic.interactive.best_match /- def missing doc string -/
#print tactic.interactive.ac_mono_ctx'.map /- def missing doc string -/
#print tactic.interactive.repeat_or_not /- def missing doc string -/
#print tactic.interactive.ac_monotonicity_goal /- def missing doc string -/
#print tactic.interactive.ac_mono_ctx /- def missing doc string -/
#print tactic.interactive.ac_mono_ctx' /- constant missing doc string -/
#print tactic.interactive.one_line /- def missing doc string -/
#print tactic.interactive.mk_rel /- def missing doc string -/
#print tactic.interactive.arity /- def missing doc string -/
#print tactic.interactive.mono_function /- constant missing doc string -/
#print tactic.interactive.fold_assoc1 /- def missing doc string -/
#print tactic.interactive.bin_op_right /- def missing doc string -/
#print tactic.interactive.same_function /- def missing doc string -/

-- tactic/monotonicity/basic.lean
#print tactic.interactive.monotonicity.attr /- def missing doc string -/
#print tactic.interactive.monotoncity.check /- def missing doc string -/
#print tactic.interactive.filter_instances /- def missing doc string -/
#print tactic.interactive.monotoncity.check_rel /- def missing doc string -/
#print tactic.interactive.mono_key /- def missing doc string -/
#print tactic.interactive.find_one_difference /- def missing doc string -/
#print tactic.interactive.get_operator /- def missing doc string -/
#print tactic.interactive.mono_head_candidates /- def missing doc string -/
#print tactic.interactive.compare /- def missing doc string -/
#print tactic.interactive.side /- def missing doc string -/
#print tactic.interactive.mono_cfg /- constant missing doc string -/
#print tactic.interactive.same_operator /- def missing doc string -/
#print tactic.interactive.get_monotonicity_lemmas /- def missing doc string -/
#print tactic.interactive.match_imp /- def missing doc string -/
#print tactic.interactive.mono_selection /- constant missing doc string -/
#print tactic.interactive.last_two /- def missing doc string -/

-- tactic/mk_iff_of_inductive_prop.lean
#print tactic.mk_iff /- def missing doc string -/
#print tactic.constr_to_prop /- def missing doc string -/
#print tactic.select /- def missing doc string -/

-- tactic/localized.lean
#print localized_attr /- def missing doc string -/

-- tactic/local_cache.lean
#print tactic.local_cache.internal.def_local.hash_context /- def missing doc string -/
#print tactic.local_cache.internal.save_data /- def missing doc string -/
#print tactic.local_cache.internal.def_local.get_root_name /- def missing doc string -/
#print tactic.local_cache.internal.def_local.try_get_name /- def missing doc string -/
#print tactic.local_cache.internal.def_local.mk_dead_name /- def missing doc string -/
#print tactic.local_cache.internal.cache_scope /- constant missing doc string -/
#print tactic.local_cache.internal.def_local.hash_string /- def missing doc string -/
#print tactic.local_cache.internal.run_once_under_name /- def missing doc string -/
#print tactic.local_cache.internal.def_local.apply_tag /- def missing doc string -/
#print tactic.local_cache.internal.def_local.FNV_PRIME /- def missing doc string -/
#print tactic.local_cache.internal.block_local.clear /- def missing doc string -/
#print tactic.local_cache.internal.def_local.FNV_OFFSET_BASIS /- def missing doc string -/
#print tactic.local_cache.internal.def_local.hash_byte /- def missing doc string -/
#print tactic.local_cache.internal.block_local.present /- def missing doc string -/
#print tactic.local_cache.internal.def_local.is_name_dead /- def missing doc string -/
#print tactic.local_cache.internal.def_local.present /- def missing doc string -/
#print tactic.local_cache.internal.def_local.kill_name /- def missing doc string -/
#print tactic.local_cache.internal.def_local.RADIX /- def missing doc string -/
#print tactic.local_cache.internal.def_local.get_name /- def missing doc string -/
#print tactic.local_cache.internal.def_local.get_tag_with_status /- def missing doc string -/
#print tactic.local_cache.internal.block_local.try_get_name /- def missing doc string -/
#print tactic.local_cache.internal.poke_data /- def missing doc string -/
#print tactic.local_cache.internal.def_local.clear /- def missing doc string -/
#print tactic.local_cache.internal.mk_full_namespace /- def missing doc string -/
#print tactic.local_cache.internal.load_data /- def missing doc string -/
#print tactic.local_cache.internal.block_local.get_name /- def missing doc string -/

-- tactic/linarith.lean
#print linarith.replace_strict_int_pfs /- def missing doc string -/
#print linarith.parse_into_comp_and_expr /- def missing doc string -/
#print linarith.comp.scale /- def missing doc string -/
#print linarith.mk_lt_zero_pf_aux /- def missing doc string -/
#print linarith.pcomp /- constant missing doc string -/
#print linarith.comp_source /- constant missing doc string -/
#print linarith.mk_single_comp_zero_pf /- def missing doc string -/
#print linarith.rb_map.find_defeq /- def missing doc string -/
#print linarith.get_nat_comps /- def missing doc string -/
#print linarith.comp.is_contr /- def missing doc string -/
#print linarith.replace_nat_pfs /- def missing doc string -/
#print linarith.elab_arg_list /- def missing doc string -/
#print linarith.to_comp_fold /- def missing doc string -/
#print linarith.add_exprs_aux /- def missing doc string -/
#print linarith.ineq /- constant missing doc string -/
#print linarith.pcomp.scale /- def missing doc string -/
#print linarith.add_neg_eq_pfs /- def missing doc string -/
#print linarith.elim_all_vars /- def missing doc string -/
#print linarith.guard_is_strict_int_prop /- def missing doc string -/
#print linarith.pcomp.add /- def missing doc string -/
#print linarith.ineq_const_nm /- def missing doc string -/
#print linarith.get_rel_sides /- def missing doc string -/
#print linarith.is_numeric /- def missing doc string -/
#print linarith.linarith_config /- constant missing doc string -/
#print linarith.linarith_monad.run /- def missing doc string -/
#print linarith.get_var_list /- def missing doc string -/
#print nat.to_pexpr /- def missing doc string -/
#print linarith.pelim_var /- def missing doc string -/
#print linarith.get_vars /- def missing doc string -/
#print linarith.guard_is_nat_prop /- def missing doc string -/
#print linarith.get_comps /- def missing doc string -/
#print linarith.comp.add /- def missing doc string -/
#print linarith.mk_cast_eq_and_nonneg_prfs /- def missing doc string -/
#print linarith.find_contr /- def missing doc string -/
#print linarith.pcomp.is_contr /- def missing doc string -/
#print linarith.mk_coe_nat_nonneg_prfs /- def missing doc string -/
#print linarith.linarith_monad /- def missing doc string -/
#print linarith.validate /- def missing doc string -/
#print linarith.cast_expr /- def missing doc string -/
#print linarith.map_of_expr_mul_aux /- def missing doc string -/
#print linarith.norm_hyp /- def missing doc string -/
#print linarith.rem_neg /- def missing doc string -/
#print linarith.elim_with_set /- def missing doc string -/
#print linarith.update /- def missing doc string -/
#print linarith.norm_hyp_aux /- def missing doc string -/
#print linarith.comp.coeff_of /- def missing doc string -/
#print linarith.to_comp /- def missing doc string -/
#print linarith.ineq.is_lt /- def missing doc string -/
#print linarith.partition_by_type /- def missing doc string -/
#print linarith.mul_expr /- def missing doc string -/
#print linarith.preferred_type_of_goal /- def missing doc string -/
#print linarith.is_nat_int_coe /- def missing doc string -/
#print linarith.mk_non_strict_int_pf_of_strict_int_pf /- def missing doc string -/
#print linarith.ineq.to_string /- def missing doc string -/
#print linarith.monad.elim_var /- def missing doc string -/
#print linarith.comp_source.to_string /- def missing doc string -/
#print linarith.ineq_pf_tp /- def missing doc string -/
#print linarith.comp.lt /- def missing doc string -/
#print linarith.mk_neg_one_lt_zero_pf /- def missing doc string -/
#print linarith.get_contr_lemma_name /- def missing doc string -/
#print linarith.mk_prod_prf /- def missing doc string -/
#print linarith.ineq.max /- def missing doc string -/
#print linarith.term_of_ineq_prf /- def missing doc string -/
#print linarith.expr_contains /- def missing doc string -/
#print linarith.comp_source.flatten /- def missing doc string -/
#print linarith.find_cancel_factor /- def missing doc string -/
#print linarith.partition_by_type_aux /- def missing doc string -/
#print linarith.add_exprs /- def missing doc string -/
#print linarith.ineq_const_mul_nm /- def missing doc string -/
#print linarith.mk_coe_nat_nonneg_prf /- def missing doc string -/
#print linarith.list.mfind /- def missing doc string -/
#print linarith.map_lt /- def missing doc string -/
#print linarith.rearr_comp /- def missing doc string -/
#print linarith.mk_int_pfs_of_nat_pf /- def missing doc string -/

-- tactic/lift.lean
#print can_lift_attr /- def missing doc string -/
#print tactic.to_texpr /- def missing doc string -/
#print tactic.using_texpr /- def missing doc string -/
#print tactic.get_lift_prf /- def missing doc string -/

-- tactic/interactive.lean
#print tactic.interactive.format_names /- def missing doc string -/
#print tactic.interactive.loc.get_local_pp_names /- def missing doc string -/
#print tactic.interactive.guard_tags /- def missing doc string -/
#print tactic.interactive.apply_iff_congr_core /- def missing doc string -/
#print tactic.interactive.convert_to_core /- def missing doc string -/
#print tactic.interactive.congr_core' /- def missing doc string -/
#print tactic.interactive.guard_hyp_nums /- def missing doc string -/
#print tactic.interactive.mk_paragraph_aux /- def missing doc string -/
#print tactic.interactive.collect_struct' /- def missing doc string -/
#print tactic.interactive.compact_decl_aux /- def missing doc string -/
#print tactic.interactive.loc.get_local_uniq_names /- def missing doc string -/
#print tactic.interactive.return_cast /- def missing doc string -/
#print tactic.interactive.refine_recursively /- def missing doc string -/
#print tactic.interactive.list_cast_of /- def missing doc string -/
#print tactic.interactive.refine_one /- def missing doc string -/
#print tactic.interactive.guard_expr_eq' /- def missing doc string -/
#print tactic.interactive.field /- def missing doc string -/
#print tactic.interactive.list_cast_of_aux /- def missing doc string -/
#print tactic.interactive.get_current_field /- def missing doc string -/
#print tactic.interactive.source_fields /- def missing doc string -/
#print tactic.interactive.collect_struct /- def missing doc string -/
#print tactic.interactive.compact_decl /- def missing doc string -/
#print tactic.interactive.clean_ids /- def missing doc string -/

-- tactic/generalize_proofs.lean
#print tactic.generalize_proofs /- def missing doc string -/

-- tactic/finish.lean
#print auto.do_subst /- def missing doc string -/
#print auto.do_substs /- def missing doc string -/
#print auto.eelims /- def missing doc string -/
#print auto.add_conjuncts /- def missing doc string -/
#print auto.whnf_reducible /- def missing doc string -/
#print auto.case_some_hyp /- def missing doc string -/
#print auto.preprocess_goal /- def missing doc string -/
#print auto.common_normalize_lemma_names /- def missing doc string -/
#print auto.mk_hinst_lemmas /- def missing doc string -/
#print auto.case_option /- constant missing doc string -/
#print auto.normalize_negations /- def missing doc string -/
#print auto.normalize_hyps /- def missing doc string -/
#print auto.add_simps /- def missing doc string -/
#print tactic.assertv_fresh /- def missing doc string -/
#print tactic.assert_fresh /- def missing doc string -/
#print auto.split_hyp /- def missing doc string -/
#print auto.classical_normalize_lemma_names /- def missing doc string -/
#print auto.normalize_hyp /- def missing doc string -/
#print auto.split_hyps /- def missing doc string -/
#print tactic.interactive.revert_all /- def missing doc string -/
#print auto.eelim /- def missing doc string -/
#print auto.preprocess_hyps /- def missing doc string -/
#print auto.auto_config /- constant missing doc string -/
#print auto.split_hyps_aux /- def missing doc string -/
#print auto.case_hyp /- def missing doc string -/
#print auto.case_some_hyp_aux /- def missing doc string -/

-- tactic/find.lean
#print pexpr.get_uninst_pis /- def missing doc string -/
#print expr.get_pis /- def missing doc string -/
#print find_cmd /- def missing doc string -/

-- tactic/fin_cases.lean
#print tactic.fin_cases_at_aux /- def missing doc string -/
#print tactic.fin_cases_at /- def missing doc string -/
#print tactic.expr_list_to_list_expr /- def missing doc string -/

-- tactic/ext.lean
#print tactic.try_intros /- def missing doc string -/
#print opt_minus /- def missing doc string -/
#print ext_param /- def missing doc string -/
#print tactic.ext /- def missing doc string -/
#print ext_param_type /- def missing doc string -/
#print get_ext_subject /- def missing doc string -/
#print tactic.ext1 /- def missing doc string -/
#print saturate_fun /- def missing doc string -/
#print equiv_type_constr /- def missing doc string -/

-- tactic/explode.lean
#print tactic.explode.core /- def missing doc string -/
#print tactic.explode.args /- def missing doc string -/
#print tactic.explode.status /- constant missing doc string -/
#print tactic.explode.entries.size /- def missing doc string -/
#print tactic.explode.append_dep /- def missing doc string -/
#print tactic.explode.head' /- def missing doc string -/
#print tactic.explode.may_be_proof /- def missing doc string -/
#print tactic.explode /- def missing doc string -/
#print tactic.explode.entries.head /- def missing doc string -/
#print tactic.explode.entries.find /- def missing doc string -/
#print tactic.explode.pad_right /- def missing doc string -/
#print tactic.explode_expr /- def missing doc string -/
#print tactic.explode.format_aux /- def missing doc string -/
#print tactic.explode.entry /- constant missing doc string -/
#print tactic.explode.entries /- constant missing doc string -/
#print tactic.explode.entries.add /- def missing doc string -/
#print tactic.explode_cmd /- def missing doc string -/

-- tactic/elide.lean
#print tactic.elide.unelide /- def missing doc string -/
#print tactic.elide.replace /- def missing doc string -/

-- tactic/core.lean
#print tactic.interactive.injections_and_clear /- def missing doc string -/
#print tactic.interactive.fsplit /- def missing doc string -/

-- tactic/converter/old_conv.lean
#print old_conv /- def missing doc string -/
#print old_conv.skip /- def missing doc string -/
#print old_conv.failed /- def missing doc string -/
#print old_conv.repeat /- def missing doc string -/
#print old_conv.trace /- def missing doc string -/
#print old_conv.findp /- def missing doc string -/
#print old_conv.first /- def missing doc string -/
#print old_conv.dsimp /- def missing doc string -/
#print old_conv_result /- constant missing doc string -/
#print old_conv.change /- def missing doc string -/
#print old_conv.apply_propext_lemmas /- def missing doc string -/
#print old_conv.apply_lemmas_core /- def missing doc string -/
#print old_conv.orelse /- def missing doc string -/
#print old_conv.to_tactic /- def missing doc string -/
#print old_conv.conversion /- def missing doc string -/
#print old_conv.apply_propext_simp_set /- def missing doc string -/
#print old_conv.apply_lemmas /- def missing doc string -/
#print old_conv.trace_lhs /- def missing doc string -/
#print old_conv.match_pattern /- def missing doc string -/
#print old_conv.funext /- def missing doc string -/
#print old_conv.find_pattern /- def missing doc string -/
#print old_conv.lhs /- def missing doc string -/
#print old_conv.congr_core /- def missing doc string -/
#print old_conv.apply_propext_lemmas_core /- def missing doc string -/
#print old_conv.apply_simp_set /- def missing doc string -/
#print old_conv.whnf /- def missing doc string -/
#print old_conv.find /- def missing doc string -/
#print old_conv.top_down /- def missing doc string -/
#print old_conv.bind /- def missing doc string -/
#print old_conv.bottom_up /- def missing doc string -/
#print old_conv.pure /- def missing doc string -/
#print old_conv.seq /- def missing doc string -/
#print old_conv.congr /- def missing doc string -/
#print old_conv.fail /- def missing doc string -/
#print old_conv.map /- def missing doc string -/
#print old_conv.lift_tactic /- def missing doc string -/
#print old_conv.mk_match_expr /- def missing doc string -/
#print old_conv.match_expr /- def missing doc string -/

-- tactic/converter/interactive.lean
#print old_conv.interactive.trace_state /- def missing doc string -/
#print old_conv.execute /- def missing doc string -/
#print old_conv.istep /- def missing doc string -/
#print old_conv.interactive.find /- def missing doc string -/
#print old_conv.interactive.whnf /- def missing doc string -/
#print old_conv.save_info /- def missing doc string -/
#print tactic.interactive.find /- def missing doc string -/
#print conv.replace_lhs /- def missing doc string -/
#print tactic.interactive.conv_rhs /- def missing doc string -/
#print conv.interactive.erw /- def missing doc string -/
#print old_conv.step /- def missing doc string -/
#print old_conv.interactive.dsimp /- def missing doc string -/
#print tactic.interactive.conv_lhs /- def missing doc string -/
#print old_conv.interactive.change /- def missing doc string -/
#print conv.discharge_eq_lhs /- def missing doc string -/
#print old_conv.interactive.itactic /- def missing doc string -/
#print tactic.interactive.old_conv /- def missing doc string -/

-- tactic/converter/binders.lean
#print old_conv.congr_rule /- def missing doc string -/
#print forall_eq_elim /- def missing doc string -/
#print old_conv.head_beta /- def missing doc string -/
#print old_conv.applyc /- def missing doc string -/
#print old_conv.propext' /- def missing doc string -/
#print binder_eq_elim.push /- def missing doc string -/
#print old_conv.congr_arg /- def missing doc string -/
#print old_conv.apply' /- def missing doc string -/
#print binder_eq_elim.check_eq /- def missing doc string -/
#print binder_eq_elim.pull /- def missing doc string -/
#print binder_eq_elim.old_conv /- def missing doc string -/
#print old_conv.apply /- def missing doc string -/
#print binder_eq_elim.check /- def missing doc string -/
#print old_conv.current_relation /- def missing doc string -/
#print supr_eq_elim /- def missing doc string -/
#print infi_eq_elim /- def missing doc string -/
#print exists_eq_elim /- def missing doc string -/
#print binder_eq_elim /- constant missing doc string -/
#print old_conv.funext' /- def missing doc string -/
#print old_conv.congr_fun /- def missing doc string -/
#print old_conv.congr_binder /- def missing doc string -/

-- tactic/chain.lean
#print tactic.abstract_if_success /- def missing doc string -/
#print tactic.chain_core /- def missing doc string -/
#print tactic.interactive.work_on_goal /- def missing doc string -/
#print tactic.trace_output /- def missing doc string -/
#print tactic.chain /- def missing doc string -/

-- tactic/auto_cases.lean
#print auto_cases_at /- def missing doc string -/

-- tactic/apply_fun.lean
#print apply_fun_name /- def missing doc string -/

-- tactic/alias.lean
#print tactic.alias.alias_attr /- def missing doc string -/
#print tactic.alias.get_lambda_body /- def missing doc string -/
#print tactic.alias.mk_iff_mp_app /- def missing doc string -/
#print tactic.alias.alias_cmd /- def missing doc string -/
#print tactic.alias.alias_direct /- def missing doc string -/
#print tactic.alias.alias_iff /- def missing doc string -/
#print tactic.alias.get_alias_target /- def missing doc string -/
#print tactic.alias.make_left_right /- def missing doc string -/

-- tactic/algebra.lean
#print tactic.ancestor_attr /- def missing doc string -/
#print tactic.find_ancestors /- def missing doc string -/
#print tactic.get_ancestors /- def missing doc string -/

-- tactic/abel.lean
#print tactic.abel.cache /- constant missing doc string -/
#print tactic.abel.smulg /- def missing doc string -/
#print tactic.abel.cache.mk_app /- def missing doc string -/
#print tactic.abel.normal_expr.refl_conv /- def missing doc string -/
#print tactic.abel.eval_atom /- def missing doc string -/
#print tactic.abel.normal_expr.to_list /- def missing doc string -/
#print tactic.abel.add_g /- def missing doc string -/
#print tactic.abel.normalize /- def missing doc string -/
#print tactic.abel.cache.mk_term /- def missing doc string -/
#print tactic.abel.termg /- def missing doc string -/
#print tactic.abel.normal_expr.term' /- def missing doc string -/
#print tactic.abel.normalize_mode /- constant missing doc string -/
#print tactic.abel.normal_expr.to_string /- def missing doc string -/
#print tactic.abel.eval' /- def missing doc string -/
#print tactic.abel.cache.app /- def missing doc string -/
#print tactic.interactive.abel.mode /- def missing doc string -/
#print tactic.abel.eval_smul /- def missing doc string -/
#print tactic.abel.cache.int_to_expr /- def missing doc string -/
#print tactic.abel.cache.iapp /- def missing doc string -/
#print tactic.abel.eval /- def missing doc string -/
#print tactic.abel.eval_add /- def missing doc string -/
#print tactic.abel.eval_neg /- def missing doc string -/
#print tactic.abel.normal_expr.zero' /- def missing doc string -/
#print tactic.abel.normal_expr /- constant missing doc string -/
#print tactic.abel.mk_cache /- def missing doc string -/
#print tactic.abel.smul /- def missing doc string -/
#print tactic.abel.term /- def missing doc string -/
#print tactic.abel.normal_expr.pp /- def missing doc string -/
#print tactic.abel.normal_expr.e /- def missing doc string -/

-- set_theory/zfc.lean
#print pSet.definable.eq_mk /- def missing doc string -/
#print Set.subset /- def missing doc string -/
#print pSet.resp.eval_aux /- def missing doc string -/
#print Set.mem /- def missing doc string -/
#print classical.all_definable /- def missing doc string -/
#print pSet.subset /- def missing doc string -/
#print Class /- def missing doc string -/
#print pSet.definable.resp /- def missing doc string -/
#print pSet.resp.f /- def missing doc string -/
#print pSet.resp.equiv /- def missing doc string -/
#print Set.mk /- def missing doc string -/

-- set_theory/surreal.lean
#print surreal.add /- def missing doc string -/

-- set_theory/ordinal_notation.lean
#print onote.power_aux /- def missing doc string -/
#print onote.to_string_aux1 /- def missing doc string -/

-- set_theory/ordinal.lean
#print principal_seg.lt_le /- def missing doc string -/
#print cardinal.ord.order_embedding /- def missing doc string -/
#print ordinal.typein_iso /- def missing doc string -/
#print ordinal.limit_rec_on /- def missing doc string -/
#print principal_seg.lt_equiv /- def missing doc string -/
#print ordinal.principal_seg_out /- def missing doc string -/
#print cardinal.aleph_idx.order_iso /- def missing doc string -/
#print order_embedding.collapse_F /- def missing doc string -/
#print principal_seg.equiv_lt /- def missing doc string -/
#print ordinal.typein.principal_seg /- def missing doc string -/
#print Well_order /- constant missing doc string -/
#print principal_seg.trans /- def missing doc string -/
#print cardinal.aleph'.order_iso /- def missing doc string -/
#print ordinal.initial_seg_out /- def missing doc string -/
#print ordinal.order_iso_out /- def missing doc string -/
#print ordinal.lift.initial_seg /- def missing doc string -/
#print initial_seg.le_add /- def missing doc string -/
#print principal_seg /- constant missing doc string -/
#print initial_seg.le_lt /- def missing doc string -/
#print ordinal.lift.principal_seg /- def missing doc string -/
#print initial_seg.lt_or_eq /- def missing doc string -/
#print cardinal.aleph_idx.initial_seg /- def missing doc string -/
#print ordinal.CNF_rec /- def missing doc string -/

-- set_theory/lists.lean
#print lists.to_list /- def missing doc string -/
#print lists.mem /- def missing doc string -/
#print lists'.to_list /- def missing doc string -/
#print lists /- def missing doc string -/
#print lists.of' /- def missing doc string -/
#print finsets /- def missing doc string -/
#print lists'.cons /- def missing doc string -/
#print lists.atom /- def missing doc string -/
#print lists.is_list /- def missing doc string -/
#print lists.induction_mut /- def missing doc string -/
#print lists.of_list /- def missing doc string -/
#print lists'.of_list /- def missing doc string -/
#print lists' /- constant missing doc string -/

-- set_theory/cofinality.lean
#print strict_order.cof /- def missing doc string -/

-- ring_theory/unique_factorization_domain.lean
#print unique_irreducible_factorization /- constant missing doc string -/
#print unique_factorization_domain.of_unique_irreducible_factorization /- def missing doc string -/
#print associates.factors /- def missing doc string -/
#print associates.factors' /- def missing doc string -/
#print associates.factor_set.prod /- def missing doc string -/

-- ring_theory/subring.lean
#print ring.closure /- def missing doc string -/

-- ring_theory/principal_ideal_domain.lean
#print ideal.is_principal.generator /- def missing doc string -/
#print principal_ideal_domain /- constant missing doc string -/
#print ideal.is_principal /- constant missing doc string -/
#print principal_ideal_domain.factors /- def missing doc string -/

-- ring_theory/power_series.lean
#print power_series.inv.aux /- def missing doc string -/
#print power_series.inv /- def missing doc string -/
#print polynomial.monomial /- def missing doc string -/
#print mv_power_series.inv /- def missing doc string -/
#print mv_power_series.trunc_fun /- def missing doc string -/

-- ring_theory/noetherian.lean
#print submodule.fg /- def missing doc string -/
#print is_noetherian /- constant missing doc string -/
#print is_noetherian_ring /- def missing doc string -/

-- ring_theory/multiplicity.lean
#print multiplicity.finite /- def missing doc string -/

-- ring_theory/maps.lean
#print is_ring_anti_hom /- constant missing doc string -/
#print comm_ring.anti_equiv_to_equiv /- def missing doc string -/
#print ring_anti_equiv.refl /- def missing doc string -/
#print ring_invo.id /- def missing doc string -/
#print ring_invo.to_ring_anti_equiv /- def missing doc string -/
#print comm_ring.equiv_to_anti_equiv /- def missing doc string -/

-- ring_theory/localization.lean
#print localization.fraction_ring.map /- def missing doc string -/
#print localization.equiv_of_equiv /- def missing doc string -/
#print localization.le_order_embedding /- def missing doc string -/
#print localization.away_to_away_right /- def missing doc string -/
#print localization.map /- def missing doc string -/
#print localization.non_zero_divisors /- def missing doc string -/
#print localization.away.inv_self /- def missing doc string -/
#print localization.away /- def missing doc string -/
#print localization.lift' /- def missing doc string -/
#print localization.lift /- def missing doc string -/
#print localization.fraction_ring.equiv_of_equiv /- def missing doc string -/
#print localization.mk /- def missing doc string -/
#print localization.fraction_ring.inv_aux /- def missing doc string -/
#print localization.at_prime /- def missing doc string -/
#print localization.r /- def missing doc string -/
#print localization.away.lift /- def missing doc string -/

-- ring_theory/integral_closure.lean
#print is_integral /- def missing doc string -/
#print integral_closure /- def missing doc string -/

-- ring_theory/ideals.lean
#print ideal.is_coprime /- def missing doc string -/
#print local_ring.residue_field /- def missing doc string -/
#print local_ring /- constant missing doc string -/
#print nonunits /- def missing doc string -/
#print local_of_unit_or_unit_one_sub /- def missing doc string -/
#print ideal.is_prime /- def missing doc string -/
#print ideal.is_maximal /- def missing doc string -/
#print ideal.quotient /- def missing doc string -/
#print ideal.span /- def missing doc string -/
#print ideal.quotient.lift /- def missing doc string -/
#print ideal.quotient.mk /- def missing doc string -/
#print local_of_is_local_ring /- def missing doc string -/
#print local_ring.residue_field.map /- def missing doc string -/
#print ideal.quotient.nonzero_comm_ring /- def missing doc string -/
#print is_local_ring_hom /- constant missing doc string -/
#print ideal.quotient.map_mk /- def missing doc string -/
#print is_local_ring /- def missing doc string -/
#print local_of_unique_max_ideal /- def missing doc string -/
#print local_ring.nonunits_ideal /- def missing doc string -/
#print local_of_nonunits_ideal /- def missing doc string -/

-- ring_theory/ideal_operations.lean
#print submodule.colon /- def missing doc string -/
#print ideal.radical /- def missing doc string -/
#print submodule.annihilator /- def missing doc string -/
#print is_ring_hom.ker /- def missing doc string -/
#print ideal.quotient_inf_to_pi_quotient /- def missing doc string -/
#print ideal.comap /- def missing doc string -/
#print ideal.le_order_embedding_of_surjective /- def missing doc string -/
#print ideal.map /- def missing doc string -/
#print ideal.lt_order_embedding_of_surjective /- def missing doc string -/

-- ring_theory/free_ring.lean
#print free_ring /- def missing doc string -/
#print free_ring.lift /- def missing doc string -/
#print free_ring.map /- def missing doc string -/
#print free_ring.of /- def missing doc string -/

-- ring_theory/free_comm_ring.lean
#print free_comm_ring.of /- def missing doc string -/
#print free_comm_ring.lift /- def missing doc string -/
#print free_ring.to_free_comm_ring /- def missing doc string -/
#print free_ring_pempty_equiv_int /- def missing doc string -/
#print free_comm_ring /- def missing doc string -/
#print free_ring.subsingleton_equiv_free_comm_ring /- def missing doc string -/
#print free_comm_ring.map /- def missing doc string -/
#print free_comm_ring_pempty_equiv_int /- def missing doc string -/
#print free_comm_ring.restriction /- def missing doc string -/
#print free_ring_punit_equiv_polynomial_int /- def missing doc string -/
#print free_comm_ring.is_supported /- def missing doc string -/
#print free_comm_ring_equiv_mv_polynomial_int /- def missing doc string -/
#print free_comm_ring_punit_equiv_polynomial_int /- def missing doc string -/

-- ring_theory/algebra.lean
#print subalgebra /- constant missing doc string -/
#print alg_hom.to_ring_hom /- def missing doc string -/
#print algebra_map /- def missing doc string -/
#print algebra.to_top /- def missing doc string -/
#print algebra.of_id /- def missing doc string -/
#print subalgebra.val /- def missing doc string -/
#print alg_hom.id /- def missing doc string -/
#print algebra.comap.of_comap /- def missing doc string -/
#print subalgebra.under /- def missing doc string -/
#print algebra.to_comap /- def missing doc string -/
#print alg_hom.range /- def missing doc string -/
#print algebra.gi /- def missing doc string -/
#print subalgebra.to_submodule /- def missing doc string -/
#print algebra.lmul_left /- def missing doc string -/
#print algebra.comap.to_comap /- def missing doc string -/
#print algebra.adjoin /- def missing doc string -/
#print algebra.lmul_right /- def missing doc string -/
#print subalgebra.comap /- def missing doc string -/
#print alg_hom.comp /- def missing doc string -/

-- ring_theory/adjoin_root.lean
#print adjoin_root.root /- def missing doc string -/
#print adjoin_root.lift /- def missing doc string -/
#print adjoin_root.of /- def missing doc string -/
#print adjoin_root.mk /- def missing doc string -/
#print adjoin_root /- def missing doc string -/

-- ring_theory/adjoin.lean
#print subalgebra.fg /- def missing doc string -/

-- order/zorn.lean
#print zorn.max_chain /- def missing doc string -/
#print zorn.succ_chain /- def missing doc string -/
#print zorn.is_max_chain /- def missing doc string -/
#print zorn.chain_closure /- constant missing doc string -/
#print zorn.super_chain /- def missing doc string -/

-- order/pilex.lean
#print pi.lex /- def missing doc string -/
#print pilex /- def missing doc string -/

-- order/order_iso.lean
#print order_iso.prod_lex_congr /- def missing doc string -/
#print subrel.order_embedding /- def missing doc string -/
#print order_iso.to_order_embedding /- def missing doc string -/
#print order_iso.trans /- def missing doc string -/
#print order_embedding.lt_embedding_of_le_embedding /- def missing doc string -/
#print order_iso.refl /- def missing doc string -/
#print order_iso.sum_lex_congr /- def missing doc string -/
#print order_iso.symm /- def missing doc string -/
#print order_embedding.nat_lt /- def missing doc string -/
#print order_embedding.trans /- def missing doc string -/
#print order_iso.of_surjective /- def missing doc string -/
#print order_embedding.refl /- def missing doc string -/
#print order_embedding /- constant missing doc string -/
#print order_embedding.nat_gt /- def missing doc string -/

-- order/liminf_limsup.lean
#print filter.Liminf /- def missing doc string -/
#print filter.is_bounded_default /- def missing doc string -/
#print filter.limsup /- def missing doc string -/
#print filter.liminf /- def missing doc string -/
#print filter.Limsup /- def missing doc string -/
#print filter.is_cobounded_under /- def missing doc string -/
#print filter.is_bounded_under /- def missing doc string -/

-- order/lexicographic.lean
#print lex /- def missing doc string -/

-- order/fixed_points.lean
#print lattice.fixed_points.next /- def missing doc string -/
#print lattice.fixed_points.prev_fixed /- def missing doc string -/
#print lattice.fixed_points /- def missing doc string -/
#print lattice.fixed_points.prev /- def missing doc string -/
#print lattice.fixed_points.next_fixed /- def missing doc string -/

-- order/filter/pointwise.lean
#print filter.pointwise_one /- def missing doc string -/
#print filter.pointwise_zero /- def missing doc string -/
#print filter.pointwise_add /- def missing doc string -/
#print filter.pointwise_mul /- def missing doc string -/
#print filter.pointwise_mul_monoid /- def missing doc string -/
#print filter.pointwise_add_add_monoid /- def missing doc string -/

-- order/filter/partial.lean
#print filter.rcomap /- def missing doc string -/
#print filter.ptendsto /- def missing doc string -/
#print filter.rcomap' /- def missing doc string -/
#print filter.ptendsto' /- def missing doc string -/
#print filter.pmap /- def missing doc string -/
#print filter.rtendsto /- def missing doc string -/
#print filter.rtendsto' /- def missing doc string -/
#print filter.rmap /- def missing doc string -/
#print filter.pcomap' /- def missing doc string -/

-- order/filter/filter_product.lean
#print filter.filter_product.of_seq /- def missing doc string -/

-- order/filter/basic.lean
#print filter.ultrafilter.bind /- def missing doc string -/
#print filter.ultrafilter.pure /- def missing doc string -/
#print filter.ultrafilter /- def missing doc string -/
#print filter.monad /- def missing doc string -/
#print filter.gi_generate /- def missing doc string -/
#print filter.ultrafilter.map /- def missing doc string -/
#print lattice.complete_lattice.copy /- def missing doc string -/
#print filter.mk_of_closure /- def missing doc string -/
#print filter /- constant missing doc string -/
#print filter.hyperfilter /- def missing doc string -/

-- order/conditionally_complete_lattice.lean
#print lattice.conditionally_complete_linear_order_bot /- constant missing doc string -/
#print lattice.conditionally_complete_linear_order /- constant missing doc string -/

-- order/bounded_lattice.lean
#print with_top /- def missing doc string -/
#print with_bot /- def missing doc string -/

-- order/basic.lean
#print preorder.lift /- def missing doc string -/
#print classical.DLO /- def missing doc string -/
#print well_founded.sup /- def missing doc string -/
#print linear_order.lift /- def missing doc string -/
#print partial_order.lift /- def missing doc string -/
#print directed_order /- constant missing doc string -/
#print well_founded.succ /- def missing doc string -/
#print decidable_linear_order_of_is_well_order /- def missing doc string -/
#print decidable_linear_order.lift /- def missing doc string -/

-- number_theory/pell.lean
#print pell.yz /- def missing doc string -/
#print pell.az /- def missing doc string -/
#print pell.xz /- def missing doc string -/

-- number_theory/dioph.lean
#print fin2.cases' /- def missing doc string -/
#print vector3.rec_on /- def missing doc string -/
#print vector3.nil_elim /- def missing doc string -/
#print fin2.elim0 /- def missing doc string -/
#print vector3.cons_elim /- def missing doc string -/

-- meta/expr.lean
#print declaration.update_with_fun /- def missing doc string -/

-- meta/coinductive_predicates.lean
#print tactic.add_coinductive_predicate.coind_rule /- constant missing doc string -/
#print tactic.add_coinductive_predicate.coind_pred.u_params /- def missing doc string -/
#print tactic.add_coinductive_predicate.coind_pred.destruct /- def missing doc string -/
#print tactic.add_coinductive_predicate.coind_pred.func /- def missing doc string -/
#print tactic.add_coinductive_predicate /- def missing doc string -/
#print tactic.add_coinductive_predicate.coind_pred.mono /- def missing doc string -/
#print tactic.add_coinductive_predicate.coind_pred.f₁_l /- def missing doc string -/
#print tactic.add_coinductive_predicate.coind_pred.func_g /- def missing doc string -/
#print tactic.add_coinductive_predicate.coind_pred.pred /- def missing doc string -/
#print tactic.coinductive_predicate /- def missing doc string -/
#print tactic.add_coinductive_predicate.coind_pred.rec' /- def missing doc string -/
#print tactic.add_coinductive_predicate.coind_pred.construct /- def missing doc string -/
#print tactic.add_coinductive_predicate.coind_pred /- constant missing doc string -/
#print tactic.interactive.coinduction /- def missing doc string -/
#print tactic.add_coinductive_predicate.coind_pred.f₂_l /- def missing doc string -/
#print tactic.add_coinductive_predicate.coind_pred.le /- def missing doc string -/
#print tactic.add_coinductive_predicate.coind_pred.corec_functional /- def missing doc string -/
#print tactic.add_coinductive_predicate.coind_pred.pred_g /- def missing doc string -/
#print tactic.mono /- def missing doc string -/
#print monotonicity /- def missing doc string -/
#print tactic.add_coinductive_predicate.coind_pred.impl_locals /- def missing doc string -/
#print tactic.add_coinductive_predicate.coind_pred.add_theorem /- def missing doc string -/
#print tactic.add_coinductive_predicate.coind_pred.impl_params /- def missing doc string -/

-- measure_theory/probability_mass_function.lean
#print pmf.pure /- def missing doc string -/
#print pmf.map /- def missing doc string -/
#print pmf.bernoulli /- def missing doc string -/
#print pmf.bind /- def missing doc string -/
#print pmf.support /- def missing doc string -/
#print pmf.of_fintype /- def missing doc string -/
#print pmf.seq /- def missing doc string -/
#print pmf.of_multiset /- def missing doc string -/

-- measure_theory/outer_measure.lean
#print measure_theory.outer_measure /- constant missing doc string -/
#print measure_theory.outer_measure.sum /- def missing doc string -/
#print measure_theory.outer_measure.Inf_gen /- def missing doc string -/
#print measure_theory.outer_measure.map /- def missing doc string -/

-- measure_theory/measure_space.lean
#print measure_theory.measure.is_complete /- def missing doc string -/
#print completion /- def missing doc string -/
#print measure_theory.outer_measure.trim /- def missing doc string -/
#print measure_theory.measure.map /- def missing doc string -/
#print measure_theory.measure /- constant missing doc string -/
#print is_null_measurable /- def missing doc string -/
#print measure_theory.measure.of_measurable /- def missing doc string -/
#print measure_theory.outer_measure.to_measure /- def missing doc string -/
#print measure_theory.volume /- def missing doc string -/
#print null_measurable /- def missing doc string -/

-- measure_theory/measurable_space.lean
#print measurable_equiv.set.range /- def missing doc string -/
#print measurable_space.dynkin_system.restrict_on /- def missing doc string -/
#print measurable_space.mk_of_closure /- def missing doc string -/
#print measurable_space.gi_generate_from /- def missing doc string -/
#print measurable_equiv.trans /- def missing doc string -/
#print measurable_equiv.cast /- def missing doc string -/
#print measurable_equiv.sum_congr /- def missing doc string -/
#print measurable_equiv.set.univ /- def missing doc string -/
#print measurable_space.dynkin_system.generate /- def missing doc string -/
#print measurable_equiv.sum_prod_sum /- def missing doc string -/
#print measurable_equiv.refl /- def missing doc string -/
#print measurable_equiv.set.range_inr /- def missing doc string -/
#print measurable_equiv.prod_congr /- def missing doc string -/
#print measurable_equiv.set.image /- def missing doc string -/
#print measurable_equiv.set.singleton /- def missing doc string -/
#print measurable_equiv.prod_comm /- def missing doc string -/
#print measurable_equiv.symm /- def missing doc string -/
#print measurable_equiv.set.prod /- def missing doc string -/
#print measurable_equiv.sum_prod_distrib /- def missing doc string -/
#print measurable_space.dynkin_system.of_measurable_space /- def missing doc string -/
#print measurable_equiv.set.range_inl /- def missing doc string -/
#print measurable_space.dynkin_system.to_measurable_space /- def missing doc string -/
#print measurable_space /- constant missing doc string -/
#print measurable_equiv.prod_sum_distrib /- def missing doc string -/

-- measure_theory/integration.lean
#print measure_theory.simple_func.pair /- def missing doc string -/
#print measure_theory.simple_func.fin_vol_supp /- def missing doc string -/
#print measure_theory.simple_func /- constant missing doc string -/
#print measure_theory.simple_func.range /- def missing doc string -/
#print measure_theory.simple_func.seq /- def missing doc string -/
#print measure_theory.measure.with_density /- def missing doc string -/
#print measure_theory.simple_func.approx /- def missing doc string -/
#print measure_theory.simple_func.eapprox /- def missing doc string -/
#print sequence_of_directed /- def missing doc string -/
#print measure_theory.simple_func.restrict /- def missing doc string -/
#print measure_theory.simple_func.ite /- def missing doc string -/
#print measure_theory.simple_func.const /- def missing doc string -/
#print measure_theory.simple_func.ennreal_rat_embed /- def missing doc string -/
#print measure_theory.simple_func.bind /- def missing doc string -/
#print measure_theory.measure.integral /- def missing doc string -/

-- measure_theory/category/Meas.lean
#print Meas /- def missing doc string -/

-- measure_theory/borel_space.lean
#print homemorph.to_measurable_equiv /- def missing doc string -/
#print ennreal.ennreal_equiv_nnreal /- def missing doc string -/
#print ennreal.ennreal_equiv_sum /- def missing doc string -/

-- measure_theory/ae_eq_fun.lean
#print measure_theory.ae_eq_fun.add /- def missing doc string -/
#print measure_theory.ae_eq_fun.smul /- def missing doc string -/
#print measure_theory.ae_eq_fun.neg /- def missing doc string -/

-- logic/unique.lean
#print unique /- constant missing doc string -/
#print unique.of_surjective /- def missing doc string -/

-- logic/relator.lean
#print relator.lift_fun /- def missing doc string -/
#print relator.right_total /- def missing doc string -/
#print relator.bi_unique /- def missing doc string -/
#print relator.left_total /- def missing doc string -/
#print relator.bi_total /- def missing doc string -/
#print relator.right_unique /- def missing doc string -/
#print relator.left_unique /- def missing doc string -/

-- logic/relation.lean
#print relation.comp /- def missing doc string -/
#print relation.map /- def missing doc string -/
#print relation.join /- def missing doc string -/

-- logic/function.lean
#print function.injective.decidable_eq /- def missing doc string -/
#print function.update /- def missing doc string -/
#print function.bicompr /- def missing doc string -/
#print function.restrict /- def missing doc string -/
#print function.uncurry' /- def missing doc string -/
#print function.bicompl /- def missing doc string -/

-- logic/embedding.lean
#print function.embedding.subtype /- def missing doc string -/
#print function.embedding.of_surjective /- def missing doc string -/
#print function.embedding.trans /- def missing doc string -/
#print function.embedding.sum_congr /- def missing doc string -/
#print function.embedding /- constant missing doc string -/
#print function.embedding.arrow_congr_right /- def missing doc string -/
#print function.embedding.prod_congr /- def missing doc string -/
#print function.embedding.sigma_congr_right /- def missing doc string -/
#print function.embedding.refl /- def missing doc string -/
#print function.embedding.subtype_map /- def missing doc string -/
#print function.embedding.of_not_nonempty /- def missing doc string -/
#print function.embedding.congr /- def missing doc string -/
#print equiv.to_embedding /- def missing doc string -/
#print function.embedding.image /- def missing doc string -/
#print function.embedding.equiv_of_surjective /- def missing doc string -/
#print function.embedding.set_value /- def missing doc string -/
#print function.embedding.arrow_congr_left /- def missing doc string -/
#print function.embedding.Pi_congr_right /- def missing doc string -/

-- logic/basic.lean
#print classical.inhabited_of_nonempty' /- def missing doc string -/
#print pempty.elim /- def missing doc string -/
#print decidable_of_bool /- def missing doc string -/
#print not.elim /- def missing doc string -/
#print decidable_of_iff' /- def missing doc string -/
#print classical.exists_cases /- def missing doc string -/
#print hidden /- def missing doc string -/
#print decidable_of_iff /- def missing doc string -/
#print empty.elim /- def missing doc string -/
#print exists.classical_rec_on /- def missing doc string -/

-- linear_algebra/tensor_product.lean
#print tensor_product.tmul /- def missing doc string -/
#print tensor_product.direct_sum /- def missing doc string -/
#print linear_map.flip /- def missing doc string -/
#print tensor_product.comm /- def missing doc string -/
#print tensor_product.relators /- def missing doc string -/
#print tensor_product /- def missing doc string -/
#print tensor_product.lift_aux /- def missing doc string -/
#print linear_map.lsmul /- def missing doc string -/
#print tensor_product.lid /- def missing doc string -/
#print tensor_product.assoc /- def missing doc string -/
#print tensor_product.mk /- def missing doc string -/
#print tensor_product.lcurry /- def missing doc string -/
#print tensor_product.congr /- def missing doc string -/
#print tensor_product.curry /- def missing doc string -/
#print linear_map.compr₂ /- def missing doc string -/
#print linear_map.mk₂ /- def missing doc string -/
#print tensor_product.smul.aux /- def missing doc string -/
#print linear_map.compl₂ /- def missing doc string -/
#print linear_map.llcomp /- def missing doc string -/
#print tensor_product.lift.equiv /- def missing doc string -/
#print tensor_product.map /- def missing doc string -/
#print tensor_product.uncurry /- def missing doc string -/
#print linear_map.lflip /- def missing doc string -/
#print linear_map.lcomp /- def missing doc string -/
#print tensor_product.lift /- def missing doc string -/

-- linear_algebra/finsupp_vector_space.lean
#print equiv_of_dim_eq_dim /- def missing doc string -/
#print fin_dim_vectorspace_equiv /- def missing doc string -/

-- linear_algebra/finsupp.lean
#print finsupp.congr /- def missing doc string -/
#print finsupp.lsum /- def missing doc string -/
#print finsupp.total_on /- def missing doc string -/
#print finsupp.supported_equiv_finsupp /- def missing doc string -/
#print finsupp.lapply /- def missing doc string -/
#print finsupp.dom_lcongr /- def missing doc string -/
#print finsupp.lsubtype_domain /- def missing doc string -/
#print finsupp.lsingle /- def missing doc string -/
#print finsupp.lmap_domain /- def missing doc string -/
#print finsupp.restrict_dom /- def missing doc string -/
#print finsupp.supported /- def missing doc string -/

-- linear_algebra/dual.lean
#print is_basis.coord_fun /- def missing doc string -/
#print is_basis.to_dual_flip /- def missing doc string -/

-- linear_algebra/direct_sum_module.lean
#print direct_sum.lof /- def missing doc string -/
#print direct_sum.lid /- def missing doc string -/
#print direct_sum.lset_to_set /- def missing doc string -/
#print direct_sum.component /- def missing doc string -/
#print direct_sum.to_module /- def missing doc string -/
#print direct_sum.lmk /- def missing doc string -/

-- linear_algebra/dimension.lean
#print vector_space.dim /- def missing doc string -/
#print rank /- def missing doc string -/

-- linear_algebra/determinant.lean
#print matrix.det /- def missing doc string -/

-- linear_algebra/bilinear_form.lean
#print bilin_form.bilin_linear_map_equiv /- def missing doc string -/
#print bilin_form.to_linear_map /- def missing doc string -/
#print linear_map.to_bilin /- def missing doc string -/

-- linear_algebra/basis.lean
#print is_basis.repr /- def missing doc string -/

-- linear_algebra/basic.lean
#print linear_equiv.to_equiv /- def missing doc string -/
#print linear_equiv.to_linear_map /- def missing doc string -/

-- group_theory/sylow.lean
#print sylow.fixed_points_mul_left_cosets_equiv_quotient /- def missing doc string -/
#print sylow.rotate_vectors_prod_eq_one /- def missing doc string -/
#print sylow.vectors_prod_eq_one /- def missing doc string -/
#print sylow.mk_vector_prod_eq_one /- def missing doc string -/

-- group_theory/subgroup.lean
#print is_add_subgroup.trivial /- def missing doc string -/
#print gpowers /- def missing doc string -/
#print normal_subgroup /- constant missing doc string -/
#print normal_add_subgroup /- constant missing doc string -/
#print gmultiples /- def missing doc string -/
#print is_add_subgroup.add_normalizer /- def missing doc string -/
#print simple_group /- constant missing doc string -/
#print add_group.closure /- def missing doc string -/
#print add_group.in_closure /- constant missing doc string -/
#print group.in_closure /- constant missing doc string -/
#print is_subgroup.normalizer /- def missing doc string -/
#print simple_add_group /- constant missing doc string -/
#print is_group_hom.ker /- def missing doc string -/
#print is_add_group_hom.ker /- def missing doc string -/
#print is_add_subgroup.add_center /- def missing doc string -/
#print is_subgroup.center /- def missing doc string -/

-- group_theory/quotient_group.lean
#print quotient_add_group.map /- def missing doc string -/
#print quotient_group.lift /- def missing doc string -/
#print quotient_group.quotient_ker_equiv_range /- def missing doc string -/
#print quotient_add_group.quotient_ker_equiv_range /- def missing doc string -/
#print quotient_add_group.quotient_ker_equiv_of_surjective /- def missing doc string -/
#print quotient_group.map /- def missing doc string -/
#print quotient_add_group.ker_lift /- def missing doc string -/
#print quotient_add_group.lift /- def missing doc string -/
#print quotient_group.quotient_ker_equiv_of_surjective /- def missing doc string -/

-- group_theory/perm/sign.lean
#print equiv.perm.trunc_swap_factors /- def missing doc string -/
#print equiv.perm.of_subtype /- def missing doc string -/
#print equiv.perm.subtype_perm /- def missing doc string -/
#print equiv.perm.sign_aux /- def missing doc string -/
#print equiv.perm.support /- def missing doc string -/
#print equiv.perm.sign_bij_aux /- def missing doc string -/
#print equiv.perm.is_cycle /- def missing doc string -/
#print equiv.perm.swap_factors_aux /- def missing doc string -/
#print equiv.perm.disjoint /- def missing doc string -/
#print equiv.perm.is_swap /- def missing doc string -/
#print equiv.perm.sign_aux3 /- def missing doc string -/
#print equiv.perm.sign_aux2 /- def missing doc string -/

-- group_theory/perm/cycles.lean
#print equiv.perm.cycle_of /- def missing doc string -/
#print equiv.perm.cycle_factors_aux /- def missing doc string -/
#print equiv.perm.same_cycle /- def missing doc string -/
#print equiv.perm.cycle_factors /- def missing doc string -/

-- group_theory/order_of_element.lean
#print is_cyclic /- constant missing doc string -/
#print is_cyclic.comm_group /- def missing doc string -/

-- group_theory/group_action.lean
#print mul_action.stabilizer /- def missing doc string -/
#print mul_action.to_perm /- def missing doc string -/
#print mul_action.orbit /- def missing doc string -/
#print mul_action.mul_left_cosets /- def missing doc string -/
#print mul_action.comp_hom /- def missing doc string -/
#print mul_action.fixed_points /- def missing doc string -/
#print mul_action.orbit_rel /- def missing doc string -/
#print mul_action.orbit_equiv_quotient_stabilizer /- def missing doc string -/

-- group_theory/free_group.lean
#print free_group.mk /- def missing doc string -/
#print free_group.to_group.aux /- def missing doc string -/
#print free_group.map.aux /- def missing doc string -/
#print free_group.free_group_empty_equiv_unit /- def missing doc string -/
#print free_group.free_group_unit_equiv_int /- def missing doc string -/

-- group_theory/free_abelian_group.lean
#print free_abelian_group.lift.universal /- def missing doc string -/
#print free_abelian_group.lift /- def missing doc string -/
#print free_abelian_group /- def missing doc string -/
#print free_abelian_group.of /- def missing doc string -/

-- group_theory/eckmann_hilton.lean
#print eckmann_hilton.comm_group /- def missing doc string -/
#print eckmann_hilton.is_unital /- constant missing doc string -/
#print eckmann_hilton.comm_monoid /- def missing doc string -/

-- group_theory/coset.lean
#print left_coset_equiv /- def missing doc string -/
#print quotient_add_group.mk /- def missing doc string -/
#print quotient_group.mk /- def missing doc string -/
#print is_subgroup.group_equiv_quotient_times_subgroup /- def missing doc string -/
#print quotient_group.preimage_mk_equiv_subgroup_times_set /- def missing doc string -/
#print is_add_subgroup.left_coset_equiv_subgroup /- def missing doc string -/
#print left_add_coset_equiv /- def missing doc string -/
#print left_add_coset /- def missing doc string -/
#print left_coset /- def missing doc string -/
#print right_coset /- def missing doc string -/
#print quotient_add_group.left_rel /- def missing doc string -/
#print is_subgroup.left_coset_equiv_subgroup /- def missing doc string -/
#print quotient_add_group.quotient /- def missing doc string -/
#print is_add_subgroup.group_equiv_quotient_times_subgroup /- def missing doc string -/
#print right_add_coset /- def missing doc string -/
#print quotient_group.left_rel /- def missing doc string -/

-- group_theory/congruence.lean
#print con.to_setoid /- def missing doc string -/
#print add_con.to_setoid /- def missing doc string -/

-- group_theory/abelianization.lean
#print abelianization.of /- def missing doc string -/
#print abelianization.lift /- def missing doc string -/
#print commutator /- def missing doc string -/
#print abelianization /- def missing doc string -/

-- geometry/manifold/smooth_manifold_with_corners.lean
#print smooth_manifold_with_corners /- constant missing doc string -/

-- geometry/manifold/manifold.lean
#print manifold_core.local_homeomorph /- def missing doc string -/
#print manifold_core.to_manifold /- def missing doc string -/

-- field_theory/subfield.lean
#print is_subfield /- constant missing doc string -/
#print field.closure /- def missing doc string -/

-- field_theory/perfect_closure.lean
#print perfect_closure.frobenius_equiv /- def missing doc string -/
#print perfect_closure.UMP /- def missing doc string -/
#print perfect_closure.of /- def missing doc string -/
#print perfect_closure.r /- constant missing doc string -/

-- field_theory/mv_polynomial.lean
#print mv_polynomial.R /- def missing doc string -/
#print mv_polynomial.evalᵢ /- def missing doc string -/
#print mv_polynomial.indicator /- def missing doc string -/
#print mv_polynomial.restrict_total_degree /- def missing doc string -/
#print mv_polynomial.evalₗ /- def missing doc string -/
#print mv_polynomial.restrict_degree /- def missing doc string -/

-- field_theory/finite.lean
#print finite_field.field_of_integral_domain /- def missing doc string -/

-- data/zsqrtd/gaussian_int.lean
#print gaussian_int /- def missing doc string -/
#print gaussian_int.to_complex /- def missing doc string -/
#print gaussian_int.div /- def missing doc string -/
#print gaussian_int.mod /- def missing doc string -/

-- data/zsqrtd/basic.lean
#print zsqrtd.le /- def missing doc string -/
#print zsqrtd.lt /- def missing doc string -/
#print zsqrtd.norm /- def missing doc string -/

-- data/zmod/quadratic_reciprocity.lean
#print zmodp.legendre_sym /- def missing doc string -/

-- data/zmod/basic.lean
#print zmod.units_equiv_coprime /- def missing doc string -/
#print zmod /- def missing doc string -/
#print zmodp /- def missing doc string -/
#print zmod.cast /- def missing doc string -/

-- data/vector2.lean
#print vector.to_array /- def missing doc string -/
#print vector.insert_nth /- def missing doc string -/
#print vector.m_of_fn /- def missing doc string -/
#print vector.traverse /- def missing doc string -/
#print vector.mmap /- def missing doc string -/
#print vector.reverse /- def missing doc string -/

-- data/tree.lean
#print tree.map /- def missing doc string -/
#print tree.repr /- def missing doc string -/
#print tree /- constant missing doc string -/

-- data/sum.lean
#print sum.elim /- def missing doc string -/
#print sum.map /- def missing doc string -/

-- data/subtype.lean
#print subtype.restrict /- def missing doc string -/

-- data/string/defs.lean
#print string.over_list /- def missing doc string -/
#print string.map_tokens /- def missing doc string -/
#print string.split_on /- def missing doc string -/

-- data/string/basic.lean
#print string.ltb /- def missing doc string -/

-- data/setoid.lean
#print setoid.is_partition /- def missing doc string -/

-- data/set/lattice.lean
#print set.pairwise_disjoint /- def missing doc string -/
#print set.bUnion_eq_sigma_of_disjoint /- def missing doc string -/
#print set.kern_image /- def missing doc string -/
#print set.Union_eq_sigma_of_disjoint /- def missing doc string -/
#print set.sigma_to_Union /- def missing doc string -/
#print set.seq /- def missing doc string -/

-- data/set/finite.lean
#print set.fintype_bUnion /- def missing doc string -/
#print finset.preimage /- def missing doc string -/
#print set.fintype_insert' /- def missing doc string -/
#print set.fintype_subset /- def missing doc string -/
#print set.fintype_of_fintype_image /- def missing doc string -/
#print set.fintype_bind /- def missing doc string -/

-- data/set/enumerate.lean
#print set.enumerate /- def missing doc string -/

-- data/set/countable.lean
#print set.countable.to_encodable /- def missing doc string -/

-- data/set/basic.lean
#print set.pi /- def missing doc string -/

-- data/seq/wseq.lean
#print wseq.cases_on /- def missing doc string -/
#print wseq.bisim_o /- def missing doc string -/
#print wseq.tail.aux /- def missing doc string -/
#print wseq.mem /- def missing doc string -/
#print wseq.destruct_join.aux /- def missing doc string -/
#print wseq.drop.aux /- def missing doc string -/
#print wseq.destruct_append.aux /- def missing doc string -/
#print wseq.lift_rel_o /- def missing doc string -/

-- data/seq/seq.lean
#print seq.is_bisimulation /- def missing doc string -/
#print seq.bisim_o /- def missing doc string -/
#print seq.mem /- def missing doc string -/
#print seq.cases_on /- def missing doc string -/
#print seq.corec.F /- def missing doc string -/

-- data/seq/parallel.lean
#print computation.parallel_rec /- def missing doc string -/
#print computation.parallel.aux1 /- def missing doc string -/
#print computation.parallel.aux2 /- def missing doc string -/

-- data/seq/computation.lean
#print computation.terminates_rec_on /- def missing doc string -/
#print computation.bind.F /- def missing doc string -/
#print computation.mem_rec_on /- def missing doc string -/
#print computation.bind.G /- def missing doc string -/
#print computation.is_bisimulation /- def missing doc string -/
#print computation.bisim_o /- def missing doc string -/
#print computation.cases_on /- def missing doc string -/
#print computation.lift_rel_aux /- def missing doc string -/
#print computation.mem /- def missing doc string -/
#print computation.corec.F /- def missing doc string -/

-- data/semiquot.lean
#print semiquot.get /- def missing doc string -/
#print semiquot.bind /- def missing doc string -/
#print semiquot.map /- def missing doc string -/
#print semiquot.to_trunc /- def missing doc string -/
#print semiquot.lift_on /- def missing doc string -/
#print semiquot.is_pure /- def missing doc string -/
#print semiquot.pure /- def missing doc string -/
#print semiquot.of_trunc /- def missing doc string -/
#print semiquot.blur /- def missing doc string -/
#print semiquot.blur' /- def missing doc string -/
#print semiquot.univ /- def missing doc string -/
#print semiquot.mk /- def missing doc string -/

-- data/real/nnreal.lean
#print nnreal.of_real /- def missing doc string -/

-- data/real/irrational.lean
#print irrational /- def missing doc string -/

-- data/real/cau_seq_completion.lean
#print cau_seq.lim /- def missing doc string -/
#print cau_seq.completion.discrete_field /- def missing doc string -/
#print cau_seq.completion.mk /- def missing doc string -/
#print cau_seq.completion.of_rat /- def missing doc string -/
#print cau_seq.completion.Cauchy /- def missing doc string -/
#print cau_seq.is_complete /- constant missing doc string -/

-- data/real/cau_seq.lean
#print cau_seq.of_eq /- def missing doc string -/
#print cau_seq /- def missing doc string -/
#print cau_seq.inv /- def missing doc string -/

-- data/real/cardinality.lean
#print cardinal.cantor_function_aux /- def missing doc string -/
#print cardinal.cantor_function /- def missing doc string -/

-- data/real/basic.lean
#print real /- def missing doc string -/
#print real.sqrt_aux /- def missing doc string -/
#print real.le /- def missing doc string -/
#print real.sqrt /- def missing doc string -/
#print real.comm_ring_aux /- def missing doc string -/
#print real.mk /- def missing doc string -/
#print real.Inf /- def missing doc string -/
#print real.Sup /- def missing doc string -/
#print real.of_rat /- def missing doc string -/

-- data/rat/order.lean
#print rat.le /- def missing doc string -/
#print rat.nonneg /- def missing doc string -/
#print rat.sqrt /- def missing doc string -/

-- data/rat/basic.lean
#print rat.num_denom_cases_on /- def missing doc string -/
#print rat.repr /- def missing doc string -/
#print rat.mul /- def missing doc string -/
#print rat.neg /- def missing doc string -/
#print rat.inv /- def missing doc string -/
#print rat.add /- def missing doc string -/
#print rat.num_denom_cases_on' /- def missing doc string -/

-- data/quot.lean
#print trunc.rec /- def missing doc string -/
#print quotient.out' /- def missing doc string -/
#print quotient.choice /- def missing doc string -/
#print trunc.rec_on /- def missing doc string -/
#print trunc.bind /- def missing doc string -/
#print trunc.rec_on_subsingleton /- def missing doc string -/
#print quotient.mk' /- def missing doc string -/
#print trunc.map /- def missing doc string -/
#print quotient.lift_on₂' /- def missing doc string -/
#print quotient.hrec_on₂ /- def missing doc string -/
#print quotient.lift_on' /- def missing doc string -/
#print trunc.lift_on /- def missing doc string -/
#print quot.hrec_on₂ /- def missing doc string -/

-- data/polynomial.lean
#print polynomial.nonzero_comm_ring.of_polynomial_ne /- def missing doc string -/
#print polynomial.div /- def missing doc string -/
#print polynomial.coeff_coe_to_fun /- def missing doc string -/
#print polynomial.pow_sub_pow_factor /- def missing doc string -/
#print polynomial.root_multiplicity /- def missing doc string -/
#print polynomial.pow_add_expansion /- def missing doc string -/
#print polynomial.comp /- def missing doc string -/
#print polynomial.rec_on_horner /- def missing doc string -/
#print polynomial.div_mod_by_monic_aux /- def missing doc string -/
#print polynomial.nonzero_comm_semiring.of_polynomial_ne /- def missing doc string -/
#print polynomial.mod /- def missing doc string -/
#print polynomial.lcoeff /- def missing doc string -/
#print polynomial.binom_expansion /- def missing doc string -/
#print polynomial.decidable_dvd_monic /- def missing doc string -/
#print polynomial.eval_sub_factor /- def missing doc string -/

-- data/pnat/xgcd.lean
#print pnat.xgcd /- def missing doc string -/
#print pnat.xgcd_type.qp /- def missing doc string -/
#print pnat.gcd_x /- def missing doc string -/
#print pnat.xgcd_type.is_reduced' /- def missing doc string -/
#print pnat.gcd_y /- def missing doc string -/
#print pnat.xgcd_type.q /- def missing doc string -/
#print pnat.gcd_w /- def missing doc string -/
#print pnat.xgcd_type.mk' /- def missing doc string -/
#print pnat.xgcd_type.b /- def missing doc string -/
#print pnat.gcd_z /- def missing doc string -/
#print pnat.gcd_d /- def missing doc string -/
#print pnat.xgcd_type.z /- def missing doc string -/
#print pnat.xgcd_type.r /- def missing doc string -/
#print pnat.xgcd_type.succ₂ /- def missing doc string -/
#print pnat.gcd_a' /- def missing doc string -/
#print pnat.xgcd_type.is_special' /- def missing doc string -/
#print pnat.gcd_b' /- def missing doc string -/
#print pnat.xgcd_type.finish /- def missing doc string -/
#print pnat.xgcd_type.v /- def missing doc string -/
#print pnat.xgcd_type.flip /- def missing doc string -/
#print pnat.xgcd_type.w /- def missing doc string -/
#print pnat.xgcd_type.a /- def missing doc string -/

-- data/pnat/factors.lean
#print prime_multiset.prod /- def missing doc string -/
#print prime_multiset.of_pnat_list /- def missing doc string -/
#print prime_multiset.to_pnat_multiset /- def missing doc string -/
#print prime_multiset.of_nat_multiset /- def missing doc string -/
#print prime_multiset.of_pnat_multiset /- def missing doc string -/

-- data/pnat/basic.lean
#print pnat.gcd /- def missing doc string -/
#print pnat.prime /- def missing doc string -/
#print pnat.div_exact /- def missing doc string -/
#print pnat.lcm /- def missing doc string -/
#print pnat.mod /- def missing doc string -/
#print pnat.mod_div /- def missing doc string -/
#print pnat.div /- def missing doc string -/

-- data/pfun.lean
#print pfun.fix_induction /- def missing doc string -/
#print roption.restrict /- def missing doc string -/
#print pfun.image /- def missing doc string -/
#print pfun.graph' /- def missing doc string -/
#print pfun.res /- def missing doc string -/
#print pfun.core /- def missing doc string -/
#print roption.get_or_else /- def missing doc string -/
#print roption.equiv_option /- def missing doc string -/
#print pfun.fix /- def missing doc string -/
#print pfun.equiv_subtype /- def missing doc string -/
#print pfun.preimage /- def missing doc string -/

-- data/pequiv.lean
#print pequiv.symm /- def missing doc string -/
#print pequiv.trans /- def missing doc string -/
#print pequiv.of_set /- def missing doc string -/
#print pequiv.refl /- def missing doc string -/
#print pequiv.single /- def missing doc string -/
#print equiv.to_pequiv /- def missing doc string -/

-- data/padics/padic_numbers.lean
#print padic.lim_seq /- def missing doc string -/
#print padic_norm_e.rat_norm /- def missing doc string -/

-- data/padics/padic_integers.lean
#print padic_norm_z /- def missing doc string -/

-- data/option/defs.lean
#print option.lift_or_get /- def missing doc string -/
#print option.rel /- constant missing doc string -/
#print option.traverse /- def missing doc string -/
#print option.to_list /- def missing doc string -/

-- data/opposite.lean
#print opposite.op /- def missing doc string -/
#print tactic.op_induction' /- def missing doc string -/
#print opposite.op_induction /- def missing doc string -/
#print tactic.op_induction /- def missing doc string -/
#print tactic.op_induction.is_opposite /- def missing doc string -/
#print tactic.op_induction.find_opposite_hyp /- def missing doc string -/
#print tactic.interactive.op_induction /- def missing doc string -/
#print opposite.unop /- def missing doc string -/

-- data/num/lemmas.lean
#print num.transfer /- def missing doc string -/
#print num.transfer_rw /- def missing doc string -/
#print pos_num.transfer /- def missing doc string -/
#print pos_num.transfer_rw /- def missing doc string -/
#print znum.transfer /- def missing doc string -/
#print znum.transfer_rw /- def missing doc string -/
#print int.of_snum /- def missing doc string -/

-- data/num/bitwise.lean
#print num.ldiff /- def missing doc string -/
#print pos_num.lxor /- def missing doc string -/
#print pos_num.test_bit /- def missing doc string -/
#print snum.add /- def missing doc string -/
#print snum.not /- def missing doc string -/
#print nzsnum.tail /- def missing doc string -/
#print pos_num.land /- def missing doc string -/
#print snum.bit0 /- def missing doc string -/
#print snum.bit /- def missing doc string -/
#print snum.pred /- def missing doc string -/
#print num.land /- def missing doc string -/
#print num.lxor /- def missing doc string -/
#print nzsnum.head /- def missing doc string -/
#print snum.drec' /- def missing doc string -/
#print snum.czadd /- def missing doc string -/
#print snum.succ /- def missing doc string -/
#print snum.test_bit /- def missing doc string -/
#print snum.sub /- def missing doc string -/
#print snum.bits /- def missing doc string -/
#print snum.neg /- def missing doc string -/
#print nzsnum.bit0 /- def missing doc string -/
#print nzsnum.sign /- def missing doc string -/
#print pos_num.shiftl /- def missing doc string -/
#print num.lor /- def missing doc string -/
#print pos_num.lor /- def missing doc string -/
#print nzsnum.not /- def missing doc string -/
#print pos_num.shiftr /- def missing doc string -/
#print pos_num.ldiff /- def missing doc string -/
#print snum.rec' /- def missing doc string -/
#print num.one_bits /- def missing doc string -/
#print snum.sign /- def missing doc string -/
#print nzsnum.bit1 /- def missing doc string -/
#print num.shiftl /- def missing doc string -/
#print snum.cadd /- def missing doc string -/
#print nzsnum.drec' /- def missing doc string -/
#print snum.bit1 /- def missing doc string -/
#print snum.head /- def missing doc string -/
#print num.shiftr /- def missing doc string -/
#print num.test_bit /- def missing doc string -/
#print snum.tail /- def missing doc string -/
#print snum.mul /- def missing doc string -/
#print pos_num.one_bits /- def missing doc string -/

-- data/num/basic.lean
#print pos_num.succ /- def missing doc string -/
#print cast_pos_num /- def missing doc string -/
#print pos_num.mod' /- def missing doc string -/
#print pos_num.pred' /- def missing doc string -/
#print num.gcd /- def missing doc string -/
#print num.div /- def missing doc string -/
#print num.mul /- def missing doc string -/
#print pos_num.size /- def missing doc string -/
#print pos_num.div' /- def missing doc string -/
#print pos_num.divmod /- def missing doc string -/
#print pos_num.sub /- def missing doc string -/
#print cast_num /- def missing doc string -/
#print znum.succ /- def missing doc string -/
#print num.mod /- def missing doc string -/
#print cast_znum /- def missing doc string -/
#print znum.pred /- def missing doc string -/
#print num.succ /- def missing doc string -/
#print pos_num.pred /- def missing doc string -/
#print num.to_znum_neg /- def missing doc string -/
#print num.of_znum' /- def missing doc string -/
#print znum.bitm1 /- def missing doc string -/
#print znum.add /- def missing doc string -/
#print pos_num.mul /- def missing doc string -/
#print pos_num.nat_size /- def missing doc string -/
#print num.bit /- def missing doc string -/
#print pos_num.cmp /- def missing doc string -/
#print num.add /- def missing doc string -/
#print num.nat_size /- def missing doc string -/
#print znum.gcd /- def missing doc string -/
#print pos_num.of_nat_succ /- def missing doc string -/
#print znum.mod /- def missing doc string -/
#print num.bit0 /- def missing doc string -/
#print num.of_znum /- def missing doc string -/
#print pos_num.is_one /- def missing doc string -/
#print znum.bit1 /- def missing doc string -/
#print znum.cmp /- def missing doc string -/
#print pos_num.of_nat /- def missing doc string -/
#print num.cmp /- def missing doc string -/
#print num.psub /- def missing doc string -/
#print znum.zneg /- def missing doc string -/
#print znum.div /- def missing doc string -/
#print pos_num.add /- def missing doc string -/
#print num.of_nat' /- def missing doc string -/
#print num.div2 /- def missing doc string -/
#print pos_num.of_znum /- def missing doc string -/
#print znum.mul /- def missing doc string -/
#print num.size /- def missing doc string -/
#print znum.of_int' /- def missing doc string -/
#print pos_num.sqrt_aux1 /- def missing doc string -/
#print num.to_znum /- def missing doc string -/
#print pos_num.bit /- def missing doc string -/
#print num.sub /- def missing doc string -/
#print znum.abs /- def missing doc string -/
#print num.ppred /- def missing doc string -/
#print pos_num.divmod_aux /- def missing doc string -/
#print num.pred /- def missing doc string -/
#print num.gcd_aux /- def missing doc string -/
#print num.bit1 /- def missing doc string -/
#print znum.bit0 /- def missing doc string -/
#print pos_num.sub' /- def missing doc string -/
#print pos_num.of_znum' /- def missing doc string -/
#print pos_num.sqrt_aux /- def missing doc string -/
#print num.sub' /- def missing doc string -/
#print num.succ' /- def missing doc string -/

-- data/nat/totient.lean
#print nat.totient /- def missing doc string -/

-- data/nat/sqrt.lean
#print nat.sqrt_aux /- def missing doc string -/

-- data/nat/prime.lean
#print nat.min_fac_aux /- def missing doc string -/

-- data/nat/parity.lean
#print nat.even /- def missing doc string -/

-- data/nat/modeq.lean
#print nat.modeq.chinese_remainder /- def missing doc string -/

-- data/nat/enat.lean
#print enat /- def missing doc string -/

-- data/multiset.lean
#print multiset.strong_induction_on /- def missing doc string -/
#print multiset.subsingleton_equiv /- def missing doc string -/
#print multiset.powerset_aux' /- def missing doc string -/
#print multiset.choose_x /- def missing doc string -/
#print multiset.pi.cons /- def missing doc string -/
#print multiset.sum /- def missing doc string -/
#print multiset.decidable_exists_multiset /- def missing doc string -/
#print multiset.traverse /- def missing doc string -/
#print multiset.powerset_len_aux /- def missing doc string -/
#print multiset.powerset_len /- def missing doc string -/
#print multiset.powerset_aux /- def missing doc string -/
#print multiset.pi.empty /- def missing doc string -/
#print multiset.decidable_forall_multiset /- def missing doc string -/
#print multiset.powerset /- def missing doc string -/
#print multiset.choose /- def missing doc string -/
#print multiset.rec_on /- def missing doc string -/
#print multiset.sections /- def missing doc string -/

-- data/mllist.lean
#print tactic.mllist.m_of_list /- def missing doc string -/
#print tactic.mllist.empty /- def missing doc string -/
#print tactic.mllist.head /- def missing doc string -/
#print tactic.mllist.force /- def missing doc string -/
#print tactic.mllist.enum_from /- def missing doc string -/
#print tactic.mllist.map /- def missing doc string -/
#print tactic.mllist.enum /- def missing doc string -/
#print tactic.mllist.filter /- def missing doc string -/
#print tactic.mllist.fix /- def missing doc string -/
#print tactic.mllist.squash /- def missing doc string -/
#print tactic.mllist.range /- def missing doc string -/
#print tactic.mllist.concat /- def missing doc string -/
#print tactic.mllist.of_list /- def missing doc string -/
#print tactic.mllist.fixl_with /- def missing doc string -/
#print tactic.mllist.bind_ /- def missing doc string -/
#print tactic.mllist /- constant missing doc string -/
#print tactic.mllist.uncons /- def missing doc string -/
#print tactic.mllist.mmap /- def missing doc string -/
#print tactic.mllist.filter_map /- def missing doc string -/
#print tactic.mllist.monad_lift /- def missing doc string -/
#print tactic.mllist.join /- def missing doc string -/
#print tactic.mllist.mfirst /- def missing doc string -/
#print tactic.mllist.take /- def missing doc string -/
#print tactic.mllist.mfilter /- def missing doc string -/
#print tactic.mllist.append /- def missing doc string -/
#print tactic.mllist.mfilter_map /- def missing doc string -/
#print tactic.mllist.fixl /- def missing doc string -/

-- data/matrix/basic.lean
#print matrix.transpose /- def missing doc string -/
#print matrix.sub_up_right /- def missing doc string -/
#print matrix.minor /- def missing doc string -/
#print matrix.mul /- def missing doc string -/
#print matrix.sub_up_left /- def missing doc string -/
#print matrix.sub_down /- def missing doc string -/
#print matrix.vec_mul /- def missing doc string -/
#print matrix.mul_vec /- def missing doc string -/
#print matrix.diagonal /- def missing doc string -/
#print matrix.sub_down_left /- def missing doc string -/
#print matrix.row /- def missing doc string -/
#print matrix /- def missing doc string -/
#print matrix.sub_right /- def missing doc string -/
#print matrix.vec_mul_vec /- def missing doc string -/
#print matrix.sub_left /- def missing doc string -/
#print matrix.col /- def missing doc string -/
#print matrix.sub_down_right /- def missing doc string -/
#print matrix.sub_up /- def missing doc string -/

-- data/list/sigma.lean
#print list.nodupkeys /- def missing doc string -/
#print list.erase_dupkeys /- def missing doc string -/
#print list.kextract /- def missing doc string -/
#print list.kreplace /- def missing doc string -/

-- data/list/defs.lean
#print list.permutations_aux2 /- def missing doc string -/
#print list.split_on_p_aux /- def missing doc string -/
#print list.transpose_aux /- def missing doc string -/
#print list.func.neg /- def missing doc string -/
#print list.func.sub /- def missing doc string -/
#print list.of_fn /- def missing doc string -/
#print list.sublists_aux₁ /- def missing doc string -/
#print list.func.set /- def missing doc string -/
#print list.scanr_aux /- def missing doc string -/
#print list.func.equiv /- def missing doc string -/
#print list.erasep /- def missing doc string -/
#print list.choose_x /- def missing doc string -/
#print list.extractp /- def missing doc string -/
#print list.revzip /- def missing doc string -/
#print list.map_with_index /- def missing doc string -/
#print list.find_indexes_aux /- def missing doc string -/
#print list.choose /- def missing doc string -/
#print list.of_fn_nth_val /- def missing doc string -/
#print list.func.pointwise /- def missing doc string -/
#print list.sublists_aux /- def missing doc string -/
#print list.forall₂ /- constant missing doc string -/
#print list.of_fn_aux /- def missing doc string -/
#print list.tfae /- def missing doc string -/
#print list.map_with_index_core /- def missing doc string -/
#print list.reduce_option /- def missing doc string -/
#print list.head' /- def missing doc string -/
#print list.map_last /- def missing doc string -/
#print list.permutations_aux /- def missing doc string -/
#print list.sublists'_aux /- def missing doc string -/
#print list.take' /- def missing doc string -/
#print list.func.get /- def missing doc string -/
#print list.map_head /- def missing doc string -/
#print list.partition_map /- def missing doc string -/
#print list.func.add /- def missing doc string -/
#print list.traverse /- def missing doc string -/
#print list.insert_nth /- def missing doc string -/
#print list.permutations_aux.rec /- def missing doc string -/

-- data/list/basic.lean
#print list.sublists_len /- def missing doc string -/
#print list.sublists_len_aux /- def missing doc string -/
#print list.reverse_rec_on /- def missing doc string -/
#print list.lex /- constant missing doc string -/

-- data/list/alist.lean
#print alist.disjoint /- def missing doc string -/
#print list.to_alist /- def missing doc string -/

-- data/lazy_list2.lean
#print lazy_list.traverse /- def missing doc string -/
#print lazy_list.thunk.mk /- def missing doc string -/
#print lazy_list.list_equiv_lazy_list /- def missing doc string -/

-- data/int/parity.lean
#print int.even /- def missing doc string -/

-- data/int/modeq.lean
#print int.modeq /- def missing doc string -/

-- data/int/gcd.lean
#print nat.xgcd_aux /- def missing doc string -/

-- data/int/basic.lean
#print int.to_nat' /- def missing doc string -/
#print int.induction_on' /- def missing doc string -/
#print int.bit_cases_on /- def missing doc string -/
#print int.range /- def missing doc string -/

-- data/holor.lean
#print holor_index.assoc_left /- def missing doc string -/
#print holor.assoc_right /- def missing doc string -/
#print holor_index.take /- def missing doc string -/
#print holor_index.drop /- def missing doc string -/
#print holor_index.assoc_right /- def missing doc string -/
#print holor.assoc_left /- def missing doc string -/

-- data/fp/basic.lean
#print fp.emax /- def missing doc string -/
#print fp.float.div /- def missing doc string -/
#print fp.float.is_finite /- def missing doc string -/
#print fp.float.neg /- def missing doc string -/
#print fp.float.add /- def missing doc string -/
#print fp.of_rat_up /- def missing doc string -/
#print fp.next_dn_pos /- def missing doc string -/
#print fp.float.is_zero /- def missing doc string -/
#print int.shift2 /- def missing doc string -/
#print fp.next_up /- def missing doc string -/
#print fp.to_rat /- def missing doc string -/
#print fp.div_nat_lt_two_pow /- def missing doc string -/
#print fp.valid_finite /- def missing doc string -/
#print fp.of_pos_rat_dn /- def missing doc string -/
#print fp.float_cfg /- constant missing doc string -/
#print fp.float.sign' /- def missing doc string -/
#print fp.float.sub /- def missing doc string -/
#print fp.rmode /- constant missing doc string -/
#print fp.prec /- def missing doc string -/
#print fp.of_rat_dn /- def missing doc string -/
#print fp.next_dn /- def missing doc string -/
#print fp.emin /- def missing doc string -/
#print fp.of_rat /- def missing doc string -/
#print fp.float.sign /- def missing doc string -/
#print fp.float.zero /- def missing doc string -/
#print fp.next_up_pos /- def missing doc string -/
#print fp.float.mul /- def missing doc string -/
#print fp.float /- constant missing doc string -/

-- data/fintype.lean
#print quotient.fin_choice_aux /- def missing doc string -/
#print perms_of_finset /- def missing doc string -/
#print fintype.choose /- def missing doc string -/
#print fintype_perm /- def missing doc string -/
#print finset.insert_none /- def missing doc string -/
#print fintype.of_subsingleton /- def missing doc string -/
#print infinite.nat_embedding /- def missing doc string -/
#print infinite /- constant missing doc string -/
#print fintype.choose_x /- def missing doc string -/
#print fintype.of_injective /- def missing doc string -/
#print fintype.fintype_prod_left /- def missing doc string -/
#print fintype.subtype /- def missing doc string -/
#print fintype.fintype_prod_right /- def missing doc string -/
#print set_fintype /- def missing doc string -/
#print quotient.fin_choice /- def missing doc string -/
#print perms_of_list /- def missing doc string -/

-- data/finsupp.lean
#print finsupp.uncurry /- def missing doc string -/
#print finsupp.antidiagonal /- def missing doc string -/
#print finsupp.equiv_multiset /- def missing doc string -/
#print finsupp.split_comp /- def missing doc string -/
#print multiset.to_finsupp /- def missing doc string -/
#print finsupp.erase /- def missing doc string -/
#print finsupp.comap_domain /- def missing doc string -/
#print finsupp.curry /- def missing doc string -/
#print finsupp.finsupp_prod_equiv /- def missing doc string -/
#print finsupp.frange /- def missing doc string -/
#print finsupp.restrict_support_equiv /- def missing doc string -/
#print finsupp.split /- def missing doc string -/
#print finsupp.equiv_fun_on_fintype /- def missing doc string -/
#print finsupp.split_support /- def missing doc string -/
#print finsupp.to_multiset /- def missing doc string -/
#print finsupp.of_multiset /- def missing doc string -/
#print finsupp.dom_congr /- def missing doc string -/

-- data/finset.lean
#print finset.pi /- def missing doc string -/
#print finset.subtype /- def missing doc string -/
#print finset.powerset_len /- def missing doc string -/
#print finset.strong_induction_on /- def missing doc string -/
#print finset.max' /- def missing doc string -/
#print finset.min' /- def missing doc string -/
#print finset.max /- def missing doc string -/
#print finset.map_embedding /- def missing doc string -/
#print finset.map /- def missing doc string -/
#print finset.pi.empty /- def missing doc string -/
#print finset.attach_fin /- def missing doc string -/
#print finset.pi.cons /- def missing doc string -/
#print finset.powerset /- def missing doc string -/
#print finset.empty /- def missing doc string -/
#print finset.choose_x /- def missing doc string -/
#print finset.min /- def missing doc string -/
#print finset.choose /- def missing doc string -/

-- data/finmap.lean
#print finmap.sdiff /- def missing doc string -/
#print finmap.disjoint /- def missing doc string -/
#print finmap.any /- def missing doc string -/
#print finmap.all /- def missing doc string -/
#print list.to_finmap /- def missing doc string -/

-- data/fin.lean
#print fin_zero_elim' /- def missing doc string -/
#print fin.tail /- def missing doc string -/
#print fin.cases /- def missing doc string -/
#print fin.clamp /- def missing doc string -/
#print fin.find /- def missing doc string -/
#print fin.succ_rec_on /- def missing doc string -/
#print fin.succ_rec /- def missing doc string -/
#print fin.cons /- def missing doc string -/

-- data/erased.lean
#print erased.out_type /- def missing doc string -/
#print erased.out /- def missing doc string -/
#print erased.bind /- def missing doc string -/
#print erased.equiv /- def missing doc string -/
#print erased.join /- def missing doc string -/
#print erased.choice /- def missing doc string -/
#print erased.mk /- def missing doc string -/

-- data/equiv/nat.lean
#print equiv.nat_sum_nat_equiv_nat /- def missing doc string -/
#print equiv.int_equiv_nat /- def missing doc string -/
#print equiv.bool_prod_nat_equiv_nat /- def missing doc string -/
#print equiv.pnat_equiv_nat /- def missing doc string -/
#print equiv.prod_equiv_of_equiv_nat /- def missing doc string -/
#print equiv.nat_prod_nat_equiv_nat /- def missing doc string -/

-- data/equiv/list.lean
#print denumerable.raise'_finset /- def missing doc string -/
#print encodable.encode_list /- def missing doc string -/
#print equiv.list_equiv_self_of_equiv_nat /- def missing doc string -/
#print denumerable.lower /- def missing doc string -/
#print denumerable.raise /- def missing doc string -/
#print encodable.encodable_of_list /- def missing doc string -/
#print denumerable.raise' /- def missing doc string -/
#print denumerable.lower' /- def missing doc string -/
#print encodable.fintype_pi /- def missing doc string -/
#print encodable.decode_list /- def missing doc string -/
#print encodable.decode_multiset /- def missing doc string -/
#print encodable.fintype_arrow /- def missing doc string -/
#print encodable.trunc_encodable_of_fintype /- def missing doc string -/
#print equiv.list_nat_equiv_nat /- def missing doc string -/
#print encodable.encode_multiset /- def missing doc string -/

-- data/equiv/functor.lean
#print functor.map_equiv /- def missing doc string -/

-- data/equiv/fin.lean
#print fin_two_equiv /- def missing doc string -/
#print fin_one_equiv /- def missing doc string -/
#print fin_zero_equiv /- def missing doc string -/
#print sum_fin_sum_equiv /- def missing doc string -/
#print fin_prod_fin_equiv /- def missing doc string -/

-- data/equiv/encodable.lean
#print encodable.choose_x /- def missing doc string -/
#print quot.encodable_quotient /- def missing doc string -/
#print encodable.choose /- def missing doc string -/
#print encodable.of_left_injection /- def missing doc string -/
#print encodable.decode_sum /- def missing doc string -/
#print encodable.decode2 /- def missing doc string -/
#print encodable.decode_sigma /- def missing doc string -/
#print encodable.decidable_eq_of_encodable /- def missing doc string -/
#print encodable.encode_sum /- def missing doc string -/
#print quot.rep /- def missing doc string -/
#print encodable.of_left_inverse /- def missing doc string -/
#print encodable.encode_subtype /- def missing doc string -/
#print encodable.equiv_range_encode /- def missing doc string -/
#print encodable.of_equiv /- def missing doc string -/
#print encodable.of_inj /- def missing doc string -/
#print encodable.decidable_range_encode /- def missing doc string -/
#print encodable.decode_subtype /- def missing doc string -/
#print encodable.encode_sigma /- def missing doc string -/

-- data/equiv/denumerable.lean
#print denumerable.pair /- def missing doc string -/
#print denumerable.of_equiv /- def missing doc string -/
#print nat.subtype.of_nat /- def missing doc string -/
#print denumerable.equiv₂ /- def missing doc string -/
#print nat.subtype.denumerable /- def missing doc string -/
#print denumerable.eqv /- def missing doc string -/
#print denumerable.mk' /- def missing doc string -/
#print nat.subtype.succ /- def missing doc string -/
#print denumerable.of_encodable_of_infinite /- def missing doc string -/
#print denumerable.of_nat /- def missing doc string -/

-- data/equiv/basic.lean
#print equiv.prod_comm /- def missing doc string -/
#print equiv.psigma_equiv_sigma /- def missing doc string -/
#print equiv_punit_of_unique /- def missing doc string -/
#print equiv.conj /- def missing doc string -/
#print equiv.punit_arrow_equiv /- def missing doc string -/
#print equiv.equiv_congr /- def missing doc string -/
#print equiv.sum_empty /- def missing doc string -/
#print equiv.set.range /- def missing doc string -/
#print equiv.empty_of_not_nonempty /- def missing doc string -/
#print equiv.psum_equiv_sum /- def missing doc string -/
#print equiv.set.union_sum_inter /- def missing doc string -/
#print equiv.prod_empty /- def missing doc string -/
#print equiv.set.insert /- def missing doc string -/
#print equiv.sigma_equiv_prod /- def missing doc string -/
#print equiv.subtype_equiv_of_subtype' /- def missing doc string -/
#print equiv.set.union' /- def missing doc string -/
#print equiv.arrow_prod_equiv_prod_arrow /- def missing doc string -/
#print equiv.prod_congr /- def missing doc string -/
#print equiv.set.empty /- def missing doc string -/
#print equiv.bool_prod_equiv_sum /- def missing doc string -/
#print equiv.punit_prod /- def missing doc string -/
#print equiv.prod_punit /- def missing doc string -/
#print equiv.arrow_arrow_equiv_prod_arrow /- def missing doc string -/
#print equiv.sigma_prod_distrib /- def missing doc string -/
#print equiv.subtype_subtype_equiv_subtype_inter /- def missing doc string -/
#print equiv.set.image_of_inj_on /- def missing doc string -/
#print equiv.inhabited_of_equiv /- def missing doc string -/
#print equiv.set.congr /- def missing doc string -/
#print equiv.prop_equiv_punit /- def missing doc string -/
#print equiv.empty_equiv_pempty /- def missing doc string -/
#print equiv.set.singleton /- def missing doc string -/
#print equiv.of_bijective /- def missing doc string -/
#print equiv.subtype_congr_prop /- def missing doc string -/
#print equiv.sigma_preimage_equiv /- def missing doc string -/
#print equiv.sum_arrow_equiv_prod_arrow /- def missing doc string -/
#print equiv.sum_equiv_sigma_bool /- def missing doc string -/
#print equiv.set.image /- def missing doc string -/
#print equiv.Prop_equiv_bool /- def missing doc string -/
#print equiv.swap_core /- def missing doc string -/
#print equiv.empty_sum /- def missing doc string -/
#print equiv.pempty_prod /- def missing doc string -/
#print equiv.set.pempty /- def missing doc string -/
#print equiv.decidable_eq_of_equiv /- def missing doc string -/
#print equiv.equiv_pempty /- def missing doc string -/
#print equiv.plift /- def missing doc string -/
#print equiv.sigma_congr_right /- def missing doc string -/
#print equiv.sigma_subtype_preimage_equiv /- def missing doc string -/
#print equiv.nat_equiv_nat_sum_punit /- def missing doc string -/
#print equiv.set.prod /- def missing doc string -/
#print equiv.set.univ /- def missing doc string -/
#print equiv.prod_assoc /- def missing doc string -/
#print unique_unique_equiv /- def missing doc string -/
#print equiv.cast /- def missing doc string -/
#print equiv.bool_equiv_punit_sum_punit /- def missing doc string -/
#print equiv.subtype_pi_equiv_pi /- def missing doc string -/
#print equiv.symm /- def missing doc string -/
#print equiv.list_equiv_of_equiv /- def missing doc string -/
#print equiv.punit_equiv_punit /- def missing doc string -/
#print equiv.subtype_quotient_equiv_quotient_subtype /- def missing doc string -/
#print equiv.decidable_eq /- def missing doc string -/
#print equiv.subtype_subtype_equiv_subtype_exists /- def missing doc string -/
#print equiv.arrow_congr /- def missing doc string -/
#print equiv.prod_pempty /- def missing doc string -/
#print equiv.nat_sum_punit_equiv_nat /- def missing doc string -/
#print equiv.false_arrow_equiv_punit /- def missing doc string -/
#print equiv.sum_assoc /- def missing doc string -/
#print equiv.set_congr /- def missing doc string -/
#print equiv.unique_congr /- def missing doc string -/
#print equiv.pempty_arrow_equiv_punit /- def missing doc string -/
#print equiv.pi_equiv_subtype_sigma /- def missing doc string -/
#print equiv.Pi_curry /- def missing doc string -/
#print equiv.prod_sum_distrib /- def missing doc string -/
#print equiv.false_equiv_empty /- def missing doc string -/
#print equiv.set.of_eq /- def missing doc string -/
#print equiv.arrow_punit_equiv_punit /- def missing doc string -/
#print equiv.ulift /- def missing doc string -/
#print equiv.sum_prod_distrib /- def missing doc string -/
#print function.involutive.to_equiv /- def missing doc string -/
#print equiv.true_equiv_punit /- def missing doc string -/
#print equiv.sum_congr /- def missing doc string -/
#print equiv.sum_comm /- def missing doc string -/
#print equiv.equiv_empty /- def missing doc string -/
#print equiv.empty_prod /- def missing doc string -/
#print equiv.subtype_congr_right /- def missing doc string -/
#print equiv.sum_pempty /- def missing doc string -/
#print equiv.trans /- def missing doc string -/
#print equiv.pempty_of_not_nonempty /- def missing doc string -/
#print equiv.option_equiv_sum_punit /- def missing doc string -/
#print equiv.subtype_congr /- def missing doc string -/
#print equiv.int_equiv_nat_sum_nat /- def missing doc string -/
#print equiv.sigma_congr_left /- def missing doc string -/
#print equiv.set.union /- def missing doc string -/
#print equiv.set.sep /- def missing doc string -/
#print equiv.refl /- def missing doc string -/
#print equiv.sigma_equiv_prod_of_equiv /- def missing doc string -/
#print equiv.sigma_subtype_preimage_equiv_subtype /- def missing doc string -/
#print equiv.set.sum_compl /- def missing doc string -/
#print equiv.Pi_congr_right /- def missing doc string -/
#print equiv.perm_congr /- def missing doc string -/
#print equiv.false_equiv_pempty /- def missing doc string -/
#print equiv.fin_equiv_subtype /- def missing doc string -/
#print equiv.unique_of_equiv /- def missing doc string -/
#print equiv_of_unique_of_unique /- def missing doc string -/
#print equiv.pempty_equiv_pempty /- def missing doc string -/
#print equiv.pempty_sum /- def missing doc string -/
#print equiv.empty_arrow_equiv_punit /- def missing doc string -/

-- data/equiv/algebra.lean
#print add_equiv.refl /- def missing doc string -/
#print add_equiv.symm /- def missing doc string -/
#print equiv.comm_monoid /- def missing doc string -/
#print add_equiv.to_equiv /- def missing doc string -/
#print equiv.has_one /- def missing doc string -/
#print equiv.has_zero /- def missing doc string -/
#print equiv.ring /- def missing doc string -/
#print equiv.neg /- def missing doc string -/
#print equiv.has_add /- def missing doc string -/
#print equiv.add_left /- def missing doc string -/
#print add_equiv.mk' /- def missing doc string -/
#print equiv.add_comm_monoid /- def missing doc string -/
#print equiv.add_monoid /- def missing doc string -/
#print equiv.has_mul /- def missing doc string -/
#print equiv.units_equiv_ne_zero /- def missing doc string -/
#print equiv.monoid /- def missing doc string -/
#print units.map_equiv /- def missing doc string -/
#print equiv.add_comm_group /- def missing doc string -/
#print equiv.group /- def missing doc string -/
#print equiv.discrete_field /- def missing doc string -/
#print equiv.has_neg /- def missing doc string -/
#print add_equiv.to_add_monoid_hom /- def missing doc string -/
#print equiv.add_group /- def missing doc string -/
#print equiv.integral_domain /- def missing doc string -/
#print equiv.comm_semigroup /- def missing doc string -/
#print equiv.add_comm_semigroup /- def missing doc string -/
#print equiv.comm_ring /- def missing doc string -/
#print ring_equiv /- constant missing doc string -/
#print ring_equiv.to_mul_equiv /- def missing doc string -/
#print equiv.zero_ne_one_class /- def missing doc string -/
#print equiv.semiring /- def missing doc string -/
#print equiv.comm_semiring /- def missing doc string -/
#print add_equiv.trans /- def missing doc string -/
#print equiv.mul_right /- def missing doc string -/
#print ring_equiv.to_add_equiv /- def missing doc string -/
#print equiv.inv /- def missing doc string -/
#print mul_equiv.to_equiv /- def missing doc string -/
#print equiv.add_semigroup /- def missing doc string -/
#print equiv.add_right /- def missing doc string -/
#print equiv.domain /- def missing doc string -/
#print equiv.has_inv /- def missing doc string -/
#print equiv.semigroup /- def missing doc string -/
#print equiv.field /- def missing doc string -/
#print equiv.division_ring /- def missing doc string -/
#print ring_equiv.to_equiv /- def missing doc string -/
#print equiv.comm_group /- def missing doc string -/
#print equiv.nonzero_comm_ring /- def missing doc string -/
#print equiv.mul_left /- def missing doc string -/

-- data/dlist/instances.lean
#print dlist.list_equiv_dlist /- def missing doc string -/

-- data/dlist/basic.lean
#print dlist.join /- def missing doc string -/

-- data/dfinsupp.lean
#print dfinsupp.erase /- def missing doc string -/
#print dfinsupp.zip_with /- def missing doc string -/
#print decidable_zero_symm /- def missing doc string -/
#print dfinsupp.to_has_scalar /- def missing doc string -/
#print dfinsupp.single /- def missing doc string -/
#print dfinsupp.pre /- constant missing doc string -/
#print dfinsupp.mk /- def missing doc string -/
#print dfinsupp.to_module /- def missing doc string -/
#print dfinsupp.lsingle /- def missing doc string -/
#print dfinsupp.lmk /- def missing doc string -/
#print dfinsupp /- def missing doc string -/
#print dfinsupp.support /- def missing doc string -/

-- data/complex/exponential.lean
#print real.exp /- def missing doc string -/
#print complex.exp' /- def missing doc string -/
#print real.tan /- def missing doc string -/
#print complex.cosh /- def missing doc string -/
#print complex.exp /- def missing doc string -/
#print real.cos /- def missing doc string -/
#print real.sin /- def missing doc string -/
#print real.sinh /- def missing doc string -/
#print complex.tan /- def missing doc string -/
#print complex.sin /- def missing doc string -/
#print real.tanh /- def missing doc string -/
#print complex.sinh /- def missing doc string -/
#print real.cosh /- def missing doc string -/
#print complex.cos /- def missing doc string -/
#print complex.tanh /- def missing doc string -/

-- data/complex/basic.lean
#print complex.conj /- def missing doc string -/
#print complex /- constant missing doc string -/
#print complex.cau_seq_conj /- def missing doc string -/
#print complex.cau_seq_im /- def missing doc string -/
#print complex.of_real /- def missing doc string -/
#print complex.abs /- def missing doc string -/
#print complex.I /- def missing doc string -/
#print complex.real_prod_equiv /- def missing doc string -/
#print complex.cau_seq_abs /- def missing doc string -/
#print complex.cau_seq_re /- def missing doc string -/
#print complex.lim_aux /- def missing doc string -/
#print complex.norm_sq /- def missing doc string -/

-- data/buffer/basic.lean
#print buffer.list_equiv_buffer /- def missing doc string -/

-- data/array/lemmas.lean
#print equiv.array_equiv_fin /- def missing doc string -/
#print equiv.vector_equiv_array /- def missing doc string -/
#print equiv.vector_equiv_fin /- def missing doc string -/
#print equiv.d_array_equiv_fin /- def missing doc string -/

-- data/analysis/topology.lean
#print locally_finite.realizer /- constant missing doc string -/
#print ctop.realizer.of_equiv /- def missing doc string -/
#print ctop.to_realizer /- def missing doc string -/
#print ctop.realizer.id /- def missing doc string -/
#print ctop.realizer.nhds /- def missing doc string -/
#print compact.realizer /- def missing doc string -/

-- data/analysis/filter.lean
#print cfilter.to_realizer /- def missing doc string -/
#print filter.realizer.of_eq /- def missing doc string -/

-- computability/turing_machine.lean
#print turing.TM1to1.tr_normal /- def missing doc string -/
#print turing.TM0to1.tr_cfg /- def missing doc string -/
#print turing.tape.write /- def missing doc string -/
#print turing.TM2.eval /- def missing doc string -/
#print turing.TM0.stmt.map /- def missing doc string -/
#print turing.TM2to1.st_act /- constant missing doc string -/
#print turing.TM2to1.stackel.is_top /- def missing doc string -/
#print turing.TM1to1.tr /- def missing doc string -/
#print turing.TM2.init /- def missing doc string -/
#print turing.TM2to1.tr_st_act /- def missing doc string -/
#print turing.TM2to1.st_run /- def missing doc string -/
#print turing.TM2.step /- def missing doc string -/
#print turing.frespects /- def missing doc string -/
#print turing.TM0.cfg.map /- def missing doc string -/
#print turing.TM2to1.st_write /- def missing doc string -/
#print turing.TM1to1.writes /- def missing doc string -/
#print turing.TM2.stmts₁ /- def missing doc string -/
#print turing.TM2to1.stackel.is_bottom /- def missing doc string -/
#print turing.TM2to1.stackel.get /- def missing doc string -/
#print turing.reaches /- def missing doc string -/
#print turing.reaches₁ /- def missing doc string -/
#print turing.TM2to1.tr_normal /- def missing doc string -/
#print turing.TM1to1.tr_cfg /- def missing doc string -/
#print turing.TM2.reaches /- def missing doc string -/
#print turing.TM2to1.Λ' /- constant missing doc string -/
#print turing.TM2.stmts /- def missing doc string -/
#print turing.TM2to1.st_var /- def missing doc string -/
#print turing.tape.mk' /- def missing doc string -/
#print turing.TM1to1.tr_tape /- def missing doc string -/
#print turing.TM0to1.Λ' /- constant missing doc string -/
#print turing.TM2to1.tr_cfg /- constant missing doc string -/
#print turing.TM2.step_aux /- def missing doc string -/
#print turing.tape.move /- def missing doc string -/
#print turing.pointed_map /- def missing doc string -/
#print turing.TM1.stmts₁ /- def missing doc string -/
#print turing.TM1to0.tr_aux /- def missing doc string -/
#print turing.TM1.step /- def missing doc string -/
#print turing.TM2to1.tr_stk /- def missing doc string -/
#print turing.TM1to1.tr_tape' /- def missing doc string -/
#print turing.eval /- def missing doc string -/
#print turing.TM2to1.tr /- def missing doc string -/
#print turing.tape.mk /- def missing doc string -/
#print turing.TM2to1.stackel_equiv /- def missing doc string -/
#print turing.TM0.machine.map /- def missing doc string -/
#print turing.TM1to1.read_aux /- def missing doc string -/
#print turing.TM0to1.tr /- def missing doc string -/
#print turing.TM2to1.stmt_st_rec /- def missing doc string -/
#print turing.tape.map /- def missing doc string -/
#print turing.TM1to0.Λ' /- def missing doc string -/
#print turing.TM1to0.tr_cfg /- def missing doc string -/
#print turing.reaches₀ /- def missing doc string -/
#print turing.TM1.eval /- def missing doc string -/
#print turing.TM2to1.tr_stmts₁ /- def missing doc string -/
#print turing.TM2to1.stackel /- constant missing doc string -/
#print turing.TM1to0.tr_stmts /- def missing doc string -/
#print turing.TM2.supports /- def missing doc string -/
#print turing.TM1.supports_stmt /- def missing doc string -/
#print turing.TM1.stmts /- def missing doc string -/
#print turing.TM2to1.Γ' /- def missing doc string -/
#print turing.TM2.cfg /- constant missing doc string -/
#print turing.tape /- def missing doc string -/
#print turing.respects /- def missing doc string -/
#print turing.TM1to1.tr_supp /- def missing doc string -/
#print turing.TM2.supports_stmt /- def missing doc string -/
#print turing.TM1to1.move /- def missing doc string -/
#print turing.dwrite /- def missing doc string -/
#print turing.TM1to0.tr /- def missing doc string -/
#print turing.TM1.init /- def missing doc string -/
#print turing.TM2to1.tr_supp /- def missing doc string -/
#print turing.TM1to1.Λ' /- constant missing doc string -/
#print turing.TM2to1.tr_init /- def missing doc string -/
#print turing.tape.nth /- def missing doc string -/
#print turing.TM1to1.read /- def missing doc string -/
#print turing.TM1to1.write /- def missing doc string -/

-- computability/primrec.lean
#print primcodable.of_equiv /- def missing doc string -/
#print nat.cases /- def missing doc string -/
#print nat.primrec'.vec /- def missing doc string -/
#print nat.elim /- def missing doc string -/
#print nat.unpaired /- def missing doc string -/
#print primcodable.subtype /- def missing doc string -/

-- computability/partrec_code.lean
#print nat.partrec.code.encode_code /- def missing doc string -/
#print nat.partrec.code.const /- def missing doc string -/
#print nat.partrec.code.curry /- def missing doc string -/
#print nat.partrec.code.evaln /- def missing doc string -/
#print nat.partrec.code.of_nat_code /- def missing doc string -/
#print nat.partrec.code /- constant missing doc string -/
#print nat.partrec.code.eval /- def missing doc string -/
#print nat.partrec.code.id /- def missing doc string -/

-- computability/partrec.lean
#print partrec₂ /- def missing doc string -/
#print computable /- def missing doc string -/
#print computable₂ /- def missing doc string -/
#print partrec /- def missing doc string -/
#print nat.partrec /- constant missing doc string -/
#print nat.rfind /- def missing doc string -/
#print nat.rfind_opt /- def missing doc string -/
#print nat.rfind_x /- def missing doc string -/

-- computability/halting.lean
#print computable_pred /- def missing doc string -/
#print re_pred /- def missing doc string -/
#print nat.partrec'.vec /- def missing doc string -/

-- category_theory/yoneda.lean
#print category_theory.yoneda_sections_small /- def missing doc string -/
#print category_theory.coyoneda /- def missing doc string -/
#print category_theory.coyoneda.is_iso /- def missing doc string -/
#print category_theory.yoneda /- def missing doc string -/
#print category_theory.yoneda_pairing /- def missing doc string -/
#print category_theory.representable /- constant missing doc string -/
#print category_theory.yoneda_sections /- def missing doc string -/
#print category_theory.yoneda_evaluation /- def missing doc string -/
#print category_theory.yoneda_lemma /- def missing doc string -/
#print category_theory.yoneda.is_iso /- def missing doc string -/

-- category_theory/whiskering.lean
#print category_theory.iso_whisker_right /- def missing doc string -/
#print category_theory.whisker_right /- def missing doc string -/
#print category_theory.functor.left_unitor /- def missing doc string -/
#print category_theory.iso_whisker_left /- def missing doc string -/
#print category_theory.functor.associator /- def missing doc string -/
#print category_theory.functor.right_unitor /- def missing doc string -/
#print category_theory.whiskering_left /- def missing doc string -/
#print category_theory.whiskering_right /- def missing doc string -/
#print category_theory.whisker_left /- def missing doc string -/

-- category_theory/types.lean
#print equiv.to_iso /- def missing doc string -/
#print category_theory.ulift_trivial /- def missing doc string -/
#print category_theory.functor.sections /- def missing doc string -/
#print category_theory.hom_of_element /- def missing doc string -/
#print category_theory.ulift_functor /- def missing doc string -/
#print category_theory.iso.to_equiv /- def missing doc string -/

-- category_theory/sums/associator.lean
#print category_theory.sum.associator /- def missing doc string -/
#print category_theory.sum.inverse_associator /- def missing doc string -/
#print category_theory.sum.associativity /- def missing doc string -/

-- category_theory/single_obj.lean
#print category_theory.single_obj.star /- def missing doc string -/

-- category_theory/punit.lean
#print category_theory.functor.star /- def missing doc string -/

-- category_theory/products/basic.lean
#print category_theory.evaluation /- def missing doc string -/
#print category_theory.prod.symmetry /- def missing doc string -/
#print category_theory.evaluation_uncurried /- def missing doc string -/
#print category_theory.prod.braiding /- def missing doc string -/
#print category_theory.prod.swap /- def missing doc string -/

-- category_theory/products/associator.lean
#print category_theory.prod.associator /- def missing doc string -/
#print category_theory.prod.inverse_associator /- def missing doc string -/
#print category_theory.prod.associativity /- def missing doc string -/

-- category_theory/opposites.lean
#print category_theory.has_hom.hom.unop /- def missing doc string -/
#print category_theory.functor.unop /- def missing doc string -/
#print category_theory.functor.right_op /- def missing doc string -/
#print category_theory.nat_trans.op /- def missing doc string -/
#print category_theory.nat_trans.unop /- def missing doc string -/
#print category_theory.nat_iso.op /- def missing doc string -/
#print category_theory.functor.left_op /- def missing doc string -/
#print category_theory.functor.op_hom /- def missing doc string -/
#print category_theory.iso.op /- def missing doc string -/
#print category_theory.nat_trans.left_op /- def missing doc string -/
#print category_theory.has_hom.hom.op /- def missing doc string -/
#print category_theory.op_op /- def missing doc string -/
#print category_theory.functor.op_inv /- def missing doc string -/
#print category_theory.functor.op /- def missing doc string -/
#print category_theory.nat_trans.right_op /- def missing doc string -/
#print category_theory.is_iso_of_op /- def missing doc string -/

-- category_theory/natural_isomorphism.lean
#print category_theory.functor.ulift_down_up /- def missing doc string -/
#print category_theory.nat_iso.is_iso_app_of_is_iso /- def missing doc string -/
#print category_theory.nat_iso.of_components /- def missing doc string -/
#print category_theory.functor.ulift_up_down /- def missing doc string -/
#print category_theory.nat_iso.hcomp /- def missing doc string -/
#print category_theory.nat_iso.is_iso_of_is_iso_app /- def missing doc string -/

-- category_theory/monoidal/functor.lean
#print category_theory.monoidal_functor.μ_iso /- def missing doc string -/
#print category_theory.monoidal_functor.ε_iso /- def missing doc string -/

-- category_theory/monad/limits.lean
#print category_theory.monadic_creates_limits /- def missing doc string -/
#print category_theory.monad.forget_creates_limits.γ /- def missing doc string -/
#print category_theory.monad.forget_creates_limits.c /- def missing doc string -/
#print category_theory.monad.forget_creates_limits.cone_point /- def missing doc string -/
#print category_theory.monad.forget_creates_limits /- def missing doc string -/
#print category_theory.has_limits_of_reflective /- def missing doc string -/

-- category_theory/monad/basic.lean
#print category_theory.monad /- constant missing doc string -/

-- category_theory/monad/algebra.lean
#print category_theory.monad.algebra.hom /- constant missing doc string -/
#print category_theory.monad.algebra.hom.comp /- def missing doc string -/
#print category_theory.monad.free /- def missing doc string -/
#print category_theory.monad.forget /- def missing doc string -/
#print category_theory.monad.algebra.hom.id /- def missing doc string -/

-- category_theory/monad/adjunction.lean
#print category_theory.monad.comparison /- def missing doc string -/
#print category_theory.monad.comparison_forget /- def missing doc string -/

-- category_theory/limits/types.lean
#print category_theory.limits.types.limit /- def missing doc string -/
#print category_theory.limits.types.colimit /- def missing doc string -/
#print category_theory.limits.types.limit_is_limit /- def missing doc string -/
#print category_theory.limits.types.colimit_is_colimit /- def missing doc string -/

-- category_theory/limits/shapes/terminal.lean
#print category_theory.limits.terminal.from /- def missing doc string -/
#print category_theory.limits.initial.to /- def missing doc string -/
#print category_theory.limits.terminal /- def missing doc string -/
#print category_theory.limits.has_initial /- constant missing doc string -/
#print category_theory.limits.initial /- def missing doc string -/
#print category_theory.limits.has_terminal /- constant missing doc string -/

-- category_theory/limits/shapes/pullbacks.lean
#print category_theory.limits.cone.of_pullback_cone /- def missing doc string -/
#print category_theory.limits.pullback_cone.mk /- def missing doc string -/
#print category_theory.limits.pushout_cocone.of_cocone /- def missing doc string -/
#print category_theory.limits.pushout.inr /- def missing doc string -/
#print category_theory.limits.pullback_cone.of_cone /- def missing doc string -/
#print category_theory.limits.pullback.lift /- def missing doc string -/
#print category_theory.limits.pushout.desc /- def missing doc string -/
#print category_theory.limits.pushout_cocone.inl /- def missing doc string -/
#print category_theory.limits.pushout_cocone.mk /- def missing doc string -/
#print category_theory.limits.pushout_cocone.inr /- def missing doc string -/
#print category_theory.limits.pullback.snd /- def missing doc string -/
#print category_theory.limits.walking_span.hom.comp /- def missing doc string -/
#print category_theory.limits.pullback_cone /- def missing doc string -/
#print category_theory.limits.walking_cospan.hom.comp /- def missing doc string -/
#print category_theory.limits.has_pullbacks /- constant missing doc string -/
#print category_theory.limits.pullback.fst /- def missing doc string -/
#print category_theory.limits.pullback_cone.fst /- def missing doc string -/
#print category_theory.limits.has_pushouts /- constant missing doc string -/
#print category_theory.limits.pushout.inl /- def missing doc string -/
#print category_theory.limits.pullback_cone.snd /- def missing doc string -/
#print category_theory.limits.pushout_cocone /- def missing doc string -/
#print category_theory.limits.cocone.of_pushout_cocone /- def missing doc string -/

-- category_theory/limits/shapes/products.lean
#print category_theory.limits.pi.π /- def missing doc string -/
#print category_theory.limits.has_coproducts /- constant missing doc string -/
#print category_theory.limits.pi.lift /- def missing doc string -/
#print category_theory.limits.sigma.ι /- def missing doc string -/
#print category_theory.limits.sigma.map /- def missing doc string -/
#print category_theory.limits.fan.mk /- def missing doc string -/
#print category_theory.limits.has_products /- constant missing doc string -/
#print category_theory.limits.pi.map /- def missing doc string -/
#print category_theory.limits.fan /- def missing doc string -/
#print category_theory.limits.cofan /- def missing doc string -/
#print category_theory.limits.sigma.desc /- def missing doc string -/
#print category_theory.limits.cofan.mk /- def missing doc string -/

-- category_theory/limits/shapes/finite_products.lean
#print category_theory.limits.has_finite_products /- constant missing doc string -/
#print category_theory.limits.has_finite_coproducts /- constant missing doc string -/

-- category_theory/limits/shapes/finite_limits.lean
#print category_theory.limits.has_finite_limits /- constant missing doc string -/
#print category_theory.limits.has_finite_colimits /- constant missing doc string -/

-- category_theory/limits/shapes/equalizers.lean
#print category_theory.limits.has_equalizers /- constant missing doc string -/
#print category_theory.limits.fork.of_cone /- def missing doc string -/
#print category_theory.limits.cone.of_fork /- def missing doc string -/
#print category_theory.limits.walking_parallel_pair_hom.comp /- def missing doc string -/
#print category_theory.limits.cofork /- def missing doc string -/
#print category_theory.limits.cofork.π /- def missing doc string -/
#print category_theory.limits.coequalizer.desc /- def missing doc string -/
#print category_theory.limits.has_coequalizers /- constant missing doc string -/
#print category_theory.limits.equalizer.lift /- def missing doc string -/
#print category_theory.limits.coequalizer /- def missing doc string -/
#print category_theory.limits.equalizer /- def missing doc string -/
#print category_theory.limits.parallel_pair /- def missing doc string -/
#print category_theory.limits.cofork.of_π /- def missing doc string -/
#print category_theory.limits.coequalizer.π /- def missing doc string -/
#print category_theory.limits.fork.ι /- def missing doc string -/
#print category_theory.limits.cocone.of_cofork /- def missing doc string -/
#print category_theory.limits.fork /- def missing doc string -/
#print category_theory.limits.cofork.of_cocone /- def missing doc string -/
#print category_theory.limits.fork.of_ι /- def missing doc string -/
#print category_theory.limits.equalizer.ι /- def missing doc string -/

-- category_theory/limits/shapes/binary_products.lean
#print category_theory.limits.coprod /- def missing doc string -/
#print category_theory.limits.coprod.inr /- def missing doc string -/
#print category_theory.limits.coprod.map /- def missing doc string -/
#print category_theory.limits.prod.fst /- def missing doc string -/
#print category_theory.limits.prod.lift /- def missing doc string -/
#print category_theory.limits.has_binary_coproducts /- constant missing doc string -/
#print category_theory.limits.map_pair /- def missing doc string -/
#print category_theory.limits.has_binary_products /- constant missing doc string -/
#print category_theory.limits.binary_fan /- def missing doc string -/
#print category_theory.limits.binary_fan.mk /- def missing doc string -/
#print category_theory.limits.pair_function /- def missing doc string -/
#print category_theory.limits.coprod.desc /- def missing doc string -/
#print category_theory.limits.prod.snd /- def missing doc string -/
#print category_theory.limits.pair /- def missing doc string -/
#print category_theory.limits.binary_cofan /- def missing doc string -/
#print category_theory.limits.binary_cofan.mk /- def missing doc string -/
#print category_theory.limits.prod.map /- def missing doc string -/
#print category_theory.limits.coprod.inl /- def missing doc string -/
#print category_theory.limits.prod /- def missing doc string -/

-- category_theory/limits/preserves.lean
#print category_theory.limits.reflects_colimit /- constant missing doc string -/
#print category_theory.limits.reflects_limit /- constant missing doc string -/
#print category_theory.limits.preserves_colimits_of_shape /- constant missing doc string -/
#print category_theory.limits.preserves_colimit /- constant missing doc string -/
#print category_theory.limits.preserves_limits_of_shape /- constant missing doc string -/
#print category_theory.limits.reflects_colimits_of_shape /- constant missing doc string -/
#print category_theory.limits.reflects_limits_of_shape /- constant missing doc string -/
#print category_theory.limits.reflects_limits /- constant missing doc string -/
#print category_theory.limits.preserves_limits /- constant missing doc string -/
#print category_theory.limits.preserves_limit /- constant missing doc string -/
#print category_theory.limits.preserves_colimits /- constant missing doc string -/
#print category_theory.limits.reflects_colimits /- constant missing doc string -/

-- category_theory/limits/over.lean
#print category_theory.over.colimit /- def missing doc string -/
#print category_theory.under.limit /- def missing doc string -/
#print category_theory.over.forget_colimit_is_colimit /- def missing doc string -/
#print category_theory.functor.to_cone /- def missing doc string -/
#print category_theory.under.forget_limit_is_limit /- def missing doc string -/
#print category_theory.functor.to_cocone /- def missing doc string -/

-- category_theory/limits/limits.lean
#print category_theory.limits.colimit.cocone_morphism /- def missing doc string -/
#print category_theory.limits.is_limit.of_iso_limit /- def missing doc string -/
#print category_theory.limits.is_limit.iso_unique_cone_morphism /- def missing doc string -/
#print category_theory.limits.limit.hom_iso /- def missing doc string -/
#print category_theory.limits.is_colimit.desc_cocone_morphism /- def missing doc string -/
#print category_theory.limits.has_limit_of_iso /- def missing doc string -/
#print category_theory.limits.has_limit_of_equivalence_comp /- def missing doc string -/
#print category_theory.limits.is_colimit.hom_iso' /- def missing doc string -/
#print category_theory.limits.lim_yoneda /- def missing doc string -/
#print category_theory.limits.colimit.hom_iso' /- def missing doc string -/
#print category_theory.limits.limit.pre /- def missing doc string -/
#print category_theory.limits.limit.cone_morphism /- def missing doc string -/
#print category_theory.limits.limit.π /- def missing doc string -/
#print category_theory.limits.colimit.desc /- def missing doc string -/
#print category_theory.limits.colimit.post /- def missing doc string -/
#print category_theory.limits.has_colimits_of_shape_of_equivalence /- def missing doc string -/
#print category_theory.limits.is_limit.lift_cone_morphism /- def missing doc string -/
#print category_theory.limits.limit.post /- def missing doc string -/
#print category_theory.limits.colimit.is_colimit /- def missing doc string -/
#print category_theory.limits.has_limits_of_shape_of_equivalence /- def missing doc string -/
#print category_theory.limits.limit.is_limit /- def missing doc string -/
#print category_theory.limits.is_colimit.of_iso_colimit /- def missing doc string -/
#print category_theory.limits.colimit /- def missing doc string -/
#print category_theory.limits.is_colimit.iso_unique_cocone_morphism /- def missing doc string -/
#print category_theory.limits.has_colimit_of_iso /- def missing doc string -/
#print category_theory.limits.colimit.cocone /- def missing doc string -/
#print category_theory.limits.colimit.hom_iso /- def missing doc string -/
#print category_theory.limits.colim_coyoneda /- def missing doc string -/
#print category_theory.limits.is_colimit.mk_cocone_morphism /- def missing doc string -/
#print category_theory.limits.limit /- def missing doc string -/
#print category_theory.limits.colimit.ι /- def missing doc string -/
#print category_theory.limits.has_colimit_of_equivalence_comp /- def missing doc string -/
#print category_theory.limits.limit.cone /- def missing doc string -/
#print category_theory.limits.is_limit.mk_cone_morphism /- def missing doc string -/
#print category_theory.limits.colimit.pre /- def missing doc string -/
#print category_theory.limits.is_limit.hom_iso' /- def missing doc string -/
#print category_theory.limits.limit.hom_iso' /- def missing doc string -/
#print category_theory.limits.limit.lift /- def missing doc string -/

-- category_theory/limits/functor_category.lean
#print category_theory.limits.functor_category_is_limit_cone /- def missing doc string -/
#print category_theory.limits.functor_category_colimit_cocone /- def missing doc string -/
#print category_theory.limits.functor_category_limit_cone /- def missing doc string -/
#print category_theory.limits.evaluate_functor_category_limit_cone /- def missing doc string -/
#print category_theory.limits.evaluate_functor_category_colimit_cocone /- def missing doc string -/
#print category_theory.limits.functor_category_is_colimit_cocone /- def missing doc string -/

-- category_theory/limits/cones.lean
#print category_theory.limits.cocones.functoriality /- def missing doc string -/
#print category_theory.limits.cocones.precompose /- def missing doc string -/
#print category_theory.limits.cone_of_cocone_left_op /- def missing doc string -/
#print category_theory.limits.cocones.precompose_equivalence /- def missing doc string -/
#print category_theory.limits.cocone.whisker /- def missing doc string -/
#print category_theory.limits.cones.postcompose_comp /- def missing doc string -/
#print category_theory.limits.cones.functoriality /- def missing doc string -/
#print category_theory.limits.cocone.extensions /- def missing doc string -/
#print category_theory.limits.cones.postcompose_id /- def missing doc string -/
#print category_theory.limits.cones.postcompose_equivalence /- def missing doc string -/
#print category_theory.limits.cocones.precompose_id /- def missing doc string -/
#print category_theory.limits.cocones.forget /- def missing doc string -/
#print category_theory.functor.map_cocone_morphism /- def missing doc string -/
#print category_theory.limits.cocones.precompose_comp /- def missing doc string -/
#print category_theory.limits.cones.postcompose /- def missing doc string -/
#print category_theory.limits.cocone_morphism /- constant missing doc string -/
#print category_theory.limits.cone.whisker /- def missing doc string -/
#print category_theory.limits.cone_left_op_of_cocone /- def missing doc string -/
#print category_theory.functor.map_cone_inv /- def missing doc string -/
#print category_theory.limits.cocone_of_cone_left_op /- def missing doc string -/
#print category_theory.functor.map_cone_morphism /- def missing doc string -/
#print category_theory.limits.cocone_left_op_of_cone /- def missing doc string -/
#print category_theory.limits.cone.equiv /- def missing doc string -/
#print category_theory.limits.cocone.equiv /- def missing doc string -/
#print category_theory.limits.cones.forget /- def missing doc string -/
#print category_theory.limits.cone.extensions /- def missing doc string -/
#print category_theory.limits.cone_morphism /- constant missing doc string -/

-- category_theory/isomorphism.lean
#print category_theory.iso.refl /- def missing doc string -/
#print category_theory.functor.map_iso /- def missing doc string -/
#print category_theory.iso /- constant missing doc string -/
#print category_theory.iso.symm /- def missing doc string -/
#print category_theory.as_iso /- def missing doc string -/
#print category_theory.iso.trans /- def missing doc string -/

-- category_theory/groupoid.lean
#print category_theory.large_groupoid /- def missing doc string -/
#print category_theory.small_groupoid /- def missing doc string -/

-- category_theory/functor_category.lean
#print category_theory.functor.flip /- def missing doc string -/

-- category_theory/functor.lean
#print category_theory.functor.ulift_down /- def missing doc string -/
#print category_theory.functor.ulift_up /- def missing doc string -/

-- category_theory/fully_faithful.lean
#print category_theory.is_iso_of_fully_faithful /- def missing doc string -/

-- category_theory/full_subcategory.lean
#print category_theory.induced_functor /- def missing doc string -/
#print category_theory.induced_category /- def missing doc string -/
#print category_theory.full_subcategory_inclusion /- def missing doc string -/

-- category_theory/equivalence.lean
#print category_theory.equivalence.adjointify_η /- def missing doc string -/
#print category_theory.equivalence.ess_surj_of_equivalence /- def missing doc string -/
#print category_theory.functor.fun_inv_id /- def missing doc string -/
#print category_theory.functor.inv_fun_id /- def missing doc string -/
#print category_theory.equivalence.counit /- def missing doc string -/
#print category_theory.equivalence.trans /- def missing doc string -/
#print category_theory.functor.as_equivalence /- def missing doc string -/
#print category_theory.equivalence.unit /- def missing doc string -/
#print category_theory.equivalence.unit_inv /- def missing doc string -/
#print category_theory.equivalence.inv_fun_id_assoc /- def missing doc string -/
#print category_theory.equivalence.fun_inv_id_assoc /- def missing doc string -/
#print category_theory.functor.fun_obj_preimage_iso /- def missing doc string -/
#print category_theory.functor.obj_preimage /- def missing doc string -/
#print category_theory.equivalence.refl /- def missing doc string -/
#print category_theory.ess_surj.iso /- def missing doc string -/
#print category_theory.functor.inv /- def missing doc string -/
#print category_theory.equivalence.mk /- def missing doc string -/
#print category_theory.is_equivalence.mk /- def missing doc string -/
#print category_theory.equivalence.counit_inv /- def missing doc string -/
#print category_theory.equivalence.symm /- def missing doc string -/
#print category_theory.ess_surj /- constant missing doc string -/
#print category_theory.equivalence.equivalence_of_fully_faithfully_ess_surj /- def missing doc string -/

-- category_theory/eq_to_hom.lean
#print category_theory.eq_to_hom /- def missing doc string -/
#print category_theory.eq_to_iso /- def missing doc string -/

-- category_theory/endomorphism.lean
#print category_theory.Aut /- def missing doc string -/

-- category_theory/discrete_category.lean
#print category_theory.discrete.opposite /- def missing doc string -/
#print category_theory.discrete.lift /- def missing doc string -/
#print category_theory.functor.of_function /- def missing doc string -/
#print category_theory.nat_iso.of_isos /- def missing doc string -/
#print category_theory.discrete /- def missing doc string -/
#print category_theory.nat_trans.of_homs /- def missing doc string -/
#print category_theory.nat_trans.of_function /- def missing doc string -/

-- category_theory/currying.lean
#print category_theory.curry /- def missing doc string -/
#print category_theory.currying /- def missing doc string -/
#print category_theory.uncurry /- def missing doc string -/
#print category_theory.curry_obj /- def missing doc string -/

-- category_theory/core.lean
#print category_theory.core.inclusion /- def missing doc string -/
#print category_theory.core /- def missing doc string -/
#print category_theory.core.forget_functor_to_core /- def missing doc string -/

-- category_theory/const.lean
#print category_theory.functor.const /- def missing doc string -/
#print category_theory.functor.const.op_obj_unop /- def missing doc string -/
#print category_theory.functor.const.op_obj_op /- def missing doc string -/

-- category_theory/conj.lean
#print category_theory.iso.hom_congr /- def missing doc string -/

-- category_theory/comma.lean
#print category_theory.over.hom_mk /- def missing doc string -/
#print category_theory.under.forget /- def missing doc string -/
#print category_theory.under.post /- def missing doc string -/
#print category_theory.comma.snd /- def missing doc string -/
#print category_theory.comma.map_left_id /- def missing doc string -/
#print category_theory.comma.map_left_comp /- def missing doc string -/
#print category_theory.comma.map_right /- def missing doc string -/
#print category_theory.over.forget /- def missing doc string -/
#print category_theory.comma /- constant missing doc string -/
#print category_theory.comma.fst /- def missing doc string -/
#print category_theory.comma.nat_trans /- def missing doc string -/
#print category_theory.under /- def missing doc string -/
#print category_theory.under.map /- def missing doc string -/
#print category_theory.over.post /- def missing doc string -/
#print category_theory.comma.map_left /- def missing doc string -/
#print category_theory.over.mk /- def missing doc string -/
#print category_theory.under.mk /- def missing doc string -/
#print category_theory.comma_morphism /- constant missing doc string -/
#print category_theory.under.hom_mk /- def missing doc string -/
#print category_theory.comma.map_right_id /- def missing doc string -/
#print category_theory.over /- def missing doc string -/
#print category_theory.comma.map_right_comp /- def missing doc string -/
#print category_theory.over.map /- def missing doc string -/

-- category_theory/category/default.lean
#print category_theory.mono /- constant missing doc string -/
#print category_theory.category_struct /- constant missing doc string -/
#print category_theory.obviously' /- def missing doc string -/
#print category_theory.epi /- constant missing doc string -/
#print category_theory.has_hom /- constant missing doc string -/
#print obviously.attr /- def missing doc string -/

-- category_theory/category/Kleisli.lean
#print category_theory.Kleisli.mk /- def missing doc string -/
#print category_theory.Kleisli /- def missing doc string -/

-- category_theory/adjunction/limits.lean
#print category_theory.adjunction.cones_iso /- def missing doc string -/
#print category_theory.adjunction.functoriality_counit /- def missing doc string -/
#print category_theory.adjunction.functoriality_is_left_adjoint /- def missing doc string -/
#print category_theory.adjunction.functoriality_counit' /- def missing doc string -/
#print category_theory.adjunction.functoriality_left_adjoint /- def missing doc string -/
#print category_theory.adjunction.functoriality_is_right_adjoint /- def missing doc string -/
#print category_theory.adjunction.has_limit_of_comp_equivalence /- def missing doc string -/
#print category_theory.adjunction.cocones_iso /- def missing doc string -/
#print category_theory.adjunction.functoriality_unit /- def missing doc string -/
#print category_theory.adjunction.functoriality_right_adjoint /- def missing doc string -/
#print category_theory.adjunction.has_colimit_of_comp_equivalence /- def missing doc string -/
#print category_theory.adjunction.functoriality_unit' /- def missing doc string -/

-- category_theory/adjunction/basic.lean
#print category_theory.adjunction.mk_of_unit_counit /- def missing doc string -/
#print category_theory.adjunction.core_hom_equiv /- constant missing doc string -/
#print category_theory.adjunction.id /- def missing doc string -/
#print category_theory.is_right_adjoint /- constant missing doc string -/
#print category_theory.equivalence.to_adjunction /- def missing doc string -/
#print category_theory.left_adjoint /- def missing doc string -/
#print category_theory.adjunction.adjunction_of_equiv_right /- def missing doc string -/
#print category_theory.functor.adjunction /- def missing doc string -/
#print category_theory.adjunction.mk_of_hom_equiv /- def missing doc string -/
#print category_theory.adjunction.left_adjoint_of_equiv /- def missing doc string -/
#print category_theory.adjunction.right_adjoint_of_equiv /- def missing doc string -/
#print category_theory.adjunction.comp /- def missing doc string -/
#print category_theory.adjunction.adjunction_of_equiv_left /- def missing doc string -/
#print category_theory.right_adjoint /- def missing doc string -/
#print category_theory.adjunction.core_unit_counit /- constant missing doc string -/
#print category_theory.is_left_adjoint /- constant missing doc string -/

-- category/traversable/lemmas.lean
#print traversable.pure_transformation /- def missing doc string -/

-- category/traversable/equiv.lean
#print equiv.functor /- def missing doc string -/
#print equiv.traversable /- def missing doc string -/
#print equiv.is_lawful_traversable /- def missing doc string -/
#print equiv.map /- def missing doc string -/
#print equiv.is_lawful_traversable' /- def missing doc string -/
#print equiv.traverse /- def missing doc string -/

-- category/traversable/derive.lean
#print tactic.interactive.traversable_derive_handler' /- def missing doc string -/
#print tactic.interactive.functor_derive_handler' /- def missing doc string -/
#print tactic.interactive.traversable_derive_handler /- def missing doc string -/
#print tactic.interactive.lawful_functor_derive_handler' /- def missing doc string -/
#print tactic.interactive.higher_order_derive_handler /- def missing doc string -/
#print tactic.interactive.guard_class /- def missing doc string -/
#print tactic.interactive.lawful_traversable_derive_handler /- def missing doc string -/
#print tactic.interactive.mk_mapp_aux' /- def missing doc string -/
#print tactic.interactive.derive_lawful_functor /- def missing doc string -/
#print tactic.interactive.derive_traverse /- def missing doc string -/
#print tactic.interactive.derive_functor /- def missing doc string -/
#print tactic.interactive.lawful_functor_derive_handler /- def missing doc string -/
#print tactic.interactive.with_prefix /- def missing doc string -/
#print tactic.interactive.lawful_traversable_derive_handler' /- def missing doc string -/
#print tactic.interactive.functor_derive_handler /- def missing doc string -/
#print tactic.interactive.mk_one_instance /- def missing doc string -/
#print tactic.interactive.simp_functor /- def missing doc string -/
#print tactic.interactive.get_equations_of /- def missing doc string -/
#print tactic.interactive.derive_lawful_traversable /- def missing doc string -/
#print tactic.interactive.traversable_law_starter /- def missing doc string -/
#print tactic.interactive.mk_mapp' /- def missing doc string -/

-- category/traversable/basic.lean
#print applicative_transformation /- constant missing doc string -/
#print is_lawful_traversable /- constant missing doc string -/
#print sum.traverse /- def missing doc string -/
#print traversable /- constant missing doc string -/
#print sequence /- def missing doc string -/

-- category/monad/writer.lean
#print writer_t.lift /- def missing doc string -/
#print swap_right /- def missing doc string -/
#print writer_t.tell /- def missing doc string -/
#print option_t.pass_aux /- def missing doc string -/
#print writer /- def missing doc string -/
#print except_t.pass_aux /- def missing doc string -/
#print writer_t.adapt /- def missing doc string -/
#print writer_t.pure /- def missing doc string -/
#print writer_t.pass /- def missing doc string -/
#print writer_t.monad_map /- def missing doc string -/
#print writer_t.bind /- def missing doc string -/
#print writer_t.listen /- def missing doc string -/
#print writer_t /- constant missing doc string -/

-- category/monad/cont.lean
#print is_lawful_monad_cont /- constant missing doc string -/
#print reader_t.call_cc /- def missing doc string -/
#print option_t.call_cc /- def missing doc string -/
#print cont_t.with_cont_t /- def missing doc string -/
#print monad_cont.label /- constant missing doc string -/
#print cont /- def missing doc string -/
#print cont_t.monad_lift /- def missing doc string -/
#print writer_t.call_cc /- def missing doc string -/
#print except_t.mk_label /- def missing doc string -/
#print cont_t.run /- def missing doc string -/
#print writer_t.mk_label /- def missing doc string -/
#print state_t.mk_label /- def missing doc string -/
#print option_t.mk_label /- def missing doc string -/
#print reader_t.mk_label /- def missing doc string -/
#print cont_t.map /- def missing doc string -/
#print monad_cont.goto /- def missing doc string -/
#print cont_t /- def missing doc string -/
#print state_t.call_cc /- def missing doc string -/
#print except_t.call_cc /- def missing doc string -/
#print monad_cont /- constant missing doc string -/

-- category/functor.lean
#print functor.const.mk' /- def missing doc string -/
#print functor.comp.map /- def missing doc string -/
#print functor.const.mk /- def missing doc string -/
#print functor.comp.run /- def missing doc string -/
#print functor.add_const.mk /- def missing doc string -/
#print id.mk /- def missing doc string -/
#print functor.add_const /- def missing doc string -/
#print functor.const.run /- def missing doc string -/
#print functor.add_const.run /- def missing doc string -/
#print functor.comp.mk /- def missing doc string -/

-- category/fold.lean
#print monoid.mfoldr.mk /- def missing doc string -/
#print monoid.foldr.get /- def missing doc string -/
#print traversable.free.mk /- def missing doc string -/
#print traversable.map_fold /- def missing doc string -/
#print traversable.mfoldl /- def missing doc string -/
#print traversable.fold_map /- def missing doc string -/
#print traversable.free.map /- def missing doc string -/
#print monoid.mfoldl.of_free_monoid /- def missing doc string -/
#print monoid.foldl.get /- def missing doc string -/
#print monoid.mfoldl.mk /- def missing doc string -/
#print monoid.foldr.of_free_monoid /- def missing doc string -/
#print traversable.length /- def missing doc string -/
#print traversable.mfoldr /- def missing doc string -/
#print traversable.foldl /- def missing doc string -/
#print monoid.mfoldl.get /- def missing doc string -/
#print monoid.mfoldl /- def missing doc string -/
#print monoid.foldr.mk /- def missing doc string -/
#print monoid.mfoldr /- def missing doc string -/
#print monoid.mfoldr.get /- def missing doc string -/
#print monoid.foldl.mk /- def missing doc string -/
#print monoid.foldr /- def missing doc string -/
#print monoid.mfoldr.of_free_monoid /- def missing doc string -/
#print traversable.foldr /- def missing doc string -/
#print monoid.foldl.of_free_monoid /- def missing doc string -/

-- category/bitraversable/instances.lean
#print bicompl.bitraverse /- def missing doc string -/
#print prod.bitraverse /- def missing doc string -/
#print flip.bitraverse /- def missing doc string -/
#print const.bitraverse /- def missing doc string -/
#print sum.bitraverse /- def missing doc string -/
#print bicompr.bitraverse /- def missing doc string -/

-- category/bitraversable/basic.lean
#print bitraversable /- constant missing doc string -/
#print bisequence /- def missing doc string -/
#print is_lawful_bitraversable /- constant missing doc string -/

-- category/bifunctor.lean
#print bifunctor.fst /- def missing doc string -/
#print bifunctor /- constant missing doc string -/
#print is_lawful_bifunctor /- constant missing doc string -/
#print bifunctor.snd /- def missing doc string -/

-- category/basic.lean
#print sum.bind /- def missing doc string -/
#print succeeds /- def missing doc string -/
#print list.mpartition /- def missing doc string -/
#print is_comm_applicative /- constant missing doc string -/
#print list.mmap_accuml /- def missing doc string -/
#print mzip_with' /- def missing doc string -/
#print mtry /- def missing doc string -/
#print list.mmap_accumr /- def missing doc string -/
#print mzip_with /- def missing doc string -/

-- category/applicative.lean
#print comp.seq /- def missing doc string -/

-- analysis/normed_space/real_inner_product.lean
#print has_inner /- constant missing doc string -/

-- algebraic_geometry/stalks.lean
#print algebraic_geometry.PresheafedSpace.stalk_map /- def missing doc string -/
#print algebraic_geometry.PresheafedSpace.stalk /- def missing doc string -/

-- algebraic_geometry/presheafed_space.lean
#print algebraic_geometry.PresheafedSpace.comp /- def missing doc string -/
#print algebraic_geometry.PresheafedSpace.id /- def missing doc string -/
#print category_theory.nat_trans.on_presheaf /- def missing doc string -/

-- algebra/ring.lean
#print ring_hom.to_add_monoid_hom /- def missing doc string -/
#print ring_hom.to_monoid_hom /- def missing doc string -/

-- algebra/pointwise.lean
#print set.pointwise_zero /- def missing doc string -/
#print set.pointwise_add_add_semigroup /- def missing doc string -/
#print set.pointwise_neg /- def missing doc string -/
#print set.pointwise_mul_monoid /- def missing doc string -/
#print set.pointwise_mul_fintype /- def missing doc string -/
#print set.pointwise_mul_action /- def missing doc string -/
#print set.comm_monoid /- def missing doc string -/
#print set.pointwise_inv /- def missing doc string -/
#print set.pointwise_mul /- def missing doc string -/
#print set.pointwise_add_add_monoid /- def missing doc string -/
#print set.pointwise_one /- def missing doc string -/
#print set.pointwise_mul_semigroup /- def missing doc string -/
#print set.pointwise_mul_comm_semiring /- def missing doc string -/
#print set.pointwise_mul_semiring /- def missing doc string -/
#print set.add_comm_monoid /- def missing doc string -/
#print set.pointwise_add_fintype /- def missing doc string -/
#print set.pointwise_add /- def missing doc string -/

-- algebra/ordered_ring.lean
#print nonneg_ring.to_linear_nonneg_ring /- def missing doc string -/
#print canonically_ordered_comm_semiring /- constant missing doc string -/

-- algebra/ordered_group.lean
#print nonneg_comm_group.to_decidable_linear_ordered_comm_group /- def missing doc string -/
#print with_zero.ordered_comm_monoid /- def missing doc string -/

-- algebra/order.lean
#print decidable.lt_by_cases /- def missing doc string -/

-- algebra/module.lean
#print module.of_core /- def missing doc string -/
#print module.End /- def missing doc string -/
#print submodule.subtype /- def missing doc string -/
#print ideal /- def missing doc string -/
#print is_linear_map.mk' /- def missing doc string -/
#print linear_map /- constant missing doc string -/
#print is_add_group_hom.to_linear_map /- def missing doc string -/
#print linear_map.comp /- def missing doc string -/
#print module.core /- constant missing doc string -/
#print is_linear_map /- constant missing doc string -/
#print is_ring_hom.to_module /- def missing doc string -/
#print linear_map.id /- def missing doc string -/

-- algebra/group_power.lean
#print gsmul /- def missing doc string -/
#print add_monoid.smul /- def missing doc string -/

-- algebra/group/with_one.lean
#print with_zero.inv /- def missing doc string -/
#print with_one /- def missing doc string -/
#print with_zero.lift /- def missing doc string -/
#print with_zero /- def missing doc string -/
#print with_one.map /- def missing doc string -/
#print with_one.lift /- def missing doc string -/
#print with_zero.div /- def missing doc string -/
#print with_zero.map /- def missing doc string -/

-- algebra/group/units_hom.lean
#print units.map /- def missing doc string -/

-- algebra/group/units.lean
#print units.inv' /- def missing doc string -/
#print units.mul /- def missing doc string -/
#print units.mk_of_mul_eq_one /- def missing doc string -/
#print units /- constant missing doc string -/

-- algebra/group/type_tags.lean
#print multiplicative /- def missing doc string -/
#print additive /- def missing doc string -/

-- algebra/group/to_additive.lean
#print to_additive.target_name /- def missing doc string -/
#print to_additive.tokens_dict /- def missing doc string -/
#print to_additive.proceed_fields /- def missing doc string -/
#print to_additive.guess_name /- def missing doc string -/
#print to_additive.value_type /- constant missing doc string -/
#print to_additive.parser /- def missing doc string -/
#print to_additive.map_namespace /- def missing doc string -/
#print to_additive.aux_attr /- def missing doc string -/
#print to_additive.attr /- def missing doc string -/

-- algebra/group/hom.lean
#print add_monoid_hom.neg /- def missing doc string -/
#print add_monoid_hom.add /- def missing doc string -/
#print add_monoid_hom.mk' /- def missing doc string -/
#print add_monoid_hom.zero /- def missing doc string -/
#print monoid_hom.one /- def missing doc string -/
#print add_monoid_hom.id /- def missing doc string -/
#print add_monoid_hom.comp /- def missing doc string -/

-- algebra/group/free_monoid.lean
#print free_add_monoid /- def missing doc string -/
#print free_monoid /- def missing doc string -/

-- algebra/group/conj.lean
#print is_conj /- def missing doc string -/

-- algebra/gcd_domain.lean
#print associates.out /- def missing doc string -/
#print normalize /- def missing doc string -/
#print associates_int_equiv_nat /- def missing doc string -/

-- algebra/free.lean
#print free_magma /- constant missing doc string -/
#print free_semigroup.lift' /- def missing doc string -/
#print free_semigroup.of /- def missing doc string -/
#print free_magma.length /- def missing doc string -/
#print magma.free_semigroup.lift /- def missing doc string -/
#print magma.free_semigroup /- def missing doc string -/
#print free_semigroup /- def missing doc string -/
#print magma.free_semigroup.of /- def missing doc string -/
#print free_semigroup.map /- def missing doc string -/
#print free_magma.lift /- def missing doc string -/
#print free_semigroup.lift /- def missing doc string -/
#print free_semigroup_free_magma /- def missing doc string -/
#print magma.free_semigroup.r /- constant missing doc string -/
#print free_magma.map /- def missing doc string -/
#print free_magma.traverse /- def missing doc string -/
#print free_semigroup.traverse /- def missing doc string -/
#print free_semigroup.traverse' /- def missing doc string -/
#print free_magma.repr' /- def missing doc string -/
#print magma.free_semigroup.map /- def missing doc string -/

-- algebra/euclidean_domain.lean
#print euclidean_domain.lcm /- def missing doc string -/
#print euclidean_domain.gcd /- def missing doc string -/
#print euclidean_domain /- constant missing doc string -/
#print euclidean_domain.xgcd_aux /- def missing doc string -/

-- algebra/direct_sum.lean
#print direct_sum.mk /- def missing doc string -/
#print direct_sum /- def missing doc string -/
#print direct_sum.of /- def missing doc string -/
#print direct_sum.to_group /- def missing doc string -/
#print direct_sum.id /- def missing doc string -/
#print direct_sum.set_to_set /- def missing doc string -/

-- algebra/direct_limit.lean
#print field.direct_limit.discrete_field /- def missing doc string -/
#print module.direct_limit.totalize /- def missing doc string -/
#print field.direct_limit.inv /- def missing doc string -/
#print field.direct_limit.field /- def missing doc string -/

-- algebra/commute.lean
#print centralizer.add_submonoid /- def missing doc string -/
#print set.centralizer.add_submonoid /- def missing doc string -/

-- algebra/category/Mon/colimits.lean
#print Mon.colimits.cocone_morphism /- def missing doc string -/
#print Mon.colimits.desc_morphism /- def missing doc string -/
#print Mon.colimits.colimit_is_colimit /- def missing doc string -/
#print Mon.colimits.colimit /- def missing doc string -/
#print Mon.colimits.desc_fun_lift /- def missing doc string -/
#print Mon.colimits.colimit_type /- def missing doc string -/
#print Mon.colimits.relation /- constant missing doc string -/
#print Mon.colimits.desc_fun /- def missing doc string -/
#print Mon.colimits.colimit_cocone /- def missing doc string -/
#print Mon.colimits.prequotient /- constant missing doc string -/
#print Mon.colimits.cocone_fun /- def missing doc string -/

-- algebra/category/Mon/basic.lean
#print AddMon.of /- def missing doc string -/
#print AddCommMon.of /- def missing doc string -/
#print AddCommMon /- def missing doc string -/
#print AddMon /- def missing doc string -/

-- algebra/category/Module/basic.lean
#print Module.of /- def missing doc string -/

-- algebra/category/Group.lean
#print AddCommGroup /- def missing doc string -/
#print AddGroup /- def missing doc string -/
#print AddCommGroup.of /- def missing doc string -/
#print AddGroup.of /- def missing doc string -/

-- algebra/category/CommRing/colimits.lean
#print CommRing.colimits.desc_fun_lift /- def missing doc string -/
#print CommRing.colimits.relation /- constant missing doc string -/
#print CommRing.colimits.colimit_type /- def missing doc string -/
#print CommRing.colimits.colimit_cocone /- def missing doc string -/
#print CommRing.colimits.colimit /- def missing doc string -/
#print CommRing.colimits.cocone_fun /- def missing doc string -/
#print CommRing.colimits.prequotient /- constant missing doc string -/
#print CommRing.colimits.desc_morphism /- def missing doc string -/
#print CommRing.colimits.cocone_morphism /- def missing doc string -/
#print CommRing.colimits.desc_fun /- def missing doc string -/
#print CommRing.colimits.colimit_is_colimit /- def missing doc string -/

-- algebra/big_operators.lean
#print finset.sum /- def missing doc string -/

-- algebra/associated.lean
#print associated /- def missing doc string -/
#print associates.mk /- def missing doc string -/
#print associates /- def missing doc string -/
#print associates.prime /- def missing doc string -/
#print associated.setoid /- def missing doc string -/

-- algebra/archimedean.lean
#print archimedean /- constant missing doc string -/
#print archimedean.floor_ring /- def missing doc string -/

/- ILLEGAL CONSTANTS IN DECLARATIONS: -/

-- topology/uniform_space/absolute_value.lean
#print is_absolute_value.mem_uniformity /- the type contains ≥/>. Use ≤/< instead. -/

-- topology/sequences.lean
#print topological_space.seq_tendsto_iff /- the type contains ≥/>. Use ≤/< instead. -/

-- topology/metric_space/hausdorff_distance.lean
#print metric.Hausdorff_dist_le_of_inf_dist /- the type contains ≥/>. Use ≤/< instead. -/

-- topology/metric_space/emetric_space.lean
#print emetric.cauchy_iff /- the type contains ≥/>. Use ≤/< instead. -/
#print emetric.uniform_continuous_iff /- the type contains ≥/>. Use ≤/< instead. -/
#print emetric.totally_bounded_iff' /- the type contains ≥/>. Use ≤/< instead. -/
#print emetric.tendsto_at_top /- the type contains ≥/>. Use ≤/< instead. -/
#print emetric.mem_nhds_iff /- the type contains ≥/>. Use ≤/< instead. -/
#print emetric.cauchy_seq_iff /- the type contains ≥/>. Use ≤/< instead. -/
#print emetric.tendsto_nhds /- the type contains ≥/>. Use ≤/< instead. -/
#print emetric.mem_closure_iff' /- the type contains ≥/>. Use ≤/< instead. -/
#print emetric.uniform_embedding_iff /- the type contains ≥/>. Use ≤/< instead. -/
#print emetric.uniform_embedding_iff' /- the type contains ≥/>. Use ≤/< instead. -/
#print emetric.cauchy_seq_iff' /- the type contains ≥/>. Use ≤/< instead. -/
#print mem_uniformity_edist /- the type contains ≥/>. Use ≤/< instead. -/
#print emetric.nhds_eq /- the type contains ≥/>. Use ≤/< instead. -/
#print emetric.exists_ball_subset_ball /- the type contains ≥/>. Use ≤/< instead. -/
#print emetric.totally_bounded_iff /- the type contains ≥/>. Use ≤/< instead. -/
#print uniformity_edist' /- the type contains ≥/>. Use ≤/< instead. -/
#print uniformity_edist'' /- the type contains ≥/>. Use ≤/< instead. -/
#print uniformity_edist_nnreal /- the type contains ≥/>. Use ≤/< instead. -/
#print uniformity_dist_of_mem_uniformity /- the type contains ≥/>. Use ≤/< instead. -/
#print eq_of_forall_edist_le /- the type contains ≥/>. Use ≤/< instead. -/
#print emetric.is_open_iff /- the type contains ≥/>. Use ≤/< instead. -/

-- topology/metric_space/completion.lean
#print metric.completion.mem_uniformity_dist /- the type contains ≥/>. Use ≤/< instead. -/
#print metric.completion.uniformity_dist' /- the type contains ≥/>. Use ≤/< instead. -/
#print metric.completion.uniformity_dist /- the type contains ≥/>. Use ≤/< instead. -/

-- topology/metric_space/basic.lean
#print metric.totally_bounded_iff /- the type contains ≥/>. Use ≤/< instead. -/
#print metric.mem_uniformity_edist /- the type contains ≥/>. Use ≤/< instead. -/
#print metric.tendsto_at_top /- the type contains ≥/>. Use ≤/< instead. -/
#print metric.mem_of_closed' /- the type contains ≥/>. Use ≤/< instead. -/
#print metric.diam_le_of_forall_dist_le /- the type contains ≥/>. Use ≤/< instead. -/
#print lebesgue_number_lemma_of_metric_sUnion /- the type contains ≥/>. Use ≤/< instead. -/
#print metric.diam_closed_ball /- the type contains ≥/>. Use ≤/< instead. -/
#print metric.continuous_iff /- the type contains ≥/>. Use ≤/< instead. -/
#print metric.mem_uniformity_dist /- the type contains ≥/>. Use ≤/< instead. -/
#print metric.tendsto_nhds /- the type contains ≥/>. Use ≤/< instead. -/
#print eq_of_forall_dist_le /- the type contains ≥/>. Use ≤/< instead. -/
#print metric.uniformity_dist /- the type contains ≥/>. Use ≤/< instead. -/
#print metric.exists_delta_of_continuous /- the type contains ≥/>. Use ≤/< instead. -/
#print metric.cauchy_iff /- the type contains ≥/>. Use ≤/< instead. -/
#print uniformity_edist /- the type contains ≥/>. Use ≤/< instead. -/
#print metric.exists_ball_subset_ball /- the type contains ≥/>. Use ≤/< instead. -/
#print metric.uniformity_dist' /- the type contains ≥/>. Use ≤/< instead. -/
#print metric.mem_closed_ball_self /- the type contains ≥/>. Use ≤/< instead. -/
#print metric.uniform_embedding_iff /- the type contains ≥/>. Use ≤/< instead. -/
#print metric.uniformity_edist' /- the type contains ≥/>. Use ≤/< instead. -/
#print cauchy_seq_bdd /- the type contains ≥/>. Use ≤/< instead. -/
#print metric.mem_ball_self /- the type contains ≥/>. Use ≤/< instead. -/
#print metric.uniform_continuous_iff /- the type contains ≥/>. Use ≤/< instead. -/
#print metric.continuous_iff' /- the type contains ≥/>. Use ≤/< instead. -/
#print lebesgue_number_lemma_of_metric /- the type contains ≥/>. Use ≤/< instead. -/
#print metric.is_open_iff /- the type contains ≥/>. Use ≤/< instead. -/
#print metric.nhds_eq /- the type contains ≥/>. Use ≤/< instead. -/
#print metric.second_countable_of_almost_dense_set /- the type contains ≥/>. Use ≤/< instead. -/
#print metric.cauchy_seq_iff' /- the type contains ≥/>. Use ≤/< instead. -/
#print metric.mem_closure_range_iff /- the type contains ≥/>. Use ≤/< instead. -/
#print metric.diam_ball /- the type contains ≥/>. Use ≤/< instead. -/
#print metric.totally_bounded_of_finite_discretization /- the type contains ≥/>. Use ≤/< instead. -/
#print metric.second_countable_of_countable_discretization /- the type contains ≥/>. Use ≤/< instead. -/
#print metric.mem_closure_iff' /- the type contains ≥/>. Use ≤/< instead. -/
#print metric.pos_of_mem_ball /- the type contains ≥/>. Use ≤/< instead. -/
#print metric.uniform_embedding_iff' /- the type contains ≥/>. Use ≤/< instead. -/
#print metric.cauchy_seq_iff /- the type contains ≥/>. Use ≤/< instead. -/
#print metric.mem_nhds_iff /- the type contains ≥/>. Use ≤/< instead. -/

-- topology/metric_space/baire.lean
#print nonempty_interior_of_Union_of_closed /- the type contains ≥/>. Use ≤/< instead. -/

-- topology/instances/ennreal.lean
#print ennreal.Icc_mem_nhds /- the type contains ≥/>. Use ≤/< instead. -/
#print ennreal.nhds_of_ne_top /- the type contains ≥/>. Use ≤/< instead. -/
#print infi_real_pos_eq_infi_nnreal_pos /- the type contains ≥/>. Use ≤/< instead. -/
#print ennreal.tendsto_nhds /- the type contains ≥/>. Use ≤/< instead. -/
#print ennreal.tendsto_at_top /- the type contains ≥/>. Use ≤/< instead. -/

-- topology/bounded_continuous_function.lean
#print bounded_continuous_function.dist_set_exists /- the type contains ≥/>. Use ≤/< instead. -/
#print bounded_continuous_function.dist_eq /- the type contains ≥/>. Use ≤/< instead. -/
#print bounded_continuous_function.arzela_ascoli₂ /- the type contains ≥/>. Use ≤/< instead. -/
#print bounded_continuous_function.equicontinuous_of_continuity_modulus /- the type contains ≥/>. Use ≤/< instead. -/
#print continuous_of_locally_uniform_limit_of_continuous /- the type contains ≥/>. Use ≤/< instead. -/
#print bounded_continuous_function.arzela_ascoli /- the type contains ≥/>. Use ≤/< instead. -/
#print bounded_continuous_function.arzela_ascoli₁ /- the type contains ≥/>. Use ≤/< instead. -/
#print continuous_of_uniform_limit_of_continuous /- the type contains ≥/>. Use ≤/< instead. -/

-- topology/algebra/polynomial.lean
#print polynomial.tendsto_infinity /- the type contains ≥/>. Use ≤/< instead. -/

-- topology/algebra/ordered.lean
#print le_nhds_of_Limsup_eq_Liminf /- the type contains ≥/>. Use ≤/< instead. -/
#print gt_mem_sets_of_Liminf_gt /- the type contains ≥/>. Use ≤/< instead. -/
#print orderable_topology_of_nhds_abs /- the type contains ≥/>. Use ≤/< instead. -/
#print is_bounded_under_ge_of_tendsto /- the type contains ≥/>. Use ≤/< instead. -/
#print is_cobounded_ge_nhds /- the type contains ≥/>. Use ≤/< instead. -/
#print induced_orderable_topology' /- the type contains ≥/>. Use ≤/< instead. -/
#print is_bounded_ge_nhds /- the type contains ≥/>. Use ≤/< instead. -/
#print is_cobounded_under_ge_of_tendsto /- the type contains ≥/>. Use ≤/< instead. -/
#print tendsto_orderable /- the type contains ≥/>. Use ≤/< instead. -/

-- tactic/norm_cast.lean
#print ge_from_le /- the type contains ≥/>. Use ≤/< instead. -/
#print gt_from_lt /- the type contains ≥/>. Use ≤/< instead. -/

-- tactic/monotonicity/lemmas.lean
#print gt_of_mul_lt_mul_neg_right /- the type contains ≥/>. Use ≤/< instead. -/
#print mul_mono_nonpos /- the type contains ≥/>. Use ≤/< instead. -/

-- tactic/linarith.lean
#print linarith.mul_nonpos /- the type contains ≥/>. Use ≤/< instead. -/
#print linarith.mul_eq /- the type contains ≥/>. Use ≤/< instead. -/
#print linarith.mul_neg /- the type contains ≥/>. Use ≤/< instead. -/

-- set_theory/ordinal.lean
#print ordinal.CNF_sorted /- the type contains ≥/>. Use ≤/< instead. -/
#print ordinal.unbounded_range_of_sup_ge /- the type contains ≥/>. Use ≤/< instead. -/
#print ordinal.add_absorp_iff /- the type contains ≥/>. Use ≤/< instead. -/

-- ring_theory/power_series.lean
#print power_series.order_add_ge /- the type contains ≥/>. Use ≤/< instead. -/
#print power_series.order_mul_ge /- the type contains ≥/>. Use ≤/< instead. -/
#print power_series.order_ge /- the type contains ≥/>. Use ≤/< instead. -/
#print power_series.order_ge_nat /- the type contains ≥/>. Use ≤/< instead. -/

-- ring_theory/noetherian.lean
#print is_noetherian_iff_well_founded /- the type contains ≥/>. Use ≤/< instead. -/
#print well_founded_submodule_gt /- the type contains ≥/>. Use ≤/< instead. -/

-- ring_theory/ideal_operations.lean
#print ideal.radical_pow /- the type contains ≥/>. Use ≤/< instead. -/

-- order/order_iso.lean
#print order_embedding.well_founded_iff_no_descending_seq /- the type contains ≥/>. Use ≤/< instead. -/
#print order_embedding.nat_gt /- the type contains ≥/>. Use ≤/< instead. -/

-- order/liminf_limsup.lean
#print filter.liminf_le_liminf /- the type contains ≥/>. Use ≤/< instead. -/
#print filter.liminf_eq_supr_infi_of_nat /- the type contains ≥/>. Use ≤/< instead. -/
#print filter.Liminf_le_of_le /- the type contains ≥/>. Use ≤/< instead. -/
#print filter.limsup_eq_infi_supr_of_nat /- the type contains ≥/>. Use ≤/< instead. -/
#print filter.Liminf_le_Liminf_of_le /- the type contains ≥/>. Use ≤/< instead. -/
#print filter.Liminf_le_Limsup /- the type contains ≥/>. Use ≤/< instead. -/
#print filter.is_cobounded_ge_of_top /- the type contains ≥/>. Use ≤/< instead. -/
#print filter.is_bounded_ge_of_bot /- the type contains ≥/>. Use ≤/< instead. -/
#print filter.le_Liminf_of_le /- the type contains ≥/>. Use ≤/< instead. -/
#print filter.is_trans_ge /- the type contains ≥/>. Use ≤/< instead. -/
#print filter.Liminf_le_Liminf /- the type contains ≥/>. Use ≤/< instead. -/
#print filter.is_bounded_under_inf /- the type contains ≥/>. Use ≤/< instead. -/

-- order/galois_connection.lean
#print nat.galois_connection_mul_div /- the type contains ≥/>. Use ≤/< instead. -/

-- order/filter/lift.lean
#print filter.lift_infi' /- the type contains ≥/>. Use ≤/< instead. -/

-- order/filter/basic.lean
#print filter.mem_at_top_sets /- the type contains ≥/>. Use ≤/< instead. -/
#print filter.infi_neq_bot_iff_of_directed /- the type contains ≥/>. Use ≤/< instead. -/
#print filter.tendsto_at_top_principal /- the type contains ≥/>. Use ≤/< instead. -/
#print filter.map_div_at_top_eq_nat /- the type contains ≥/>. Use ≤/< instead. -/
#print filter.mem_infi /- the type contains ≥/>. Use ≤/< instead. -/
#print filter.tendsto_at_top_at_bot /- the type contains ≥/>. Use ≤/< instead. -/
#print filter.infi_neq_bot_of_directed /- the type contains ≥/>. Use ≤/< instead. -/
#print filter.tendsto_at_top' /- the type contains ≥/>. Use ≤/< instead. -/
#print filter.infi_sets_eq /- the type contains ≥/>. Use ≤/< instead. -/
#print filter.map_at_top_eq_of_gc /- the type contains ≥/>. Use ≤/< instead. -/
#print filter.map_infi_eq /- the type contains ≥/>. Use ≤/< instead. -/
#print filter.map_binfi_eq /- the type contains ≥/>. Use ≤/< instead. -/

-- order/complete_lattice.lean
#print lattice.infi_eq_bot /- the type contains ≥/>. Use ≤/< instead. -/
#print lattice.Inf_eq_bot /- the type contains ≥/>. Use ≤/< instead. -/

-- order/basic.lean
#print dense_or_discrete /- the type contains ≥/>. Use ≤/< instead. -/
#print ge.is_total_preorder /- the type contains ≥/>. Use ≤/< instead. -/
#print gt.is_asymm /- the type contains ≥/>. Use ≤/< instead. -/
#print ge.is_total /- the type contains ≥/>. Use ≤/< instead. -/
#print ge.is_antisymm /- the type contains ≥/>. Use ≤/< instead. -/
#print gt.is_trans /- the type contains ≥/>. Use ≤/< instead. -/
#print ge.is_trans /- the type contains ≥/>. Use ≤/< instead. -/
#print ge.is_partial_order /- the type contains ≥/>. Use ≤/< instead. -/
#print eq_of_le_of_forall_ge_of_dense /- the type contains ≥/>. Use ≤/< instead. -/
#print ge.is_linear_order /- the type contains ≥/>. Use ≤/< instead. -/
#print ge_of_eq /- the type contains ≥/>. Use ≤/< instead. -/
#print gt.is_antisymm /- the type contains ≥/>. Use ≤/< instead. -/
#print le_of_forall_ge_of_dense /- the type contains ≥/>. Use ≤/< instead. -/
#print ge.is_preorder /- the type contains ≥/>. Use ≤/< instead. -/
#print gt.is_trichotomous /- the type contains ≥/>. Use ≤/< instead. -/
#print gt.is_strict_order /- the type contains ≥/>. Use ≤/< instead. -/
#print gt.is_irrefl /- the type contains ≥/>. Use ≤/< instead. -/
#print eq_of_le_of_forall_le_of_dense /- the type contains ≥/>. Use ≤/< instead. -/
#print le_of_forall_le_of_dense /- the type contains ≥/>. Use ≤/< instead. -/
#print ge.is_refl /- the type contains ≥/>. Use ≤/< instead. -/

-- number_theory/pell.lean
#print pell.is_pell_pell_zd /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.pell_zd /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.xy_succ_succ /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.xn_add /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.y_mul_dvd /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.eq_pell /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.xn_modeq_x2n_sub /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.yn /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.yz /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.yn_add /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.dvd_of_ysq_dvd /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.is_pell_mul /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.x_sub_y_dvd_pow_lem /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.eq_of_xn_modeq' /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.pell_eq /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.d_pos /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.yz_succ /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.xz_succ /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.x_pos /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.pell_val /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.eq_of_xn_modeq_lem2 /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.is_pell_one /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.yn_zero /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.pell_zd_add /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.xn_succ /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.xn_ge_a_pow /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.pell_zd_sub /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.n_lt_xn /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.xn_modeq_x4n_add /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.eq_of_xn_modeq /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.is_pell_norm /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.az /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.is_pell_conj /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.yn_ge_n /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.eq_of_xn_modeq_le /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.yz_sub /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.n_lt_a_pow /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.xn_zero /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.xn_modeq_x2n_add /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.matiyasevic /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.xn_modeq_x2n_sub_lem /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.xn_succ_succ /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.modeq_of_xn_modeq /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.xn_one /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.xz_succ_succ /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.xy_coprime /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.dnsq /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.eq_pow_of_pell /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.eq_pow_of_pell_lem /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.pell_eqz /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.xn_modeq_x4n_sub /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.y_increasing /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.x_increasing /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.is_pell /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.eq_of_xn_modeq_lem1 /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.asq_pos /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.y_dvd_iff /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.xz /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.xy_modeq_of_modeq /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.pell_zd_succ /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.yn_succ /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.yn_modeq_two /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.xy_modeq_yn /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.is_pell_nat /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.yn_succ_succ /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.yn_one /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.ysq_dvd_yy /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.eq_pell_lem /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.pell_zd_im /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.xz_sub /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.dz_val /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.yz_succ_succ /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.xn_modeq_x2n_add_lem /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.yn_modeq_a_sub_one /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.eq_pell_zd /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.xn /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.x_sub_y_dvd_pow /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.pell_zd_re /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.eq_of_xn_modeq_lem3 /- the type contains ≥/>. Use ≤/< instead. -/
#print pell.pell_zd_succ_succ /- the type contains ≥/>. Use ≤/< instead. -/

-- number_theory/dioph.lean
#print dioph.xn_dioph /- the type contains ≥/>. Use ≤/< instead. -/
#print dioph.pell_dioph /- the type contains ≥/>. Use ≤/< instead. -/

-- measure_theory/integration.lean
#print measure_theory.lintegral_eq_nnreal /- the type contains ≥/>. Use ≤/< instead. -/

-- linear_algebra/dimension.lean
#print exists_mem_ne_zero_of_dim_pos /- the type contains ≥/>. Use ≤/< instead. -/

-- group_theory/order_of_element.lean
#print exists_pow_eq_one /- the type contains ≥/>. Use ≤/< instead. -/
#print order_of_pos /- the type contains ≥/>. Use ≤/< instead. -/

-- data/real/pi.lean
#print real.sqrt_two_add_series_zero_nonneg /- the type contains ≥/>. Use ≤/< instead. -/
#print real.sqrt_two_add_series_nonneg /- the type contains ≥/>. Use ≤/< instead. -/
#print real.pi_gt_three /- the type contains ≥/>. Use ≤/< instead. -/
#print real.pi_gt_sqrt_two_add_series /- the type contains ≥/>. Use ≤/< instead. -/
#print real.pi_gt_314 /- the type contains ≥/>. Use ≤/< instead. -/

-- data/real/nnreal.lean
#print nnreal.of_real_lt_iff_lt_coe /- the type contains ≥/>. Use ≤/< instead. -/
#print nnreal.le_of_real_iff_coe_le /- the type contains ≥/>. Use ≤/< instead. -/
#print nnreal.le_of_forall_epsilon_le /- the type contains ≥/>. Use ≤/< instead. -/

-- data/real/hyperreal.lean
#print hyperreal.infinite_pos_iff_infinite_and_pos /- the type contains ≥/>. Use ≤/< instead. -/
#print hyperreal.is_st_iff_abs_sub_lt_delta /- the type contains ≥/>. Use ≤/< instead. -/
#print hyperreal.lt_neg_of_pos_of_infinitesimal /- the type contains ≥/>. Use ≤/< instead. -/
#print hyperreal.infinite_pos_iff_infinitesimal_inv_pos /- the type contains ≥/>. Use ≤/< instead. -/
#print hyperreal.infinitesimal_pos_iff_infinite_pos_inv /- the type contains ≥/>. Use ≤/< instead. -/
#print hyperreal.gt_of_neg_of_infinitesimal /- the type contains ≥/>. Use ≤/< instead. -/
#print hyperreal.infinite_pos_iff_infinite_of_nonneg /- the type contains ≥/>. Use ≤/< instead. -/
#print hyperreal.neg_lt_of_tendsto_zero_of_pos /- the type contains ≥/>. Use ≤/< instead. -/
#print hyperreal.infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos /- the type contains ≥/>. Use ≤/< instead. -/
#print hyperreal.infinite_pos_iff_infinite_of_pos /- the type contains ≥/>. Use ≤/< instead. -/
#print hyperreal.lt_of_tendsto_zero_of_pos /- the type contains ≥/>. Use ≤/< instead. -/
#print hyperreal.infinitesimal_def /- the type contains ≥/>. Use ≤/< instead. -/
#print hyperreal.infinite_pos_def /- the type contains ≥/>. Use ≤/< instead. -/
#print hyperreal.lt_of_pos_of_infinitesimal /- the type contains ≥/>. Use ≤/< instead. -/
#print hyperreal.infinite_neg_mul_of_not_infinitesimal_pos_infinite_neg /- the type contains ≥/>. Use ≤/< instead. -/
#print hyperreal.epsilon_lt_pos /- the type contains ≥/>. Use ≤/< instead. -/
#print hyperreal.pos_of_infinite_pos /- the type contains ≥/>. Use ≤/< instead. -/

-- data/real/cau_seq.lean
#print cau_seq.equiv_def₃ /- the type contains ≥/>. Use ≤/< instead. -/
#print is_cau_seq.cauchy₂ /- the type contains ≥/>. Use ≤/< instead. -/
#print cau_seq.cauchy /- the type contains ≥/>. Use ≤/< instead. -/
#print cau_seq.le_of_exists /- the type contains ≥/>. Use ≤/< instead. -/
#print exists_forall_ge_and /- the type contains ≥/>. Use ≤/< instead. -/
#print cau_seq.cauchy₂ /- the type contains ≥/>. Use ≤/< instead. -/
#print cau_seq.abv_pos_of_not_lim_zero /- the type contains ≥/>. Use ≤/< instead. -/
#print rat_inv_continuous_lemma /- the type contains ≥/>. Use ≤/< instead. -/
#print is_cau_seq.cauchy₃ /- the type contains ≥/>. Use ≤/< instead. -/
#print cau_seq.of_near /- the type contains ≥/>. Use ≤/< instead. -/
#print rat_add_continuous_lemma /- the type contains ≥/>. Use ≤/< instead. -/
#print cau_seq.cauchy₃ /- the type contains ≥/>. Use ≤/< instead. -/
#print cau_seq.bounded' /- the type contains ≥/>. Use ≤/< instead. -/
#print rat_mul_continuous_lemma /- the type contains ≥/>. Use ≤/< instead. -/
#print cau_seq.inv_aux /- the type contains ≥/>. Use ≤/< instead. -/

-- data/real/basic.lean
#print real.le_of_forall_epsilon_le /- the type contains ≥/>. Use ≤/< instead. -/
#print real.mk_le_of_forall_le /- the type contains ≥/>. Use ≤/< instead. -/
#print real.of_near /- the type contains ≥/>. Use ≤/< instead. -/
#print real.mk_near_of_forall_near /- the type contains ≥/>. Use ≤/< instead. -/
#print real.le_mk_of_forall_le /- the type contains ≥/>. Use ≤/< instead. -/

-- data/polynomial.lean
#print polynomial.degree_eq_iff_nat_degree_eq_of_pos /- the type contains ≥/>. Use ≤/< instead. -/

-- data/padics/padic_numbers.lean
#print padic.rat_dense' /- the type contains ≥/>. Use ≤/< instead. -/
#print padic.rat_dense /- the type contains ≥/>. Use ≤/< instead. -/
#print padic.exi_rat_seq_conv /- the type contains ≥/>. Use ≤/< instead. -/
#print padic.complete' /- the type contains ≥/>. Use ≤/< instead. -/
#print padic_seq.stationary_point_spec /- the type contains ≥/>. Use ≤/< instead. -/
#print padic_norm_e.nonneg /- the type contains ≥/>. Use ≤/< instead. -/
#print padic_seq.norm_nonneg /- the type contains ≥/>. Use ≤/< instead. -/
#print padic_norm_e.defn /- the type contains ≥/>. Use ≤/< instead. -/
#print padic.padic_norm_e_lim_le /- the type contains ≥/>. Use ≤/< instead. -/

-- data/num/lemmas.lean
#print num.cmp_to_nat /- the type contains ≥/>. Use ≤/< instead. -/
#print pos_num.cmp_to_nat /- the type contains ≥/>. Use ≤/< instead. -/
#print pos_num.pred_to_nat /- the type contains ≥/>. Use ≤/< instead. -/
#print znum.cmp_to_int /- the type contains ≥/>. Use ≤/< instead. -/

-- data/nat/dist.lean
#print nat.dist_eq_sub_of_ge /- the type contains ≥/>. Use ≤/< instead. -/

-- data/list/basic.lean
#print list.pairwise_gt_iota /- the type contains ≥/>. Use ≤/< instead. -/
#print list.insert_nth_remove_nth_of_ge /- the type contains ≥/>. Use ≤/< instead. -/

-- data/hash_map.lean
#print hash_map.valid.modify /- the type contains ≥/>. Use ≤/< instead. -/

-- data/complex/exponential.lean
#print is_cau_of_mono_bounded /- the type contains ≥/>. Use ≤/< instead. -/
#print cauchy_product /- the type contains ≥/>. Use ≤/< instead. -/
#print is_cau_of_decreasing_bounded /- the type contains ≥/>. Use ≤/< instead. -/
#print forall_ge_le_of_forall_le_succ /- the type contains ≥/>. Use ≤/< instead. -/

-- analysis/normed_space/basic.lean
#print summable_iff_vanishing_norm /- the type contains ≥/>. Use ≤/< instead. -/
#print normed_group.tendsto_nhds_zero /- the type contains ≥/>. Use ≤/< instead. -/

-- algebra/order_functions.lean
#print min_le_add_of_nonneg_left /- the type contains ≥/>. Use ≤/< instead. -/
#print min_le_add_of_nonneg_right /- the type contains ≥/>. Use ≤/< instead. -/
#print max_le_add_of_nonneg /- the type contains ≥/>. Use ≤/< instead. -/

-- algebra/order.lean
#print gt_iff_lt /- the type contains ≥/>. Use ≤/< instead. -/
#print ordering.compares.eq_gt /- the type contains ≥/>. Use ≤/< instead. -/
#print ge_iff_le /- the type contains ≥/>. Use ≤/< instead. -/

-- algebra/char_p.lean
#print zmod.to_module' /- the type contains ≥/>. Use ≤/< instead. -/
#print char_p.char_is_prime_of_ge_two /- the type contains ≥/>. Use ≤/< instead. -/


external command exited with status 1

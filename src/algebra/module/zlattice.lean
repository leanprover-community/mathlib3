/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import analysis.normed.order.basic
import linear_algebra.free_module.pid
import measure_theory.group.fundamental_domain
import ring_theory.localization.module

/-!
# ℤ-lattices
Let `E` be a finite dimensional vector space over a `normed_lattice_field` `K` that is also
a `floor_ring`, e.g. `ℚ` or `ℝ`. A (full) ℤ-lattice `L` of `E` is a discrete subgroup of `E` such
that `L` spans `E` over `K`.

The ℤ-lattice `L` can be defined in two ways:
* For `b` a basis of `E`, then `L : submodule.span ℤ (set.range b)` is a ℤ-lattice of `E`.
* As `L : add_subgroup E` with the additional properties:
  `(hd : ∀ r : ℝ, (L ∩ (metric.closed_ball 0 r)).finite)`, that is `L` is discrete
  `(hs : submodule.span ℝ (L : set E) = ⊤)`, that is `L` spans `E` over `K`.

## Main results
* `zspan.is_add_fundamental_domain`: for `L : submodule.span ℤ (set.range b)` a ℤ-lattice, proves
that the set defined by `zspan.fundamental_domain` is indeed a fundamental domain.
* `zlattice.dim`: for `L : add_subgroup E` with `L` discrete and spanning `E` over `K`, proves that
`finrank ℤ L = finrank K E`.
-/

open_locale classical

noncomputable theory

section zspan

open measure_theory measurable_set submodule

variables {E ι : Type*}

section basis

variables {R K : Type*} [comm_ring R] [division_ring K] [algebra R K] [add_comm_group E]
  [module K E] [module R E] [is_scalar_tower R K E] [no_zero_smul_divisors R K]
variables (b : basis ι K E)

variable (R)

/-- The R-lattice spanned by `b` admits `b` as a R-basis. -/
def zspan.basis : basis ι R (span R (set.range b)) :=
basis.span (b.linear_independent.restrict_scalars (smul_left_injective R (ne_zero.ne 1)))

@[simp]
lemma zspan.basis_apply (i : ι) : (zspan.basis R b i : E) = b i :=
  by simp only [zspan.basis, basis.span_apply]

@[simp]
lemma zspan.repr_apply (m : span R (set.range b)) [finite ι] (i : ι)  :
  algebra_map R K ((zspan.basis R b).repr m i) = b.repr m i :=
begin
  casesI nonempty_fintype ι,
  rw ← congr_arg (coe : _ → E) (basis.sum_repr (zspan.basis R b) m),
  simp_rw [coe_sum, coe_smul_of_tower, zspan.basis_apply, linear_equiv.map_sum,
    ← is_scalar_tower.algebra_map_smul K, b.repr.map_smul, basis.repr_self, algebra_map_smul,
    finsupp.smul_single, finset.sum_apply', algebra.algebra_map_eq_smul_one, finsupp.single_apply,
    finset.sum_ite_eq', finset.mem_univ],
  refl,
end

lemma zspan.mem_span_iff [finite ι] (m : E) :
  m ∈ span R (set.range b) ↔ ∀ i, ∃ c : R, b.repr m i = algebra_map R K c :=
begin
  casesI nonempty_fintype ι,
  split,
  { exact λ hm i, ⟨(zspan.basis R b).repr ⟨m, hm⟩ i, (zspan.repr_apply R b ⟨m, hm⟩ i).symm⟩, },
  { intros h,
    rw ← b.sum_repr m,
    refine sum_mem (λ i _ , _),
    rw [(h i).some_spec, @is_scalar_tower.algebra_map_smul R K],
    exact smul_mem _ _ (subset_span (set.mem_range_self i)), }
end

end basis

section normed_lattice_field

variables {K : Type*} [normed_lattice_field K]
variables [normed_add_comm_group E] [normed_space K E]
variables (b : basis ι K E)

/-- The fundamental domain of the ℤ-lattice spanned by `b`. See `zspan.is_add_fundamental_domain`
for the proof that it is the fundamental domain. -/
def zspan.fundamental_domain : set E := { m | ∀ i : ι, b.repr m i ∈ set.Ico (0 : K) 1 }

variables [floor_ring K]

section fintype

variable [fintype ι]

/-- The map that sends a vector of `E` to the element of the ℤ-lattice spanned by `b` obtained
by rounding down its coordinates on the basis `b`. -/
def zspan.floor_map : E → span ℤ (set.range b) :=
λ m, finset.univ.sum (λ i, int.floor (b.repr m i) • zspan.basis ℤ b i)

lemma zspan.floor_map_single (m : E) (i : ι) :
  b.repr (zspan.floor_map b m) i = int.floor (b.repr m i) :=
by simp only [zspan.floor_map, zsmul_eq_smul_cast K, b.repr.map_smul, finsupp.single_apply,
  finset.sum_apply', basis.repr_self, finsupp.smul_single', mul_one, finset.sum_ite_eq',
  finset.mem_univ, if_true, coe_sum, coe_smul_of_tower, zspan.basis_apply, linear_equiv.map_sum]

/-- The map that sends a vector `E` to the fundamental domain of the lattice,
see `zspan.fract_mem_fundamental_domain`. -/
def zspan.fract_map : E → E := λ m, m - zspan.floor_map b m

lemma zspan.fract_map_def (m : E) : zspan.fract_map b m = m - zspan.floor_map b m := rfl

@[simp]
lemma zspan.fract_map_single (m : E) (i : ι):
  b.repr (zspan.fract_map b m) i = int.fract (b.repr m i) :=
by rw [zspan.fract_map, map_sub, finsupp.coe_sub, pi.sub_apply, zspan.floor_map_single, int.fract]

@[simp]
lemma zspan.fract_map_zspan_add (m : E) {v : E} (h : v ∈ span ℤ (set.range b)) :
  zspan.fract_map b (v + m) = zspan.fract_map b m :=
begin
  refine (basis.ext_elem_iff b).mpr (λ i, _),
  simp_rw [zspan.fract_map_single, int.fract_eq_fract],
  use (zspan.basis ℤ b).repr ⟨v, h⟩ i,
  rw [map_add, finsupp.coe_add, pi.add_apply, add_tsub_cancel_right,
    ← (eq_int_cast (algebra_map ℤ K) _), zspan.repr_apply, coe_mk],
end

lemma zspan.mem_fundamental_domain {x : E} :
  x ∈ (zspan.fundamental_domain b) ↔ zspan.fract_map b x = x :=
by simp only [basis.ext_elem_iff b, zspan.fundamental_domain, set.mem_Ico, set.mem_set_of_eq,
  zspan.fract_map_single, int.fract_eq_self]

lemma zspan.fract_map_mem_fundamental_domain (x : E) :
  zspan.fract_map b x ∈ zspan.fundamental_domain b :=
by simp only [zspan.mem_fundamental_domain, basis.ext_elem_iff b, zspan.fract_map_single,
  int.fract_fract, eq_self_iff_true, implies_true_iff]

lemma zspan.fract_map_eq_iff (m n : E) :
zspan.fract_map b m = zspan.fract_map b n ↔ -m + n ∈ span ℤ (set.range b) :=
begin
  rw [eq_comm, basis.ext_elem_iff b],
  simp only [int.fract_eq_fract, zspan.fract_map_single],
  simp_rw [zspan.mem_span_iff, sub_eq_neg_add, map_add, linear_equiv.map_neg, finsupp.coe_add,
    finsupp.coe_neg, pi.add_apply, pi.neg_apply, ← (eq_int_cast (algebra_map ℤ K) _)],
end

lemma zspan.fract_map_le (m : E) :
  ‖zspan.fract_map b m‖ ≤ finset.univ.sum (λ j, ‖b j‖) :=
begin
  calc
    ‖zspan.fract_map b m‖
        = ‖finset.univ.sum (λ i, b.repr (zspan.fract_map b m) i • b i)‖ : by rw b.sum_repr
    ... = ‖finset.univ.sum (λ i, int.fract (b.repr m i) • b i)‖ : by simp_rw zspan.fract_map_single
    ... ≤ finset.univ.sum (λ i, ‖int.fract (b.repr m i) • b i‖) : norm_sum_le _ _
    ... ≤ finset.univ.sum (λ i, ‖int.fract (b.repr m i)‖ * ‖b i‖) : by simp_rw norm_smul
    ... ≤ finset.univ.sum (λ j, ‖b j‖) : finset.sum_le_sum (λ i _, _),
    suffices : ‖int.fract (((b.repr) m) i)‖ ≤ 1,
    { convert mul_le_mul_of_nonneg_right this (norm_nonneg _ : 0 ≤ ‖b i ‖),
      exact (one_mul _).symm, },
    rw (norm_one.symm : 1 = ‖(1 : K)‖),
    apply norm_le_norm_of_abs_le_abs,
    rw [abs_one, int.abs_fract],
    exact le_of_lt (int.fract_lt_one _),
end

end fintype

lemma zspan.fundamental_domain_metric_bounded [finite ι] :
  metric.bounded (zspan.fundamental_domain b) :=
begin
  casesI nonempty_fintype ι,
  use 2 * finset.univ.sum (λ j, ‖b j‖),
  intros x hx y hy,
  refine le_trans (dist_le_norm_add_norm x y) _,
  rw [← (zspan.mem_fundamental_domain b).mp hx, ← (zspan.mem_fundamental_domain b).mp hy],
  refine (add_le_add (zspan.fract_map_le b x) (zspan.fract_map_le b y)).trans _,
  rw ← two_mul,
end

lemma zspan.exist_vadd_mem_fundamental_domain [finite ι] (x : E) :
  ∃! v : span ℤ (set.range b), v +ᵥ x ∈ zspan.fundamental_domain b :=
begin
  casesI nonempty_fintype ι,
  use (-zspan.floor_map b x),
  split,
  { simp_rw [zspan.fundamental_domain, set.mem_Ico, vadd_def, vadd_eq_add,
      add_subgroup_class.coe_neg, neg_add_eq_sub, ← zspan.fract_map_def],
    simp only [zspan.fract_map_single, int.fract_nonneg, int.fract_lt_one, true_and,
      set.mem_set_of_eq, implies_true_iff], },
  { intros y _,
    rwa [subtype.ext_iff, ← add_right_inj x, add_subgroup_class.coe_neg, ← sub_eq_add_neg,
      ← zspan.fract_map_def, ← zspan.fract_map_zspan_add b _ (subtype.mem y), add_comm,
      ← vadd_eq_add, ← vadd_def, eq_comm, ← zspan.mem_fundamental_domain], },
end

open subtype

/-- The map `zspan.fract_map` lift to an equiv between `E ⧸ span ℤ (set.range b)`
and `zspan.fundamental_domain b` . -/
def zspan.quo_fract_equiv [fintype ι] : E ⧸ span ℤ (set.range b) ≃ (zspan.fundamental_domain b) :=
begin
  refine equiv.of_bijective _ _,
  { refine λ q, quotient.lift_on' q _ _,
    { exact λ x, ⟨zspan.fract_map b x, zspan.fract_map_mem_fundamental_domain b x⟩, },
    { exact λ _ _ h, mk_eq_mk.mpr
        ((zspan.fract_map_eq_iff b _ _).mpr (quotient_add_group.left_rel_apply.mp h)), }},
  { exact ⟨λ x y, quotient.induction_on₂' x y (λ a c h, by { rwa [quotient.eq',
      quotient_add_group.left_rel_apply, mem_to_add_subgroup, ← zspan.fract_map_eq_iff,
      ← @mk_eq_mk _ (zspan.fundamental_domain b)], }),
      λ y, ⟨quotient.mk' y, ext_iff.mpr ((zspan.mem_fundamental_domain b).mp (subtype.mem y))⟩⟩, },
end

lemma zspan.sub_quo_fract_mem (x : E) [fintype ι] :
  x - zspan.quo_fract_equiv b (quotient.mk' x) ∈ span ℤ (set.range b) :=
begin
  change x - zspan.fract_map b x ∈ span ℤ (set.range b),
  simp only [zspan.fract_map_def, sub_sub_cancel, coe_mem],
end

end normed_lattice_field

section real

variables [normed_add_comm_group E] [normed_space ℝ E]
variables (b : basis ι ℝ E)

lemma zspan.fundamental_domain_measurable [measurable_space E] [opens_measurable_space E]
  [finite ι]:
  measurable_set (zspan.fundamental_domain b) :=
begin
  haveI : finite_dimensional ℝ E := finite_dimensional.of_fintype_basis b,
  let f := (finsupp.linear_equiv_fun_on_finite ℝ ℝ ι).to_linear_map.comp b.repr.to_linear_map,
  let D : set (ι → ℝ) := set.pi set.univ (λ i : ι, (set.Ico (0 : ℝ) 1)),
  rw ( _ : zspan.fundamental_domain b = f⁻¹' D),
  { refine measurable_set_preimage (linear_map.continuous_of_finite_dimensional f).measurable _,
    exact pi set.univ.to_countable (λ (i : ι) (H : i ∈ set.univ), measurable_set_Ico), },
  { ext,
    simp only [zspan.fundamental_domain, set.mem_set_of_eq, linear_map.coe_comp,
      linear_equiv.coe_to_linear_map, set.mem_preimage, function.comp_app, set.mem_univ_pi,
      finsupp.linear_equiv_fun_on_finite_apply], },
end

lemma zspan.is_add_fundamental_domain [finite ι] [measurable_space E] [opens_measurable_space E]
  (μ : measure E) :
  is_add_fundamental_domain (span ℤ (set.range b)).to_add_subgroup
    (zspan.fundamental_domain b) μ :=
begin
  casesI nonempty_fintype ι,
  exact is_add_fundamental_domain.mk'
    (null_measurable_set (zspan.fundamental_domain_measurable b))
    (λ x, zspan.exist_vadd_mem_fundamental_domain b x),
end

end real

end zspan

section zlattice

open submodule

variables {K : Type*} [normed_lattice_field K] [floor_ring K]
variables {E : Type*} [normed_add_comm_group E] [normed_space K E]
variables [finite_dimensional K E] {L : add_subgroup E}
variables (hd : ∀ r : ℝ, ((L : set E) ∩ (metric.closed_ball 0 r)).finite)
variables (hs : span K (L : set E) = ⊤)

include hd hs

lemma zlattice.fg : add_subgroup.fg L :=
begin
  suffices : L.to_int_submodule.fg,
  { rwa [fg_iff_add_subgroup_fg, add_subgroup.to_int_submodule_to_add_subgroup] at this, },
  obtain ⟨s, ⟨h1, ⟨h2, h3⟩⟩⟩ := exists_linear_independent K (L.to_int_submodule : set E),
  -- Let `s` be a maximal `K`-linear independent family of elements of `L`. We show that
  -- `L` is finitely generated (as a ℤ-module) because its fits in the exact sequence
  -- `0 → L ∩ ker (span ℤ s) → L → L / ker (span ℤ s) → 0`
  -- with `L ∩ ker (span ℤ s)` and `L / ker (span ℤ s)` finitely generated.
  refine fg_of_fg_map_of_fg_inf_ker (mkq (span ℤ s)) _ _,
  { rw submodule.fg_def,
    use (map (span ℤ s).mkq (add_subgroup.to_int_submodule L)),
    split,
    { haveI : fintype s := set.finite.fintype h3.finite,
      let b := basis.mk h3 (by
        simp only [h2, hs, subtype.range_coe, add_subgroup.coe_to_int_submodule, top_le_iff]),
      rw (_ : submodule.span ℤ s = submodule.span ℤ (set.range b)),
      -- Elements of `L / ker (span ℤ s)` are in bijection with element of
      -- `L ∩ fundamental_domain s` so there are finitely many since
      -- `fundamental_domain s` is bounded.
      refine @set.finite.of_finite_image _ _ _ ((coe : _ → E) ∘ (zspan.quo_fract_equiv b)) _ _,
      { obtain ⟨C, hC⟩ := metric.bounded.subset_ball (zspan.fundamental_domain_metric_bounded b) 0,
        refine set.finite.subset (hd C) _,
        rintros _ ⟨_, ⟨⟨x, ⟨hx, rfl⟩⟩, rfl⟩⟩,
        split,
        { suffices : span ℤ (set.range b) ≤ L.to_int_submodule,
          { rw [set_like.mem_coe, ← neg_mem_iff, ← add_mem_cancel_left (by convert hx : x ∈ L),
              ← sub_eq_add_neg],
            exact this (zspan.sub_quo_fract_mem b x), },
          { simpa only [submodule.span_le, add_subgroup.coe_to_int_submodule, basis.coe_mk,
              subtype.range_coe_subtype, set.set_of_mem_eq], }},
        { simp only [mkq_apply, function.comp_app, mem_closed_ball_zero_iff],
          exact mem_closed_ball_zero_iff.mp (hC (zspan.fract_map_mem_fundamental_domain b x)), }},
      { refine function.injective.inj_on (function.injective.comp subtype.coe_injective
        (zspan.quo_fract_equiv b).injective) _, },
      { congr,
        simp only [basis.coe_mk, subtype.range_coe_subtype, set.set_of_mem_eq], }},
    { exact submodule.span_eq _, }},
  -- `L ∩ ker (span ℤ s)` is finitely generated because `s` is finite.
  { rw [submodule.ker_mkq (submodule.span ℤ s), inf_of_le_right (submodule.span_le.mpr h1)],
    exact submodule.fg_span (linear_independent.finite h3), }
end

lemma zlattice.module.finite : module.finite ℤ L :=
begin
rw [module.finite.iff_add_group_fg, add_group.fg_iff_add_monoid.fg],
exact (add_monoid.fg_iff_add_submonoid_fg _).mpr
  ((add_subgroup.fg_iff_add_submonoid.fg L).mp (zlattice.fg hd hs)),
end

variable [no_zero_smul_divisors ℤ E]

lemma zlattice.module.free : module.free ℤ L :=
begin
  haveI : module.finite ℤ L := zlattice.module.finite hd hs,
  haveI : no_zero_smul_divisors ℤ L,
  { change no_zero_smul_divisors ℤ L.to_int_submodule,
    exact submodule.no_zero_smul_divisors _, },
  exact module.free_of_finite_type_torsion_free',
end

variables [module ℚ E]

open finite_dimensional

lemma zlattice.rank : finrank ℤ L = finrank K E :=
begin
  haveI : module.finite ℤ L := zlattice.module.finite hd hs,
  haveI : module.free ℤ L := zlattice.module.free hd hs,
  let b := module.free.choose_basis ℤ L,
  have h_spaneq : span ℤ (set.range ((coe : L → E) ∘ b)) = L.to_int_submodule,
  { convert congr_arg (submodule.map L.to_int_submodule.subtype) b.span_eq,
    { rw [submodule.map_span, submodule.coe_subtype, set.range_comp], },
    { rw map_subtype_top, }},
  have h_spantop : submodule.span K (set.range ((coe : L → E) ∘ b)) = ⊤,
  { rwa [← @submodule.span_span_of_tower ℤ E K _, h_spaneq], },
  rw module.free.finrank_eq_card_choose_basis_index,
  apply le_antisymm,
  { -- The proof proceeds by proving that there is ℤ-relation between the
    -- vectors of `b` otherwise.
    have h : linear_independent ℤ (λ x : set.range ((coe : L → E) ∘ b), (x : E)),
    { rw linear_independent_subtype_range
        (function.injective.comp subtype.coe_injective (basis.injective b)),
      convert b.linear_independent.map' L.to_int_submodule.subtype (submodule.ker_subtype _), },
    contrapose! h,
    -- Extract a `K`-basis `e` of `E` from `b`
    obtain ⟨t, ⟨ht1, ⟨ht2, ht3⟩⟩⟩ := exists_linear_independent K (set.range ((coe : L → E) ∘ b)),
    haveI : fintype t := set.finite.fintype ((set.range (coe ∘ b)).to_finite.subset ht1),
    let e : basis t K E := basis.mk ht3
      (by { rw [subtype.range_coe, ht2, h_spantop], exact le_rfl, }),
    -- Then there exists `v` in `b ∖ e`
    rsuffices ⟨v, hv⟩ : ((set.range ((coe : L → E) ∘ b)) \ (set.range e)).nonempty,
    { -- and there exist `n, m : ℕ`, `n ≠ m` such that `(n - m) • v ∈ span ℤ e`.
      obtain ⟨n, -, m, -, hnm, heq⟩ := @set.infinite.exists_ne_map_eq_of_maps_to ℤ _ _ _
        (λ n : ℤ, zspan.fract_map e (n • v)) set.infinite_univ _
        (hd (finset.univ.sum (λ j, ‖e j‖))),
      -- from this we will prove that `e ∪ {v}` is not ℤ-linear independent which will give
      -- the required contradiction
      { suffices : ¬ linear_independent ℤ (λ x : has_insert.insert v (set.range e), (x : E)),
        { contrapose! this,
          refine linear_independent.mono _ this,
          exact set.insert_subset.mpr ⟨set.mem_of_mem_diff hv, by
          { simp only [ht1, basis.coe_mk, subtype.range_coe_subtype, set.set_of_mem_eq], }⟩},
        rw (@linear_independent.iff_fraction_ring ℤ ℚ _ _ _ _ E _ _ _ _ _ _).not,
        { -- We prove finally that `e ∪ {v}` is not ℤ-linear independent or, equivalently,
          -- not ℚ-linear independent by showing that `v ∈ span ℚ e`.
          rw (linear_independent_insert (set.not_mem_of_mem_diff hv)).not,
          push_neg,
          intro _,
          have hnz : (-n + m : ℚ) ≠ 0,
          { rwa [add_comm, ← int.cast_neg, ← int.cast_add, int.cast_ne_zero, ← int.sub_eq_add_neg,
              ne.def, int.sub_eq_zero_iff_eq.not, eq_comm], },
          apply (submodule.smul_mem_iff (span ℚ (set.range e)) hnz).mp,
          refine (submodule.span_subset_span ℤ ℚ (set.range e)) _,
          rwa [(by push_cast : - (n : ℚ) + (m : ℚ) = (-n + m : ℤ)), ← zsmul_eq_smul_cast ℚ,
            set_like.mem_coe, add_smul, neg_smul, ← zspan.fract_map_eq_iff], }},
      intros n _,
      split,
      { change _ ∈ L.to_int_submodule,
        simp_rw [zspan.fract_map_def e, ← h_spaneq],
        refine sub_mem _ _,
        { exact zsmul_mem (submodule.subset_span (set.diff_subset _ _ hv)) _, },
        { refine ((span_mono _) (coe_mem (zspan.floor_map e (n • v)))),
          simp only [ht1, basis.coe_mk, subtype.range_coe_subtype, set.set_of_mem_eq], }},
      { exact mem_closed_ball_zero_iff.mpr (zspan.fract_map_le e _), }},
    { rwa [basis.coe_mk, subtype.range_coe_subtype, set.set_of_mem_eq, ← set.to_finset_nonempty,
        ← finset.card_pos, set.to_finset_diff, finset.card_sdiff (set.to_finset_mono ht1),
        set.to_finset_range, set.to_finset_card, ← finrank_eq_card_basis e, tsub_pos_iff_lt,
        finset.card_image_of_injective _],
      exact function.injective.comp subtype.coe_injective (basis.injective _), }},
  { rw [← (@submodule.top_equiv K E _ _ _).finrank_eq, ← h_spantop],
    convert finrank_span_le_card (set.range ((coe : L → E) ∘ b)),
    rw set.to_finset_range,
    exact (finset.univ.card_image_of_injective
      (subtype.coe_injective.comp (basis.injective _))).symm, },
end

end zlattice

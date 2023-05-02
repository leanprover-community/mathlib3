/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import analysis.normed.order.lattice
import linear_algebra.finite_dimensional
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
  `∀ r : ℝ, (L ∩ metric.closed_ball 0 r).finite`, that is `L` is discrete
  `submodule.span ℝ (L : set E) = ⊤`, that is `L` spans `E` over `K`.

## Main results
* `zspan.is_add_fundamental_domain`: for `L : submodule.span ℤ (set.range b)` a ℤ-lattice, proves
that the set defined by `zspan.fundamental_domain` is indeed a fundamental domain.
* `zlattice.dim`: for `L : add_subgroup E` with `L` discrete and spanning `E` over `K`, proves that
`finrank ℤ L = finrank K E`.
-/

open_locale big_operators classical

noncomputable theory

namespace zspan

open measure_theory measurable_set submodule

variables {E ι : Type*}

section normed_lattice_field

variables {K : Type*} [normed_lattice_field K]
variables [normed_add_comm_group E] [normed_space K E]
variables (b : basis ι K E)

/-- The fundamental domain of the ℤ-lattice spanned by `b`. See `zspan.is_add_fundamental_domain`
for the proof that it is the fundamental domain. -/
def fundamental_domain : set E := { m | ∀ i, b.repr m i ∈ set.Ico (0 : K) 1 }

@[simp]
lemma mem_fundamental_domain {m : E} :
  m ∈ fundamental_domain b ↔ ∀ i, b.repr m i ∈ set.Ico (0 : K) 1 := iff.rfl

variables [floor_ring K]

section fintype

variable [fintype ι]

/-- The map that sends a vector of `E` to the element of the ℤ-lattice spanned by `b` obtained
by rounding down its coordinates on the basis `b`. -/
def floor (m : E) : span ℤ (set.range b) := ∑ i, ⌊b.repr m i⌋ • b.restrict_scalars ℤ i

/-- The map that sends a vector of `E` to the element of the ℤ-lattice spanned by `b` obtained
by rounding up its coordinates on the basis `b`. -/
def ceil (m : E) : span ℤ (set.range b) := ∑ i, ⌈b.repr m i⌉ • b.restrict_scalars ℤ i

@[simp]
lemma repr_floor_apply (m : E) (i : ι) :
  b.repr (floor b m) i = ⌊b.repr m i⌋ :=
by simp only [floor, zsmul_eq_smul_cast K, b.repr.map_smul, finsupp.single_apply, finset.sum_apply',
  basis.repr_self, finsupp.smul_single', mul_one, finset.sum_ite_eq', finset.mem_univ, if_true,
  coe_sum, coe_smul_of_tower, basis.restrict_scalars_apply, linear_equiv.map_sum]

@[simp]
lemma repr_ceil_apply (m : E) (i : ι) :
  b.repr (ceil b m) i = ⌈b.repr m i⌉ :=
by simp only [ceil, zsmul_eq_smul_cast K, b.repr.map_smul, finsupp.single_apply, finset.sum_apply',
  basis.repr_self, finsupp.smul_single', mul_one, finset.sum_ite_eq', finset.mem_univ, if_true,
  coe_sum, coe_smul_of_tower, basis.restrict_scalars_apply, linear_equiv.map_sum]

/-- The map that sends a vector `E` to the fundamental domain of the lattice,
see `zspan.fract_mem_fundamental_domain`. -/
def fract : E → E := λ m, m - floor b m

lemma fract_apply (m : E) : fract b m = m - floor b m := rfl

@[simp]
lemma repr_fract_apply (m : E) (i : ι):
  b.repr (fract b m) i = int.fract (b.repr m i) :=
by rw [fract, map_sub, finsupp.coe_sub, pi.sub_apply, repr_floor_apply, int.fract]

@[simp]
lemma fract_fract (m : E) : fract b (fract b m) = fract b m :=
basis.ext_elem b (λ _, by simp only [repr_fract_apply, int.fract_fract])

@[simp]
lemma fract_zspan_add (m : E) {v : E} (h : v ∈ span ℤ (set.range b)) :
  fract b (v + m) = fract b m :=
begin
  refine (basis.ext_elem_iff b).mpr (λ i, _),
  simp_rw [repr_fract_apply, int.fract_eq_fract],
  use (b.restrict_scalars ℤ).repr ⟨v, h⟩ i,
  rw [map_add, finsupp.coe_add, pi.add_apply, add_tsub_cancel_right,
    ← (eq_int_cast (algebra_map ℤ K) _), basis.restrict_scalars_repr_apply, coe_mk],
end

@[simp]
lemma fract_add_zspan (m : E) {v : E} (h : v ∈ span ℤ (set.range b)) :
  fract b (m + v) = fract b m := by { rw [add_comm, fract_zspan_add b m h] }

variable {b}

lemma fract_eq_self {x : E} :
  fract b x = x ↔ x ∈ fundamental_domain b :=
by simp only [basis.ext_elem_iff b, repr_fract_apply, int.fract_eq_self, mem_fundamental_domain,
  set.mem_Ico]

variable (b)

lemma fract_mem_fundamental_domain (x : E) :
  fract b x ∈ fundamental_domain b := fract_eq_self.mp (fract_fract b _)

lemma fract_eq_fract (m n : E) :
  fract b m = fract b n ↔ -m + n ∈ span ℤ (set.range b) :=
begin
  rw [eq_comm, basis.ext_elem_iff b],
  simp_rw [repr_fract_apply, int.fract_eq_fract, eq_comm, basis.mem_span_iff_repr_mem,
    sub_eq_neg_add, map_add, linear_equiv.map_neg, finsupp.coe_add, finsupp.coe_neg, pi.add_apply,
    pi.neg_apply, ← (eq_int_cast (algebra_map ℤ K) _), set.mem_range],
end

lemma norm_fract_le (m : E) :
  ‖fract b m‖ ≤ ∑ i, ‖b i‖ :=
begin
  calc
    ‖fract b m‖ = ‖∑ i, b.repr (fract b m) i • b i‖ : by rw b.sum_repr
            ... = ‖∑ i, int.fract (b.repr m i) • b i‖ : by simp_rw repr_fract_apply
            ... ≤ ∑ i, ‖int.fract (b.repr m i) • b i‖ : norm_sum_le _ _
            ... ≤ ∑ i, ‖int.fract (b.repr m i)‖ * ‖b i‖ : by simp_rw norm_smul
            ... ≤ ∑ i, ‖b i‖ : finset.sum_le_sum (λ i _, _),
    suffices : ‖int.fract (((b.repr) m) i)‖ ≤ 1,
    { convert mul_le_mul_of_nonneg_right this (norm_nonneg _ : 0 ≤ ‖b i ‖),
      exact (one_mul _).symm, },
    rw (norm_one.symm : 1 = ‖(1 : K)‖),
    apply norm_le_norm_of_abs_le_abs,
    rw [abs_one, int.abs_fract],
    exact le_of_lt (int.fract_lt_one _),
end

section unique

variable [unique ι]

@[simp] lemma coe_floor_self (k : K) : (floor (basis.singleton ι K) k : K) = ⌊k⌋ :=
basis.ext_elem _ (λ _, by rw [repr_floor_apply, basis.singleton_repr, basis.singleton_repr])

@[simp] lemma coe_fract_self (k : K) : (fract (basis.singleton ι K) k : K) = int.fract k :=
basis.ext_elem _ (λ _, by rw [repr_fract_apply, basis.singleton_repr, basis.singleton_repr])

end unique

end fintype

lemma fundamental_domain_bounded [finite ι] :
  metric.bounded (fundamental_domain b) :=
begin
  casesI nonempty_fintype ι,
  use 2 * ∑ j, ‖b j‖,
  intros x hx y hy,
  refine le_trans (dist_le_norm_add_norm x y) _,
  rw [← fract_eq_self.mpr hx, ← fract_eq_self.mpr hy],
  refine (add_le_add (norm_fract_le b x) (norm_fract_le b y)).trans _,
  rw ← two_mul,
end

lemma exist_unique_vadd_mem_fundamental_domain [finite ι] (x : E) :
  ∃! v : span ℤ (set.range b), v +ᵥ x ∈ fundamental_domain b :=
begin
  casesI nonempty_fintype ι,
  refine ⟨-floor b x, _, λ y _, _⟩,
  { simp_rw [fundamental_domain, set.mem_Ico, vadd_def, vadd_eq_add, add_subgroup_class.coe_neg,
    neg_add_eq_sub, ← fract_apply],
    simp only [repr_fract_apply, int.fract_nonneg, int.fract_lt_one, true_and, set.mem_set_of_eq,
      implies_true_iff], },
  { rwa [subtype.ext_iff, ← add_right_inj x, add_subgroup_class.coe_neg, ← sub_eq_add_neg,
      ← fract_apply, ← fract_zspan_add b _ (subtype.mem y), add_comm, ← vadd_eq_add, ← vadd_def,
      eq_comm, fract_eq_self], },
end

open subtype

/-- The map `zspan.fract_map` lift to an equiv between `E ⧸ span ℤ (set.range b)`
and `zspan.fundamental_domain b`. -/
def quo_fract_equiv [fintype ι] : E ⧸ span ℤ (set.range b) ≃ (fundamental_domain b) :=
begin
  refine equiv.of_bijective _ _,
  { refine λ q, quotient.lift_on' q _ _,
    { exact λ x, ⟨fract b x, fract_mem_fundamental_domain b x⟩, },
    { exact λ _ _ h, mk_eq_mk.mpr
      ((fract_eq_fract b _ _).mpr (quotient_add_group.left_rel_apply.mp h)), }},
  { exact ⟨λ x y, quotient.induction_on₂' x y (λ a c h, by { rwa [quotient.eq',
      quotient_add_group.left_rel_apply, mem_to_add_subgroup, ← fract_eq_fract,
      ← @mk_eq_mk _ (fundamental_domain b)], }),
      λ y, ⟨quotient.mk' y, ext_iff.mpr (fract_eq_self.mpr (subtype.mem y))⟩⟩, },
end

lemma sub_quo_fract_mem (x : E) [fintype ι] :
  x - quo_fract_equiv b (quotient.mk' x) ∈ span ℤ (set.range b) :=
begin
  change x - fract b x ∈ span ℤ (set.range b),
  simp only [fract_apply, sub_sub_cancel, coe_mem],
end

end normed_lattice_field

section real

variables [normed_add_comm_group E] [normed_space ℝ E]
variables (b : basis ι ℝ E)

@[measurability]
lemma fundamental_domain_measurable_set [measurable_space E] [opens_measurable_space E]
  [finite ι] :
  measurable_set (fundamental_domain b) :=
begin
  haveI : finite_dimensional ℝ E := finite_dimensional.of_fintype_basis b,
  let f := (finsupp.linear_equiv_fun_on_finite ℝ ℝ ι).to_linear_map.comp b.repr.to_linear_map,
  let D : set (ι → ℝ) := set.pi set.univ (λ i : ι, (set.Ico (0 : ℝ) 1)),
  rw ( _ : fundamental_domain b = f⁻¹' D),
  { refine measurable_set_preimage (linear_map.continuous_of_finite_dimensional f).measurable _,
    exact pi set.univ.to_countable (λ (i : ι) (H : i ∈ set.univ), measurable_set_Ico), },
  { ext,
    simp only [fundamental_domain, set.mem_set_of_eq, linear_map.coe_comp,
      linear_equiv.coe_to_linear_map, set.mem_preimage, function.comp_app, set.mem_univ_pi,
      finsupp.linear_equiv_fun_on_finite_apply], },
end

protected lemma is_add_fundamental_domain [finite ι] [measurable_space E]
  [opens_measurable_space E] (μ : measure E) :
  is_add_fundamental_domain (span ℤ (set.range b)).to_add_subgroup (fundamental_domain b) μ :=
begin
  casesI nonempty_fintype ι,
  exact is_add_fundamental_domain.mk' (null_measurable_set (fundamental_domain_measurable_set b))
    (λ x, exist_unique_vadd_mem_fundamental_domain b x),
end

end real

end zspan

section zlattice

open submodule

variables (K : Type*) [normed_lattice_field K] [floor_ring K]
variables {E : Type*} [normed_add_comm_group E] [normed_space K E] [finite_dimensional K E]
variables {L : add_subgroup E}
variables (hd : ∀ r : ℝ, ((L : set E) ∩ (metric.closed_ball 0 r)).finite)
variables (hs : span K (L : set E) = ⊤)

include hd hs

lemma zlattice.fg : add_subgroup.fg L :=
begin
  suffices : L.to_int_submodule.fg,
  { rwa [fg_iff_add_subgroup_fg, add_subgroup.to_int_submodule_to_add_subgroup] at this, },
  obtain ⟨s, ⟨h1, ⟨h2, h3⟩⟩⟩ := exists_linear_independent K (L.to_int_submodule : set E),
  -- Let `s` be a maximal `K`-linear independent family of elements of `L`. We show that
  -- `L` is finitely generated (as a ℤ-module) because it fits in the exact sequence
  -- `0 → span ℤ s → L → L / span ℤ s → 0`
  -- with `span ℤ s` and `L / span ℤ s` finitely generated.
  refine fg_of_fg_map_of_fg_inf_ker (mkq (span ℤ s)) _ _,
  { rw submodule.fg_def,
    use (map (span ℤ s).mkq (add_subgroup.to_int_submodule L)),
    split,
    { haveI : fintype s := set.finite.fintype h3.finite,
      let b := basis.mk h3 (by
        simp only [h2, hs, subtype.range_coe, add_subgroup.coe_to_int_submodule, top_le_iff]),
      rw (_ : submodule.span ℤ s = submodule.span ℤ (set.range b)),
      -- Elements of `L / span ℤ s` are in bijection with elements of
      -- `L ∩ fundamental_domain s` so there are finitely many since
      -- `fundamental_domain s` is bounded.
      refine @set.finite.of_finite_image _ _ _ ((coe : _ → E) ∘ (zspan.quo_fract_equiv b)) _ _,
      { obtain ⟨C, hC⟩ := metric.bounded.subset_ball (zspan.fundamental_domain_bounded b) 0,
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
          exact mem_closed_ball_zero_iff.mp (hC (zspan.fract_mem_fundamental_domain b x)), }},
      { refine function.injective.inj_on (function.injective.comp subtype.coe_injective
        (zspan.quo_fract_equiv b).injective) _, },
      { congr,
        simp only [basis.coe_mk, subtype.range_coe_subtype, set.set_of_mem_eq], }},
    { exact submodule.span_eq _, }},
  -- `span ℤ s` is finitely generated because `s` is finite.
  { rw [submodule.ker_mkq (submodule.span ℤ s), inf_of_le_right (submodule.span_le.mpr h1)],
    exact submodule.fg_span (linear_independent.finite h3), }
end

lemma zlattice.module.finite : module.finite ℤ L :=
begin
rw [module.finite.iff_add_group_fg, add_group.fg_iff_add_monoid.fg],
exact (add_monoid.fg_iff_add_submonoid_fg _).mpr
  ((add_subgroup.fg_iff_add_submonoid.fg L).mp (zlattice.fg K hd hs)),
end

lemma zlattice.module.free : module.free ℤ L :=
begin
  haveI : module.finite ℤ L := zlattice.module.finite K hd hs,
  haveI : module ℚ E := module.comp_hom E (algebra_map ℚ K),
  haveI : no_zero_smul_divisors ℤ E := rat_module.no_zero_smul_divisors,
  haveI : no_zero_smul_divisors ℤ L,
  { change no_zero_smul_divisors ℤ L.to_int_submodule,
    exact submodule.no_zero_smul_divisors _, },
  exact module.free_of_finite_type_torsion_free',
end

open finite_dimensional

lemma zlattice.rank : finrank ℤ L = finrank K E :=
begin
  haveI : module.finite ℤ L := zlattice.module.finite K hd hs,
  haveI : module.free ℤ L := zlattice.module.free K hd hs,
  haveI : module ℚ E := module.comp_hom E (algebra_map ℚ K),
  let b := module.free.choose_basis ℤ L,
  have h_spaneq : span ℤ (set.range ((coe : L → E) ∘ b)) = L.to_int_submodule,
  { convert congr_arg (submodule.map L.to_int_submodule.subtype) b.span_eq,
    { rw [submodule.map_span, submodule.coe_subtype, set.range_comp], },
    { rw map_subtype_top, }},
  have h_spantop : submodule.span K (set.range ((coe : L → E) ∘ b)) = ⊤,
  { rwa [← @submodule.span_span_of_tower ℤ E K _, h_spaneq], },
  rw finrank_eq_card_choose_basis_index,
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
        (λ n : ℤ, zspan.fract e (n • v)) set.infinite_univ _ (hd (finset.univ.sum (λ j, ‖e j‖))),
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
            set_like.mem_coe, add_smul, neg_smul, ← zspan.fract_eq_fract], }},
      intros n _,
      split,
      { change _ ∈ L.to_int_submodule,
        simp_rw [zspan.fract_apply e, ← h_spaneq],
        refine sub_mem _ _,
        { exact zsmul_mem (submodule.subset_span (set.diff_subset _ _ hv)) _, },
        { refine ((span_mono _) (coe_mem (zspan.floor e (n • v)))),
          simp only [ht1, basis.coe_mk, subtype.range_coe_subtype, set.set_of_mem_eq], }},
      { exact mem_closed_ball_zero_iff.mpr (zspan.norm_fract_le e _), }},
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

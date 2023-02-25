/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import analysis.normed_space.basic
import linear_algebra.finite_dimensional
import measure_theory.group.fundamental_domain
import linear_algebra.free_module.pid

/-!
# ℤ-lattices
Let `E` be a finite dimensional real vector space. A (full) ℤ-lattice `L` of `E` is a discrete
subgroup of `E` such that `L` spans `E` over `ℝ`.

The ℤ-lattice `L` can be defined in two ways:
* For `b` a basis of `E`, then `L : submodule.span ℤ (set.range b)` is a ℤ-lattice of `E`.
* As `L : add_subgroup E` with the additional properties:
  `(hd : ∀ r : ℝ, (L ∩ (metric.closed_ball 0 r)).finite)`, that is `L` is discrete
  `(hs : submodule.span ℝ (L : set E) = ⊤)`, that is `L` spans `E` over `ℝ`.

## Main results
* `zspan.is_add_fundamental_domain`: proves that the set defined by `zsapn.fundamental_domain` is
indeed a fundamental domain of the lattice.
* `zlattice.dim`: for `L : add_subgroup E` with `L` discrete and spanning `E` over `ℝ`, proves that
`finrank ℤ L = finrank ℝ E`.
-/

open_locale classical

noncomputable theory

section zspan

open measure_theory measurable_set submodule

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
variables {ι : Type*} (b : basis ι ℝ E)

/-- The ℤ-lattice spanned by `b` admits `b` as a ℤ-basis. -/
def zspan.basis : basis ι ℤ (span ℤ (set.range b)) :=
basis.span (b.linear_independent.restrict_scalars (smul_left_injective ℤ (ne_zero.ne 1)))

@[simp]
lemma zspan.basis_apply (i : ι) : (zspan.basis b i : E) = b i :=
  by simp only [zspan.basis, basis.span_apply]

@[simp]
lemma zspan.repr_apply (m : span ℤ (set.range b)) [finite ι] (i : ι)  :
  ((zspan.basis b).repr m i : ℝ) = b.repr m i :=
begin
  casesI nonempty_fintype ι,
  rw ← congr_arg (coe : _ → E) (basis.sum_repr (zspan.basis b) m),
  simp only [coe_sum, coe_smul_of_tower, zspan.basis_apply, linear_equiv.map_sum,
    zsmul_eq_smul_cast ℝ, b.repr.map_smul, finsupp.single_apply, finset.sum_apply', basis.repr_self,
    finsupp.smul_single', mul_one, finset.sum_ite_eq', finset.mem_univ, if_true],
end

lemma zspan.mem_span_iff [finite ι] (m : E) :
  m ∈ span ℤ (set.range b) ↔ ∀ i, ∃ c : ℤ, b.repr m i = c :=
begin
  casesI nonempty_fintype ι,
  split,
  { exact λ hm i, ⟨(zspan.basis b).repr ⟨m, hm⟩ i, (zspan.repr_apply b ⟨m, hm⟩ i).symm⟩, },
  { intros h,
    rw ← b.sum_repr m,
    refine sum_mem _,
    intros i _,
    rw [(h i).some_spec, ← zsmul_eq_smul_cast ℝ],
    exact zsmul_mem (subset_span (set.mem_range_self i)) _, }
end

/-- The fundamental domain of the ℤ-lattice spanned by `b`. See `zspan.is_add_fundamental_domain`
for the proof that it is the fundamental domain. -/
def zspan.fundamental_domain : set E := { m | ∀ i : ι, b.repr m i ∈ set.Ico (0 : ℝ) 1 }

section fintype

variable [fintype ι]

/-- The map that sends a vector of `E` to the element of the ℤ-lattice spanned by `b` obtained
by rounding down its coordinates on the basis `b`. -/
def zspan.floor_map : E → span ℤ (set.range b) :=
λ m, finset.univ.sum (λ i, int.floor (b.repr m i) • zspan.basis b i)

lemma zspan.floor_map_single (m : E) (i : ι) :
  b.repr (zspan.floor_map b m) i = int.floor (b.repr m i) :=
by simp only [zspan.floor_map, zsmul_eq_smul_cast ℝ, b.repr.map_smul, finsupp.single_apply,
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
  use (zspan.basis b).repr ⟨v, h⟩ i,
  simp only [map_add, finsupp.coe_add, pi.add_apply, add_tsub_cancel_right, zspan.repr_apply,
    coe_mk],
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
  simp only [int.fract_eq_fract, zspan.mem_span_iff, zspan.fract_map_single, sub_eq_neg_add,
    map_add, linear_equiv.map_neg, finsupp.coe_add, finsupp.coe_neg, pi.add_apply, pi.neg_apply],
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
    ... ≤ finset.univ.sum (λ j, ‖b j‖) : finset.sum_le_sum _,
    intros i _,
    rw [real.norm_eq_abs, int.abs_fract],
    refine le_trans (mul_le_mul_of_nonneg_right (le_of_lt (int.fract_lt_one _)) (norm_nonneg _)) _,
    rw one_mul,
end

end fintype

lemma zspan.metric.fundamental_domain_bounded [finite ι] :
  metric.bounded (zspan.fundamental_domain b) :=
begin
  casesI nonempty_fintype ι,
  use 2 * finset.univ.sum (λ j, ‖b j‖),
  intros x hx y hy,
  refine le_trans (dist_le_norm_add_norm x y) _,
  rw [← (zspan.mem_fundamental_domain b).mp hx, ← (zspan.mem_fundamental_domain b).mp hy],
  refine (add_le_add (zspan.fract_map_le b x) (zspan.fract_map_le b y)).trans _,
  linarith,
end

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

lemma zspan.exist_vadd_mem_fundamental_domain (x : E) [finite ι] :
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

end zspan

#lint


#exit

section zlattice

open submodule

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
variables [finite_dimensional ℝ E] {L : add_subgroup E}
variables (hd : ∀ r : ℝ, ((L : set E) ∩ (metric.closed_ball 0 r)).finite)
variables (hs : span ℝ (L : set E) = ⊤)

include hd hs

lemma zlattice.fg : add_subgroup.fg L :=
begin
  suffices : L.to_int_submodule.fg,
  { rwa [fg_iff_add_subgroup_fg, add_subgroup.to_int_submodule_to_add_subgroup] at this, },
  obtain ⟨s, ⟨h1, ⟨h2, h3⟩⟩⟩ := exists_linear_independent ℝ (L.to_int_submodule : set E),
-- Let `s` be maximal ℝ-linear independent family of elements of `L`. We show that
-- `L` is finitely generated (as a ℤ-module) because its fits in the exact sequence
-- `0 → L ∩ ker (span ℤ s) → L → L / ker (span ℤ s) → 0`
-- with `L ∩ ker (span ℤ s)` and `L / ker (span ℤ s)` finitely generated.
  refine fg_of_fg_map_of_fg_inf_ker (mkq (span ℤ s)) _ _,
  { rw submodule.fg_def,
    use (map (span ℤ s).mkq (add_subgroup.to_int_submodule L)),
    split,
    { haveI : fintype s := sorry,
      let b := basis.mk h3 (by
        simp only [h2, hs, subtype.range_coe, add_subgroup.coe_to_int_submodule, top_le_iff]),
      rw (_ : submodule.span ℤ s = submodule.span ℤ (set.range b)),
-- Elements of `L / ker (span ℤ s)` are in bijection with element of `L ∩ fundamental_domain s`
-- so there are finitely many since `fundamental_domain s` is bounded.
      refine @set.finite.of_finite_image _ _ _ ((coe : _ → E) ∘ (zspan.quo_fract_equiv b)) _ _,
      { obtain ⟨C, hC⟩ := metric.bounded.subset_ball (zspan.metric.bounded_fundamental_domain b) 0,


    --    refine set.finite.subset (hd (finset.univ.sum (λ j, ‖b j‖))) _,
        refine set.finite.subset (hd C) _,
        rintros _ ⟨_, ⟨⟨x, ⟨hx, rfl⟩⟩, rfl⟩⟩,
        split,
        { simp *,
          sorry, },
        { simp only [mkq_apply, function.comp_app, mem_closed_ball_zero_iff],
          exact mem_closed_ball_zero_iff.mp (hC (zspan.fract_map_mem_fundamental_domain b x)), },
      },
      sorry,
      sorry, },
    { exact submodule.span_eq _, }},
-- `L ∩ ker (span ℤ s)` is finitely generated because `s` is finite.
  { rw [submodule.ker_mkq (submodule.span ℤ s), inf_of_le_right (submodule.span_le.mpr h1)],
    exact submodule.fg_span (linear_independent.finite h3), }
end

#exit

  haveI : fintype s,
  { suffices : s.finite,
    { exact set.finite.fintype this, },
    convert h3.finite, },
  let b := basis.mk h3
  begin
    have : set.range (coe : s → E) = (s : set E),
    { exact subtype.range_coe, },
    have : submodule.span ℝ (set.range coe) = submodule.span ℝ s,
    { exact congr_arg (submodule.span ℝ) this, },
    rw this,
    rwa h2,
    rw hs,
    exact le_rfl,
  end,
  have hh : s = set.range b,
  { rw congr_arg set.range (basis.coe_mk _ _),
    simp only [subtype.range_coe_subtype, set.set_of_mem_eq], },
  have hb : set.range b ≤ L, { rwa ← hh, },
  have hr : submodule.span ℤ s = submodule.span ℤ (set.range b),
  { exact congr_arg (submodule.span ℤ) hh, },
  refine submodule.fg_of_fg_map_of_fg_inf_ker (submodule.mkq (submodule.span ℤ s)) _ _,
  { rw submodule.fg_iff_add_subgroup_fg,
    rw add_subgroup.fg_iff_add_submonoid.fg,
    rw ← add_monoid.fg_iff_add_submonoid_fg,
    convert add_monoid.fg_of_finite,
    rw hr,
    change finite (submodule.map (submodule.span ℤ (set.range ⇑b)).mkq L).carrier,
    rw set.finite_coe_iff,
    refine set.finite.of_finite_image _ ((zspan.injective_fract_quo_map b).inj_on _),
    refine set.finite.subset (hd (finset.univ.sum (λ j, ‖b j‖))) _,
    rintros _ ⟨_, ⟨⟨x, ⟨hx, rfl⟩⟩, rfl⟩⟩,
    split,
    { rw zspan.fract_quo_map_eq,
      rw zspan.fract_map,
      rw set_like.mem_coe,
      refine sub_mem hx _,
      have : submodule.span ℤ (set.range b) ≤ L := submodule.span_le.mpr hb,
      refine this (submodule.coe_mem _), },
    { rw mem_closed_ball_zero_iff,
      exact zspan.fract_map_le _ _, }},
  { have : L ⊓ linear_map.ker _ = submodule.span ℤ s,
    { rw submodule.ker_mkq (submodule.span ℤ s),
      rw inf_eq_right,
      rwa submodule.span_le, },
    rw this,
    exact submodule.fg_span (linear_independent.finite h3), },
end

#exit

--- Add a result that `L` is a free ℤ-module

/-- A basis of the lattice `L`.-/
def zlattice.basis [no_zero_smul_divisors ℤ E]
  (hd : ∀ r : ℝ, ((L : set E) ∩ (metric.closed_ball 0 r)).finite)
  (hs : submodule.span ℝ (L : set E) = ⊤) :  Σ (n : ℕ), basis (fin n) ℤ L :=
begin
  haveI : module.finite ℤ L,
  { rw module.finite.iff_add_group_fg,
    rw add_group.fg_iff_add_monoid.fg,
    have := zlattice.fg hd hs,
    rw submodule.fg_iff_add_subgroup_fg at this,
    rw add_subgroup.fg_iff_add_submonoid.fg at this,
    rw ← add_monoid.fg_iff_add_submonoid_fg at this,
    convert this, },
  exact @module.free_of_finite_type_torsion_free' ℤ _ _ _ L _ _ _ _,
end

lemma zlattice.dim [no_zero_smul_divisors ℤ E]
  (hd : ∀ r : ℝ, ((L : set E) ∩ (metric.closed_ball 0 r)).finite)
  (hs : submodule.span ℝ (L : set E) = ⊤) :
  (zlattice.basis hd hs).1 = finite_dimensional.finrank ℝ E :=
begin
  let s := set.range (λ i : fin ((zlattice.basis hd hs).1), (((zlattice.basis hd hs).2 i) : E)),
  have t1 : submodule.span ℝ s = ⊤,
  { rw ← hs,
    rw ← submodule.span_span_of_tower ℤ ℝ s,
    congr,
    have := basis.span_eq (zlattice.basis hd hs).2,
    have z1 := congr_arg (submodule.map L.subtype) this,
    rw ← submodule.span_image L.subtype at z1,
    rw submodule.map_subtype_top L at z1,
    rw ← z1,
    congr,
    ext,
    split,
    { rintro ⟨_, rfl⟩,
      simp only [set.mem_image, set.mem_range, exists_exists_eq_and, exists_apply_eq_apply,
        submodule.coe_subtype], },
    { rintro ⟨_, ⟨⟨t1, rfl⟩, rfl⟩⟩,
      simp only [set.mem_range, exists_apply_eq_apply, submodule.coe_subtype], }},
  have t2 : (zlattice.basis hd hs).1 = finset.card s.to_finset,
  { rw set.to_finset_range,
    rw finset.card_image_of_injective,
    exact (finset.card_fin _).symm,
    have : function.injective (coe : L → E) := subtype.coe_injective,
    have := (this.of_comp_iff (zlattice.basis hd hs).2).mpr (zlattice.basis hd hs).2.injective,
    exact this, },
  rw t2,
  apply le_antisymm,
  { -- Proceed by contradiction
    by_contradiction,
    push_neg at h,
    -- Extract a basis b of E from s
    obtain ⟨t, ⟨ht1, ⟨ht2, ht3⟩⟩⟩ := exists_linear_independent ℝ s,
    have ht4 : ⊤ ≤ submodule.span ℝ (set.range (coe : t → E)),
    { have : set.range (coe : t → E) = (t : set E),
      { exact subtype.range_coe, },
      have : submodule.span ℝ (set.range coe) = submodule.span ℝ t,
      { exact congr_arg (submodule.span ℝ) this, },
      rw this,
      rw ht2,
      rw t1,
      exact le_rfl, },
    let b : basis t ℝ E := basis.mk ht3 ht4,
    haveI : fintype t := set.finite.fintype (s.to_finite.subset ht1),
    have t3 : t.to_finset.card = finite_dimensional.finrank ℝ E,
    { rw finite_dimensional.finrank_eq_card_basis b,
      rw set.to_finset_card, },
    have : (s \ t).nonempty,
    { suffices :  0 < (s \ t).to_finset.card,
      { rw ← set.to_finset_nonempty,
        rwa ← finset.card_pos, },
      rw set.to_finset_diff,
      rw finset.card_sdiff (set.to_finset_mono ht1),
      rw t3,
      rwa tsub_pos_iff_lt, },
    obtain ⟨v, hv1⟩ := this,
    -- Use fract_map b to prove that n • v - m • v ∈ span ℤ b
    have t3 : ∃ d : ℤ, d ≠ 0 ∧ d • v ∈ submodule.span ℤ (set.range b),
    { obtain ⟨n, _, m, _, hnm, h⟩  := @set.infinite.exists_ne_map_eq_of_maps_to ℕ _ _ _
        (λ n : ℕ, zspan.fract_map b (n • v)) set.infinite_univ _
        (hd (finset.univ.sum (λ j, ‖b j‖))),
      { use (n : ℤ) - m,
        split,
        { rw sub_ne_zero,
          exact_mod_cast hnm, },
        { rw sub_smul,
          rw ← zspan.fract_map_eq_iff b,
          dsimp only at h,
          rw coe_nat_zsmul,
          rwa coe_nat_zsmul, }},
      { intros n _,
        have t4 : s ⊆ L,
        { rintros _ ⟨i, rfl⟩,
          simp only [set_like.mem_coe, submodule.coe_mem], },
        split,
        { dsimp only [zspan.fract_map],
          rw set_like.mem_coe,
          refine sub_mem _ _,
          { refine nsmul_mem _ n,
            exact t4 (s.diff_subset _ hv1), },
          { dsimp only [zspan.floor_map],
            rw submodule.coe_sum,
            refine sum_mem _,
            intros x _,
            rw submodule.coe_smul,
            refine zsmul_mem _ _,
            rw zspan.basis_eq,
            rw basis.coe_mk,
            exact t4 (ht1 (subtype.mem x)), }},
        { rw mem_closed_ball_zero_iff,
          exact zspan.fract_map_le b _, }}},
    -- Deduce that there is a ℤ-relation between the vectors of zap_basis
    let t0 := has_insert.insert v t.to_finset,
    suffices : ¬ linear_independent ℤ (coe : t0 → E),
    { have t5 := (zlattice.basis hd hs).2.linear_independent,
      have z1 := t5.map' L.subtype L.ker_subtype,
      have t6 := z1.to_subtype_range,
      have t7 : linear_independent ℤ (coe : s → E),
      { convert t6, },
      have z3 : (t0 : set E) ⊆ s,
      { dsimp only [t0],
        rw finset.coe_insert,
        rw set.coe_to_finset,
        rw set.insert_subset,
        split,
        { exact set.mem_of_mem_diff hv1, },
        { exact ht1, }},
      have z4 := linear_independent.mono z3,
      have z5 := z4 t7,
      exact this z5, },
    rw fintype.not_linear_independent_iff,
    obtain ⟨d, ⟨hd1, hd2⟩⟩ := t3,
    have : set.range b = t.to_finset,
    { convert subtype.range_coe,
      exact basis.coe_mk ht3 ht4,
      exact set.coe_to_finset t, },
    rw this at hd2,
    rw mem_span_finset at hd2,
    obtain ⟨f, hf⟩ := hd2,
    let g : t0 → ℤ := λ x, ite ((x : E) = v) (- d) (f x),
    use g,
    split,
    { let k : E → E := λ x, ite ((x : E) = v) ((- d) • v)  ((f x) • x),
      have : ∀ i : t0, g i • (i : E) = k i,
      { intro i,
        dsimp only [k, g],
        split_ifs with h1 h2,
        { rw h1, },
        { refl, }},
      simp_rw this,
      have := finset.sum_coe_sort t0 k,
      rw this,
      rw finset.sum_insert,
      dsimp [k],
      rw if_pos _,
      have : ∀ x ∈ t.to_finset, ¬ x = v,
      { intros x hx,
        by_contra,
        rw h at hx,
        have := set.not_mem_of_mem_diff hv1,
        rw set.mem_to_finset at hx,
        exact this hx, },
      rw finset.sum_ite_of_false _ _ this,
      rw hf,
      rw ← add_zsmul,
      simp only [add_left_neg, zero_smul],
      refl,
      apply (iff.not set.mem_to_finset).mpr,
      exact set.not_mem_of_mem_diff hv1, },
    { use v,
      exact finset.mem_insert_self _ _,
      dsimp only [g],
      rw if_pos _,
      rwa neg_ne_zero,
      exact subtype.coe_mk _ _, }},
  { have := finrank_span_le_card s,
    rw t1 at this,
    have := @submodule.top_equiv ℝ E _ _ _,
    have := this.finrank_eq,
    rwa ← this, },
end

end zlattice

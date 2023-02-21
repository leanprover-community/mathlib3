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
A ℤ-lattice `L` is a discrete subgroup of a finite dimensional real vector space `E` such
that `L` spans `E` over `ℝ`.

The ℤ-lattice `L` can be defined in two ways:
* `L : submodule.span ℤ (set.range b)` where `b` is a basis of `E`
* `L : submodule ℤ E` with the additional properties:
  `(hd : ∀ r : ℝ, (L ∩ (metric.closed_ball 0 r)).finite)`, that is `L` is discrete
  `(hs : submodule.span ℝ (L : set E) = ⊤)`, that is `L` spans `E`

## Main results
* `zspan.is_add_fundamental_domain`: proves that the set defined by `zsapn.fundamental_domain` is
indeed a fundamental domain of the lattice
-/

open_locale classical

noncomputable theory

section zspan

-- TODO. Generalize to other fields(?)
variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
variables {ι : Type*} (b : basis ι ℝ E)

/-- The lattice defined by the basis `b` admits `b` as a `ℤ`-basis. -/
def zspan.basis : basis ι ℤ (submodule.span ℤ (set.range b)) :=
basis.span (b.linear_independent.restrict_scalars (smul_left_injective ℤ (by norm_num)))

lemma zspan.basis_eq (i : ι) : (zspan.basis b i : E) = b i :=
  by simp only [zspan.basis, basis.span_apply]

lemma zspan.repr_eq (m : submodule.span ℤ (set.range b)) [finite ι] (i : ι)  :
   b.repr m i = ((zspan.basis b).repr m i : ℝ) :=
begin
  casesI nonempty_fintype ι,
  rw ← sub_eq_zero,
  revert i,
  apply fintype.linear_independent_iff.mp b.linear_independent,
  simp_rw sub_smul,
  rw finset.sum_sub_distrib,
  rw sub_eq_zero,
  rw basis.sum_repr,
  simp_rw ← zspan.basis_eq b,
  simp_rw ← zsmul_eq_smul_cast ℝ _ _,
  rw ← congr_arg (coe : _ → E) ((zspan.basis b).sum_repr m),
  rw submodule.coe_sum,
  simp_rw set_like.coe_smul,
end

lemma zspan.mem_span_iff [finite ι] (m : E) :
  m ∈ submodule.span ℤ (set.range b) ↔ ∀ i, ∃ c : ℤ, b.repr m i = c :=
begin
  casesI nonempty_fintype ι,
  split,
  { intros hm i,
    use (zspan.basis b).repr ⟨m, hm⟩ i,
    convert zspan.repr_eq b ⟨m, hm⟩ i, },
  { intro h,
    rw ← b.sum_repr m,
    refine sum_mem _,
    intros i _,
    obtain ⟨c, hc⟩ := h i,
    rw hc,
    rw ← zsmul_eq_smul_cast ℝ _ _,
    refine zsmul_mem _ _,
    exact submodule.subset_span (set.mem_range_self i),  }
end

variable [fintype ι]

/-- The map that sends a vector of the ambiant space to the element of the lattice obtained
by round down its coordinate on the basis `b`. -/
def zspan.floor_map : E → submodule.span ℤ (set.range b) :=
λ m, finset.univ.sum (λ i, int.floor (b.repr m i) • zspan.basis b i)

lemma zspan.floor_map_single (m : E) (i : ι) :
  b.repr (zspan.floor_map b m) i = int.floor (b.repr m i) :=
begin
  rw ← sub_eq_zero,
  revert i,
  have zz := fintype.linear_independent_iff.mp b.linear_independent,
  apply zz,
  simp_rw sub_smul,
  rw finset.sum_sub_distrib,
  rw sub_eq_zero,
  simp_rw ← zspan.basis_eq,
  simp_rw zspan.repr_eq,
  simp_rw ← zsmul_eq_smul_cast ℝ _ _,
  rw_mod_cast basis.sum_repr (zspan.basis b) (zspan.floor_map b m),
  refl,
end

/-- The map that sends a vector of the ambiant space to the fundamental domain of the lattice. -/
def zspan.fract_map : E → E := λ m, m - zspan.floor_map b m

lemma zspan.fract_map_single (m : E) (i : ι):
  b.repr (zspan.fract_map b m) i = int.fract (b.repr m i) :=
begin
  rw zspan.fract_map,
  rw map_sub,
  rw finsupp.coe_sub,
  rw pi.sub_apply,
  rw zspan.floor_map_single,
  refl,
end

lemma zspan.fract_map_eq_iff (m n : E) :
  zspan.fract_map b m = zspan.fract_map b n ↔ m - n ∈ submodule.span ℤ (set.range b) :=
begin
  have : zspan.fract_map b m = zspan.fract_map b n ↔ ∀ i, ∃ z : ℤ, b.repr (m - n) i = z,
  { rw basis.ext_elem_iff b,
    simp_rw zspan.fract_map_single,
    simp_rw map_sub,
    simp_rw finsupp.coe_sub,
    simp_rw pi.sub_apply,
    simp_rw int.fract_eq_fract, },
  rw this,
  exact (zspan.mem_span_iff b (m - n)).symm,
end

/-- The map between `E` quotiented by the lattice and its fundamental domain. -/
def zspan.fract_quo_map : E ⧸ submodule.span ℤ (set.range b) → E :=
begin
  intro q,
  refine quotient.lift_on' q (zspan.fract_map b) _,
  intros x y hxy,
  rw zspan.fract_map_eq_iff,
  rw ← neg_mem_iff,
  have := quotient_add_group.left_rel_apply.mp hxy,
  convert this,
  abel,
end

lemma zspan.fract_quo_map_eq (x : E) :
  (zspan.fract_quo_map b) (((submodule.span ℤ (set.range ⇑b)).mkq) x) = zspan.fract_map b x := rfl

lemma zspan.injective_fract_quo_map : function.injective (zspan.fract_quo_map b) :=
begin
  dsimp only [zspan.fract_quo_map],
  refine λ x y, quotient.induction_on₂' x y _,
  intros a1 a2 h,
  simp_rw quotient.lift_on'_mk' _ _ _ at h,
  rw zspan.fract_map_eq_iff at h,
  rw ← submodule.mem_to_add_subgroup at h,
  rw ← neg_mem_iff at h,
  rwa quotient.eq',
  rw quotient_add_group.left_rel_apply,
  convert h,
  abel,
end

lemma zspan.fract_map_le (m : E):
  ‖zspan.fract_map b m‖ ≤ finset.univ.sum (λ j, ‖b j‖) :=
begin
  calc
    ‖zspan.fract_map b m‖
        = ‖finset.univ.sum (λ i, b.repr (zspan.fract_map b m) i • b i)‖ : by rw b.sum_repr
    ... = ‖finset.univ.sum (λ i, int.fract (b.repr m i) • b i)‖ : by simp_rw zspan.fract_map_single
    ... ≤ finset.univ.sum (λ i, ‖int.fract (b.repr m i) • b i‖) : norm_sum_le _ _
    ... ≤ finset.univ.sum (λ i, |int.fract (b.repr m i)| * ‖b i‖)
        : by simp_rw [norm_smul, real.norm_eq_abs]
    ... ≤ finset.univ.sum (λ j, ‖b j‖) : finset.sum_le_sum _,
    intros i _,
    rw int.abs_fract,
    refine le_trans (mul_le_mul_of_nonneg_right (le_of_lt (int.fract_lt_one _)) (norm_nonneg _)) _,
    rw one_mul,
end

end zspan

section fundamental_domain

open measure_theory measurable_set

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
variables {ι : Type*}  (b : basis ι ℝ E)

instance zspan.vadd : has_vadd (submodule.span ℤ (set.range b)) E := ⟨ λ s m, s + m ⟩

@[simp]
lemma zspan.vadd_eq_add (m : E) (v : submodule.span ℤ (set.range b)) :
  v +ᵥ m = v + m := rfl

/-- The fundamental domain of the lattice. -/
def zspan.fundamental_domain : set E := { m | ∀ i : ι, b.repr m i ∈ set.Ico (0 : ℝ) 1 }

-- TODO. use this to simplify proof of is_add_fundamental_domain
lemma zspan.mem_fundamental_domain [fintype ι] {x : E} :
  x ∈ (zspan.fundamental_domain b) ↔ zspan.fract_map b x = x :=
begin
  rw basis.ext_elem_iff b,
  simp only [zspan.fundamental_domain, set.mem_Ico, set.mem_set_of_eq, zspan.fract_map_single,
    int.fract_eq_self],
end

lemma zspan.metric.bounded_fundamental_domain [finite ι] :
  metric.bounded (zspan.fundamental_domain b) :=
begin
  casesI nonempty_fintype ι,
  use 2 * finset.univ.sum (λ j, ‖b j‖),
  intros x hx y hy,
  have : ‖x‖ ≤ finset.univ.sum (λ j, ‖b j‖),
  { convert zspan.fract_map_le b x,
    exact ((zspan.mem_fundamental_domain b).mp hx).symm, },
  have : ‖y‖ ≤ finset.univ.sum (λ j, ‖b j‖),
  { convert zspan.fract_map_le b y,
    exact ((zspan.mem_fundamental_domain b).mp hy).symm, },
  refine le_trans (dist_le_norm_add_norm x y) _,
  linarith,
end

lemma zspan.is_add_fundamental_domain [measurable_space E] [opens_measurable_space E]
  (μ : measure E) [finite ι] :
  is_add_fundamental_domain (submodule.span ℤ (set.range b)).to_add_subgroup
    (zspan.fundamental_domain b) μ :=
{ null_measurable_set :=
  begin
    haveI : finite_dimensional ℝ E := finite_dimensional.of_fintype_basis b,
    refine null_measurable_set _,
    let D : set (ι → ℝ) := set.pi set.univ (λ i : ι, (set.Ico (0 : ℝ) (1 : ℝ))),
    have t1 : measurable_set D,
    { refine pi set.univ.to_countable (λ (i : ι) (H : i ∈ set.univ), measurable_set_Ico), },
    let f := (finsupp.linear_equiv_fun_on_finite ℝ ℝ ι).to_linear_map.comp b.repr.to_linear_map,
    have t2 : measurable f := (linear_map.continuous_of_finite_dimensional f).measurable,
    have t3 : measurable_set (f⁻¹' D) := t2 t1,
    convert t3,
    ext,
    dsimp only [zspan.fundamental_domain, f],
    simp only [set.mem_set_of_eq, set.mem_preimage, set.mem_univ_pi, linear_map.coe_comp,
      linear_equiv.coe_to_linear_map, function.comp_app, finsupp.linear_equiv_fun_on_finite_apply],
  end,
  ae_covers :=
  begin
    casesI nonempty_fintype ι,
    refine filter.eventually_of_forall _,
    intro x,
    use - zspan.floor_map b x,
    have : -zspan.floor_map b x +ᵥ x = zspan.fract_map b x,
    { simp only [zspan.fract_map, zspan.vadd_eq_add, add_subgroup_class.coe_neg],
      abel, },
    rw this,
    intro i,
    rw zspan.fract_map_single,
    simp only [int.fract_lt_one, set.mem_Ico, int.fract_nonneg, and_self],
  end,
  ae_disjoint :=
  begin
    intros v w hvw,
    refine disjoint.ae_disjoint _,
    intros s hsv hsw x hx,
    obtain ⟨a, ⟨ha1, ha2⟩⟩ := hsv hx,
    obtain ⟨c, ⟨hc1, hc2⟩⟩ := hsw hx,
    have t1 := ha2.trans hc2.symm,
    simp_rw zspan.vadd_eq_add at t1,
    have t2 : ∀ i, (b.repr a) i = (b.repr c) i,
    { intro i,
      have t4 := congr_arg (λ z, b.repr z i) t1,
      dsimp only at t4,
      rw [map_add, map_add] at t4,
      rw [finsupp.coe_add, pi.add_apply, finsupp.coe_add, pi.add_apply] at t4,
      have t5 := congr_arg int.fract t4,
      have t6 : ∃ n : ℤ, b.repr v i = n := (zspan.mem_span_iff b v).1 (set_like.coe_mem v) i,
      obtain ⟨n, hn⟩ := t6,
      rw hn at t5,
      have t7 : ∃ m : ℤ, b.repr w i = m := (zspan.mem_span_iff b w).1 (set_like.coe_mem w) i,
      obtain ⟨m, hm⟩ := t7,
      rw hm at t5,
      rw [int.fract_int_add, int.fract_int_add] at t5,
      rw int.fract_eq_self.2 (ha1 i) at t5,
      rwa int.fract_eq_self.2 (hc1 i) at t5, },
    have t3 : ∀ i, b.repr v i = b.repr w i,
    { intro i,
      have t4 := congr_arg (λ z, b.repr z i) t1,
      simp_rw map_add at t4,
      simp_rw [finsupp.coe_add, pi.add_apply] at t4,
      rw t2 i at t4,
      rwa add_left_inj at t4, },
    rw ← basis.ext_elem_iff b at t3,
    rw ← subtype.ext_iff at t3,
    exact hvw t3,
  end }

end fundamental_domain

section lattice_basic

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
variables [finite_dimensional ℝ E] {L : submodule ℤ E}

lemma zlattice.fg (hd : ∀ r : ℝ, ((L : set E) ∩ (metric.closed_ball 0 r)).finite)
  (hs : submodule.span ℝ (L : set E) = ⊤) : submodule.fg L :=
begin
  obtain ⟨s, ⟨h1, ⟨h2, h3⟩⟩⟩ := exists_linear_independent ℝ (L : set E),
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
      exact set.not_mem_of_mem_diff hv1,
    },
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

end lattice_basic

import group_theory.subgroup.basic
import data.real.basic
import topology.order
import topology.algebra.group.basic
import topology.constructions
import topology.instances.real
import linear_algebra.free_module.basic
import linear_algebra.free_module.pid
import analysis.normed.group.basic
import linear_algebra.finite_dimensional
import analysis.normed_space.basic
import group_theory.finite_abelian

open_locale classical

section basis

variables {R M ι : Type*} [semiring R]
variables [add_comm_monoid M] [module R M]  (b : basis ι R M)

lemma basis.ext_elem_iff {x y : M} :
    x = y ↔ (∀ i, b.repr x i = b.repr y i) :=
 by simp only [← finsupp.ext_iff, embedding_like.apply_eq_iff_eq]

end basis

section zspan

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
variables {ι : Type*} [fintype ι] (b : basis ι ℝ E)

noncomputable def zspan.basis : basis ι ℤ (submodule.span ℤ (set.range b)) :=
basis.span (b.linear_independent.restrict_scalars (smul_left_injective ℤ (by norm_num)))

lemma zspan.basis_eq (i : ι) : b i = zspan.basis b i := by simp only [zspan.basis, basis.span_apply]

lemma zspan.repr_eq (m : submodule.span ℤ (set.range b)) (i : ι) :
  ((zspan.basis b).repr m i : ℝ) = b.repr m i :=
begin
  rw ← sub_eq_zero,
  revert i,
  apply fintype.linear_independent_iff.mp b.linear_independent,
  simp_rw sub_smul,
  rw finset.sum_sub_distrib,
  rw sub_eq_zero,
  rw basis.sum_repr,
  simp_rw zspan.basis_eq b,
  simp_rw ← zsmul_eq_smul_cast ℝ _ _,
  rw ← congr_arg (coe : _ → E) ((zspan.basis b).sum_repr m),
  rw submodule.coe_sum,
  simp_rw set_like.coe_smul,
end

noncomputable def zspan.floor_map : E → submodule.span ℤ (set.range b) :=
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
  simp_rw zspan.basis_eq,
  simp_rw ← zspan.repr_eq,
  simp_rw ← zsmul_eq_smul_cast ℝ _ _,
  rw_mod_cast basis.sum_repr (zspan.basis b) (zspan.floor_map b m),
  refl,
end

noncomputable def zspan.fract_map : E → E := λ m, m - zspan.floor_map b m

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
  zspan.fract_map b m = zspan.fract_map b n ↔ m - n ∈ submodule.span ℤ (set.range ⇑b) :=
begin
  have : zspan.fract_map b m = zspan.fract_map b n ↔ ∀ i, ∃ z : ℤ, b.repr (m - n) i = z,
  { rw basis.ext_elem_iff b,
    simp_rw zspan.fract_map_single,
    simp_rw map_sub,
    simp_rw finsupp.coe_sub,
    simp_rw pi.sub_apply,
    simp_rw int.fract_eq_fract, },
  rw this,
  split,
  { intro h,
    rw ← basis.sum_repr b (m - n),
    refine sum_mem _,
    intros i _,
    obtain ⟨z, hz⟩ := h i,
    rw_mod_cast hz,
    rw ← zsmul_eq_smul_cast ℝ _ _,
    refine zsmul_mem (submodule.subset_span (set.mem_range_self i)) _, },
  { intros h i,
    rw (zspan.basis b).mem_submodule_iff' at h,
    obtain ⟨c, hc⟩ := h,
    rw_mod_cast hc,
    use c i,
    simp_rw submodule.coe_sum,
    simp_rw set_like.coe_smul,
    simp_rw ← zspan.basis_eq b,
    simp_rw zsmul_eq_smul_cast ℝ _ _,
    exact congr_fun (basis.repr_sum_self b (λ x, (c x : ℝ))) i, },
end

example (x y : E) (L : submodule ℤ E) (h : x ∈ L) : - x ∈ L := neg_mem_iff.mpr h

-- TODO: prove that it is an add hom
noncomputable def zspan.fract_quo_map : E ⧸ submodule.span ℤ (set.range ⇑b) →+ E :=
{ to_fun :=
  begin
    intro q,
    refine quotient.lift_on' q (zspan.fract_map b) _,
    intros x y hxy,
    rw zspan.fract_map_eq_iff,
    rw ← neg_mem_iff,
    have := quotient_add_group.left_rel_apply.mp hxy,
    convert this,
    abel,
  end,
  map_zero' :=
  begin
    have : zspan.fract_map b 0 = 0,
    { simp only [basis.ext_elem_iff b, zspan.fract_map_single, map_zero, finsupp.coe_zero,
      pi.zero_apply, int.fract_zero, eq_self_iff_true, implies_true_iff], },
    exact this,
  end,
  map_add' :=
  begin
    refine λ x y, quotient.induction_on₂' x y _,
    intros a1 a2,
    simp_rw quotient.lift_on'_mk' _ _ _,
    sorry,
  end
}

lemma zspan.fract_quo_map_eq (x : E) :
  (zspan.fract_quo_map b) (((submodule.span ℤ (set.range ⇑b)).mkq) x) = zspan.fract_map b x := rfl

lemma zspan.injective_fract_quo_map : function.injective (zspan.fract_quo_map b) :=
begin
  dsimp [zspan.fract_quo_map],
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

section basis

variables {ι R M : Type*} {v : ι → M} [ring R] [add_comm_group M] [module R M]

lemma basis.mk_range (hli : linear_independent R v) (hsp : ⊤ ≤ submodule.span R (set.range v)) :
  set.range (basis.mk hli hsp) = set.range v :=
congr_arg set.range (basis.coe_mk hli hsp)

end basis

section lattice_basic

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
variables [finite_dimensional ℝ E] {L : submodule ℤ E}

lemma zap1 (hd : ∀ r : ℝ, ((L : set E) ∩ (metric.closed_ball 0 r)).finite)
  (hs : ⊤ ≤ submodule.span ℝ (L : set E)) : submodule.fg L :=
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
      change x - (zspan.floor_map b x) ∈ L,
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

noncomputable def zap_basis [no_zero_smul_divisors ℤ E]
  (hd : ∀ r : ℝ, ((L : set E) ∩ (metric.closed_ball 0 r)).finite)
  (hs : ⊤ ≤ submodule.span ℝ (L : set E)) :  Σ (n : ℕ), basis (fin n) ℤ L :=
begin
  haveI : module.finite ℤ L,
  { rw module.finite.iff_add_group_fg,
    rw add_group.fg_iff_add_monoid.fg,
    have := zap1 hd hs,
    rw submodule.fg_iff_add_subgroup_fg at this,
    rw add_subgroup.fg_iff_add_submonoid.fg at this,
    rw ← add_monoid.fg_iff_add_submonoid_fg at this,
    convert this, },
  exact @module.free_of_finite_type_torsion_free' ℤ _ _ _ L _ _ _ _,
end

example [no_zero_smul_divisors ℤ E]
  (hd : ∀ r : ℝ, ((L : set E) ∩ (metric.closed_ball 0 r)).finite)
  (hs : ⊤ ≤ submodule.span ℝ (L : set E)) :
  (zap_basis hd hs).1 = finite_dimensional.finrank ℝ E :=
begin
  have h1 : (zap_basis hd hs).1 ≤ finite_dimensional.finrank ℝ E,
  { sorry, },
  obtain h | h := le_or_lt (finite_dimensional.finrank ℝ E) (zap_basis hd hs).1,
  { exact le_antisymm h1 h, },
  { let v : fin (finite_dimensional.finrank ℝ E) → E := λ n, (zap_basis hd hs).2 ⟨n, _⟩,
    


    sorry, },
end

end lattice_basic

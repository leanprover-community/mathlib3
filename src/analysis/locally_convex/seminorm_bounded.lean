/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import analysis.locally_convex.bounded
import analysis.seminorm
/-!
# Seminorm Bounded

## Main definitions

* `foo_bar`

## Main statements

* `foo_bar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/


variables {𝕜 E ι ι' : Type*}

open_locale topological_space pointwise

namespace topological_space

section normed_field
variables [normed_field 𝕜] [add_comm_group E] [module 𝕜 E] [nonempty ι]

@[simp] lemma ball_eq_emptyset (p : seminorm 𝕜 E) {x : E} {r : ℝ} (hr : r ≤ 0) : p.ball x r = ∅ :=
begin
  ext,
  rw [seminorm.mem_ball, set.mem_empty_eq, iff_false, not_lt],
  exact hr.trans (p.nonneg _),
end

lemma smul_ball_zero {p : seminorm 𝕜 E} {k : 𝕜} {r : ℝ} (hk : 0 < ∥k∥):
  k • p.ball 0 r = p.ball 0 (∥k∥ * r) :=
begin
  ext,
  rw [set.mem_smul_set, seminorm.mem_ball_zero],
  split; intro h,
  { rcases h with ⟨y, hy, h⟩,
    rw [←h, seminorm.smul],
    rw seminorm.mem_ball_zero at hy,
    exact (mul_lt_mul_left hk).mpr hy },
  refine ⟨k⁻¹ • x, _, _⟩,
  { rw [seminorm.mem_ball_zero, seminorm.smul, norm_inv, ←(mul_lt_mul_left hk),
      ←mul_assoc, ←(div_eq_mul_inv ∥k∥ ∥k∥), div_self (ne_of_gt hk), one_mul],
    exact h},
  rw [←smul_assoc, smul_eq_mul, ←div_eq_mul_inv, div_self (norm_pos_iff.mp hk), one_smul],
end

lemma ball_zero_absorbs_ball_zero (p : seminorm 𝕜 E) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) :
  absorbs 𝕜 (p.ball 0 r₁) (p.ball 0 r₂) :=
begin
  by_cases hr₂ : r₂ ≤ 0,
  { rw ball_eq_emptyset p hr₂, exact absorbs_empty },
  rw [not_le] at hr₂,
  rcases exists_between hr₁ with ⟨r, hr, hr'⟩,
  refine ⟨r₂/r, div_pos hr₂ hr, _⟩,
  simp_rw set.subset_def,
  intros a ha x hx,
  have ha' : 0 < ∥a∥ := lt_of_lt_of_le (div_pos hr₂ hr) ha,
  rw [smul_ball_zero ha', p.mem_ball_zero],
  rw p.mem_ball_zero at hx,
  rw div_le_iff hr at ha,
  exact hx.trans (lt_of_le_of_lt ha ((mul_lt_mul_left ha').mpr hr')),
end

variables (p : ι → seminorm 𝕜 E)
variables  [topological_space E] [seminorm.with_seminorms p]

lemma with_seminorms_has_basis : (𝓝 (0 : E)).has_basis
  (λ (s : set E), s ∈ (seminorm.seminorm_basis_zero p)) id :=
begin
  rw (congr_fun (congr_arg (@nhds E) (seminorm.with_seminorms_eq p)) 0),
  exact add_group_filter_basis.nhds_zero_has_basis _,
end

lemma bounded_iff_bounded_basis {q : ι' → Prop} {s : ι' → set E} {A : set E}
  (h : (𝓝 (0 : E)).has_basis q s) :
  is_bounded 𝕜 A ↔ ∀ i (hi : q i), absorbs 𝕜 (s i) A :=
begin
  refine ⟨λ hA i hi, hA (s i) (filter.has_basis.mem_of_mem h hi), λ hA V hV, _⟩,
  rcases h.mem_iff.mp hV with ⟨i, hi, hV⟩,
  exact absorbs.mono_left (hA i hi) hV,
end



end normed_field

section nondiscrete_normed_field

variables [nondiscrete_normed_field 𝕜] [add_comm_group E] [module 𝕜 E] [nonempty ι]
variables (p : ι → seminorm 𝕜 E)
variables [topological_space E] [seminorm.with_seminorms p]

lemma is_bounded_iff_finset_seminorm_bounded {s : set E} :
  is_bounded 𝕜 s ↔ ∀ (I : finset ι), ∃ r (hr : 0 < r), ∀ (x ∈ s), I.sup p x < r :=
begin
  rw bounded_iff_bounded_basis (with_seminorms_has_basis p),
  split,
  { intros h I,
    simp only [id.def] at h,
    specialize h ((I.sup p).ball 0 1) (seminorm.seminorm_basis_zero_mem p I zero_lt_one),
    rcases h with ⟨r, hr, h⟩,
    cases normed_field.exists_lt_norm 𝕜 r with a ha,
    specialize h a (le_of_lt ha),
    rw [smul_ball_zero (lt_trans hr ha), mul_one] at h,
    refine ⟨∥a∥, lt_trans hr ha, _⟩,
    intros x hx,
    specialize h hx,
    exact (finset.sup I p).mem_ball_zero.mp h },
  intros h s' hs',
  rw seminorm.seminorm_basis_zero_iff at hs',
  rcases hs' with ⟨I, r, hr, hs'⟩,
  rw [id.def, hs'],
  rcases h I with ⟨r', hr', h'⟩,
  simp_rw ←(I.sup p).mem_ball_zero at h',
  refine absorbs.mono_right _ h',
  exact ball_zero_absorbs_ball_zero (finset.sup I p) hr,
end

end nondiscrete_normed_field
end topological_space

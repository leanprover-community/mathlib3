/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import analysis.locally_convex.bounded
import analysis.locally_convex.with_seminorms
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

open bornology

namespace topological_space

section normed_field
variables [normed_field 𝕜] [add_comm_group E] [module 𝕜 E] [nonempty ι]


variables (p : ι → seminorm 𝕜 E)
variables  [topological_space E] [with_seminorms p]

lemma with_seminorms_has_basis : (𝓝 (0 : E)).has_basis
  (λ (s : set E), s ∈ (seminorm_basis_zero p)) id :=
begin
  rw (congr_fun (congr_arg (@nhds E) (with_seminorms_eq p)) 0),
  exact add_group_filter_basis.nhds_zero_has_basis _,
end




end normed_field

section nondiscrete_normed_field

variables [nondiscrete_normed_field 𝕜] [add_comm_group E] [module 𝕜 E] [nonempty ι]
variables (p : ι → seminorm 𝕜 E)
variables [topological_space E] [with_seminorms p]

lemma is_bounded_iff_finset_seminorm_bounded {s : set E} :
  is_vonN_bounded 𝕜 s ↔ ∀ (I : finset ι), ∃ r (hr : 0 < r), ∀ (x ∈ s), I.sup p x < r :=
begin
  rw is_vonN_bounded_iff_vonN_bounded_basis (with_seminorms_has_basis p),
  split,
  { intros h I,
    simp only [id.def] at h,
    specialize h ((I.sup p).ball 0 1) (seminorm_basis_zero_mem p I zero_lt_one),
    rcases h with ⟨r, hr, h⟩,
    cases normed_field.exists_lt_norm 𝕜 r with a ha,
    specialize h a (le_of_lt ha),
    rw [seminorm.smul_ball_zero (lt_trans hr ha), mul_one] at h,
    refine ⟨∥a∥, lt_trans hr ha, _⟩,
    intros x hx,
    specialize h hx,
    exact (finset.sup I p).mem_ball_zero.mp h },
  intros h s' hs',
  rw seminorm_basis_zero_iff at hs',
  rcases hs' with ⟨I, r, hr, hs'⟩,
  rw [id.def, hs'],
  rcases h I with ⟨r', hr', h'⟩,
  simp_rw ←(I.sup p).mem_ball_zero at h',
  refine absorbs.mono_right _ h',
  exact (finset.sup I p).ball_zero_absorbs_ball_zero hr,
end

end nondiscrete_normed_field
end topological_space

/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser
-/

import ring_theory.graded_algebra.homogeneous_ideal

/-!

This file contains a proof that the radical of any homogeneous ideal is a homogeneous ideal

## Main statements

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

* `ideal.is_homogeneous.is_prime_iff`: for any `I : ideal A`, if `I` is homogeneous, then
  `I` is prime if and only if `I` is homogeneously prime, i.e. `I ≠ ⊤` and if `x, y` are
  homogeneous elements such that `x * y ∈ I`, then at least one of `x,y` is in `I`.
* `ideal.is_prime.homogeneous_core`: for any `I : ideal A`, if `I` is prime, then
  `I.homogeneous_core 𝒜` (i.e. the largest homogeneous ideal contained in `I`) is also prime.
* `ideal.is_homogeneous.radical`: for any `I : ideal A`, if `I` is homogeneous, then the
  radical of `I` is homogeneous as well.
* `homogeneous_ideal.radical`: for any `I : homogeneous_ideal 𝒜`, `I.radical` is the the
  radical of `I` as a `homogeneous_ideal 𝒜`

## Implementation details

Throughout this file, the indexing type `ι` of grading is assumed to be a
`linear_ordered_cancel_add_comm_monoid`. This might be stronger than necessary but cancelling
property is strictly necessary; for a counterexample of how `ideal.is_homogeneous.is_prime_iff`
fails for a non-cancellative set see `counterexample/homogeneous_prime_not_prime.lean`.

## Tags

homogeneous, radical
-/

open graded_ring direct_sum set_like finset
open_locale big_operators

variables {ι σ A : Type*}
variables [comm_ring A]
variables [linear_ordered_cancel_add_comm_monoid ι]
variables [set_like σ A] [add_submonoid_class σ A] {𝒜 : ι → σ} [graded_ring 𝒜]
include A

lemma ideal.is_homogeneous.is_prime_of_homogeneous_mem_or_mem
  {I : ideal A} (hI : I.is_homogeneous 𝒜) (I_ne_top : I ≠ ⊤)
  (homogeneous_mem_or_mem : ∀ {x y : A},
    is_homogeneous 𝒜 x → is_homogeneous 𝒜 y → (x * y ∈ I → x ∈ I ∨ y ∈ I)) :
  ideal.is_prime I :=
⟨I_ne_top, begin
  intros x y hxy,
  by_contradiction rid,
  obtain ⟨rid₁, rid₂⟩ := not_or_distrib.mp rid,
  /-
  The idea of the proof is the following :
  since `x * y ∈ I` and `I` homogeneous, then `proj i (x * y) ∈ I` for any `i : ι`.
  Then consider two sets `{i ∈ x.support | xᵢ ∉ I}` and `{j ∈ y.support | yⱼ ∉ J}`;
  let `max₁, max₂` be the maximum of the two sets, then `proj (max₁ + max₂) (x * y) ∈ I`.
  Then, `proj max₁ x ∉ I` and `proj max₂ j ∉ I`
  but `proj i x ∈ I` for all `max₁ < i` and `proj j y ∈ I` for all `max₂ < j`.
  `  proj (max₁ + max₂) (x * y)`
  `= ∑ {(i, j) ∈ supports | i + j = max₁ + max₂}, xᵢ * yⱼ`
  `= proj max₁ x * proj max₂ y`
  `  + ∑ {(i, j) ∈ supports \ {(max₁, max₂)} | i + j = max₁ + max₂}, xᵢ * yⱼ`.
  This is a contradiction, because both `proj (max₁ + max₂) (x * y) ∈ I` and the sum on the
  right hand side is in `I` however `proj max₁ x * proj max₂ y` is not in `I`.
  -/
  classical,
  set set₁ := (decompose 𝒜 x).support.filter (λ i, proj 𝒜 i x ∉ I) with set₁_eq,
  set set₂ := (decompose 𝒜 y).support.filter (λ i, proj 𝒜 i y ∉ I) with set₂_eq,
  have nonempty :
    ∀ (x : A), (x ∉ I) → ((decompose 𝒜 x).support.filter (λ i, proj 𝒜 i x ∉ I)).nonempty,
  { intros x hx,
    rw filter_nonempty_iff,
    contrapose! hx,
    simp_rw proj_apply at hx,
    rw ← sum_support_decompose 𝒜 x,
    exact ideal.sum_mem _ hx, },
  set max₁ := set₁.max' (nonempty x rid₁) with max₁_eq,
  set max₂ := set₂.max' (nonempty y rid₂) with max₂_eq,
  have mem_max₁ : max₁ ∈ set₁ := max'_mem set₁ (nonempty x rid₁),
  have mem_max₂ : max₂ ∈ set₂ := max'_mem set₂ (nonempty y rid₂),
  replace hxy : proj 𝒜 (max₁ + max₂) (x * y) ∈ I := hI _ hxy,

  have mem_I : proj 𝒜 max₁ x * proj 𝒜 max₂ y ∈ I,
  { set antidiag :=
      ((decompose 𝒜 x).support ×ˢ (decompose 𝒜 y).support)
        .filter (λ z : ι × ι, z.1 + z.2 = max₁ + max₂) with ha,
    have mem_antidiag : (max₁, max₂) ∈ antidiag,
    { simp only [add_sum_erase, mem_filter, mem_product],
      exact ⟨⟨mem_of_mem_filter _ mem_max₁, mem_of_mem_filter _ mem_max₂⟩, rfl⟩ },
    have eq_add_sum :=
      calc  proj 𝒜 (max₁ + max₂) (x * y)
          = ∑ ij in antidiag, proj 𝒜 ij.1 x * proj 𝒜 ij.2 y
          : by simp_rw [ha, proj_apply, direct_sum.decompose_mul,
                        direct_sum.coe_mul_apply 𝒜]
      ... = proj 𝒜 max₁ x * proj 𝒜 max₂ y + ∑ ij in antidiag.erase (max₁, max₂),
                                              proj 𝒜 ij.1 x * proj 𝒜 ij.2 y
          : (add_sum_erase _ _ mem_antidiag).symm,
    rw eq_sub_of_add_eq eq_add_sum.symm,
    refine ideal.sub_mem _ hxy (ideal.sum_mem _ (λ z H, _)),
    rcases z with ⟨i, j⟩,
    simp only [mem_erase, prod.mk.inj_iff, ne.def, mem_filter, mem_product] at H,
    rcases H with ⟨H₁, ⟨H₂, H₃⟩, H₄⟩,
    have max_lt : max₁ < i ∨ max₂ < j,
    { rcases lt_trichotomy max₁ i with h | rfl | h,
      { exact or.inl h },
      { refine false.elim (H₁ ⟨rfl, add_left_cancel H₄⟩), },
      { apply or.inr,
        have := add_lt_add_right h j,
        rw H₄ at this,
        exact lt_of_add_lt_add_left this, }, },
    cases max_lt,
    { -- in this case `max₁ < i`, then `xᵢ ∈ I`; for otherwise `i ∈ set₁` then `i ≤ max₁`.
      have not_mem : i ∉ set₁ := λ h, lt_irrefl _
        ((max'_lt_iff set₁ (nonempty x rid₁)).mp max_lt i h),
      rw set₁_eq at not_mem,
      simp only [not_and, not_not, ne.def, mem_filter] at not_mem,
      exact ideal.mul_mem_right _ I (not_mem H₂), },
    { -- in this case  `max₂ < j`, then `yⱼ ∈ I`; for otherwise `j ∈ set₂`, then `j ≤ max₂`.
      have not_mem : j ∉ set₂ := λ h, lt_irrefl _
        ((max'_lt_iff set₂ (nonempty y rid₂)).mp max_lt j h),
      rw set₂_eq at not_mem,
      simp only [not_and, not_not, ne.def, mem_filter] at not_mem,
      exact ideal.mul_mem_left I _ (not_mem H₃), }, },

  have not_mem_I : proj 𝒜 max₁ x * proj 𝒜 max₂ y ∉ I,
  { have neither_mem : proj 𝒜 max₁ x ∉ I ∧ proj 𝒜 max₂ y ∉ I,
    { rw mem_filter at mem_max₁ mem_max₂,
      exact ⟨mem_max₁.2, mem_max₂.2⟩, },
    intro rid,
    cases homogeneous_mem_or_mem ⟨max₁, set_like.coe_mem _⟩ ⟨max₂, set_like.coe_mem _⟩ mem_I,
    { apply neither_mem.1 h },
    { apply neither_mem.2 h }, },

  exact not_mem_I mem_I,
end⟩

lemma ideal.is_homogeneous.is_prime_iff {I : ideal A} (h : I.is_homogeneous 𝒜) :
  I.is_prime ↔
  (I ≠ ⊤) ∧
    ∀ {x y : A}, set_like.is_homogeneous 𝒜 x → set_like.is_homogeneous 𝒜 y
      → (x * y ∈ I → x ∈ I ∨ y ∈ I) :=
⟨λ HI,
  ⟨ne_of_apply_ne _ HI.ne_top, λ x y hx hy hxy, ideal.is_prime.mem_or_mem HI hxy⟩,
  λ ⟨I_ne_top, homogeneous_mem_or_mem⟩,
    h.is_prime_of_homogeneous_mem_or_mem I_ne_top @homogeneous_mem_or_mem⟩

lemma ideal.is_prime.homogeneous_core {I : ideal A} (h : I.is_prime) :
  (I.homogeneous_core 𝒜).to_ideal.is_prime :=
begin
  apply (ideal.homogeneous_core 𝒜 I).is_homogeneous.is_prime_of_homogeneous_mem_or_mem,
  { exact ne_top_of_le_ne_top h.ne_top (ideal.to_ideal_homogeneous_core_le 𝒜 I) },
  rintros x y hx hy hxy,
  have H := h.mem_or_mem (ideal.to_ideal_homogeneous_core_le 𝒜 I hxy),
  refine H.imp _ _,
  { exact ideal.mem_homogeneous_core_of_is_homogeneous_of_mem hx, },
  { exact ideal.mem_homogeneous_core_of_is_homogeneous_of_mem hy, },
end

lemma ideal.is_homogeneous.radical_eq {I : ideal A} (hI : I.is_homogeneous 𝒜) :
  I.radical = Inf { J | J.is_homogeneous 𝒜 ∧ I ≤ J ∧ J.is_prime } :=
begin
  rw ideal.radical_eq_Inf,
  apply le_antisymm,
  { exact Inf_le_Inf (λ J, and.right), },
  { refine Inf_le_Inf_of_forall_exists_le _,
    rintros J ⟨HJ₁, HJ₂⟩,
    refine ⟨(J.homogeneous_core 𝒜).to_ideal, _, J.to_ideal_homogeneous_core_le _⟩,
    refine ⟨homogeneous_ideal.is_homogeneous _, _, HJ₂.homogeneous_core⟩,
    refine hI.to_ideal_homogeneous_core_eq_self.symm.trans_le (ideal.homogeneous_core_mono _ HJ₁), }
end

lemma ideal.is_homogeneous.radical {I : ideal A} (h : I.is_homogeneous 𝒜)  :
  I.radical.is_homogeneous 𝒜 :=
by { rw h.radical_eq, exact ideal.is_homogeneous.Inf (λ _, and.left) }

/-- The radical of a homogenous ideal, as another homogenous ideal. -/
def homogeneous_ideal.radical (I : homogeneous_ideal 𝒜) : homogeneous_ideal 𝒜 :=
⟨I.to_ideal.radical, I.is_homogeneous.radical⟩

@[simp]
lemma homogeneous_ideal.coe_radical (I : homogeneous_ideal 𝒜) :
  I.radical.to_ideal = I.to_ideal.radical := rfl

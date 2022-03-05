/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import ring_theory.graded_algebra.homogeneous_ideal

/-!

This file contains a proof that the radical of any homogeneous ideal is a homogeneous ideal

## Main statements

* `homogeneous_ideal.is_prime_iff`: a homogeneous ideal `I` is prime if and only if `I` is
  homogeneously prime, i.e. if `x, y` are homogeneous elements such that `x * y ∈ I`, then
  at least one of `x,y` is in `I`.
* `homogeneous_ideal.rad`: radical of homogeneous ideal is a homogeneous ideal.

## Implementation details

Throughout this file, the indexing type `ι` of grading is assumed to be a
`linear_ordered_cancel_add_comm_monoid`. This might be stronger than necessary and `linarith`
does not work on `linear_ordered_cancel_add_comm_monoid`.

## Tags

homogeneous, radical
-/

open graded_algebra set_like finset
open_locale big_operators

variables {ι R A : Type*}
variables [comm_semiring R] [comm_ring A] [algebra R A]
variables [linear_ordered_cancel_add_comm_monoid ι]
variables {𝒜 : ι → submodule R A} [graded_algebra 𝒜]

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
  letI : Π (x : A),
    decidable_pred (λ (i : ι), proj 𝒜 i x ∉ I) := λ x, classical.dec_pred _,
  letI : Π i (x : 𝒜 i), decidable (x ≠ 0) := λ i x, classical.dec _,
  set set₁ := (support 𝒜 x).filter (λ i, proj 𝒜 i x ∉ I) with set₁_eq,
  set set₂ := (support 𝒜 y).filter (λ i, proj 𝒜 i y ∉ I) with set₂_eq,
  have nonempty : ∀ (x : A), (x ∉ I) → ((support 𝒜 x).filter (λ i, proj 𝒜 i x ∉ I)).nonempty,
  { intros x hx,
    rw filter_nonempty_iff,
    contrapose! hx,
    rw ← sum_support_decompose 𝒜 x,
    apply ideal.sum_mem _ hx, },
  set max₁ := set₁.max' (nonempty x rid₁) with max₁_eq,
  set max₂ := set₂.max' (nonempty y rid₂) with max₂_eq,
  have mem_max₁ : max₁ ∈ set₁ := max'_mem set₁ (nonempty x rid₁),
  have mem_max₂ : max₂ ∈ set₂ := max'_mem set₂ (nonempty y rid₂),
  replace hxy : proj 𝒜 (max₁ + max₂) (x * y) ∈ I := hI _ hxy,

  have mem_I : proj 𝒜 max₁ x * proj 𝒜 max₂ y ∈ I,
  { set antidiag :=
      ((support 𝒜 x).product (support 𝒜 y)).filter (λ z : ι × ι, z.1 + z.2 = max₁ + max₂) with ha,
    have mem_antidiag : (max₁, max₂) ∈ antidiag,
    { simp only [add_sum_erase, mem_filter, mem_product],
      exact ⟨⟨mem_of_mem_filter _ mem_max₁, mem_of_mem_filter _ mem_max₂⟩, rfl⟩ },
    have eq_add_sum :=
      calc  proj 𝒜 (max₁ + max₂) (x * y)
          = ∑ ij in antidiag, proj 𝒜 ij.1 x * proj 𝒜 ij.2 y
          : by simp_rw [ha, proj_apply, map_mul, support, direct_sum.coe_mul_apply_submodule]
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
      simp only [not_and, not_not, ne.def, dfinsupp.mem_support_to_fun, mem_filter] at not_mem,
      exact ideal.mul_mem_right _ I (not_mem H₂), },
    { -- in this case  `max₂ < j`, then `yⱼ ∈ I`; for otherwise `j ∈ set₂`, then `j ≤ max₂`.
      have not_mem : j ∉ set₂ := λ h, lt_irrefl _
        ((max'_lt_iff set₂ (nonempty y rid₂)).mp max_lt j h),
      rw set₂_eq at not_mem,
      simp only [not_and, not_not, ne.def, dfinsupp.mem_support_to_fun, mem_filter] at not_mem,
      exact ideal.mul_mem_left I _ (not_mem H₃), }, },

  have not_mem_I : proj 𝒜 max₁ x * proj 𝒜 max₂ y ∉ I,
  { have neither_mem : proj 𝒜 max₁ x ∉ I ∧ proj 𝒜 max₂ y ∉ I,
    { rw mem_filter at mem_max₁ mem_max₂,
      exact ⟨mem_max₁.2, mem_max₂.2⟩, },
    intro rid,
    cases homogeneous_mem_or_mem ⟨max₁, submodule.coe_mem _⟩ ⟨max₂, submodule.coe_mem _⟩ mem_I,
    { apply neither_mem.1 h },
    { apply neither_mem.2 h }, },

  exact not_mem_I mem_I,
end⟩

lemma ideal.is_homogeneous.is_prime_iff {I : ideal A} (h : ideal.is_homogeneous 𝒜) :
  I.is_prime ↔
  (I ≠ ⊤) ∧
    ∀ {x y : A}, set_like.is_homogeneous 𝒜 x → set_like.is_homogeneous 𝒜 y
      → (x * y ∈ I → x ∈ I ∨ y ∈ I) :=
⟨λ HI,
  ⟨ne_of_apply_ne _ HI.ne_top, λ x y hx hy hxy, ideal.is_prime.mem_or_mem HI hxy⟩,
  λ ⟨I_ne_top, homogeneous_mem_or_mem⟩,
    I.prop.is_prime_of_homogeneous_mem_or_mem (subtype.coe_injective.ne I_ne_top)
      @homogeneous_mem_or_mem ⟩

lemma ideal.is_prime.homogeneous_core {I : ideal A} (h : I.is_prime) :
  (I.homogeneous_core 𝒜 : ideal A).is_prime :=
begin
  apply (ideal.homogeneous_core 𝒜 I).prop.is_prime_of_homogeneous_mem_or_mem,
  { exact ne_top_of_le_ne_top h.ne_top (ideal.coe_homogeneous_core_le 𝒜 I) },
  rintros x y hx hy hxy,
  have H := h.mem_or_mem (ideal.coe_homogeneous_core_le 𝒜 I hxy),
  refine H.imp _ _,
  { exact ideal.mem_homogeneous_core_of_is_homogeneous_of_mem hx, },
  { exact ideal.mem_homogeneous_core_of_is_homogeneous_of_mem hy, },
end

lemma homogeneous_ideal.radical_eq (I : homogeneous_ideal 𝒜) :
  (I : ideal A).radical = Inf {J | ↑I ≤ J ∧ J.is_homogeneous 𝒜 ∧ J.is_prime} :=
begin
  letI : Π i (x : 𝒜 i), decidable (x ≠ 0) := λ i x, classical.dec _,
  rw ideal.radical_eq_Inf,
  apply le_antisymm,
  { refine Inf_le_Inf _,
    rintros J ⟨HJ₁, _, HJ₂⟩,
    exact ⟨HJ₁, HJ₂⟩, },
  { intros x hx,
    rw [submodule.mem_Inf] at hx ⊢,
    rintros J ⟨HJ₁, HJ₂⟩,
    refine (ideal.coe_homogeneous_core_le 𝒜 J) (hx _ _),
    refine ⟨_, subtype.prop _, HJ₂.homogeneous_core⟩,
    refine I.homogeneous_core_coe_eq_self.symm.trans_le (ideal.homogeneous_core_mono _ HJ₁), }
end

lemma ideal.is_homogeneous_ideal.radical {I : ideal A} (h : I.is_homogeneous 𝒜)  :
  I.radical.is_homogeneous 𝒜 :=
begin
  have radI_eq : I.radical = _ := homogeneous_ideal.radical_eq ⟨I, h⟩,
  rw radI_eq,
  convert (Inf {J : homogeneous_ideal 𝒜 | I ≤ J.val ∧ J.val.is_prime}).2,
  ext J,
  simp only [subtype.coe_mk, set.mem_set_of_eq, subtype.exists, exists_prop],
  split;
  intro H,
  { exact ⟨_, H.2.1, ⟨H.1, H.2.2⟩, rfl⟩, },
  { obtain ⟨J', HJ1, ⟨HJ2, HJ3⟩, rfl⟩ := H,
    exact ⟨HJ2, HJ1, HJ3⟩, },
end

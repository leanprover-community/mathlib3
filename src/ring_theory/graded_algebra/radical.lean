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

Through out this file, the indexing type `ι` of grading is assumed to be a
`linear_ordered_cancel_add_comm_monoid`. This might be stronger than necessary and `linearith`
does not work on `linear_ordered_cancel_add_comm_monoid`.

## Tags

homogeneous, radical
-/


open_locale big_operators

section linear_ordered_cancel_add_comm_monoid

variables {ι R A : Type*}
variables [comm_semiring R] [comm_ring A] [algebra R A]
variables [linear_ordered_cancel_add_comm_monoid ι] [decidable_eq ι]
variables (𝒜 : ι → submodule R A) [graded_algebra 𝒜]
variable [Π (I : homogeneous_ideal 𝒜) (x : A),
  decidable_pred (λ (i : ι), graded_algebra.proj 𝒜 i x ∉ I)]
variable [Π (i : ι) (x : 𝒜 i), decidable (x ≠ 0)]

lemma homogeneous_ideal.is_prime_of_homogeneous_mem_or_mem
  (I : homogeneous_ideal 𝒜)
  (I_ne_top : I ≠ ⊤)
  (homogeneous_mem_or_mem : ∀ {x y : A},
    set_like.is_homogeneous 𝒜 x → set_like.is_homogeneous 𝒜 y
    → (x * y ∈ I.1 → x ∈ I.1 ∨ y ∈ I.1)) : ideal.is_prime I.1 :=
⟨subtype.coe_injective.ne I_ne_top, begin
  intros x y hxy, by_contradiction rid,
  obtain ⟨rid₁, rid₂⟩ := not_or_distrib.mp rid,
  set set₁ := (graded_algebra.support 𝒜 x).filter (λ i, graded_algebra.proj 𝒜 i x ∉ I) with set₁_eq,
  set set₂ := (graded_algebra.support 𝒜 y).filter (λ i, graded_algebra.proj 𝒜 i y ∉ I) with set₂_eq,
  have set₁_nonempty : set₁.nonempty,
  { replace rid₁ : ¬(∀ (i : ι), (graded_algebra.decompose 𝒜 x i : A) ∈ I.val),
    { intros rid,
      apply rid₁,
      rw ←graded_algebra.sum_support_decompose 𝒜 x,
      apply ideal.sum_mem,
      intros,
      apply rid, },
    rw [not_forall] at rid₁,
    obtain ⟨i, h⟩ := rid₁,
    refine ⟨i, _⟩,
    rw set₁_eq,
    simp only [ne.def, dfinsupp.mem_support_to_fun, finset.mem_filter],
    refine ⟨_, h⟩,
    rw graded_algebra.mem_support_iff,
    intro rid₃,
    rw graded_algebra.proj_apply at rid₃,
    rw rid₃ at h,
    simpa only [not_true, submodule.zero_mem, add_monoid_hom.map_zero] using h, },
  have set₂_nonempty : set₂.nonempty,
  { replace rid₂ : ¬(∀ (i : ι), (graded_algebra.decompose 𝒜 y i : A) ∈ I.val),
    { intros rid,
      apply rid₂,
      rw ←graded_algebra.sum_support_decompose 𝒜 y,
      apply ideal.sum_mem,
      intros,
      apply rid, },
    rw [not_forall] at rid₂,
    obtain ⟨i, h⟩ := rid₂,
    refine ⟨i, _⟩,
    rw set₂_eq,
    simp only [ne.def, dfinsupp.mem_support_to_fun, finset.mem_filter],
    refine ⟨_, h⟩,
    rw graded_algebra.mem_support_iff,
    intro rid₃,
    rw graded_algebra.proj_apply at rid₃,
    rw rid₃ at h,
    simpa only [not_true, submodule.zero_mem, add_monoid_hom.map_zero] using h, },
  set max₁ := set₁.max' set₁_nonempty with max₁_eq,
  set max₂ := set₂.max' set₂_nonempty with max₂_eq,
  have mem_max₁ := finset.max'_mem set₁ set₁_nonempty,
  rw [←max₁_eq, set₁_eq] at mem_max₁,
  have mem_max₂ := finset.max'_mem set₂ set₂_nonempty,
  rw [←max₂_eq, set₂_eq] at mem_max₂,
  replace hxy : ∀ (i : ι), (graded_algebra.decompose 𝒜 (x * y) i : A) ∈ I.val := λ i, I.2 i hxy,
  specialize hxy (max₁ + max₂),
  have eq :=
    calc  graded_algebra.proj 𝒜 (max₁ + max₂) (x * y)
        = ∑ ij in ((graded_algebra.support 𝒜 x).product (graded_algebra.support 𝒜 y)).filter
            (λ (z : ι × ι), z.1 + z.2 = max₁ + max₂),
            (graded_algebra.proj 𝒜 ij.1 x) * (graded_algebra.proj 𝒜 ij.2 y)
        : _ --(0)
    ... = ∑ ij in ((graded_algebra.support 𝒜 x).product (graded_algebra.support 𝒜 y)).filter
            (λ (z : ι × ι), z.1 + z.2 = max₁ + max₂)
                    \ {(max₁, max₂)} ∪ {(max₁, max₂)},
            (graded_algebra.proj 𝒜 ij.1 x) * (graded_algebra.proj 𝒜 ij.2 y)
        : _ -- (1),
    ... = ∑ (ij : ι × ι) in ((graded_algebra.support 𝒜 x).product
            (graded_algebra.support 𝒜 y)).filter
            (λ (z : ι × ι), prod.fst z + z.snd = max₁ + max₂)
                    \ {(max₁, max₂)},
            (graded_algebra.proj 𝒜 (prod.fst ij) x) * (graded_algebra.proj 𝒜 ij.snd y)
        + ∑ ij in {(max₁, max₂)}, (graded_algebra.proj 𝒜 (prod.fst ij) x)
            * (graded_algebra.proj 𝒜 ij.snd y)
        : _ -- (2)
    ... = ∑ ij in ((graded_algebra.support 𝒜 x).product (graded_algebra.support 𝒜 y)).filter
            (λ (z : ι × ι), z.1 + z.2 = max₁ + max₂)
                    \ {(max₁, max₂)},
            (graded_algebra.proj 𝒜 ij.1 x) * (graded_algebra.proj 𝒜 ij.2 y)
        + _
        : by rw finset.sum_singleton,

  have eq₂ :
    (graded_algebra.proj 𝒜 max₁) x * (graded_algebra.proj 𝒜 max₂) y
          = graded_algebra.proj 𝒜 (max₁ + max₂) (x * y)
          - ∑ (ij : ι × ι) in finset.filter (λ (z : ι × ι), z.fst + z.snd = max₁ + max₂)
              ((graded_algebra.support 𝒜 x).product (graded_algebra.support 𝒜 y)) \ {(max₁, max₂)},
              (graded_algebra.proj 𝒜 ij.fst) x * (graded_algebra.proj 𝒜 ij.snd) y,
  { rw [eq, eq_sub_iff_add_eq, add_comm], },

  have mem_I₂ : ∑ (ij : ι × ι) in finset.filter (λ (z : ι × ι), z.fst + z.snd = max₁ + max₂)
              ((graded_algebra.support 𝒜 x).product (graded_algebra.support 𝒜 y)) \ {(max₁, max₂)},
              (graded_algebra.proj 𝒜 ij.fst) x * (graded_algebra.proj 𝒜 ij.snd) y ∈ I,
  { apply ideal.sum_mem,
    rintros ⟨i, j⟩ H,
    simp only [not_and, prod.mk.inj_iff, finset.mem_sdiff, ne.def, dfinsupp.mem_support_to_fun,
       finset.mem_singleton, finset.mem_filter, finset.mem_product] at H,
    obtain ⟨⟨⟨H₁, H₂⟩, H₃⟩, H₄⟩ := H,
    cases lt_trichotomy i max₁,
    { -- in this case `i < max₁`, so `max₂ < j`, so `of A j (y j) ∈ I`
      have ineq : max₂ < j,
      { by_contra rid₂, rw not_lt at rid₂,
        have rid₃ := add_lt_add_of_le_of_lt rid₂ h,
        conv_lhs at rid₃ { rw add_comm },
        conv_rhs at rid₃ { rw add_comm },
        rw H₃ at rid₃, exact lt_irrefl _ rid₃, },
      have not_mem_j : j ∉ set₂,
      { intro rid₂,
        rw max₂_eq at ineq,
        have rid₃ := (finset.max'_lt_iff set₂ set₂_nonempty).mp ineq j rid₂,
        exact lt_irrefl _ rid₃, },
      rw set₂_eq at not_mem_j,
      simp only [not_and, not_not, ne.def, dfinsupp.mem_support_to_fun,
        finset.mem_filter] at not_mem_j,
      specialize not_mem_j H₂,
      apply ideal.mul_mem_left,
      convert not_mem_j, },
    { cases h,
      { -- in this case `i = max₁`, so `max₂ = j`, contradictory
        have : j = max₂,
        { rw h at H₃,
          exact linear_ordered_cancel_add_comm_monoid.add_left_cancel _ _ _ H₃, },
        exfalso,
        exact H₄ h this, },
      { -- in this case `i > max₁`, so `i < max₁`, so `of A i (x i) ∈ I`
        have ineq : max₁ < i,
        { by_contra rid₂, rw not_lt at rid₂,
          have rid₃ := add_lt_add_of_le_of_lt rid₂ h,
          conv_lhs at rid₃ { rw linear_ordered_cancel_add_comm_monoid.add_comm },
          exact lt_irrefl _ rid₃, },
        have not_mem_i : i ∉ set₁,
        { intro rid₂,
          rw max₁_eq at ineq,
          have rid₃ := (finset.max'_lt_iff set₁ set₁_nonempty).mp ineq i rid₂,
          exact lt_irrefl _ rid₃,},
        rw set₁_eq at not_mem_i,
        simp only [not_and, not_not, ne.def, dfinsupp.mem_support_to_fun,
          finset.mem_filter] at not_mem_i,
        specialize not_mem_i H₁,
        apply ideal.mul_mem_right _ I.1,
        convert not_mem_i, }, } },
  have mem_I₃ :
    (graded_algebra.proj 𝒜 (max₁, max₂).fst) x * (graded_algebra.proj 𝒜 (max₁, max₂).snd) y ∈ I,
  { rw eq₂, apply ideal.sub_mem,
    have HI := I.2,
    specialize HI (max₁ + max₂) hxy, exact hxy, exact mem_I₂, },
  specialize homogeneous_mem_or_mem ⟨max₁, _⟩ ⟨max₂, _⟩ mem_I₃,
  rw [graded_algebra.proj_apply], exact submodule.coe_mem _,
  rw [graded_algebra.proj_apply], exact submodule.coe_mem _,
  cases homogeneous_mem_or_mem,
  simp only [ne.def, dfinsupp.mem_support_to_fun, finset.mem_filter] at mem_max₁,
  refine mem_max₁.2 homogeneous_mem_or_mem,
  simp only [ne.def, dfinsupp.mem_support_to_fun, finset.mem_filter] at mem_max₂,
  refine mem_max₂.2 homogeneous_mem_or_mem,

  -- (0)
  { rw [graded_algebra.proj_apply, alg_equiv.map_mul, graded_algebra.support,
      graded_algebra.support, direct_sum.coe_mul_apply_submodule], refl },

  -- (1)
  { congr, ext, split; intros H,
    { simp only [finset.mem_filter, ne.def, dfinsupp.mem_support_to_fun, finset.mem_product] at H,
      rw finset.mem_union,
      by_cases a = (max₁, max₂),
      right, rw h, exact finset.mem_singleton_self (max₁, max₂),
      left, rw finset.mem_sdiff, split,
      simp only [finset.mem_filter, ne.def, dfinsupp.mem_support_to_fun, finset.mem_product],
      exact H, intro rid, simp only [finset.mem_singleton] at rid, exact h rid, },
    { rw finset.mem_union at H, cases H,
      rw finset.mem_sdiff at H, exact H.1,
      simp only [finset.mem_filter, ne.def, dfinsupp.mem_support_to_fun, finset.mem_product],
      simp only [finset.mem_singleton] at H, rw H,
      refine ⟨⟨_, _⟩, rfl⟩,
      simp only [ne.def, dfinsupp.mem_support_to_fun, finset.mem_filter] at mem_max₁,
      exact mem_max₁.1,
      simp only [ne.def, dfinsupp.mem_support_to_fun, finset.mem_filter] at mem_max₂,
      exact mem_max₂.1, }, },

  -- (2)
  { rw [finset.sum_union],
    apply finset.disjoint_iff_inter_eq_empty.mpr,
    rw finset.eq_empty_iff_forall_not_mem, rintros ⟨i, j⟩ Hij,
    rw [finset.mem_inter, finset.mem_sdiff, finset.mem_filter] at Hij,
    simp only [not_and, prod.mk.inj_iff, ne.def, dfinsupp.mem_support_to_fun, finset.mem_singleton,
      finset.mem_product] at Hij,
    exact Hij.1.2 Hij.2.1 Hij.2.2, },
end⟩

lemma homogeneous_ideal.is_prime_iff (I : homogeneous_ideal 𝒜) :
  I.1.is_prime ↔
  (I ≠ ⊤) ∧
    ∀ {x y : A}, set_like.is_homogeneous 𝒜 x → set_like.is_homogeneous 𝒜 y
      → (x * y ∈ I.1 → x ∈ I.1 ∨ y ∈ I.1) :=
⟨λ HI, ⟨λ rid, begin
    rw homogeneous_ideal.eq_top_iff at rid,
    apply HI.1,
    exact rid,
  end, λ x y hx hy hxy, ideal.is_prime.mem_or_mem HI hxy⟩, λ HI, begin
  obtain ⟨I_ne_top, homogeneous_mem_or_mem⟩ := HI,
  apply homogeneous_ideal.is_prime_of_homogeneous_mem_or_mem 𝒜 I I_ne_top,
  intros x y,
  apply homogeneous_mem_or_mem,
end⟩

lemma homogeneous_ideal.rad_eq (I : homogeneous_ideal 𝒜) :
  I.1.radical = Inf {J | I.1 ≤ J ∧ J.is_homogeneous 𝒜 ∧ J.is_prime} :=
begin
  have subset₁ : I.1.radical ≤ Inf {J | I.1 ≤ J ∧ J.is_homogeneous 𝒜 ∧ J.is_prime},
  { rw ideal.radical_eq_Inf, intros x hx,
    rw [submodule.mem_Inf] at hx ⊢, intros J HJ, apply hx,
    obtain ⟨HJ₁, _, HJ₂⟩ := HJ,
    refine ⟨HJ₁, HJ₂⟩, },
  have subset₂ : Inf {J | I.1 ≤ J ∧ J.is_homogeneous 𝒜 ∧ J.is_prime} ≤ I.1.radical,
  { intros x hx,
    rw ideal.radical_eq_Inf,
    rw [submodule.mem_Inf] at hx ⊢,
    rintros J ⟨HJ₁, HJ₂⟩,
    specialize hx (ideal.homogeneous_core 𝒜 J) _,
    refine ⟨_, (ideal.homogeneous_core 𝒜 _).2, _⟩,
    { have HI := I.2,
      rw [ideal.is_homogeneous.iff_eq] at HI,
      rw ← HI,
      apply ideal.span_mono, intros y hy,
      obtain ⟨z, ⟨hz₁, rfl⟩⟩ := hy,
      rw set.mem_preimage at hz₁,
      specialize HJ₁ hz₁,
      refine ⟨z, _, rfl⟩,
      simpa [set.mem_preimage] using HJ₁, },
    { set J' := ideal.homogeneous_core 𝒜 J with eq_J',
      have homogeneity₀ := (ideal.homogeneous_core 𝒜 J).2,
      apply homogeneous_ideal.is_prime_of_homogeneous_mem_or_mem 𝒜 ⟨J', homogeneity₀⟩,
      intro rid,
      have rid' : J = ⊤,
      { have : J'.1 ≤ J := ideal.coe_homogeneous_core_le 𝒜 J,
        simp only [homogeneous_ideal.eq_top_iff] at rid,
        erw ← subtype.val_eq_coe at rid,
        erw rid at this,
        rw top_le_iff at this,
        exact this, },
      apply HJ₂.1, exact rid',
      rintros x y hx hy hxy,
      have H := HJ₂.mem_or_mem (ideal.coe_homogeneous_core_le 𝒜 J hxy),
      cases H,
      { left,
        have : ∀ i : ι, (graded_algebra.decompose 𝒜 x i : A) ∈
          (⟨J', homogeneity₀⟩ : homogeneous_ideal 𝒜),
        { intros i, apply homogeneity₀, apply ideal.subset_span,
          simp only [set.mem_inter_eq, set_like.mem_coe, set.mem_set_of_eq],
          refine ⟨⟨x, hx⟩, H, rfl⟩, },
        rw ←graded_algebra.sum_support_decompose 𝒜 x,
        apply ideal.sum_mem J'.1,
        intros j hj,
        apply this, },
      { right,
        have : ∀ i : ι, (graded_algebra.decompose 𝒜 y i : A) ∈
          (⟨J', homogeneity₀⟩ : homogeneous_ideal 𝒜),
        { intros i, apply homogeneity₀, apply ideal.subset_span,
          simp only [set.mem_inter_eq, set_like.mem_coe, set.mem_set_of_eq],
          refine ⟨⟨y, hy⟩, H, rfl⟩, },
        rw ←graded_algebra.sum_support_decompose 𝒜 y,
        apply ideal.sum_mem J'.1,
        intros j hj,
        apply this, }, },
      refine (ideal.coe_homogeneous_core_le 𝒜 J) hx, },

  ext x, split;
  intro hx,
  { exact subset₁ hx },
  { exact subset₂ hx },
end

lemma ideal.is_homogeneous_ideal.radical {I : ideal A} (h : I.is_homogeneous 𝒜)  :
  I.radical.is_homogeneous 𝒜 :=
begin
  have radI_eq := homogeneous_ideal.rad_eq 𝒜 ⟨I, h⟩,
  rw radI_eq,
  have : Inf {J : ideal A | I ≤ J ∧ J.is_homogeneous 𝒜 ∧ J.is_prime} =
    (Inf {J : homogeneous_ideal 𝒜 | I.1 ≤ J.1 ∧ J.1.is_prime }).1,
  { simp only [subtype.coe_le_coe, subtype.val_eq_coe],
    rw homogeneous_ideal.coe_Inf,
    congr' 1,
    ext J,
    rw set.mem_image,
    simp only [set.mem_set_of_eq, subtype.exists, subtype.coe_mk, exists_and_distrib_right,
      exists_eq_right],
    split;
    intro H,
    { exact ⟨⟨H.2.1, H.1⟩, H.2.2⟩, },
    { obtain ⟨⟨HJ1, HJ2⟩, HJ3⟩ := H,
      exact ⟨HJ2, HJ1, HJ3⟩, } },
  rw this,
  exact (Inf {J : homogeneous_ideal 𝒜 | I ≤ J.val ∧ J.val.is_prime}).2,
end

end linear_ordered_cancel_add_comm_monoid

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
variables {𝒜 : ι → submodule R A} [graded_algebra 𝒜]

lemma ideal.is_homogeneous.is_prime_of_homogeneous_mem_or_mem
  {I : ideal A} (hI : I.is_homogeneous 𝒜) (I_ne_top : I ≠ ⊤)
  (homogeneous_mem_or_mem : ∀ {x y : A},
    set_like.is_homogeneous 𝒜 x → set_like.is_homogeneous 𝒜 y
    → (x * y ∈ I → x ∈ I ∨ y ∈ I)) : ideal.is_prime I :=
⟨I_ne_top, begin
  intros x y hxy, by_contradiction rid,
  obtain ⟨rid₁, rid₂⟩ := not_or_distrib.mp rid,
  letI : Π (x : A),
    decidable_pred (λ (i : ι), graded_algebra.proj 𝒜 i x ∉ I) := λ x, classical.dec_pred _,
  letI : Π i (x : 𝒜 i), decidable (x ≠ 0) := λ i x, classical.dec _,
  set set₁ := (graded_algebra.support 𝒜 x).filter (λ i, graded_algebra.proj 𝒜 i x ∉ I) with set₁_eq,
  set set₂ := (graded_algebra.support 𝒜 y).filter (λ i, graded_algebra.proj 𝒜 i y ∉ I) with set₂_eq,
  have set₁_nonempty : set₁.nonempty,
  { rw finset.filter_nonempty_iff,
    contrapose! rid₁,
    rw ← graded_algebra.sum_support_decompose 𝒜 x,
    apply ideal.sum_mem _ rid₁,},
  have set₂_nonempty : set₂.nonempty,
  { rw finset.filter_nonempty_iff,
    contrapose! rid₂,
    rw ← graded_algebra.sum_support_decompose 𝒜 y,
    apply ideal.sum_mem _ rid₂, },
  set max₁ := set₁.max' set₁_nonempty with max₁_eq,
  set max₂ := set₂.max' set₂_nonempty with max₂_eq,
  have mem_max₁ := finset.max'_mem set₁ set₁_nonempty,
  have mem_max₂ := finset.max'_mem set₂ set₂_nonempty,
  replace hxy : ∀ (i : ι), (graded_algebra.decompose 𝒜 (x * y) i : A) ∈ I := λ i, hI i hxy,
  specialize hxy (max₁ + max₂),
  have eq :=
    calc  graded_algebra.proj 𝒜 (max₁ + max₂) (x * y)
        = ∑ ij in ((graded_algebra.support 𝒜 x).product (graded_algebra.support 𝒜 y)).filter
            (λ z, z.1 + z.2 = max₁ + max₂),
            (graded_algebra.proj 𝒜 ij.1 x) * (graded_algebra.proj 𝒜 ij.2 y)
        : begin
          rw [graded_algebra.proj_apply, alg_equiv.map_mul, graded_algebra.support,
            graded_algebra.support, direct_sum.coe_mul_apply_submodule],
          refl,
        end
    ... = ∑ ij in (((graded_algebra.support 𝒜 x).product (graded_algebra.support 𝒜 y)).filter
            (λ (z : ι × ι), z.1 + z.2 = max₁ + max₂)).erase (max₁, max₂),
            (graded_algebra.proj 𝒜 ij.1 x) * (graded_algebra.proj 𝒜 ij.2 y) +
          (graded_algebra.proj 𝒜 max₁ x) * (graded_algebra.proj 𝒜 max₂ y)
        : begin
          rw finset.sum_erase_add,
          simp only [finset.mem_filter, finset.mem_product, eq_self_iff_true, and_true],
          exact ⟨(finset.filter_subset _ _) mem_max₁, (finset.filter_subset _ _) mem_max₂⟩,
        end,

  have eq₂ : (graded_algebra.proj 𝒜 max₁) x * (graded_algebra.proj 𝒜 max₂) y
          = graded_algebra.proj 𝒜 (max₁ + max₂) (x * y)
          - ∑ (ij : ι × ι) in (((graded_algebra.support 𝒜 x).product
              (graded_algebra.support 𝒜 y)).filter
              (λ (z : ι × ι), z.fst + z.snd = max₁ + max₂)).erase (max₁, max₂),
              (graded_algebra.proj 𝒜 ij.fst) x * (graded_algebra.proj 𝒜 ij.snd) y,
  { rw [eq, eq_sub_iff_add_eq, add_comm], },

  have mem_I :
    (graded_algebra.proj 𝒜 (max₁, max₂).fst) x * (graded_algebra.proj 𝒜 (max₁, max₂).snd) y ∈ I,
  { rw eq₂,
    refine ideal.sub_mem _ hxy (ideal.sum_mem _ (λ z H, _)),
    rcases z with ⟨i, j⟩,
    simp only [finset.mem_erase, prod.mk.inj_iff, ne.def, finset.mem_filter,
      finset.mem_product] at H,
    rcases H with ⟨H₁, ⟨H₂, H₃⟩, H₄⟩,
    have max_lt : max₁ < i ∨ max₂ < j,
    { rcases lt_trichotomy max₁ i with h | rfl | h,
      { exact or.inl h },
      { refine false.elim (H₁ ⟨rfl, add_left_cancel H₄⟩), },
      { apply or.inr,
        have := add_lt_add_right h j,
        rw H₄ at this,
        apply lt_of_add_lt_add_left this, }, },
    cases max_lt,
    { -- in this case `i < max₁`, so `of A i (x i) ∈ I`
      have not_mem : i ∉ set₁ := λ h,
        lt_irrefl _ ((finset.max'_lt_iff set₁ set₁_nonempty).mp max_lt i h),
      rw set₁_eq at not_mem,
      simp only [not_and, not_not, ne.def, dfinsupp.mem_support_to_fun,
        finset.mem_filter] at not_mem,
      exact ideal.mul_mem_right _ I (not_mem H₂), },
    { -- in this case  `max₂ < j`, so `of A j (y j) ∈ I`
      have not_mem : j ∉ set₂ := λ h,
        lt_irrefl _ ((finset.max'_lt_iff set₂ set₂_nonempty).mp max_lt j h),
      rw set₂_eq at not_mem,
      simp only [not_and, not_not, ne.def, dfinsupp.mem_support_to_fun,
        finset.mem_filter] at not_mem,
      exact ideal.mul_mem_left I _ (not_mem H₃), }, },
  specialize homogeneous_mem_or_mem ⟨max₁, submodule.coe_mem _⟩ ⟨max₂, submodule.coe_mem _⟩ mem_I,
  cases homogeneous_mem_or_mem;
  simp only [ne.def, dfinsupp.mem_support_to_fun, finset.mem_filter] at mem_max₁ mem_max₂,
  exact mem_max₁.2 homogeneous_mem_or_mem,
  exact mem_max₂.2 homogeneous_mem_or_mem,
end⟩

lemma homogeneous_ideal.is_prime_iff (I : homogeneous_ideal 𝒜) :
  I.1.is_prime ↔
  (I ≠ ⊤) ∧
    ∀ {x y : A}, set_like.is_homogeneous 𝒜 x → set_like.is_homogeneous 𝒜 y
      → (x * y ∈ I.1 → x ∈ I.1 ∨ y ∈ I.1) :=
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

lemma homogeneous_ideal.rad_eq (I : homogeneous_ideal 𝒜) :
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
    specialize hx (ideal.homogeneous_core 𝒜 J) _,
    refine ⟨_, (ideal.homogeneous_core 𝒜 _).prop, HJ₂.homogeneous_core⟩,
    { refine eq.trans_le _ (ideal.homogeneous_core_mono _ HJ₁),
      have HI := I.prop,
      rw [ideal.is_homogeneous.iff_eq] at HI,
      rw HI },
    refine (ideal.coe_homogeneous_core_le 𝒜 J) hx, },
end

lemma ideal.is_homogeneous_ideal.radical {I : ideal A} (h : I.is_homogeneous 𝒜)  :
  I.radical.is_homogeneous 𝒜 :=
begin
  have radI_eq : I.radical = _ := homogeneous_ideal.rad_eq ⟨I, h⟩,
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

end linear_ordered_cancel_add_comm_monoid

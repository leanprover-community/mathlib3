/-
Copyright (c) 2021 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser
-/

import algebra.direct_sum.ring
import ring_theory.ideal.basic
import ring_theory.ideal.operations
import linear_algebra.finsupp
import ring_theory.graded_ring.basic

/-!

# Homogeneous ideal of a graded commutative ring

This file defines properties of ideals of graded commutative ring `⨁ i, A i`

-/

noncomputable theory

open_locale direct_sum classical big_operators
open set direct_sum

variables (R : Type*) [ring R] {ι : Type*} [add_comm_monoid ι]
  (A : ι → add_subgroup R) [graded_ring R A]

def is_homogeneous_ideal (I : ideal R) : Prop :=
  ∃ S : set (homogeneous_element R A), I = ideal.span ↑S

def is_homogeneous_ideal' (I : ideal R) : Prop :=
  I = ideal.span {x | x ∈ I ∧ is_homogeneous R A x}

def is_homogeneous_ideal'' (I : ideal R) : Prop :=
  ∀ r : R, r ∈ I → ∀ i : ι, graded_ring.proj R A i r ∈ I

lemma is_homogeneous_ideal_iff_is_homogeneous_ideal' (I : ideal R) :
  is_homogeneous_ideal R A I ↔ is_homogeneous_ideal' R A I :=
⟨λ hI, begin
  obtain ⟨S, hS⟩ := hI,
  rw [is_homogeneous_ideal'], ext r, split; intro hr,
  { rw hS at hr,
    suffices : ↑S ⊆ {x | x ∈ I ∧ is_homogeneous R A x},
    exact (ideal.span_mono this) hr,
    intros s hs, split, rw hS,
    refine ideal.subset_span hs,
    obtain ⟨⟨s', homs'⟩, hs₁, hs₂⟩ := hs,
    convert homs', rw ←hs₂, refl },
  { obtain ⟨l, hl⟩ := (finsupp.mem_span_iff_total R _ _).mp hr,
    rw ←hl, apply ideal.sum_mem, rintros ⟨x, hx₁, hx₂⟩ hx₃,
    simp only [linear_map.id_coe, id.def, finsupp.mem_support_iff, linear_map.coe_smul_right,
      ne.def, smul_eq_mul, subtype.coe_mk] at hx₁ hx₂ hx₃ ⊢,
    exact ideal.mul_mem_left _ _ hx₁, }
end, λ hI, begin
  rw is_homogeneous_ideal' at hI,
  rw is_homogeneous_ideal,
  use {x : homogeneous_element R A | ↑x ∈ I},
  rw hI, congr, ext r, split; intros hr,
  { rcases hr with ⟨r_mem, ⟨i, r_eq⟩⟩,
    use r, exact ⟨i, r_eq⟩, refine ⟨_, rfl⟩,
    simp only [mem_set_of_eq, subtype.coe_mk], convert ←r_mem, },
  { rcases hr with ⟨⟨r', hr'⟩, hr₁, hr₂⟩,
    simp only [mem_set_of_eq, subtype.coe_mk] at hr₁,
    rw ←hr₂, rw ←hI at hr₁, refine ⟨hr₁, hr'⟩, }
end⟩

lemma is_homogeneous_ideal.mem_iff (I : ideal R) (hI : is_homogeneous_ideal R A I) (r : R) :
  r ∈ I ↔ ∀ i : ι, graded_ring.proj R A i r ∈ I :=
⟨λ hr i, begin
  have hI' := hI,
  rw [is_homogeneous_ideal_iff_is_homogeneous_ideal', is_homogeneous_ideal', ideal.span,
    finsupp.span_eq_range_total] at hI', rw hI' at hr,
  obtain ⟨s, rfl⟩ := hr,
  rw [finsupp.total_apply, finsupp.sum, add_monoid_hom.map_sum],
  apply ideal.sum_mem, rintros ⟨a, ha₁, ⟨j, ha₂⟩⟩ ha₃,
  rw [smul_eq_mul, graded_ring.mul_proj R A _ _ i],
  apply ideal.sum_mem, rintros ⟨j, k⟩ hjk,
  apply ideal.mul_mem_left,
  simp only [subtype.coe_mk],

  sorry
end, λ hr, begin
  rw graded_ring.as_sum R A r,
  apply ideal.sum_mem, intros c _, apply hr,
end⟩

-- section defs

-- variables [Π i, add_comm_monoid (A i)]

-- /-- An element `x : ⨁ i, A i` is a homogeneous element if it is a member of one of the summand. -/
-- def is_homogeneous_element (x : ⨁ i, A i) : Prop := ∃ (y : graded_monoid A), of A y.fst y.snd = x

-- variables [add_comm_monoid ι] [gcomm_semiring A]
-- /-- this might be useful, but I don't know where to put it -/
-- @[simps]
-- def graded_monoid.to_direct_sum :
--   (graded_monoid A) →* (⨁ i, A i) :=
-- { to_fun := λ a, of A a.fst a.snd,
--   map_one' := rfl,
--   map_mul' := λ x y, (of_mul_of _ _).symm, }


-- private lemma homogeneous_ideal.mul_homogeneous_element
--   {I : ideal (⨁ i, A i)} (HI : homogeneous_ideal I) (r x : ⨁ i, A i)
--   (hx₁ : is_homogeneous_element x) (hx₂ : x ∈ I) (j : ι) :
--   of A j ((r * x) j) ∈ I :=
-- begin
--   rw [direct_sum.eq_sum_of _ r, finset.sum_mul, dfinsupp.finset_sum_apply, add_monoid_hom.map_sum],
--   apply ideal.sum_mem,
--   intros k hk,
--   obtain ⟨⟨i, z⟩, rfl⟩ := hx₁,
--   rw of_mul_of,
--   dsimp only,
--   by_cases k + i = j,
--   { subst h,
--     rw [of_eq_same, ←of_mul_of],
--     apply I.mul_mem_left _ hx₂, },
--   { rw [of_eq_of_ne _ _ _ _ h, add_monoid_hom.map_zero],
--     exact I.zero_mem }
-- end


-- private lemma homogeneous_ideal.homogeneous_component
--   {I : ideal (⨁ i, A i)} (HI : homogeneous_ideal I) (x : ⨁ i, A i) (hx : x ∈ I) (i : ι) :
--   of A i (x i) ∈ I :=
-- begin
--   have HI' := HI,
--   rw [homogeneous_ideal_iff_homogeneous_ideal', homogeneous_ideal', ideal.span,
--       finsupp.span_eq_range_total] at HI',
--   rw HI' at hx,
--   obtain ⟨s, rfl⟩ := hx,
--   rw [finsupp.total_apply, finsupp.sum, dfinsupp.finset_sum_apply, add_monoid_hom.map_sum],
--   apply ideal.sum_mem,
--   rintros ⟨-, y_mem_I, z, rfl⟩ hy,
--   simp only [algebra.id.smul_eq_mul, subtype.coe_mk],
--   apply homogeneous_ideal.mul_homogeneous_element HI,
--   use z, exact y_mem_I,
-- end


-- lemma homogeneous_ideal.mem_iff
--   (I : ideal (⨁ i, A i)) (HI : homogeneous_ideal I) (x : ⨁ i, A i) :
--   x ∈ I ↔ ∀ (i : ι), of A i (x i) ∈ I :=
-- ⟨λ hx j, begin
--   have HI' := HI,
--   rw [homogeneous_ideal_iff_homogeneous_ideal', homogeneous_ideal', ideal.span,
--       finsupp.span_eq_range_total] at HI',
--   rw HI' at hx,
--   obtain ⟨s, rfl⟩ := hx,
--   rw [finsupp.total_apply, finsupp.sum, dfinsupp.finset_sum_apply, add_monoid_hom.map_sum],
--   apply ideal.sum_mem,
--   rintros ⟨-, y_mem_I, z, rfl⟩ hy,
--   exact homogeneous_ideal.mul_homogeneous_element HI _ _ ⟨z, rfl⟩ y_mem_I _,
-- end, begin
--   intro H, rw [direct_sum.eq_sum_of _ x], apply ideal.sum_mem, intros j hj,
--   apply H,
-- end⟩

-- /--Another definition of homogeneous ideal-/
-- def homogeneous_ideal'' (I : ideal (⨁ i, A i)) : Prop :=
--   ∀ (x : ⨁ i, A i), x ∈ I → ∀ (i : ι), of A i (x i) ∈ I

-- lemma homogeneous_ideal_iff_homogeneous_ideal''
--   (I : ideal (⨁ i, A i)) :
--   homogeneous_ideal I ↔ homogeneous_ideal'' I :=
-- ⟨λ HI, begin
--   intros x hx i,
--   apply homogeneous_ideal.homogeneous_component HI x hx,
-- end, λ HI, begin
--   rw [homogeneous_ideal_iff_homogeneous_ideal', homogeneous_ideal'],
--   ext, split; intro hx,
--   { rw direct_sum.eq_sum_of _ x,
--     refine ideal.sum_mem _ _,
--     intros j hj, specialize HI x hx j,
--     rw ideal.mem_span, intros J HJ,
--     refine HJ _,
--     simp only [mem_set_of_eq],
--     refine ⟨HI, _⟩, use ⟨j, x j⟩, },
--   { rw [ideal.mem_span] at hx,
--     apply hx,
--     intros y hy,
--     exact hy.1,  }
-- end⟩

-- lemma homogeneous_ideal.equivalent (I : ideal (⨁ i, A i)) :
--   tfae [homogeneous_ideal I, homogeneous_ideal' I, homogeneous_ideal'' I] :=
-- begin
--   tfae_have : 1↔2, exact homogeneous_ideal_iff_homogeneous_ideal' I,
--   tfae_have : 1↔3, exact homogeneous_ideal_iff_homogeneous_ideal'' I,
--   tfae_finish,
-- end

-- /-- Given any ideal `I : ideal (⨁ i, A i)`, there is a homogeneous ideal generated by
-- the homogeneous elements of `I`-/
-- def homogeneous_ideal_of_ideal (I : ideal (⨁ i, A i)) :
--   ideal (⨁ i, A i) := ideal.span (set_of is_homogeneous_element ∩ I)

-- lemma homogeneous_ideal_of_ideal_le_ideal
--   (I : ideal (⨁ i, A i)) :
--   homogeneous_ideal_of_ideal I ≤ I :=
-- begin
--   rw homogeneous_ideal_of_ideal,
--   conv_rhs { rw ←ideal.span_eq I },
--   apply ideal.span_mono, exact (set_of is_homogeneous_element).inter_subset_right ↑I,
-- end

-- lemma homogeneous_ideal.homogeneous_ideal_of_ideal
--   (I : ideal (⨁ i, A i)) :
--   homogeneous_ideal (homogeneous_ideal_of_ideal I) :=
-- begin
--   use set.preimage graded_monoid.to_direct_sum (set_of is_homogeneous_element ∩ I.carrier),
--   rw homogeneous_ideal_of_ideal, congr,
--   have set_eq : set_of is_homogeneous_element ∩ ↑I =
--     graded_monoid.to_direct_sum '' (graded_monoid.to_direct_sum ⁻¹'
--       (set_of is_homogeneous_element ∩ I.carrier)),
--   { ext, split,
--     { intros hx,
--       obtain ⟨⟨z, hz⟩, hx₂⟩ := hx,
--       simp only [mem_image, mem_inter_eq, graded_monoid.to_direct_sum_apply,
--         mem_set_of_eq, mem_preimage, set_like.mem_coe, submodule.mem_carrier],
--         use z, refine ⟨⟨_, _,⟩, hz⟩,
--         use z, rw hz, exact hx₂},
--     { intros hx,
--       simp only [mem_image, mem_inter_eq, graded_monoid.to_direct_sum_apply,
--         mem_set_of_eq, mem_preimage, set_like.mem_coe, submodule.mem_carrier] at hx,
--         obtain ⟨z, ⟨⟨h₁, h₂⟩, h₃⟩⟩ := hx, split,
--         use z, exact h₃, rw ←h₃, exact h₂ } },
--   rw set_eq,
-- end

-- end defs

-- section properties

-- variables [Π i, add_comm_group (A i)]

-- lemma homogeneous_ideal.is_prime_iff [linear_ordered_cancel_add_comm_monoid ι] [gcomm_semiring A]
--   (I : ideal (⨁ i, A i)) (HI : homogeneous_ideal I) (I_ne_top : I ≠ ⊤)
--   (homogeneous_mem_or_mem : ∀ {x y : ⨁ i, A i}, is_homogeneous_element x → is_homogeneous_element y
--     → (x * y ∈ I → x ∈ I ∨ y ∈ I)) : ideal.is_prime I :=
-- ⟨I_ne_top, begin
--   intros x y hxy, by_contradiction rid,
--   obtain ⟨rid₁, rid₂⟩ := not_or_distrib.mp rid,
--   set set₁ := x.support.filter (λ i, of A i (x i) ∉ I) with set₁_eq,
--   set set₂ := y.support.filter (λ i, of A i (y i) ∉ I) with set₂_eq,
--   have set₁_nonempty : set₁.nonempty,
--   { rw [homogeneous_ideal.mem_iff _ HI, not_forall] at rid₁,
--     obtain ⟨i, h⟩ := rid₁,
--     refine ⟨i, _⟩, rw set₁_eq, simp only [ne.def, dfinsupp.mem_support_to_fun, finset.mem_filter],
--     refine ⟨_, h⟩, intro rid₃, rw rid₃ at h,
--     simp only [not_true, submodule.zero_mem, add_monoid_hom.map_zero] at h, exact h, },
--   have set₂_nonempty : set₂.nonempty,
--   { rw [homogeneous_ideal.mem_iff _ HI, not_forall] at rid₂,
--     obtain ⟨i, h⟩ := rid₂,
--     refine ⟨i, _⟩, rw set₂_eq, simp only [ne.def, dfinsupp.mem_support_to_fun, finset.mem_filter],
--     refine ⟨_, h⟩, intro rid₃, rw rid₃ at h,
--     simp only [not_true, submodule.zero_mem, add_monoid_hom.map_zero] at h, exact h, },
--   set max₁ := set₁.max' set₁_nonempty with max₁_eq,
--   set max₂ := set₂.max' set₂_nonempty with max₂_eq,
--   have mem_max₁ := finset.max'_mem set₁ set₁_nonempty,
--   rw [←max₁_eq, set₁_eq] at mem_max₁,
--   have mem_max₂ := finset.max'_mem set₂ set₂_nonempty,
--   rw [←max₂_eq, set₂_eq] at mem_max₂,
--   rw homogeneous_ideal.mem_iff _ HI at hxy,
--   specialize hxy (max₁ + max₂),
--   have eq :=
--     calc  of A (max₁ + max₂) ((x * y) (max₁ + max₂))
--         = ∑ ij in (x.support.product y.support).filter (λ z, prod.fst z + prod.snd z = max₁ + max₂),
--             of A (prod.fst ij + prod.snd ij)
--               (graded_monoid.ghas_mul.mul (x (prod.fst ij)) (y (prod.snd ij))) : _ -- (1)
--     ... = ∑ ij in ((x.support.product y.support).filter (λ z, z.fst + z.snd = max₁ + max₂))
--                     \ {(max₁, max₂)} ∪ {(max₁, max₂)},
--             of A (prod.fst ij + prod.snd ij)
--               (graded_monoid.ghas_mul.mul (x (prod.fst ij)) (y (prod.snd ij)))
--         : _ -- (2)
--     ... = ∑ ij in (x.support.product y.support).filter (λ z, prod.fst z + prod.snd z = max₁ + max₂)
--                     \ {(max₁, max₂)},
--             of A (prod.fst ij + prod.snd ij)
--               (graded_monoid.ghas_mul.mul (x (prod.fst ij)) (y (prod.snd ij)))
--         + ∑ ij in {(max₁, max₂)},
--             of A (prod.fst ij + prod.snd ij)
--               (graded_monoid.ghas_mul.mul (x (prod.fst ij)) (y (prod.snd ij))) : _ -- (3)
--     ... = ∑ ij in (x.support.product y.support).filter (λ z, prod.fst z + prod.snd z = max₁ + max₂)
--                     \ {(max₁, max₂)},
--             of A (prod.fst ij + prod.snd ij)
--               (graded_monoid.ghas_mul.mul (x (prod.fst ij)) (y (prod.snd ij)))
--         + of A (max₁ + max₂) (graded_monoid.ghas_mul.mul (x max₁) (y max₂))
--         : by rw finset.sum_singleton,

--   have eq₂ : of A (max₁ + max₂) (graded_monoid.ghas_mul.mul (x max₁) (y max₂))
--           = of A (max₁ + max₂) ((x * y) (max₁ + max₂))
--           - ∑ ij in (x.support.product y.support).filter
--               (λ z, prod.fst z + prod.snd z = max₁ + max₂) \ {(max₁, max₂)},
--             of A (prod.fst ij + prod.snd ij)
--               (graded_monoid.ghas_mul.mul (x (prod.fst ij)) (y (prod.snd ij))),
--   { rw eq, ring },

--   have mem_I₂ : ∑ ij in (x.support.product y.support).filter
--                     (λ z, prod.fst z + prod.snd z = max₁ + max₂) \ {(max₁, max₂)},
--                   of A (prod.fst ij + prod.snd ij)
--                   (graded_monoid.ghas_mul.mul (x (prod.fst ij)) (y (prod.snd ij))) ∈ I,
--   { apply ideal.sum_mem, rintros ⟨i, j⟩ H,
--     simp only [not_and, prod.mk.inj_iff, finset.mem_sdiff, ne.def, dfinsupp.mem_support_to_fun,
--        finset.mem_singleton, finset.mem_filter, finset.mem_product] at H,
--     rw ←of_mul_of,
--     obtain ⟨⟨⟨H₁, H₂⟩, H₃⟩, H₄⟩ := H,
--     cases lt_trichotomy i max₁,
--     { -- in this case `i < max₁`, so `max₂ < j`, so `of A j (y j) ∈ I`
--       have ineq : max₂ < j,
--       { by_contra rid₂, rw not_lt at rid₂,
--         have rid₃ := add_lt_add_of_le_of_lt rid₂ h,
--         conv_lhs at rid₃ { rw add_comm },
--         conv_rhs at rid₃ { rw add_comm },
--         rw H₃ at rid₃, exact lt_irrefl _ rid₃, },
--       have not_mem_j : j ∉ set₂,
--       { intro rid₂,
--         rw max₂_eq at ineq,
--         have rid₃ := (finset.max'_lt_iff set₂ set₂_nonempty).mp ineq j rid₂,
--         exact lt_irrefl _ rid₃, },
--       rw set₂_eq at not_mem_j,
--       simp only [not_and, not_not, ne.def, dfinsupp.mem_support_to_fun,
--         finset.mem_filter] at not_mem_j,
--       specialize not_mem_j H₂,
--       apply ideal.mul_mem_left,
--       convert not_mem_j, },
--     { cases h,
--       { -- in this case `i = max₁`, so `max₂ = j`, contradictory
--         have : j = max₂,
--         { rw h at H₃,
--           exact linear_ordered_cancel_add_comm_monoid.add_left_cancel _ _ _ H₃, },
--         exfalso,
--         exact H₄ h this, },
--       { -- in this case `i > max₁`, so `i < max₁`, so `of A i (x i) ∈ I`
--         have ineq : max₁ < i,
--         { by_contra rid₂, rw not_lt at rid₂,
--           have rid₃ := add_lt_add_of_le_of_lt rid₂ h,
--           conv_lhs at rid₃ { rw add_comm }, exact lt_irrefl _ rid₃, },
--         have not_mem_i : i ∉ set₁,
--         { intro rid₂,
--           rw max₁_eq at ineq,
--           have rid₃ := (finset.max'_lt_iff set₁ set₁_nonempty).mp ineq i rid₂,
--           exact lt_irrefl _ rid₃,},
--         rw set₁_eq at not_mem_i,
--         simp only [not_and, not_not, ne.def, dfinsupp.mem_support_to_fun,
--           finset.mem_filter] at not_mem_i,
--         specialize not_mem_i H₁,
--         apply ideal.mul_mem_right,
--         convert not_mem_i, }, } },
--   have mem_I₃ : of A (max₁ + max₂) (graded_monoid.ghas_mul.mul (x max₁) (y max₂)) ∈ I,
--   { rw eq₂, apply ideal.sub_mem,
--     rw [homogeneous_ideal_iff_homogeneous_ideal'', homogeneous_ideal''] at HI,
--     specialize HI _ hxy (max₁ + max₂), exact hxy, exact mem_I₂, },
--   rw ←of_mul_of at mem_I₃,
--   specialize homogeneous_mem_or_mem ⟨⟨max₁, x max₁⟩, rfl⟩ ⟨⟨max₂, y max₂⟩, rfl⟩ mem_I₃,
--   cases homogeneous_mem_or_mem,
--   simp only [ne.def, dfinsupp.mem_support_to_fun, finset.mem_filter] at mem_max₁,
--   refine mem_max₁.2 homogeneous_mem_or_mem,
--   simp only [ne.def, dfinsupp.mem_support_to_fun, finset.mem_filter] at mem_max₂,
--   refine mem_max₂.2 homogeneous_mem_or_mem,

--   -- equalities from calc
--   -- (1)
--   conv_lhs { rw [direct_sum.eq_sum_of _ x, direct_sum.eq_sum_of _ y, finset.sum_mul_sum] },
--   simp only [dfinsupp.finset_sum_apply],
--   rw [add_monoid_hom.map_sum],
--   simp_rw [of_mul_of],
--   rw calc
--         ∑ (ij : ι × ι) in x.support.product y.support,
--           (of A (max₁ + max₂)) (of A (ij.fst + ij.snd)
--             (graded_monoid.ghas_mul.mul (x ij.fst) (y ij.snd))
--             (max₁ + max₂))
--       = ∑ (ij : ι × ι) in (x.support.product y.support).filter (λ z, z.fst + z.snd = max₁ + max₂),
--           (of A (max₁ + max₂)) ((of A (ij.fst + ij.snd))
--             (graded_monoid.ghas_mul.mul (x ij.fst) (y ij.snd))
--             (max₁ + max₂))
--       + ∑ (ij : ι × ι) in (x.support.product y.support).filter (λ z, z.fst + z.snd ≠ max₁ + max₂),
--           (of A (max₁ + max₂)) ((of A (ij.fst + ij.snd))
--             (graded_monoid.ghas_mul.mul (x ij.fst) (y ij.snd))
--             (max₁ + max₂)) : by rw finset.sum_filter_add_sum_filter_not
--   ... = ∑ (ij : ι × ι) in (x.support.product y.support).filter (λ z, z.fst + z.snd = max₁ + max₂),
--           (of A (max₁ + max₂)) ((of A (ij.fst + ij.snd))
--             (graded_monoid.ghas_mul.mul (x ij.fst) (y ij.snd))
--             (max₁ + max₂)) : _, -- (1.1)
--   apply finset.sum_congr, refl,
--   rintros ⟨i, j⟩ hij,
--   simp only [ne.def, dfinsupp.mem_support_to_fun, finset.mem_filter, finset.mem_product] at hij,
--   rw [←hij.2, of_eq_same],
--   -- (1.1)
--   have eq :
--     ∑ (ij : ι × ι) in (x.support.product y.support).filter (λ z, z.fst + z.snd ≠ max₁ + max₂),
--         (of A (max₁ + max₂)) ((of A (ij.fst + ij.snd))
--           (graded_monoid.ghas_mul.mul (x ij.fst) (y ij.snd))
--           (max₁ + max₂)) = 0,
--   { apply finset.sum_eq_zero,
--     rintros ⟨i, j⟩ hij,
--     simp only [ne.def, dfinsupp.mem_support_to_fun, finset.mem_filter, finset.mem_product] at hij,
--     rw of_eq_of_ne, simp only [add_monoid_hom.map_zero],
--     exact hij.2, },
--   rw [eq, add_zero],

--   -- (2)
--   congr, ext, split; intros H,
--   { simp only [finset.mem_filter, ne.def, dfinsupp.mem_support_to_fun, finset.mem_product] at H,
--     rw finset.mem_union,
--     by_cases a = (max₁, max₂),
--     right, rw h, exact finset.mem_singleton_self (max₁, max₂),
--     left, rw finset.mem_sdiff, split,
--     simp only [finset.mem_filter, ne.def, dfinsupp.mem_support_to_fun, finset.mem_product],
--     exact H, intro rid, simp only [finset.mem_singleton] at rid, exact h rid, },
--   { rw finset.mem_union at H, cases H,
--     rw finset.mem_sdiff at H, exact H.1,
--     simp only [finset.mem_filter, ne.def, dfinsupp.mem_support_to_fun, finset.mem_product],
--     simp only [finset.mem_singleton] at H, rw H,
--     refine ⟨⟨_, _⟩, rfl⟩,
--     simp only [ne.def, dfinsupp.mem_support_to_fun, finset.mem_filter] at mem_max₁,
--     exact mem_max₁.1,
--     simp only [ne.def, dfinsupp.mem_support_to_fun, finset.mem_filter] at mem_max₂,
--     exact mem_max₂.1, },

--   -- (3)
--   rw [finset.sum_union],
--   apply finset.disjoint_iff_inter_eq_empty.mpr,
--   rw finset.eq_empty_iff_forall_not_mem, rintros ⟨i, j⟩ Hij,
--   rw [finset.mem_inter, finset.mem_sdiff, finset.mem_filter] at Hij,
--   simp only [not_and, prod.mk.inj_iff, ne.def, dfinsupp.mem_support_to_fun, finset.mem_singleton,
--     finset.mem_product] at Hij,
--   exact Hij.1.2 Hij.2.1 Hij.2.2,
-- end⟩

-- end properties

-- section operations

-- open_locale pointwise

-- variables [Π i, add_comm_monoid (A i)] [add_comm_monoid ι] [gcomm_semiring A]

-- lemma homogeneous_ideal.mul {I J : ideal (⨁ i, A i)}
--   (HI : homogeneous_ideal I) (HJ : homogeneous_ideal J):
--   homogeneous_ideal (I * J) :=
-- begin
--   obtain ⟨si, rfl⟩ := HI,
--   obtain ⟨sj, rfl⟩ := HJ,
--   refine ⟨si * sj, _⟩,
--   rw ideal.span_mul_span',
--   exact congr_arg _ (image_mul graded_monoid.to_direct_sum.to_mul_hom).symm,
-- end

-- lemma homogeneous_ideal.sup {I J : ideal (⨁ i, A i)}
--   (HI : homogeneous_ideal I) (HJ : homogeneous_ideal J):
--   homogeneous_ideal (I ⊔ J) :=
-- begin
--   obtain ⟨si, rfl⟩ := HI,
--   obtain ⟨sj, rfl⟩ := HJ,
--   refine ⟨si ∪ sj, _⟩,
--   rw image_union,
--   exact (submodule.span_union _ _).symm,
-- end

-- private lemma homogeneous_ideal.inf_subset
--   {I J : ideal (⨁ i, A i)} (HI : homogeneous_ideal I) (HJ : homogeneous_ideal J) :
--   I ⊓ J ≤ ideal.span {x | x ∈ I ⊓ J ∧ is_homogeneous_element x} :=
-- begin
--   rintro x ⟨hxi, hxj⟩,
--   have hx : ∀ i, of A i (x i) ∈ I ⊓ J,
--   { intro j, split; refine (homogeneous_ideal.mem_iff _ _ x).mp _ _; assumption },

--   rw [direct_sum.eq_sum_of _ x],
--   refine ideal.sum_mem _ _,
--   intros i hi, refine ideal.subset_span _, refine ⟨hx _, _⟩, use ⟨i, x i⟩,
-- end

-- private lemma homogeneous_ideal.subset_inf
--   {I J : ideal (⨁ i, A i)} (HI : homogeneous_ideal I) (HJ : homogeneous_ideal J) :
--   ideal.span {x | x ∈ I ⊓ J ∧ is_homogeneous_element x} ≤ I ⊓ J :=
-- begin
--   intros x hx,
--   { split,
--     { simp only [set_like.mem_coe],
--       rw [homogeneous_ideal_iff_homogeneous_ideal', homogeneous_ideal'] at HI,
--       rw [HI, ideal.mem_span], intros K HK,
--       replace HK := ideal.span_mono HK,
--       rw [ideal.span_eq] at HK,
--       have eq₁ : ideal.span {x | x ∈ I ⊓ J ∧ is_homogeneous_element x}
--         ≤ ideal.span {x | x ∈ I ∧ is_homogeneous_element x},
--       { apply ideal.span_mono, rintros y ⟨⟨hy₁, _⟩, hy₂⟩, refine ⟨hy₁, hy₂⟩, },
--       refine HK _, refine eq₁ hx, },
--     { simp only [set_like.mem_coe],
--       rw [homogeneous_ideal_iff_homogeneous_ideal', homogeneous_ideal'] at HJ,
--       rw [HJ, ideal.mem_span], intros K HK,
--       replace HK := ideal.span_mono HK,
--       rw [ideal.span_eq] at HK,
--       have eq₁ : ideal.span {x | x ∈ I ⊓ J ∧ is_homogeneous_element x}
--         ≤ ideal.span {x | x ∈ J ∧ is_homogeneous_element x},
--       { apply ideal.span_mono, rintros y ⟨⟨_, hy₁⟩, hy₂⟩, refine ⟨hy₁, hy₂⟩, },
--       refine HK _, refine eq₁ hx, },
--   },
-- end

-- lemma homogeneous_ideal.inf
--   {I J : ideal (⨁ i, A i)} (HI : homogeneous_ideal I) (HJ : homogeneous_ideal J) :
--   homogeneous_ideal (I ⊓ J) :=
-- begin
--   rw [homogeneous_ideal_iff_homogeneous_ideal', homogeneous_ideal'],
--   exact le_antisymm (homogeneous_ideal.inf_subset HI HJ) (homogeneous_ideal.subset_inf HI HJ),
-- end

-- lemma homogeneous_ideal.Inf {ℐ : set (ideal (⨁ i, A i))}
--   (HI : ∀ I ∈ ℐ, homogeneous_ideal I) :
--   homogeneous_ideal (Inf ℐ) :=
-- begin
--   rw homogeneous_ideal_iff_homogeneous_ideal'',
--   intros x Hx i, simp only [submodule.mem_Inf] at Hx ⊢,
--   intros J HJ, specialize HI J HJ, rw homogeneous_ideal_iff_homogeneous_ideal'' at HI,
--   apply HI, apply Hx, exact HJ
-- end

-- end operations


-- section

-- variables [Π i, add_comm_group (A i)] [linear_ordered_cancel_add_comm_monoid ι] [gcomm_semiring A]

-- lemma homogeneous_ideal.rad_eq {I : ideal (⨁ i, A i)} (HI : homogeneous_ideal I) :
--   I.radical = Inf {J | I ≤ J ∧ homogeneous_ideal J ∧ J.is_prime} :=
-- begin
--   have subset₁ : I.radical ≤ Inf {J | I ≤ J ∧ homogeneous_ideal J ∧ J.is_prime},
--   { rw ideal.radical_eq_Inf, intros x hx,
--     rw [submodule.mem_Inf] at hx ⊢, intros J HJ, apply hx,
--     obtain ⟨HJ₁, _, HJ₂⟩ := HJ,
--     refine ⟨HJ₁, HJ₂⟩, },
--   have subset₂ : Inf {J | I ≤ J ∧ homogeneous_ideal J ∧ J.is_prime} ≤ I.radical,
--   { intros x hx,
--     rw ideal.radical_eq_Inf,
--     rw [submodule.mem_Inf] at hx ⊢,
--     intros J HJ,
--     specialize hx (homogeneous_ideal_of_ideal J) _,
--     obtain ⟨HJ₁, HJ₂⟩ := HJ,
--     refine ⟨_, homogeneous_ideal.homogeneous_ideal_of_ideal _, _⟩,
--     { rw [homogeneous_ideal_iff_homogeneous_ideal', homogeneous_ideal'] at HI,
--       rw HI, apply ideal.span_mono, intros y hy,
--       obtain ⟨hy₁, ⟨z, hz⟩⟩ := hy,
--       specialize HJ₁ hy₁, refine ⟨⟨z, hz⟩, HJ₁⟩, },
--     { set J' := homogeneous_ideal_of_ideal J with eq_J',
--       have homogeneity₀ : homogeneous_ideal J' := homogeneous_ideal.homogeneous_ideal_of_ideal J,
--       apply homogeneous_ideal.is_prime_iff J' homogeneity₀,
--       intro rid,
--       have rid' : J = ⊤,
--       { have : J' ≤ J := homogeneous_ideal_of_ideal_le_ideal J,
--         rw rid at this, rw top_le_iff at this, exact this, },
--       apply HJ₂.1, exact rid',
--       rintros x y hx hy hxy,
--       have H := HJ₂.mem_or_mem (homogeneous_ideal_of_ideal_le_ideal J hxy),
--       cases H,
--       { left, rw homogeneous_ideal.mem_iff, intros j,
--         obtain ⟨⟨i, z⟩, rfl⟩ := hx,
--         by_cases i = j,
--         { rw [←h, direct_sum.of_eq_same, eq_J', homogeneous_ideal_of_ideal],
--           refine ideal.subset_span ⟨⟨⟨i,z⟩,rfl⟩, H⟩, },
--         { rw direct_sum.of_eq_of_ne _ _ _ _ h,
--           simp only [submodule.zero_mem, add_monoid_hom.map_zero], },
--           exact homogeneous_ideal.homogeneous_ideal_of_ideal _, },
--       { right, rw homogeneous_ideal.mem_iff, intros j,
--         obtain ⟨⟨i, z⟩, rfl⟩ := hy,
--         by_cases i = j,
--         { rw [←h, direct_sum.of_eq_same, eq_J', homogeneous_ideal_of_ideal],
--           refine ideal.subset_span ⟨⟨⟨i,z⟩,rfl⟩, H⟩, },
--         { rw direct_sum.of_eq_of_ne _ _ _ _ h,
--           simp only [submodule.zero_mem, add_monoid_hom.map_zero], },
--           exact homogeneous_ideal.homogeneous_ideal_of_ideal _, }, },
--       refine (homogeneous_ideal_of_ideal_le_ideal J) hx, },

--   ext x, split; intro hx,
--   exact subset₁ hx, exact subset₂ hx,
-- end

-- lemma homogeneous_ideal.rad
--   {I : ideal (⨁ i, A i)} (HI : homogeneous_ideal I) : homogeneous_ideal I.radical :=
-- begin
--   have radI_eq := homogeneous_ideal.rad_eq HI,
--   rw radI_eq, apply homogeneous_ideal.Inf,
--   rintros J ⟨_, HJ, _⟩, exact HJ,
-- end

-- end

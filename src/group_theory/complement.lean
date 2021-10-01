/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import group_theory.group_action
import group_theory.order_of_element
import group_theory.quotient_group

/-!
# Complements

In this file we define the complement of a subgroup.

## Main definitions

- `is_complement S T` where `S` and `T` are subsets of `G` states that every `g : G` can be
  written uniquely as a product `s * t` for `s ∈ S`, `t ∈ T`.
- `left_transversals T` where `T` is a subset of `G` is the set of all left-complements of `T`,
  i.e. the set of all `S : set G` that contain exactly one element of each left coset of `T`.
- `right_transversals S` where `S` is a subset of `G` is the set of all right-complements of `S`,
  i.e. the set of all `T : set G` that contain exactly one element of each right coset of `S`.

## Main results

- `is_complement_of_coprime` : Subgroups of coprime order are complements.
-/

open_locale big_operators

namespace subgroup

variables {G : Type*} [group G] (H K : subgroup G) (S T : set G)

/-- `S` and `T` are complements if `(*) : S × T → G` is a bijection.
  This notion generalizes left transversals, right transversals, and complementary subgroups. -/
@[to_additive "`S` and `T` are complements if `(*) : S × T → G` is a bijection"]
def is_complement : Prop := function.bijective (λ x : S × T, x.1.1 * x.2.1)

/-- The set of left-complements of `T : set G` -/
@[to_additive "The set of left-complements of `T : set G`"]
def left_transversals : set (set G) := {S : set G | is_complement S T}

/-- The set of right-complements of `S : set G` -/
@[to_additive "The set of right-complements of `S : set G`"]
def right_transversals : set (set G) := {T : set G | is_complement S T}

variables {H K S T}

@[to_additive] lemma is_complement_iff_exists_unique :
  is_complement S T ↔ ∀ g : G, ∃! x : S × T, x.1.1 * x.2.1 = g :=
function.bijective_iff_exists_unique _

@[to_additive] lemma is_complement.exists_unique (h : is_complement S T) (g : G) :
  ∃! x : S × T, x.1.1 * x.2.1 = g :=
is_complement_iff_exists_unique.mp h g

@[to_additive] lemma is_complement.symm (h : is_complement (H : set G) (K : set G)) :
  is_complement (K : set G) (H : set G) :=
begin
  let ϕ : H × K ≃ K × H := equiv.mk (λ x, ⟨x.2⁻¹, x.1⁻¹⟩) (λ x, ⟨x.2⁻¹, x.1⁻¹⟩)
    (λ x, prod.ext (inv_inv _) (inv_inv _)) (λ x, prod.ext (inv_inv _) (inv_inv _)),
  let ψ : G ≃ G := equiv.mk (λ g : G, g⁻¹) (λ g : G, g⁻¹) inv_inv inv_inv,
  suffices : ψ ∘ (λ x : H × K, x.1.1 * x.2.1) = (λ x : K × H, x.1.1 * x.2.1) ∘ ϕ,
  { rwa [is_complement, ←equiv.bijective_comp, ←this, equiv.comp_bijective] },
  exact funext (λ x, mul_inv_rev _ _),
end

@[to_additive] lemma is_complement_comm :
  is_complement (H : set G) (K : set G) ↔ is_complement (K : set G) (H : set G) :=
⟨is_complement.symm, is_complement.symm⟩

@[to_additive] lemma is_complement_top_singleton {g : G} :
  is_complement (⊤ : set G) {g} :=
⟨λ ⟨x, _, rfl⟩ ⟨y, _, rfl⟩ h, prod.ext (subtype.ext (mul_right_cancel h)) rfl,
  λ x, ⟨⟨⟨x * g⁻¹, ⟨⟩⟩, g, rfl⟩, inv_mul_cancel_right x g⟩⟩

@[to_additive] lemma is_complement_singleton_top {g : G} :
  is_complement ({g} : set G) (⊤ : set G) :=
⟨λ ⟨⟨_, rfl⟩, x⟩ ⟨⟨_, rfl⟩, y⟩ h, prod.ext rfl (subtype.ext (mul_left_cancel h)),
  λ x, ⟨⟨⟨g, rfl⟩, g⁻¹ * x, ⟨⟩⟩, mul_inv_cancel_left g x⟩⟩

@[to_additive] lemma mem_left_transversals_iff_exists_unique_inv_mul_mem :
  S ∈ left_transversals T ↔ ∀ g : G, ∃! s : S, (s : G)⁻¹ * g ∈ T :=
begin
  rw [left_transversals, set.mem_set_of_eq, is_complement_iff_exists_unique],
  refine ⟨λ h g, _, λ h g, _⟩,
  { obtain ⟨x, h1, h2⟩ := h g,
    exact ⟨x.1, (congr_arg (∈ T) (eq_inv_mul_of_mul_eq h1)).mp x.2.2, λ y hy,
      (prod.ext_iff.mp (h2 ⟨y, y⁻¹ * g, hy⟩ (mul_inv_cancel_left y g))).1⟩ },
  { obtain ⟨x, h1, h2⟩ := h g,
    refine ⟨⟨x, x⁻¹ * g, h1⟩, mul_inv_cancel_left x g, λ y hy, _⟩,
    have := h2 y.1 ((congr_arg (∈ T) (eq_inv_mul_of_mul_eq hy)).mp y.2.2),
    exact prod.ext this (subtype.ext (eq_inv_mul_of_mul_eq ((congr_arg _ this).mp hy))) },
end

@[to_additive] lemma mem_right_transversals_iff_exists_unique_mul_inv_mem :
  S ∈ right_transversals T ↔ ∀ g : G, ∃! s : S, g * (s : G)⁻¹ ∈ T :=
begin
  rw [right_transversals, set.mem_set_of_eq, is_complement_iff_exists_unique],
  refine ⟨λ h g, _, λ h g, _⟩,
  { obtain ⟨x, h1, h2⟩ := h g,
    exact ⟨x.2, (congr_arg (∈ T) (eq_mul_inv_of_mul_eq h1)).mp x.1.2, λ y hy,
      (prod.ext_iff.mp (h2 ⟨⟨g * y⁻¹, hy⟩, y⟩ (inv_mul_cancel_right g y))).2⟩ },
  { obtain ⟨x, h1, h2⟩ := h g,
    refine ⟨⟨⟨g * x⁻¹, h1⟩, x⟩, inv_mul_cancel_right g x, λ y hy, _⟩,
    have := h2 y.2 ((congr_arg (∈ T) (eq_mul_inv_of_mul_eq hy)).mp y.1.2),
    exact prod.ext (subtype.ext (eq_mul_inv_of_mul_eq ((congr_arg _ this).mp hy))) this },
end

@[to_additive] lemma mem_left_transversals_iff_exists_unique_quotient_mk'_eq :
  S ∈ left_transversals (H : set G) ↔
  ∀ q : quotient (quotient_group.left_rel H), ∃! s : S, quotient.mk' s.1 = q :=
begin
  have key : ∀ g h, quotient.mk' g = quotient.mk' h ↔ g⁻¹ * h ∈ H :=
  @quotient.eq' G (quotient_group.left_rel H),
  simp_rw [mem_left_transversals_iff_exists_unique_inv_mul_mem, set_like.mem_coe, ←key],
  exact ⟨λ h q, quotient.induction_on' q h, λ h g, h (quotient.mk' g)⟩,
end

@[to_additive] lemma mem_right_transversals_iff_exists_unique_quotient_mk'_eq :
  S ∈ right_transversals (H : set G) ↔
  ∀ q : quotient (quotient_group.right_rel H), ∃! s : S, quotient.mk' s.1 = q :=
begin
  have key : ∀ g h, quotient.mk' g = quotient.mk' h ↔ h * g⁻¹ ∈ H :=
  @quotient.eq' G (quotient_group.right_rel H),
  simp_rw [mem_right_transversals_iff_exists_unique_mul_inv_mem, set_like.mem_coe, ←key],
  exact ⟨λ h q, quotient.induction_on' q h, λ h g, h (quotient.mk' g)⟩,
end

@[to_additive] lemma mem_left_transversals_iff_bijective : S ∈ left_transversals (H : set G) ↔
  function.bijective (S.restrict (quotient.mk' : G → quotient (quotient_group.left_rel H))) :=
mem_left_transversals_iff_exists_unique_quotient_mk'_eq.trans
  (function.bijective_iff_exists_unique (S.restrict quotient.mk')).symm

@[to_additive] lemma mem_right_transversals_iff_bijective : S ∈ right_transversals (H : set G) ↔
  function.bijective (set.restrict (quotient.mk' : G → quotient (quotient_group.right_rel H)) S) :=
mem_right_transversals_iff_exists_unique_quotient_mk'_eq.trans
  (function.bijective_iff_exists_unique (S.restrict quotient.mk')).symm

@[to_additive] instance : inhabited (left_transversals (H : set G)) :=
⟨⟨set.range quotient.out', mem_left_transversals_iff_bijective.mpr ⟨by
{ rintros ⟨_, q₁, rfl⟩ ⟨_, q₂, rfl⟩ hg,
  rw (q₁.out_eq'.symm.trans hg).trans q₂.out_eq' }, λ q, ⟨⟨q.out', q, rfl⟩, quotient.out_eq' q⟩⟩⟩⟩

@[to_additive] instance : inhabited (right_transversals (H : set G)) :=
⟨⟨set.range quotient.out', mem_right_transversals_iff_bijective.mpr ⟨by
{ rintros ⟨_, q₁, rfl⟩ ⟨_, q₂, rfl⟩ hg,
  rw (q₁.out_eq'.symm.trans hg).trans q₂.out_eq' }, λ q, ⟨⟨q.out', q, rfl⟩, quotient.out_eq' q⟩⟩⟩⟩

lemma is_complement.card_mul [fintype G] [fintype H] [fintype K]
  (h : is_complement (H : set G) (K : set G)) :
  fintype.card H * fintype.card K = fintype.card G :=
(fintype.card_prod _ _).symm.trans (fintype.card_of_bijective h)

lemma is_complement.disjoint (h : is_complement (H : set G) (K : set G)) : disjoint H K :=
λ g hg, let x : H × K := ⟨⟨g, hg.1⟩, 1⟩, y : H × K := ⟨1, ⟨g, hg.2⟩⟩ in subtype.ext_iff.mp
  (prod.ext_iff.mp (h.1 (show x.1.1 * _ = y.1.1 * _, from (mul_one g).trans (one_mul g).symm))).1

lemma is_complement_of_card_mul_and_disjoint [fintype G] [fintype H] [fintype K]
  (h1 : fintype.card H * fintype.card K = fintype.card G) (h2 : disjoint H K) :
  is_complement (H : set G) (K : set G) :=
begin
  refine (fintype.bijective_iff_injective_and_card _).mpr
    ⟨λ x y h, _, (fintype.card_prod H K).trans h1⟩,
  rw [←eq_inv_mul_iff_mul_eq, ←mul_assoc, ←mul_inv_eq_iff_eq_mul] at h,
  change ↑(x.2 * y.2⁻¹) = ↑(x.1⁻¹ * y.1) at h,
  rw [prod.ext_iff, ←@inv_mul_eq_one H _ x.1 y.1, ←@mul_inv_eq_one K _ x.2 y.2, subtype.ext_iff,
      subtype.ext_iff, coe_one, coe_one, h, and_self, ←mem_bot, ←h2.eq_bot, mem_inf],
  exact ⟨subtype.mem ((x.1)⁻¹ * (y.1)), (congr_arg (∈ K) h).mp (subtype.mem (x.2 * (y.2)⁻¹))⟩,
end

lemma is_complement_iff_card_mul_and_disjoint [fintype G] [fintype H] [fintype K] :
  is_complement (H : set G) (K : set G) ↔
    fintype.card H * fintype.card K = fintype.card G ∧ disjoint H K :=
⟨λ h, ⟨h.card_mul, h.disjoint⟩, λ h, is_complement_of_card_mul_and_disjoint h.1 h.2⟩

lemma is_complement_of_coprime [fintype G] [fintype H] [fintype K]
  (h1 : fintype.card H * fintype.card K = fintype.card G)
  (h2 : nat.coprime (fintype.card H) (fintype.card K)) :
  is_complement (H : set G) (K : set G) :=
is_complement_of_card_mul_and_disjoint h1 (disjoint_iff.mpr (inf_eq_bot_of_coprime h2))

end subgroup

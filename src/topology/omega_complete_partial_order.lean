/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import topology.basic
import order.omega_complete_partial_order

/-!
# Scott Topological Spaces

I don't know what they're good for but their notion
of continuity is equivalent to continuity in ωCPOs.

## Reference

 * https://ncatlab.org/nlab/show/Scott+topology

-/

open omega_complete_partial_order
open_locale classical

universes u
namespace scott_topological_space

/--  -/
def is_ωSup {α : Type u} [preorder α] (c : chain α) (x : α) : Prop :=
(∀ i, c i ≤ x) ∧ (∀ y, (∀ i, c i ≤ y) → x ≤ y)

variables (α : Type u) [preorder α]

/-- The characteristic function of open sets is monotone and preserves
the limits of chains. -/
def is_open (s : set α) : Prop :=
∃ (h : monotone s), ∀ (c : chain α) x, is_ωSup c x → is_ωSup (c.map ⟨s,h⟩) (s x)

theorem is_open_univ : is_open α set.univ :=
⟨λ x y h, le_refl _, λ c x ⟨h₀,h₁⟩, ⟨λ i _, trivial, λ y h₂, h₂ 0⟩⟩

theorem is_open_inter (s t : set α) : is_open α s → is_open α t → is_open α (s ∩ t) :=
begin
  simp only [is_open, exists_imp_distrib],
  intros h₀ h₁ h₂ h₃,
  have h₄ : monotone (s ∩ t : set α),
  { intros x y h, apply and_implies (h₀ h) (h₂ h) },
  existsi h₄,
  intros c x h₅,
  specialize h₁ _ _ h₅,
  specialize h₃ _ _ h₅,
  split,
  { rintros i ⟨h₆,h₇⟩,
    refine ⟨h₁.1 i h₆, h₃.1 i h₇⟩, },
  { rintros y h ⟨h₆,h₇⟩,
    cases h₁ with ha₁ hb₁,
    cases h₃ with ha₃ hb₃,
    apply hb₃ y _ h₇, -- h₆,
    intros i ht,
    apply hb₁ y _ h₆,
    intros j hs,
    apply h (max i j), split,
    { apply h₀ (c.monotone (le_max_right _ _)) hs, },
    { apply h₂ (c.monotone (le_max_left _ _)) ht, }, }
end

theorem is_open_sUnion : ∀s, (∀t∈s, is_open α t) → is_open α (⋃₀ s) :=
begin
  introv h₀,
  simp only [is_open],
  have h : monotone (⋃₀ s),
  { intros x y h,
    simp only [set.sUnion, set_of, exists_prop],
    apply exists_imp_exists, intro t,
    rintro ⟨h₁,h₂⟩,
    specialize h₀ _ h₁,
    cases h₀ with h₃ h₄,
    existsi h₁,
    exact h₃ h h₂ },
  existsi h,
  introv, rintro h₁, split,
  { rintros i ⟨t,ht,h⟩, refine ⟨_, ht, _⟩,
    specialize h₀ _ ht,
    rcases h₀ with ⟨h₀,h₂⟩,
    exact (h₂ _ _ h₁).1 i h, },
  { rintro y hy ⟨t,ht,hx⟩,
    specialize h₀ _ ht,
    rcases h₀ with ⟨h₀,h₂⟩,
    refine (h₂ _ _ h₁).2 y _ hx,
    intros i hi, apply hy _ ⟨_,ht,hi⟩ }
end

end scott_topological_space

/-- A Scott topological space is defined on preorders
such that their open sets, seen as a function `α → Prop`,
preserves the joins of ω-chains  -/
@[reducible]
def Scott (α : Type u) := α

instance scott_topological_space (α : Type u) [preorder α] : topological_space (Scott α) :=
{ is_open := scott_topological_space.is_open α,
  is_open_univ := scott_topological_space.is_open_univ α,
  is_open_inter := scott_topological_space.is_open_inter α,
  is_open_sUnion := scott_topological_space.is_open_sUnion α }

@[simp]
lemma le_iff_imp {p q : Prop} : p ≤ q ↔ (p → q) := by refl

section
variables {α : Type*} [preorder α] (y : Scott α)

/-- `not_below` is an open set in `Scott α` used
to prove the monotonicity of continuous functions -/
def not_below := { x | ¬ x ≤ y }

lemma f_below_is_open : is_open (not_below y) :=
begin
  have h : monotone (not_below y),
  { intros x y' h,
    simp only [not_below, set_of, le_iff_imp],
    intros h₀ h₁, apply h₀ (le_trans h h₁) },
  existsi h,
  rintros c x ⟨h₀,h₁⟩, split,
  { intros i,
    simp only [not_below, set_of, le_iff_imp, preorder_hom.coe_fun_mk, chain.map_to_fun, function.comp_app],
    intros h₂ h₃, apply h₂,
    transitivity, apply h₀, exact h₃ },
  { simp only [not_below, set_of, le_iff_imp, preorder_hom.coe_fun_mk, chain.map_to_fun, function.comp_app],
    intros p hp hyx,
    by_contradiction h₂, apply hyx, clear hyx,
    apply h₁, intro i,
    by_contradiction h₃,
    apply h₂ (hp _ h₃), }
end

end

open scott_topological_space (hiding is_open)
open omega_complete_partial_order

@[simp]
lemma set_of_apply {α} (p : α → Prop) (x : α) : set_of p x ↔ p x := iff.rfl

lemma is_ωSup_ωSup {α} [omega_complete_partial_order α] (c : chain α) :
  is_ωSup c (ωSup c) :=
begin
  split,
  { apply le_ωSup, },
  { apply ωSup_le, },
end

lemma Scott_continuous_of_continuous {α β}
  [omega_complete_partial_order α]
  [omega_complete_partial_order β]
  (f : Scott α → Scott β) (hf : continuous f) :
  omega_complete_partial_order.continuous' f :=
begin
  have h : monotone f,
  { intros x y h,
    cases (hf {x | ¬ x ≤ f y} (f_below_is_open _)) with hf hf', clear hf',
    specialize hf h, simp only [set.preimage, set_of, (∈), set.mem, le_iff_imp] at hf,
    by_contradiction, apply hf a (le_refl (f y)) },
  existsi h, intro c,
  apply eq_of_forall_ge_iff, intro z,
  simp only [ωSup_le_iff, preorder_hom.coe_fun_mk, chain.map_to_fun, function.comp_app],
  specialize (hf _ (f_below_is_open z)),
  cases hf, specialize hf_h c (ωSup c) _,
  simp only [not_below, set.preimage, set.mem_set_of_eq, set_of_apply] at hf_h,
  { cases hf_h with h₀ h₁, split, intros,
    { transitivity; [skip, apply a],
      apply h, apply le_ωSup, },
    { simp only [le_iff_imp, preorder_hom.coe_fun_mk, chain.map_to_fun, function.comp_app, set_of_apply] at h₀ h₁,
      intros h₂,
      by_contradiction h₃,
      refine h₁ false _ h₃,
      intros i h₄, apply h₄ (h₂ i), } },
  { split, apply le_ωSup,
    apply ωSup_le, }
end

lemma continuous_of_Scott_continuous {α β}
  [omega_complete_partial_order α]
  [omega_complete_partial_order β]
  (f : Scott α → Scott β) (hf : omega_complete_partial_order.continuous' f) :
  continuous f :=
begin
  intros s hs,
  cases hf with hf hf',
  have hf₀ : monotone (f ⁻¹' s),
  { intros x y h,
    simp only [set.preimage, le_iff_imp, set_of_apply],
    cases hs, intro h',
    apply hs_w (hf h) h', },
  existsi hf₀, rintros c x ⟨h₀,h₁⟩,
  split,
  { simp only [set.preimage, le_iff_imp, preorder_hom.coe_fun_mk, chain.map_to_fun, function.comp_app, set_of_apply],
    intros i h₂,
    exact hf₀ (h₀ i) h₂ },
  { intros p hp hs',
    simp only [set.preimage, le_iff_imp, preorder_hom.coe_fun_mk, chain.map_to_fun, function.comp_app, set_of_apply] at hp hs',
    cases hs with hs₀ hs₁,
    specialize hs₁ (c.map ⟨f,hf⟩) (ωSup (c.map ⟨f,hf⟩)) (is_ωSup_ωSup _),
    { cases hs₁ with hs₁ hs₂,
      simp only [le_iff_imp, preorder_hom.coe_fun_mk, chain.map_to_fun, function.comp_app] at hs₁ hs₂,
      specialize hf' c,
      apply hs₂ _ hp, clear hs₂,
      rw ← hf',
      rwa [show ωSup c = x, from _],
      apply le_antisymm,
      { apply ωSup_le _ _ h₀, },
      { apply h₁, apply le_ωSup, } }, }
end

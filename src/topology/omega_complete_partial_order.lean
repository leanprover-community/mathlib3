/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import topology.basic
import order.omega_complete_partial_order

/-!
# Scott Topological Spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A type of topological spaces whose notion
of continuity is equivalent to continuity in ωCPOs.

## Reference

 * https://ncatlab.org/nlab/show/Scott+topology

-/

open set omega_complete_partial_order
open_locale classical

universes u
namespace Scott

/-- `x` is an `ω`-Sup of a chain `c` if it is the least upper bound of the range of `c`. -/
def is_ωSup {α : Type u} [preorder α] (c : chain α) (x : α) : Prop :=
(∀ i, c i ≤ x) ∧ (∀ y, (∀ i, c i ≤ y) → x ≤ y)

lemma is_ωSup_iff_is_lub {α : Type u} [preorder α] {c : chain α} {x : α} :
  is_ωSup c x ↔ is_lub (range c) x :=
by simp [is_ωSup, is_lub, is_least, upper_bounds, lower_bounds]

variables (α : Type u) [omega_complete_partial_order α]

/-- The characteristic function of open sets is monotone and preserves
the limits of chains. -/
def is_open (s : set α) : Prop :=
continuous' (λ x, x ∈ s)

theorem is_open_univ : is_open α univ :=
⟨λ x y h hx, mem_univ _, @complete_lattice.top_continuous α Prop _ _⟩

theorem is_open.inter (s t : set α) : is_open α s → is_open α t → is_open α (s ∩ t) :=
complete_lattice.inf_continuous'

theorem is_open_sUnion (s : set (set α)) (hs : ∀t∈s, is_open α t) : is_open α (⋃₀ s) :=
begin
  simp only [is_open] at hs ⊢,
  convert complete_lattice.Sup_continuous' (set_of ⁻¹' s) _,
  { ext1 x,
    simp only [Sup_apply, set_of_bijective.surjective.exists, exists_prop, mem_preimage,
      set_coe.exists, supr_Prop_eq, mem_set_of_eq, subtype.coe_mk, mem_sUnion] },
  { intros p hp,
    exact hs (set_of p) (mem_preimage.1 hp) },
end

end Scott

/-- A Scott topological space is defined on preorders
such that their open sets, seen as a function `α → Prop`,
preserves the joins of ω-chains  -/
@[reducible]
def Scott (α : Type u) := α

instance Scott.topological_space (α : Type u) [omega_complete_partial_order α] :
  topological_space (Scott α) :=
{ is_open := Scott.is_open α,
  is_open_univ := Scott.is_open_univ α,
  is_open_inter := Scott.is_open.inter α,
  is_open_sUnion := Scott.is_open_sUnion α }

section not_below
variables {α : Type*} [omega_complete_partial_order α] (y : Scott α)

/-- `not_below` is an open set in `Scott α` used
to prove the monotonicity of continuous functions -/
def not_below := { x | ¬ x ≤ y }

lemma not_below_is_open : is_open (not_below y) :=
begin
  have h : monotone (not_below y),
  { intros x y' h,
    simp only [not_below, set_of, le_Prop_eq],
    intros h₀ h₁, apply h₀ (le_trans h h₁) },
  existsi h, rintros c,
  apply eq_of_forall_ge_iff, intro z,
  rw ωSup_le_iff,
  simp only [ωSup_le_iff, not_below, mem_set_of_eq, le_Prop_eq, order_hom.coe_fun_mk,
             chain.map_coe, function.comp_app, exists_imp_distrib, not_forall],
end

end not_below

open Scott (hiding is_open)
open omega_complete_partial_order

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
  simp only [continuous_def, (⁻¹')] at hf,
  have h : monotone f,
  { intros x y h,
    cases (hf {x | ¬ x ≤ f y} (not_below_is_open _)) with hf hf', clear hf',
    specialize hf h, simp only [preimage, mem_set_of_eq, le_Prop_eq] at hf,
    by_contradiction H, apply hf H le_rfl },
  existsi h, intro c,
  apply eq_of_forall_ge_iff, intro z,
  specialize (hf _ (not_below_is_open z)),
  cases hf, specialize hf_h c,
  simp only [not_below, order_hom.coe_fun_mk, eq_iff_iff, mem_set_of_eq] at hf_h,
  rw [← not_iff_not],
  simp only [ωSup_le_iff, hf_h, ωSup, supr, Sup, complete_lattice.Sup, complete_semilattice_Sup.Sup,
    exists_prop, mem_range, order_hom.coe_fun_mk, chain.map_coe, function.comp_app,
    eq_iff_iff, not_forall],
  tauto,
end

lemma continuous_of_Scott_continuous {α β}
  [omega_complete_partial_order α]
  [omega_complete_partial_order β]
  (f : Scott α → Scott β) (hf : omega_complete_partial_order.continuous' f) :
  continuous f :=
begin
  rw continuous_def,
  intros s hs,
  change continuous' (s ∘ f),
  cases hs with hs hs',
  cases hf with hf hf',
  apply continuous.of_bundled,
  apply continuous_comp _ _ hf' hs',
end

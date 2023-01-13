/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import logic.equiv.defs
import order.directed
import order.upper_lower
import topology.basic

/-!
# Scott topology

This file introduces the Scott topology on a preorder.

## References

* [Gierz et al, *A Compendium of Continuous Lattices*][GierzEtAl1980]
-/

-- Other references to Scott
--import topology.omega_complete_partial_order
--#check Scott
--import order.omega_complete_partial_order -- Scott continuity
--#check omega_complete_partial_order.continuous

variables (α : Type*)

/-
-- A complete lattice is a omega complete partial order
variables [complete_lattice α]

#check Scott.topological_space α

lemma Scott_upper (u : set α) (h: Scott.is_open α u) : is_upper_set u :=
begin
  intros a b hab ha,

end

lemma scott_open :
  Scott.is_open α = λ u, is_upper_set u ∧ ∀ (d : set α), directed_on (≤) d → Sup d ∈ u → d∩u ≠ ∅ :=
begin
  ext u,
  split,
  { intro h,
    split, },
  { intro h,
  sorry, }
end
-/
open set --topological_space

/--
Type synonym for a preorder equipped with the Scott topology
-/
def with_scott_topology := α

variables {α}

namespace with_scott_topology

/-- `to_scott` is the identity function to the `with_scott_topology` of a type.  -/
@[pattern] def to_scott : α ≃ with_scott_topology α := equiv.refl _

/-- `of_scott` is the identity function from the `with_scott_topology` of a type.  -/
@[pattern] def of_scott : with_scott_topology α ≃ α := equiv.refl _

@[simp] lemma to_with_scott_topology_symm_eq : (@to_scott α).symm = of_scott := rfl
@[simp] lemma of_with_scott_topology_symm_eq : (@of_scott α).symm = to_scott := rfl
@[simp] lemma to_scott_of_scott (a : with_scott_topology α) : to_scott (of_scott a) = a := rfl
@[simp] lemma of_scott_to_scott (a : α) : of_scott (to_scott a) = a := rfl
@[simp] lemma to_scott_inj {a b : α} : to_scott a = to_scott b ↔ a = b := iff.rfl
@[simp] lemma of_scott_inj {a b : with_scott_topology α} : of_scott a = of_scott b ↔ a = b :=
iff.rfl

/-- A recursor for `with_scott_topology`. Use as `induction x using with_scott_topology.rec`. -/
protected def rec {β : with_scott_topology α → Sort*}
  (h : Π a, β (to_scott a)) : Π a, β a := λ a, h (of_scott a)

instance [nonempty α] : nonempty (with_scott_topology α) := ‹nonempty α›
instance [inhabited α] : inhabited (with_scott_topology α) := ‹inhabited α›
instance [complete_lattice α] : complete_lattice (with_scott_topology α) := ‹complete_lattice α›

--variables [partial_order α]



/-
instance : topological_space (with_scott_topology α) := generate_from {s | ∃ a, (Ici a)ᶜ = s}

lemma is_open_preimage_of_scott (S : set α) :
  is_open (with_scott_topology.of_scott ⁻¹' S) ↔
    (generate_from {s : set α | ∃ (a : α), (Ici a)ᶜ = s}).is_open S := iff.rfl

lemma is_open_def (T : set (with_scott_topology α)) :
  is_open T ↔ (generate_from {s : set α | ∃ (a : α), (Ici a)ᶜ = s}).is_open
    (with_scott_topology.to_scott ⁻¹' T) := iff.rfl
-/

section preorder

variable [preorder α]

instance : preorder (with_scott_topology α) := ‹preorder α›

/-- A subset `u` of a pre-order is Scott open if, for every (non-empty) directed set `d` with least
upper bound `a`, if `a` lies in `u` then `u` and `d` intersect.
-/
def is_scott_open (u : set α) : Prop := is_upper_set u ∧
  ∀ (d : set α) (a : α), d.nonempty → directed_on (≤) d → is_lub d a → a ∈ u → d∩u ≠ ∅

lemma is_open_univ : is_scott_open (univ : set α) :=
begin
  rw is_scott_open,
  split,
  { exact is_upper_set_univ, },
  { intros d a hd₁ hd₂ hd₃ ha,
    rw inter_univ,
    exact nonempty.ne_empty hd₁ }
end

lemma is_open.inter (s t : set α) : is_scott_open s → is_scott_open t → is_scott_open (s ∩ t) :=
begin
  intros hs ht,
  rw is_scott_open at *,
  split,
  { exact is_upper_set.inter hs.1 ht.1, },
  { intros d a hd₁ hd₂ hd₃ ha,
    have hs₁: d ∩ s ≠ ∅ := hs.2 d a hd₁ hd₂ hd₃ ha.1,
    have ht₁: d ∩ t ≠ ∅ := ht.2 d a hd₁ hd₂ hd₃ ha.2,
    rw [← nonempty_iff_ne_empty, inter_nonempty] at hs₁,
    cases hs₁ with x hx,
    rw [← nonempty_iff_ne_empty, inter_nonempty] at ht₁,
    cases ht₁ with y hy,
    rw directed_on at hd₂,
    cases hd₂ x hx.1 y hy.1 with z hz,
    cases hz,
    rw [← nonempty_iff_ne_empty, inter_nonempty],
    use z,
    split,
    { exact hz_w, },
    { rw mem_inter_iff,
      split,
      { exact hs.1 hz_h.1 hx.2, },
      { exact ht.1 hz_h.2 hy.2, } } }
end

lemma is_open_sUnion (s : set (set α)) (hs : ∀t∈s, is_scott_open t) : is_scott_open (⋃₀ s) :=
begin
  rw is_scott_open at *,
  split,
  { apply is_upper_set_sUnion,
    intros s hs₁,
    apply (hs s hs₁).1, },
  { intros d a hd₁ hd₂ hd₃ ha,
  cases ha with s₁,
  cases ha_h,
  have d1: d ∩ s₁ ≠ ∅ := begin
   apply (hs s₁ ha_h_w).2,
   exact hd₁,
   exact hd₂,
   exact hd₃,
   exact ha_h_h,
  end,
  rw ← nonempty_iff_ne_empty,
  rw ← nonempty_iff_ne_empty at d1,
  cases d1 with x,
  use x,
  rw mem_inter_iff,
  split,
  { exact d1_h.1, },
  { rw mem_sUnion, use s₁, split, exact ha_h_w, exact d1_h.2, } }
end

def upper_set_topology : topological_space α :=
{
  is_open := is_upper_set,
  is_open_univ := is_upper_set_univ,
  is_open_inter := λ _ _, is_upper_set.inter,
  is_open_sUnion := λ _, is_upper_set_sUnion
}

#check subset_inter

def directed_set_topology : topological_space α :=
{
  is_open := λ u, ∀ (d : set α) (a : α), d.nonempty → directed_on (≤) d → is_lub d a → a ∈ u →
               ∃ b ∈ d, (Ici b)∩ d ⊆ u,
  is_open_univ := begin
    intros d a hd₁ hd₂ hd₃ ha,
    cases hd₁ with b hb,
    use b,
    split,
    { exact hb, },
    { exact (Ici b ∩ d).subset_univ, },
  end,
  is_open_inter := begin
    rintros s t,
    intros hs,
    intro ht,
    intros d a hd₁ hd₂ hd₃ ha,
    cases (hs d a hd₁ hd₂ hd₃ ha.1) with b₁ hb₁,
    cases (ht d a hd₁ hd₂ hd₃ ha.2) with b₂ hb₂,
    cases hb₁,
    cases hb₂,
    rw directed_on at hd₂,
    cases (hd₂ b₁ hb₁_w b₂ hb₂_w) with c hc,
    cases hc,
    use c,
    split,
    { exact hc_w, },
    { calc Ici c ∩ d ⊆ (Ici b₁ ∩ Ici b₂)∩d : by
        { apply inter_subset_inter_left d,
          apply subset_inter (Ici_subset_Ici.mpr hc_h.1) (Ici_subset_Ici.mpr hc_h.2), }
        ... = ((Ici b₁)∩d) ∩ ((Ici b₂)∩d) : by rw inter_inter_distrib_right
        ... ⊆ s ∩ t : by { exact inter_subset_inter hb₁_h hb₂_h } }
  end,
  is_open_sUnion := sorry,
}

instance : topological_space (with_scott_topology α) :=
{ is_open := is_scott_open,
  is_open_univ := is_open_univ,
  is_open_inter := is_open.inter,
  is_open_sUnion := is_open_sUnion }

end preorder

section complete_lattice

lemma complete_scott_open [complete_lattice α] :
  is_scott_open = λ u, is_upper_set u ∧
    ∀ (d : set α), d.nonempty → directed_on (≤) d → Sup d ∈ u → d∩u ≠ ∅ :=
begin
  ext u,
  rw is_scott_open,
  split,
  { intro h,
    split,
    { exact h.1, },
    { intros d hd₁ hd₂ hd₃,
      exact h.2 d (Sup d) hd₁ hd₂ (is_lub_Sup d) hd₃ } },
  { intro h,
    split,
    { exact h.1, },
    { intros d a hd₁ hd₂ hd₃ ha,
      apply h.2 d hd₁ hd₂,
      { rw (is_lub.Sup_eq hd₃), exact ha, } } }
end

end complete_lattice

end with_scott_topology

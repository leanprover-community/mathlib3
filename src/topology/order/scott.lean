/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import logic.equiv.defs
import order.directed
import order.upper_lower.basic
import topology.basic
import topology.order
import topology.continuous_function.basic

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

lemma is_open_join {a b : topological_space α} :
  (a⊔b).is_open = λ s, (a.is_open s ∧ b.is_open s) := rfl

variable [preorder α]

instance : preorder (with_scott_topology α) := ‹preorder α›

/--
The set of upper sets forms a topology
-/
def upper_set_topology : topological_space α :=
{ is_open := is_upper_set,
  is_open_univ := is_upper_set_univ,
  is_open_inter := λ _ _, is_upper_set.inter,
  is_open_sUnion := λ _, is_upper_set_sUnion }

/--
The set of sets satisfying "property (S)" (Gierz et al p100) form a topology
-/
def directed_set_topology : topological_space α :=
{ is_open := λ u, ∀ (d : set α) (a : α), d.nonempty → directed_on (≤) d → is_lub d a → a ∈ u →
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
  is_open_sUnion := begin
  intros s h,
  intros d a hd₁ hd₂ hd₃ ha,
  rw mem_sUnion at ha,
  cases ha with s₀ hs₀,
  cases hs₀,
  cases (h s₀ hs₀_w d a hd₁ hd₂ hd₃ hs₀_h) with b hb,
  use b,
  cases hb,
  split,
  { exact hb_w, },
  { exact subset_sUnion_of_subset s s₀ hb_h hs₀_w, }
  end, }

instance : topological_space (with_scott_topology α) := (upper_set_topology ⊔ directed_set_topology)

lemma scott_open (u : set (with_scott_topology α)) : is_open u =
  (upper_set_topology.is_open u ∧ directed_set_topology.is_open u) := rfl

lemma scott_is_open (u : set (with_scott_topology α)) : is_open u = (is_upper_set u ∧
∀ (d : set α) (a : α), d.nonempty → directed_on (≤) d → is_lub d a → a ∈ u
  → ∃ b ∈ d, (Ici b) ∩ d ⊆ u) := rfl

lemma scott_is_open' (u : set (with_scott_topology α)) : is_open u = (is_upper_set u ∧
∀ (d : set α) (a : α), d.nonempty → directed_on (≤) d → is_lub d a → a ∈ u → (d∩u).nonempty) :=
begin
  rw [scott_is_open, eq_iff_iff],
  split,
  { refine and.imp_right _,
    intros h d a d₁ d₂ d₃ ha,
    cases (h d a d₁ d₂ d₃ ha) with b,
    rw inter_nonempty_iff_exists_left,
    use b,
    cases h_1,
    split,
    { exact h_1_w, },
    { apply mem_of_subset_of_mem h_1_h,
      rw mem_inter_iff,
      split,
      { exact left_mem_Ici, },
      { exact h_1_w, } } },
  { intros h,
    split,
    { exact h.1, },
    { intros d a d₁ d₂ d₃ ha,
      have e1 : (d ∩ u).nonempty := by exact h.2 d a d₁ d₂ d₃ ha,
      rw inter_nonempty_iff_exists_left at e1,
      cases e1 with b,
      cases e1_h,
      use b,
      split,
      { exact e1_h_w, },
      { have e2 : Ici b ⊆ u := by exact is_upper_set_iff_Ici_subset.mp h.1 e1_h_h,
      apply subset.trans _ e2,
      apply inter_subset_left, }, }, }
end

lemma scott_closed (s : set (with_scott_topology α)) : is_closed s = (is_lower_set s ∧
∀ (d : set α) (a : α), d.nonempty → directed_on (≤) d → is_lub d a → d ⊆ s → a ∈ s ) :=
begin
  rw [← is_open_compl_iff, scott_is_open', is_lower_set_compl.symm, compl_compl],
  refine let_value_eq (and (is_lower_set s)) _,
  rw eq_iff_iff,
  split,
  { intros h d a d₁ d₂ d₃ d₄,
    by_contra h',
    rw ← mem_compl_iff at h',
    have c1: (d ∩ sᶜ).nonempty := by exact h d a d₁ d₂ d₃ h',
    have c2: (d ∩ sᶜ) =  ∅ :=
    begin
      rw [← subset_empty_iff, ← inter_compl_self s],
      exact inter_subset_inter_left _ d₄,
    end,
    rw c2 at c1,
    simp only [not_nonempty_empty] at c1,
    exact c1, },
  { intros h d a d₁ d₂ d₃ d₄,
    by_contra h',
    rw [inter_compl_nonempty_iff, not_not] at h',
    have c1: a ∈ s := by exact h d a d₁ d₂ d₃ h',
    contradiction, }
end

lemma scott_open_is_upper {s : set (with_scott_topology α)} : is_open s → is_upper_set s :=
begin
  intros h,
  rw scott_open at h,
  exact h.1,
end

lemma scott_closed_is_lower {s : set (with_scott_topology α)} : is_closed s → is_lower_set s :=
begin
  intro h,
  rw scott_closed at h,
  exact h.1,
end

/--
The closure of a singleton `{a}` in the Scott topology is the right-closed left-infinite interval
(-∞,a].
-/
@[simp] lemma closure_singleton (a : with_scott_topology α) : closure {a} = Iic a :=
begin
  rw ← lower_set.coe_Iic,
  rw ← lower_closure_singleton,
  refine subset_antisymm _ _,
  { apply closure_minimal subset_lower_closure,
    rw scott_closed,
    split,
    { exact (lower_closure {a}).lower },
    { rw lower_closure_singleton,
      intros d b d₁ d₂ d₃ d₄,
      rw [lower_set.coe_Iic, mem_Iic],
      exact (is_lub_le_iff d₃).mpr d₄, } },
  { apply lower_closure_min subset_closure (scott_closed_is_lower _),
    apply is_closed_closure, }
end

lemma is_upper_set_iff_forall_le {s : set α} : is_upper_set s ↔ ∀ ⦃a b : α⦄, a ≤ b → a ∈ s → b ∈ s
  := iff.rfl

variables {β : Type*} [preorder β]

lemma continuous.to_monotone (f : continuous_map (with_scott_topology α) (with_scott_topology β)) :
  monotone f :=
begin
  rw monotone,
  intros a b hab,
  let u := (Iic (f b))ᶜ,
  by_contra,
  have u2 : a ∈ (f⁻¹'  u) := h,
  have s1 : is_open u :=
  begin
    rw [is_open_compl_iff, ← closure_singleton],
    exact is_closed_closure,
  end,
  have s2 :  is_open (f⁻¹'  u) := is_open.preimage f.continuous_to_fun s1,
  have u3 : b ∈ (f⁻¹'  u) := is_upper_set_iff_forall_le.mp s2.1 hab u2,
  have c1 : f(b) ∈ (Iic (f b))ᶜ :=
  begin
    simp only [mem_compl_iff, mem_preimage, mem_Iic, le_refl, not_true] at u3,
    simp only [mem_compl_iff, mem_Iic, le_refl, not_true],
    exact u3,
  end,
  simp only [mem_compl_iff, mem_Iic, le_refl, not_true] at c1,
  exact c1,
end

-- https://planetmath.org/scottcontinuous

lemma pair_is_chain (a b : α) (hab: a ≤ b) : is_chain (≤) ({a, b} : set α) :=
begin
  apply is_chain.insert (set.subsingleton.is_chain subsingleton_singleton),
  intros c h₁ h₂,
  rw mem_singleton_iff at h₁,
  rw h₁,
  exact or.inl hab,
end

lemma directed_on_pair (a b : α) (hab: a ≤ b) : directed_on (≤) ({a, b} : set α) := by
begin
  apply is_chain.directed_on,
  apply pair_is_chain,
  exact hab,
end

/--
A function which preserves lub on directed sets
-/
def preserve_lub_on_directed (f : α → β) := ∀ (d : set α) (a : α), d.nonempty → directed_on (≤) d →
  is_lub d a → is_lub (f '' d) (f(a))

lemma preserve_lub_montotone (f : α → β) (h: preserve_lub_on_directed f): monotone f :=
begin
  intros a b hab,
  rw preserve_lub_on_directed at h,
  let d := ({a, b} : set α),
  have e1: is_lub (f '' d) (f b) :=
  begin
    apply h,
    { exact insert_nonempty a {b} },
    { exact directed_on_pair a b hab },
    { rw is_lub,
      split,
      { simp only [upper_bounds_insert, upper_bounds_singleton, mem_inter_iff, mem_Ici, le_refl,
          and_true],
        exact hab, },
      { simp only [upper_bounds_insert, upper_bounds_singleton],
        rw (inter_eq_self_of_subset_right (Ici_subset_Ici.mpr hab)),
        exact λ {x : α}, mem_Ici.mpr, } },
  end,
  rw [is_lub, is_least] at e1,
  cases e1,
  apply e1_left,
  rw mem_image,
  use a,
  simp only [mem_insert_iff, eq_self_iff_true, true_or, and_self],
end

lemma scott_continuity2 (f : (with_scott_topology α) → (with_scott_topology β)) :
  preserve_lub_on_directed f → continuous f :=
begin
  intro h,
  rw continuous_def,
  intros u hu,
  rw scott_is_open',
  split,
  { apply is_upper_set.preimage (scott_open_is_upper hu),
    apply preserve_lub_montotone,
    exact h, },
  { intros d a hd₁ hd₂ hd₃ ha,
  have e1: is_lub (f '' d) (f(a)) :=
  begin
    apply h,
    apply hd₁,
    apply hd₂,
    apply hd₃,
  end,
  rw scott_is_open' at hu,
  have e2: ((f '' d) ∩ u).nonempty :=
  begin
    apply hu.2,
    exact nonempty.image f hd₁,
    have e3: monotone f := begin
      apply preserve_lub_montotone,
      exact h,
    end,
    apply directed_on_image.mpr,
    exact directed_on.mono hd₂ e3,
    apply e1,
    exact ha,
  end,
  exact image_inter_nonempty_iff.mp e2, }
end

lemma scott_continuity (f : continuous_map (with_scott_topology α) (with_scott_topology β)) :
  preserve_lub_on_directed f :=
begin
  intros d a d₁ d₂ d₃,
  rw is_lub,
  split,
  { apply monotone.mem_upper_bounds_image (continuous.to_monotone f),
    rw ← is_lub_le_iff,
    exact d₃, },
  { rw [lower_bounds, mem_set_of_eq],
    intros b hb,
    let u := (Iic b)ᶜ,
    by_contra,
    have e1: a ∈ (f⁻¹'  u) := h,
    have s1 : is_open u :=
    begin
      rw [is_open_compl_iff, ← closure_singleton],
      exact is_closed_closure,
    end,
    have s2 : is_open (f⁻¹'  u) := is_open.preimage f.continuous_to_fun s1,
    rw scott_is_open' at s2,
    cases s2,
    cases s2_right d a d₁ d₂ d₃ e1 with c,
    cases h_1,
    simp at h_1_right,
    rw upper_bounds at hb,
    simp at hb,
    have c1: f c ≤ b :=
    begin
      apply hb,
      exact h_1_left,
    end,
    contradiction, },
end

end preorder

section complete_lattice

lemma complete_scott_open [complete_lattice α] (u : set (with_scott_topology α)) : is_open u =
(is_upper_set u ∧
  ∀ (d : set α), d.nonempty → directed_on (≤) d → Sup d ∈ u → ∃ b ∈ d, (Ici b) ∩ d ⊆ u) :=
begin
  rw scott_is_open,
  refine let_value_eq (and (is_upper_set u)) _,
  rw eq_iff_iff,
  split,
  { intros h d hd₁ hd₂ hd₃,
      exact h d (Sup d) hd₁ hd₂ (is_lub_Sup d) hd₃, },
  { intros h d a hd₁ hd₂ hd₃ ha,
      apply h d hd₁ hd₂,
      { rw (is_lub.Sup_eq hd₃), exact ha, } }
end

lemma complete_scott_open' [complete_lattice α] (u : set (with_scott_topology α)) : is_open u =
(is_upper_set u ∧
  ∀ (d : set α), d.nonempty → directed_on (≤) d → Sup d ∈ u → (d∩u).nonempty) :=
begin
  rw scott_is_open',
  refine let_value_eq (and (is_upper_set u)) _,
  rw eq_iff_iff,
  split,
  { intros h d hd₁ hd₂ hd₃,
      exact h d (Sup d) hd₁ hd₂ (is_lub_Sup d) hd₃, },
  { intros h d a hd₁ hd₂ hd₃ ha,
      apply h d hd₁ hd₂,
      { rw (is_lub.Sup_eq hd₃), exact ha, } }
end

end complete_lattice

end with_scott_topology
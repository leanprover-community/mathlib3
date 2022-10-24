/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import topology.basic
import topology.order
import topology.separation
import data.set.intervals.basic
import order.upper_lower

/-!
# Lower topology

This file introduces the lower topology on a preorder. It is shown that the lower topology on a
partial order is T₀ and the non-empty complements of the upper closures of finite subsets form a
basis.

## Implementation notes

Approach inspired by `order_topology` from topology.algebra.order.basic

## References

* [Gierz et al, A Compendium of Continuous Lattices][GierzEtAl1980]

## Tags

lower topology, preorder
-/

universe u
variable {α : Type u}

open set topological_space

/--
Type synonym for a preorder equipped with the lower topology
-/
@[reducible]
def lower (α : Type u) := α

-- Needed if the above definition is not reducible
/-
instance lower.preorder (α : Type u) [preorder α] :
  preorder (lower α) := _inst_1
-/

/--
The lower topology is the topology generated by the complements of the closed intervals to infinity
-/
def lower_topology (α : Type u) [preorder α] : topological_space α := generate_from {s | ∃ a, (Ici a)ᶜ = s}

instance lower.topological_space (α : Type u) [preorder α] :
  topological_space (lower α) := lower_topology α


section pre_order


variable [preorder α]

lemma lower_topology_def : (lower_topology α) = generate_from {s | ∃ a, (Ici a)ᶜ = s} := rfl

lemma is_open_iff_generate_Ici_comp {s : set α} :
  is_open s ↔ generate_open {s | ∃a, (Ici a)ᶜ = s } s := iff.rfl

/-
Left-closed right-infinite intervals [a,∞) are closed in the lower topology
-/
lemma Ici_is_closed (a : α) : is_closed (Ici a) :=
is_open_compl_iff.1 $ generate_open.basic _ ⟨a, rfl⟩

/-
The upper closure of a finite subset is closed in the lower topology
-/
lemma upper_closure_is_closed (F : set α) (h : F.finite) : is_closed (upper_closure F : set α) :=
begin
  simp only [← upper_set.infi_Ici, upper_set.coe_infi],
  exact is_closed_bUnion h (λ a h₁, Ici_is_closed a),
end

/-
Every subset open in the lower topology is a lower set
-/
lemma lower_open_is_lower {s : set α} (h: is_open s) : is_lower_set s :=
begin
  rw is_open_iff_generate_Ici_comp at h,
  induction h,
  case topological_space.generate_open.basic : u
  { rw mem_set_of_eq at h_H,
    choose a h_H using h_H,
    rw ← h_H,
    apply is_upper_set.compl,
    apply is_upper_set_Ici, },
  case topological_space.generate_open.univ : { exact is_lower_set_univ },
  case topological_space.generate_open.inter : u v hu1 hv1 hu2 hv2
    { apply is_lower_set.inter hu2 hv2 },
  case topological_space.generate_open.sUnion : { apply is_lower_set_sUnion h_ih, },
end

/-
The closure of a singleton {a} in the lower topology is the left-closed right-infinite interval
[a,∞)
-/
lemma lower_topology.closure_singleton (a : α) : closure {a} = Ici a :=
begin
  rw subset_antisymm_iff,
  split,
  { apply closure_minimal _ (Ici_is_closed a), rw [singleton_subset_iff, mem_Ici], },
  { unfold closure,
    refine subset_sInter _,
    intro u,
    intro h,
    rw mem_set_of_eq at h,
    intro b,
    intro hb,
    rw mem_Ici at hb,
    rw [singleton_subset_iff, ← is_open_compl_iff] at h,
    by_contradiction H,
    rw ← mem_compl_iff at H,
    have h1: a ∈ uᶜ, from lower_open_is_lower h.left hb H,
    rw mem_compl_iff at h1,
    rw ← not_not_mem at h,
    apply absurd h1 h.right, },
end

end pre_order

section partial_order

variable [partial_order α]

lemma Ici_eq (a b : α) : Ici a = Ici b ↔ a = b :=
begin
  split,
  { intro h,
    rw le_antisymm_iff,
    rw subset_antisymm_iff at h,
    split,
    { rw ← Ici_subset_Ici, exact h.2, },
    { rw ← Ici_subset_Ici, exact h.1, } },
  { apply congr_arg, }
end

/--
The non-empty complements of the upper closures of finite subsets are a collection of lower sets
which form a basis for the lower topology
-/
def lower_basis (α : Type u) [preorder α] :=
{s : set α | ∃ (F : set α), F.finite ∧
  ↑(upper_closure F).compl = s ∧
  s.nonempty }

lemma lower_basis_is_basis : is_topological_basis (lower_basis α) :=
begin
  convert is_topological_basis_of_subbasis lower_topology_def,
  rw image,
  ext,
  rw mem_set_of_eq,
  unfold lower_basis,
  rw mem_set_of_eq,
  let g := (⟨λ a, (Ici a)ᶜ,
  begin
    intros a b,
    simp only [compl_inj_iff],
    rw Ici_eq,
    exact congr_arg (λ ⦃a : α⦄, a),
  end⟩ : α ↪ set α),
  split,
  { intro h,
    cases h with F,
    let f := {s : set α | ∃ a ∈ F,  (Ici a)ᶜ = s},
    have ef: f = {s : set α | ∃ a ∈ F, (Ici a)ᶜ = s} := by refl,
    have efn: (⋂₀ f) = (upper_closure F).compl :=
    begin
      rw [upper_set.coe_compl, ← upper_set.infi_Ici, upper_set.coe_infi],
      simp only [upper_set.coe_infi, upper_set.coe_Ici, compl_Union],
      rw ← sInter_image,
      rw ef,
      apply congr_arg,
      rw image,
      simp_rw [exists_prop],
    end,
    have ef2: f = g '' F :=
    begin
      rw [ef, image],
      simp only [exists_prop, function.embedding.coe_fn_mk],
    end,
    use f,
    rw mem_set_of_eq,
    split,
    { split,
      { rw ef2,
      rw ← finite_coe_iff,
      rw ← finite_coe_iff at h_h,
      cases h_h,
      casesI nonempty_fintype F,
      apply_instance, },
      { split,
        { simp only [set_of_subset_set_of, forall_exists_index, forall_apply_eq_imp_iff₂,
            implies_true_iff, exists_apply_eq_apply], },
        { rw efn, rw h_h.2.1,  rw upper_set.carrier_eq_coe at , exact h_h.2.2 } }, },
    { rw [← h_h.2.1, efn], } },
  { intro h,
    cases h with f,
    rw mem_set_of_eq at h_h,
    let F := { a : α | (Ici a)ᶜ ∈ f },
    have eF' : F =  g ⁻¹' f := by refl,
    have eF: (⋂₀ f) = (upper_closure F).compl :=
    begin
      rw [upper_set.coe_compl, ← upper_set.infi_Ici, upper_set.coe_infi],
      simp only [upper_set.coe_infi, upper_set.coe_Ici, compl_Union],
      rw ← sInter_image,
      apply congr_arg,
      rw image,
      ext s,
      split,
      { rw mem_set_of_eq,
      intro hs,
      have es: ∃ (a : α), (Ici a)ᶜ = s := by exact h_h.1.2.1 hs,
      cases es with a,
      use a,
      split,
      { rw ← es_h at hs, rw mem_set_of_eq, exact hs, },
      { exact es_h, }, },
      { intros h,
        rw mem_set_of_eq at h,
        cases h with a,
        rw ← h_h_1.2,
        apply h_h_1.1, }
    end,
    use F,
    split,
    { cases h_h,
      cases h_h_left with hf,
      rw eF',
      apply finite.preimage_embedding,
      exact hf, },
    { split,
      { rw [← h_h.2, eF], },
      { convert h_h.1.2.2,
        rw h_h.2, } } }
end

/-
The lower topology on a partial order is T₀.
-/
@[priority 90] -- see Note [lower instance priority]
instance lower_topology.to_t0_space : t0_space α :=
begin
  rw t0_space_iff_inseparable,
  intros x y h,
  rw [inseparable_iff_closure_eq, lower_topology.closure_singleton,
    lower_topology.closure_singleton, subset_antisymm_iff] at h,
  rw le_antisymm_iff,
  split,
  { rw ← Ici_subset_Ici, apply h.2, },
  { rw ← Ici_subset_Ici, apply h.1, }
end

end partial_order

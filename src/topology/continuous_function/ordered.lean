/-
Copyright © 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Shing Tak Lam
-/

import topology.algebra.order.proj_Icc
import topology.algebra.order.group
import topology.continuous_function.basic

/-!
# Bundled continuous maps into orders, with order-compatible topology

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/

variables {α : Type*} {β : Type*} {γ : Type*}
variables [topological_space α] [topological_space β] [topological_space γ]

namespace continuous_map

section
variables [linear_ordered_add_comm_group β] [order_topology β]

/-- The pointwise absolute value of a continuous function as a continuous function. -/
def abs (f : C(α, β)) : C(α, β) :=
{ to_fun := λ x, |f x|, }

@[priority 100] -- see Note [lower instance priority]
instance : has_abs C(α, β) := ⟨λf, abs f⟩

@[simp] lemma abs_apply (f : C(α, β)) (x : α) : |f| x = |f x| :=
rfl

end

/-!
We now set up the partial order and lattice structure (given by pointwise min and max)
on continuous functions.
-/
section lattice

instance partial_order [partial_order β] :
  partial_order C(α, β) :=
partial_order.lift (λ f, f.to_fun) (by tidy)

lemma le_def [partial_order β] {f g : C(α, β)} : f ≤ g ↔ ∀ a, f a ≤ g a :=
pi.le_def

lemma lt_def [partial_order β] {f g : C(α, β)} :
  f < g ↔ (∀ a, f a ≤ g a) ∧ (∃ a, f a < g a) :=
pi.lt_def

instance has_sup [linear_order β] [order_closed_topology β] : has_sup C(α, β) :=
{ sup := λ f g, { to_fun := λ a, max (f a) (g a), } }

@[simp, norm_cast] lemma sup_coe [linear_order β] [order_closed_topology β] (f g : C(α, β)) :
  ((f ⊔ g : C(α, β)) : α → β) = (f ⊔ g : α → β) :=
rfl

@[simp] lemma sup_apply [linear_order β] [order_closed_topology β] (f g : C(α, β)) (a : α) :
  (f ⊔ g) a = max (f a) (g a) :=
rfl

instance [linear_order β] [order_closed_topology β] : semilattice_sup C(α, β) :=
{ le_sup_left := λ f g, le_def.mpr (by simp [le_refl]),
  le_sup_right := λ f g, le_def.mpr (by simp [le_refl]),
  sup_le := λ f₁ f₂ g w₁ w₂, le_def.mpr (λ a, by simp [le_def.mp w₁ a, le_def.mp w₂ a]),
  ..continuous_map.partial_order,
  ..continuous_map.has_sup, }

instance has_inf [linear_order β] [order_closed_topology β] : has_inf C(α, β) :=
{ inf := λ f g, { to_fun := λ a, min (f a) (g a), } }

@[simp, norm_cast] lemma inf_coe [linear_order β] [order_closed_topology β] (f g : C(α, β)) :
  ((f ⊓ g : C(α, β)) : α → β) = (f ⊓ g : α → β) :=
rfl

@[simp] lemma inf_apply [linear_order β] [order_closed_topology β] (f g : C(α, β)) (a : α) :
  (f ⊓ g) a = min (f a) (g a) :=
rfl

instance [linear_order β] [order_closed_topology β] : semilattice_inf C(α, β) :=
{ inf_le_left := λ f g, le_def.mpr (by simp [le_refl]),
  inf_le_right := λ f g, le_def.mpr (by simp [le_refl]),
  le_inf := λ f₁ f₂ g w₁ w₂, le_def.mpr (λ a, by simp [le_def.mp w₁ a, le_def.mp w₂ a]),
  ..continuous_map.partial_order,
  ..continuous_map.has_inf, }

instance [linear_order β] [order_closed_topology β] : lattice C(α, β) :=
{ ..continuous_map.semilattice_inf,
  ..continuous_map.semilattice_sup }

-- TODO transfer this lattice structure to `bounded_continuous_function`

section sup'
variables [linear_order γ] [order_closed_topology γ]

lemma sup'_apply {ι : Type*} {s : finset ι} (H : s.nonempty) (f : ι → C(β, γ)) (b : β) :
  s.sup' H f b = s.sup' H (λ a, f a b) :=
finset.comp_sup'_eq_sup'_comp H (λ f : C(β, γ), f b) (λ i j, rfl)

@[simp, norm_cast]
lemma sup'_coe {ι : Type*} {s : finset ι} (H : s.nonempty) (f : ι → C(β, γ)) :
  ((s.sup' H f : C(β, γ)) : ι → β) = s.sup' H (λ a, (f a : β → γ)) :=
by { ext, simp [sup'_apply], }

end sup'

section inf'
variables [linear_order γ] [order_closed_topology γ]

lemma inf'_apply {ι : Type*} {s : finset ι} (H : s.nonempty) (f : ι → C(β, γ)) (b : β) :
  s.inf' H f b = s.inf' H (λ a, f a b) :=
@sup'_apply _ γᵒᵈ _ _ _ _ _ _ H f b

@[simp, norm_cast]
lemma inf'_coe {ι : Type*} {s : finset ι} (H : s.nonempty) (f : ι → C(β, γ)) :
  ((s.inf' H f : C(β, γ)) : ι → β) = s.inf' H (λ a, (f a : β → γ)) :=
@sup'_coe _ γᵒᵈ _ _ _ _ _ _ H f

end inf'

end lattice

section extend

variables [linear_order α] [order_topology α] {a b : α} (h : a ≤ b)

/--
Extend a continuous function `f : C(set.Icc a b, β)` to a function `f : C(α, β)`.
-/
def Icc_extend (f : C(set.Icc a b, β)) : C(α, β) := ⟨set.Icc_extend h f⟩

@[simp] lemma coe_Icc_extend (f : C(set.Icc a b, β)) :
  ((Icc_extend h f : C(α, β)) : α → β) = set.Icc_extend h f := rfl

end extend

end continuous_map

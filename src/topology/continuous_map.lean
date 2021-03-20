/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/

import topology.subset_properties
import topology.tactic
import topology.algebra.ordered

/-!
# Continuous bundled map

In this file we define the type `continuous_map` of continuous bundled maps.
-/

/-- Bundled continuous maps. -/
@[protect_proj]
structure continuous_map (α : Type*) (β : Type*)
[topological_space α] [topological_space β] :=
(to_fun             : α → β)
(continuous_to_fun  : continuous to_fun . tactic.interactive.continuity')

notation `C(` α `, ` β `)` := continuous_map α β

namespace continuous_map

attribute [continuity] continuous_map.continuous_to_fun

variables {α : Type*} {β : Type*} {γ : Type*}
variables [topological_space α] [topological_space β] [topological_space γ]

instance : has_coe_to_fun (C(α, β)) := ⟨_, continuous_map.to_fun⟩

@[simp] lemma to_fun_eq_coe {f : C(α, β)} : f.to_fun = (f : α → β) := rfl

variables {α β} {f g : continuous_map α β}

protected lemma continuous (f : C(α, β)) : continuous f := f.continuous_to_fun
protected lemma continuous_at (f : C(α, β)) (x : α) : continuous_at f x :=
f.continuous.continuous_at

@[continuity] lemma coe_continuous : continuous (f : α → β) := f.continuous_to_fun

protected lemma congr_fun {f g : C(α, β)} (H : f = g) (x : α) : f x = g x := H ▸ rfl
protected lemma congr_arg (f : C(α, β)) {x y : α} (h : x = y) : f x = f y := h ▸ rfl

@[ext] theorem ext (H : ∀ x, f x = g x) : f = g :=
by cases f; cases g; congr'; exact funext H

lemma ext_iff : f = g ↔ ∀ x, f x = g x :=
⟨continuous_map.congr_fun, ext⟩

instance [inhabited β] : inhabited C(α, β) :=
⟨{ to_fun := λ _, default _, }⟩

lemma coe_inj ⦃f g : C(α, β)⦄ (h : (f : α → β) = g) : f = g :=
by cases f; cases g; cases h; refl

@[simp] lemma coe_mk (f : α → β) (h : continuous f) :
  ⇑(⟨f, h⟩ : continuous_map α β) = f := rfl

section
variables (α β)
/--
The map forgetting that a continuous function is continuous.
-/
def forget_continuity : C(α, β) → (α → β) :=
λ f, f.1

@[simp] lemma forget_continuity_coe (f : C(α, β)) : (forget_continuity α β f : α → β) = f :=
rfl

lemma forget_continuity_injective : function.injective (forget_continuity α β) :=
by tidy

/--
The continuous functions from `α` to `β` are the same as the plain functions when `α` is discrete.
-/
@[simps]
def equiv_fn_of_discrete [discrete_topology α] : C(α, β) ≃ (α → β) :=
⟨(λ f, f), (λ f, ⟨f, continuous_of_discrete_topology⟩),
  λ f, by { ext, refl, }, λ f, by { ext, refl, }⟩

end

/-- The identity as a continuous map. -/
def id : C(α, α) := ⟨id⟩

@[simp] lemma id_coe : (id : α → α) = id := rfl
lemma id_apply (a : α) : id a = a := rfl

/-- The composition of continuous maps, as a continuous map. -/
def comp (f : C(β, γ)) (g : C(α, β)) : C(α, γ) := ⟨f ∘ g⟩

@[simp] lemma comp_coe (f : C(β, γ)) (g : C(α, β)) : (comp f g : α → γ) = f ∘ g := rfl
lemma comp_apply (f : C(β, γ)) (g : C(α, β)) (a : α) : comp f g a = f (g a) := rfl

/-- Constant map as a continuous map -/
def const (b : β) : C(α, β) := ⟨λ x, b⟩

@[simp] lemma const_coe (b : β) : (const b : α → β) = (λ x, b) := rfl
lemma const_apply (b : β) (a : α) : const b a = b := rfl

section
variables [linear_ordered_add_comm_group β] [order_topology β]

/-- The pointwise absolute value of a continuous function as a continuous function. -/
def abs (f : C(α, β)) : C(α, β) :=
{ to_fun := λ x, abs (f x), }

@[simp] lemma abs_apply (f : C(α, β)) (x : α) : f.abs x = _root_.abs (f x) :=
rfl

end

/-!
We now set up the partial order and lattice structure (given by pointwise min and max)
on continuous functions.
-/
section lattice

instance partial_order [partial_order β] :
  partial_order C(α, β) :=
partial_order.lift (forget_continuity α β) (forget_continuity_injective α β)

lemma le_def [partial_order β] {f g : C(α, β)} : f ≤ g ↔ ∀ a, f a ≤ g a :=
pi.le_def

lemma lt_def [partial_order β] {f g : C(α, β)} :
  f < g ↔ (∀ a, f a ≤ g a) ∧ (∃ a, f a < g a) :=
pi.lt_def

instance has_sup [linear_order β] [order_closed_topology β] : has_sup C(α, β) :=
{ sup := λ f g, { to_fun := λ a, max (f a) (g a), } }

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

end lattice

end continuous_map

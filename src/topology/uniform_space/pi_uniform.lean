/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import topology.uniform_space.uniform_convergence

/-! TODO -/
noncomputable theory
open_locale topological_space classical uniformity filter

open set filter

def pi_uniform (α β : Type*) := α → β
def pi_uniform_on (α β : Type*) (𝔖 : set (set α)) := α → β

localized "notation α ` →ᵤ[`:25 𝔖:25 `] `:0 β:0 := pi_uniform_on α β 𝔖" in pi_uniform
localized "notation α ` →ᵤ `:25 β:0 := pi_uniform α β" in pi_uniform

open_locale pi_uniform

namespace pi_uniform

variables (α : Type*) {β γ ι : Type*} [uniform_space β]
variables {F : ι → α → β} {f : α → β} {s s' : set α} {x : α} {p : filter ι} {g : ι → α}

protected def gen (V : set (β × β)) : set ((α →ᵤ β) × (α →ᵤ β)) :=
  {uv : (α →ᵤ β) × (α →ᵤ β) | ∀ x, (uv.1 x, uv.2 x) ∈ V}

protected lemma is_basis_gen : is_basis (λ V : set (β × β), V ∈ 𝓤 β) (pi_uniform.gen α) :=
sorry

protected def uniformity_basis : filter_basis ((α →ᵤ β) × (α →ᵤ β)) :=
(pi_uniform.is_basis_gen α).filter_basis

protected def uniform_core : uniform_space.core (α →ᵤ β) :=
{ uniformity := (pi_uniform.uniformity_basis α).filter,
  refl := sorry,
  symm := sorry,
  comp := sorry }

instance : uniform_space (α →ᵤ β) :=
uniform_space.of_core (pi_uniform.uniform_core α)

end pi_uniform

namespace pi_uniform_on

variables {α : Type*} {β γ ι : Type*} [uniform_space β] (𝔖 : set (set α))
variables {F : ι → α → β} {f : α → β} {s s' : set α} {x : α} {p : filter ι} {g : ι → α}

protected def restrict (S : set α) (f : α →ᵤ[𝔖] β) : S →ᵤ β :=
f ∘ coe

variables {α}

instance : uniform_space (α →ᵤ[𝔖] β) :=
⨅ (S : set α) (hS : S ∈ 𝔖), uniform_space.comap (pi_uniform_on.restrict 𝔖 S) infer_instance

end pi_uniform_on

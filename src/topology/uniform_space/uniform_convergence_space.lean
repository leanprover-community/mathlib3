/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import topology.uniform_space.uniform_convergence

/-!
# TODO
-/
noncomputable theory
open_locale topological_space classical uniformity filter

open set filter

namespace uniform_convergence

variables (α : Type*) {β γ ι : Type*} [uniform_space β]
variables {F : ι → α → β} {f : α → β} {s s' : set α} {x : α} {p : filter ι} {g : ι → α}

protected def gen (V : set (β × β)) : set ((α → β) × (α → β)) :=
  {uv : (α → β) × (α → β) | ∀ x, (uv.1 x, uv.2 x) ∈ V}

protected lemma is_basis_gen : is_basis (λ V : set (β × β), V ∈ 𝓤 β) (uniform_convergence.gen α) :=
sorry

protected def uniformity_basis : filter_basis ((α → β) × (α → β)) :=
(uniform_convergence.is_basis_gen α).filter_basis

protected def uniform_core : uniform_space.core (α → β) :=
{ uniformity := (uniform_convergence.uniformity_basis α).filter,
  refl := sorry,
  symm := sorry,
  comp := sorry }

protected def uniform_space : uniform_space (α → β) :=
uniform_space.of_core (uniform_convergence.uniform_core α)

end uniform_convergence

namespace uniform_convergence_on

variables {α : Type*} {β γ ι : Type*} [uniform_space β] (𝔖 : set (set α))
variables {F : ι → α → β} {f : α → β} {s s' : set α} {x : α} {p : filter ι} {g : ι → α}

protected def restrict (S : set α) (f : α → β) : S → β :=
f ∘ coe

variables {α}

def uniform_space : uniform_space (α → β) :=
⨅ (S : set α) (hS : S ∈ 𝔖), uniform_space.comap (λ f, f ∘ coe) (uniform_convergence.uniform_space S)

end uniform_convergence_on

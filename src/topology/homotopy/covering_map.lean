/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/

import topology.local_homeomorph

universes u v

structure covering_map (X : Type u) (Y : Type v) [topological_space X] [topological_space Y]
  extends C(X, Y) :=
(nbhd : Y → set Y)
(mem_nbhd : ∀ y, y ∈ nbhd y)
(local_homeos : Y → set (local_homeomorph Y X))
(local_homeos_source : ∀ y, ∀ (f : local_homeomorph Y X), f ∈ local_homeos y → f.source = nbhd y)
(local_homeos_target_disjoint : ∀ y, ∀ (f g : local_homeomorph Y X),
  f ∈ local_homeos y → g ∈ local_homeos y → f ≠ g → f.target ∩ g.target = ∅)

namespace covering_map

variables {X : Type u} {Y : Type v} [topological_space X] [topological_space Y]

def targets (p : covering_map X Y) (y : Y) : set (set X) :=
(λ f : local_homeomorph Y X, f.target) '' p.local_homeos y

def of_homeomorph (h : Y ≃ₜ X) : covering_map X Y :=
{ to_fun := h.symm,
  nbhd := λ _, set.univ,
  mem_nbhd := λ _, trivial,
  local_homeos := λ y, {h.to_local_homeomorph},
  local_homeos_source := λ y f hf, by simp * at *,
  local_homeos_target_disjoint := λ y f g hf hf h, false.elim $ h $ by simp * at * }

end covering_map

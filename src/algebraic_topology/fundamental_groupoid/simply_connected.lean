/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
import algebraic_topology.fundamental_groupoid.induced_maps
import topology.homotopy.contractible
import category_theory.punit
import algebraic_topology.fundamental_groupoid.punit

/-!
# Simply connected spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
This file defines simply connected spaces.
A topological space is simply connected if its fundamental groupoid is equivalent to `unit`.

## Main theorems
  - `simply_connected_iff_unique_homotopic` - A space is simply connected if and only if it is
    nonempty and there is a unique path up to homotopy between any two points

  - `simply_connected_space.of_contractible` - A contractible space is simply connected
-/
noncomputable theory

open category_theory
open continuous_map
open_locale continuous_map

/-- A simply connected space is one whose fundamental groupoid is equivalent to `discrete unit` -/
class simply_connected_space (X : Type*) [topological_space X] : Prop :=
(equiv_unit [] : nonempty (fundamental_groupoid X ≌ discrete unit))

lemma simply_connected_def (X : Type*) [topological_space X] :
  simply_connected_space X ↔ nonempty (fundamental_groupoid X ≌ discrete unit) :=
⟨λ h, @simply_connected_space.equiv_unit X _ h, λ h, ⟨h⟩⟩

lemma simply_connected_iff_unique_homotopic (X : Type*) [topological_space X] :
  simply_connected_space X ↔ (nonempty X) ∧
  ∀ (x y : X), nonempty (unique (path.homotopic.quotient x y)) :=
by { rw [simply_connected_def, equiv_punit_iff_unique], refl, }

namespace simply_connected_space
variables {X : Type*} [topological_space X] [simply_connected_space X]

instance (x y : X) : subsingleton (path.homotopic.quotient x y) :=
@unique.subsingleton _ (nonempty.some (by { rw simply_connected_iff_unique_homotopic at *, tauto }))

local attribute [instance] path.homotopic.setoid

@[priority 100]
instance : path_connected_space X :=
let unique_homotopic := (simply_connected_iff_unique_homotopic X).mp infer_instance in
{ nonempty := unique_homotopic.1, joined := λ x y, ⟨(unique_homotopic.2 x y).some.default.out⟩, }

/-- In a simply connected space, any two paths are homotopic -/
lemma paths_homotopic {x y : X} (p₁ p₂ : path x y) : path.homotopic p₁ p₂ :=
by simpa using @subsingleton.elim (path.homotopic.quotient x y) _ ⟦p₁⟧ ⟦p₂⟧

@[priority 100]
instance of_contractible (Y : Type*) [topological_space Y] [contractible_space Y] :
  simply_connected_space Y :=
{ equiv_unit :=
  let H : Top.of Y ≃ₕ Top.of unit := (contractible_space.hequiv_unit Y).some in
  ⟨(fundamental_groupoid_functor.equiv_of_homotopy_equiv H).trans
    fundamental_groupoid.punit_equiv_discrete_punit⟩, }

end simply_connected_space

local attribute [instance] path.homotopic.setoid

/-- A space is simply connected iff it is path connected, and there is at most one path
  up to homotopy between any two points. -/
lemma simply_connected_iff_paths_homotopic {Y : Type*} [topological_space Y] :
  simply_connected_space Y ↔ (path_connected_space Y) ∧
  (∀ x y : Y, subsingleton (path.homotopic.quotient x y)) :=
⟨by { introI, split; apply_instance, },
λ h, begin
  casesI h, rw simply_connected_iff_unique_homotopic,
  exact ⟨infer_instance, λ x y, ⟨unique_of_subsingleton ⟦path_connected_space.some_path x y⟧⟩⟩,
end⟩

/-- Another version of `simply_connected_iff_paths_homotopic` -/
lemma simply_connected_iff_paths_homotopic' {Y : Type*} [topological_space Y] :
  simply_connected_space Y ↔ (path_connected_space Y) ∧
  (∀ {x y : Y} (p₁ p₂ : path x y), path.homotopic p₁ p₂) :=
begin
  convert simply_connected_iff_paths_homotopic,
  simp [path.homotopic.quotient, setoid.eq_top_iff], refl,
end

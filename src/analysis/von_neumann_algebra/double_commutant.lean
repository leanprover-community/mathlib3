/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import analysis.von_neumann_algebra.basic
import topology.algebra.algebra

/-!
# Von Neumann's double commutant theorem
-/

noncomputable theory

/--
`strong_operator_topology 𝕜 X Y` is a type synonym for `X →L[𝕜] Y`,
equipped with the strong operator topology.
(That is, the weakest topology so `T ↦ ∥Tx∥` is continuous for every `x : X`.)
-/
def strong_operator_topology (𝕜 : Type*) [normed_field 𝕜]
  (X Y : Type*) [normed_group X] [normed_space 𝕜 X] [normed_group Y] [normed_space 𝕜 Y] :=
X →L[𝕜] Y

/--
`weak_operator_topology 𝕜 X Y` is a type synonym for `X →L[𝕜] Y`,
equipped with the weak operator topology.
(That is, the weakest topology so `T ↦ |φ(Tx)|` is continuous for every `x : X` and `φ : dual Y`.)
-/
def weak_operator_topology (𝕜 : Type*) [normed_field 𝕜]
  (X Y : Type*) [normed_group X] [normed_space 𝕜 X] [normed_group Y] [normed_space 𝕜 Y] :=
X →L[𝕜] Y


section
variables (𝕜 : Type*) [normed_field 𝕜]
variables (X Y : Type*) [normed_group X] [normed_space 𝕜 X] [normed_group Y] [normed_space 𝕜 Y]

instance : has_coe_to_fun (strong_operator_topology 𝕜 X Y) (λ f, X → Y) :=
{ coe := λ f, by { dsimp [strong_operator_topology] at f, exact f, } }

instance : has_coe_to_fun (weak_operator_topology 𝕜 X Y) (λ f, X → Y) :=
{ coe := λ f, by { dsimp [weak_operator_topology] at f, exact f, } }

instance : ring (strong_operator_topology 𝕜 X X) :=
by { dsimp [strong_operator_topology], apply_instance, }

instance : ring (weak_operator_topology 𝕜 X X) :=
by { dsimp [weak_operator_topology], apply_instance, }

instance : algebra 𝕜 (strong_operator_topology 𝕜 X X) :=
by { dsimp [strong_operator_topology], apply_instance, }

instance : algebra 𝕜 (weak_operator_topology 𝕜 X X) :=
by { dsimp [weak_operator_topology], apply_instance, }

open topological_space

instance : topological_space (strong_operator_topology 𝕜 X Y) :=
⨅ (x : X), induced (λ T, ∥T x∥) infer_instance

instance : topological_ring (strong_operator_topology 𝕜 X X) :=
sorry

end

section
variables (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
variables (X Y : Type*) [normed_group X] [normed_space 𝕜 X] [normed_group Y] [normed_space 𝕜 Y]

open topological_space

instance : topological_space (weak_operator_topology 𝕜 X Y) :=
⨅ (x : X) (φ : normed_space.dual 𝕜 Y), induced (λ T, φ (T x)) infer_instance

instance : topological_ring (weak_operator_topology 𝕜 X X) :=
sorry

end

section
variables (𝕜 : Type*) [is_R_or_C 𝕜] (H : Type*) [inner_product_space 𝕜 H] [complete_space H]

instance : star_ring (strong_operator_topology 𝕜 H H) :=
by { dsimp [strong_operator_topology], apply_instance, }

instance : star_ring (weak_operator_topology 𝕜 H H) :=
by { dsimp [weak_operator_topology], apply_instance, }

instance : star_module 𝕜 (strong_operator_topology 𝕜 H H) :=
by { dsimp [strong_operator_topology], apply_instance, }

instance : star_module 𝕜 (weak_operator_topology 𝕜 H H) :=
by { dsimp [weak_operator_topology], apply_instance, }

end

namespace subalgebra
variables {𝕜 : Type*} [normed_field 𝕜]
variables {X : Type*} [normed_group X] [normed_space 𝕜 X]

def strong_closure (O : subalgebra 𝕜 (X →L[𝕜] X)) : subalgebra 𝕜 (strong_operator_topology 𝕜 X X) :=
subalgebra.topological_closure O

def weak_closure (O : subalgebra 𝕜 (X →L[𝕜] X)) : subalgebra 𝕜 (weak_operator_topology 𝕜 X X) :=
subalgebra.topological_closure O

end subalgebra

namespace star_subalgebra
variables {𝕜 : Type*} [is_R_or_C 𝕜] {H : Type*} [inner_product_space 𝕜 H] [complete_space H]

def strong_closure (O : star_subalgebra 𝕜 (H →L[𝕜] H)) :
  star_subalgebra 𝕜 (strong_operator_topology 𝕜 H H) :=
-- star_subalgebra.topological_closure O
sorry

def weak_closure (O : star_subalgebra 𝕜 (H →L[𝕜] H)) :
  star_subalgebra 𝕜 (weak_operator_topology 𝕜 H H) :=
-- star_subalgebra.topological_closure O
sorry

end star_subalgebra

theorem von_neumann_double_commutant
  (𝕜 : Type*) [is_R_or_C 𝕜] (H : Type*) [inner_product_space 𝕜 H] [complete_space H]
  (M : star_subalgebra 𝕜 (H →L[𝕜] H)) :
  M.commutant.commutant = M.weak_closure :=
sorry

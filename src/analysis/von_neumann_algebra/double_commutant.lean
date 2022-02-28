/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import analysis.von_neumann_algebra.basic
import topology.algebra.algebra
import analysis.seminorm

/-!
# Von Neumann's double commutant theorem
-/

theorem finset.sup_mul_left
  {ι : Type*} (s : finset ι) (f : ι → nnreal) (a : nnreal) :
  s.sup (λ i, a * f i) = a * s.sup f :=
sorry

noncomputable theory

/--
`strong_operator_topology 𝕜 X Y` is a type synonym for `X →L[𝕜] Y`,
equipped with the strong operator topology.
(That is, the weakest topology so `T ↦ ∥T x∥` is continuous for every `x : X`.)
-/
def strong_operator_topology (𝕜 : Type*) [normed_field 𝕜]
  (X Y : Type*) [normed_group X] [normed_space 𝕜 X] [normed_group Y] [normed_space 𝕜 Y] :=
X →L[𝕜] Y

/--
`weak_operator_topology 𝕜 X Y` is a type synonym for `X →L[𝕜] Y`,
equipped with the weak operator topology.
(That is, the weakest topology so `T ↦ |φ (T x)|` is continuous for every `x : X` and `φ : dual Y`.)
-/
def weak_operator_topology (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
  (X Y : Type*) [normed_group X] [normed_space 𝕜 X] [normed_group Y] [normed_space 𝕜 Y] :=
X →L[𝕜] Y


section
variables (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
variables (X Y : Type*) [normed_group X] [normed_space 𝕜 X] [normed_group Y] [normed_space 𝕜 Y]

instance strong_operator_topology.has_coe : has_coe (strong_operator_topology 𝕜 X Y) (X →L[𝕜] Y) :=
{ coe := λ f, f }

instance : add_comm_group (strong_operator_topology 𝕜 X Y) :=
by { dsimp [strong_operator_topology], apply_instance, }

instance : module 𝕜 (strong_operator_topology 𝕜 X Y) :=
by { dsimp [strong_operator_topology], apply_instance, }

instance : ring (strong_operator_topology 𝕜 X X) :=
by { dsimp [strong_operator_topology], apply_instance, }

instance : algebra 𝕜 (strong_operator_topology 𝕜 X X) :=
by { dsimp [strong_operator_topology], apply_instance, }

open topological_space

def seminorm_at (x : X) :=
(norm_seminorm 𝕜 Y).comp (continuous_linear_map.apply 𝕜 Y x).to_linear_map

@[simp] lemma seminorm_at_apply (x : X) (T : X →L[𝕜] Y) : seminorm_at 𝕜 X Y x T = ∥T x∥ := rfl

def strong_operator_topology.module_filter_basis :
  module_filter_basis 𝕜 (strong_operator_topology 𝕜 X Y) :=
seminorm.seminorm_module_filter_basis (seminorm_at 𝕜 X Y)

instance : topological_space (strong_operator_topology 𝕜 X Y) :=
(strong_operator_topology.module_filter_basis 𝕜 X Y).topology

example : topological_add_group (strong_operator_topology 𝕜 X Y) :=
by apply_instance

example : has_continuous_smul 𝕜 (strong_operator_topology 𝕜 X Y) :=
by apply_instance

/-! Composition of operators is separately continuous in each argument (TODO!),
but not jointly continuous, so there is no `topological_ring` structure to construct here. -/

end


section
variables (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
variables (X Y : Type*) [normed_group X] [normed_space 𝕜 X] [normed_group Y] [normed_space 𝕜 Y]

instance weak_operator_topology.has_coe : has_coe (weak_operator_topology 𝕜 X Y) (X →L[𝕜] Y) :=
{ coe := λ f, f }

instance : add_comm_group (weak_operator_topology 𝕜 X Y) :=
by { dsimp [weak_operator_topology], apply_instance, }

instance : module 𝕜 (weak_operator_topology 𝕜 X Y) :=
by { dsimp [weak_operator_topology], apply_instance, }

instance : ring (weak_operator_topology 𝕜 X X) :=
by { dsimp [weak_operator_topology], apply_instance, }

instance : algebra 𝕜 (weak_operator_topology 𝕜 X X) :=
by { dsimp [weak_operator_topology], apply_instance, }

open topological_space

instance : topological_space (weak_operator_topology 𝕜 X Y) :=
⨅ (x : X) (φ : normed_space.dual 𝕜 Y), induced (λ T, φ (T x)) infer_instance

instance : has_continuous_add (weak_operator_topology 𝕜 X Y) :=
sorry

instance : has_continuous_smul 𝕜 (weak_operator_topology 𝕜 X Y) :=
sorry

/-! Composition of operators is separately continuous in each argument (TODO!),
but not jointly continuous, so there is no `topological_ring` structure to construct here. -/

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

namespace star_subalgebra
variables {𝕜 : Type*} [is_R_or_C 𝕜] {H : Type*} [inner_product_space 𝕜 H] [complete_space H]

def strong_closure_as_set (O : star_subalgebra 𝕜 (H →L[𝕜] H)) :
  set (strong_operator_topology 𝕜 H H) :=
closure (O : set (H →L[𝕜] H))

def weak_closure_as_set (O : star_subalgebra 𝕜 (H →L[𝕜] H)) :
  set (weak_operator_topology 𝕜 H H) :=
closure (O : set (H →L[𝕜] H))

end star_subalgebra

namespace star_subalgebra
variables (𝕜 : Type*) [is_R_or_C 𝕜] (H : Type*) --[inner_product_space 𝕜 H] [complete_space H]

example [inner_product_space 𝕜 H] (ι : Type*) [fintype ι] :
  inner_product_space 𝕜 (pi_Lp 2 (λ i : ι, H)) := by apply_instance
example [inner_product_space 𝕜 H] [complete_space H] (ι : Type*) [fintype ι] :
  complete_space (pi_Lp 2 (λ i : ι, H)) := by apply_instance
instance [inner_product_space 𝕜 H] [complete_space H] (ι : Type*) [fintype ι] :
  complete_space (pi_Lp 2 (λ i : ι, H)) := sorry

-- #print star_subalgebra.foo

example [inner_product_space 𝕜 H] (ι : Type*) [fintype ι] : topological_space (pi_Lp 2 (λ i : ι, H)) := by apply_instance
instance (ι : Type*) [fintype ι] [add_group H] : add_group (pi_Lp 2 (λ i : ι, H)) :=
by { dsimp [pi_Lp], apply_instance, }

instance [inner_product_space 𝕜 H] (ι : Type*) [fintype ι] : topological_add_group (pi_Lp 2 (λ i : ι, H)) :=
sorry

example [inner_product_space 𝕜 H] [complete_space H] (ι : Type*) [fintype ι] : star_ring (H →L[𝕜] H) :=
continuous_linear_map.star_ring

example [inner_product_space 𝕜 H] (ι : Type*) [fintype ι] :
  ring ((pi_Lp 2 (λ i : ι, H)) →L[𝕜] (pi_Lp 2 (λ i : ι, H))) :=
by apply_instance
-- continuous_linear_map.ring

-- TIMEOUT!
example [inner_product_space 𝕜 H] [complete_space H] (ι : Type*) [fintype ι] :
  star_ring ((pi_Lp 2 (λ i : ι, H)) →L[𝕜] (pi_Lp 2 (λ i : ι, H))) :=
by apply_instance
-- @continuous_linear_map.star_ring 𝕜 (pi_Lp 2 (λ i : ι, H)) _ _ _

def amplify [inner_product_space 𝕜 H] [complete_space H] (M : star_subalgebra 𝕜 (H →L[𝕜] H)) (ι : Type*) [fintype ι] :
  star_subalgebra 𝕜 ((pi_Lp 2 (λ i : ι, H)) →L[𝕜] (pi_Lp 2 (λ i : ι, H))) :=
sorry

end star_subalgebra

theorem von_neumann_double_commutant
  (𝕜 : Type*) [is_R_or_C 𝕜] (H : Type*) [inner_product_space 𝕜 H] [complete_space H]
  (M : star_subalgebra 𝕜 (H →L[𝕜] H)) :
  (M.commutant.commutant : set (H →L[𝕜] H)) = M.strong_closure_as_set :=
sorry

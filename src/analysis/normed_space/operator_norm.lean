/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel

The space of bounded linear maps

Define the set of bounded linear maps between normed spaces and show basic facts about it. In
particular

(*) define a set L(E,F) of bounded linear maps between k normed spaces,
(*) show that L(E,F) is a vector subspace of E → F,
(*) define the 'operator norm' on L(E,F) and show that it induces the structure of a normed space
    on L(E,F).
-/
import algebra.module
import analysis.normed_space.bounded_linear_maps

variables {k : Type*}
variables {E : Type*} {F : Type*}


-- Define the subspace of bounded linear maps.
section bounded_linear_maps
set_option class.instance_max_depth 50


variables [hnfk : normed_field k] [normed_space k E] [normed_space k F]
include hnfk

def bounded_linear_maps : subspace k (E → F) :=
{ carrier := {A : E → F | is_bounded_linear_map k A},
  zero := is_bounded_linear_map.zero,
  add := assume A B, is_bounded_linear_map.add,
  smul := assume c A, is_bounded_linear_map.smul c }

-- introduce the local notation L(E,F) for the set of bounded linear maps.
local notation `L(` E `,` F `)` := @bounded_linear_maps k E F _ _ _

/-- Coerce bounded linear maps to functions. -/
instance bounded_linear_maps.to_fun : has_coe_to_fun $ L(E,F) :=
{F :=  λ _, (E → F), coe := (λ f, f.val)}

@[extensionality] theorem ext {A B : L(E,F)} (H : ∀ x, A x = B x) : A = B :=
set_coe.ext $ funext H

def to_linear_map (A : L(E, F)) : linear_map _ E F :=
{to_fun := A.val, ..A.property}

@[simp] lemma bounded_linear_maps.map_zero {A : L(E, F)} : A (0 : E) = 0 :=
(to_linear_map A).map_zero

@[simp] lemma bounded_linear_maps.coe_zero {x : E} : (0 : L(E, F)) x = 0 := rfl

@[simp] lemma bounded_linear_maps.smul_coe {A : L(E, F)} {x : E} {c : k} :
  (c • A) x = c • (A x) := rfl

@[simp] lemma bounded_linear_maps.zero_smul {A : L(E, F)} : (0 : k) • A = 0 :=
by ext; simp

@[simp] lemma bounded_linear_maps.one_smul {A : L(E, F)} : (1 : k) • A = A :=
by ext; simp

/-- Bounded linear maps are ... bounded -/
lemma exists_bound (A : L(E,F)) : ∃ c, 0 < c ∧ ∀ x : E, ∥A x∥ ≤ c * ∥x∥ := A.property.bound

end bounded_linear_maps

/-
Now define the operator norm.

The main task is to show that the operator norm is definite, homogeneous, and satisfies the
triangle inequality. This is done after a few preliminary lemmas necessary to deal with csupr.
-/
section operator_norm

variables [normed_field k] [normed_space k E] [normed_space k F]
open lattice set

local notation `L(` E `,` F `)` := @bounded_linear_maps k E F _ _ _

/-- The operator norm of a bounded linear map A : E → F is the sup of ∥A x∥/∥x∥. -/
noncomputable def operator_norm (A : L(E, F)) : ℝ :=
supr (λ x, ∥A x∥/∥x∥)

noncomputable instance bounded_linear_maps.to_has_norm : has_norm L(E,F) :=
{norm := operator_norm}

lemma bdd_above_range_norm_image_div_norm (A : L(E,F)) : bdd_above (range (λ x, ∥A x∥/∥x∥)) :=
let ⟨c, _, H⟩ := (exists_bound A : ∃ c, 0 < c ∧ ∀ x : E, ∥A x∥ ≤ c * ∥x∥) in
bdd_above.mk c $ forall_range_iff.2 $ λx, begin
  by_cases h : ∥x∥ = 0,
  { simp [h, le_of_lt ‹0 < c›] },
  { refine (div_le_iff _).2 (H x),
    simpa [ne.symm h] using le_iff_eq_or_lt.1 (norm_nonneg x) }
end

lemma operator_norm_nonneg (A : L(E,F)) : 0 ≤ ∥A∥ :=
begin
  have : (0 : ℝ) = (λ x, ∥A x∥/∥x∥) 0, by simp,
  rw this,
  exact le_csupr (bdd_above_range_norm_image_div_norm A),
end

set_option class.instance_max_depth 34

/-- This is the fundamental property of the operator norm: ∥A x∥ ≤ ∥A∥ * ∥x∥. -/
theorem bounded_by_operator_norm {A : L(E,F)} {x : E} : ∥A x∥ ≤ ∥A∥ * ∥x∥ :=
begin
  classical, by_cases h : x = 0,
  { simp [h] },
  { have : ∥A x∥/∥x∥ ≤ ∥A∥, from le_csupr (bdd_above_range_norm_image_div_norm A),
    rwa (div_le_iff _) at this,
    have : ∥x∥ ≠ 0, from ne_of_gt ((norm_pos_iff x).mpr h),
    have I := le_iff_eq_or_lt.1 (norm_nonneg x),
    simpa [ne.symm this] using I }
end

/-- If one controls the norm of every A x, then one controls the norm of A. -/
lemma operator_norm_bounded_by {A : L(E,F)} {c : ℝ} (hc : 0 ≤ c) (H : ∀ x, ∥A x∥ ≤ c * ∥x∥) :
  ∥A∥ ≤ c :=
begin
  haveI : nonempty E := ⟨0⟩,
  refine csupr_le (λx, _),
  by_cases h : ∥x∥ = 0,
  { simp [h, hc] },
  { refine (div_le_iff _).2 (H x),
    simpa [ne.symm h] using le_iff_eq_or_lt.1 (norm_nonneg x) }
end

/-- The operator norm satisfies the triangle inequality. -/
theorem operator_norm_triangle (A B : L(E,F)) : ∥A + B∥ ≤ ∥A∥ + ∥B∥ :=
operator_norm_bounded_by (add_nonneg (operator_norm_nonneg A) (operator_norm_nonneg B))
  (assume x,
    calc ∥(A + B) x∥ = ∥A x + B x∥ : by refl
                ... ≤ ∥A x∥ + ∥B x∥ : by exact norm_triangle _ _
                ... ≤ ∥A∥ * ∥x∥ + ∥B∥ * ∥x∥ :
                  add_le_add bounded_by_operator_norm bounded_by_operator_norm
                ... = (∥A∥ + ∥B∥) * ∥x∥ : by ring)

/-- An operator is zero iff its norm vanishes. -/
theorem operator_norm_zero_iff (A : L(E,F)) : ∥A∥ = 0 ↔ A = 0 :=
iff.intro
  (assume : ∥A∥ = 0,
    suffices ∀ x, A x = 0, from ext this,
    assume x,
      have ∥A x∥ ≤ 0, from
        calc ∥A x∥ ≤ ∥A∥ * ∥x∥ : bounded_by_operator_norm
              ... = 0 : by rw[‹∥A∥ = 0›]; ring,
      (norm_le_zero_iff (A x)).mp this)
  (assume : A = 0,
    have ∥A∥ ≤ 0, from operator_norm_bounded_by (le_refl 0) $ by rw this; simp [le_refl],
    le_antisymm this (operator_norm_nonneg A))

section instance_70
-- one needs to increase the max_depth for the following proof
set_option class.instance_max_depth 70

/-- Auxiliary lemma to prove that the operator norm is homogeneous. -/
lemma operator_norm_homogeneous_le (c : k) (A : L(E, F)) : ∥c • A∥ ≤ ∥c∥ * ∥A∥ :=
begin
  apply operator_norm_bounded_by (mul_nonneg (norm_nonneg _) (operator_norm_nonneg _)) (λx, _),
  erw [norm_smul _ _, mul_assoc],
  exact mul_le_mul_of_nonneg_left bounded_by_operator_norm (norm_nonneg _)
end

theorem operator_norm_homogeneous (c : k) (A : L(E, F)) : ∥c • A∥ = ∥c∥ * ∥A∥ :=
begin
  refine le_antisymm (operator_norm_homogeneous_le c A) _,
  by_cases h : ∥c∥ = 0,
  { have : c = 0, from (norm_eq_zero _).1 h,
    have I : ∥(0 : L(E, F))∥ = 0, by rw operator_norm_zero_iff,
    simp only [h],
    simp [this, I] },
  { have h' : c ≠ 0, by simpa [norm_eq_zero] using h,
    have : ∥A∥ ≤ ∥c • A∥ / ∥c∥, from calc
      ∥A∥ = ∥(1 : k) • A∥ : by rw bounded_linear_maps.one_smul
      ... = ∥c⁻¹ • c • A∥ : by rw [smul_smul, inv_mul_cancel h']
      ... ≤ ∥c⁻¹∥ * ∥c • A∥ : operator_norm_homogeneous_le _ _
      ... = ∥c • A∥ / ∥c∥ : by rw [norm_inv, div_eq_inv_mul],
    rwa [le_div_iff, mul_comm] at this,
    simpa [ne.symm h] using le_iff_eq_or_lt.1 (norm_nonneg c) }
end
end instance_70

/-- Expose L(E,F) equipped with the operator norm as normed space. -/
noncomputable instance bounded_linear_maps.to_normed_space : normed_space k L(E,F) :=
normed_space.of_core k L(E,F) {
  norm_eq_zero_iff := operator_norm_zero_iff,
  norm_smul := operator_norm_homogeneous,
  triangle := operator_norm_triangle }

end operator_norm

/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow

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


-- Define the subspace of bounded linear maps, introduce the notation L(E,F) for the set of bounded linear maps.
section bounded_linear_maps

variables [hnfk : normed_field k] [normed_space k E] [normed_space k F]
include hnfk

def bounded_linear_maps : subspace k (E → F) :=
{ carrier := {A : E → F | is_bounded_linear_map A},
  zero := is_bounded_linear_map.zero,
  add := assume A B, is_bounded_linear_map.add,
  smul := assume c A, is_bounded_linear_map.smul c }

local notation `L(` E `,` F `)` := @bounded_linear_maps _ E F _ _ _

/-- Coerce bounded linear maps to functions. -/
instance bounded_linear_maps.to_fun : has_coe_to_fun $ L(E,F) :=
{F :=  λ _, (E → F), coe := (λ f, f.val)}

@[extensionality] theorem ext {A B : L(E,F)} (H : ∀ x, A x = B x) : A = B :=
set_coe.ext $ funext H

/-- Bounded linear maps are ... bounded -/
lemma exists_bound (A : L(E,F)) : ∃ c, c > 0 ∧ ∀ x : E, ∥A x∥ ≤ c * ∥x∥ := A.property.bound

/-- Bounded linear maps are conveniently bounded on the unit ball. -/
lemma exists_bound' (A : L(E,F)) : ∃ c, c > 0 ∧ ∀ x : E, ∥x∥ ≤ 1 → ∥A x∥ ≤ c :=
let ⟨c, _, H⟩ := exists_bound A in
exists.intro c ⟨‹c > 0›,
  assume x _,
  calc ∥A x∥ ≤ c * ∥x∥ : H x
        ... ≤ c * 1 : (mul_le_mul_left ‹c > 0›).mpr ‹∥x∥ ≤ 1›
        ... = c : mul_one c⟩

end bounded_linear_maps

/-
Now define the operator norm. We only do this for normed spaces over ℝ, since we need a
scalar multiplication with reals to prove that ∥A x∥ ≤ ∥A∥ * ∥x∥. It would be enough to
have a vector space over a normed field k with a real scalar multiplication and certain
compatibility conditions.

The main task is to show that the operator norm is definite, homogeneous, and satisfies the
triangle inequality. This is done after a few preliminary lemmas necessary to deal with cSup.
-/
section operator_norm

variables [normed_space ℝ E] [normed_space ℝ F]
open lattice set

local notation `L(` E `,` F `)` := @bounded_linear_maps _ E F _ _ _

noncomputable def to_linear_map (A : L(E, F)) : linear_map _ E F :=
{to_fun := A.val, ..A.property}

/-- The operator norm of a bounded linear map A : E → F is the sup of
    the set ∥A x∥ with ∥x∥ ≤ 1. If E = {0} we set ∥A∥ = 0. -/
noncomputable def operator_norm (A : L(E, F)) : ℝ :=
Sup (image (λ x, ∥A x∥) {x | ∥x∥ ≤ 1})

noncomputable instance bounded_linear_maps.to_has_norm : has_norm L(E,F) :=
{norm := operator_norm}

lemma norm_of_unit_ball_bdd_above (A : L(E,F)) : bdd_above (image (norm ∘ A) {x | ∥x∥ ≤ 1}) :=
let ⟨c, _, H⟩ := (exists_bound' A : ∃ c, c > 0 ∧ ∀ x : E, ∥x∥ ≤ 1 → ∥A x∥ ≤ c) in
bdd_above.mk c
  (assume r ⟨x, (_ : ∥x∥ ≤ 1), (_ : ∥A x∥ = r)⟩,
    show r ≤ c, from
      calc r = ∥A x∥ : eq.symm ‹∥A x∥ = r›
         ... ≤ c : H x ‹∥x∥ ≤ 1›)

lemma zero_in_im_ball (A : L(E,F)) : (0:ℝ) ∈ {r : ℝ | ∃ (x : E), ∥x∥ ≤ 1 ∧ ∥A x∥ = r} :=
have A 0 = 0, from (to_linear_map A).map_zero,
exists.intro (0:E) $ and.intro (by rw[norm_zero]; exact zero_le_one) (by rw[‹A 0 = 0›]; simp)

lemma operator_norm_nonneg (A : L(E,F)) : 0 ≤ ∥A∥ :=
have (0:ℝ) ∈ _, from zero_in_im_ball A,
show 0 ≤ Sup (image (norm ∘ A) {x | ∥x∥ ≤ 1}), from
let ⟨c, _, H⟩ := (exists_bound' A : ∃ c, c > 0 ∧ ∀ x : E, ∥x∥ ≤ 1 → ∥A x∥ ≤ c) in
le_cSup (norm_of_unit_ball_bdd_above A) ‹(0:ℝ) ∈ _›

lemma bounded_by_operator_norm_on_unit_vector (A : L(E, F)) {x : E} (_ : ∥x∥ = 1) : ∥A x∥ ≤ ∥A∥ :=
show ∥A x∥ ≤ Sup (image (norm ∘ A) {x | ∥x∥ ≤ 1}), from
let ⟨c, _, _⟩ := (exists_bound A : ∃ c, c > 0 ∧ ∀ x : E, ∥ A x ∥ ≤ c * ∥ x ∥) in
have ∥A x∥ ∈ (image (norm ∘ A) {x | ∥x∥ ≤ 1}), from mem_image_of_mem _ $ le_of_eq ‹∥x∥ = 1›,
le_cSup (norm_of_unit_ball_bdd_above A) ‹∥A x∥ ∈ _›

/-- This is the fundamental property of the operator norm: ∥A x∥ ≤ ∥A∥ * ∥x∥. -/
theorem bounded_by_operator_norm {A : L(E,F)} {x : E} : ∥A x∥ ≤ ∥A∥ * ∥x∥ :=
have A 0 = 0, from (to_linear_map A).map_zero,
classical.by_cases
  (assume : x = (0:E),
    show ∥A x∥ ≤ ∥A∥ * ∥x∥, by rw[‹x = 0›, ‹A 0 = 0›, norm_zero, norm_zero, mul_zero]; exact le_refl 0)
  (assume : x ≠ (0:E),
    have ∥x∥ ≠ 0, from ne_of_gt $ (norm_pos_iff x).mpr ‹x ≠ 0›,
    have ∥∥x∥⁻¹∥ = ∥x∥⁻¹, from abs_of_nonneg $ inv_nonneg.mpr $ norm_nonneg x,
    have ∥∥x∥⁻¹•x∥ = 1, begin rw[norm_smul, ‹∥∥x∥⁻¹∥ = ∥x∥⁻¹›], exact inv_mul_cancel ‹∥x∥ ≠ 0› end,
    calc ∥A x∥ = (∥x∥ * ∥x∥⁻¹) * ∥A x∥ : by rw[mul_inv_cancel ‹∥x∥ ≠ 0›]; ring
          ... = ∥∥x∥⁻¹∥ * ∥A x∥ * ∥x∥  : by rw[‹∥∥x∥⁻¹∥ = ∥x∥⁻¹›]; ring
          ... = ∥∥x∥⁻¹• A x ∥ * ∥x∥    : by rw[←normed_space.norm_smul ∥x∥⁻¹ (A x)]
          ... = ∥A (∥x∥⁻¹• x)∥ * ∥x∥   : by {
                                          change  ∥∥x∥⁻¹ • A.val x∥ * ∥x∥ = ∥A.val (∥x∥⁻¹ • x)∥ * ∥x∥,
                                          rw A.property.smul}
          ... ≤ ∥A∥ * ∥x∥              : (mul_le_mul_right ((norm_pos_iff x).mpr ‹x ≠ 0›)).mpr
                                          (bounded_by_operator_norm_on_unit_vector A ‹∥∥x∥⁻¹•x∥ = 1›))

lemma bounded_by_operator_norm_on_unit_ball (A : L(E, F)) {x : E} (_ : ∥x∥ ≤ 1) : ∥A x∥ ≤ ∥A∥ :=
calc ∥A x∥ ≤ ∥A∥ * ∥x∥ : bounded_by_operator_norm
        ... ≤ ∥A∥ * 1 : mul_le_mul_of_nonneg_left ‹∥x∥ ≤ 1› (operator_norm_nonneg A)
        ... = ∥A∥ : mul_one ∥A∥

lemma operator_norm_bounded_by {A : L(E,F)} (c : nnreal) :
  (∀ x : E, ∥x∥ ≤ 1 → ∥A x∥ ≤ (c:ℝ)) → ∥A∥ ≤ c :=
assume H : ∀ x : E, ∥x∥ ≤ 1 → ∥A x∥ ≤ c,
suffices Sup (image (norm ∘ A) {x | ∥x∥ ≤ 1}) ≤ c, by assumption,
cSup_le (set.ne_empty_of_mem $ zero_in_im_ball A)
  (show ∀ (r : ℝ), r ∈ (image (norm ∘ A) {x | ∥x∥ ≤ 1}) → r ≤ c, from
    assume r ⟨x, _, _⟩,
      calc r = ∥A x∥ : eq.symm ‹_›
         ... ≤ c : H x ‹_›)

theorem operator_norm_triangle (A : L(E,F)) (B : L(E,F)) : ∥A + B∥ ≤ ∥A∥ + ∥B∥ :=
operator_norm_bounded_by (⟨∥A∥, operator_norm_nonneg A⟩ + ⟨∥B∥, operator_norm_nonneg B⟩)
  (assume x _, by exact
    calc ∥(A + B) x∥ = ∥A x + B x∥ : by refl
                ... ≤ ∥A x∥ + ∥B x∥ : by exact norm_triangle _ _
                ... ≤ ∥A∥ + ∥B∥ : by exact add_le_add (bounded_by_operator_norm_on_unit_ball A ‹_›)
                                            (bounded_by_operator_norm_on_unit_ball B ‹_›))

theorem operator_norm_zero_iff (A : L(E,F)) : ∥A∥ = 0 ↔ A = 0 :=
have A 0 = 0, from (to_linear_map A).map_zero,
iff.intro
  (assume : ∥A∥ = 0,
    suffices ∀ x, A x = 0, from ext this,
    assume x,
      have ∥A x∥ ≤ 0, from
        calc ∥A x∥ ≤ ∥A∥ * ∥x∥ : bounded_by_operator_norm
              ... = 0 : by rw[‹∥A∥ = 0›]; ring,
      (norm_le_zero_iff (A x)).mp this)
  (assume : A = 0,
    let M := {r : ℝ | ∃ (x : E), ∥x∥ ≤ 1 ∧ ∥A x∥ = r} in
    -- note that we have M = (image (norm ∘ A) {x | ∥x∥ ≤ 1}), from rfl
    suffices Sup M = 0, by assumption,
    suffices M = {0}, by rw[this]; exact cSup_singleton 0,
    (set.ext_iff M {0}).mpr $ assume r, iff.intro
      (assume : ∃ (x : E), ∥x∥ ≤ 1 ∧ ∥A x∥ = r,
        let ⟨x, _, _⟩ := this in
          have h : ∥(0:F)∥ = r, by rwa[‹A=0›] at *,
          by finish)
      (assume : r ∈ {0},
        have r = 0, from set.eq_of_mem_singleton this,
        exists.intro (0:E) $ ⟨by rw[norm_zero]; exact zero_le_one, by rw[this, ‹A 0 = 0›]; simp⟩))

theorem operator_norm_homogeneous (c : ℝ) (A : L(E, F)) : ∥c • A∥ = ∥c∥ * ∥A∥ :=
-- ∥c • A∥ is the supremum of the image of the map x ↦ ∥c • A x∥ on the unit ball in E
-- we show that this is the same as ∥c∥ * ∥A∥ by showing 1) and 2):
-- 1) ∥c∥ * ∥A∥ is an upper bound for the image of x ↦ ∥c • A x∥ on the unit ball
-- 2) any w < ∥c∥ * ∥A∥ is not an upper bound (this is equivalent to showing that every upper bound is ≥ ∥c∥ * ∥A∥)
suffices (∀ a ∈ _, a ≤ ∥c∥ * ∥A∥) ∧ (∀ (ub : ℝ), (∀ a ∈ _, a ≤ ub) → ∥c∥ * ∥A∥ ≤ ub), from
  cSup_intro' (show _ ≠ ∅, from set.ne_empty_of_mem $ zero_in_im_ball _) this.1 this.2,
and.intro
  (show ∀ a ∈ image (λ x, ∥(c • A) x∥) {x : E | ∥x∥ ≤ 1}, a ≤ ∥c∥ * ∥A∥, from
    assume a (hₐ : ∃ (x : E), ∥x∥ ≤ 1 ∧ ∥(c • A) x∥ = a),
      let ⟨x, _, _⟩ := hₐ in
        calc a = ∥c • A x∥    : eq.symm ‹_›
           ... = ∥c∥ * ∥A x∥   : by rw[←norm_smul c (A x)]; refl
           ... ≤ ∥c∥ * ∥A∥     : mul_le_mul_of_nonneg_left
                                   (bounded_by_operator_norm_on_unit_ball A ‹∥x∥ ≤ 1›)
                                   (norm_nonneg c))
  (show ∀ (ub : ℝ), (∀ a ∈ image (λ (x : E), ∥(c • A) x∥) {x : E | ∥x∥ ≤ 1}, a ≤ ub) → ∥c∥ * ∥A∥ ≤ ub, from
    assume u u_is_ub,
      classical.by_cases
        (assume : c = 0,
          calc ∥c∥ * ∥A∥ = 0 : by rw[‹c=0›, norm_zero, zero_mul]
                    ... ≤ u : u_is_ub (0:ℝ) $ zero_in_im_ball _)
        (assume : c ≠ 0,
          have ∥c∥ ≠ 0, from ne_of_gt $ (norm_pos_iff c).mpr ‹c ≠ 0›,
          have bla : u = ∥c∥ * (∥c∥⁻¹ * u), by rw[←mul_assoc, mul_inv_cancel ‹∥c∥ ≠ 0›, one_mul],
          suffices ∥A∥ ≤ ∥c∥⁻¹ * u, from
            have u = ∥c∥ * (∥c∥⁻¹ * u), by rw[←mul_assoc, mul_inv_cancel ‹∥c∥ ≠ 0›, one_mul],
            by rw[this]; exact mul_le_mul_of_nonneg_left ‹_› (norm_nonneg c),
          cSup_le
            (set.ne_empty_of_mem $ zero_in_im_ball _)
            (assume n (H : ∃ (x : E), ∥x∥ ≤ 1 ∧ ∥A x∥ = n),
              let ⟨x, _, _⟩ := H in
              calc n = ∥A x∥             : eq.symm ‹∥A x∥ = n›
                 ... = ∥c∥⁻¹ * ∥c • A x∥ : by rw[norm_smul, ←mul_assoc, inv_mul_cancel ‹∥c∥ ≠ 0›, one_mul]
                 ... ≤ ∥c∥⁻¹ * u         : mul_le_mul_of_nonneg_left (u_is_ub ∥c • A x∥ ⟨x, ‹∥x∥ ≤ 1›, rfl⟩) $
                                                                     inv_nonneg.mpr $ norm_nonneg c)))

/-- Expose L(E,F) equipped with the operator norm as normed space. -/
noncomputable instance bounded_linear_maps.to_normed_space : normed_space ℝ L(E,F) :=
normed_space.of_core ℝ L(E,F) {
  norm_eq_zero_iff := operator_norm_zero_iff,
  norm_smul := operator_norm_homogeneous,
  triangle := operator_norm_triangle
}

end operator_norm

/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov
-/
import analysis.normed_space.reflection
import topology.instances.real_vector_space

/-!
# Mazur-Ulam Theorem

Mazur-Ulam theorem states that an isometric bijection between two normed spaces over `ℝ` is affine.
Since `mathlib` has no notion of an affine map (yet?), we formalize it in two definitions:

* `isometric.to_real_linear_equiv_of_map_zero` : given `E ≃ᵢ F` sending `0` to `0`,
  returns `E ≃L[ℝ] F` with the same `to_fun` and `inv_fun`;
* `isometric.to_real_linear_equiv` : given `f : E ≃ᵢ F`,
  returns `g : E ≃L[ℝ] F` with `g x = f x - f 0`.

The formalization is based on [Jussi Väisälä, *A Proof of the Mazur-Ulam Theorem*][Vaisala_2003].

## Tags

isometry, affine map, linear map
-/

variables {E : Type*} [normed_group E] [normed_space ℝ E]
  {F : Type*} [normed_group F] [normed_space ℝ F]

open set

noncomputable theory

namespace isometric

/-- If an isometric self-homeomorphism of a normed vector space over `ℝ` fixes `x` and `y`,
then it fixes the midpoint of `[x, y]`. This is a lemma for a more general Mazur-Ulam theorem,
see below. -/
lemma midpoint_fixed {x y : E} :
  ∀ e : E ≃ᵢ E, e x = x → e y = y → e (midpoint ℝ x y) = midpoint ℝ x y :=
begin
  set z := midpoint ℝ x y,
  set s := { e : E ≃ᵢ E | e x = x ∧ e y = y },
  set c := ⨆ e : s, dist (e z) z,
  haveI : nonempty s := ⟨⟨isometric.refl E, rfl, rfl⟩⟩,
  have A : bdd_above (range $ λ e : s, dist (e z) z),
  { refine ⟨dist x z + dist x z, forall_range_iff.2 $ λ e, _⟩,
    calc dist (e z) z ≤ dist (e z) x + dist x z : dist_triangle (e z) x z
    ... = dist (e x) (e z) + dist x z : by erw [e.2.1, dist_comm]
    ... = _ : by erw [e.1.dist_eq x z] },
  suffices : c ≤ 0,
  { intros e hx hy,
    have A : dist (e z) z ≤ c, from @le_csupr _ _ _ _ A ⟨e, hx, hy⟩,
    exact dist_le_zero.1 (le_trans A this) },
  suffices : c ≤ c / 2, { linarith },
  apply csupr_le,
  set g : E ≃ᵢ E := reflection z,
  rintros ⟨e, he⟩,
  apply le_div_of_mul_le (zero_lt_two : 0 < (2:ℝ)),
  have : ((e.trans g).trans e.symm).trans g ∈ s,
    by split; simp [he.1, he.2, (e.symm_apply_eq).2 he.1.symm, (e.symm_apply_eq).2 he.2.symm],
  dsimp,
  rw [mul_comm, dist_comm, ← reflection_dist_self, ← e.symm.dist_eq, e.symm_apply_apply,
    ← reflection_dist_fixed],
  exact @le_csupr _ _ _ _ A ⟨_, this⟩
end

/-- Mazur-Ulam Theorem: if `f` is an isometric bijection between two normed vector spaces
over `ℝ` and `f 0 = 0`, then `f` is a linear equivalence. -/
def to_real_linear_equiv_of_map_zero (f : E ≃ᵢ F) (h0 : f 0 = 0) :
  E ≃L[ℝ] F :=
begin
  refine { .. (add_monoid_hom.of_map_midpoint ℝ ℝ f h0 _).to_real_linear_map f.continuous,
    .. f.to_homeomorph },
  intros x y,
  set e : E ≃ᵢ E := ((f.trans $ reflection $ midpoint ℝ (f x) (f y)).trans f.symm).trans
    (reflection $ midpoint ℝ x y),
  have hx : e x = x, by simp,
  have hy : e y = y, by simp,
  have hm := e.midpoint_fixed hx hy,
  simp only [e, trans_apply] at hm,
  rwa [← eq_symm_apply, reflection_symm, reflection_self, symm_apply_eq, reflection_fixed_iff] at hm
end

@[simp] lemma coe_to_real_linear_equiv_of_map_zero (f : E ≃ᵢ F) (h0 : f 0 = 0) :
  ⇑(f.to_real_linear_equiv_of_map_zero h0) = f := rfl

@[simp] lemma coe_to_real_linear_equiv_of_map_zero_symm (f : E ≃ᵢ F) (h0 : f 0 = 0) :
  ⇑(f.to_real_linear_equiv_of_map_zero h0).symm = f.symm := rfl

/-- Mazur-Ulam Theorem: if `f` is an isometric bijection between two normed vector spaces
over `ℝ`, then `x ↦ f x - f 0` is a linear equivalence. -/
def to_real_linear_equiv (f : E ≃ᵢ F) : E ≃L[ℝ] F :=
(f.trans (isometric.add_right (f 0)).symm).to_real_linear_equiv_of_map_zero (sub_self $ f 0)

@[simp] lemma to_real_linear_equiv_apply (f : E ≃ᵢ F) (x : E) :
  (f.to_real_linear_equiv : E → F) x = f x - f 0 := rfl

@[simp] lemma to_real_linear_equiv_symm_apply (f : E ≃ᵢ F) (y : F) :
  (f.to_real_linear_equiv.symm : F → E) y = f.symm (y + f 0) := rfl

end isometric

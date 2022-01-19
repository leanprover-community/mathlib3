/-
Copyright (c) 2022 Daniel Roca González. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Roca González
-/
import analysis.inner_product_space.projection
import analysis.inner_product_space.dual
import analysis.normed_space.banach
import topology.metric_space.antilipschitz

/-!
# The Lax-Milgram Theorem


We consider an Hilbert space `V` over `ℝ`
equipped with a bounded bilinear form `B : V →L[ℝ] V →L[ℝ] ℝ`.
For every such form we define the
`lax_milgram_map : V →L[ℝ] V`,
which is defined by the property `B (lax_milgram_map B v) w = ⟪v, w⟫`
using the Fréchet-Riesz representation theorem.
We also define a property `is_coercive` for (B : V →L[ℝ] V →L[ℝ] ℝ),
such that `is_coercive B` iff
`∃ C, (0 < C) ∧ ∀ u, C * ∥u∥ * ∥u∥ ≤ B u u`.

Under the hypothesis that `B` i
we prove the Lax-Milgram theorem:
that is, the `lax_milgram_map` can be upgraded to a continuous equivalence `lax_milgram`

## References

* We follow the notes of Peter Howard's Spring 2020 *M612: Partial Differential Equations* lecture,
  see[howard]


## Tags

dual, Lax-Milgram
-/

noncomputable theory



open_locale classical complex_conjugate
open is_R_or_C continuous_linear_map linear_map linear_equiv

universe u

/--
A bounded bilinear form in an inner product space is coercive
if there is some positive constant C such that `C * ∥u∥ * ∥u∥ ≤ B u u`.
-/
def is_coercive
  {V : Type u} [inner_product_space ℝ V] (B : V →L[ℝ] V →L[ℝ] ℝ) : Prop :=
∃ C, (0 < C) ∧ ∀ u, C * ∥u∥ * ∥u∥ ≤ B u u

namespace lax_milgram
variables {V : Type u} [inner_product_space ℝ V] [complete_space V]
variables (B : V →L[ℝ] V →L[ℝ] ℝ)


/--
The Lax-;ilgram map of a bounded bilinear operator: for all `v : V`
there exists an `lax_milgram_map B v` is the element of `V`
such that `⟪lax_milgram_map B v, w⟫ = B v w`.
This element is obtained using `inner_product_space.to_dual`.
-/
def lax_milgram_map (B : V →L[ℝ] V →L[ℝ] ℝ) : V →L[ℝ] V :=
(inner_product_space.to_dual ℝ V).symm.to_continuous_linear_equiv.to_continuous_linear_map ∘L B


@[simp]
lemma lax_milgram_map_apply (v w : V) : B v w = inner (lax_milgram_map B v) w :=
by {dunfold lax_milgram_map, simp,}

lemma unique_lax_milgram_map (v f : V)
  (is_lax_milgram : (∀ w, inner f w = B v w)) :
  f = lax_milgram_map B v :=
begin
  refine inner_product_space.ext_inner_right ℝ _,
  intro w,
  rw ←lax_milgram_map_apply,
  exact is_lax_milgram w,
end

variables {B}

lemma antilipschitz_of_lax_milgram (coercive : is_coercive B) :
  ∃ C : ℝ, 0 < C ∧ antilipschitz_with C.to_nnreal (lax_milgram_map B) :=
begin
  rcases coercive with ⟨C, C_pos, coercivity⟩,
  refine ⟨C⁻¹, inv_pos.mpr C_pos, _⟩,
  refine linear_map.antilipschitz_of_bound ↑(lax_milgram_map B) _,
  intros v,
  by_cases h : 0 < ∥v∥,
  {
    rw [←mul_le_mul_left C_pos, ←mul_assoc],
    simp only [real.coe_to_nnreal', normed_group.dist_eq, max_eq_left_of_lt (inv_pos.mpr C_pos)],
    rw [mul_inv_cancel, one_mul],
    show C ≠ 0, by linarith,
    refine (mul_le_mul_right h).mp _,
    exact calc
         C * ∥v∥ * ∥v∥
         ≤ B v v                         : coercivity v
    ...  = inner (lax_milgram_map B v) v : by simp
    ...  ≤ ∥lax_milgram_map B v ∥ * ∥v∥    : real_inner_le_norm (lax_milgram_map B v) v,
  },
  {
    have : v = 0 := by simpa using h,
    simp [this],
  }
end

lemma injective (coercive : is_coercive B) : (lax_milgram_map B).ker = ⊥ :=
begin
  simp only [submodule.eq_bot_iff, continuous_linear_map.mem_ker],
  intros v zero_of_image,
  rw ←norm_le_zero_iff,
  rcases antilipschitz_of_lax_milgram coercive with ⟨C, C_pos, antilipschitz⟩,
  have :=  antilipschitz v 0,
  simpa [edist_dist, zero_of_image, norm_zero] using this,
end

lemma closed_range (coercive : is_coercive B) : is_closed ((lax_milgram_map B).range : set V) :=
begin
  rcases antilipschitz_of_lax_milgram coercive with ⟨_, _, antilipschitz⟩,
  exact antilipschitz.is_closed_range (lax_milgram_map B).uniform_continuous,
end

lemma surjective (coercive : is_coercive B): (lax_milgram_map B).range = ⊤ :=
begin
  haveI := (closed_range coercive).complete_space_coe,
  rw ← (lax_milgram_map B).range.orthogonal_orthogonal,
  rw submodule.eq_top_iff',
  intros v w mem_w_orthogonal,
  rcases coercive with ⟨C, C_ge_0, coercivity⟩,
  have : C * ∥w∥ * ∥w∥ ≤ 0 :=
  calc C * ∥w∥ * ∥w∥
        ≤ B w w                         : coercivity w
  ...  = inner (lax_milgram_map B w) w  : by simp
  ...  = 0                              : mem_w_orthogonal _ ⟨w, rfl⟩,
  have : ∥w∥ * ∥w∥ ≤ 0 := by nlinarith,
  have h : ∥w∥ = 0 := by nlinarith [norm_nonneg w],
  have w_eq_zero : w = 0 := by simpa using h,
  simp [w_eq_zero],
end


def lax_milgram (coercive : is_coercive B) : V ≃L[ℝ] V :=
continuous_linear_equiv.of_bijective
  (lax_milgram_map B)
  (injective coercive)
  (surjective coercive)


end lax_milgram

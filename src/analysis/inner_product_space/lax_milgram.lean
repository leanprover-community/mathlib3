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
which is defined by the property `⟪lax_milgram_map B v, w⟫ = B v w`
using the Fréchet-Riesz representation theorem.
We also define a property `is_coercive` for `B : V →L[ℝ] V →L[ℝ] ℝ`,
such that `is_coercive B` iff
`∃ C, (0 < C) ∧ ∀ u, C * ∥u∥ * ∥u∥ ≤ B u u`.

Under the hypothesis that `B` is coercive
we prove the Lax-Milgram theorem:
that is, the `lax_milgram_map` can be upgraded
to a continuous equivalence `lax_milgram_equiv : V ≃L[ℝ] V`.

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
The Lax-Milgram map of a bounded bilinear operator: for all `v : V`
`lax_milgram_map B v` is the unique element of `V`
such that `⟪lax_milgram_map B v, w⟫ = B v w`.
This element is obtained using `inner_product_space.to_dual`.
-/
def lax_milgram_map (B : V →L[ℝ] V →L[ℝ] ℝ) : V →L[ℝ] V :=
↑(id (inner_product_space.to_dual ℝ V).symm.to_continuous_linear_equiv : (V →L[ℝ] ℝ) ≃L[ℝ] V) ∘L B

@[simp]
lemma lax_milgram_map_apply (v w : V) : inner (lax_milgram_map B v) w = B v w :=
by simp [lax_milgram_map]

lemma unique_lax_milgram_map {v f : V}
  (is_lax_milgram : (∀ w, inner f w = B v w)) :
  f = lax_milgram_map B v :=
begin
  refine inner_product_space.ext_inner_right ℝ _,
  intro w,
  rw lax_milgram_map_apply,
  exact is_lax_milgram w,
end

variables {B}

lemma bounded_below (coercive : is_coercive B) :
  ∃ C, 0 < C ∧ ∀ v, C * ∥v∥ ≤ ∥lax_milgram_map B v∥ :=
begin
  rcases coercive with ⟨C, C_ge_0, coercivity⟩,
  refine ⟨C, C_ge_0, _⟩,
  intro v,
  by_cases h : 0 < ∥v∥,
  {
    refine (mul_le_mul_right h).mp _,
    exact calc C * ∥v∥ * ∥v∥
               ≤ B v v                         : coercivity v
    ...        = inner (lax_milgram_map B v) v : by simp
    ...        ≤ ∥lax_milgram_map B v∥ * ∥v∥     : real_inner_le_norm (lax_milgram_map B v) v,
  },
  {
    have : v = 0 := by simpa using h,
    simp [this],
  }
end

lemma antilipschitz_of_lax_milgram (coercive : is_coercive B) :
  ∃ C : nnreal, 0 < C ∧ antilipschitz_with C (lax_milgram_map B) :=
begin -- I still want to golf this somewhat
  rcases bounded_below coercive with ⟨C, C_pos, below_bound⟩,
  have C_nonneg : 0 ≤ C⁻¹ := le_of_lt (inv_pos.mpr C_pos),
  refine ⟨(C⁻¹).to_nnreal, _, _⟩,
  simpa [nnreal.coe_pos] using C_pos,
  refine linear_map.antilipschitz_of_bound ↑(lax_milgram_map B) _,
  intros v,
  have := below_bound v,
  rw [←mul_le_mul_left C_pos, ←mul_assoc],
  simp only [max_eq_left_of_lt (inv_pos.mpr C_pos), real.coe_to_nnreal',
    continuous_linear_map.to_linear_map_eq_coe, continuous_linear_map.coe_coe, inv_pos],
  rwa [mul_inv_cancel, one_mul], linarith,
end

lemma ker_eq_bot (coercive : is_coercive B) : (lax_milgram_map B).ker = ⊥ :=
begin
  rw [←ker_coe, linear_map.ker_eq_bot],
  rcases antilipschitz_of_lax_milgram coercive with ⟨_, _, antilipschitz⟩,
  exact antilipschitz_with.injective antilipschitz,
end

lemma closed_range (coercive : is_coercive B) : is_closed ((lax_milgram_map B).range : set V) :=
begin
  rcases antilipschitz_of_lax_milgram coercive with ⟨_, _, antilipschitz⟩,
  exact antilipschitz.is_closed_range (lax_milgram_map B).uniform_continuous,
end

lemma range_eq_top (coercive : is_coercive B): (lax_milgram_map B).range = ⊤ :=
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

/--
The Lax-Milgram equivalence of a coercive bounded bilinear operator:
for all `v : V`, `lax_milgram_equiv B v` is the unique element `V`
such that `⟪lax_milgram_equiv B v, w⟫ = B v w`.
The Lax-Milgram theorem states that this is a continuous equivalence.
-/
def lax_milgram_equiv (coercive : is_coercive B) : V ≃L[ℝ] V :=
continuous_linear_equiv.of_bijective
  (lax_milgram_map B)
  (ker_eq_bot coercive)
  (range_eq_top coercive)


@[simp]
lemma lax_milgram_equiv_apply (coercive : is_coercive B) (v w : V) :
  inner (lax_milgram_equiv coercive v) w = B v w :=
lax_milgram_map_apply B v w

lemma unique_lax_milgram_equiv (coercive : is_coercive B) {v f : V}
  (is_lax_milgram : (∀ w, inner f w = B v w)) :
  f = lax_milgram_equiv coercive v :=
unique_lax_milgram_map B is_lax_milgram

end lax_milgram

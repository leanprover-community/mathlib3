/-
Copyright (c) 2022 Daniel Roca González. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Roca González
-/
import analysis.inner_product_space.projection
import analysis.inner_product_space.dual
import analysis.normed_space.banach

/-!
# The The Lax-Milgram Theorem


We consider an Hilbert space `V` over `ℝ`
equipped with a bilinear form `B : V →L[ℝ] V →L[ℝ] ℝ`.
For every such form we define the
`lax_milgram_map : V →L[ℝ] V`,
which is defined by the property `B (lax_milgram_map B v) w = ⟪v, w⟫`
using the Fréchet-Riesz representation theorem.

Under the hypothesis that `B` is *coercive* (fulfills `is_coercive`),
we prove the Lax-Milgram theorem:
that is, the `lax_milgram_map` can be upgraded to a continuous equivalence `lax_milgram`

## References

TODO cite the slides


## Tags

dual, Lax-Milgram
-/

noncomputable theory



open_locale classical complex_conjugate
open is_R_or_C continuous_linear_map linear_map linear_equiv

universe u
def is_coercive
  {V : Type u} [inner_product_space ℝ V] [complete_space V] (B : V →L[ℝ] V →L[ℝ] ℝ) : Prop :=
∃ C, (0 < C) ∧ ∀ u, C * ∥u∥ * ∥u∥ ≤ B u u


namespace lax_milgram
variables {V : Type u} [inner_product_space ℝ V] [complete_space V]
variables (B : V →L[ℝ] V →L[ℝ] ℝ)


def lax_milgram_map (B : V →L[ℝ] V →L[ℝ] ℝ) : V →L[ℝ] V :=
(inner_product_space.to_dual ℝ V).symm.to_continuous_linear_equiv.to_continuous_linear_map ∘L B


@[simp]
lemma lax_milgram_map_apply (v w : V) : B v w = inner (lax_milgram_map B v) w :=
begin
  dunfold lax_milgram_map,
  simp,
end

variables {B}

lemma injective (coercive : is_coercive B) : (lax_milgram_map B).ker = ⊥ :=
begin
  simp only [submodule.eq_bot_iff, continuous_linear_map.mem_ker],
  intros v,
  contrapose,
  simp_rw [← ne.def, ← norm_pos_iff],
  intros hv,
  rcases coercive with ⟨C, C_ge_0, coercivity⟩,
  have squared : C * ∥v∥ * ∥v∥ ≤ ∥lax_milgram_map B v ∥ * ∥v∥ :=
  calc C * ∥v∥*∥v∥
       ≤ B v v                         : coercivity v
  ...  = inner (lax_milgram_map B v) v : by simp
  ...  ≤ ∥lax_milgram_map B v ∥ * ∥v∥    : real_inner_le_norm (lax_milgram_map B v) v,
  have coerced := (mul_le_mul_right hv).mp squared,
  exact calc 0 < C * ∥v∥                  : mul_pos C_ge_0 hv
  ...          ≤ ∥(lax_milgram_map B) v∥  : coerced,
end


lemma closed_range (coercive : is_coercive B) : is_closed ((lax_milgram_map B).range : set V) :=
begin
  rw ←is_seq_closed_iff_is_closed,
  apply is_seq_closed_of_def,
  intros x y mem_range_x tendsto_y,
  sorry,
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
        ≤ B w w                          : coercivity w
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

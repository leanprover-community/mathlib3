/-
Copyright (c) 2022 Jesse Reimann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Reimann, Kalle Kytölä
-/
import topology.continuous_function.bounded
import topology.urysohns_bounded
import measure_theory.measure.content


/-!
#  Riesz–Markov–Kakutani representation theorem

This file will prove different versions of the Riesz-Markov-Kakutani representation theorem.
The theorem is first proven for compact spaces, from which the statements about linear functionals
on bounded continuous functions or compactly supported functions on locally compact spaces follow.

To make use of the existing API, the measure is constructed from a content `λ` on the
compact subsets of the space X, rather than the usual construction of open sets in the literature.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/

noncomputable theory

open_locale bounded_continuous_function nnreal ennreal
open set function topological_space measure_theory

variables {X : Type*} [topological_space X]
variables (Λ : (X →ᵇ ℝ≥0) →ₗ[ℝ≥0] ℝ≥0)

/-! ### Construction of the content: -/

/-- Given a positive linear functional Λ on X, for `K ⊆ X` compact define
`λ(K) = inf {Λf | 1≤f on K}`. When X is a compact Hausdorff space, this will be shown to be a
content, and will be shown to agree with the Riesz measure on the compact subsets `K ⊆ X`. -/
def riesz_content_aux : (compacts X) → ℝ≥0 :=
λ K, Inf (Λ '' {f : X →ᵇ ℝ≥0 | ∀ x ∈ K, (1 : ℝ≥0) ≤ f x})

section riesz_monotone

/-- For any compact subset `K ⊆ X`, there exist some bounded continuous nonnegative
functions f on X such that `f ≥ 1` on K. -/
lemma riesz_content_aux_image_nonempty (K : compacts X) :
  (Λ '' {f : X →ᵇ ℝ≥0 | ∀ x ∈ K, (1 : ℝ≥0) ≤ f x}).nonempty :=
begin
  rw nonempty_image_iff,
  use (1 : X →ᵇ ℝ≥0),
  intros x x_in_K,
  simp only [bounded_continuous_function.coe_one, pi.one_apply],
end

/-- Riesz content λ (associated with a positive linear functional Λ) is
monotone: if `K₁ ⊆ K₂` are compact subsets in X, then `λ(K₁) ≤ λ(K₂)`. -/
lemma riesz_content_aux_mono {K₁ K₂ : compacts X} (h : K₁ ≤ K₂) :
  riesz_content_aux Λ K₁ ≤ riesz_content_aux Λ K₂ :=
cInf_le_cInf (order_bot.bdd_below _) (riesz_content_aux_image_nonempty Λ K₂)
  (image_subset Λ (set_of_subset_set_of.mpr (λ f f_hyp x x_in_K₁, f_hyp x (h x_in_K₁))))

end riesz_monotone

section riesz_subadditive

/-- Any bounded continuous nonnegative f such that `f ≥ 1` on K gives an upper bound on the
content of K; namely `λ(K) ≤ Λ f`. -/
lemma riesz_content_aux_le {K : compacts X}
  {f : X →ᵇ ℝ≥0} (h : ∀ x ∈ K, (1 : ℝ≥0) ≤ f x) :
  riesz_content_aux Λ K ≤ Λ f := cInf_le (order_bot.bdd_below _) ⟨f, ⟨h, rfl⟩⟩

/-- The Riesz content can be approximated arbitrarily well by evaluating the positive linear
functional on test functions: for any `ε > 0`, there exists a bounded continuous nonnegative
function f on X such that `f ≥ 1` on K and such that `λ(K) ≤ Λ f < λ(K) + ε`. -/
lemma exists_lt_riesz_content_aux_add_pos (K : compacts X)
  {ε : ℝ≥0} (εpos : 0 < ε) :
  ∃ (f : X →ᵇ ℝ≥0), (∀ x ∈ K, (1 : ℝ≥0) ≤ f x) ∧ Λ f < riesz_content_aux Λ K + ε :=
begin
  --choose a test function `f` s.t. `Λf = α < λ(K) + ε`
  obtain ⟨α, ⟨⟨f, f_hyp⟩, α_hyp⟩⟩ :=
    exists_lt_of_cInf_lt (riesz_content_aux_image_nonempty Λ K)
    (lt_add_of_pos_right (riesz_content_aux Λ K) εpos),
  refine ⟨f, f_hyp.left, _ ⟩,
  rw f_hyp.right,
  exact α_hyp,
end

/-- The Riesz content λ associated to a given positive linear functional Λ is
finitely subadditive: `λ(K₁ ∪ K₂) ≤ λ(K₁) + λ(K₂)` for any compact subsets `K₁, K₂ ⊆ X`. -/
lemma riesz_content_aux_sup_le (K1 K2 : compacts X) :
  riesz_content_aux Λ (K1 ⊔ K2) ≤ riesz_content_aux Λ (K1) + riesz_content_aux Λ (K2) :=
begin
  apply nnreal.le_of_forall_pos_le_add,
  intros ε εpos,
  --get test functions s.t. `λ(Ki) ≤ Λfi ≤ λ(Ki) + ε/2, i=1,2`
  obtain ⟨f1, f_test_function_K1⟩ := exists_lt_riesz_content_aux_add_pos Λ K1
    (nnreal.half_pos εpos),
  obtain ⟨f2, f_test_function_K2⟩ := exists_lt_riesz_content_aux_add_pos Λ K2
    (nnreal.half_pos εpos),
  --let `f := f1 + f2` test function for the content of `K`
  have f_test_function_union : (∀ x ∈ (K1 ⊔ K2), (1 : ℝ≥0) ≤ (f1 + f2) x),
  { rintros x (x_in_K1 | x_in_K2),
    { exact le_add_right (f_test_function_K1.left x x_in_K1) },
    { exact le_add_left (f_test_function_K2.left x x_in_K2) }},
  --use that `Λf` is an upper bound for `λ(K1⊔K2)`
  apply (riesz_content_aux_le Λ f_test_function_union).trans (le_of_lt _),
  rw map_add,
  --use that `Λfi` are lower bounds for `λ(Ki) + ε/2`
  apply lt_of_lt_of_le (add_lt_add f_test_function_K1.right f_test_function_K2.right) (le_of_eq _),
  rw [add_assoc, add_comm (ε/2), add_assoc, nnreal.add_halves ε, add_assoc],
end

end riesz_subadditive

section urysohn_bounded_nnreal

lemma real.isometry_const_sub (c : ℝ) :
  isometry (λ (r : ℝ), c - r) :=
begin
  intros x y,
  simp_rw [edist_dist],
  apply congr_arg ennreal.of_real,
  simp only [real.dist_eq, sub_sub_sub_cancel_left, abs_sub_comm],
end

lemma nnreal.lipschitz_with_one_const_sub (c : ℝ≥0) : lipschitz_with 1 (λ (u : ℝ≥0), c - u) :=
begin
  have lip₁ : lipschitz_with 1 (coe : ℝ≥0 → ℝ), from lipschitz_with.subtype_coe _,
  have lip₂ := isometry.lipschitz (real.isometry_const_sub c),
  have lip₃ : lipschitz_with 1 real.to_nnreal, from lipschitz_with_pos,
  simpa only [mul_one] using (lip₃.comp lip₂).comp lip₁,
end

/--Urysohn's lemma for `ℝ≥0`-valued functions:  if `s` and `t` are two disjoint closed sets in a
  normal topological space `X`, then there exists a continuous function `f : X → ℝ≥0` such that

  * `f` equals zero on `s`;
  * `f` equals one on `t`;
  * `f x ≤ 1` for all `x`. -/

lemma exists_bounded_zero_one_of_closed_nnreal {α : Type*} [topological_space α] [normal_space α]
  {s t : set α} (s_closed : is_closed s) (t_closed : is_closed t) (disj : disjoint s t) :
  ∃ (f : α →ᵇ ℝ≥0), eq_on f 0 s ∧ eq_on f 1 t ∧ ⇑f ≤ 1 :=
begin
  rcases exists_bounded_zero_one_of_closed s_closed t_closed disj
    with ⟨g, ⟨g_on_s, ⟨g_on_t, g_bdd⟩⟩⟩,
  use g.nnreal_part,
  rw bounded_continuous_function.nnreal_part_coe_fun_eq,
  refine ⟨_, _, _⟩,
  { intros x hx,
    simp only [pi.zero_apply, real.to_nnreal_eq_zero, g_on_s hx] },
  { intros x hx,
    simp only [comp_app, pi.one_apply, real.to_nnreal_one, g_on_t hx] },
  { intros x,
    convert real.to_nnreal_le_to_nnreal (g_bdd x).2,
    simp only [pi.one_apply, real.to_nnreal_one] },
end

/--Given two disjoint closed sets `s,t` in a normal space, there exist two bounded continuous
  `ℝ≥0`-valued functions `f₁,f₂` such that

  * `f₁ = 1` on `s`
  * `f₂ = 1` on `t`
  * `f₁ + f₂ = 1`.

-/
lemma exists_sum_one_of_closed_nnreal {α : Type*} [topological_space α] [normal_space α]
  {s t : set α} (s_closed : is_closed s) (t_closed : is_closed t) (disj : disjoint s t) :
  ∃ (f₁ f₂ : α →ᵇ ℝ≥0), eq_on f₁ 1 s ∧ eq_on f₂ 1 t ∧ f₁ + f₂ = 1 :=
begin
  rcases exists_bounded_zero_one_of_closed_nnreal s_closed t_closed disj
    with ⟨f₂, ⟨f₂_on_s, ⟨f₂_on_t, f₂_le_one⟩⟩⟩,
  let f₁ := f₂.comp _ (nnreal.lipschitz_with_one_const_sub 1),
  have def_f₁ : ∀ x, (f₁ x = 1 - f₂ x), from λ x, rfl,
  use [f₁, f₂],
  refine ⟨_, _, _⟩,
  { intros x hx,
    rw [def_f₁, f₂_on_s hx, pi.zero_apply, tsub_zero, pi.one_apply], },
  { intros x hx,
    rw f₂_on_t hx, },
  { ext x,
    simp only [bounded_continuous_function.coe_add, pi.add_apply, nonneg.coe_add,
               bounded_continuous_function.coe_one, pi.one_apply, nonneg.coe_one],
    rw [def_f₁, ← nnreal.coe_add, @tsub_add_cancel_of_le ℝ≥0 _ _ _ _ _ _ _ 1 (f₂_le_one x),
        nnreal.coe_one], },
end
end urysohn_bounded_nnreal

/-- A positive linear functional on bounded continuous functions on X is monotone. -/
lemma positive_linear_functional_mono {f g : X →ᵇ ℝ≥0} (f_le_g : ∀ (x : X), f x ≤ g x) :
  Λ f ≤ Λ g :=
begin
  have g_decomposition : g = (g.nnreal_sub f) + f,
  { ext x,
    rw [bounded_continuous_function.coe_add, pi.add_apply,
      bounded_continuous_function.nnreal_sub_apply, nonneg.coe_add, nnreal.coe_sub (f_le_g x)],
    ring, },
  rw g_decomposition,
  simp only [map_add, le_add_iff_nonneg_left, zero_le'],
end

variables [compact_space X] [t2_space X]

/-- The Riesz content (associated to a given positive linear functional Λ) is
finitely additive: λ(K₁ ∪ K₂) = λ(K₁) + λ(K₂) for any disjoint compact subsets K₁, K₂ ⊆ X. -/
lemma riesz_content_additive {K₁ K₂ : compacts X} (disj : disjoint K₁ K₂) :
  riesz_content_aux Λ (K₁ ⊔ K₂) = riesz_content_aux Λ K₁ + riesz_content_aux Λ K₂ :=
begin
  refine le_antisymm (riesz_content_aux_sup_le Λ K₁ K₂) _,
  refine le_cInf (riesz_content_aux_image_nonempty Λ (K₁ ⊔ K₂)) _,
  rintros b ⟨f, ⟨hf, Λf_eq_b⟩⟩,
  haveI : normal_space X := normal_of_compact_t2,
  obtain ⟨g₁, g₂, ⟨hg₁, hg₂, h_sum⟩⟩ :=
    exists_sum_one_of_closed_nnreal K₁.is_compact.is_closed K₂.is_compact.is_closed disj,
  have f_eq_sum : f = g₁.nnreal_mul f + g₂.nnreal_mul f,
  { ext x,
    simp only [bounded_continuous_function.coe_add, pi.add_apply,
               bounded_continuous_function.nnreal_mul_apply, nonneg.coe_add, nonneg.coe_mul],
    rw [← nnreal.coe_mul, ← nnreal.coe_mul, ← nnreal.coe_add, ← add_mul,
        (show g₁ x + g₂ x = (g₁ + g₂) x, by refl), h_sum],
    simp only [bounded_continuous_function.coe_one, pi.one_apply, one_mul], },
  rw [← Λf_eq_b, f_eq_sum, map_add],
  have aux₁ : ∀ x ∈ K₁, 1 ≤ (g₁.nnreal_mul f) x,
  { intros x hx,
    simp only [hg₁ hx, pi.one_apply, bounded_continuous_function.nnreal_mul_apply, one_mul],
    exact hf x (mem_union_left _ hx), },
  have aux₂ : ∀ x ∈ K₂, 1 ≤ (g₂.nnreal_mul f) x,
  { intros x hx,
    simp only [hg₂ hx, pi.one_apply, bounded_continuous_function.nnreal_mul_apply, one_mul],
    exact hf x (mem_union_right _ hx), },
  apply add_le_add (riesz_content_aux_le Λ aux₁)
                   (riesz_content_aux_le Λ aux₂),
end

section riesz_content
/-- Given a positive linear functional Λ on a compact Hausdorff space X, a content λ is
defined on compact subsets K ⊆ X by λ(K) = inf {Λf | 1≤f on K}. -/
def riesz_content (Λ : (X →ᵇ ℝ≥0) →ₗ[ℝ≥0] ℝ≥0) : content X :=
{ to_fun := riesz_content_aux Λ,
  mono' := λ K₁ K₂, riesz_content_aux_mono Λ,
  sup_disjoint' := λ K₁ K₂, riesz_content_additive Λ,
  sup_le' := riesz_content_aux_sup_le Λ, }

lemma riesz_content.to_fun_eq (Λ : (X →ᵇ ℝ≥0) →ₗ[ℝ≥0] ℝ≥0) :
  (riesz_content Λ).to_fun = riesz_content_aux Λ := rfl

lemma riesz_content.coe_to_fun_eq (Λ : (X →ᵇ ℝ≥0) →ₗ[ℝ≥0] ℝ≥0) :
  ⇑(riesz_content Λ) = (coe : ℝ≥0 → ℝ≥0∞) ∘ (riesz_content_aux Λ) := rfl

end riesz_content

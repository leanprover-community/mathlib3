/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.metric_space.gluing
import topology.metric_space.hausdorff_distance
import topology.continuous_function.bounded

/-!
# The Gromov-Hausdorff distance is realized

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we construct of a good coupling between nonempty compact metric spaces, minimizing
their Hausdorff distance. This construction is instrumental to study the Gromov-Hausdorff
distance between nonempty compact metric spaces.

Given two nonempty compact metric spaces `X` and `Y`, we define `optimal_GH_coupling X Y` as a
compact metric space, together with two isometric embeddings `optimal_GH_injl` and `optimal_GH_injr`
respectively of `X` and `Y` into `optimal_GH_coupling X Y`. The main property of the optimal
coupling is that the Hausdorff distance between `X` and `Y` in `optimal_GH_coupling X Y` is smaller
than the corresponding distance in any other coupling. We do not prove completely this fact in this
file, but we show a good enough approximation of this fact in `Hausdorff_dist_optimal_le_HD`, that
will suffice to obtain the full statement once the Gromov-Hausdorff distance is properly defined,
in `Hausdorff_dist_optimal`.

The key point in the construction is that the set of possible distances coming from isometric
embeddings of `X` and `Y` in metric spaces is a set of equicontinuous functions. By Arzela-Ascoli,
it is compact, and one can find such a distance which is minimal. This distance defines a premetric
space structure on `X ⊕ Y`. The corresponding metric quotient is `optimal_GH_coupling X Y`.
-/

noncomputable theory
open_locale classical topology nnreal
universes u v w

open classical set function topological_space filter metric quotient
open bounded_continuous_function
open sum (inl inr)

local attribute [instance] metric_space_sum

namespace Gromov_Hausdorff

section Gromov_Hausdorff_realized
/- This section shows that the Gromov-Hausdorff distance
is realized. For this, we consider candidate distances on the disjoint union
`X ⊕ Y` of two compact nonempty metric spaces, almost realizing the Gromov-Hausdorff
distance, and show that they form a compact family by applying Arzela-Ascoli
theorem. The existence of a minimizer follows. -/

section definitions
variables (X : Type u) (Y : Type v)
  [metric_space X] [compact_space X] [nonempty X]
  [metric_space Y] [compact_space Y] [nonempty Y]

@[reducible] private def prod_space_fun : Type* := ((X ⊕ Y) × (X ⊕ Y)) → ℝ
@[reducible] private def Cb : Type* := bounded_continuous_function ((X ⊕ Y) × (X ⊕ Y)) ℝ

private def max_var : ℝ≥0 :=
2 * ⟨diam (univ : set X), diam_nonneg⟩ + 1 + 2 * ⟨diam (univ : set Y), diam_nonneg⟩

private lemma one_le_max_var : 1 ≤ max_var X Y := calc
  (1 : real) = 2 * 0 + 1 + 2 * 0 : by simp
  ... ≤ 2 * diam (univ : set X) + 1 + 2 * diam (univ : set Y) :
  by apply_rules [add_le_add, mul_le_mul_of_nonneg_left, diam_nonneg]; norm_num

/-- The set of functions on `X ⊕ Y` that are candidates distances to realize the
minimum of the Hausdorff distances between `X` and `Y` in a coupling -/
def candidates : set (prod_space_fun X Y) :=
  {f | (((((∀ x y : X, f (sum.inl x, sum.inl y) = dist x y)
    ∧ (∀ x y : Y, f (sum.inr x, sum.inr y) = dist x y))
    ∧ (∀ x y,     f (x, y) = f (y, x)))
    ∧ (∀ x y z,   f (x, z) ≤ f (x, y) + f (y, z)))
    ∧ (∀ x,       f (x, x) = 0))
    ∧ (∀ x y,     f (x, y) ≤ max_var X Y) }

/-- Version of the set of candidates in bounded_continuous_functions, to apply
Arzela-Ascoli -/
private def candidates_b : set (Cb X Y) := {f : Cb X Y | (f : _ → ℝ) ∈ candidates X Y}

end definitions --section

section constructions

variables {X : Type u} {Y : Type v}
[metric_space X] [compact_space X] [nonempty X] [metric_space Y] [compact_space Y] [nonempty Y]
{f : prod_space_fun X Y} {x y z t : X ⊕ Y}
local attribute [instance, priority 10] inhabited_of_nonempty'

private lemma max_var_bound : dist x y ≤ max_var X Y := calc
  dist x y ≤ diam (univ : set (X ⊕ Y)) :
    dist_le_diam_of_mem bounded_of_compact_space (mem_univ _) (mem_univ _)
  ... = diam (range inl ∪ range inr : set (X ⊕ Y)) :
    by rw [range_inl_union_range_inr]
  ... ≤ diam (range inl : set (X ⊕ Y)) + dist (inl default) (inr default) +
          diam (range inr : set (X ⊕ Y)) :
    diam_union (mem_range_self _) (mem_range_self _)
  ... = diam (univ : set X) + (dist default default + 1 + dist default default) +
          diam (univ : set Y) :
    by { rw [isometry_inl.diam_range, isometry_inr.diam_range], refl }
  ... = 1 * diam (univ : set X) + 1 + 1 * diam (univ : set Y) : by simp
  ... ≤ 2 * diam (univ : set X) + 1 + 2 * diam (univ : set Y) :
  begin
    apply_rules [add_le_add, mul_le_mul_of_nonneg_right, diam_nonneg, le_refl],
    norm_num, norm_num
  end

private lemma candidates_symm (fA : f ∈ candidates X Y) : f (x, y) = f (y, x) := fA.1.1.1.2 x y

private lemma candidates_triangle (fA : f ∈ candidates X Y) : f (x, z) ≤ f (x, y) + f (y, z) :=
  fA.1.1.2 x y z

private lemma candidates_refl (fA : f ∈ candidates X Y) : f (x, x) = 0 := fA.1.2 x

private lemma candidates_nonneg (fA : f ∈ candidates X Y) : 0 ≤ f (x, y) :=
begin
  have : 0 ≤ 2 * f (x, y) := calc
    0 = f (x, x) : (candidates_refl fA).symm
    ... ≤ f (x, y) + f (y, x) : candidates_triangle fA
    ... = f (x, y) + f (x, y) : by rw [candidates_symm fA]
    ... = 2 * f (x, y) : by ring,
  by linarith
end

private lemma candidates_dist_inl (fA : f ∈ candidates X Y) (x y: X) :
  f (inl x, inl y) = dist x y :=
fA.1.1.1.1.1 x y

private lemma candidates_dist_inr (fA : f ∈ candidates X Y) (x y : Y) :
  f (inr x, inr y) = dist x y :=
fA.1.1.1.1.2 x y

private lemma candidates_le_max_var (fA : f ∈ candidates X Y) : f (x, y) ≤ max_var X Y :=
fA.2 x y

/-- candidates are bounded by `max_var X Y` -/
private lemma candidates_dist_bound  (fA : f ∈ candidates X Y) :
  ∀ {x y : X ⊕ Y}, f (x, y) ≤ max_var X Y * dist x y
| (inl x) (inl y) := calc
    f (inl x, inl y) = dist x y : candidates_dist_inl fA x y
    ... = dist (inl x) (inl y) : by { rw @sum.dist_eq X Y, refl }
    ... = 1 * dist (inl x) (inl y) : by simp
    ... ≤ max_var X Y * dist (inl x) (inl y) :
      mul_le_mul_of_nonneg_right (one_le_max_var X Y) dist_nonneg
| (inl x) (inr y) := calc
    f (inl x, inr y) ≤ max_var X Y : candidates_le_max_var fA
    ... = max_var X Y * 1 : by simp
    ... ≤ max_var X Y * dist (inl x) (inr y) :
      mul_le_mul_of_nonneg_left sum.one_dist_le (le_trans (zero_le_one) (one_le_max_var X Y))
| (inr x) (inl y) := calc
    f (inr x, inl y) ≤ max_var X Y : candidates_le_max_var fA
    ... = max_var X Y * 1 : by simp
    ... ≤ max_var X Y * dist (inl x) (inr y) :
      mul_le_mul_of_nonneg_left sum.one_dist_le (le_trans (zero_le_one) (one_le_max_var X Y))
| (inr x) (inr y) := calc
    f (inr x, inr y) = dist x y : candidates_dist_inr fA x y
    ... = dist (inr x) (inr y) : by { rw @sum.dist_eq X Y, refl }
    ... = 1 * dist (inr x) (inr y) : by simp
    ... ≤ max_var X Y * dist (inr x) (inr y) :
      mul_le_mul_of_nonneg_right (one_le_max_var X Y) dist_nonneg

/-- Technical lemma to prove that candidates are Lipschitz -/
private lemma candidates_lipschitz_aux (fA : f ∈ candidates X Y) :
  f (x, y) - f (z, t) ≤ 2 * max_var X Y * dist (x, y) (z, t) :=
calc
  f (x, y) - f(z, t) ≤ f (x, t) + f (t, y) - f (z, t) : sub_le_sub_right (candidates_triangle fA) _
  ... ≤ (f (x, z) + f (z, t) + f(t, y)) - f (z, t) :
    sub_le_sub_right (add_le_add_right (candidates_triangle fA) _ ) _
  ... = f (x, z) + f (t, y) : by simp [sub_eq_add_neg, add_assoc]
  ... ≤ max_var X Y * dist x z + max_var X Y * dist t y :
    add_le_add (candidates_dist_bound fA) (candidates_dist_bound fA)
  ... ≤ max_var X Y * max (dist x z) (dist t y) + max_var X Y * max (dist x z) (dist t y) :
  begin
    apply add_le_add,
    apply mul_le_mul_of_nonneg_left (le_max_left (dist x z) (dist t y))
      (zero_le_one.trans (one_le_max_var X Y)),
    apply mul_le_mul_of_nonneg_left (le_max_right (dist x z) (dist t y))
      (zero_le_one.trans (one_le_max_var X Y)),
  end
  ... = 2 * max_var X Y * max (dist x z) (dist y t) :
    by { simp [dist_comm], ring }
  ... = 2 * max_var X Y * dist (x, y) (z, t) : by refl

/-- Candidates are Lipschitz -/
private lemma candidates_lipschitz (fA : f ∈ candidates X Y) :
  lipschitz_with (2 * max_var X Y) f :=
begin
  apply lipschitz_with.of_dist_le_mul,
  rintros ⟨x, y⟩ ⟨z, t⟩,
  rw [real.dist_eq, abs_sub_le_iff],
  use candidates_lipschitz_aux fA,
  rw [dist_comm],
  exact candidates_lipschitz_aux fA
end

/-- candidates give rise to elements of bounded_continuous_functions -/
def candidates_b_of_candidates (f : prod_space_fun X Y) (fA : f ∈ candidates X Y) : Cb X Y :=
bounded_continuous_function.mk_of_compact ⟨f, (candidates_lipschitz fA).continuous⟩

lemma candidates_b_of_candidates_mem (f : prod_space_fun X Y) (fA : f ∈ candidates X Y) :
  candidates_b_of_candidates f fA ∈ candidates_b X Y := fA

/-- The distance on `X ⊕ Y` is a candidate -/
private lemma dist_mem_candidates : (λp : (X ⊕ Y) × (X ⊕ Y), dist p.1 p.2) ∈ candidates X Y :=
begin
  simp only [candidates, dist_comm, forall_const, and_true, add_comm, eq_self_iff_true,
             and_self, sum.forall, set.mem_set_of_eq, dist_self],
  repeat { split
    <|> exact (λa y z, dist_triangle_left _ _ _)
    <|> exact (λx y, by refl)
    <|> exact (λx y, max_var_bound) }
end

/-- The distance on `X ⊕ Y` as a candidate -/
def candidates_b_dist (X : Type u) (Y : Type v) [metric_space X] [compact_space X] [inhabited X]
  [metric_space Y] [compact_space Y] [inhabited Y] : Cb X Y :=
candidates_b_of_candidates _ dist_mem_candidates

lemma candidates_b_dist_mem_candidates_b : candidates_b_dist X Y ∈ candidates_b X Y :=
candidates_b_of_candidates_mem _ _

private lemma candidates_b_nonempty : (candidates_b X Y).nonempty :=
⟨_,  candidates_b_dist_mem_candidates_b⟩

/-- To apply Arzela-Ascoli, we need to check that the set of candidates is closed and
equicontinuous. Equicontinuity follows from the Lipschitz control, we check closedness. -/
private lemma closed_candidates_b : is_closed (candidates_b X Y) :=
begin
  have I1 : ∀ x y, is_closed {f : Cb X Y | f (inl x, inl y) = dist x y} :=
    λx y, is_closed_eq continuous_eval_const continuous_const,
  have I2 : ∀ x y, is_closed {f : Cb X Y | f (inr x, inr y) = dist x y } :=
    λx y, is_closed_eq continuous_eval_const continuous_const,
  have I3 : ∀ x y, is_closed {f : Cb X Y | f (x, y) = f (y, x)} :=
    λx y, is_closed_eq continuous_eval_const continuous_eval_const,
  have I4 : ∀ x y z, is_closed {f : Cb X Y | f (x, z) ≤ f (x, y) + f (y, z)} :=
    λx y z, is_closed_le continuous_eval_const (continuous_eval_const.add continuous_eval_const),
  have I5 : ∀ x, is_closed {f : Cb X Y | f (x, x) = 0} :=
    λx, is_closed_eq continuous_eval_const continuous_const,
  have I6 : ∀ x y, is_closed {f : Cb X Y | f (x, y) ≤ max_var X Y} :=
    λx y, is_closed_le continuous_eval_const continuous_const,
  have : candidates_b X Y = (⋂x y, {f : Cb X Y | f ((@inl X Y x), (@inl X Y y)) = dist x y})
               ∩ (⋂x y, {f : Cb X Y | f ((@inr X Y x), (@inr X Y y)) = dist x y})
               ∩ (⋂x y, {f : Cb X Y | f (x, y) = f (y, x)})
               ∩ (⋂x y z, {f : Cb X Y | f (x, z) ≤ f (x, y) + f (y, z)})
               ∩ (⋂x, {f : Cb X Y | f (x, x) = 0})
               ∩ (⋂x y, {f : Cb X Y | f (x, y) ≤ max_var X Y}),
  { ext, simp only [candidates_b, candidates, mem_inter_iff, mem_Inter, mem_set_of_eq] },
  rw this,
  repeat { apply is_closed.inter _ _
       <|> apply is_closed_Inter _
       <|> apply I1 _ _
       <|> apply I2 _ _
       <|> apply I3 _ _
       <|> apply I4 _ _ _
       <|> apply I5 _
       <|> apply I6 _ _
       <|> assume x },
end

/-- Compactness of candidates (in bounded_continuous_functions) follows. -/
private lemma is_compact_candidates_b : is_compact (candidates_b X Y) :=
begin
  refine arzela_ascoli₂ (Icc 0 (max_var X Y)) is_compact_Icc (candidates_b X Y)
  closed_candidates_b _ _,
  { rintros f ⟨x1, x2⟩ hf,
    simp only [set.mem_Icc],
    exact ⟨candidates_nonneg hf, candidates_le_max_var hf⟩ },
  { refine equicontinuous_of_continuity_modulus (λt, 2 * max_var X Y * t) _ _ _,
    { have : tendsto (λ (t : ℝ), 2 * (max_var X Y : ℝ) * t) (𝓝 0) (𝓝 (2 * max_var X Y * 0)) :=
        tendsto_const_nhds.mul tendsto_id,
      simpa using this },
    { rintros x y ⟨f, hf⟩,
      exact (candidates_lipschitz hf).dist_le_mul _ _ } }
end

/-- We will then choose the candidate minimizing the Hausdorff distance. Except that we are not
in a metric space setting, so we need to define our custom version of Hausdorff distance,
called HD, and prove its basic properties. -/
def HD (f : Cb X Y) := max (⨆ x, ⨅ y, f (inl x, inr y)) (⨆ y, ⨅ x, f (inl x, inr y))

/- We will show that HD is continuous on bounded_continuous_functions, to deduce that its
minimum on the compact set candidates_b is attained. Since it is defined in terms of
infimum and supremum on `ℝ`, which is only conditionnally complete, we will need all the time
to check that the defining sets are bounded below or above. This is done in the next few
technical lemmas -/

lemma HD_below_aux1 {f : Cb X Y} (C : ℝ) {x : X} :
  bdd_below (range (λ (y : Y), f (inl x, inr y) + C)) :=
let ⟨cf, hcf⟩ := (real.bounded_iff_bdd_below_bdd_above.1 f.bounded_range).1 in
⟨cf + C, forall_range_iff.2 (λi, add_le_add_right ((λx, hcf (mem_range_self x)) _) _)⟩

private lemma HD_bound_aux1 (f : Cb X Y) (C : ℝ) :
  bdd_above (range (λ (x : X), ⨅ y, f (inl x, inr y) + C)) :=
begin
  rcases (real.bounded_iff_bdd_below_bdd_above.1 f.bounded_range).2 with ⟨Cf, hCf⟩,
  refine ⟨Cf + C, forall_range_iff.2 (λx, _)⟩,
  calc (⨅ y, f (inl x, inr y) + C) ≤ f (inl x, inr default) + C :
    cinfi_le (HD_below_aux1 C) default
    ... ≤ Cf + C : add_le_add ((λx, hCf (mem_range_self x)) _) le_rfl
end

lemma HD_below_aux2 {f : Cb X Y} (C : ℝ) {y : Y} :
  bdd_below (range (λ (x : X), f (inl x, inr y) + C)) :=
let ⟨cf, hcf⟩ := (real.bounded_iff_bdd_below_bdd_above.1 f.bounded_range).1 in
⟨cf + C, forall_range_iff.2 (λi, add_le_add_right ((λx, hcf (mem_range_self x)) _) _)⟩

private lemma HD_bound_aux2 (f : Cb X Y) (C : ℝ) :
  bdd_above (range (λ (y : Y), ⨅ x, f (inl x, inr y) + C)) :=
begin
  rcases (real.bounded_iff_bdd_below_bdd_above.1 f.bounded_range).2 with ⟨Cf, hCf⟩,
  refine ⟨Cf + C, forall_range_iff.2 (λy, _)⟩,
  calc (⨅ x, f (inl x, inr y) + C) ≤ f (inl default, inr y) + C :
    cinfi_le (HD_below_aux2 C) default
  ... ≤ Cf + C : add_le_add ((λx, hCf (mem_range_self x)) _) le_rfl
end

/-- Explicit bound on `HD (dist)`. This means that when looking for minimizers it will
be sufficient to look for functions with `HD(f)` bounded by this bound. -/
lemma HD_candidates_b_dist_le :
  HD (candidates_b_dist X Y) ≤ diam (univ : set X) + 1 + diam (univ : set Y) :=
begin
  refine max_le (csupr_le (λx, _)) (csupr_le (λy, _)),
  { have A : (⨅ y, candidates_b_dist X Y (inl x, inr y)) ≤
      candidates_b_dist X Y (inl x, inr default) :=
      cinfi_le (by simpa using HD_below_aux1 0) default,
    have B : dist (inl x) (inr default) ≤ diam (univ : set X) + 1 + diam (univ : set Y) := calc
      dist (inl x) (inr (default : Y)) = dist x (default : X) + 1 + dist default default : rfl
      ... ≤ diam (univ : set X) + 1 + diam (univ : set Y) :
      begin
        apply add_le_add (add_le_add _ le_rfl),
        exact dist_le_diam_of_mem bounded_of_compact_space (mem_univ _) (mem_univ _),
        any_goals { exact ordered_add_comm_monoid.to_covariant_class_left ℝ },
        any_goals { exact ordered_add_comm_monoid.to_covariant_class_right ℝ },
        exact dist_le_diam_of_mem bounded_of_compact_space (mem_univ _) (mem_univ _),
      end,
    exact le_trans A B },
  { have A : (⨅ x, candidates_b_dist X Y (inl x, inr y)) ≤
      candidates_b_dist X Y (inl default, inr y) :=
      cinfi_le (by simpa using HD_below_aux2 0) default,
    have B : dist (inl default) (inr y) ≤ diam (univ : set X) + 1 + diam (univ : set Y) := calc
      dist (inl (default : X)) (inr y) = dist default default + 1 + dist default y : rfl
      ... ≤ diam (univ : set X) + 1 + diam (univ : set Y) :
      begin
        apply add_le_add (add_le_add _ le_rfl),
        exact dist_le_diam_of_mem bounded_of_compact_space (mem_univ _) (mem_univ _),
        any_goals { exact ordered_add_comm_monoid.to_covariant_class_left ℝ },
        any_goals { exact ordered_add_comm_monoid.to_covariant_class_right ℝ },
        exact dist_le_diam_of_mem bounded_of_compact_space (mem_univ _) (mem_univ _)
      end,
    exact le_trans A B },
end

/- To check that HD is continuous, we check that it is Lipschitz. As HD is a max, we
prove separately inequalities controlling the two terms (relying too heavily on copy-paste...) -/
private lemma HD_lipschitz_aux1 (f g : Cb X Y) :
  (⨆ x, ⨅ y, f (inl x, inr y)) ≤ (⨆ x, ⨅ y, g (inl x, inr y)) + dist f g :=
begin
  rcases (real.bounded_iff_bdd_below_bdd_above.1 g.bounded_range).1 with ⟨cg, hcg⟩,
  have Hcg : ∀ x, cg ≤ g x := λx, hcg (mem_range_self x),
  rcases (real.bounded_iff_bdd_below_bdd_above.1 f.bounded_range).1 with ⟨cf, hcf⟩,
  have Hcf : ∀ x, cf ≤ f x := λx, hcf (mem_range_self x),

  -- prove the inequality but with `dist f g` inside, by using inequalities comparing
  -- supr to supr and infi to infi
  have Z : (⨆ x, ⨅ y, f (inl x, inr y)) ≤ ⨆ x, ⨅ y, g (inl x, inr y) + dist f g :=
    csupr_mono (HD_bound_aux1 _ (dist f g))
      (λx, cinfi_mono ⟨cf, forall_range_iff.2(λi, Hcf _)⟩ (λy, coe_le_coe_add_dist)),
  -- move the `dist f g` out of the infimum and the supremum, arguing that continuous monotone maps
  -- (here the addition of `dist f g`) preserve infimum and supremum
  have E1 : ∀ x, (⨅ y, g (inl x, inr y)) + dist f g = ⨅ y, g (inl x, inr y) + dist f g,
  { assume x,
    refine monotone.map_cinfi_of_continuous_at (continuous_at_id.add continuous_at_const) _ _,
    { assume x y hx, simpa },
    { show bdd_below (range (λ (y : Y), g (inl x, inr y))),
        from ⟨cg, forall_range_iff.2(λi, Hcg _)⟩ } },
  have E2 : (⨆ x, ⨅ y, g (inl x, inr y)) + dist f g = ⨆ x, (⨅ y, g (inl x, inr y)) + dist f g,
  { refine monotone.map_csupr_of_continuous_at (continuous_at_id.add continuous_at_const) _ _,
    { assume x y hx, simpa },
    { simpa using HD_bound_aux1 _ 0 } },
  -- deduce the result from the above two steps
  simpa [E2, E1, function.comp]
end

private lemma HD_lipschitz_aux2 (f g : Cb X Y) :
  (⨆ y, ⨅ x, f (inl x, inr y)) ≤ (⨆ y, ⨅ x, g (inl x, inr y)) + dist f g :=
begin
  rcases (real.bounded_iff_bdd_below_bdd_above.1 g.bounded_range).1 with ⟨cg, hcg⟩,
  have Hcg : ∀ x, cg ≤ g x := λx, hcg (mem_range_self x),
  rcases (real.bounded_iff_bdd_below_bdd_above.1 f.bounded_range).1 with ⟨cf, hcf⟩,
  have Hcf : ∀ x, cf ≤ f x := λx, hcf (mem_range_self x),

  -- prove the inequality but with `dist f g` inside, by using inequalities comparing
  -- supr to supr and infi to infi
  have Z : (⨆ y, ⨅ x, f (inl x, inr y)) ≤ ⨆ y, ⨅ x, g (inl x, inr y) + dist f g :=
    csupr_mono (HD_bound_aux2 _ (dist f g))
      (λy, cinfi_mono  ⟨cf, forall_range_iff.2(λi, Hcf _)⟩ (λy, coe_le_coe_add_dist)),
  -- move the `dist f g` out of the infimum and the supremum, arguing that continuous monotone maps
  -- (here the addition of `dist f g`) preserve infimum and supremum
  have E1 : ∀ y, (⨅ x, g (inl x, inr y)) + dist f g = ⨅ x, g (inl x, inr y) + dist f g,
  { assume y,
    refine monotone.map_cinfi_of_continuous_at (continuous_at_id.add continuous_at_const) _ _,
    { assume x y hx, simpa },
    { show bdd_below (range (λx:X, g (inl x, inr y))),
        from ⟨cg, forall_range_iff.2 (λi, Hcg _)⟩ } },
  have E2 : (⨆ y, ⨅ x, g (inl x, inr y)) + dist f g = ⨆ y, (⨅ x, g (inl x, inr y)) + dist f g,
  { refine monotone.map_csupr_of_continuous_at (continuous_at_id.add continuous_at_const) _ _,
    { assume x y hx, simpa },
    { simpa using HD_bound_aux2 _ 0 } },
  -- deduce the result from the above two steps
  simpa [E2, E1]
end

private lemma HD_lipschitz_aux3 (f g : Cb X Y) : HD f ≤ HD g + dist f g :=
max_le (le_trans (HD_lipschitz_aux1 f g) (add_le_add_right (le_max_left _ _) _))
       (le_trans (HD_lipschitz_aux2 f g) (add_le_add_right (le_max_right _ _) _))

/-- Conclude that HD, being Lipschitz, is continuous -/
private lemma HD_continuous : continuous (HD : Cb X Y → ℝ) :=
lipschitz_with.continuous (lipschitz_with.of_le_add HD_lipschitz_aux3)

end constructions --section

section consequences
variables (X : Type u) (Y : Type v) [metric_space X] [compact_space X] [nonempty X] [metric_space Y]
  [compact_space Y] [nonempty Y]

/- Now that we have proved that the set of candidates is compact, and that HD is continuous,
we can finally select a candidate minimizing HD. This will be the candidate realizing the
optimal coupling. -/
private lemma exists_minimizer : ∃ f ∈ candidates_b X Y, ∀ g ∈ candidates_b X Y, HD f ≤ HD g :=
is_compact_candidates_b.exists_forall_le candidates_b_nonempty HD_continuous.continuous_on

private definition optimal_GH_dist : Cb X Y := classical.some (exists_minimizer X Y)

private lemma optimal_GH_dist_mem_candidates_b : optimal_GH_dist X Y ∈ candidates_b X Y :=
by cases (classical.some_spec (exists_minimizer X Y)); assumption

private lemma HD_optimal_GH_dist_le (g : Cb X Y) (hg : g ∈ candidates_b X Y) :
  HD (optimal_GH_dist X Y) ≤ HD g :=
let ⟨Z1, Z2⟩ := classical.some_spec (exists_minimizer X Y) in Z2 g hg

/-- With the optimal candidate, construct a premetric space structure on `X ⊕ Y`, on which the
predistance is given by the candidate. Then, we will identify points at `0` predistance
to obtain a genuine metric space -/
def premetric_optimal_GH_dist : pseudo_metric_space (X ⊕ Y) :=
{ dist := λp q, optimal_GH_dist X Y (p, q),
  dist_self := λx, candidates_refl (optimal_GH_dist_mem_candidates_b X Y),
  dist_comm := λx y, candidates_symm (optimal_GH_dist_mem_candidates_b X Y),
  dist_triangle := λx y z, candidates_triangle (optimal_GH_dist_mem_candidates_b X Y) }

local attribute [instance] premetric_optimal_GH_dist

/-- A metric space which realizes the optimal coupling between `X` and `Y` -/
@[derive metric_space, nolint has_nonempty_instance]
definition optimal_GH_coupling : Type* :=
@uniform_space.separation_quotient (X ⊕ Y) (premetric_optimal_GH_dist X Y).to_uniform_space

/-- Injection of `X` in the optimal coupling between `X` and `Y` -/
def optimal_GH_injl (x : X) : optimal_GH_coupling X Y := quotient.mk' (inl x)

/-- The injection of `X` in the optimal coupling between `X` and `Y` is an isometry. -/
lemma isometry_optimal_GH_injl : isometry (optimal_GH_injl X Y) :=
isometry.of_dist_eq $ λ x y, candidates_dist_inl (optimal_GH_dist_mem_candidates_b X Y) _ _

/-- Injection of `Y` in the optimal coupling between `X` and `Y` -/
def optimal_GH_injr (y : Y) : optimal_GH_coupling X Y := quotient.mk' (inr y)

/-- The injection of `Y` in the optimal coupling between `X` and `Y` is an isometry. -/
lemma isometry_optimal_GH_injr : isometry (optimal_GH_injr X Y) :=
isometry.of_dist_eq $ λ x y, candidates_dist_inr (optimal_GH_dist_mem_candidates_b X Y) _ _

/-- The optimal coupling between two compact spaces `X` and `Y` is still a compact space -/
instance compact_space_optimal_GH_coupling : compact_space (optimal_GH_coupling X Y) :=
⟨begin
  rw [← range_quotient_mk'],
  exact is_compact_range (continuous_sum_dom.2 ⟨(isometry_optimal_GH_injl X Y).continuous,
    (isometry_optimal_GH_injr X Y).continuous⟩)
end⟩

/-- For any candidate `f`, `HD(f)` is larger than or equal to the Hausdorff distance in the
optimal coupling. This follows from the fact that HD of the optimal candidate is exactly
the Hausdorff distance in the optimal coupling, although we only prove here the inequality
we need. -/
lemma Hausdorff_dist_optimal_le_HD {f} (h : f ∈ candidates_b X Y) :
  Hausdorff_dist (range (optimal_GH_injl X Y)) (range (optimal_GH_injr X Y)) ≤ HD f :=
begin
  refine le_trans (le_of_forall_le_of_dense (λ r hr, _)) (HD_optimal_GH_dist_le X Y f h),
  have A : ∀ x ∈ range (optimal_GH_injl X Y), ∃ y ∈ range (optimal_GH_injr X Y), dist x y ≤ r,
  { rintro _ ⟨z, rfl⟩,
    have I1 : (⨆ x, ⨅ y, optimal_GH_dist X Y (inl x, inr y)) < r :=
      lt_of_le_of_lt (le_max_left _ _) hr,
    have I2 : (⨅ y, optimal_GH_dist X Y (inl z, inr y)) ≤
        ⨆ x, ⨅ y, optimal_GH_dist X Y (inl x, inr y) :=
      le_cSup (by simpa using HD_bound_aux1 _ 0) (mem_range_self _),
    have I : (⨅ y, optimal_GH_dist X Y (inl z, inr y)) < r := lt_of_le_of_lt I2 I1,
    rcases exists_lt_of_cInf_lt (range_nonempty _) I with ⟨r', ⟨z', rfl⟩, hr'⟩,
    exact ⟨optimal_GH_injr X Y z', mem_range_self _, le_of_lt hr'⟩ },
  refine Hausdorff_dist_le_of_mem_dist _ A _,
  { inhabit X,
    rcases A _ (mem_range_self default) with ⟨y, -, hy⟩,
    exact le_trans dist_nonneg hy },
  { rintro _ ⟨z, rfl⟩,
    have I1 : (⨆ y, ⨅ x, optimal_GH_dist X Y (inl x, inr y)) < r :=
      lt_of_le_of_lt (le_max_right _ _) hr,
    have I2 : (⨅ x, optimal_GH_dist X Y (inl x, inr z)) ≤
        ⨆ y, ⨅ x, optimal_GH_dist X Y (inl x, inr y) :=
      le_cSup (by simpa using HD_bound_aux2 _ 0) (mem_range_self _),
    have I : (⨅ x, optimal_GH_dist X Y (inl x, inr z)) < r := lt_of_le_of_lt I2 I1,
    rcases exists_lt_of_cInf_lt (range_nonempty _) I with ⟨r', ⟨z', rfl⟩, hr'⟩,
    refine ⟨optimal_GH_injl X Y z', mem_range_self _, le_of_lt _⟩,
    rwa dist_comm }
end

end consequences
/- We are done with the construction of the optimal coupling -/
end Gromov_Hausdorff_realized

end Gromov_Hausdorff

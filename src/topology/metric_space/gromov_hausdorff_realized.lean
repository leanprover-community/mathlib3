/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sébastien Gouëzel

Construction of a good coupling between nonempty compact metric spaces, minimizing
their Hausdorff distance. This construction is instrumental to study the Gromov-Hausdorff
distance between nonempty compact metric spaces -/

import topology.bounded_continuous_function topology.metric_space.gluing
topology.metric_space.hausdorff_distance

noncomputable theory
open_locale classical
universes u v w

open classical lattice set function topological_space filter metric quotient
open bounded_continuous_function
open sum (inl inr)
set_option class.instance_max_depth 50

local attribute [instance] metric_space_sum

namespace Gromov_Hausdorff

section Gromov_Hausdorff_realized
/- This section shows that the Gromov-Hausdorff distance
is realized. For this, we consider candidate distances on the disjoint union
α ⊕ β of two compact nonempty metric spaces, almost realizing the Gromov-Hausdorff
distance, and show that they form a compact family by applying Arzela-Ascoli
theorem. The existence of a minimizer follows. -/

section definitions
variables (α : Type u) (β : Type v)
  [metric_space α] [compact_space α] [nonempty α]
  [metric_space β] [compact_space β] [nonempty β]

@[reducible] private def prod_space_fun : Type* := ((α ⊕ β) × (α ⊕ β)) → ℝ
@[reducible] private def Cb : Type* := bounded_continuous_function ((α ⊕ β) × (α ⊕ β)) ℝ

private def max_var : ℝ := 2 * diam (univ : set α) + 1 + 2 * diam (univ : set β)

private lemma one_le_max_var : 1 ≤ max_var α β := calc
  (1 : real) = 2 * 0 + 1 + 2 * 0 : by simp
  ... ≤ 2 * diam (univ : set α) + 1 + 2 * diam (univ : set β) :
  by apply_rules [add_le_add, mul_le_mul_of_nonneg_left, diam_nonneg, diam_nonneg]; norm_num

/-- The set of functions on α ⊕ β that are candidates distances to realize the
minimum of the Hausdorff distances between α and β in a coupling -/
def candidates : set (prod_space_fun α β) :=
  {f | (((((∀x y : α, f (sum.inl x, sum.inl y) = dist x y)
    ∧ (∀x y : β, f (sum.inr x, sum.inr y) = dist x y))
    ∧ (∀x y,     f (x, y) = f (y, x)))
    ∧ (∀x y z,   f (x, z) ≤ f (x, y) + f (y, z)))
    ∧ (∀x,       f (x, x) = 0))
    ∧ (∀x y,     f (x, y) ≤ max_var α β) }

/-- Version of the set of candidates in bounded_continuous_functions, to apply
Arzela-Ascoli -/
private def candidates_b : set (Cb α β) := {f : Cb α β | f.val ∈ candidates α β}

end definitions --section

section constructions

variables {α : Type u} {β : Type v}
[metric_space α] [compact_space α] [nonempty α] [metric_space β] [compact_space β] [nonempty β]
{f : prod_space_fun α β} {x y z t : α ⊕ β}
local attribute [instance, priority 0] inhabited_of_nonempty'

private lemma max_var_bound : dist x y ≤ max_var α β := calc
  dist x y ≤ diam (univ : set (α ⊕ β)) :
    dist_le_diam_of_mem (bounded_of_compact compact_univ) (mem_univ _) (mem_univ _)
  ... = diam (inl '' (univ : set α) ∪ inr '' (univ : set β)) :
    by apply congr_arg; ext x y z; cases x; simp [mem_univ, mem_range_self]
  ... ≤ diam (inl '' (univ : set α)) + dist (inl (default α)) (inr (default β)) + diam (inr '' (univ : set β)) :
    diam_union (mem_image_of_mem _ (mem_univ _)) (mem_image_of_mem _ (mem_univ _))
  ... = diam (univ : set α) + (dist (default α) (default α) + 1 + dist (default β) (default β)) + diam (univ : set β) :
    by { rw [isometry.diam_image isometry_on_inl, isometry.diam_image isometry_on_inr], refl }
  ... = 1 * diam (univ : set α) + 1 + 1 * diam (univ : set β) : by simp
  ... ≤ 2 * diam (univ : set α) + 1 + 2 * diam (univ : set β) :
  begin
    apply_rules [add_le_add, mul_le_mul_of_nonneg_right, diam_nonneg, diam_nonneg, le_refl],
    norm_num, norm_num
  end

private lemma candidates_symm (fA : f ∈ candidates α β) : f (x, y) = f (y ,x) := fA.1.1.1.2 x y

private lemma candidates_triangle (fA : f ∈ candidates α β) : f (x, z) ≤ f (x, y) + f (y, z) :=
  fA.1.1.2 x y z

private lemma candidates_refl (fA : f ∈ candidates α β) : f (x, x) = 0 := fA.1.2 x

private lemma candidates_nonneg (fA : f ∈ candidates α β) : 0 ≤ f (x, y) :=
begin
  have : 0 ≤ 2 * f (x, y) := calc
    0 = f (x, x) : (candidates_refl fA).symm
    ... ≤ f (x, y) + f (y, x) : candidates_triangle fA
    ... = f (x, y) + f (x, y) : by rw [candidates_symm fA]
    ... = 2 * f (x, y) : by ring,
  by linarith
end

private lemma candidates_dist_inl (fA : f ∈ candidates α β) (x y: α) : f (inl x, inl y) = dist x y :=
fA.1.1.1.1.1 x y

private lemma candidates_dist_inr (fA : f ∈ candidates α β) (x y : β) : f (inr x, inr y) = dist x y :=
fA.1.1.1.1.2 x y

private lemma candidates_le_max_var (fA : f ∈ candidates α β) : f (x, y) ≤ max_var α β :=
fA.2 x y

/-- candidates are bounded by max_var α β -/
private lemma candidates_dist_bound  (fA : f ∈ candidates α β) :
  ∀ {x y : α ⊕ β}, f (x, y) ≤ max_var α β * dist x y
| (inl x) (inl y) := calc
    f (inl x, inl y) = dist x y : candidates_dist_inl fA x y
    ... = dist (inl x) (inl y) : by { rw @sum.dist_eq α β, refl }
    ... = 1 * dist (inl x) (inl y) : by simp
    ... ≤ max_var α β * dist (inl x) (inl y) :
      mul_le_mul_of_nonneg_right (one_le_max_var α β) dist_nonneg
| (inl x) (inr y) := calc
    f (inl x, inr y) ≤ max_var α β : candidates_le_max_var fA
    ... = max_var α β * 1 : by simp
    ... ≤ max_var α β * dist (inl x) (inr y) :
      mul_le_mul_of_nonneg_left sum.one_dist_le (le_trans (zero_le_one) (one_le_max_var α β))
| (inr x) (inl y) := calc
    f (inr x, inl y) ≤ max_var α β : candidates_le_max_var fA
    ... = max_var α β * 1 : by simp
    ... ≤ max_var α β * dist (inl x) (inr y) :
      mul_le_mul_of_nonneg_left sum.one_dist_le (le_trans (zero_le_one) (one_le_max_var α β))
| (inr x) (inr y) := calc
    f (inr x, inr y) = dist x y : candidates_dist_inr fA x y
    ... = dist (inr x) (inr y) : by { rw @sum.dist_eq α β, refl }
    ... = 1 * dist (inr x) (inr y) : by simp
    ... ≤ max_var α β * dist (inr x) (inr y) :
      mul_le_mul_of_nonneg_right (one_le_max_var α β) dist_nonneg

/-- Technical lemma to prove that candidates are Lipschitz -/
private lemma candidates_lipschitz_aux (fA : f ∈ candidates α β) : f (x, y) - f (z, t) ≤ 2 * max_var α β * dist (x, y) (z, t) :=
calc
  f (x, y) - f(z, t) ≤ f (x, t) + f (t, y) - f (z, t) : add_le_add_right (candidates_triangle fA) _
  ... ≤ (f (x, z) + f (z, t) + f(t, y)) - f (z, t) :
    add_le_add_right (add_le_add_right (candidates_triangle fA) _ ) _
  ... = f (x, z) + f (t, y) : by simp
  ... ≤ max_var α β * dist x z + max_var α β * dist t y :
    add_le_add (candidates_dist_bound fA) (candidates_dist_bound fA)
  ... ≤ max_var α β * max (dist x z) (dist t y) + max_var α β * max (dist x z) (dist t y) :
  begin
    apply add_le_add,
    apply mul_le_mul_of_nonneg_left (le_max_left (dist x z) (dist t y)) (le_trans zero_le_one (one_le_max_var α β)),
    apply mul_le_mul_of_nonneg_left (le_max_right (dist x z) (dist t y)) (le_trans zero_le_one (one_le_max_var α β)),
  end
  ... = 2 * max_var α β * max (dist x z) (dist y t) :
    by { simp [dist_comm], ring }
  ... = 2 * max_var α β * dist (x, y) (z, t) : by refl

/-- Candidates are Lipschitz -/
private lemma candidates_lipschitz (fA : f ∈ candidates α β) (p q : (α ⊕ β) × (α ⊕ β)) :
  dist (f p) (f q) ≤ 2 * max_var α β * dist p q :=
begin
  rcases p with ⟨x, y⟩,
  rcases q with ⟨z, t⟩,
  rw real.dist_eq,
  apply abs_le_of_le_of_neg_le,
  { exact candidates_lipschitz_aux fA },
  { have : -(f (x, y) - f (z, t)) = f (z, t) - f (x, y), by ring,
    rw [this, dist_comm],
    exact candidates_lipschitz_aux fA }
end

/-- candidates give rise to elements of bounded_continuous_functions -/
def candidates_b_of_candidates (f : prod_space_fun α β) (fA : f ∈ candidates α β) : Cb α β :=
bounded_continuous_function.mk_of_compact f (continuous_of_lipschitz (candidates_lipschitz fA))

lemma candidates_b_of_candidates_mem (f : prod_space_fun α β) (fA : f ∈ candidates α β) :
  candidates_b_of_candidates f fA ∈ candidates_b α β := fA

/-- The distance on α ⊕ β is a candidate -/
private lemma dist_mem_candidates : (λp : (α ⊕ β) × (α ⊕ β), dist p.1 p.2) ∈ candidates α β :=
begin
  simp only [candidates, dist_comm, forall_const, and_true, add_comm, eq_self_iff_true,
             and_self, sum.forall, set.mem_set_of_eq, dist_self],
  repeat { split
    <|> exact (λa y z, dist_triangle_left _ _ _)
    <|> exact (λx y, by refl)
    <|> exact (λx y, max_var_bound) }
end

def candidates_b_dist (α : Type u) (β : Type v) [metric_space α] [compact_space α] [inhabited α]
  [metric_space β] [compact_space β] [inhabited β] : Cb α β := candidates_b_of_candidates _ dist_mem_candidates

lemma candidates_b_dist_mem_candidates_b : candidates_b_dist α β ∈ candidates_b α β :=
candidates_b_of_candidates_mem _ _

private lemma candidates_b_ne_empty : candidates_b α β ≠ ∅ :=
ne_empty_of_mem candidates_b_dist_mem_candidates_b

/-- To apply Arzela-Ascoli, we need to check that the set of candidates is closed and equicontinuous.
Equicontinuity follows from the Lipschitz control, we check closedness -/
private lemma closed_candidates_b : is_closed (candidates_b α β) :=
begin
  have I1 : ∀x y, is_closed {f : Cb α β | f (inl x, inl y) = dist x y} :=
    λx y, is_closed_eq continuous_evalx continuous_const,
  have I2 : ∀x y, is_closed {f : Cb α β | f (inr x, inr y) = dist x y } :=
    λx y, is_closed_eq continuous_evalx continuous_const,
  have I3 : ∀x y, is_closed {f : Cb α β | f (x, y) = f (y, x)} :=
    λx y, is_closed_eq continuous_evalx continuous_evalx,
  have I4 : ∀x y z, is_closed {f : Cb α β | f (x, z) ≤ f (x, y) + f (y, z)} :=
    λx y z, is_closed_le continuous_evalx (continuous_add continuous_evalx continuous_evalx),
  have I5 : ∀x, is_closed {f : Cb α β | f (x, x) = 0} :=
    λx, is_closed_eq continuous_evalx continuous_const,
  have I6 : ∀x y, is_closed {f : Cb α β | f (x, y) ≤ max_var α β} :=
    λx y, is_closed_le continuous_evalx continuous_const,
  have : candidates_b α β = (⋂x y, {f : Cb α β | f ((@inl α β x), (@inl α β y)) = dist x y})
               ∩ (⋂x y, {f : Cb α β | f ((@inr α β x), (@inr α β y)) = dist x y})
               ∩ (⋂x y, {f : Cb α β | f (x, y) = f (y, x)})
               ∩ (⋂x y z, {f : Cb α β | f (x, z) ≤ f (x, y) + f (y, z)})
               ∩ (⋂x, {f : Cb α β | f (x, x) = 0})
               ∩ (⋂x y, {f : Cb α β | f (x, y) ≤ max_var α β}) :=
    begin ext, unfold candidates_b, unfold candidates, simp [-sum.forall], refl end,
  rw this,
  repeat { apply is_closed_inter _ _
       <|> apply is_closed_Inter _
       <|> apply I1 _ _
       <|> apply I2 _ _
       <|> apply I3 _ _
       <|> apply I4 _ _ _
       <|> apply I5 _
       <|> apply I6 _ _
       <|> assume x },
end

/-- Compactness of candidates (in bounded_continuous_functions) follows -/
private lemma compact_candidates_b : compact (candidates_b α β) :=
begin
  refine arzela_ascoli₂ (Icc 0 (max_var α β)) compact_Icc (candidates_b α β) closed_candidates_b _ _,
  { rintros f ⟨x1, x2⟩ hf,
    simp only [set.mem_Icc],
    exact ⟨candidates_nonneg hf, candidates_le_max_var hf⟩ },
  { refine equicontinuous_of_continuity_modulus (λt, 2 * max_var α β * t) _ _ _,
    { have : tendsto (λ (t : ℝ), 2 * max_var α β * t) (nhds 0) (nhds (2 * max_var α β * 0)) :=
        tendsto_mul tendsto_const_nhds tendsto_id,
      simpa using this },
    { assume x y f hf,
      exact candidates_lipschitz hf _ _ } }
end

/-- We will then choose the candidate minimizing the Hausdorff distance. Except that we are not
in a metric space setting, so we need to define our custom version of Hausdorff distance,
called HD, and prove its basic properties. -/
def HD (f : Cb α β) := max (supr (λx:α, infi (λy:β, f (inl x, inr y))))
                           (supr (λy:β, infi (λx:α, f (inl x, inr y))))

/- We will show that HD is continuous on bounded_continuous_functions, to deduce that its
minimum on the compact set candidates_b is attained. Since it is defined in terms of
infimum and supremum on ℝ, which is only conditionnally complete, we will need all the time
to check that the defining sets are bounded below or above. This is done in the next few
technical lemmas -/

lemma HD_below_aux1 {f : Cb α β} (C : ℝ) {x : α} : bdd_below (range (λ (y : β), f (inl x, inr y) + C)) :=
let ⟨cf, hcf⟩ := (real.bounded_iff_bdd_below_bdd_above.1 bounded_range).1 in
⟨cf + C, forall_range_iff.2 (λi, add_le_add_right ((λx, hcf (f x) (mem_range_self _)) _) _)⟩

private lemma HD_bound_aux1 (f : Cb α β) (C : ℝ) : bdd_above (range (λ (x : α), infi (λy:β, f (inl x, inr y) + C))) :=
begin
  rcases (real.bounded_iff_bdd_below_bdd_above.1 bounded_range).2 with ⟨Cf, hCf⟩,
  refine ⟨Cf + C, forall_range_iff.2 (λx, _)⟩,
  calc infi (λy:β, f (inl x, inr y) + C) ≤ f (inl x, inr (default β)) + C :
    cinfi_le (HD_below_aux1 C)
    ... ≤ Cf + C : add_le_add ((λx, hCf (f x) (mem_range_self _)) _) (le_refl _)
end

lemma HD_below_aux2 {f : Cb α β} (C : ℝ) {y : β} : bdd_below (range (λ (x : α), f (inl x, inr y) + C)) :=
let ⟨cf, hcf⟩ := (real.bounded_iff_bdd_below_bdd_above.1 bounded_range).1 in
⟨cf + C, forall_range_iff.2 (λi, add_le_add_right ((λx, hcf (f x) (mem_range_self _)) _) _)⟩

private lemma HD_bound_aux2 (f : Cb α β) (C : ℝ) : bdd_above (range (λ (y : β), infi (λx:α, f (inl x, inr y) + C))) :=
begin
  rcases (real.bounded_iff_bdd_below_bdd_above.1 bounded_range).2 with ⟨Cf, hCf⟩,
  refine ⟨Cf + C, forall_range_iff.2 (λy, _)⟩,
  calc infi (λx:α, f (inl x, inr y) + C) ≤ f (inl (default α), inr y) + C :
    cinfi_le (HD_below_aux2 C)
  ... ≤ Cf + C : add_le_add ((λx, hCf (f x) (mem_range_self _)) _) (le_refl _)
end

/-- Explicit bound on HD (dist). This means that when looking for minimizers it will
be sufficient to look for functions with HD(f) bounded by this bound. -/
lemma HD_candidates_b_dist_le : HD (candidates_b_dist α β) ≤ diam (univ : set α) + 1 + diam (univ : set β) :=
begin
  refine max_le (csupr_le (λx, _)) (csupr_le (λy, _)),
  { have A : infi (λy:β, candidates_b_dist α β (inl x, inr y)) ≤ candidates_b_dist α β (inl x, inr (default β)) :=
      cinfi_le (by simpa using HD_below_aux1 0),
    have B : dist (inl x) (inr (default β)) ≤ diam (univ : set α) + 1 + diam (univ : set β) := calc
      dist (inl x) (inr (default β)) = dist x (default α) + 1 + dist (default β) (default β) : rfl
      ... ≤ diam (univ : set α) + 1 + diam (univ : set β) :
      begin
        apply add_le_add (add_le_add _ (le_refl _)),
        exact dist_le_diam_of_mem (bounded_of_compact (compact_univ)) (mem_univ _) (mem_univ _),
        exact dist_le_diam_of_mem (bounded_of_compact (compact_univ)) (mem_univ _) (mem_univ _)
      end,
    exact le_trans A B },
  { have A : infi (λx:α, candidates_b_dist α β (inl x, inr y)) ≤ candidates_b_dist α β (inl (default α), inr y) :=
      cinfi_le (by simpa using HD_below_aux2 0),
    have B : dist (inl (default α)) (inr y) ≤ diam (univ : set α) + 1 + diam (univ : set β) := calc
      dist (inl (default α)) (inr y) = dist (default α) (default α) + 1 + dist (default β) y : rfl
      ... ≤ diam (univ : set α) + 1 + diam (univ : set β) :
      begin
        apply add_le_add (add_le_add _ (le_refl _)),
        exact dist_le_diam_of_mem (bounded_of_compact (compact_univ)) (mem_univ _) (mem_univ _),
        exact dist_le_diam_of_mem (bounded_of_compact (compact_univ)) (mem_univ _) (mem_univ _)
      end,
    exact le_trans A B },
end

/- To check that HD is continuous, we check that it is Lipschitz. As HD is a max, we
prove separately inequalities controlling the two terms (relying too heavily on copy-paste...) -/
private lemma HD_lipschitz_aux1 (f g : Cb α β) :
  supr (λx:α, infi (λy:β, f (inl x, inr y))) ≤ supr (λx:α, infi (λy:β, g (inl x, inr y))) + dist f g :=
begin
  rcases (real.bounded_iff_bdd_below_bdd_above.1 bounded_range).1 with ⟨cg, hcg⟩,
  have Hcg : ∀x, cg ≤ g x := λx, hcg (g x) (mem_range_self _),
  rcases (real.bounded_iff_bdd_below_bdd_above.1 bounded_range).1 with ⟨cf, hcf⟩,
  have Hcf : ∀x, cf ≤ f x := λx, hcf (f x) (mem_range_self _),

  -- prove the inequality but with `dist f g` inside, by using inequalities comparing
  -- supr to supr and infi to infi
  have Z : supr (λx:α, infi (λy:β, f (inl x, inr y))) ≤ supr (λx:α, infi (λy:β, g (inl x, inr y) + dist f g)) :=
    csupr_le_csupr (HD_bound_aux1 _ (dist f g))
      (λx, cinfi_le_cinfi ⟨cf, forall_range_iff.2(λi, Hcf _)⟩ (λy, coe_le_coe_add_dist)),
  -- move the `dist f g` out of the infimum and the supremum, arguing that continuous monotone maps
  -- (here the addition of `dist f g`) preserve infimum and supremum
  have E1 : ∀x, infi (λy:β, g (inl x, inr y)) + dist f g =
             infi ((λz, z + dist f g) ∘ (λy:β, (g (inl x, inr y)))),
  { assume x,
    refine cinfi_of_cinfi_of_monotone_of_continuous (_ : continuous (λ (z : ℝ), z + dist f g)) _ _,
    { exact continuous_add continuous_id continuous_const },
    { assume x y hx, simpa },
    { show bdd_below (range (λ (y : β), g (inl x, inr y))),
        from ⟨cg, forall_range_iff.2(λi, Hcg _)⟩ } },
  have E2 : supr (λx:α, infi (λy:β, g (inl x, inr y))) + dist f g =
         supr ((λz, z + dist f g) ∘ (λx:α, infi (λy:β, g (inl x, inr y)))),
  { refine csupr_of_csupr_of_monotone_of_continuous (_ : continuous (λ (z : ℝ), z + dist f g)) _ _,
    { exact continuous_add continuous_id continuous_const },
    { assume x y hx, simpa },
    { by simpa using HD_bound_aux1 _ 0 } },
  -- deduce the result from the above two steps
  simp only [add_comm] at Z,
  simpa [E2, E1, function.comp]
end

private lemma HD_lipschitz_aux2 (f g : Cb α β) :
  supr (λy:β, infi (λx:α, f (inl x, inr y))) ≤ supr (λy:β, infi (λx:α, g (inl x, inr y))) + dist f g :=
begin
  rcases (real.bounded_iff_bdd_below_bdd_above.1 bounded_range).1 with ⟨cg, hcg⟩,
  have Hcg : ∀x, cg ≤ g x := λx, hcg (g x) (mem_range_self _),
  rcases (real.bounded_iff_bdd_below_bdd_above.1 bounded_range).1 with ⟨cf, hcf⟩,
  have Hcf : ∀x, cf ≤ f x := λx, hcf (f x) (mem_range_self _),

  -- prove the inequality but with `dist f g` inside, by using inequalities comparing
  -- supr to supr and infi to infi
  have Z : supr (λy:β, infi (λx:α, f (inl x, inr y))) ≤ supr (λy:β, infi (λx:α, g (inl x, inr y) + dist f g)) :=
    csupr_le_csupr (HD_bound_aux2 _ (dist f g))
      (λy, cinfi_le_cinfi  ⟨cf, forall_range_iff.2(λi, Hcf _)⟩ (λy, coe_le_coe_add_dist)),
  -- move the `dist f g` out of the infimum and the supremum, arguing that continuous monotone maps
  -- (here the addition of `dist f g`) preserve infimum and supremum
  have E1 : ∀y, infi (λx:α, g (inl x, inr y)) + dist f g =
             infi ((λz, z + dist f g) ∘ (λx:α, (g (inl x, inr y)))),
  { assume y,
    refine cinfi_of_cinfi_of_monotone_of_continuous (_ : continuous (λ (z : ℝ), z + dist f g)) _ _,
    { exact continuous_add continuous_id continuous_const },
    { assume x y hx, simpa },
    { show bdd_below (range (λx:α, g (inl x, inr y))),
        from ⟨cg, forall_range_iff.2(λi, Hcg _)⟩ } },
  have E2 : supr (λy:β, infi (λx:α, g (inl x, inr y))) + dist f g =
         supr ((λz, z + dist f g) ∘ (λy:β, infi (λx:α, g (inl x, inr y)))),
  { refine csupr_of_csupr_of_monotone_of_continuous (_ : continuous (λ (z : ℝ), z + dist f g)) _ _,
    { exact continuous_add continuous_id continuous_const },
    { assume x y hx, simpa },
    { by simpa using HD_bound_aux2 _ 0 } },
  -- deduce the result from the above two steps
  simp only [add_comm] at Z,
  simpa [E2, E1, function.comp]
end

private lemma HD_lipschitz_aux3 (f g : Cb α β) : HD f ≤ HD g + dist f g :=
max_le (le_trans (HD_lipschitz_aux1 f g) (add_le_add_right (le_max_left _ _) _))
       (le_trans (HD_lipschitz_aux2 f g) (add_le_add_right (le_max_right _ _) _))

/-- Conclude that HD, being Lipschitz, is continuous -/
private lemma HD_continuous : continuous (HD : Cb α β → ℝ) :=
uniform_continuous.continuous $ uniform_continuous_of_le_add 1 $
λf g, begin simp, exact HD_lipschitz_aux3 _ _ end

end constructions --section

section consequences
variables (α : Type u) (β : Type v) [metric_space α] [compact_space α] [nonempty α] [metric_space β] [compact_space β] [nonempty β]

/- Now that we have proved that the set of candidates is compact, and that HD is continuous,
we can finally select a candidate minimizing HD. This will be the candidate realizing the
optimal coupling. -/
private lemma exists_minimizer : ∃f ∈ candidates_b α β, ∀g ∈ candidates_b α β, HD f ≤ HD g :=
exists_forall_le_of_compact_of_continuous _ HD_continuous _ compact_candidates_b candidates_b_ne_empty

private definition optimal_GH_dist : Cb α β := classical.some (exists_minimizer α β)

private lemma optimal_GH_dist_mem_candidates_b : optimal_GH_dist α β ∈ candidates_b α β :=
by cases (classical.some_spec (exists_minimizer α β)); assumption

private lemma HD_optimal_GH_dist_le (g : Cb α β) (hg : g ∈ candidates_b α β) : HD (optimal_GH_dist α β) ≤ HD g :=
let ⟨Z1, Z2⟩ := classical.some_spec (exists_minimizer α β) in Z2 g hg

/-- With the optimal candidate, construct a premetric space structure on α ⊕ β, on which the
predistance is given by the candidate. Then, we will identify points at 0 predistance
to obtain a genuine metric space -/
def premetric_optimal_GH_dist : premetric_space (α ⊕ β) :=
{ dist := λp q, optimal_GH_dist α β (p, q),
  dist_self := λx, candidates_refl (optimal_GH_dist_mem_candidates_b α β),
  dist_comm := λx y, candidates_symm (optimal_GH_dist_mem_candidates_b α β),
  dist_triangle := λx y z, candidates_triangle (optimal_GH_dist_mem_candidates_b α β) }

local attribute [instance] premetric_optimal_GH_dist premetric.dist_setoid

/-- A metric space which realizes the optimal coupling between α and β -/
@[reducible] definition optimal_GH_coupling : Type* :=
premetric.metric_quot (α ⊕ β)

instance : metric_space (optimal_GH_coupling α β) := by apply_instance

private lemma optimal_GH_dist.dist_eq (p q : α ⊕ β) : dist ⟦p⟧ ⟦q⟧ = (optimal_GH_dist α β).val (p, q) := rfl

/-- Injection of α in the optimal coupling between α and β -/
def optimal_GH_injl (x : α) : optimal_GH_coupling α β := ⟦inl x⟧

/-- The injection of α in the optimal coupling between α and β is an isometry. -/
lemma isometry_optimal_GH_injl : isometry (optimal_GH_injl α β) :=
begin
  refine isometry_emetric_iff_metric.2 (λx y, _),
  change dist ⟦inl x⟧ ⟦inl y⟧ = dist x y,
  rw [optimal_GH_dist.dist_eq α β],
  exact candidates_dist_inl (optimal_GH_dist_mem_candidates_b α β) _ _,
end

/-- Injection of β  in the optimal coupling between α and β -/
def optimal_GH_injr (y : β) : optimal_GH_coupling α β := ⟦inr y⟧

/-- The injection of β in the optimal coupling between α and β is an isometry. -/
lemma isometry_optimal_GH_injr : isometry (optimal_GH_injr α β) :=
begin
  refine isometry_emetric_iff_metric.2 (λx y, _),
  change dist ⟦inr x⟧ ⟦inr y⟧ = dist x y,
  rw [optimal_GH_dist.dist_eq α β],
  exact candidates_dist_inr (optimal_GH_dist_mem_candidates_b α β) _ _,
end

/-- The optimal coupling between two compact spaces α and β is still a compact space -/
instance compact_space_optimal_GH_coupling : compact_space (optimal_GH_coupling α β) :=
⟨begin
  have : (univ : set (optimal_GH_coupling α β)) =
           (optimal_GH_injl α β '' univ) ∪ (optimal_GH_injr α β '' univ),
  { refine subset.antisymm (λxc hxc, _) (subset_univ _),
    rcases quotient.exists_rep xc with ⟨x, hx⟩,
    cases x; rw ← hx,
    { have : ⟦inl x⟧ = optimal_GH_injl α β x := rfl,
      rw this,
      exact mem_union_left _ (mem_image_of_mem _ (mem_univ _)) },
    { have : ⟦inr x⟧ = optimal_GH_injr α β x := rfl,
      rw this,
      exact mem_union_right _ (mem_image_of_mem _ (mem_univ _)) } },
  rw this,
  exact compact_union_of_compact
    (compact_image (compact_univ) (isometry_optimal_GH_injl α β).continuous)
    (compact_image (compact_univ) (isometry_optimal_GH_injr α β).continuous)
end⟩

/-- For any candidate f, HD(f) is larger than or equal to the Hausdorff distance in the
optimal coupling. This follows from the fact that HD of the optimal candidate is exactly
the Hausdorff distance in the optimal coupling, although we only prove here the inequality
we need. -/
lemma Hausdorff_dist_optimal_le_HD {f} (h : f ∈ candidates_b α β) :
  Hausdorff_dist (range (optimal_GH_injl α β)) (range (optimal_GH_injr α β)) ≤ HD f :=
begin
  refine le_trans (le_of_forall_le_of_dense (λr hr, _)) (HD_optimal_GH_dist_le α β f h),
  have A : ∀ x ∈ range (optimal_GH_injl α β), ∃ y ∈ range (optimal_GH_injr α β), dist x y ≤ r,
  { assume x hx,
    rcases mem_range.1 hx with ⟨z, hz⟩,
    rw ← hz,
    have I1 : supr (λx:α, infi (λy:β, optimal_GH_dist α β (inl x, inr y))) < r :=
      lt_of_le_of_lt (le_max_left _ _) hr,
    have I2 : infi (λy:β, optimal_GH_dist α β (inl z, inr y)) ≤
        supr (λx:α, infi (λy:β, optimal_GH_dist α β (inl x, inr y))) :=
      le_cSup (by simpa using HD_bound_aux1 _ 0) (mem_range_self _),
    have I : infi (λy:β, optimal_GH_dist α β (inl z, inr y)) < r := lt_of_le_of_lt I2 I1,
    rcases exists_lt_of_cInf_lt (by simpa) I with ⟨r', r'range, hr'⟩,
    rcases mem_range.1 r'range with ⟨z', hz'⟩,
    existsi [optimal_GH_injr α β z', mem_range_self _],
    have : (optimal_GH_dist α β) (inl z, inr z') ≤ r := begin rw hz', exact le_of_lt hr' end,
    exact this },
  refine Hausdorff_dist_le_of_mem_dist _ A _,
  { rcases exists_mem_of_nonempty α with ⟨xα, _⟩,
    have : optimal_GH_injl α β xα ∈ range (optimal_GH_injl α β) := mem_range_self _,
    rcases A _ this with ⟨y, yrange, hy⟩,
    exact le_trans dist_nonneg hy },
  { assume y hy,
    rcases mem_range.1 hy with ⟨z, hz⟩,
    rw ← hz,
    have I1 : supr (λy:β, infi (λx:α, optimal_GH_dist α β (inl x, inr y))) < r :=
      lt_of_le_of_lt (le_max_right _ _) hr,
    have I2 : infi (λx:α, optimal_GH_dist α β (inl x, inr z)) ≤
        supr (λy:β, infi (λx:α, optimal_GH_dist α β (inl x, inr y))) :=
      le_cSup (by simpa using HD_bound_aux2 _ 0) (mem_range_self _),
    have I : infi (λx:α, optimal_GH_dist α β (inl x, inr z)) < r := lt_of_le_of_lt I2 I1,
    rcases exists_lt_of_cInf_lt (by simpa) I with ⟨r', r'range, hr'⟩,
    rcases mem_range.1 r'range with ⟨z', hz'⟩,
    existsi [optimal_GH_injl α β z', mem_range_self _],
    have : (optimal_GH_dist α β) (inl z', inr z) ≤ r := begin rw hz', exact le_of_lt hr' end,
    rw dist_comm,
    exact this }
end

end consequences
/- We are done with the construction of the optimal coupling -/
end Gromov_Hausdorff_realized

end Gromov_Hausdorff

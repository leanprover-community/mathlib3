/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.metric_space.basic
import measure_theory.constructions.borel_space

/-!
# Vitali covering theorem
-/

variables {α : Type*}

open set
open_locale classical

/-- Vitali covering theorem: given a set `t` of subsets of a type, one may extract a disjoint
subfamily `u` such that the `τ`-enlargment of this family covers all elements of `t`, where `τ > 1`
is any fixed number.

When `t` is a family of balls, the `τ`-enlargment of `ball x r` is `ball x ((1+2τ) r)`. In general,
it is expressed in terms of a function `δ` (think "radius" or "diameter"), positive and bounded on
all elements of `t`. The condition is that every element `a` of `t` should intersect an
element `b` of `u` of size larger than that of `a` up to `τ`, i.e., `δ b ≥ δ a / τ`. -/
theorem vitali (t : set (set α)) (δ : set α → ℝ) (τ : ℝ) (hτ : 1 < τ) (δpos : ∀ a ∈ t, 0 < δ a)
  (R : ℝ) (δle : ∀ a ∈ t, δ a ≤ R) (hne : ∀ a ∈ t, set.nonempty a) :
  ∃ u ⊆ t, u.pairwise_on (disjoint on id) ∧
    ∀ a ∈ t, ∃ b ∈ u, set.nonempty (a ∩ b) ∧ δ a ≤ τ * δ b :=
begin
  /- The proof could be formulated by a transfinite induction. First pick an element of `t` with `δ`
  as large as possible (up to a factor of `τ`). Then among the remaining elements not intersecting
  the already chosen one, pick another element with large `δ`. Go on forever (transfinitely) until
  there is nothing left.

  Instead, we give a direct Zorn-based argument. Consider a maximal family `u` of disjoint sets
  with the following property: if an element `a` of `t` intersects some element `b` of `u`, then it
  intersects some `b' ∈ u` with `δ b' ≥ δ a / τ`. Such a maximal family exists by Zorn. If this
  family did not intersect some element `a ∈ t`, then take an element `a' ∈ t` which does not
  intersect any element of `u`, with `δ a'` almost as large as possible. One checks easily
  that `u ∪ {a'}` still has this property, contradicting the maximality. Therefore, `u`
  intersects all elements of `t`, and by definition it satisfies all the desired properties.
  -/
  let T : set (set (set α)) := {u | u ⊆ t ∧ u.pairwise_on (disjoint on id)
    ∧ ∀ a ∈ t, ∀ b ∈ u, set.nonempty (a ∩ b) → ∃ c ∈ u, (a ∩ c).nonempty ∧ δ a ≤ τ * δ c},
  -- By Zorn, choose a maximal family in the good set `T` of disjoint families.
  obtain ⟨u, uT, hu⟩ : ∃ u ∈ T, ∀ v ∈ T, u ⊆ v → v = u,
  { refine zorn.zorn_subset _ (λ U UT hU, _),
    refine ⟨⋃₀ U, _, λ s hs, subset_sUnion_of_mem hs⟩,
    simp only [set.sUnion_subset_iff, and_imp, exists_prop, forall_exists_index,
                set.mem_set_of_eq],
    refine ⟨λ u hu, (UT hu).1, _, λ a hat b u uU hbu hab, _⟩,
    { rw [pairwise_on_sUnion hU.directed_on],
      assume u hu,
      exact (UT hu).2.1 },
    { obtain ⟨c, cu, ac, hc⟩ : ∃ (c : set α) (H : c ∈ u), (a ∩ c).nonempty ∧ δ a ≤ τ * δ c :=
        (UT uU).2.2 a hat b hbu hab,
      exact ⟨c, ⟨u, uU, cu⟩, ac, hc⟩ } },
  -- the only nontrivial bit is to check that every `a ∈ t` intersects an element `b ∈ u` with
  -- comparatively large `δ b`. Assume this is not the case, then we will contradict the maximality.
  refine ⟨u, uT.1, uT.2.1, λ a hat, _⟩,
  contrapose! hu,
  have a_disj : ∀ c ∈ u, disjoint a c,
  { assume c hc,
    by_contra,
    rw not_disjoint_iff_nonempty_inter at h,
    obtain ⟨d, du, ad, hd⟩ : ∃ (d : set α) (H : d ∈ u), (a ∩ d).nonempty ∧ δ a ≤ τ * δ d :=
      uT.2.2 a hat c hc h,
    exact lt_irrefl _ ((hu d du ad).trans_le hd) },
  -- Let `A` be all the elements of `t` which do not intersect the family `u`. It is nonempty as it
  -- contains `a`. We will pick an element `a'` of `A` with `δ a'` as large as possible.
  let A := {a' | a' ∈ t ∧ ∀ c ∈ u, disjoint a' c},
  have Anonempty : A.nonempty := ⟨a, hat, a_disj⟩,
  let m := Sup (δ '' A),
  have bddA : bdd_above (δ '' A),
  { refine ⟨R, λ x xA, _⟩,
    rcases (mem_image _ _ _).1 xA with ⟨a', ha', rfl⟩,
    exact δle a' ha'.1 },
  have mpos : 0 < m,
  { have : δ a ≤ m := le_cSup bddA (mem_image_of_mem _ ⟨hat, a_disj⟩),
    exact (δpos a hat).trans_le this },
  clear hat hu a_disj a,
  have I : m / τ < m,
  { rw div_lt_iff (zero_lt_one.trans hτ),
    conv_lhs { rw ← mul_one m },
    exact (mul_lt_mul_left mpos).2 hτ },
  -- choose `a'` in `A` with `δ a'` as large as possible (up to the factor `τ > 1`).
  obtain ⟨a', a'A, ha'⟩ : ∃ a' ∈ A, m / τ < δ a',
  { rcases exists_lt_of_lt_cSup (nonempty_image_iff.2 Anonempty) I with ⟨x, xA, hx⟩,
    rcases (mem_image _ _ _).1 xA with ⟨a', ha', rfl⟩,
    exact ⟨a', ha', hx⟩, },
  have a'_ne_u : a' ∉ u := λ H, (hne _ a'A.1).ne_empty (disjoint_self.1 (a'A.2 _ H)),
  -- we claim that `u ∪ {a'}` still belongs to `T`, contradicting the maximality of `u`.
  refine ⟨insert a' u, ⟨_, _, _⟩, subset_insert _ _, (ne_insert_of_not_mem _ a'_ne_u).symm⟩,
  -- check that `u ∪ {a'}` is made of elements of `t`.
  { rw insert_subset,
    exact ⟨a'A.1, uT.1⟩ },
  -- check that `u ∪ {a'}` is a disjoint family. This follows from the fact that `a'` does not
  -- intersect `u`.
  { rw pairwise_on_insert_of_symmetric, swap,
    { simp only [function.on_fun, symmetric, disjoint.comm, imp_self, forall_const] },
    exact ⟨uT.2.1, λ b bu ba', a'A.2 b bu⟩ },
  -- check that every element `c` of `t` intersecting `u ∪ {a'}` intersects an element of this family
  -- with large `δ`.
  { assume c ct b ba'u hcb,
    -- if `c` already intersects an element of `u`, then it intersects an element of `u` with
    -- large `δ` by the assumption on `u`, and there is nothing left to do.
    by_cases H : ∃ d ∈ u, set.nonempty (c ∩ d),
    { rcases H with ⟨d, du, hd⟩,
      rcases uT.2.2 c ct d du hd with ⟨d', d'u, hd'⟩,
      exact ⟨d', mem_insert_of_mem _ d'u, hd'⟩ },
    -- otherwise, `c` belongs to `A`. The element of `u ∪ {a'}` that it intersects has to be `a'`.
    -- moreover, `δ c` is smaller than the maximum `m` of `δ` over `A`, which is `≤ δ a' / τ` thanks
    -- to the good choice of `a'`. This is the desired inequality.
    { push_neg at H,
      simp only [← not_disjoint_iff_nonempty_inter, not_not] at H,
      rcases mem_insert_iff.1 ba'u with rfl|H',
      { refine ⟨b, mem_insert _ _, hcb, _⟩,
        calc δ c ≤ m : le_cSup bddA (mem_image_of_mem _ ⟨ct, H⟩)
        ... = τ * (m / τ) : by { field_simp [(zero_lt_one.trans hτ).ne'], ring }
        ... ≤ τ * δ b : mul_le_mul_of_nonneg_left ha'.le (zero_le_one.trans hτ.le) },
      { rw ← not_disjoint_iff_nonempty_inter at hcb,
        exact (hcb (H _ H')).elim } } }
end


open metric measure_theory set
open_locale nnreal

theorem measurable_vitali [metric_space α] [measurable_space α] [opens_measurable_space α]
  (μ : measure α) [is_locally_finite_measure μ] (s : set α)
  (t : set (set α)) (hf : ∀ x ∈ s, ∀ (ε > (0 : ℝ)), ∃ a ∈ t, x ∈ a ∧ diam a < ε)
  (ht : ∀ a ∈ t, (interior a).nonempty) (h't : ∀ a ∈ t, is_closed a)
  (C : ℝ≥0) (h : ∀ a ∈ t, ∀ x ∈ a, μ (closed_ball x (5 * diam a)) ≤ C * μ a) :
  ∃ u ⊆ t, countable u ∧ u.pairwise_on (disjoint on id) ∧ μ (s \ ⋃ (a ∈ u), a) = 0 :=
sorry

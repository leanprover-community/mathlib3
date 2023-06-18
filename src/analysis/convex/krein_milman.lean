/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import analysis.convex.exposed
import analysis.normed_space.hahn_banach.separation

/-!
# The Krein-Milman theorem

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves the Krein-Milman lemma and the Krein-Milman theorem.

## The lemma

The lemma states that a nonempty compact set `s` has an extreme point. The proof goes:
1. Using Zorn's lemma, find a minimal nonempty closed `t` that is an extreme subset of `s`. We will
  show that `t` is a singleton, thus corresponding to an extreme point.
2. By contradiction, `t` contains two distinct points `x` and `y`.
3. With the (geometric) Hahn-Banach theorem, find an hyperplane that separates `x` and `y`.
4. Look at the extreme (actually exposed) subset of `t` obtained by going the furthest away from
  the separating hyperplane in the direction of `x`. It is nonempty, closed and an extreme subset
  of `s`.
5. It is a strict subset of `t` (`y` isn't in it), so `t` isn't minimal. Absurd.

## The theorem

The theorem states that a compact convex set `s` is the closure of the convex hull of its extreme
points. It is an almost immediate strengthening of the lemma. The proof goes:
1. By contradiction, `s \ closure (convex_hull ℝ (extreme_points ℝ s))` is nonempty, say with `x`.
2. With the (geometric) Hahn-Banach theorem, find an hyperplane that separates `x` from
  `closure (convex_hull ℝ (extreme_points ℝ s))`.
3. Look at the extreme (actually exposed) subset of
  `s \ closure (convex_hull ℝ (extreme_points ℝ s))` obtained by going the furthest away from the
  separating hyperplane. It is nonempty by assumption of nonemptiness and compactness, so by the
  lemma it has an extreme point.
4. This point is also an extreme point of `s`. Absurd.

## Related theorems

When the space is finite dimensional, the `closure` can be dropped to strengthen the result of the
Krein-Milman theorem. This leads to the Minkowski-Carathéodory theorem (currently not in mathlib).
Birkhoff's theorem is the Minkowski-Carathéodory theorem applied to the set of bistochastic
matrices, permutation matrices being the extreme points.

## References

See chapter 8 of [Barry Simon, *Convexity*][simon2011]

-/

open set
open_locale classical

variables {E : Type*} [add_comm_group E] [module ℝ E] [topological_space E] [t2_space E]
  [topological_add_group E] [has_continuous_smul ℝ E] [locally_convex_space ℝ E] {s : set E}

/-- **Krein-Milman lemma**: In a LCTVS, any nonempty compact set has an extreme point. -/
lemma is_compact.has_extreme_point (hscomp : is_compact s) (hsnemp : s.nonempty) :
  (s.extreme_points ℝ).nonempty :=
begin
  let S : set (set E) := {t | t.nonempty ∧ is_closed t ∧ is_extreme ℝ s t},
  rsuffices ⟨t, ⟨⟨x, hxt⟩, htclos, hst⟩, hBmin⟩ : ∃ t ∈ S, ∀ u ∈ S, u ⊆ t → u = t,
  { refine ⟨x, mem_extreme_points_iff_extreme_singleton.2 _⟩,
    rwa ←eq_singleton_iff_unique_mem.2 ⟨hxt, λ y hyB, _⟩,
    by_contra hyx,
    obtain ⟨l, hl⟩ := geometric_hahn_banach_point_point hyx,
    obtain ⟨z, hzt, hz⟩ := (is_compact_of_is_closed_subset hscomp htclos hst.1).exists_forall_ge
      ⟨x, hxt⟩ l.continuous.continuous_on,
    have h : is_exposed ℝ t {z ∈ t | ∀ w ∈ t, l w ≤ l z} := λ h, ⟨l, rfl⟩,
    rw ←hBmin {z ∈ t | ∀ w ∈ t, l w ≤ l z} ⟨⟨z, hzt, hz⟩, h.is_closed htclos, hst.trans
      h.is_extreme⟩ (t.sep_subset _) at hyB,
    exact hl.not_le (hyB.2 x hxt) },
  refine zorn_superset _ (λ F hFS hF, _),
  obtain rfl | hFnemp := F.eq_empty_or_nonempty,
  { exact ⟨s, ⟨hsnemp, hscomp.is_closed, is_extreme.rfl⟩, λ _, false.elim⟩ },
  refine ⟨⋂₀ F, ⟨_, is_closed_sInter $ λ t ht, (hFS ht).2.1, is_extreme_sInter hFnemp $
    λ t ht, (hFS ht).2.2⟩, λ t ht, sInter_subset_of_mem ht⟩,
  haveI : nonempty ↥F := hFnemp.to_subtype,
  rw sInter_eq_Inter,
  refine is_compact.nonempty_Inter_of_directed_nonempty_compact_closed _ (λ t u, _)
    (λ t, (hFS t.mem).1)
    (λ t, is_compact_of_is_closed_subset hscomp (hFS t.mem).2.1 (hFS t.mem).2.2.1)
    (λ t, (hFS t.mem).2.1),
  obtain htu | hut := hF.total t.mem u.mem,
  exacts [⟨t, subset.rfl, htu⟩, ⟨u, hut, subset.rfl⟩],
end

/-- **Krein-Milman theorem**: In a LCTVS, any compact convex set is the closure of the convex hull
    of its extreme points. -/
lemma closure_convex_hull_extreme_points (hscomp : is_compact s) (hAconv : convex ℝ s) :
  closure (convex_hull ℝ $ s.extreme_points ℝ) = s :=
begin
  apply (closure_minimal (convex_hull_min extreme_points_subset hAconv) hscomp.is_closed).antisymm,
  by_contra hs,
  obtain ⟨x, hxA, hxt⟩ := not_subset.1 hs,
  obtain ⟨l, r, hlr, hrx⟩ := geometric_hahn_banach_closed_point (convex_convex_hull _ _).closure
    is_closed_closure hxt,
  have h : is_exposed ℝ s {y ∈ s | ∀ z ∈ s, l z ≤ l y} := λ _, ⟨l, rfl⟩,
  obtain ⟨z, hzA, hz⟩ := hscomp.exists_forall_ge ⟨x, hxA⟩ l.continuous.continuous_on,
  obtain ⟨y, hy⟩ := (h.is_compact hscomp).has_extreme_point ⟨z, hzA, hz⟩,
  linarith [hlr _ (subset_closure $ subset_convex_hull _ _ $
    h.is_extreme.extreme_points_subset_extreme_points hy), hy.1.2 x hxA],
end

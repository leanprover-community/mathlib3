/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.metric_space.basic
import measure_theory.constructions.borel_space
import measure_theory.covering.vitali_family

/-!
# Vitali covering theorems

The topological Vitali covering theorem, in its most classical version, states the following.
Consider a family of balls `(B (x_i, r_i))_{i ∈ I}` in a metric space, with uniformly bounded
radii. Then one can extract a disjoint subfamily indexed by `J ⊆ I`, such that any `B (x_i, r_i)`
is included in a ball `B (x_j, 5 r_j)`.

We prove this theorem in `vitali.exists_disjoint_subfamily_covering_enlargment_closed_ball`.
It is deduced from a more general version, called
`vitali.exists_disjoint_subfamily_covering_enlargment`, which applies to any family of sets
together with a size function `δ` (think "radius" or "diameter").

We deduce the measurable Vitali covering theorem. Assume one is given a family `t` of closed sets
with nonempty interior, such that each `a ∈ t` is included in a ball `B (x, r)` and covers a
definite proportion of the ball `B (x, 6 r)` for a given measure `μ` (think of the situation
where `μ` is a doubling measure and `t` is a family of balls). Consider a set `s` at which the
family is fine, i.e., every point of `s` belongs to arbitrarily small elements of `t`. Then one
can extract from `t` a disjoint subfamily that covers almost all `s`. It is proved in
`vitali.exists_disjoint_covering_ae`.

A way to restate this theorem is to say that the set of closed sets `a` with nonempty interior
covering a fixed proportion `1/C` of the ball `closed_ball x (3 * diam a)` forms a Vitali family.
This version is given in `vitali.vitali_family`.
-/

variables {α : Type*}

open set metric measure_theory topological_space filter
open_locale nnreal classical ennreal topological_space

namespace vitali

/-- Vitali covering theorem: given a set `t` of subsets of a type, one may extract a disjoint
subfamily `u` such that the `τ`-enlargment of this family covers all elements of `t`, where `τ > 1`
is any fixed number.

When `t` is a family of balls, the `τ`-enlargment of `ball x r` is `ball x ((1+2τ) r)`. In general,
it is expressed in terms of a function `δ` (think "radius" or "diameter"), positive and bounded on
all elements of `t`. The condition is that every element `a` of `t` should intersect an
element `b` of `u` of size larger than that of `a` up to `τ`, i.e., `δ b ≥ δ a / τ`.
-/
theorem exists_disjoint_subfamily_covering_enlargment
  (t : set (set α)) (δ : set α → ℝ) (τ : ℝ) (hτ : 1 < τ) (δnonneg : ∀ a ∈ t, 0 ≤ δ a)
  (R : ℝ) (δle : ∀ a ∈ t, δ a ≤ R) (hne : ∀ a ∈ t, set.nonempty a) :
  ∃ u ⊆ t, u.pairwise_on disjoint ∧
    ∀ a ∈ t, ∃ b ∈ u, set.nonempty (a ∩ b) ∧ δ a ≤ τ * δ b :=
begin
  /- The proof could be formulated as a transfinite induction. First pick an element of `t` with `δ`
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
  let T : set (set (set α)) := {u | u ⊆ t ∧ u.pairwise_on disjoint
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
  -- contains `a`. We will pick an element `a'` of `A` with `δ a'` almost as large as possible.
  let A := {a' | a' ∈ t ∧ ∀ c ∈ u, disjoint a' c},
  have Anonempty : A.nonempty := ⟨a, hat, a_disj⟩,
  let m := Sup (δ '' A),
  have bddA : bdd_above (δ '' A),
  { refine ⟨R, λ x xA, _⟩,
    rcases (mem_image _ _ _).1 xA with ⟨a', ha', rfl⟩,
    exact δle a' ha'.1 },
  obtain ⟨a', a'A, ha'⟩ : ∃ a' ∈ A, m / τ ≤ δ a',
  { have : 0 ≤ m := (δnonneg a hat).trans (le_cSup bddA (mem_image_of_mem _ ⟨hat, a_disj⟩)),
    rcases eq_or_lt_of_le this with mzero|mpos,
    { refine ⟨a, ⟨hat, a_disj⟩, _⟩,
      simpa only [← mzero, zero_div] using δnonneg a hat },
    { have I : m / τ < m,
      { rw div_lt_iff (zero_lt_one.trans hτ),
        conv_lhs { rw ← mul_one m },
        exact (mul_lt_mul_left mpos).2 hτ },
      rcases exists_lt_of_lt_cSup (nonempty_image_iff.2 Anonempty) I with ⟨x, xA, hx⟩,
      rcases (mem_image _ _ _).1 xA with ⟨a', ha', rfl⟩,
      exact ⟨a', ha', hx.le⟩, } },
  clear hat hu a_disj a,
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
  -- check that every element `c` of `t` intersecting `u ∪ {a'}` intersects an element of this
  -- family with large `δ`.
  { assume c ct b ba'u hcb,
    -- if `c` already intersects an element of `u`, then it intersects an element of `u` with
    -- large `δ` by the assumption on `u`, and there is nothing left to do.
    by_cases H : ∃ d ∈ u, set.nonempty (c ∩ d),
    { rcases H with ⟨d, du, hd⟩,
      rcases uT.2.2 c ct d du hd with ⟨d', d'u, hd'⟩,
      exact ⟨d', mem_insert_of_mem _ d'u, hd'⟩ },
    -- otherwise, `c` belongs to `A`. The element of `u ∪ {a'}` that it intersects has to be `a'`.
    -- moreover, `δ c` is smaller than the maximum `m` of `δ` over `A`, which is `≤ δ a' / τ`
    -- thanks to the good choice of `a'`. This is the desired inequality.
    { push_neg at H,
      simp only [← not_disjoint_iff_nonempty_inter, not_not] at H,
      rcases mem_insert_iff.1 ba'u with rfl|H',
      { refine ⟨b, mem_insert _ _, hcb, _⟩,
        calc δ c ≤ m : le_cSup bddA (mem_image_of_mem _ ⟨ct, H⟩)
        ... = τ * (m / τ) : by { field_simp [(zero_lt_one.trans hτ).ne'], ring }
        ... ≤ τ * δ b : mul_le_mul_of_nonneg_left ha' (zero_le_one.trans hτ.le) },
      { rw ← not_disjoint_iff_nonempty_inter at hcb,
        exact (hcb (H _ H')).elim } } }
end

/-- Vitali covering theorem, closed balls version: given a family `t` of closed balls, one can
extract a disjoint subfamily `u ⊆ t` so that all balls in `t` are covered by the 5-times
dilations of balls in `u`. -/
theorem exists_disjoint_subfamily_covering_enlargment_closed_ball [metric_space α]
  (t : set (set α)) (R : ℝ) (ht : ∀ s ∈ t, ∃ x r, s = closed_ball x r ∧ r ≤ R) :
  ∃ u ⊆ t, u.pairwise_on disjoint ∧
    ∀ a ∈ t, ∃ x r, closed_ball x r ∈ u ∧ a ⊆ closed_ball x (5 * r) :=
begin
  rcases eq_empty_or_nonempty t with rfl|tnonempty,
  { exact ⟨∅, subset.refl _, by simp⟩ },
  haveI : inhabited α,
  { choose s hst using tnonempty,
    choose x r hxr using ht s hst,
    exact ⟨x⟩ },
  -- Exclude the trivial case where `t` is reduced to the empty set.
  rcases eq_or_ne t {∅} with rfl|t_ne_empty,
  { refine ⟨{∅}, subset.refl _, _⟩,
    simp only [true_and, closed_ball_eq_empty, mem_singleton_iff, and_true, empty_subset, forall_eq,
      pairwise_on_singleton, exists_const],
    exact ⟨-1, by simp only [right.neg_neg_iff, zero_lt_one]⟩ },
  -- The real proof starts now. Since the center or the radius of a ball is not uniquely defined
  -- in a general metric space, we just choose one for definiteness.
  choose! x r hxr using ht,
  have r_nonneg : ∀ (a : set α), a ∈ t → a.nonempty → 0 ≤ r a,
  { assume a hat a_nonempty,
    rw (hxr a hat).1 at a_nonempty,
    simpa only [nonempty_closed_ball] using a_nonempty },
  -- The difference with the generic version is that we are not excluding empty sets in our family
  -- (which would correspond to `r a < 0`). To compensate for this, we apply the generic version
  -- to the subfamily `t'` made of nonempty sets, and we use `δ = r` there. This gives a disjointed
  -- subfamily `u'`.
  let t' := {a ∈ t | 0 ≤ r a},
  obtain ⟨u', u't', u'_disj, hu'⟩ : ∃ u' ⊆ t', u'.pairwise_on disjoint ∧
    ∀ a ∈ t', ∃ b ∈ u', set.nonempty (a ∩ b) ∧ r a ≤ 2 * r b,
  { refine exists_disjoint_subfamily_covering_enlargment t' r 2 one_lt_two
      (λ a ha, ha.2) R (λ a ha, (hxr a ha.1).2) (λ a ha, _),
    rw [(hxr a ha.1).1],
    simp only [ha.2, nonempty_closed_ball] },
  -- this subfamily is nonempty, as we have excluded the situation `t = {∅}`.
  have u'_nonempty : u'.nonempty,
  { have : ∃ a ∈ t, a ≠ ∅,
    { contrapose! t_ne_empty,
      apply subset.antisymm,
      { simpa only using t_ne_empty },
      { rcases tnonempty with ⟨a, hat⟩,
        have := t_ne_empty a hat,
        simpa only [this, singleton_subset_iff] using hat } },
    rcases this with ⟨a, hat, a_nonempty⟩,
    have ranonneg : 0 ≤ r a := r_nonneg a hat (ne_empty_iff_nonempty.1 a_nonempty),
    rcases hu' a ⟨hat, ranonneg⟩ with ⟨b, bu', hb⟩,
    exact ⟨b, bu'⟩ },
  -- check that the family `u'` gives the desired disjoint covering.
  refine ⟨u', λ a ha, (u't' ha).1, u'_disj, λ a hat, _⟩,
  -- it remains to check that any ball in `t` is contained in the 5-dilation of a ball
  -- in `u'`. This depends on whether the ball is empty of not.
  rcases eq_empty_or_nonempty a with rfl|a_nonempty,
  -- if the ball is empty, use any element of `u'` (since we know that `u'` is nonempty).
  { rcases u'_nonempty with ⟨b, hb⟩,
    refine ⟨x b, r b, _, empty_subset _⟩,
    rwa ← (hxr b (u't' hb).1).1 },
  -- if the ball is not empty, it belongs to `t'`. Then it intersects a ball `a'` in `u'` with
  -- controlled radius, by definition of `u'`. It is straightforward to check that this ball
  -- satisfies all the desired properties.
  { have hat' : a ∈ t' := ⟨hat, r_nonneg a hat a_nonempty⟩,
    obtain ⟨a', a'u', aa', raa'⟩ :
      (∃ (a' : set α) (H : a' ∈ u'), (a ∩ a').nonempty ∧ r a ≤ 2 * r a') := hu' a hat',
    refine ⟨x a', r a', _, _⟩,
    { convert a'u',
      exact (hxr a' (u't' a'u').1).1.symm },
    { rw (hxr a hat'.1).1 at aa' ⊢,
      rw (hxr a' (u't' a'u').1).1 at aa',
      have : dist (x a) (x a') ≤ r a + r a' :=
        dist_le_add_of_nonempty_closed_ball_inter_closed_ball aa',
      apply closed_ball_subset_closed_ball',
      linarith } }
end

/-- The measurable Vitali covering theorem. Assume one is given a family `t` of closed sets with
nonempty interior, such that each `a ∈ t` is included in a ball `B (x, r)` and covers a definite
proportion of the ball `B (x, 6 r)` for a given measure `μ` (think of the situation where `μ` is
a doubling measure and `t` is a family of balls). Consider a (possible non-measurable) set `s`
at which the family is fine, i.e., every point of `s` belongs to arbitrarily small elements of `t`.
Then one can extract from `t` a disjoint subfamily that covers almost all `s`. -/
theorem exists_disjoint_covering_ae [metric_space α] [measurable_space α] [opens_measurable_space α]
  [second_countable_topology α]
  (μ : measure α) [is_locally_finite_measure μ] (s : set α)
  (t : set (set α)) (hf : ∀ x ∈ s, ∀ (ε > (0 : ℝ)), ∃ a ∈ t, x ∈ a ∧ a ⊆ closed_ball x ε)
  (ht : ∀ a ∈ t, (interior a).nonempty) (h't : ∀ a ∈ t, is_closed a)
  (C : ℝ≥0) (h : ∀ a ∈ t, ∃ x ∈ a, μ (closed_ball x (3 * diam a)) ≤ C * μ a) :
  ∃ u ⊆ t, countable u ∧ u.pairwise_on disjoint ∧ μ (s \ ⋃ (a ∈ u), a) = 0 :=
begin
  /- The idea of the proof is the following. Assume for simplicity that `μ` is finite. Applying the
  abstract Vitali covering theorem with `δ = diam`, one obtains a disjoint subfamily `u`, such
  that any element of `t` intersects an element of `u` with comparable diameter. Fix `ε > 0`.
  Since the elements of `u` have summable measure, one can remove finitely elements `w_1, ..., w_n`.
  so that the measure of the remaining elements is `< ε`. Consider now a point `z` not
  in the `w_i`. There is a small ball around `z` not intersecting the `w_i` (as they are closed),
  an element `a ∈ t` contained in this small ball (as the family `t` is fine at `z`) and an element
  `b ∈ u` intersecting `a`, with comparable diameter (by definition of `u`). Then `z` belongs to the
  enlargement of `b`. This shows that `s \ (w_1 ∪ ... ∪ w_n)` is contained in
  `⋃ (b ∈ u \ {w_1, ... w_n}) (enlargement of b)`. The measure of the latter set is bounded by
  `∑ (b ∈ u \ {w_1, ... w_n}) C * μ b` (by the doubling property of the measure), which is at most
  `C ε`. Letting `ε` tend to `0` shows that `s` is almost everywhere covered by the family `u`.

  For the real argument, the measure is only locally finite. Therefore, we implement the same
  strategy, but locally restricted to balls on which the measure is finite. For this, we do not
  use the whole family `t`, but a subfamily `t'` supported on small balls (which is possible since
  the family is assumed to be fine at every point of `s`).
  -/
  rcases eq_empty_or_nonempty s with rfl|nonempty,
  { refine ⟨∅, empty_subset _, countable_empty, by simp only [pairwise_on_empty],
      by simp only [measure_empty, Union_false, Union_empty, diff_self]⟩ },
  haveI : inhabited α,
  { choose x hx using nonempty,
    exact ⟨x⟩ },
  -- choose around each `x` a small ball on which the measure is finite
  have : ∀ x, ∃ r, 0 < r ∧ r ≤ 1 ∧ μ (closed_ball x (20 * r)) < ∞,
  { assume x,
    obtain ⟨R, Rpos, μR⟩ : ∃ (R : ℝ) (hR : 0 < R), μ (closed_ball x R) < ∞ :=
      (μ.finite_at_nhds x).exists_mem_basis nhds_basis_closed_ball,
    refine ⟨min 1 (R/20), _, min_le_left _ _, _⟩,
    { simp only [true_and, lt_min_iff, zero_lt_one],
      linarith },
    { apply lt_of_le_of_lt (measure_mono _) μR,
      apply closed_ball_subset_closed_ball,
      calc 20 * min 1 (R / 20) ≤ 20 * (R/20) :
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
      ... = R : by ring } },
  choose r hr using this,
  -- we restrict to a subfamily `t'` of `t`, made of elements small enough to ensure that
  -- they only see a finite part of the measure.
  let t' := {a ∈ t | ∃ x, a ⊆ closed_ball x (r x)},
  -- extract a disjoint subfamily `u` of `t'` thanks to the abstract Vitali covering theorem.
  obtain ⟨u, ut', u_disj, hu⟩ : ∃ u ⊆ t', u.pairwise_on disjoint ∧
    ∀ a ∈ t', ∃ b ∈ u, set.nonempty (a ∩ b) ∧ diam a ≤ 2 * diam b,
  { have A : ∀ (a : set α), a ∈ t' → diam a ≤ 2,
    { rintros a ⟨hat, ⟨x, hax⟩⟩,
      calc diam a ≤ diam (closed_ball x (r x)) : diam_mono hax bounded_closed_ball
      ... ≤ 2 * r x : diam_closed_ball (hr x).1.le
      ... ≤ 2 * 1 : mul_le_mul_of_nonneg_left (hr x).2.1 zero_le_two
      ... = 2 : by norm_num },
    have B : ∀ (a : set α), a ∈ t' → a.nonempty :=
      λ a hat', set.nonempty.mono interior_subset (ht a hat'.1),
    exact exists_disjoint_subfamily_covering_enlargment t' diam 2 one_lt_two
      (λ a ha, diam_nonneg) 2 A B },
  have ut : u ⊆ t := λ a hau, (ut' hau).1,
  -- As the space is second countable, the family is countable since all its sets have nonempty
  -- interior.
  have u_count : countable u :=
    countable_of_nonempty_interior_of_disjoint id (λ a ha, ht a (ut ha)) u_disj,
  -- the family `u` will be the desired family
  refine ⟨u, λ a hat', (ut' hat').1, u_count, u_disj, _⟩,
  -- it suffices to show that it covers almost all `s` locally around each point `x`.
  refine null_of_locally_null _ (λ x hx, _),
  -- let `v` be the subfamily of `u` made of those sets intersecting the small ball `ball x (r x)`
  let v := {a ∈ u | (a ∩ ball x (r x)).nonempty },
  have vu : v ⊆ u := λ a ha, ha.1,
  -- they are all contained in a fixed ball of finite measure, thanks to our choice of `t'`
  obtain ⟨R, μR, hR⟩ : ∃ R, μ (closed_ball x R) < ∞ ∧
                          ∀ a ∈ u, (a ∩ ball x (r x)).nonempty → a ⊆ closed_ball x R,
  { have : ∀ a ∈ u, ∃ y, a ⊆ closed_ball y (r y) := λ a hau, (ut' hau).2,
    choose! y hy using this,
    have Idist_v : ∀ a ∈ v, dist (y a) x ≤ r (y a) + r x,
    { assume a hav,
      apply dist_le_add_of_nonempty_closed_ball_inter_closed_ball,
      exact hav.2.mono (inter_subset_inter (hy a hav.1) ball_subset_closed_ball) },
    set R0 := Sup ((λ a, r (y a)) '' v) with hR0,
    have R0_bdd : bdd_above ((λ a, r (y a)) '' v),
    { refine ⟨1, λ r' hr', _⟩,
      rcases (mem_image _ _ _).1 hr' with ⟨b, hb, rfl⟩,
      exact (hr _).2.1 },
    rcases le_total R0 (r x) with H|H,
    { refine ⟨20 * r x, (hr x).2.2, λ a au hax, _⟩,
      refine (hy a au).trans _,
      apply closed_ball_subset_closed_ball',
      have : r (y a) ≤ R0 := le_cSup R0_bdd (mem_image_of_mem _ ⟨au, hax⟩),
      linarith [(hr (y a)).1.le, (hr x).1.le, Idist_v a ⟨au, hax⟩] },
    { have R0pos : 0 < R0 := (hr x).1.trans_le H,
      have vnonempty : v.nonempty,
      { by_contra,
        rw [← ne_empty_iff_nonempty, not_not] at h,
        simp only [h, real.Sup_empty, image_empty] at hR0,
        exact lt_irrefl _ (R0pos.trans_le (le_of_eq hR0)) },
      obtain ⟨a, hav, R0a⟩ : ∃ a ∈ v, R0/2 < r (y a),
      { obtain ⟨r', r'mem, hr'⟩ : ∃ r' ∈ ((λ a, r (y a)) '' v), R0 / 2 < r' :=
          exists_lt_of_lt_cSup (nonempty_image_iff.2 vnonempty) (half_lt_self R0pos),
        rcases (mem_image _ _ _).1 r'mem with ⟨a, hav, rfl⟩,
        exact ⟨a, hav, hr'⟩ },
      refine ⟨8 * R0, _, _⟩,
      { apply lt_of_le_of_lt (measure_mono _) (hr (y a)).2.2,
        apply closed_ball_subset_closed_ball',
        rw dist_comm,
        linarith [Idist_v a hav] },
      { assume b bu hbx,
        refine (hy b bu).trans _,
        apply closed_ball_subset_closed_ball',
        have : r (y b) ≤ R0 := le_cSup R0_bdd (mem_image_of_mem _ ⟨bu, hbx⟩),
        linarith [Idist_v b ⟨bu, hbx⟩] } } },
  -- we will show that, in `ball x (r x)`, almost all `s` is covered by the family `u`.
  refine ⟨ball x (r x), _, le_antisymm (le_of_forall_le_of_dense (λ ε εpos, _)) bot_le⟩,
  { apply mem_nhds_within_of_mem_nhds (is_open_ball.mem_nhds _),
    simp only [(hr x).left, mem_ball, dist_self] },
  -- the elements of `v` are disjoint and all contained in a finite volume ball, hence the sum
  -- of their measures is finite.
  have I : ∑' (a : v), μ a < ∞,
  { calc ∑' (a : v), μ a = μ (⋃ (a ∈ v), a) : begin
      rw measure_bUnion (u_count.mono vu) _ (λ a ha, (h't _ (vu.trans ut ha)).measurable_set),
      exact u_disj.mono vu
    end
    ... ≤ μ (closed_ball x R) : measure_mono (bUnion_subset (λ a ha, hR a (vu ha) ha.2))
    ... < ∞ : μR },
  -- we can obtain a finite subfamily of `v`, such that the measures of the remaining elements
  -- add up to an arbitrarily small number, say `ε / C`.
  obtain ⟨w, hw⟩ : ∃ (w : finset ↥v), ∑' (a : {a // a ∉ w}), μ a < ε / C,
  { haveI : ne_bot (at_top : filter (finset v)) := at_top_ne_bot,
    have : 0 < ε / C, by simp only [ennreal.div_pos_iff, εpos.ne', ennreal.coe_ne_top, ne.def,
                                    not_false_iff, and_self],
    exact ((tendsto_order.1 (ennreal.tendsto_tsum_compl_at_top_zero I.ne)).2 _ this).exists },
  choose! y hy using h,
  -- main property: the points `z` of `s` which are not covered by `u` are contained in the
  -- enlargements of the elements not in `w`.
  have M : (s \ ⋃ (a : set α) (H : a ∈ u), a) ∩ ball x (r x)
    ⊆ ⋃ (a : {a // a ∉ w}), closed_ball (y a) (3 * diam (a : set α)),
  { assume z hz,
    set k := ⋃ (a : v) (ha : a ∈ w), (a : set α) with hk,
    have k_closed : is_closed k :=
      is_closed_bUnion w.finite_to_set (λ i hi, h't _ (ut (vu i.2))),
    have z_notmem_k : z ∉ k,
    { simp only [not_exists, exists_prop, mem_Union, mem_sep_eq, forall_exists_index,
        set_coe.exists, not_and, exists_and_distrib_right, subtype.coe_mk],
      assume b hbv h'b h'z,
      have : z ∈ (s \ ⋃ (a : set α) (H : a ∈ u), a) ∩ (⋃ (a : set α) (H : a ∈ u), a) :=
        mem_inter (mem_of_mem_inter_left hz) (mem_bUnion (vu hbv) h'z),
      simpa only [diff_inter_self] },
    -- since the elements of `w` are closed and finitely many, one can find a small ball around `z`
    -- not intersecting them
    have : ball x (r x) \ k ∈ 𝓝 z,
    { apply is_open.mem_nhds (is_open_ball.sdiff k_closed) _,
      exact (mem_diff _).2 ⟨mem_of_mem_inter_right hz, z_notmem_k⟩ },
    obtain ⟨d, dpos, hd⟩ : ∃ (d : ℝ) (dpos : 0 < d), closed_ball z d ⊆ ball x (r x) \ k :=
      nhds_basis_closed_ball.mem_iff.1 this,
    -- choose an element `a` of the family `t` contained in this small ball
    obtain ⟨a, hat, za, ad⟩ : ∃ a ∈ t, z ∈ a ∧ a ⊆ closed_ball z d :=
      hf z ((mem_diff _).1 (mem_of_mem_inter_left hz)).1 d dpos,
    have ax : a ⊆ ball x (r x) := ad.trans (hd.trans (diff_subset (ball x (r x)) k)),
    -- it intersects an element `b` of `u` with comparable diameter, by definition of `u`
    obtain ⟨b, bu, ab, bdiam⟩ : ∃ (b : set α) (H : b ∈ u), (a ∩ b).nonempty ∧ diam a ≤ 2 * diam b :=
      hu a ⟨hat, ⟨x, ax.trans ball_subset_closed_ball⟩⟩,
    have bv : b ∈ v,
    { refine ⟨bu, ab.mono _⟩,
      rw inter_comm,
      exact inter_subset_inter_right _ ax },
    let b' : v := ⟨b, bv⟩,
    -- `b` can not belong to `w`, as the elements of `w` do not intersect `closed_ball z d`,
    -- contrary to `b`
    have b'_notmem_w : b' ∉ w,
    { assume b'w,
      have b'k : (b' : set α) ⊆ k := finset.subset_set_bUnion_of_mem b'w,
      have : ((ball x (r x) \ k) ∩ k).nonempty := ab.mono (inter_subset_inter (ad.trans hd) b'k),
      simpa only [diff_inter_self, not_nonempty_empty] },
    let b'' : {a // a ∉ w} := ⟨b', b'_notmem_w⟩,
    -- since `a` and `b` have comparable diameters, it follows that `z` belongs to the
    -- enlargement of `b`
    have zb : z ∈ closed_ball (y b) (3 * diam b),
    { rcases ab with ⟨e, ⟨ea, eb⟩⟩,
      have A : dist z e ≤ diam a := dist_le_diam_of_mem (bounded_closed_ball.mono ad) za ea,
      have B : dist e (y b) ≤ diam b,
      { rcases (ut' bu).2 with ⟨c, hc⟩,
        apply dist_le_diam_of_mem (bounded_closed_ball.mono hc) eb (hy b (ut bu)).1 },
      simp only [mem_closed_ball],
      linarith [dist_triangle z e (y b)] },
    suffices H : closed_ball (y (b'' : set α)) (3 * diam (b'' : set α))
      ⊆ ⋃ (a : {a // a ∉ w}), closed_ball (y (a : set α)) (3 * diam (a : set α)), from H zb,
    exact subset_Union (λ (a : {a // a ∉ w}), closed_ball (y a) (3 * diam (a : set α))) b'' },
  -- now that we have proved our main inclusion, we can use it to estimate the measure of the points
  -- in `ball x (r x)` not covered by `u`.
  haveI : encodable v := (u_count.mono vu).to_encodable,
  calc μ ((s \ ⋃ (a : set α) (H : a ∈ u), a) ∩ ball x (r x))
      ≤ μ (⋃ (a : {a // a ∉ w}), closed_ball (y a) (3 * diam (a : set α))) : measure_mono M
  ... ≤ ∑' (a : {a // a ∉ w}), μ (closed_ball (y a) (3 * diam (a : set α))) : measure_Union_le _
  ... ≤ ∑' (a : {a // a ∉ w}), C * μ a : ennreal.tsum_le_tsum (λ a, (hy a (ut (vu a.1.2))).2)
  ... = C * ∑' (a : {a // a ∉ w}), μ a : ennreal.tsum_mul_left
  ... ≤ C * (ε / C) : ennreal.mul_le_mul le_rfl hw.le
  ... ≤ ε : ennreal.mul_div_le,
end

/-- Assume that around every point there are arbitrarily small scales at which the measure is
doubling. Then the set of closed sets `a` with nonempty interior covering a fixed proportion `1/C`
of the ball `closed_ball x (3 * diam a)` forms a Vitali family. This is essentially a restatement
of the measurable Vitali theorem. -/
protected def vitali_family [metric_space α] [measurable_space α] [opens_measurable_space α]
  [second_countable_topology α] (μ : measure α) [is_locally_finite_measure μ] (C : ℝ≥0)
  (h : ∀ x (ε > 0), ∃ r ∈ Ioc (0 : ℝ) ε, μ (closed_ball x (6 * r)) ≤ C * μ (closed_ball x r)) :
  vitali_family μ :=
{ sets_at := λ x, {a | x ∈ a ∧ is_closed a ∧ (interior a).nonempty ∧
                      μ (closed_ball x (3 * diam a)) ≤ C * μ a},
  measurable_set' := λ x a ha, ha.2.1.measurable_set,
  nonempty_interior := λ x a ha, ha.2.2.1,
  nontrivial := λ x ε εpos, begin
    obtain ⟨r, ⟨rpos, rε⟩, μr⟩ : ∃ r ∈ Ioc (0 : ℝ) ε,
      μ (closed_ball x (6 * r)) ≤ C * μ (closed_ball x r) := h x ε εpos,
    refine ⟨closed_ball x r, ⟨_, is_closed_ball, _, _⟩, closed_ball_subset_closed_ball rε⟩,
    { simp only [rpos.le, mem_closed_ball, dist_self] },
    { exact (nonempty_ball.2 rpos).mono (ball_subset_interior_closed_ball) },
    { apply le_trans (measure_mono (closed_ball_subset_closed_ball _)) μr,
      have : diam (closed_ball x r) ≤ 2 * r := diam_closed_ball rpos.le,
      linarith }
  end,
  covering := begin
    assume s f fsubset ffine,
    rcases eq_empty_or_nonempty s with rfl|H,
    { refine ⟨∅, λ _, ∅, by simp, by simp⟩ },
    haveI : inhabited α, { choose x hx using H, exact ⟨x⟩ },
    let t := ⋃ (x ∈ s), f x,
    have A₁ : ∀ x ∈ s, ∀ (ε : ℝ), 0 < ε → (∃ a ∈ t, x ∈ a ∧ a ⊆ closed_ball x ε),
    { assume x xs ε εpos,
      rcases ffine x xs ε εpos with ⟨a, xa, hax⟩,
      exact ⟨a, mem_bUnion xs xa, (fsubset x xs xa).1, hax⟩ },
    have A₂ : ∀ a ∈ t, (interior a).nonempty,
    { rintros a ha,
      rcases mem_bUnion_iff.1 ha with ⟨x, xs, xa⟩,
      exact (fsubset x xs xa).2.2.1 },
    have A₃ : ∀ a ∈ t, is_closed a,
    { rintros a ha,
      rcases mem_bUnion_iff.1 ha with ⟨x, xs, xa⟩,
      exact (fsubset x xs xa).2.1 },
    have A₄ : ∀ a ∈ t, ∃ x ∈ a, μ (closed_ball x (3 * diam a)) ≤ C * μ a,
    { rintros a ha,
      rcases mem_bUnion_iff.1 ha with ⟨x, xs, xa⟩,
      exact ⟨x, (fsubset x xs xa).1, (fsubset x xs xa).2.2.2⟩ },
    obtain ⟨u, ut, u_count, u_disj, μu⟩ :
      ∃ u ⊆ t, u.countable ∧ u.pairwise_on (disjoint on id) ∧ μ (s \ ⋃ a ∈ u, a) = 0 :=
        exists_disjoint_covering_ae μ s t A₁ A₂ A₃ C A₄,
    have : ∀ a ∈ u, ∃ x ∈ s, a ∈ f x := λ a ha, mem_bUnion_iff.1 (ut ha),
    choose! x hx using this,
    have inj_on_x : inj_on x u,
    { assume a ha b hb hab,
      have A : (a ∩ b).nonempty,
      { refine ⟨x a, mem_inter ((fsubset _ (hx a ha).1 (hx a ha).2).1) _⟩,
        rw hab,
        exact (fsubset _ (hx b hb).1 (hx b hb).2).1 },
      contrapose A,
      have : disjoint a b := u_disj a ha b hb A,
      simpa only [← not_disjoint_iff_nonempty_inter] },
    refine ⟨x '' u, function.inv_fun_on x u, _, _, _, _⟩,
    { assume y hy,
      rcases (mem_image _ _ _).1 hy with ⟨a, au, rfl⟩,
      exact (hx a au).1 },
    { rw [inj_on_x.pairwise_on_image],
      assume a ha b hb hab,
      simp only [function.on_fun, function.inv_fun_on_eq' inj_on_x, ha, hb],
      exact u_disj a ha b hb hab },
    { assume y hy,
      rcases (mem_image _ _ _).1 hy with ⟨a, ha, rfl⟩,
      rw function.inv_fun_on_eq' inj_on_x ha,
      exact (hx a ha).2 },
    { rw [bUnion_image],
      convert μu using 3,
      exact bUnion_congr (λ a ha, function.inv_fun_on_eq' inj_on_x ha) }
  end }

end vitali

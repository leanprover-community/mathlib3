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

We prove this theorem in `vitali_covering_closed_ball`. It is deduced from a more general version,
called `vitali_covering`, which applies to any family of sets together with a size function `δ`
(think "radius" or "diameter").
-/

variables {α : Type*}

open set metric measure_theory
open_locale nnreal classical

/-- Vitali covering theorem: given a set `t` of subsets of a type, one may extract a disjoint
subfamily `u` such that the `τ`-enlargment of this family covers all elements of `t`, where `τ > 1`
is any fixed number.

When `t` is a family of balls, the `τ`-enlargment of `ball x r` is `ball x ((1+2τ) r)`. In general,
it is expressed in terms of a function `δ` (think "radius" or "diameter"), positive and bounded on
all elements of `t`. The condition is that every element `a` of `t` should intersect an
element `b` of `u` of size larger than that of `a` up to `τ`, i.e., `δ b ≥ δ a / τ`. -/
theorem vitali_covering
  (t : set (set α)) (δ : set α → ℝ) (τ : ℝ) (hτ : 1 < τ) (δpos : ∀ a ∈ t, 0 < δ a)
  (R : ℝ) (δle : ∀ a ∈ t, δ a ≤ R) (hne : ∀ a ∈ t, set.nonempty a) :
  ∃ u ⊆ t, u.pairwise_on (disjoint on id) ∧
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
        ... ≤ τ * δ b : mul_le_mul_of_nonneg_left ha'.le (zero_le_one.trans hτ.le) },
      { rw ← not_disjoint_iff_nonempty_inter at hcb,
        exact (hcb (H _ H')).elim } } }
end

/-- Vitali covering theorem, closed balls version: given a family `t` of closed balls, one can
extract a disjoint subfamily `u ⊆ t` so that all balls in `t` are covered by the 5-times
dilations of balls in `u`. -/
theorem vitali_covering_closed_ball [metric_space α]
  (t : set (set α)) (R : ℝ) (ht : ∀ s ∈ t, ∃ x r, s = closed_ball x r ∧ r ≤ R) :
  ∃ u ⊆ t, u.pairwise_on (disjoint on id) ∧
    ∀ a ∈ t, ∃ x r, closed_ball x r ∈ u ∧ a ⊆ closed_ball x (5 * r) :=
begin
  /- For the proof, one wishes to apply the abstract version of the Vitali covering theorem to the
  function `δ (closed_ball x r) = r`. This would work directly if all radii were positive. It turns
  out that the theorem is still true without this positivity assumption, but slightly more painful
  to write: one applies the abstract Vitali theorem to the subfamily `t'` of `t` made of balls of
  positive radius, to get a disjoint subfamily `u'`, and then one adds back the balls of
  radius `0` that are not covered by `⋃₀ u'` (they are automatically pairwise disjoint, and still
  satisfy the statement). -/
  -- Exclude the trivial case where `t` is empty (to be able to use `choose!` later).
  rcases eq_empty_or_nonempty t with rfl|tnonempty,
  { refine ⟨∅, subset.refl _, by simp⟩ },
  haveI : inhabited α,
  { choose s hst using tnonempty,
    choose x r hxr using ht s hst,
    exact ⟨x⟩ },
  -- Exclude the trivial case where `t` is reduced to the empty set.
  by_cases t_eq_empty : t = {∅},
  { rw t_eq_empty,
    refine ⟨{∅}, subset.refl _, _⟩,
    simp only [true_and, closed_ball_eq_empty, mem_singleton_iff, and_true, empty_subset, forall_eq,
      pairwise_on_singleton, exists_const],
    exact ⟨-1, by simp only [right.neg_neg_iff, zero_lt_one]⟩ },
  -- The real proof starts now. Since the center or the radius of a ball is not uniquely defined
  -- in a general metric space, we just choose one for definiteness.
  choose! x r hxr using ht,
  -- `t'` is the subfamily of balls in `t` with positive radius, to which we will apply
  -- the abstract Vitali theorem to get a nice subfamily `u'`..
  let t' := {s' | s' ∈ t ∧ 0 < r s'},
  obtain ⟨u', u't', u'_disj, hu'⟩ :
    (∃ (u' : set (set α)) (H : u' ⊆ t'), u'.pairwise_on (disjoint on id) ∧
      ∀ (a : set α), a ∈ t' → (∃ (b : set α) (H : b ∈ u'), (a ∩ b).nonempty ∧ r a ≤ 2 * r b)),
  { apply vitali_covering t' r 2 one_lt_two (λ s' hs't', hs't'.2) R
      (λ s' hs't', (hxr s' hs't'.1).2),
    assume s' hs't',
    rw (hxr s' hs't'.1).1,
    simp only [hs't'.2.le, nonempty_closed_ball] },
  -- Put in `u''` all the radius 0 elements of `t` that are not covered by `u'`.
  let u'' := {s | s ∈ t ∧ r s = 0 ∧ s ∩ (⋃₀ u') = ∅},
  -- Show that `u'` or `u''` is nonempty (otherwise, `t` would be reduced to the empty set, a case
  -- we have already excluded).
  have u'u''_nonempty : (u' ∪ u'').nonempty,
  { simp only [union_nonempty],
    by_contra,
    simp only [not_or_distrib, not_nonempty_iff_eq_empty] at h,
    have : ∃ a ∈ t, a ≠ ∅,
    { contrapose! t_eq_empty,
      apply subset.antisymm,
      { simpa only using t_eq_empty },
      { rcases tnonempty with ⟨a, hat⟩,
        have := t_eq_empty a hat,
        simpa only [this, singleton_subset_iff] using hat } },
    rcases this with ⟨a, hat, a_nonempty⟩,
    rcases lt_trichotomy (r a) 0 with ra|ra|ra,
    { rw [(hxr a hat).1, closed_ball_eq_empty.2 ra] at a_nonempty,
      exact a_nonempty rfl },
    { have : a ∈ u'', by simp only [hat, ra, h.left, inter_empty, sUnion_empty, mem_set_of_eq,
        eq_self_iff_true, and_self],
      rwa h.2 at this },
    { rcases hu' a ⟨hat, ra⟩ with ⟨b, bu', hb⟩,
      rwa h.1 at bu' } },
  have A : ∀ s ∈ t, r s = 0 → s = {x s},
  { assume s hst hrs,
    conv_lhs { rw [(hxr s hst).1, hrs, closed_ball_zero] } },
  have u'u''t : u' ∪ u'' ⊆ t := union_subset (λ s hs, (u't' hs).1) (λ s hs, hs.1),
  -- we will now check that `u' ∪ u''` is the desired disjoint family
  refine ⟨u' ∪ u'', u'u''t, _, _⟩,
  { -- check that `u' ∪ u''` is disjoint.
    simp only [pairwise_on_union, u'_disj, true_and, and_imp, mem_set_of_eq, ne.def],
    simp only [function.on_fun, disjoint.comm, id.def, and_self],
    split,
    { assume s hs s' hs' hss',
      rw [A s hs.1 hs.2.1, A s' hs'.1 hs'.2.1] at ⊢ hss',
      simpa only [ne.def, singleton_eq_singleton_iff, disjoint_singleton_right] using hss'.symm },
    { assume s' s'u' a hat ra hinter hne,
      rw A a hat ra at hinter ⊢,
      simp only [not_exists, exists_prop, not_and, mem_set_of_eq, singleton_inter_eq_empty]
        at hinter,
      simpa only [disjoint_singleton_right] using hinter _ s'u' } },
  { -- check that any ball of radius `r` in `t` is contained in the 5-dilation of a ball
    -- in `u' ∪ u''`. This depends on the value of `r`.
    assume s hst,
    rcases lt_trichotomy (r s) 0 with rneg|rzero|rpos,
    -- if `r` is negative (i.e., we are dealing with the empty set), use the fact that `u' ∪ u''`
    -- is nonempty.
    { have : s = ∅, by { rw (hxr s hst).1, simp only [rneg, closed_ball_eq_empty] },
      simp only [this, empty_subset, and_true],
      rcases u'u''_nonempty with ⟨a, ha⟩,
      have := hxr a (u'u''t ha),
      rw this.1 at ha,
      exact ⟨_, _, ha⟩ },
    -- if `r` is zero (i.e., we are dealing with a singleton), either it is contained in no element
    -- of `u'`, and then it is in `u''` and we can use it directly. Or it is contained in an element
    -- of `u'`, and then we can use this element (no enlargement would be necessary).
    { rcases eq_empty_or_nonempty (s ∩ ⋃₀ u') with H|H,
      { refine ⟨x s, 0, _, _⟩,
        { apply mem_union_right,
          have : s ∈ u'' := ⟨hst, rzero, H⟩,
          rwa [A s hst rzero, ← closed_ball_zero] at this },
        { conv_lhs { rw [A s hst rzero, ← closed_ball_zero] },
          simp only [imp_self, forall_const, mem_singleton_iff, mul_zero] } },
      { obtain ⟨a, au', xsa⟩ : ∃ (a : set α), a ∈ u' ∧ x s ∈ a,
        { rw [A s hst rzero] at H,
          simpa only [exists_prop, mem_set_of_eq, singleton_inter_nonempty] using H },
        refine ⟨x a, r a, _, _⟩,
        { apply mem_union_left,
          convert au',
          exact (hxr a (u't' au').1).1.symm },
        { rw [A s hst rzero, singleton_subset_iff],
          rw (hxr a (u't' au').1).1 at xsa,
          apply (closed_ball_subset_closed_ball _) xsa,
          linarith [(u't' au').2] } } },
    -- finally, if `r` is positive, we are considering an element `s` in `t'`. By definition
    -- of `u'`, the set `s` interects an element `a` of `u'` with comparable radius. Then the fact
    -- that `s` is contained in the 5-dilation of `a` is straightforward.
    { have st' : s ∈ t' := ⟨hst, rpos⟩,
      obtain ⟨a, au', sa, rsa⟩ : (∃ (a : set α) (H : a ∈ u'), (s ∩ a).nonempty ∧ r s ≤ 2 * r a) :=
        hu' s st',
      refine ⟨x a, r a, _, _⟩,
      { apply mem_union_left,
        convert au',
        exact (hxr a (u't' au').1).1.symm },
      { rw (hxr s st'.1).1 at sa ⊢,
        rw (hxr a (u't' au').1).1 at sa,
        have : dist (x s) (x a) ≤ r s + r a :=
          dist_le_add_of_nonempty_closed_ball_inter_closed_ball sa,
        apply closed_ball_subset_closed_ball',
        linarith } } }
end

#exit


theorem measurable_vitali [metric_space α] [measurable_space α] [opens_measurable_space α]
  (μ : measure α) [is_locally_finite_measure μ] (s : set α)
  (t : set (set α)) (hf : ∀ x ∈ s, ∀ (ε > (0 : ℝ)), ∃ a ∈ t, x ∈ a ∧ diam a < ε)
  (ht : ∀ a ∈ t, (interior a).nonempty) (h't : ∀ a ∈ t, is_closed a)
  (C : ℝ≥0) (h : ∀ a ∈ t, ∀ x ∈ a, μ (closed_ball x (5 * diam a)) ≤ C * μ a) :
  ∃ u ⊆ t, countable u ∧ u.pairwise_on (disjoint on id) ∧ μ (s \ ⋃ (a ∈ u), a) = 0 :=
sorry

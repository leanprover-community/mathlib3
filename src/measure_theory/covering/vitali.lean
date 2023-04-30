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

variables {α ι : Type*}

open set metric measure_theory topological_space filter
open_locale nnreal classical ennreal topology

namespace vitali

/-- Vitali covering theorem: given a set `t` of subsets of a type, one may extract a disjoint
subfamily `u` such that the `τ`-enlargment of this family covers all elements of `t`, where `τ > 1`
is any fixed number.

When `t` is a family of balls, the `τ`-enlargment of `ball x r` is `ball x ((1+2τ) r)`. In general,
it is expressed in terms of a function `δ` (think "radius" or "diameter"), positive and bounded on
all elements of `t`. The condition is that every element `a` of `t` should intersect an
element `b` of `u` of size larger than that of `a` up to `τ`, i.e., `δ b ≥ δ a / τ`.

We state the lemma slightly more generally, with an indexed family of sets `B a` for `a ∈ t`, for
wider applicability.
-/
theorem exists_disjoint_subfamily_covering_enlargment
  (B : ι → set α) (t : set ι) (δ : ι → ℝ) (τ : ℝ) (hτ : 1 < τ) (δnonneg : ∀ a ∈ t, 0 ≤ δ a)
  (R : ℝ) (δle : ∀ a ∈ t, δ a ≤ R) (hne : ∀ a ∈ t, (B a).nonempty) :
  ∃ u ⊆ t, u.pairwise_disjoint B ∧
    ∀ a ∈ t, ∃ b ∈ u, (B a ∩ B b).nonempty ∧ δ a ≤ τ * δ b :=
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
  let T : set (set ι) := {u | u ⊆ t ∧ u.pairwise_disjoint B
    ∧ ∀ a ∈ t, ∀ b ∈ u, (B a ∩ B b).nonempty → ∃ c ∈ u, (B a ∩ B c).nonempty ∧ δ a ≤ τ * δ c},
  -- By Zorn, choose a maximal family in the good set `T` of disjoint families.
  obtain ⟨u, uT, hu⟩ : ∃ u ∈ T, ∀ v ∈ T, u ⊆ v → v = u,
  { refine zorn_subset _ (λ U UT hU, _),
    refine ⟨⋃₀ U, _, λ s hs, subset_sUnion_of_mem hs⟩,
    simp only [set.sUnion_subset_iff, and_imp, exists_prop, forall_exists_index, mem_sUnion,
                set.mem_set_of_eq],
    refine ⟨λ u hu, (UT hu).1, (pairwise_disjoint_sUnion hU.directed_on).2 (λ u hu, (UT hu).2.1),
      λ a hat b u uU hbu hab, _⟩,
    obtain ⟨c, cu, ac, hc⟩ : ∃ (c : ι) (H : c ∈ u), (B a ∩ B c).nonempty ∧ δ a ≤ τ * δ c :=
      (UT uU).2.2 a hat b hbu hab,
    exact ⟨c, ⟨u, uU, cu⟩, ac, hc⟩ },
  -- the only nontrivial bit is to check that every `a ∈ t` intersects an element `b ∈ u` with
  -- comparatively large `δ b`. Assume this is not the case, then we will contradict the maximality.
  refine ⟨u, uT.1, uT.2.1, λ a hat, _⟩,
  contrapose! hu,
  have a_disj : ∀ c ∈ u, disjoint (B a) (B c),
  { assume c hc,
    by_contra,
    rw not_disjoint_iff_nonempty_inter at h,
    obtain ⟨d, du, ad, hd⟩ : ∃ (d : ι) (H : d ∈ u), (B a ∩ B d).nonempty ∧ δ a ≤ τ * δ d :=
      uT.2.2 a hat c hc h,
    exact lt_irrefl _ ((hu d du ad).trans_le hd) },
  -- Let `A` be all the elements of `t` which do not intersect the family `u`. It is nonempty as it
  -- contains `a`. We will pick an element `a'` of `A` with `δ a'` almost as large as possible.
  let A := {a' | a' ∈ t ∧ ∀ c ∈ u, disjoint (B a') (B c)},
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
  { exact uT.2.1.insert (λ b bu ba', a'A.2 b bu) },
  -- check that every element `c` of `t` intersecting `u ∪ {a'}` intersects an element of this
  -- family with large `δ`.
  { assume c ct b ba'u hcb,
    -- if `c` already intersects an element of `u`, then it intersects an element of `u` with
    -- large `δ` by the assumption on `u`, and there is nothing left to do.
    by_cases H : ∃ d ∈ u, (B c ∩ B d).nonempty,
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
  (t : set ι) (x : ι → α) (r : ι → ℝ) (R : ℝ) (hr : ∀ a ∈ t, r a ≤ R) :
  ∃ u ⊆ t, u.pairwise_disjoint (λ a, closed_ball (x a) (r a)) ∧
    ∀ a ∈ t, ∃ b ∈ u, closed_ball (x a) (r a) ⊆ closed_ball (x b) (5 * r b) :=
begin
  rcases eq_empty_or_nonempty t with rfl|tnonempty,
  { exact ⟨∅, subset.refl _, pairwise_disjoint_empty, by simp⟩ },
  by_cases ht : ∀ a ∈ t, r a < 0,
  { exact ⟨t, subset.rfl, λ a ha b hb hab,
      by simp only [function.on_fun, closed_ball_eq_empty.2 (ht a ha), empty_disjoint],
      λ a ha, ⟨a, ha, by simp only [closed_ball_eq_empty.2 (ht a ha), empty_subset]⟩⟩ },
  push_neg at ht,
  let t' := {a ∈ t | 0 ≤ r a},
  rcases exists_disjoint_subfamily_covering_enlargment (λ a, closed_ball (x a) (r a)) t' r
    2 one_lt_two (λ a ha, ha.2) R (λ a ha, hr a ha.1) (λ a ha, ⟨x a, mem_closed_ball_self ha.2⟩)
    with ⟨u, ut', u_disj, hu⟩,
  have A : ∀ a ∈ t', ∃ b ∈ u, closed_ball (x a) (r a) ⊆ closed_ball (x b) (5 * r b),
  { assume a ha,
    rcases hu a ha with ⟨b, bu, hb, rb⟩,
    refine ⟨b, bu, _⟩,
    have : dist (x a) (x b) ≤ r a + r b :=
      dist_le_add_of_nonempty_closed_ball_inter_closed_ball hb,
    apply closed_ball_subset_closed_ball',
    linarith },
  refine ⟨u, ut'.trans (λ a ha, ha.1), u_disj, λ a ha, _⟩,
  rcases le_or_lt 0 (r a) with h'a|h'a,
  { exact A a ⟨ha, h'a⟩ },
  { rcases ht with ⟨b, rb⟩,
    rcases A b ⟨rb.1, rb.2⟩ with ⟨c, cu, hc⟩,
    refine ⟨c, cu, by simp only [closed_ball_eq_empty.2 h'a, empty_subset]⟩ },
end


/-- The measurable Vitali covering theorem. Assume one is given a family `t` of closed sets with
nonempty interior, such that each `a ∈ t` is included in a ball `B (x, r)` and covers a definite
proportion of the ball `B (x, 3 r)` for a given measure `μ` (think of the situation where `μ` is
a doubling measure and `t` is a family of balls). Consider a (possibly non-measurable) set `s`
at which the family is fine, i.e., every point of `s` belongs to arbitrarily small elements of `t`.
Then one can extract from `t` a disjoint subfamily that covers almost all `s`.

For more flexibility, we give a statement with a parameterized family of sets.
-/
theorem exists_disjoint_covering_ae [metric_space α] [measurable_space α] [opens_measurable_space α]
  [second_countable_topology α]
  (μ : measure α) [is_locally_finite_measure μ] (s : set α)
  (t : set ι) (C : ℝ≥0) (r : ι → ℝ) (c : ι → α) (B : ι → set α)
  (hB : ∀ a ∈ t, B a ⊆ closed_ball (c a) (r a))
  (μB : ∀ a ∈ t, μ (closed_ball (c a) (3 * r a)) ≤ C * μ (B a))
  (ht : ∀ a ∈ t, (interior (B a)).nonempty) (h't : ∀ a ∈ t, is_closed (B a))
  (hf : ∀ x ∈ s, ∀ (ε > (0 : ℝ)), ∃ a ∈ t, r a ≤ ε ∧ c a = x) :
  ∃ u ⊆ t, u.countable ∧ u.pairwise_disjoint B ∧ μ (s \ ⋃ a ∈ u, B a) = 0 :=
begin
  /- The idea of the proof is the following. Assume for simplicity that `μ` is finite. Applying the
  abstract Vitali covering theorem with `δ = r` given by `hf`, one obtains a disjoint subfamily `u`,
  such that any element of `t` intersects an element of `u` with comparable radius. Fix `ε > 0`.
  Since the elements of `u` have summable measure, one can remove finitely elements `w_1, ..., w_n`.
  so that the measure of the remaining elements is `< ε`. Consider now a point `z` not
  in the `w_i`. There is a small ball around `z` not intersecting the `w_i` (as they are closed),
  an element `a ∈ t` contained in this small ball (as the family `t` is fine at `z`) and an element
  `b ∈ u` intersecting `a`, with comparable radius (by definition of `u`). Then `z` belongs to the
  enlargement of `b`. This shows that `s \ (w_1 ∪ ... ∪ w_n)` is contained in
  `⋃ (b ∈ u \ {w_1, ... w_n}) (enlargement of b)`. The measure of the latter set is bounded by
  `∑ (b ∈ u \ {w_1, ... w_n}) C * μ b` (by the doubling property of the measure), which is at most
  `C ε`. Letting `ε` tend to `0` shows that `s` is almost everywhere covered by the family `u`.

  For the real argument, the measure is only locally finite. Therefore, we implement the same
  strategy, but locally restricted to balls on which the measure is finite. For this, we do not
  use the whole family `t`, but a subfamily `t'` supported on small balls (which is possible since
  the family is assumed to be fine at every point of `s`).
  -/
  -- choose around each `x` a small ball on which the measure is finite
  have : ∀ x, ∃ R, 0 < R ∧ R ≤ 1 ∧ μ (closed_ball x (20 * R)) < ∞,
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
  choose R hR0 hR1 hRμ,
  -- we restrict to a subfamily `t'` of `t`, made of elements small enough to ensure that
  -- they only see a finite part of the measure, and with a doubling property
  let t' := {a ∈ t | r a ≤ R (c a)},
  -- extract a disjoint subfamily `u` of `t'` thanks to the abstract Vitali covering theorem.
  obtain ⟨u, ut', u_disj, hu⟩ : ∃ u ⊆ t', u.pairwise_disjoint B ∧
    ∀ a ∈ t', ∃ b ∈ u, (B a ∩ B b).nonempty ∧ r a ≤ 2 * r b,
  { have A : ∀ a ∈ t', r a ≤ 1,
    { assume a ha,
      apply ha.2.trans (hR1 (c a)), },
    have A' : ∀ a ∈ t', (B a).nonempty :=
      λ a hat', set.nonempty.mono interior_subset (ht a hat'.1),
    refine exists_disjoint_subfamily_covering_enlargment B t' r 2 one_lt_two
      (λ a ha, _) 1 A A',
    exact nonempty_closed_ball.1 ((A' a ha).mono (hB a ha.1)) },
  have ut : u ⊆ t := λ a hau, (ut' hau).1,
  -- As the space is second countable, the family is countable since all its sets have nonempty
  -- interior.
  have u_count : u.countable := u_disj.countable_of_nonempty_interior (λ a ha, ht a (ut ha)),
  -- the family `u` will be the desired family
  refine ⟨u, λ a hat', (ut' hat').1, u_count, u_disj, _⟩,
  -- it suffices to show that it covers almost all `s` locally around each point `x`.
  refine null_of_locally_null _ (λ x hx, _),
  -- let `v` be the subfamily of `u` made of those sets intersecting the small ball `ball x (r x)`
  let v := {a ∈ u | (B a ∩ ball x (R x)).nonempty },
  have vu : v ⊆ u := λ a ha, ha.1,
  -- they are all contained in a fixed ball of finite measure, thanks to our choice of `t'`
  obtain ⟨K, μK, hK⟩ : ∃ K, μ (closed_ball x K) < ∞ ∧
                          ∀ a ∈ u, (B a ∩ ball x (R x)).nonempty → B a ⊆ closed_ball x K,
  { have Idist_v : ∀ a ∈ v, dist (c a) x ≤ r a + R x,
    { assume a hav,
      apply dist_le_add_of_nonempty_closed_ball_inter_closed_ball,
      refine hav.2.mono _,
      apply inter_subset_inter _ ball_subset_closed_ball,
      exact hB a (ut (vu hav)) },
    set R0 := Sup (r '' v) with R0_def,
    have R0_bdd : bdd_above (r '' v),
    { refine ⟨1, λ r' hr', _⟩,
      rcases (mem_image _ _ _).1 hr' with ⟨b, hb, rfl⟩,
      exact le_trans (ut' (vu hb)).2 (hR1 (c b)) },
    rcases le_total R0 (R x) with H|H,
    { refine ⟨20 * R x, hRμ x, λ a au hax, _⟩,
      refine (hB a (ut au)).trans _,
      apply closed_ball_subset_closed_ball',
      have : r a ≤ R0 := le_cSup R0_bdd (mem_image_of_mem _ ⟨au, hax⟩),
      linarith [Idist_v a ⟨au, hax⟩, hR0 x] },
    { have R0pos : 0 < R0 := (hR0 x).trans_le H,
      have vnonempty : v.nonempty,
      { by_contra,
        rw [nonempty_iff_ne_empty, not_not] at h,
        simp only [h, real.Sup_empty, image_empty] at R0_def,
        exact lt_irrefl _ (R0pos.trans_le (le_of_eq R0_def)) },
      obtain ⟨a, hav, R0a⟩ : ∃ a ∈ v, R0/2 < r a,
      { obtain ⟨r', r'mem, hr'⟩ : ∃ r' ∈ r '' v, R0 / 2 < r' :=
          exists_lt_of_lt_cSup (nonempty_image_iff.2 vnonempty) (half_lt_self R0pos),
        rcases (mem_image _ _ _).1 r'mem with ⟨a, hav, rfl⟩,
        exact ⟨a, hav, hr'⟩ },
      refine ⟨8 * R0, _, _⟩,
      { apply lt_of_le_of_lt (measure_mono _) (hRμ (c a)),
        apply closed_ball_subset_closed_ball',
        rw dist_comm,
        linarith [Idist_v a hav, (ut' (vu hav)).2] },
      { assume b bu hbx,
        refine (hB b (ut bu)).trans _,
        apply closed_ball_subset_closed_ball',
        have : r b ≤ R0 := le_cSup R0_bdd (mem_image_of_mem _ ⟨bu, hbx⟩),
        linarith [Idist_v b ⟨bu, hbx⟩] } } },
  -- we will show that, in `ball x (R x)`, almost all `s` is covered by the family `u`.
  refine ⟨_ ∩ ball x (R x), inter_mem_nhds_within _ (ball_mem_nhds _ (hR0 _)),
    nonpos_iff_eq_zero.mp (le_of_forall_le_of_dense (λ ε εpos, _))⟩,
  -- the elements of `v` are disjoint and all contained in a finite volume ball, hence the sum
  -- of their measures is finite.
  have I : ∑' (a : v), μ (B a) < ∞,
  { calc ∑' (a : v), μ (B a) = μ (⋃ (a ∈ v), B a) : begin
      rw measure_bUnion (u_count.mono vu) _ (λ a ha, (h't _ (vu.trans ut ha)).measurable_set),
      exact u_disj.subset vu
    end
    ... ≤ μ (closed_ball x K) : measure_mono (Union₂_subset (λ a ha, hK a (vu ha) ha.2))
    ... < ∞ : μK },
  -- we can obtain a finite subfamily of `v`, such that the measures of the remaining elements
  -- add up to an arbitrarily small number, say `ε / C`.
  obtain ⟨w, hw⟩ : ∃ (w : finset ↥v), ∑' (a : {a // a ∉ w}), μ (B a) < ε / C,
  { have : 0 < ε / C, by simp only [ennreal.div_pos_iff, εpos.ne', ennreal.coe_ne_top, ne.def,
                                    not_false_iff, and_self],
    exact ((tendsto_order.1 (ennreal.tendsto_tsum_compl_at_top_zero I.ne)).2 _ this).exists },
  -- main property: the points `z` of `s` which are not covered by `u` are contained in the
  -- enlargements of the elements not in `w`.
  have M : (s \ ⋃ a ∈ u, B a) ∩ ball x (R x)
    ⊆ ⋃ (a : {a // a ∉ w}), closed_ball (c a) (3 * r a),
  { assume z hz,
    set k := ⋃ (a : v) (ha : a ∈ w), B a with hk,
    have k_closed : is_closed k :=
      is_closed_bUnion w.finite_to_set (λ i hi, h't _ (ut (vu i.2))),
    have z_notmem_k : z ∉ k,
    { simp only [not_exists, exists_prop, mem_Union, mem_sep_iff, forall_exists_index,
        set_coe.exists, not_and, exists_and_distrib_right, subtype.coe_mk],
      assume b hbv h'b h'z,
      have : z ∈ (s \ ⋃ a ∈ u, B a) ∩ (⋃ a ∈ u, B a) :=
        mem_inter (mem_of_mem_inter_left hz) (mem_bUnion (vu hbv) h'z),
      simpa only [diff_inter_self] },
    -- since the elements of `w` are closed and finitely many, one can find a small ball around `z`
    -- not intersecting them
    have : ball x (R x) \ k ∈ 𝓝 z,
    { apply is_open.mem_nhds (is_open_ball.sdiff k_closed) _,
      exact (mem_diff _).2 ⟨mem_of_mem_inter_right hz, z_notmem_k⟩ },
    obtain ⟨d, dpos, hd⟩ : ∃ (d : ℝ) (dpos : 0 < d), closed_ball z d ⊆ ball x (R x) \ k :=
      nhds_basis_closed_ball.mem_iff.1 this,
    -- choose an element `a` of the family `t` contained in this small ball
    obtain ⟨a, hat, ad, rfl⟩ : ∃ a ∈ t, r a ≤ min d (R z) ∧ c a = z,
      from hf z ((mem_diff _).1 (mem_of_mem_inter_left hz)).1 (min d (R z)) (lt_min dpos (hR0 z)),
    have ax : B a ⊆ ball x (R x),
    { refine (hB a hat).trans _,
      refine subset.trans _ (hd.trans (diff_subset (ball x (R x)) k)),
      exact closed_ball_subset_closed_ball (ad.trans (min_le_left _ _)), },
    -- it intersects an element `b` of `u` with comparable diameter, by definition of `u`
    obtain ⟨b, bu, ab, bdiam⟩ : ∃ b ∈ u, (B a ∩ B b).nonempty ∧ r a ≤ 2 * r b,
      from hu a ⟨hat, ad.trans (min_le_right _ _)⟩,
    have bv : b ∈ v,
    { refine ⟨bu, ab.mono _⟩,
      rw inter_comm,
      exact inter_subset_inter_right _ ax },
    let b' : v := ⟨b, bv⟩,
    -- `b` can not belong to `w`, as the elements of `w` do not intersect `closed_ball z d`,
    -- contrary to `b`
    have b'_notmem_w : b' ∉ w,
    { assume b'w,
      have b'k : B b' ⊆ k, from @finset.subset_set_bUnion_of_mem _ _ _ (λ (y : v), B y) _ b'w,
      have : ((ball x (R x) \ k) ∩ k).nonempty,
      { apply ab.mono (inter_subset_inter _ b'k),
        refine ((hB _ hat).trans _).trans hd,
        exact (closed_ball_subset_closed_ball (ad.trans (min_le_left _ _))) },
      simpa only [diff_inter_self, not_nonempty_empty] },
    let b'' : {a // a ∉ w} := ⟨b', b'_notmem_w⟩,
    -- since `a` and `b` have comparable diameters, it follows that `z` belongs to the
    -- enlargement of `b`
    have zb : c a ∈ closed_ball (c b) (3 * r b),
    { rcases ab with ⟨e, ⟨ea, eb⟩⟩,
      have A : dist (c a) e ≤ r a, from mem_closed_ball'.1 (hB a hat ea),
      have B : dist e (c b) ≤ r b, from mem_closed_ball.1 (hB b (ut bu) eb),
      simp only [mem_closed_ball],
      linarith [dist_triangle (c a) e (c b)] },
    suffices H : closed_ball (c b'') (3 * r b'')
      ⊆ ⋃ (a : {a // a ∉ w}), closed_ball (c a) (3 * r a), from H zb,
    exact subset_Union (λ (a : {a // a ∉ w}), closed_ball (c a) (3 * r a)) b'' },
  -- now that we have proved our main inclusion, we can use it to estimate the measure of the points
  -- in `ball x (r x)` not covered by `u`.
  haveI : encodable v := (u_count.mono vu).to_encodable,
  calc μ ((s \ ⋃ a ∈ u, B a) ∩ ball x (R x))
      ≤ μ (⋃ (a : {a // a ∉ w}), closed_ball (c a) (3 * r a)) : measure_mono M
  ... ≤ ∑' (a : {a // a ∉ w}), μ (closed_ball (c a) (3 * r a)) :
    measure_Union_le _
  ... ≤ ∑' (a : {a // a ∉ w}), C * μ (B a) : ennreal.tsum_le_tsum (λ a, μB a (ut (vu a.1.2)))
  ... = C * ∑' (a : {a // a ∉ w}), μ (B a) : ennreal.tsum_mul_left
  ... ≤ C * (ε / C) : mul_le_mul_left' hw.le _
  ... ≤ ε : ennreal.mul_div_le
end

/-- Assume that around every point there are arbitrarily small scales at which the measure is
doubling. Then the set of closed sets `a` with nonempty interior contained in `closed_ball x r` and
covering a fixed proportion `1/C` of the ball `closed_ball x (3 * r)` forms a Vitali family.
This is essentially a restatement of the measurable Vitali theorem. -/
protected def vitali_family [metric_space α] [measurable_space α] [opens_measurable_space α]
  [second_countable_topology α] (μ : measure α) [is_locally_finite_measure μ] (C : ℝ≥0)
  (h : ∀ x, ∃ᶠ r in 𝓝[>] 0, μ (closed_ball x (3 * r)) ≤ C * μ (closed_ball x r)) :
  vitali_family μ :=
{ sets_at := λ x, {a | is_closed a ∧ (interior a).nonempty ∧ ∃ r, (a ⊆ closed_ball x r ∧
                      μ (closed_ball x (3 * r)) ≤ C * μ a)},
  measurable_set' := λ x a ha, ha.1.measurable_set,
  nonempty_interior := λ x a ha, ha.2.1,
  nontrivial := λ x ε εpos, begin
    obtain ⟨r, μr, rpos, rε⟩ : ∃ r,
      μ (closed_ball x (3 * r)) ≤ C * μ (closed_ball x r) ∧ r ∈ Ioc (0 : ℝ) ε :=
      ((h x).and_eventually (Ioc_mem_nhds_within_Ioi ⟨le_rfl, εpos⟩)).exists,
    refine ⟨closed_ball x r, ⟨is_closed_ball, _, ⟨r, subset.rfl, μr⟩⟩,
      closed_ball_subset_closed_ball rε⟩,
    exact (nonempty_ball.2 rpos).mono (ball_subset_interior_closed_ball)
  end,
  covering := begin
    assume s f fsubset ffine,
    let t : set (ℝ × α × set α) :=
      {p | p.2.2 ⊆ closed_ball p.2.1 p.1 ∧ μ (closed_ball p.2.1 (3 * p.1)) ≤ C * μ p.2.2
      ∧ (interior p.2.2).nonempty ∧ is_closed p.2.2 ∧ p.2.2 ∈ f p.2.1 ∧ p.2.1 ∈ s},
    have A : ∀ x ∈ s, ∀ (ε : ℝ), ε > 0 → (∃ (p : ℝ × α × set α) (Hp : p ∈ t), p.1 ≤ ε ∧ p.2.1 = x),
    { assume x xs ε εpos,
      rcases ffine x xs ε εpos with ⟨a, ha, h'a⟩,
      rcases fsubset x xs ha with ⟨a_closed, a_int, ⟨r, ar, μr⟩⟩,
      refine ⟨⟨min r ε, x, a⟩, ⟨_, _, a_int, a_closed, ha, xs⟩, min_le_right _ _, rfl⟩,
      { rcases min_cases r ε with h'|h'; rwa h'.1 },
      { apply le_trans (measure_mono (closed_ball_subset_closed_ball _)) μr,
        exact mul_le_mul_of_nonneg_left (min_le_left _ _) zero_le_three } },
    rcases exists_disjoint_covering_ae μ s t C (λ p, p.1) (λ p, p.2.1) (λ p, p.2.2) (λ p hp, hp.1)
      (λ p hp, hp.2.1) (λ p hp, hp.2.2.1) (λ p hp, hp.2.2.2.1) A
      with ⟨t', t't, t'_count, t'_disj, μt'⟩,
    refine ⟨(λ (p : ℝ × α × set α), p.2) '' t', _, _, _, _⟩,
    { rintros - ⟨q, hq, rfl⟩,
      exact (t't hq).2.2.2.2.2 },
    { rintros p ⟨q, hq, rfl⟩ p' ⟨q', hq', rfl⟩ hqq',
      exact t'_disj hq hq' (ne_of_apply_ne _ hqq') },
    { rintros - ⟨q, hq, rfl⟩,
      exact (t't hq).2.2.2.2.1 },
    { convert μt' using 3,
      rw bUnion_image }
  end }

end vitali

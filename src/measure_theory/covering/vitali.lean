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
element `b` of `u` of size larger than that of `a` up to `τ`, i.e., `δ b ≥ δ a / τ`.
-/
theorem vitali_covering
  (t : set (set α)) (δ : set α → ℝ) (τ : ℝ) (hτ : 1 < τ) (δnonneg : ∀ a ∈ t, 0 ≤ δ a)
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
theorem vitali_covering_closed_ball [metric_space α]
  (t : set (set α)) (R : ℝ) (ht : ∀ s ∈ t, ∃ x r, s = closed_ball x r ∧ r ≤ R) :
  ∃ u ⊆ t, u.pairwise_on (disjoint on id) ∧
    ∀ a ∈ t, ∃ x r, closed_ball x r ∈ u ∧ a ⊆ closed_ball x (5 * r) :=
begin
  rcases eq_empty_or_nonempty t with rfl|tnonempty,
  { exact ⟨∅, subset.refl _, by simp⟩ },
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
  have r_nonneg : ∀ (a : set α), a ∈ t → a.nonempty → 0 ≤ r a,
  { assume a hat a_nonempty,
    rw (hxr a hat).1 at a_nonempty,
    simpa only [nonempty_closed_ball] using a_nonempty },
  -- The difference with the generic version is that we are not excluding empty sets in our family
  -- (which would correspond to `r a < 0`). To compensate for this, we apply the generic version
  -- to the subfamily `t'` made of nonempty sets, and we use `δ = r` there. This gives a disjointed
  -- subfamily `u'`.
  let t' := {a ∈ t | 0 ≤ r a},
  obtain ⟨u', u't', u'_disj, hu'⟩ : ∃ u' ⊆ t', u'.pairwise_on (disjoint on id) ∧
    ∀ a ∈ t', ∃ b ∈ u', set.nonempty (a ∩ b) ∧ r a ≤ 2 * r b,
  { refine vitali_covering t' r 2 one_lt_two (λ a ha, ha.2) R (λ a ha, (hxr a ha.1).2) (λ a ha, _),
    rw [(hxr a ha.1).1],
    simp only [ha.2, nonempty_closed_ball] },
  -- this subfamily is nonempty, as we have excluded the situation `t = {∅}`.
  have u'_nonempty : u'.nonempty,
  { have : ∃ a ∈ t, a ≠ ∅,
    { contrapose! t_eq_empty,
      apply subset.antisymm,
      { simpa only using t_eq_empty },
      { rcases tnonempty with ⟨a, hat⟩,
        have := t_eq_empty a hat,
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

open topological_space
open_locale ennreal topological_space

.

open filter

theorem measurable_vitali [metric_space α] [measurable_space α] [opens_measurable_space α]
  [second_countable_topology α]
  (μ : measure α) [is_locally_finite_measure μ] (s : set α)
  (t : set (set α)) (hf : ∀ x ∈ s, ∀ (ε > (0 : ℝ)), ∃ a ∈ t, x ∈ a ∧ a ⊆ closed_ball x ε)
  (ht : ∀ a ∈ t, (interior a).nonempty) (h't : ∀ a ∈ t, is_closed a)
  (C : ℝ≥0) (h : ∀ a ∈ t, ∃ x ∈ a, μ (closed_ball x (5 * diam a)) ≤ C * μ a) :
  ∃ u ⊆ t, countable u ∧ u.pairwise_on (disjoint on id) ∧ μ (s \ ⋃ (a ∈ u), a) = 0 :=
begin
  rcases eq_empty_or_nonempty s with rfl|nonempty,
  { refine ⟨∅, empty_subset _, countable_empty, by simp only [pairwise_on_empty],
      by simp only [measure_empty, Union_false, Union_empty, diff_self]⟩ },
  haveI : inhabited α,
  { choose x hx using nonempty,
    exact ⟨x⟩ },
  have : ∀ x, ∃ r, 0 < r ∧ r ≤ 1 ∧ μ (closed_ball x (20 * r)) < ∞, sorry,
  /-{ assume x,
    obtain ⟨R, Rpos, μR⟩ : ∃ (R : ℝ) (hR : 0 < R), μ (closed_ball x R) < ∞ :=
      (μ.finite_at_nhds x).exists_mem_basis nhds_basis_closed_ball,
    refine ⟨min 1 (R/20), _, min_le_left _ _, _⟩,
    { simp only [true_and, lt_min_iff, zero_lt_one],
      linarith },
    { apply lt_of_le_of_lt (measure_mono _) μR,
      apply closed_ball_subset_closed_ball,
      calc 20 * min 1 (R / 20) ≤ 20 * (R/20) :
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
      ... = R : by ring } },-/
  choose r hr using this,
  let t' := {a ∈ t | ∃ x, a ⊆ closed_ball x (r x)},
  obtain ⟨u, ut', u_disj, hu⟩ : ∃ u ⊆ t', u.pairwise_on (disjoint on id) ∧
    ∀ a ∈ t', ∃ b ∈ u, set.nonempty (a ∩ b) ∧ diam a ≤ 2 * diam b,
  sorry,
  /-{ have A : ∀ (a : set α), a ∈ t' → diam a ≤ 2,
    { rintros a ⟨hat, ⟨x, hax⟩⟩,
      calc diam a ≤ diam (closed_ball x (r x)) : diam_mono hax bounded_closed_ball
      ... ≤ 2 * r x : diam_closed_ball (hr x).1.le
      ... ≤ 2 * 1 : mul_le_mul_of_nonneg_left (hr x).2.1 zero_le_two
      ... = 2 : by norm_num },
    have B : ∀ (a : set α), a ∈ t' → a.nonempty :=
      λ a hat', nonempty.mono interior_subset (ht a hat'.1),
    exact vitali_covering t' diam 2 one_lt_two (λ a ha, diam_nonneg) 2 A B },-/
  have ut : u ⊆ t := λ a hau, (ut' hau).1,
  have u_count : countable u :=
    countable_of_nonempty_interior_of_disjoint id (λ a ha, ht a (ut ha)) u_disj,
  refine ⟨u, λ a hat', (ut' hat').1, u_count, u_disj, _⟩,
  refine null_of_locally_null _ (λ x hx, _),
  let v := {a ∈ u | (a ∩ ball x (r x)).nonempty },
  have vu : v ⊆ u := λ a ha, ha.1,
  obtain ⟨R, μR, hR⟩ : ∃ R, μ (closed_ball x R) < ∞ ∧
                          ∀ a ∈ u, (a ∩ ball x (r x)).nonempty → a ⊆ closed_ball x R,
  sorry,
  /-{ have : ∀ a ∈ u, ∃ y, a ⊆ closed_ball y (r y) := λ a hau, (ut' hau).2,
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
    { have R0pos : 0 < R0, by linarith [(hr x).1],
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
        linarith [Idist_v b ⟨bu, hbx⟩] } } }-/
  refine ⟨ball x (r x), _, le_antisymm (le_of_forall_lt' (λ ε εpos, _)) bot_le⟩,
  { apply mem_nhds_within_of_mem_nhds (is_open_ball.mem_nhds _),
    simp only [(hr x).left, mem_ball, dist_self] },
  have I : ∑' (a : v), μ a < ∞,
  { calc ∑' (a : v), μ a = μ (⋃ (a ∈ v), a) : begin
      rw measure_bUnion (u_count.mono vu) _ (λ a ha, (h't _ (vu.trans ut ha)).measurable_set),
      exact u_disj.mono vu
    end
    ... ≤ μ (closed_ball x R) : measure_mono (bUnion_subset (λ a ha, hR a (vu ha) ha.2))
    ... < ∞ : μR },
  obtain ⟨w, hw⟩ : ∃ (w : finset ↥v), ∑' (a : {a // a ∉ w}), μ a < ε,
  { haveI : ne_bot (at_top : filter (finset v)) := at_top_ne_bot,
    exact ((tendsto_order.1 (ennreal.tendsto_tsum_compl_at_top_zero I.ne)).2 ε εpos).exists },
  choose! y hy using h,
  have : (s \ ⋃ (a : set α) (H : a ∈ u), a) ∩ ball x (r x)
    ⊆ ⋃ (a : {a // a ∉ w}), closed_ball (y a) (5 * diam (a : set α)),
  { assume z hz,
    let k := ⋃ (a : v) (ha : a ∈ w), (a : set α),
    have : is_closed k :=
      is_closed_bUnion w.finite_to_set (λ i hi, h't _ (ut (vu i.2))),
    have : ∃ d, 0 < d ∧ closed_ball z d ∩ k = ∅,
    { rcases eq_empty_or_nonempty k with hk|hk,
      { refine ⟨1, zero_lt_one, by simp [hk]⟩ },
      have : z ∉ k,
      { simp only [not_exists, exists_prop, mem_Union, mem_sep_eq, forall_exists_index,
          set_coe.exists, not_and, exists_and_distrib_right, subtype.coe_mk],
        assume b hbv h'b h'z,
        have : z ∈ (s \ ⋃ (a : set α) (H : a ∈ u), a) ∩ (⋃ (a : set α) (H : a ∈ u), a) :=
          mem_inter (mem_of_mem_inter_left hz) (mem_bUnion (vu hbv) h'z),
        simpa only [diff_inter_self] },
      refine ⟨inf_dist z k / 2, _, _⟩,
      have Z := is_closed.not_mem_iff_inf_dist_pos


    }

  }

end

/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import measure_theory.covering.differentiation
import measure_theory.covering.vitali_family
import measure_theory.integral.lebesgue
import measure_theory.measure.regular
import set_theory.ordinal.arithmetic
import topology.metric_space.basic

/-!
# Besicovitch covering theorems

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The topological Besicovitch covering theorem ensures that, in a nice metric space, there exists a
number `N` such that, from any family of balls with bounded radii, one can extract `N` families,
each made of disjoint balls, covering together all the centers of the initial family.

By "nice metric space", we mean a technical property stated as follows: there exists no satellite
configuration of `N + 1` points (with a given parameter `τ > 1`). Such a configuration is a family
of `N + 1` balls, where the first `N` balls all intersect the last one, but none of them contains
the center of another one and their radii are controlled. This property is for instance
satisfied by finite-dimensional real vector spaces.

In this file, we prove the topological Besicovitch covering theorem,
in `besicovitch.exist_disjoint_covering_families`.

The measurable Besicovitch theorem ensures that, in the same class of metric spaces, if at every
point one considers a class of balls of arbitrarily small radii, called admissible balls, then
one can cover almost all the space by a family of disjoint admissible balls.
It is deduced from the topological Besicovitch theorem, and proved
in `besicovitch.exists_disjoint_closed_ball_covering_ae`.

This implies that balls of small radius form a Vitali family in such spaces. Therefore, theorems
on differentiation of measures hold as a consequence of general results. We restate them in this
context to make them more easily usable.

## Main definitions and results

* `satellite_config α N τ` is the type of all satellite configurations of `N + 1` points
  in the metric space `α`, with parameter `τ`.
* `has_besicovitch_covering` is a class recording that there exist `N` and `τ > 1` such that
  there is no satellite configuration of `N + 1` points with parameter `τ`.
* `exist_disjoint_covering_families` is the topological Besicovitch covering theorem: from any
  family of balls one can extract finitely many disjoint subfamilies covering the same set.
* `exists_disjoint_closed_ball_covering` is the measurable Besicovitch covering theorem: from any
  family of balls with arbitrarily small radii at every point, one can extract countably many
  disjoint balls covering almost all the space. While the value of `N` is relevant for the precise
  statement of the topological Besicovitch theorem, it becomes irrelevant for the measurable one.
  Therefore, this statement is expressed using the `Prop`-valued
  typeclass `has_besicovitch_covering`.

We also restate the following specialized versions of general theorems on differentiation of
measures:
* `besicovitch.ae_tendsto_rn_deriv` ensures that `ρ (closed_ball x r) / μ (closed_ball x r)` tends
  almost surely to the Radon-Nikodym derivative of `ρ` with respect to `μ` at `x`.
* `besicovitch.ae_tendsto_measure_inter_div` states that almost every point in an arbitrary set `s`
  is a Lebesgue density point, i.e., `μ (s ∩ closed_ball x r) / μ (closed_ball x r)` tends to `1` as
  `r` tends to `0`. A stronger version for measurable sets is given in
  `besicovitch.ae_tendsto_measure_inter_div_of_measurable_set`.

## Implementation

#### Sketch of proof of the topological Besicovitch theorem:

We choose balls in a greedy way. First choose a ball with maximal radius (or rather, since there
is no guarantee the maximal radius is realized, a ball with radius within a factor `τ` of the
supremum). Then, remove all balls whose center is covered by the first ball, and choose among the
remaining ones a ball with radius close to maximum. Go on forever until there is no available
center (this is a transfinite induction in general).

Then define inductively a coloring of the balls. A ball will be of color `i` if it intersects
already chosen balls of color `0`, ..., `i - 1`, but none of color `i`. In this way, balls of the
same color form a disjoint family, and the space is covered by the families of the different colors.

The nontrivial part is to show that at most `N` colors are used. If one needs `N + 1` colors,
consider the first time this happens. Then the corresponding ball intersects `N` balls of the
different colors. Moreover, the inductive construction ensures that the radii of all the balls are
controlled: they form a satellite configuration with `N + 1` balls (essentially by definition of
satellite configurations). Since we assume that there are no such configurations, this is a
contradiction.

#### Sketch of proof of the measurable Besicovitch theorem:

From the topological Besicovitch theorem, one can find a disjoint countable family of balls
covering a proportion `> 1 / (N + 1)` of the space. Taking a large enough finite subset of these
balls, one gets the same property for finitely many balls. Their union is closed. Therefore, any
point in the complement has around it an admissible ball not intersecting these finitely many balls.
Applying again the topological Besicovitch theorem, one extracts from these a disjoint countable
subfamily covering a proportion `> 1 / (N + 1)` of the remaining points, and then even a disjoint
finite subfamily. Then one goes on again and again, covering at each step a positive proportion of
the remaining points, while remaining disjoint from the already chosen balls. The union of all these
balls is the desired almost everywhere covering.
-/

noncomputable theory

universe u

open metric set filter fin measure_theory topological_space
open_locale topology classical big_operators ennreal measure_theory nnreal


/-!
### Satellite configurations
-/

/-- A satellite configuration is a configuration of `N+1` points that shows up in the inductive
construction for the Besicovitch covering theorem. It depends on some parameter `τ ≥ 1`.

This is a family of balls (indexed by `i : fin N.succ`, with center `c i` and radius `r i`) such
that the last ball intersects all the other balls (condition `inter`),
and given any two balls there is an order between them, ensuring that the first ball does not
contain the center of the other one, and the radius of the second ball can not be larger than
the radius of the first ball (up to a factor `τ`). This order corresponds to the order of choice
in the inductive construction: otherwise, the second ball would have been chosen before.
This is the condition `h`.

Finally, the last ball is chosen after all the other ones, meaning that `h` can be strengthened
by keeping only one side of the alternative in `hlast`.
-/
structure besicovitch.satellite_config (α : Type*) [metric_space α] (N : ℕ) (τ : ℝ) :=
(c : fin N.succ → α)
(r : fin N.succ → ℝ)
(rpos : ∀ i, 0 < r i)
(h : ∀ i j, i ≠ j → (r i ≤ dist (c i) (c j) ∧ r j ≤ τ * r i) ∨
                    (r j ≤ dist (c j) (c i) ∧ r i ≤ τ * r j))
(hlast : ∀ i < last N, r i ≤ dist (c i) (c (last N)) ∧ r (last N) ≤ τ * r i)
(inter : ∀ i < last N, dist (c i) (c (last N)) ≤ r i + r (last N))

/-- A metric space has the Besicovitch covering property if there exist `N` and `τ > 1` such that
there are no satellite configuration of parameter `τ` with `N+1` points. This is the condition that
guarantees that the measurable Besicovitch covering theorem holds. It is satified by
finite-dimensional real vector spaces. -/
class has_besicovitch_covering (α : Type*) [metric_space α] : Prop :=
(no_satellite_config [] : ∃ (N : ℕ) (τ : ℝ), 1 < τ ∧ is_empty (besicovitch.satellite_config α N τ))

/-- There is always a satellite configuration with a single point. -/
instance {α : Type*} {τ : ℝ} [inhabited α] [metric_space α] :
  inhabited (besicovitch.satellite_config α 0 τ) :=
⟨{ c := default,
  r := λ i, 1,
  rpos := λ i, zero_lt_one,
  h := λ i j hij, (hij (subsingleton.elim i j)).elim,
  hlast := λ i hi, by { rw subsingleton.elim i (last 0) at hi, exact (lt_irrefl _ hi).elim },
  inter := λ i hi, by { rw subsingleton.elim i (last 0) at hi, exact (lt_irrefl _ hi).elim } }⟩

namespace besicovitch

namespace satellite_config
variables {α : Type*} [metric_space α] {N : ℕ} {τ : ℝ} (a : satellite_config α N τ)

lemma inter' (i : fin N.succ) : dist (a.c i) (a.c (last N)) ≤ a.r i + a.r (last N) :=
begin
  rcases lt_or_le i (last N) with H|H,
  { exact a.inter i H },
  { have I : i = last N := top_le_iff.1 H,
    have := (a.rpos (last N)).le,
    simp only [I, add_nonneg this this, dist_self] }
end

lemma hlast' (i : fin N.succ) (h : 1 ≤ τ) : a.r (last N) ≤ τ * a.r i :=
begin
  rcases lt_or_le i (last N) with H|H,
  { exact (a.hlast i H).2 },
  { have : i = last N := top_le_iff.1 H,
    rw this,
    exact le_mul_of_one_le_left (a.rpos _).le h }
end

end satellite_config

/-! ### Extracting disjoint subfamilies from a ball covering -/

/-- A ball package is a family of balls in a metric space with positive bounded radii. -/
structure ball_package (β : Type*) (α : Type*) :=
(c : β → α)
(r : β → ℝ)
(rpos : ∀ b, 0 < r b)
(r_bound : ℝ)
(r_le : ∀ b, r b ≤ r_bound)

/-- The ball package made of unit balls. -/
def unit_ball_package (α : Type*) : ball_package α α :=
{ c := id,
  r := λ _, 1,
  rpos := λ _, zero_lt_one,
  r_bound := 1,
  r_le := λ _, le_rfl }

instance (α : Type*) : inhabited (ball_package α α) :=
⟨unit_ball_package α⟩

/-- A Besicovitch tau-package is a family of balls in a metric space with positive bounded radii,
together with enough data to proceed with the Besicovitch greedy algorithm. We register this in
a single structure to make sure that all our constructions in this algorithm only depend on
one variable. -/
structure tau_package (β : Type*) (α : Type*) extends ball_package β α :=
(τ : ℝ)
(one_lt_tau : 1 < τ)

instance (α : Type*) : inhabited (tau_package α α) :=
⟨{ τ := 2,
  one_lt_tau := one_lt_two,
  .. unit_ball_package α }⟩

variables {α : Type*} [metric_space α] {β : Type u}

namespace tau_package

variables [nonempty β] (p : tau_package β α)
include p

/-- Choose inductively large balls with centers that are not contained in the union of already
chosen balls. This is a transfinite induction. -/
noncomputable def index : ordinal.{u} → β
| i :=
    -- `Z` is the set of points that are covered by already constructed balls
    let Z := ⋃ (j : {j // j < i}), ball (p.c (index j)) (p.r (index j)),
    -- `R` is the supremum of the radii of balls with centers not in `Z`
    R := supr (λ b : {b : β // p.c b ∉ Z}, p.r b) in
    -- return an index `b` for which the center `c b` is not in `Z`, and the radius is at
    -- least `R / τ`, if such an index exists (and garbage otherwise).
    classical.epsilon (λ b : β, p.c b ∉ Z ∧ R ≤ p.τ * p.r b)
using_well_founded {dec_tac := `[exact j.2]}

/-- The set of points that are covered by the union of balls selected at steps `< i`. -/
def Union_up_to (i : ordinal.{u}) : set α :=
⋃ (j : {j // j < i}), ball (p.c (p.index j)) (p.r (p.index j))

lemma monotone_Union_up_to : monotone p.Union_up_to :=
begin
  assume i j hij,
  simp only [Union_up_to],
  exact Union_mono' (λ r, ⟨⟨r, r.2.trans_le hij⟩, subset.rfl⟩),
end

/-- Supremum of the radii of balls whose centers are not yet covered at step `i`. -/
def R (i : ordinal.{u}) : ℝ :=
supr (λ b : {b : β // p.c b ∉ p.Union_up_to i}, p.r b)

/-- Group the balls into disjoint families, by assigning to a ball the smallest color for which
it does not intersect any already chosen ball of this color. -/
noncomputable def color : ordinal.{u} → ℕ
| i := let A : set ℕ := ⋃ (j : {j // j < i})
          (hj : (closed_ball (p.c (p.index j)) (p.r (p.index j))
            ∩ closed_ball (p.c (p.index i)) (p.r (p.index i))).nonempty), {color j} in
       Inf (univ \ A)
using_well_founded {dec_tac := `[exact j.2]}

/-- `p.last_step` is the first ordinal where the construction stops making sense, i.e., `f` returns
garbage since there is no point left to be chosen. We will only use ordinals before this step. -/
def last_step : ordinal.{u} :=
Inf {i | ¬ ∃ (b : β), p.c b ∉ p.Union_up_to i ∧ p.R i ≤ p.τ * p.r b}

lemma last_step_nonempty :
  {i | ¬ ∃ (b : β), p.c b ∉ p.Union_up_to i ∧ p.R i ≤ p.τ * p.r b}.nonempty :=
begin
  by_contra,
  suffices H : function.injective p.index, from not_injective_of_ordinal p.index H,
  assume x y hxy,
  wlog x_le_y : x ≤ y generalizing x y,
  { exact (this hxy.symm (le_of_not_le x_le_y)).symm },
  rcases eq_or_lt_of_le x_le_y with rfl|H, { refl },
  simp only [nonempty_def, not_exists, exists_prop, not_and, not_lt, not_le, mem_set_of_eq,
    not_forall] at h,
  specialize h y,
  have A : p.c (p.index y) ∉ p.Union_up_to y,
  { have : p.index y = classical.epsilon (λ b : β, p.c b ∉ p.Union_up_to y ∧ p.R y ≤ p.τ * p.r b),
      by { rw [tau_package.index], refl },
    rw this,
    exact (classical.epsilon_spec h).1 },
  simp only [Union_up_to, not_exists, exists_prop, mem_Union, mem_closed_ball, not_and, not_le,
              subtype.exists, subtype.coe_mk] at A,
  specialize A x H,
  simp [hxy] at A,
  exact (lt_irrefl _ ((p.rpos (p.index y)).trans_le A)).elim
end

/-- Every point is covered by chosen balls, before `p.last_step`. -/
lemma mem_Union_up_to_last_step (x : β) : p.c x ∈ p.Union_up_to p.last_step :=
begin
  have A : ∀ (z : β), p.c z ∈ p.Union_up_to p.last_step ∨ p.τ * p.r z < p.R p.last_step,
  { have : p.last_step ∈ {i | ¬ ∃ (b : β), p.c b ∉ p.Union_up_to i ∧ p.R i ≤ p.τ * p.r b} :=
      Inf_mem p.last_step_nonempty,
    simpa only [not_exists, mem_set_of_eq, not_and_distrib, not_le, not_not_mem] },
  by_contra,
  rcases A x with H|H, { exact h H },
  have Rpos : 0 < p.R p.last_step,
  { apply lt_trans (mul_pos (_root_.zero_lt_one.trans p.one_lt_tau) (p.rpos _)) H },
  have B : p.τ⁻¹ * p.R p.last_step < p.R p.last_step,
  { conv_rhs { rw ← one_mul (p.R p.last_step) },
    exact mul_lt_mul (inv_lt_one p.one_lt_tau) le_rfl Rpos zero_le_one },
  obtain ⟨y, hy1, hy2⟩ : ∃ (y : β),
    p.c y ∉ p.Union_up_to p.last_step ∧ (p.τ)⁻¹ * p.R p.last_step < p.r y,
  { simpa only [exists_prop, mem_range, exists_exists_and_eq_and, subtype.exists, subtype.coe_mk]
      using exists_lt_of_lt_cSup _ B,
    rw [← image_univ, nonempty_image_iff],
    exact ⟨⟨_, h⟩, mem_univ _⟩ },
  rcases A y with Hy|Hy,
  { exact hy1 Hy },
  { rw ← div_eq_inv_mul at hy2,
    have := (div_le_iff' (_root_.zero_lt_one.trans p.one_lt_tau)).1 hy2.le,
    exact lt_irrefl _ (Hy.trans_le this) }
end

/-- If there are no configurations of satellites with `N+1` points, one never uses more than `N`
distinct families in the Besicovitch inductive construction. -/
lemma color_lt {i : ordinal.{u}} (hi : i < p.last_step)
  {N : ℕ} (hN : is_empty (satellite_config α N p.τ)) :
  p.color i < N :=
begin
  /- By contradiction, consider the first ordinal `i` for which one would have `p.color i = N`.
  Choose for each `k < N` a ball with color `k` that intersects the ball at color `i`
  (there is such a ball, otherwise one would have used the color `k` and not `N`).
  Then this family of `N+1` balls forms a satellite configuration, which is forbidden by
  the assumption `hN`. -/
  induction i using ordinal.induction with i IH,
  let A : set ℕ := ⋃ (j : {j // j < i})
         (hj : (closed_ball (p.c (p.index j)) (p.r (p.index j))
            ∩ closed_ball (p.c (p.index i)) (p.r (p.index i))).nonempty), {p.color j},
  have color_i : p.color i = Inf (univ \ A), by rw [color],
  rw color_i,
  have N_mem : N ∈ univ \ A,
  { simp only [not_exists, true_and, exists_prop, mem_Union, mem_singleton_iff, mem_closed_ball,
      not_and, mem_univ, mem_diff, subtype.exists, subtype.coe_mk],
    assume j ji hj,
    exact (IH j ji (ji.trans hi)).ne' },
  suffices : Inf (univ \ A) ≠ N,
  { rcases (cInf_le (order_bot.bdd_below (univ \ A)) N_mem).lt_or_eq with H|H,
    { exact H },
    { exact (this H).elim } },
  assume Inf_eq_N,
  have : ∀ k, k < N → ∃ j, j < i
    ∧ (closed_ball (p.c (p.index j)) (p.r (p.index j))
        ∩ closed_ball (p.c (p.index i)) (p.r (p.index i))).nonempty
    ∧ k = p.color j,
  { assume k hk,
    rw ← Inf_eq_N at hk,
    have : k ∈ A,
      by simpa only [true_and, mem_univ, not_not, mem_diff] using nat.not_mem_of_lt_Inf hk,
    simp at this,
    simpa only [exists_prop, mem_Union, mem_singleton_iff, mem_closed_ball, subtype.exists,
      subtype.coe_mk] },
  choose! g hg using this,
  -- Choose for each `k < N` an ordinal `G k < i`  giving a ball of color `k` intersecting
  -- the last ball.
  let G : ℕ → ordinal := λ n, if n = N then i else g n,
  have color_G : ∀ n, n ≤ N → p.color (G n) = n,
  { assume n hn,
    unfreezingI { rcases hn.eq_or_lt with rfl|H },
    { simp only [G], simp only [color_i, Inf_eq_N, if_true, eq_self_iff_true] },
    { simp only [G], simp only [H.ne, (hg n H).right.right.symm, if_false] } },
  have G_lt_last : ∀ n, n ≤ N → G n < p.last_step,
  { assume n hn,
    unfreezingI { rcases hn.eq_or_lt with rfl|H },
    { simp only [G], simp only [hi, if_true, eq_self_iff_true], },
    { simp only [G], simp only [H.ne, (hg n H).left.trans hi, if_false] } },
  have fGn : ∀ n, n ≤ N →
    p.c (p.index (G n)) ∉ p.Union_up_to (G n) ∧ p.R (G n) ≤ p.τ * p.r (p.index (G n)),
  { assume n hn,
    have: p.index (G n) = classical.epsilon
      (λ t, p.c t ∉ p.Union_up_to (G n) ∧ p.R (G n) ≤ p.τ * p.r t), by { rw index, refl },
    rw this,
    have : ∃ t, p.c t ∉ p.Union_up_to (G n) ∧ p.R (G n) ≤ p.τ * p.r t,
      by simpa only [not_exists, exists_prop, not_and, not_lt, not_le, mem_set_of_eq,
        not_forall] using not_mem_of_lt_cInf (G_lt_last n hn) (order_bot.bdd_below _),
    exact classical.epsilon_spec this },
  -- the balls with indices `G k` satisfy the characteristic property of satellite configurations.
  have Gab : ∀ (a b : fin (nat.succ N)), G a < G b →
    p.r (p.index (G a)) ≤ dist (p.c (p.index (G a))) (p.c (p.index (G b)))
      ∧ p.r (p.index (G b)) ≤ p.τ * p.r (p.index (G a)),
  { assume a b G_lt,
    have ha : (a : ℕ) ≤ N := nat.lt_succ_iff.1 a.2,
    have hb : (b : ℕ) ≤ N := nat.lt_succ_iff.1 b.2,
    split,
    { have := (fGn b hb).1,
      simp only [Union_up_to, not_exists, exists_prop, mem_Union, mem_closed_ball, not_and,
        not_le, subtype.exists, subtype.coe_mk] at this,
      simpa only [dist_comm, mem_ball, not_lt] using this (G a) G_lt },
    { apply le_trans _ (fGn a ha).2,
      have B : p.c (p.index (G b)) ∉ p.Union_up_to (G a),
      { assume H, exact (fGn b hb).1 (p.monotone_Union_up_to G_lt.le H) },
      let b' : {t // p.c t ∉ p.Union_up_to (G a)} := ⟨p.index (G b), B⟩,
      apply @le_csupr _ _ _ (λ t : {t // p.c t ∉ p.Union_up_to (G a)}, p.r t) _ b',
      refine ⟨p.r_bound, λ t ht, _⟩,
      simp only [exists_prop, mem_range, subtype.exists, subtype.coe_mk] at ht,
      rcases ht with ⟨u, hu⟩,
      rw ← hu.2,
      exact p.r_le _ } },
  -- therefore, one may use them to construct a satellite configuration with `N+1` points
  let sc : satellite_config α N p.τ :=
  { c := λ k, p.c (p.index (G k)),
    r := λ k, p.r (p.index (G k)),
    rpos := λ k, p.rpos (p.index (G k)),
    h := begin
      assume a b a_ne_b,
      wlog G_le : G a ≤ G b generalizing a b,
      { exact (this b a a_ne_b.symm (le_of_not_le G_le)).symm },
      have G_lt : G a < G b,
      { rcases G_le.lt_or_eq with H|H, { exact H },
        have A : (a : ℕ) ≠ b := fin.coe_injective.ne a_ne_b,
        rw [← color_G a (nat.lt_succ_iff.1 a.2), ← color_G b (nat.lt_succ_iff.1 b.2), H] at A,
        exact (A rfl).elim },
      exact or.inl (Gab a b G_lt),
    end,
    hlast := begin
      assume a ha,
      have I : (a : ℕ) < N := ha,
      have : G a < G (fin.last N), by { dsimp [G], simp [I.ne, (hg a I).1] },
      exact Gab _ _ this,
    end,
    inter := begin
      assume a ha,
      have I : (a : ℕ) < N := ha,
      have J : G (fin.last N) = i, by { dsimp [G], simp only [if_true, eq_self_iff_true], },
      have K : G a = g a, { dsimp [G], simp [I.ne, (hg a I).1] },
      convert dist_le_add_of_nonempty_closed_ball_inter_closed_ball (hg _ I).2.1,
    end },
  -- this is a contradiction
  exact (hN.false : _) sc
end

end tau_package

open tau_package

/-- The topological Besicovitch covering theorem: there exist finitely many families of disjoint
balls covering all the centers in a package. More specifically, one can use `N` families if there
are no satellite configurations with `N+1` points. -/
theorem exist_disjoint_covering_families {N : ℕ} {τ : ℝ}
  (hτ : 1 < τ) (hN : is_empty (satellite_config α N τ)) (q : ball_package β α) :
  ∃ s : fin N → set β,
    (∀ (i : fin N), (s i).pairwise_disjoint (λ j, closed_ball (q.c j) (q.r j))) ∧
      (range q.c ⊆ ⋃ (i : fin N), ⋃ (j ∈ s i), ball (q.c j) (q.r j)) :=
begin
  -- first exclude the trivial case where `β` is empty (we need non-emptiness for the transfinite
  -- induction, to be able to choose garbage when there is no point left).
  casesI is_empty_or_nonempty β,
  { refine ⟨λ i, ∅, λ i, pairwise_disjoint_empty, _⟩,
    rw [← image_univ, eq_empty_of_is_empty (univ : set β)],
    simp },
  -- Now, assume `β` is nonempty.
  let p : tau_package β α := { τ := τ, one_lt_tau := hτ, .. q },
  -- we use for `s i` the balls of color `i`.
  let s := λ (i : fin N),
    ⋃ (k : ordinal.{u}) (hk : k < p.last_step) (h'k : p.color k = i), ({p.index k} : set β),
  refine ⟨s, λ i, _, _⟩,
  { -- show that balls of the same color are disjoint
    assume x hx y hy x_ne_y,
    obtain ⟨jx, jx_lt, jxi, rfl⟩ :
      ∃ (jx : ordinal), jx < p.last_step ∧ p.color jx = i ∧ x = p.index jx,
        by simpa only [exists_prop, mem_Union, mem_singleton_iff] using hx,
    obtain ⟨jy, jy_lt, jyi, rfl⟩ :
      ∃ (jy : ordinal), jy < p.last_step ∧ p.color jy = i ∧ y = p.index jy,
        by simpa only [exists_prop, mem_Union, mem_singleton_iff] using hy,
    wlog jxy : jx ≤ jy generalizing jx jy,
    { exact (this jy jy_lt jyi hy jx jx_lt jxi hx x_ne_y.symm (le_of_not_le jxy)).symm },
    replace jxy : jx < jy,
      by { rcases lt_or_eq_of_le jxy with H|rfl, { exact H }, { exact (x_ne_y rfl).elim } },
    let A : set ℕ := ⋃ (j : {j // j < jy})
         (hj : (closed_ball (p.c (p.index j)) (p.r (p.index j))
            ∩ closed_ball (p.c (p.index jy)) (p.r (p.index jy))).nonempty), {p.color j},
    have color_j : p.color jy = Inf (univ \ A), by rw [tau_package.color],
    have : p.color jy ∈ univ \ A,
    { rw color_j,
      apply Inf_mem,
      refine ⟨N, _⟩,
      simp only [not_exists, true_and, exists_prop, mem_Union, mem_singleton_iff, not_and, mem_univ,
        mem_diff, subtype.exists, subtype.coe_mk],
      assume k hk H,
      exact (p.color_lt (hk.trans jy_lt) hN).ne' },
    simp only [not_exists, true_and, exists_prop, mem_Union, mem_singleton_iff, not_and, mem_univ,
      mem_diff, subtype.exists, subtype.coe_mk] at this,
    specialize this jx jxy,
    contrapose! this,
    simpa only [jxi, jyi, and_true, eq_self_iff_true, ← not_disjoint_iff_nonempty_inter] },
  { -- show that the balls of color at most `N` cover every center.
    refine range_subset_iff.2 (λ b, _),
    obtain ⟨a, ha⟩ :
      ∃ (a : ordinal), a < p.last_step ∧ dist (p.c b) (p.c (p.index a)) < p.r (p.index a),
      by simpa only [Union_up_to, exists_prop, mem_Union, mem_ball, subtype.exists, subtype.coe_mk]
        using p.mem_Union_up_to_last_step b,
    simp only [exists_prop, mem_Union, mem_ball, mem_singleton_iff, bUnion_and', exists_eq_left,
      Union_exists, exists_and_distrib_left],
    exact ⟨⟨p.color a, p.color_lt ha.1 hN⟩, a, rfl, ha⟩ }
end

/-!
### The measurable Besicovitch covering theorem
-/

open_locale nnreal
variables [second_countable_topology α] [measurable_space α] [opens_measurable_space α]

/-- Consider, for each `x` in a set `s`, a radius `r x ∈ (0, 1]`. Then one can find finitely
many disjoint balls of the form `closed_ball x (r x)` covering a proportion `1/(N+1)` of `s`, if
there are no satellite configurations with `N+1` points.
-/
lemma exist_finset_disjoint_balls_large_measure
  (μ : measure α) [is_finite_measure μ] {N : ℕ} {τ : ℝ}
  (hτ : 1 < τ) (hN : is_empty (satellite_config α N τ)) (s : set α)
  (r : α → ℝ) (rpos : ∀ x ∈ s, 0 < r x) (rle : ∀ x ∈ s, r x ≤ 1) :
  ∃ (t : finset α), (↑t ⊆ s) ∧ μ (s \ (⋃ (x ∈ t), closed_ball x (r x))) ≤ N/(N+1) * μ s
    ∧ (t : set α).pairwise_disjoint (λ x, closed_ball x (r x)) :=
begin
  -- exclude the trivial case where `μ s = 0`.
  rcases le_or_lt (μ s) 0 with hμs|hμs,
  { have : μ s = 0 := le_bot_iff.1 hμs,
    refine ⟨∅, by simp only [finset.coe_empty, empty_subset], _, _⟩,
    { simp only [this, diff_empty, Union_false, Union_empty, nonpos_iff_eq_zero, mul_zero] },
    { simp only [finset.coe_empty, pairwise_disjoint_empty], } },
  casesI is_empty_or_nonempty α,
  { simp only [eq_empty_of_is_empty s, measure_empty] at hμs,
    exact (lt_irrefl _ hμs).elim },
  have Npos : N ≠ 0,
  { unfreezingI { rintros rfl },
    inhabit α,
    exact (not_is_empty_of_nonempty _) hN },
  -- introduce a measurable superset `o` with the same measure, for measure computations
  obtain ⟨o, so, omeas, μo⟩ : ∃ (o : set α), s ⊆ o ∧ measurable_set o ∧ μ o = μ s :=
    exists_measurable_superset μ s,
  /- We will apply the topological Besicovitch theorem, giving `N` disjoint subfamilies of balls
  covering `s`. Among these, one of them covers a proportion at least `1/N` of `s`. A large
  enough finite subfamily will then cover a proportion at least `1/(N+1)`. -/
  let a : ball_package s α :=
  { c := λ x, x,
    r := λ x, r x,
    rpos := λ x, rpos x x.2,
    r_bound := 1,
    r_le := λ x, rle x x.2 },
  rcases exist_disjoint_covering_families hτ hN a with ⟨u, hu, hu'⟩,
  have u_count : ∀ i, (u i).countable,
  { assume i,
    refine (hu i).countable_of_nonempty_interior (λ j hj, _),
    have : (ball (j : α) (r j)).nonempty := nonempty_ball.2 (a.rpos _),
    exact this.mono ball_subset_interior_closed_ball },
  let v : fin N → set α := λ i, ⋃ (x : s) (hx : x ∈ u i), closed_ball x (r x),
  have : ∀ i, measurable_set (v i) :=
    λ i, measurable_set.bUnion (u_count i) (λ b hb, measurable_set_closed_ball),
  have A : s = ⋃ (i : fin N), s ∩ v i,
  { refine subset.antisymm _ (Union_subset (λ i, inter_subset_left _ _)),
    assume x hx,
    obtain ⟨i, y, hxy, h'⟩ : ∃ (i : fin N) (i_1 : ↥s) (i : i_1 ∈ u i), x ∈ ball ↑i_1 (r ↑i_1),
    { have : x ∈ range a.c, by simpa only [subtype.range_coe_subtype, set_of_mem_eq],
      simpa only [mem_Union] using hu' this },
    refine mem_Union.2 ⟨i, ⟨hx, _⟩⟩,
    simp only [v, exists_prop, mem_Union, set_coe.exists, exists_and_distrib_right, subtype.coe_mk],
    exact ⟨y, ⟨y.2, by simpa only [subtype.coe_eta]⟩, ball_subset_closed_ball h'⟩ },
  have S : ∑ (i : fin N), μ s / N ≤ ∑ i, μ (s ∩ v i) := calc
    ∑ (i : fin N), μ s / N = μ s : begin
      simp only [finset.card_fin, finset.sum_const, nsmul_eq_mul],
      rw ennreal.mul_div_cancel',
      { simp only [Npos, ne.def, nat.cast_eq_zero, not_false_iff] },
      { exact (ennreal.nat_ne_top _) }
    end
    ... ≤ ∑ i, μ (s ∩ v i) : by { conv_lhs { rw A }, apply measure_Union_fintype_le },
  -- choose an index `i` of a subfamily covering at least a proportion `1/N` of `s`.
  obtain ⟨i, -, hi⟩ : ∃ (i : fin N) (hi : i ∈ finset.univ), μ s / N ≤ μ (s ∩ v i),
  { apply ennreal.exists_le_of_sum_le _ S,
    exact ⟨⟨0, bot_lt_iff_ne_bot.2 Npos⟩, finset.mem_univ _⟩ },
  replace hi : μ s / (N + 1) < μ (s ∩ v i),
  { apply lt_of_lt_of_le _ hi,
    apply (ennreal.mul_lt_mul_left hμs.ne' (measure_lt_top μ s).ne).2,
    rw ennreal.inv_lt_inv,
    conv_lhs {rw ← add_zero (N : ℝ≥0∞) },
    exact ennreal.add_lt_add_left (ennreal.nat_ne_top N) zero_lt_one },
  have B : μ (o ∩ v i) = ∑' (x : u i), μ (o ∩ closed_ball x (r x)),
  { have : o ∩ v i = ⋃ (x : s) (hx : x ∈ u i), o ∩ closed_ball x (r x), by simp only [inter_Union],
    rw [this, measure_bUnion (u_count i)],
    { refl },
    { exact (hu i).mono (λ k, inter_subset_right _ _) },
    { exact λ b hb, omeas.inter measurable_set_closed_ball } },
  -- A large enough finite subfamily of `u i` will also cover a proportion `> 1/(N+1)` of `s`.
  -- Since `s` might not be measurable, we express this in terms of the measurable superset `o`.
  obtain ⟨w, hw⟩ : ∃ (w : finset (u i)),
    μ s / (N + 1) < ∑ (x : u i) in w, μ (o ∩ closed_ball (x : α) (r (x : α))),
  { have C : has_sum (λ (x : u i), μ (o ∩ closed_ball x (r x))) (μ (o ∩ v i)),
      by { rw B, exact ennreal.summable.has_sum },
    have : μ s / (N+1) < μ (o ∩ v i) :=
      hi.trans_le (measure_mono (inter_subset_inter_left _ so)),
    exact ((tendsto_order.1 C).1 _ this).exists },
  -- Bring back the finset `w i` of `↑(u i)` to a finset of `α`, and check that it works by design.
  refine ⟨finset.image (λ (x : u i), x) w, _, _, _⟩,
  -- show that the finset is included in `s`.
  { simp only [image_subset_iff, coe_coe, finset.coe_image],
    assume y hy,
    simp only [subtype.coe_prop, mem_preimage] },
  -- show that it covers a large enough proportion of `s`. For measure computations, we do not
  -- use `s` (which might not be measurable), but its measurable superset `o`. Since their measures
  -- are the same, this does not spoil the estimates
  { suffices H : μ (o \ ⋃ x ∈ w, closed_ball ↑x (r ↑x)) ≤ N/(N+1) * μ s,
      { rw [finset.set_bUnion_finset_image],
        exact le_trans (measure_mono (diff_subset_diff so (subset.refl _))) H },
    rw [← diff_inter_self_eq_diff,
      measure_diff_le_iff_le_add _ (inter_subset_right _ _) ((measure_lt_top μ _).ne)], swap,
    { apply measurable_set.inter _ omeas,
      haveI : encodable (u i) := (u_count i).to_encodable,
      exact measurable_set.Union
        (λ b, measurable_set.Union (λ hb, measurable_set_closed_ball)) },
    calc
    μ o = 1/(N+1) * μ s + N/(N+1) * μ s :
      by { rw [μo, ← add_mul, ennreal.div_add_div_same, add_comm, ennreal.div_self, one_mul]; simp }
    ... ≤ μ ((⋃ (x ∈ w), closed_ball ↑x (r ↑x)) ∩ o) + N/(N+1) * μ s : begin
      refine add_le_add _ le_rfl,
      rw [div_eq_mul_inv, one_mul, mul_comm, ← div_eq_mul_inv],
      apply hw.le.trans (le_of_eq _),
      rw [← finset.set_bUnion_coe, inter_comm _ o, inter_Union₂, finset.set_bUnion_coe,
          measure_bUnion_finset],
      { have : (w : set (u i)).pairwise_disjoint (λ (b : u i), closed_ball (b : α) (r (b : α))),
          by { assume k hk l hl hkl, exact hu i k.2 l.2 (subtype.coe_injective.ne hkl) },
        exact this.mono (λ k, inter_subset_right _ _) },
      { assume b hb,
        apply omeas.inter measurable_set_closed_ball }
    end },
  -- show that the balls are disjoint
  { assume k hk l hl hkl,
    obtain ⟨k', k'w, rfl⟩ : ∃ (k' : u i), k' ∈ w ∧ ↑↑k' = k,
      by simpa only [mem_image, finset.mem_coe, coe_coe, finset.coe_image] using hk,
    obtain ⟨l', l'w, rfl⟩ : ∃ (l' : u i), l' ∈ w ∧ ↑↑l' = l,
      by simpa only [mem_image, finset.mem_coe, coe_coe, finset.coe_image] using hl,
    have k'nel' : (k' : s) ≠ l',
      by { assume h, rw h at hkl, exact hkl rfl },
    exact hu i k'.2 l'.2 k'nel' }
end

variable [has_besicovitch_covering α]

/-- The measurable Besicovitch covering theorem. Assume that, for any `x` in a set `s`,
one is given a set of admissible closed balls centered at `x`, with arbitrarily small radii.
Then there exists a disjoint covering of almost all `s` by admissible closed balls centered at some
points of `s`.
This version requires that the underlying measure is finite, and that the space has the Besicovitch
covering property (which is satisfied for instance by normed real vector spaces). It expresses the
conclusion in a slightly awkward form (with a subset of `α × ℝ`) coming from the proof technique.
For a version assuming that the measure is sigma-finite,
see `exists_disjoint_closed_ball_covering_ae_aux`.
For a version giving the conclusion in a nicer form, see `exists_disjoint_closed_ball_covering_ae`.
-/
theorem exists_disjoint_closed_ball_covering_ae_of_finite_measure_aux
  (μ : measure α) [is_finite_measure μ]
  (f : α → set ℝ) (s : set α) (hf : ∀ x ∈ s, ∀ δ > 0, (f x ∩ Ioo 0 δ).nonempty) :
  ∃ (t : set (α × ℝ)), t.countable
    ∧ (∀ (p : α × ℝ), p ∈ t → p.1 ∈ s) ∧ (∀ (p : α × ℝ), p ∈ t → p.2 ∈ f p.1)
    ∧ μ (s \ (⋃ (p : α × ℝ) (hp : p ∈ t), closed_ball p.1 p.2)) = 0
    ∧ t.pairwise_disjoint (λ p, closed_ball p.1 p.2) :=
begin
  rcases has_besicovitch_covering.no_satellite_config α with ⟨N, τ, hτ, hN⟩,
  /- Introduce a property `P` on finsets saying that we have a nice disjoint covering of a
    subset of `s` by admissible balls. -/
  let P : finset (α × ℝ) → Prop := λ t,
    (t : set (α × ℝ)).pairwise_disjoint (λ p, closed_ball p.1 p.2) ∧
    (∀ (p : α × ℝ), p ∈ t → p.1 ∈ s) ∧ (∀ (p : α × ℝ), p ∈ t → p.2 ∈ f p.1),
  /- Given a finite good covering of a subset `s`, one can find a larger finite good covering,
  covering additionally a proportion at least `1/(N+1)` of leftover points. This follows from
  `exist_finset_disjoint_balls_large_measure` applied to balls not intersecting the initial
  covering. -/
  have : ∀ (t : finset (α × ℝ)), P t → ∃ (u : finset (α × ℝ)), t ⊆ u ∧ P u ∧
    μ (s \ (⋃ (p : α × ℝ) (hp : p ∈ u), closed_ball p.1 p.2)) ≤
      N/(N+1) * μ (s \ (⋃ (p : α × ℝ) (hp : p ∈ t), closed_ball p.1 p.2)),
  { assume t ht,
    set B := ⋃ (p : α × ℝ) (hp : p ∈ t), closed_ball p.1 p.2 with hB,
    have B_closed : is_closed B :=
      is_closed_bUnion (finset.finite_to_set _) (λ i hi, is_closed_ball),
    set s' := s \ B with hs',
    have : ∀ x ∈ s', ∃ r ∈ f x ∩ Ioo 0 1, disjoint B (closed_ball x r),
    { assume x hx,
      have xs : x ∈ s := ((mem_diff x).1 hx).1,
      rcases eq_empty_or_nonempty B with hB|hB,
      { have : (0 : ℝ) < 1 := zero_lt_one,
        rcases hf x xs 1 zero_lt_one with ⟨r, hr, h'r⟩,
        exact ⟨r, ⟨hr, h'r⟩, by simp only [hB, empty_disjoint]⟩ },
      { let R := inf_dist x B,
        have : 0 < min R 1 :=
          lt_min ((B_closed.not_mem_iff_inf_dist_pos hB).1 ((mem_diff x).1 hx).2) zero_lt_one,
        rcases hf x xs _ this with ⟨r, hr, h'r⟩,
        refine ⟨r, ⟨hr, ⟨h'r.1, h'r.2.trans_le (min_le_right _ _)⟩⟩, _⟩,
        rw disjoint.comm,
        exact disjoint_closed_ball_of_lt_inf_dist (h'r.2.trans_le (min_le_left _ _)) } },
    choose! r hr using this,
    obtain ⟨v, vs', hμv, hv⟩ : ∃ (v : finset α), ↑v ⊆ s'
      ∧ μ (s' \ ⋃ (x ∈ v), closed_ball x (r x)) ≤ N/(N+1) * μ s'
      ∧ (v : set α).pairwise_disjoint (λ (x : α), closed_ball x (r x)),
    { have rI : ∀ x ∈ s', r x ∈ Ioo (0 : ℝ) 1 := λ x hx, (hr x hx).1.2,
      exact exist_finset_disjoint_balls_large_measure μ hτ hN s' r (λ x hx, (rI x hx).1)
        (λ x hx, (rI x hx).2.le) },
    refine ⟨t ∪ (finset.image (λ x, (x, r x)) v), finset.subset_union_left _ _, ⟨_, _, _⟩, _⟩,
    { simp only [finset.coe_union, pairwise_disjoint_union, ht.1, true_and, finset.coe_image],
      split,
      { assume p hp q hq hpq,
        rcases (mem_image _ _ _).1 hp with ⟨p', p'v, rfl⟩,
        rcases (mem_image _ _ _).1 hq with ⟨q', q'v, rfl⟩,
        refine hv p'v q'v (λ hp'q', _),
        rw [hp'q'] at hpq,
        exact hpq rfl },
      { assume p hp q hq hpq,
        rcases (mem_image _ _ _).1 hq with ⟨q', q'v, rfl⟩,
        apply disjoint_of_subset_left _ (hr q' (vs' q'v)).2,
        rw [hB, ← finset.set_bUnion_coe],
        exact subset_bUnion_of_mem hp } },
    { assume p hp,
      rcases finset.mem_union.1 hp with h'p|h'p,
      { exact ht.2.1 p h'p },
      { rcases finset.mem_image.1 h'p with ⟨p', p'v, rfl⟩,
        exact ((mem_diff _).1 (vs' (finset.mem_coe.2 p'v))).1 } },
    { assume p hp,
      rcases finset.mem_union.1 hp with h'p|h'p,
      { exact ht.2.2 p h'p },
      { rcases finset.mem_image.1 h'p with ⟨p', p'v, rfl⟩,
        exact (hr p' (vs' p'v)).1.1 } },
    { convert hμv using 2,
      rw [finset.set_bUnion_union, ← diff_diff, finset.set_bUnion_finset_image] } },
  /- Define `F` associating to a finite good covering the above enlarged good covering, covering
  a proportion `1/(N+1)` of leftover points. Iterating `F`, one will get larger and larger good
  coverings, missing in the end only a measure-zero set. -/
  choose! F hF using this,
  let u := λ n, F^[n] ∅,
  have u_succ : ∀ (n : ℕ), u n.succ = F (u n) :=
    λ n, by simp only [u, function.comp_app, function.iterate_succ'],
  have Pu : ∀ n, P (u n),
  { assume n,
    induction n with n IH,
    { simp only [u, P, prod.forall, id.def, function.iterate_zero],
      simp only [finset.not_mem_empty, is_empty.forall_iff, finset.coe_empty, forall_2_true_iff,
        and_self, pairwise_disjoint_empty] },
    { rw u_succ,
      exact (hF (u n) IH).2.1 } },
  refine ⟨⋃ n, u n, countable_Union (λ n, (u n).countable_to_set), _, _, _, _⟩,
  { assume p hp,
    rcases mem_Union.1 hp with ⟨n, hn⟩,
    exact (Pu n).2.1 p (finset.mem_coe.1 hn) },
  { assume p hp,
    rcases mem_Union.1 hp with ⟨n, hn⟩,
    exact (Pu n).2.2 p (finset.mem_coe.1 hn) },
  { have A : ∀ n, μ (s \ ⋃ (p : α × ℝ) (hp : p ∈ ⋃ (n : ℕ), (u n : set (α × ℝ))),
                     closed_ball p.fst p.snd)
                ≤ μ (s \ ⋃ (p : α × ℝ) (hp : p ∈ u n), closed_ball p.fst p.snd),
    { assume n,
      apply measure_mono,
      apply diff_subset_diff (subset.refl _),
      exact bUnion_subset_bUnion_left (subset_Union (λ i, (u i : set (α × ℝ))) n) },
    have B : ∀ n, μ (s \ ⋃ (p : α × ℝ) (hp : p ∈ u n), closed_ball p.fst p.snd)
      ≤ (N/(N+1))^n * μ s,
    { assume n,
      induction n with n IH,
      { simp only [le_refl, diff_empty, one_mul, Union_false, Union_empty, pow_zero] },
      calc
        μ (s \ ⋃ (p : α × ℝ) (hp : p ∈ u n.succ), closed_ball p.fst p.snd)
            ≤ (N/(N+1)) * μ (s \ ⋃ (p : α × ℝ) (hp : p ∈ u n), closed_ball p.fst p.snd) :
              by { rw u_succ, exact (hF (u n) (Pu n)).2.2 }
        ... ≤ (N/(N+1))^n.succ * μ s :
          by { rw [pow_succ, mul_assoc], exact mul_le_mul_left' IH _ } },
    have C : tendsto (λ (n : ℕ), ((N : ℝ≥0∞)/(N+1))^n * μ s) at_top (𝓝 (0 * μ s)),
    { apply ennreal.tendsto.mul_const _ (or.inr (measure_lt_top μ s).ne),
      apply ennreal.tendsto_pow_at_top_nhds_0_of_lt_1,
      rw [ennreal.div_lt_iff, one_mul],
      { conv_lhs {rw ← add_zero (N : ℝ≥0∞) },
        exact ennreal.add_lt_add_left (ennreal.nat_ne_top N) zero_lt_one },
      { simp only [true_or, add_eq_zero_iff, ne.def, not_false_iff, one_ne_zero, and_false] },
      { simp only [ennreal.nat_ne_top, ne.def, not_false_iff, or_true] } },
    rw zero_mul at C,
    apply le_bot_iff.1,
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds C (λ n, (A n).trans (B n)) },
  { refine (pairwise_disjoint_Union _).2 (λ n, (Pu n).1),
    apply (monotone_nat_of_le_succ (λ n, _)).directed_le,
    rw u_succ,
    exact (hF (u n) (Pu n)).1 }
end

/-- The measurable Besicovitch covering theorem. Assume that, for any `x` in a set `s`,
one is given a set of admissible closed balls centered at `x`, with arbitrarily small radii.
Then there exists a disjoint covering of almost all `s` by admissible closed balls centered at some
points of `s`.
This version requires that the underlying measure is sigma-finite, and that the space has the
Besicovitch covering property (which is satisfied for instance by normed real vector spaces).
It expresses the conclusion in a slightly awkward form (with a subset of `α × ℝ`) coming from the
proof technique.
For a version giving the conclusion in a nicer form, see `exists_disjoint_closed_ball_covering_ae`.
-/
theorem exists_disjoint_closed_ball_covering_ae_aux (μ : measure α) [sigma_finite μ]
  (f : α → set ℝ) (s : set α) (hf : ∀ x ∈ s, ∀ δ > 0, (f x ∩ Ioo 0 δ).nonempty) :
  ∃ (t : set (α × ℝ)), t.countable
    ∧ (∀ (p : α × ℝ), p ∈ t → p.1 ∈ s) ∧ (∀ (p : α × ℝ), p ∈ t → p.2 ∈ f p.1)
    ∧ μ (s \ (⋃ (p : α × ℝ) (hp : p ∈ t), closed_ball p.1 p.2)) = 0
    ∧ t.pairwise_disjoint (λ p, closed_ball p.1 p.2) :=
begin
  /- This is deduced from the finite measure case, by using a finite measure with respect to which
  the initial sigma-finite measure is absolutely continuous. -/
  unfreezingI { rcases exists_absolutely_continuous_is_finite_measure μ with ⟨ν, hν, hμν⟩ },
  rcases exists_disjoint_closed_ball_covering_ae_of_finite_measure_aux ν f s hf
    with ⟨t, t_count, ts, tr, tν, tdisj⟩,
  exact ⟨t, t_count, ts, tr, hμν tν, tdisj⟩,
end

/-- The measurable Besicovitch covering theorem. Assume that, for any `x` in a set `s`,
one is given a set of admissible closed balls centered at `x`, with arbitrarily small radii.
Then there exists a disjoint covering of almost all `s` by admissible closed balls centered at some
points of `s`. We can even require that the radius at `x` is bounded by a given function `R x`.
(Take `R = 1` if you don't need this additional feature).
This version requires that the underlying measure is sigma-finite, and that the space has the
Besicovitch covering property (which is satisfied for instance by normed real vector spaces).
-/
theorem exists_disjoint_closed_ball_covering_ae (μ : measure α) [sigma_finite μ]
  (f : α → set ℝ) (s : set α) (hf : ∀ x ∈ s, ∀ δ > 0, (f x ∩ Ioo 0 δ).nonempty)
  (R : α → ℝ) (hR : ∀ x ∈ s, 0 < R x):
  ∃ (t : set α) (r : α → ℝ), t.countable ∧ t ⊆ s ∧ (∀ x ∈ t, r x ∈ f x ∩ Ioo 0 (R x))
    ∧ μ (s \ (⋃ (x ∈ t), closed_ball x (r x))) = 0
    ∧ t.pairwise_disjoint (λ x, closed_ball x (r x)) :=
begin
  let g := λ x, f x ∩ Ioo 0 (R x),
  have hg : ∀ x ∈ s, ∀ δ > 0, (g x ∩ Ioo 0 δ).nonempty,
  { assume x hx δ δpos,
    rcases hf x hx (min δ (R x)) (lt_min δpos (hR x hx)) with ⟨r, hr⟩,
    exact ⟨r, ⟨⟨hr.1, hr.2.1, hr.2.2.trans_le (min_le_right _ _)⟩,
      ⟨hr.2.1, hr.2.2.trans_le (min_le_left _ _)⟩⟩⟩ },
  rcases exists_disjoint_closed_ball_covering_ae_aux μ g s hg
    with ⟨v, v_count, vs, vg, μv, v_disj⟩,
  let t := prod.fst '' v,
  have : ∀ x ∈ t, ∃ (r : ℝ), (x, r) ∈ v,
  { assume x hx,
    rcases (mem_image _ _ _).1 hx with ⟨⟨p, q⟩, hp, rfl⟩,
    exact ⟨q, hp⟩ },
  choose! r hr using this,
  have im_t : (λ x, (x, r x)) '' t = v,
  { have I : ∀ (p : α × ℝ), p ∈ v → 0 ≤ p.2 :=
      λ p hp, (vg p hp).2.1.le,
    apply subset.antisymm,
    { simp only [image_subset_iff],
      rintros ⟨x, p⟩ hxp,
      simp only [mem_preimage],
      exact hr _ (mem_image_of_mem _ hxp) },
    { rintros ⟨x, p⟩ hxp,
      have hxrx : (x, r x) ∈ v := hr _ (mem_image_of_mem _ hxp),
      have : p = r x,
      { by_contra,
        have A : (x, p) ≠ (x, r x),
          by simpa only [true_and, prod.mk.inj_iff, eq_self_iff_true, ne.def] using h,
        have H := v_disj hxp hxrx A,
        contrapose H,
        rw not_disjoint_iff_nonempty_inter,
        refine ⟨x, by simp [I _ hxp, I _ hxrx]⟩ },
      rw this,
      apply mem_image_of_mem,
      exact mem_image_of_mem _ hxp } },
  refine ⟨t, r, v_count.image _, _, _, _, _⟩,
  { assume x hx,
    rcases (mem_image _ _ _).1 hx with ⟨⟨p, q⟩, hp, rfl⟩,
    exact vs _ hp },
  { assume x hx,
    rcases (mem_image _ _ _).1 hx with ⟨⟨p, q⟩, hp, rfl⟩,
    exact vg _ (hr _ hx) },
  { have : (⋃ (x : α) (H : x ∈ t), closed_ball x (r x)) =
      (⋃ (p : α × ℝ) (H : p ∈ (λ x, (x, r x)) '' t), closed_ball p.1 p.2),
        by conv_rhs { rw bUnion_image },
    rw [this, im_t],
    exact μv },
  { have A : inj_on (λ x : α, (x, r x)) t,
      by simp only [inj_on, prod.mk.inj_iff, implies_true_iff, eq_self_iff_true] {contextual := tt},
    rwa [← im_t, A.pairwise_disjoint_image] at v_disj }
end

/-- In a space with the Besicovitch property, any set `s` can be covered with balls whose measures
add up to at most `μ s + ε`, for any positive `ε`. This works even if one restricts the set of
allowed radii around a point `x` to a set `f x` which accumulates at `0`. -/
theorem exists_closed_ball_covering_tsum_measure_le
  (μ : measure α) [sigma_finite μ] [measure.outer_regular μ]
  {ε : ℝ≥0∞} (hε : ε ≠ 0) (f : α → set ℝ) (s : set α)
  (hf : ∀ x ∈ s, ∀ δ > 0, (f x ∩ Ioo 0 δ).nonempty) :
  ∃ (t : set α) (r : α → ℝ), t.countable ∧ t ⊆ s ∧ (∀ x ∈ t, r x ∈ f x)
    ∧ s ⊆ (⋃ (x ∈ t), closed_ball x (r x))
    ∧ ∑' (x : t), μ (closed_ball x (r x)) ≤ μ s + ε  :=
begin
  /- For the proof, first cover almost all `s` with disjoint balls thanks to the usual Besicovitch
  theorem. Taking the balls included in a well-chosen open neighborhood `u` of `s`, one may
  ensure that their measures add at most to `μ s + ε / 2`. Let `s'` be the remaining set, of measure
  `0`. Applying the other version of Besicovitch, one may cover it with at most `N` disjoint
  subfamilies. Making sure that they are all included in a neighborhood `v` of `s'` of measure at
  most `ε / (2 N)`, the sum of their measures is at most `ε / 2`, completing the proof. -/
  obtain ⟨u, su, u_open, μu⟩ : ∃ U ⊇ s, is_open U ∧ μ U ≤ μ s + ε / 2 :=
    set.exists_is_open_le_add _ _ (by simpa only [or_false, ne.def, ennreal.div_zero_iff,
      ennreal.one_ne_top, ennreal.bit0_eq_top_iff] using hε),
  have : ∀ x ∈ s, ∃ R > 0, ball x R ⊆ u :=
    λ x hx, metric.mem_nhds_iff.1 (u_open.mem_nhds (su hx)),
  choose! R hR using this,
  obtain ⟨t0, r0, t0_count, t0s, hr0, μt0, t0_disj⟩ :
    ∃ (t0 : set α) (r0 : α → ℝ), t0.countable ∧ t0 ⊆ s ∧ (∀ x ∈ t0, r0 x ∈ f x ∩ Ioo 0 (R x))
      ∧ μ (s \ (⋃ (x ∈ t0), closed_ball x (r0 x))) = 0
      ∧ t0.pairwise_disjoint (λ x, closed_ball x (r0 x)) :=
        exists_disjoint_closed_ball_covering_ae μ f s hf R (λ x hx, (hR x hx).1),
  -- we have constructed an almost everywhere covering of `s` by disjoint balls. Let `s'` be the
  -- remaining set.
  let s' := s \ (⋃ (x ∈ t0), closed_ball x (r0 x)),
  have s's : s' ⊆ s := diff_subset _ _,
  obtain ⟨N, τ, hτ, H⟩ : ∃ N τ, 1 < τ ∧ is_empty (besicovitch.satellite_config α N τ) :=
    has_besicovitch_covering.no_satellite_config α,
  obtain ⟨v, s'v, v_open, μv⟩ : ∃ v ⊇ s', is_open v ∧ μ v ≤ μ s' + (ε / 2) / N :=
    set.exists_is_open_le_add _ _
      (by simp only [hε, ennreal.nat_ne_top, with_top.mul_eq_top_iff, ne.def, ennreal.div_zero_iff,
        ennreal.one_ne_top, not_false_iff, and_false, false_and, or_self, ennreal.bit0_eq_top_iff]),
  have : ∀ x ∈ s', ∃ r1 ∈ (f x ∩ Ioo (0 : ℝ) 1), closed_ball x r1 ⊆ v,
  { assume x hx,
    rcases metric.mem_nhds_iff.1 (v_open.mem_nhds (s'v hx)) with ⟨r, rpos, hr⟩,
    rcases hf x (s's hx) (min r 1) (lt_min rpos zero_lt_one) with ⟨R', hR'⟩,
    exact ⟨R', ⟨hR'.1, hR'.2.1, hR'.2.2.trans_le (min_le_right _ _)⟩,
      subset.trans (closed_ball_subset_ball (hR'.2.2.trans_le (min_le_left _ _))) hr⟩, },
  choose! r1 hr1 using this,
  let q : ball_package s' α :=
  { c := λ x, x,
    r := λ x, r1 x,
    rpos := λ x, (hr1 x.1 x.2).1.2.1,
    r_bound := 1,
    r_le := λ x, (hr1 x.1 x.2).1.2.2.le },
  -- by Besicovitch, we cover `s'` with at most `N` families of disjoint balls, all included in
  -- a suitable neighborhood `v` of `s'`.
  obtain ⟨S, S_disj, hS⟩ : ∃ S : fin N → set s',
    (∀ (i : fin N), (S i).pairwise_disjoint (λ j, closed_ball (q.c j) (q.r j))) ∧
      (range q.c ⊆ ⋃ (i : fin N), ⋃ (j ∈ S i), ball (q.c j) (q.r j)) :=
    exist_disjoint_covering_families hτ H q,
  have S_count : ∀ i, (S i).countable,
  { assume i,
    apply (S_disj i).countable_of_nonempty_interior (λ j hj, _),
    have : (ball (j : α) (r1 j)).nonempty := nonempty_ball.2 (q.rpos _),
    exact this.mono ball_subset_interior_closed_ball },
  let r := λ x, if x ∈ s' then r1 x else r0 x,
  have r_t0 : ∀ x ∈ t0, r x = r0 x,
  { assume x hx,
    have : ¬ (x ∈ s'),
    { simp only [not_exists, exists_prop, mem_Union, mem_closed_ball, not_and, not_lt,
                  not_le, mem_diff, not_forall],
      assume h'x,
      refine ⟨x, hx, _⟩,
      rw dist_self,
      exact (hr0 x hx).2.1.le },
    simp only [r, if_neg this] },
  -- the desired covering set is given by the union of the families constructed in the first and
  -- second steps.
  refine ⟨t0 ∪ (⋃ (i : fin N), (coe : s' → α) '' (S i)), r, _, _, _, _, _⟩,
  -- it remains to check that they have the desired properties
  { exact t0_count.union (countable_Union (λ i, (S_count i).image _)) },
  { simp only [t0s, true_and, union_subset_iff, image_subset_iff, Union_subset_iff],
    assume i x hx,
    exact s's x.2 },
  { assume x hx,
    cases hx,
    { rw r_t0 x hx,
      exact (hr0 _ hx).1 },
    { have h'x : x ∈ s',
      { simp only [mem_Union, mem_image] at hx,
        rcases hx with ⟨i, y, ySi, rfl⟩,
        exact y.2 },
      simp only [r, if_pos h'x, (hr1 x h'x).1.1] } },
  { assume x hx,
    by_cases h'x : x ∈ s',
    { obtain ⟨i, y, ySi, xy⟩ : ∃ (i : fin N) (y : ↥s') (ySi : y ∈ S i), x ∈ ball (y : α) (r1 y),
      { have A : x ∈ range q.c, by simpa only [not_exists, exists_prop, mem_Union, mem_closed_ball,
          not_and, not_le, mem_set_of_eq, subtype.range_coe_subtype, mem_diff] using h'x,
        simpa only [mem_Union, mem_image] using hS A },
      refine mem_Union₂.2 ⟨y, or.inr _, _⟩,
      { simp only [mem_Union, mem_image],
        exact ⟨i, y, ySi, rfl⟩ },
      { have : (y : α) ∈ s' := y.2,
        simp only [r, if_pos this],
        exact ball_subset_closed_ball xy } },
    { obtain ⟨y, yt0, hxy⟩ : ∃ (y : α), y ∈ t0 ∧ x ∈ closed_ball y (r0 y),
        by simpa [hx, -mem_closed_ball] using h'x,
      refine mem_Union₂.2 ⟨y, or.inl yt0, _⟩,
      rwa r_t0 _ yt0 } },
  -- the only nontrivial property is the measure control, which we check now
  { -- the sets in the first step have measure at most `μ s + ε / 2`
    have A : ∑' (x : t0), μ (closed_ball x (r x)) ≤ μ s + ε / 2 := calc
      ∑' (x : t0), μ (closed_ball x (r x))
      = ∑' (x : t0), μ (closed_ball x (r0 x)) :
        by { congr' 1, ext x, rw r_t0 x x.2 }
      ... = μ (⋃ (x : t0), closed_ball x (r0 x)) :
        begin
          haveI : encodable t0 := t0_count.to_encodable,
          rw measure_Union,
          { exact (pairwise_subtype_iff_pairwise_set _ _).2 t0_disj },
          { exact λ i, measurable_set_closed_ball }
        end
      ... ≤ μ u :
        begin
          apply measure_mono,
          simp only [set_coe.forall, subtype.coe_mk, Union_subset_iff],
          assume x hx,
          apply subset.trans (closed_ball_subset_ball (hr0 x hx).2.2) (hR x (t0s hx)).2,
        end
      ... ≤ μ s + ε / 2 : μu,
    -- each subfamily in the second step has measure at most `ε / (2 N)`.
    have B : ∀ (i : fin N),
      ∑' (x : (coe : s' → α) '' (S i)), μ (closed_ball x (r x)) ≤ (ε / 2) / N := λ i, calc
      ∑' (x : (coe : s' → α) '' (S i)), μ (closed_ball x (r x)) =
            ∑' (x : S i), μ (closed_ball x (r x)) :
        begin
          have : inj_on (coe : s' → α) (S i) := subtype.coe_injective.inj_on _,
          let F : S i ≃ (coe : s' → α) '' (S i) := this.bij_on_image.equiv _,
          exact (F.tsum_eq (λ x, μ (closed_ball x (r x)))).symm,
        end
      ... = ∑' (x : S i), μ (closed_ball x (r1 x)) :
        by { congr' 1, ext x, have : (x : α) ∈ s' := x.1.2, simp only [r, if_pos this] }
      ... = μ (⋃ (x : S i), closed_ball x (r1 x)) :
        begin
          haveI : encodable (S i) := (S_count i).to_encodable,
          rw measure_Union,
          { exact (pairwise_subtype_iff_pairwise_set _ _).2 (S_disj i) },
          { exact λ i, measurable_set_closed_ball }
        end
      ... ≤ μ v :
        begin
          apply measure_mono,
          simp only [set_coe.forall, subtype.coe_mk, Union_subset_iff],
          assume x xs' xSi,
          exact (hr1 x xs').2,
        end
      ... ≤ (ε / 2) / N : by { have : μ s' = 0 := μt0, rwa [this, zero_add] at μv },
    -- add up all these to prove the desired estimate
    calc ∑' (x : (t0 ∪ ⋃ (i : fin N), (coe : s' → α) '' S i)), μ (closed_ball x (r x))
        ≤ ∑' (x : t0), μ (closed_ball x (r x))
          + ∑' (x : ⋃ (i : fin N), (coe : s' → α) '' S i), μ (closed_ball x (r x)) :
            ennreal.tsum_union_le (λ x, μ (closed_ball x (r x))) _ _
    ... ≤ ∑' (x : t0), μ (closed_ball x (r x))
          + ∑ (i : fin N), ∑' (x : (coe : s' → α) '' S i), μ (closed_ball x (r x)) :
            add_le_add le_rfl (ennreal.tsum_Union_le (λ x, μ (closed_ball x (r x))) _)
    ... ≤ (μ s + ε / 2) + ∑ (i : fin N), (ε / 2) / N :
      begin
        refine add_le_add A _,
        refine finset.sum_le_sum _,
        assume i hi,
        exact B i
      end
    ... ≤ (μ s + ε / 2) + ε / 2 :
      begin
        refine add_le_add le_rfl _,
        simp only [finset.card_fin, finset.sum_const, nsmul_eq_mul, ennreal.mul_div_le],
      end
    ... = μ s + ε : by rw [add_assoc, ennreal.add_halves] }
end

/-! ### Consequences on differentiation of measures -/

/-- In a space with the Besicovitch covering property, the set of closed balls with positive radius
forms a Vitali family. This is essentially a restatement of the measurable Besicovitch theorem. -/
protected def vitali_family (μ : measure α) [sigma_finite μ] :
  vitali_family μ :=
{ sets_at := λ x, (λ (r : ℝ), closed_ball x r) '' (Ioi (0 : ℝ)),
  measurable_set' := begin
    assume x y hy,
    obtain ⟨r, rpos, rfl⟩ : ∃ (r : ℝ), 0 < r ∧ closed_ball x r = y,
      by simpa only [mem_image, mem_Ioi] using hy,
    exact is_closed_ball.measurable_set
  end,
  nonempty_interior := begin
    assume x y hy,
    obtain ⟨r, rpos, rfl⟩ : ∃ (r : ℝ), 0 < r ∧ closed_ball x r = y,
      by simpa only [mem_image, mem_Ioi] using hy,
    simp only [nonempty.mono ball_subset_interior_closed_ball, rpos, nonempty_ball],
  end,
  nontrivial := λ x ε εpos, ⟨closed_ball x ε, mem_image_of_mem _ εpos, subset.refl _⟩,
  covering := begin
    assume s f fsubset ffine,
    let g : α → set ℝ := λ x, {r | 0 < r ∧ closed_ball x r ∈ f x},
    have A : ∀ x ∈ s, ∀ δ > 0, (g x ∩ Ioo 0 δ).nonempty,
    { assume x xs δ δpos,
      obtain ⟨t, tf, ht⟩ : ∃ (t : set α) (H : t ∈ f x), t ⊆ closed_ball x (δ/2) :=
        ffine x xs (δ/2) (half_pos δpos),
      obtain ⟨r, rpos, rfl⟩ : ∃ (r : ℝ), 0 < r ∧ closed_ball x r = t,
        by simpa using fsubset x xs tf,
      rcases le_total r (δ/2) with H|H,
      { exact ⟨r, ⟨rpos, tf⟩, ⟨rpos, H.trans_lt (half_lt_self δpos)⟩⟩ },
      { have : closed_ball x r = closed_ball x (δ/2) :=
          subset.antisymm ht (closed_ball_subset_closed_ball H),
        rw this at tf,
        refine ⟨δ/2, ⟨half_pos δpos, tf⟩, ⟨half_pos δpos, half_lt_self δpos⟩⟩ } },
    obtain ⟨t, r, t_count, ts, tg, μt, tdisj⟩ : ∃ (t : set α) (r : α → ℝ), t.countable
      ∧ t ⊆ s ∧ (∀ x ∈ t, r x ∈ g x ∩ Ioo 0 1)
      ∧ μ (s \ (⋃ (x ∈ t), closed_ball x (r x))) = 0
      ∧ t.pairwise_disjoint (λ x, closed_ball x (r x)) :=
        exists_disjoint_closed_ball_covering_ae μ g s A (λ _, 1) (λ _ _, zero_lt_one),
    let F : α → α × set α := λ x, (x, closed_ball x (r x)),
    refine ⟨F '' t, _, _, _, _⟩,
    { rintros - ⟨x, hx, rfl⟩, exact ts hx },
    { rintros p ⟨x, hx, rfl⟩ q ⟨y, hy, rfl⟩ hxy,
      exact tdisj hx hy (ne_of_apply_ne F hxy) },
    { rintros - ⟨x, hx, rfl⟩, exact (tg x hx).1.2 },
    { rwa bUnion_image }
  end }

/-- The main feature of the Besicovitch Vitali family is that its filter at a point `x` corresponds
to convergence along closed balls. We record one of the two implications here, which will enable us
to deduce specific statements on differentiation of measures in this context from the general
versions. -/
lemma tendsto_filter_at (μ : measure α) [sigma_finite μ] (x : α) :
  tendsto (λ r, closed_ball x r) (𝓝[>] 0) ((besicovitch.vitali_family μ).filter_at x) :=
begin
  assume s hs,
  simp only [mem_map],
  obtain ⟨ε, εpos, hε⟩ : ∃ (ε : ℝ) (H : ε > 0), ∀ (a : set α),
    a ∈ (besicovitch.vitali_family μ).sets_at x → a ⊆ closed_ball x ε → a ∈ s :=
      (vitali_family.mem_filter_at_iff _).1 hs,
  have : Ioc (0 : ℝ) ε ∈ 𝓝[>] (0 : ℝ) := Ioc_mem_nhds_within_Ioi ⟨le_rfl, εpos⟩,
  filter_upwards [this] with _ hr,
  apply hε,
  { exact mem_image_of_mem _ hr.1 },
  { exact closed_ball_subset_closed_ball hr.2 }
end

variables [metric_space β] [measurable_space β] [borel_space β] [second_countable_topology β]
  [has_besicovitch_covering β]

/-- In a space with the Besicovitch covering property, the ratio of the measure of balls converges
almost surely to to the Radon-Nikodym derivative. -/
lemma ae_tendsto_rn_deriv
  (ρ μ : measure β) [is_locally_finite_measure μ] [is_locally_finite_measure ρ] :
  ∀ᵐ x ∂μ, tendsto (λ r, ρ (closed_ball x r) / μ (closed_ball x r))
    (𝓝[>] 0) (𝓝 (ρ.rn_deriv μ x)) :=
begin
  filter_upwards [vitali_family.ae_tendsto_rn_deriv (besicovitch.vitali_family μ) ρ] with x hx,
  exact hx.comp (tendsto_filter_at μ x)
end

/-- Given a measurable set `s`, then `μ (s ∩ closed_ball x r) / μ (closed_ball x r)` converges when
`r` tends to `0`, for almost every `x`. The limit is `1` for `x ∈ s` and `0` for `x ∉ s`.
This shows that almost every point of `s` is a Lebesgue density point for `s`.
A version for non-measurable sets holds, but it only gives the first conclusion,
see `ae_tendsto_measure_inter_div`. -/
lemma ae_tendsto_measure_inter_div_of_measurable_set
  (μ : measure β) [is_locally_finite_measure μ] {s : set β} (hs : measurable_set s) :
  ∀ᵐ x ∂μ, tendsto (λ r, μ (s ∩ closed_ball x r) / μ (closed_ball x r))
    (𝓝[>] 0) (𝓝 (s.indicator 1 x)) :=
begin
  filter_upwards [vitali_family.ae_tendsto_measure_inter_div_of_measurable_set
    (besicovitch.vitali_family μ) hs],
  assume x hx,
  exact hx.comp (tendsto_filter_at μ x)
end

/-- Given an arbitrary set `s`, then `μ (s ∩ closed_ball x r) / μ (closed_ball x r)` converges
to `1` when `r` tends to `0`, for almost every `x` in `s`.
This shows that almost every point of `s` is a Lebesgue density point for `s`.
A stronger version holds for measurable sets, see `ae_tendsto_measure_inter_div_of_measurable_set`.

See also `is_unif_loc_doubling_measure.ae_tendsto_measure_inter_div`. -/
lemma ae_tendsto_measure_inter_div (μ : measure β) [is_locally_finite_measure μ] (s : set β) :
  ∀ᵐ x ∂(μ.restrict s), tendsto (λ r, μ (s ∩ (closed_ball x r)) / μ (closed_ball x r))
    (𝓝[>] 0) (𝓝 1) :=
by filter_upwards [vitali_family.ae_tendsto_measure_inter_div (besicovitch.vitali_family μ)]
    with x hx using hx.comp (tendsto_filter_at μ x)

end besicovitch

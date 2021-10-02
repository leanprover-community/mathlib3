/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.metric_space.basic
import set_theory.cardinal_ordinal

/-!
# Besicovitch covering theorem

The topological Besicovitch covering theorem ensures that, in a nice metric space, there exists a
number `N` such that, from any family of balls with bounded radii, one can extract `N` families,
each made of disjoint balls, covering together all the centers of the initial family.

By "nice metric space", we mean a technical property stated as follows: there exists no satellite
configuration of `N+1` points (with a given parameter `τ > 1`). Such a configuration is a family
of `N + 1` balls, where the first `N` balls all intersect the last one, but none of them contains
the center of another one and their radii are controlled. This property is for instance
satisfied by finite-dimensional real vector spaces.

In this file, we prove the topological Besicovitch covering theorem,
in `besicovitch.exist_disjoint_covering_families`.

## Main definitions and results

* `satellite_config α N τ` is the type of all satellite configurations of `N+1` points
  in the metric space `α`, with parameter `τ`.
* `has_besicovitch_covering` is a class recording that there exist `N` and `τ > 1` such that
  there is no satellite configuration of `N+1` points with parameter `τ`.
* `exist_disjoint_covering_families` is the topological Besicovitch covering theorem: from any
  family of balls one can extract finitely many disjoint subfamilies covering the same set.

## Implementation

We choose balls in a greedy way. First choose a ball with maximal radius (or rather, since there
is no guarantee the maximal radius is realized, a ball with radius within a factor `τ` of the
supremum). Then, remove all balls whose center is covered by the first ball, and choose among the
remaining ones a ball with radius close to maximum. Go on forever until there is no available
center (this is a transfinite induction in general).

Then define inductively a coloring of the balls. A ball will be of color `i` if it intersects
already chosen balls of color `0`, ..., `i - 1`, but none of color `i`. In this way, balls of the
same color form a disjoint family, and the space is covered by the families of the different colors.

The nontrivial part is to show that at most `N` colors are used. If one needs `N+1` colors, consider
the first time this happens. Then the corresponding ball intersects `N` balls of the different
colors. Moreover, the inductive construction ensures that the radii of all the balls are controlled:
they form a satellite configuration with `N+1` balls (essentially by definition of satellite
configurations). Since we assume that there are no such configurations, this is a contradiction.

## Todo

Deduce the measurable Besicovitch theorem: consider a set `s` of finite measure, and for each `c`
in `s` a set of balls centered at `c` of arbitrarily small radius. Then one can choose among
all these balls a disjoint family covering almost all `s`.

While the value of `N` is relevant for the precise statement of the topological Besicovitch theorem,
it becomes irrelevant for the measurable one. Therefore, this statement will be expressed using the
`Prop`-valued typeclass `has_besicovitch_covering` (which is currently introduced, but not used).
-/

noncomputable theory

universe u

open metric set filter fin
open_locale topological_space

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
@[nolint has_inhabited_instance]
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
(no_satellite_config : ∃ (N : ℕ) (τ : ℝ), 1 < τ ∧ is_empty (besicovitch.satellite_config α N τ))

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
  apply Union_subset_Union2,
  assume r,
  exact ⟨⟨r, r.2.trans_le hij⟩, subset.refl _⟩,
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
  wlog x_le_y : x ≤ y := le_total x y using [x y, y x],
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
      wlog G_le : G a ≤ G b := le_total (G a) (G b) using [a b, b a] tactic.skip,
      { have G_lt : G a < G b,
        { rcases G_le.lt_or_eq with H|H, { exact H },
          have A : (a : ℕ) ≠ b := fin.coe_injective.ne a_ne_b,
          rw [← color_G a (nat.lt_succ_iff.1 a.2), ← color_G b (nat.lt_succ_iff.1 b.2), H] at A,
          exact (A rfl).elim },
        exact or.inl (Gab a b G_lt) },
      { assume a_ne_b,
        rw or_comm,
        exact this a_ne_b.symm }
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
    (∀ (i : fin N), (s i).pairwise_on (disjoint on (λ j, closed_ball (q.c j) (q.r j)))) ∧
      (range q.c ⊆ ⋃ (i : fin N), ⋃ (j ∈ s i), ball (q.c j) (q.r j)) :=
begin
  -- first exclude the trivial case where `β` is empty (we need non-emptiness for the transfinite
  -- induction, to be able to choose garbage when there is no point left).
  casesI is_empty_or_nonempty β,
  { refine ⟨λ i, ∅, λ i, by simp, _⟩,
    rw [← image_univ, eq_empty_of_is_empty (univ : set β)],
    simp },
  -- Now, assume `β` is nonempty.
  let p : tau_package β α := { τ := τ, one_lt_tau := hτ, .. q },
  -- we use for `s i` the balls of color `i`.
  let s := λ (i : fin N),
    ⋃ (k : ordinal.{u}) (hk : k < p.last_step) (h'k : p.color k = i), ({p.index k} : set β),
  refine ⟨s, λ i, _, _⟩,
  { -- show that balls of the same color are disjoint
    simp only [function.on_fun],
    assume x hx y hy x_ne_y,
    obtain ⟨jx, jx_lt, jxi, rfl⟩ :
      ∃ (jx : ordinal), jx < p.last_step ∧ p.color jx = i ∧ x = p.index jx,
        by simpa only [exists_prop, mem_Union, mem_singleton_iff] using hx,
    obtain ⟨jy, jy_lt, jyi, rfl⟩ :
      ∃ (jy : ordinal), jy < p.last_step ∧ p.color jy = i ∧ y = p.index jy,
        by simpa only [exists_prop, mem_Union, mem_singleton_iff] using hy,
    wlog jxy : jx ≤ jy := le_total jx jy using [jx jy, jy jx] tactic.skip,
    swap,
    { assume h1 h2 h3 h4 h5 h6 h7,
      rw disjoint.comm,
      exact this h4 h5 h6 h1 h2 h3 h7.symm },
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
    exact ⟨⟨p.color a, p.color_lt ha.1 hN⟩, p.index a, ⟨a, rfl, ha.1, rfl⟩, ha.2⟩ }
end

end besicovitch

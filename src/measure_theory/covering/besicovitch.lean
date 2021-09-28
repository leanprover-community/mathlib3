/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.besicovitch_vector_space
/-!
# Besicovitch covering lemma

We prove the Besicovith covering theorem
-/

universe u


namespace metric

lemma nonempty_closed_ball_inter_closed_ball
  {α : Type*} [pseudo_metric_space α] {x y : α} {rx ry : ℝ}
  (h : (closed_ball x rx ∩ closed_ball y ry).nonempty) :
  dist x y ≤ rx + ry :=
begin
  rcases h with ⟨z, hz⟩,
  calc dist x y ≤ dist z x + dist z y : dist_triangle_left _ _ _
  ... ≤ rx + ry : add_le_add hz.1 hz.2
end

end metric

-- a mettre à côté de not_disjoint_iff
lemma not_disjoint_iff_nonempty_inter {α : Type*} {s t : set α} :
  ¬disjoint s t ↔ (s ∩ t).nonempty :=
by simp [set.not_disjoint_iff, set.nonempty_def]

section

lemma {v} up_injective {X : Type u} :
  function.injective (ulift.up.{v} : X → ulift X) :=
begin
  rintros x1 x2 h, cc,
end

lemma not_injective_of_ordinal {X : Type u} (f : ordinal.{u} → X) :
  ¬ function.injective f :=
begin
  let g : ordinal.{u} → ulift.{u+1} X := λ o, ulift.up (f o),
  suffices : ¬ function.injective g,
  { intro hf, exact this (up_injective.comp hf) },
  intro hg,
  replace hg := cardinal.mk_le_of_injective hg,
  rw ← cardinal.lift_mk at hg,
  replace hg := lt_of_le_of_lt hg (cardinal.lift_lt_univ _),
  contrapose! hg,
  rw cardinal.univ_id
end

end

open metric set finite_dimensional measure_theory filter

open_locale ennreal topological_space

noncomputable theory


namespace besicovitch

/-- A Besicovitch package is a family of balls in a metric space with positive bounded radii,
together with enough data to proceed with the Besicovitch greedy algorithm -/
@[nolint has_inhabited_instance]
structure package (β : Type*) (α : Type*) [metric_space α] :=
(c : β → α)
(r : β → ℝ)
(rpos : ∀ b, 0 < r b)
(r_bound : ℝ)
(r_le : ∀ b, r b ≤ r_bound)
(τ : ℝ)
(one_lt_tau : 1 < τ)

variables {α : Type*} [metric_space α] {β : Type u} [nonempty β]
(p : package β α)
include p

namespace package

/-- Define inductively centers of large balls that are not contained in the union of already
chosen balls. -/
noncomputable def f : ordinal.{u} → β
| i :=
    -- `Z` is the set of points that are covered by already constructed balls
    let Z := ⋃ (j : {j // j < i}), ball (p.c (f j)) (p.r (f j)),
    -- `R` is the supremum of the radii of balls with centers not in `Z`
    R := supr (λ b : {b : β // p.c b ∉ Z}, p.r b) in
    -- return an index `b` for which the center `c b` is not in `Z`, and the radius is at
    -- least `R / τ`, if such an index exists (and garbage otherwise).
    classical.epsilon (λ b : β, p.c b ∉ Z ∧ R ≤ p.τ * p.r b)
using_well_founded {dec_tac := `[exact j.2]}

/-- The set of points that are covered by the union of balls selected at steps `< i`. -/
def Union_up_to (i : ordinal.{u}) : set α :=
⋃ (j : {j // j < i}), ball (p.c (p.f j)) (p.r (p.f j))

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

/-- Group the balls into disjoint families -/
noncomputable def index : ordinal.{u} → ℕ
| i := let A : set ℕ := ⋃ (j : {j // j < i})
          (hj : (closed_ball (p.c (p.f j)) (p.r (p.f j))
            ∩ closed_ball (p.c (p.f i)) (p.r (p.f i))).nonempty), {index j} in
       Inf (univ \ A)
using_well_founded {dec_tac := `[exact j.2]}

/-- `p.last_step` is the first ordinal where the construction stops making sense. We will only
use ordinals before this step. -/
def last_step : ordinal.{u} :=
Inf {i | ¬ ∃ (b : β), p.c b ∉ p.Union_up_to i ∧ p.R i ≤ p.τ * p.r b}

lemma last_step_nonempty :
  {i | ¬ ∃ (b : β), p.c b ∉ p.Union_up_to i ∧ p.R i ≤ p.τ * p.r b}.nonempty :=
begin
  by_contra,
  suffices H : function.injective p.f, by exact not_injective_of_ordinal p.f H,
  assume x y hxy,
  wlog x_le_y : x ≤ y := le_total x y using [x y, y x],
  rcases eq_or_lt_of_le x_le_y with rfl|H, { refl },
  simp only [nonempty_def, not_exists, exists_prop, not_and, not_lt, not_le, mem_set_of_eq,
    not_forall] at h,
  specialize h y,
  have A : p.c (p.f y) ∉ p.Union_up_to y,
  { have : p.f y = classical.epsilon (λ b : β, p.c b ∉ p.Union_up_to y ∧ p.R y ≤ p.τ * p.r b),
      by { rw [package.f], refl },
    rw this,
    exact (classical.epsilon_spec h).1 },
  simp only [Union_up_to, not_exists, exists_prop, mem_Union, mem_closed_ball, not_and, not_le,
              subtype.exists, subtype.coe_mk] at A,
  specialize A x H,
  simp [hxy] at A,
  exact (lt_irrefl _ ((p.rpos (p.f y)).trans_le A)).elim
end

lemma mem_Union_up_to_last_step (x : β) : p.c x ∈ p.Union_up_to p.last_step :=
begin
  have A : ∀ (z : β), p.c z ∈ p.Union_up_to p.last_step ∨ p.τ * p.r z < p.R p.last_step,
  { have : p.last_step ∈ {i | ¬ ∃ (b : β), p.c b ∉ p.Union_up_to i ∧ p.R i ≤ p.τ * p.r b} :=
      Inf_mem p.last_step_nonempty,
    simpa only [not_exists, mem_set_of_eq, not_and_distrib, not_le, not_not_mem] },
  by_contra,
  rcases A x with H|H, { exact h H },
  have Rpos : 0 < p.R p.last_step,
  { apply lt_trans (mul_pos (zero_lt_one.trans p.one_lt_tau) (p.rpos _)) H },
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
    have := (div_le_iff' (zero_lt_one.trans p.one_lt_tau)).1 hy2.le,
    exact lt_irrefl _ (Hy.trans_le this) }
end

/-- If there are no configurations of satellites with `N+1` points, one never uses more than `N`
distinct families in the Besicovitch inductive construction. -/
lemma index_lt {i : ordinal.{u}} (hi : i < p.last_step)
  {N : ℕ} (hN : is_empty (satellite_config α N p.τ)) :
  p.index i < N :=
begin
  /- By contradiction, consider the first ordinal `i` for which one would have `p.index i = N`.
  Choose for each `k < N` a ball with index `k` that intersects the ball at index `i` (there is such
  a ball, otherwise one would have used the index `k` and not `N`). Then this family of `N+1` balls
  forms a satellite configuration, which is forbidden by the assumption `p.no_satellite_config`. -/
  induction i using ordinal.induction with i IH,
  let A : set ℕ := ⋃ (j : {j // j < i})
         (hj : (closed_ball (p.c (p.f j)) (p.r (p.f j))
            ∩ closed_ball (p.c (p.f i)) (p.r (p.f i))).nonempty), {p.index j},
  have index_i : p.index i = Inf (univ \ A), by rw [index],
  rw index_i,
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
    ∧ (closed_ball (p.c (p.f j)) (p.r (p.f j)) ∩ closed_ball (p.c (p.f i)) (p.r (p.f i))).nonempty
    ∧ k = p.index j,
  { assume k hk,
    rw ← Inf_eq_N at hk,
    have : k ∈ A,
      by simpa only [true_and, mem_univ, not_not, mem_diff] using nat.not_mem_of_lt_Inf hk,
    simp at this,
    simpa only [exists_prop, mem_Union, mem_singleton_iff, mem_closed_ball, subtype.exists,
      subtype.coe_mk] },
  choose! g hg using this,
  -- Choose for each `k < N` an ordinal `G k < i`  giving a ball of index `k` intersecting
  -- the last ball.
  let G : ℕ → ordinal := λ n, if n = N then i else g n,
  have index_G : ∀ n, n ≤ N → p.index (G n) = n,
  { assume n hn,
    unfreezingI { rcases hn.eq_or_lt with rfl|H },
    { simp only [G], simp only [index_i, Inf_eq_N, if_true, eq_self_iff_true] },
    { simp only [G], simp only [H.ne, (hg n H).right.right.symm, if_false] } },
  have G_lt_last : ∀ n, n ≤ N → G n < p.last_step,
  { assume n hn,
    unfreezingI { rcases hn.eq_or_lt with rfl|H },
    { simp only [G], simp only [hi, if_true, eq_self_iff_true], },
    { simp only [G], simp only [H.ne, (hg n H).left.trans hi, if_false] } },
  have fGn : ∀ n, n ≤ N →
    p.c (p.f (G n)) ∉ p.Union_up_to (G n) ∧ p.R (G n) ≤ p.τ * p.r (p.f (G n)),
  { assume n hn,
    have: p.f (G n) = classical.epsilon
      (λ t, p.c t ∉ p.Union_up_to (G n) ∧ p.R (G n) ≤ p.τ * p.r t), by { rw f, refl },
    rw this,
    have : ∃ t, p.c t ∉ p.Union_up_to (G n) ∧ p.R (G n) ≤ p.τ * p.r t,
      by simpa only [not_exists, exists_prop, not_and, not_lt, not_le, mem_set_of_eq,
        not_forall] using not_mem_of_lt_cInf (G_lt_last n hn) (order_bot.bdd_below _),
    exact classical.epsilon_spec this },
  -- the balls with indices `G k` satisfy the characteristic property of satellite configurations.
  have Gab : ∀ (a b : fin (nat.succ N)), G a < G b →
    p.r (p.f (G a)) ≤ dist (p.c (p.f (G a))) (p.c (p.f (G b)))
      ∧ p.r (p.f (G b)) ≤ p.τ * p.r (p.f (G a)),
   { assume a b G_lt,
    have ha : (a : ℕ) ≤ N := nat.lt_succ_iff.1 a.2,
    have hb : (b : ℕ) ≤ N := nat.lt_succ_iff.1 b.2,
    split,
    { have := (fGn b hb).1,
      simp only [Union_up_to, not_exists, exists_prop, mem_Union, mem_closed_ball, not_and,
        not_le, subtype.exists, subtype.coe_mk] at this,
      simpa only [dist_comm, mem_ball, not_lt] using this (G a) G_lt },
    { apply le_trans _ (fGn a ha).2,
      have B : p.c (p.f (G b)) ∉ p.Union_up_to (G a),
      { assume H, exact (fGn b hb).1 (p.monotone_Union_up_to G_lt.le H) },
      let b' : {t // p.c t ∉ p.Union_up_to (G a)} := ⟨p.f (G b), B⟩,
      apply @le_csupr _ _ _ (λ t : {t // p.c t ∉ p.Union_up_to (G a)}, p.r t) _ b',
      refine ⟨p.r_bound, λ t ht, _⟩,
      simp only [exists_prop, mem_range, subtype.exists, subtype.coe_mk] at ht,
      rcases ht with ⟨u, hu⟩,
      rw ← hu.2,
      exact p.r_le _ } },
  -- therefore, one may use it to construct a satellite configuration with `N+1` points
  let sc : satellite_config α N p.τ :=
  { c := λ k, p.c (p.f (G k)),
    r := λ k, p.r (p.f (G k)),
    rpos := λ k, p.rpos (p.f (G k)),
    h := begin
      assume a b a_ne_b,
      wlog G_le : G a ≤ G b := le_total (G a) (G b) using [a b, b a] tactic.skip,
      { have G_lt : G a < G b,
        { rcases G_le.lt_or_eq with H|H, { exact H },
          have A : (a : ℕ) ≠ b := fin.coe_injective.ne a_ne_b,
          rw [← index_G a (nat.lt_succ_iff.1 a.2), ← index_G b (nat.lt_succ_iff.1 b.2), H] at A,
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
      convert nonempty_closed_ball_inter_closed_ball (hg _ I).2.1,
    end },
  -- this is a contradiction
  exact (hN.false : _) sc
end

/-- The Besicovitch covering theorem: there exist finitely many families of disjoint balls covering
all the centers in a package. More specifically, one can use `N` families if there are no
satellite configurations with `N+1` points. -/
theorem exist_disjoint_covering_families {N : ℕ} (hN : is_empty (satellite_config α N p.τ)) :
  ∃ s : fin N → set β,
    (∀ (i : fin N), (s i).pairwise_on (disjoint on (λ j, closed_ball (p.c j) (p.r j)))) ∧
      (range p.c ⊆ ⋃ (i : fin N), ⋃ (j ∈ s i), ball (p.c j) (p.r j)) :=
begin
  let s := λ (i : fin N),
    ⋃ (k : ordinal.{u}) (hk : k < p.last_step) (h'k : p.index k = i), ({p.f k} : set β),
  refine ⟨s, λ i, _, _⟩,
  { simp only [function.on_fun],
    assume x hx y hy x_ne_y,
    obtain ⟨jx, jx_lt, jxi, rfl⟩ : ∃ (jx : ordinal), jx < p.last_step ∧ p.index jx = i ∧ x = p.f jx,
      by simpa only [exists_prop, mem_Union, mem_singleton_iff] using hx,
    obtain ⟨jy, jy_lt, jyi, rfl⟩ : ∃ (jy : ordinal), jy < p.last_step ∧ p.index jy = i ∧ y = p.f jy,
      by simpa only [exists_prop, mem_Union, mem_singleton_iff] using hy,
    wlog jxy : jx ≤ jy := le_total jx jy using [jx jy, jy jx] tactic.skip,
    swap,
    { assume h1 h2 h3 h4 h5 h6 h7,
      rw disjoint.comm,
      exact this h4 h5 h6 h1 h2 h3 h7.symm },
    replace jxy : jx < jy,
      by { rcases lt_or_eq_of_le jxy with H|rfl, { exact H }, { exact (x_ne_y rfl).elim } },
    let A : set ℕ := ⋃ (j : {j // j < jy})
         (hj : (closed_ball (p.c (p.f j)) (p.r (p.f j))
            ∩ closed_ball (p.c (p.f jy)) (p.r (p.f jy))).nonempty), {p.index j},
    have index_j : p.index jy = Inf (univ \ A), by rw [index],
    have : p.index jy ∈ univ \ A,
    { rw index_j,
      apply Inf_mem,
      refine ⟨N, _⟩,
      simp only [not_exists, true_and, exists_prop, mem_Union, mem_singleton_iff, not_and, mem_univ,
        mem_diff, subtype.exists, subtype.coe_mk],
      assume k hk H,
      exact (p.index_lt (hk.trans jy_lt) hN).ne' },
    simp only [not_exists, true_and, exists_prop, mem_Union, mem_singleton_iff, not_and, mem_univ,
      mem_diff, subtype.exists, subtype.coe_mk] at this,
    specialize this jx jxy,
    contrapose! this,
    simpa only [jxi, jyi, and_true, eq_self_iff_true, ← not_disjoint_iff_nonempty_inter] },
  { refine range_subset_iff.2 (λ b, _),
    obtain ⟨a, ha⟩ : ∃ (a : ordinal), a < p.last_step ∧ dist (p.c b) (p.c (p.f a)) < p.r (p.f a),
      by simpa only [Union_up_to, exists_prop, mem_Union, mem_ball, subtype.exists, subtype.coe_mk]
        using p.mem_Union_up_to_last_step b,
    simp only [exists_prop, mem_Union, mem_ball, mem_singleton_iff, bUnion_and', exists_eq_left,
      Union_exists, exists_and_distrib_left],
    exact ⟨⟨p.index a, p.index_lt ha.1 hN⟩, p.f a, ⟨a, rfl, ha.1, rfl⟩, ha.2⟩ }
end

end package

end besicovitch

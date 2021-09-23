/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.metric_space.basic
import tactic.induction
import analysis.normed_space.basic
import analysis.normed_space.finite_dimension
import measure_theory.measure.haar_lebesgue

/-!
# Besicovitch covering lemma

We prove the Besicovitch covering lemma.

-/

universe u
open metric set finite_dimensional measure_theory filter

open_locale ennreal topological_space

lemma ball_subset_ball' {E : Type*} [normed_group E]
  (x y : E) (rx ry : ℝ) (h : rx + dist x y ≤ ry) :
  ball x rx ⊆ ball y ry :=
begin
  assume z hz,
  calc dist z y ≤ dist z x + dist x y : dist_triangle _ _ _
  ... < rx + dist x y : add_lt_add_right hz _
  ... ≤ ry : h
end

namespace ennreal

@[simp, norm_cast] lemma to_nnreal_nat (n : ℕ) : (n : ℝ≥0∞).to_nnreal = n :=
by conv_lhs { rw [← ennreal.coe_nat n, ennreal.to_nnreal_coe] }

@[simp, norm_cast] lemma to_real_nat (n : ℕ) : (n : ℝ≥0∞).to_real = n :=
by conv_lhs { rw [← ennreal.of_real_coe_nat n, ennreal.to_real_of_real (nat.cast_nonneg _)] }

end ennreal

namespace fin

lemma exists_injective_of_le_card_fintype
  {α : Type*} [fintype α] {k : ℕ} (hk : k ≤ fintype.card α) :
  ∃ (f : fin k → α), function.injective f :=
⟨_, (fintype.equiv_fin α).symm.injective.comp (fin.cast_le hk).injective⟩

lemma exists_injective_of_le_card_finset {α : Type*} {s : finset α} {k : ℕ} (hk : k ≤ s.card) :
  ∃ (f : fin k → α), function.injective f ∧ range f ⊆ s :=
begin
  rw ← fintype.card_coe at hk,
  rcases fin.exists_injective_of_le_card_fintype hk with ⟨f, hf⟩,
  exact ⟨(λ x, (f x : α)), function.injective.comp subtype.coe_injective hf,
    by simp [range_subset_iff]⟩
end

end fin

noncomputable theory

namespace besicovitch

def multiplicity (E : Type*) [normed_group E] :=
Sup {N | ∃ s : finset E, s.card = N ∧ (∀ c ∈ s, ∥c∥ ≤ 2) ∧ (∀ c ∈ s, ∀ d ∈ s, c ≠ d → 1 ≤ ∥c - d∥)}

variables {E : Type*} [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]

lemma besicovitch.card_le_of_separated
  (s : finset E) (hs : ∀ c ∈ s, ∥c∥ ≤ 2) (h : ∀ (c ∈ s) (d ∈ s), c ≠ d → 1 ≤ ∥c - d∥) :
  s.card ≤ 5 ^ (finrank ℝ E) :=
begin
  /- We consider balls of radius `1/2` around the points in `s`. They are disjoint, and all
  contained in the ball of radius `5/2`. A volume argument gives `s.card * (1/2)^dim ≤ (5/2)^dim`,
  i.e., `s.card ≤ 5^dim`. -/
  letI : measurable_space E := borel E,
  letI : borel_space E := ⟨rfl⟩,
  let μ : measure E := measure.add_haar,
  let δ : ℝ := (1 : ℝ)/2,
  let ρ : ℝ := (5 : ℝ)/2,
  have ρpos : 0 < ρ := by norm_num [ρ],
  set A := ⋃ (c ∈ s), ball (c : E) δ with hA,
  have D : set.pairwise_on (s : set E) (disjoint on (λ c, ball (c : E) δ)),
  { rintros c hc d hd hcd,
    apply ball_disjoint_ball,
    rw dist_eq_norm,
    convert h c hc d hd hcd,
    norm_num },
  have A_subset : A ⊆ ball (0 : E) ρ,
  { refine bUnion_subset (λ x hx, _),
    apply ball_subset_ball',
    calc δ + dist x 0 ≤ δ + 2 : by { rw dist_zero_right, exact add_le_add le_rfl (hs x hx) }
    ... = 5 / 2 : by norm_num [δ] },
  have I : (s.card : ℝ≥0∞) * ennreal.of_real (δ ^ (finrank ℝ E)) * μ (ball 0 1) ≤
    ennreal.of_real (ρ ^ (finrank ℝ E)) * μ (ball 0 1) := calc
  (s.card : ℝ≥0∞) * ennreal.of_real (δ ^ (finrank ℝ E)) * μ (ball 0 1) = μ A :
    begin
      rw [hA, measure_bUnion_finset D (λ c hc, measurable_set_ball)],
      have I : 0 < δ, by norm_num [δ],
      simp only [μ.add_haar_ball_of_pos _ I, one_div, one_pow, finset.sum_const,
        nsmul_eq_mul, div_pow, mul_assoc]
    end
  ... ≤ μ (ball (0 : E) ρ) : measure_mono A_subset
  ... = ennreal.of_real (ρ ^ (finrank ℝ E)) * μ (ball 0 1) :
    by simp only [μ.add_haar_ball_of_pos _ ρpos],
  have J : (s.card : ℝ≥0∞) * ennreal.of_real (δ ^ (finrank ℝ E))
    ≤ ennreal.of_real (ρ ^ (finrank ℝ E)) :=
      (ennreal.mul_le_mul_right (μ.add_haar_ball_pos _ zero_lt_one).ne'
        (μ.add_haar_ball_lt_top _ _).ne).1 I,
  have K : (s.card : ℝ) ≤ (5 : ℝ) ^ finrank ℝ E,
    by simpa [ennreal.to_real_mul, div_eq_mul_inv] using
      ennreal.to_real_le_of_le_of_real (pow_nonneg ρpos.le _) J,
  exact_mod_cast K,
end

lemma multiplicity_le : multiplicity E ≤ 5 ^ (finrank ℝ E) :=
begin
  apply cSup_le,
  { refine ⟨0, ⟨∅, by simp⟩⟩ },
  { rintros _ ⟨s, ⟨rfl, h⟩⟩,
    exact besicovitch.card_le_of_separated s h.1 h.2 }
end

lemma card_le_multiplicity
  {s : finset E} (hs : ∀ c ∈ s, ∥c∥ ≤ 2) (h's : ∀ (c ∈ s) (d ∈ s), c ≠ d → 1 ≤ ∥c - d∥) :
  s.card ≤ multiplicity E :=
begin
  apply le_cSup,
  { refine ⟨5 ^ (finrank ℝ E), _⟩,
    rintros _ ⟨s, ⟨rfl, h⟩⟩,
    exact besicovitch.card_le_of_separated s h.1 h.2 },
  { simp only [mem_set_of_eq, ne.def],
    exact ⟨s, rfl, hs, h's⟩ }
end

variable (E)
lemma exists_good_τ : ∃ (τ : ℝ), 1 < τ ∧ ∀ (s : finset E), (∀ c ∈ s, ∥c∥ ≤ 2 * τ) →
  (∀ (c ∈ s) (d ∈ s), c ≠ d → τ⁻¹ ≤ ∥c - d∥) → s.card ≤ multiplicity E :=
begin
  classical,
  by_contradiction h,
  push_neg at h,
  set N := multiplicity E + 1 with hN,
  have : ∀ (τ : ℝ), 1 < τ → ∃ f : fin N → E, (∀ (i : fin N), ∥f i∥ ≤ 2 * τ)
    ∧ (∀ i j, i ≠ j → τ⁻¹ ≤ ∥f i - f j∥),
  { assume τ hτ,
    rcases h τ hτ with ⟨s, hs, h's, s_card⟩,
    obtain ⟨f, f_inj, hfs⟩ : ∃ (f : fin N → E), function.injective f ∧ range f ⊆ ↑s :=
      fin.exists_injective_of_le_card_finset s_card,
    simp only [range_subset_iff, finset.mem_coe] at hfs,
    refine ⟨f, λ i, hs _ (hfs i), λ i j hij, h's _ (hfs i) _ (hfs j) (f_inj.ne hij)⟩ },
  choose! F hF using this,
  have : ∃ f : fin N → E, (∀ (i : fin N), ∥f i∥ ≤ 2) ∧ (∀ i j, i ≠ j → 1 ≤ ∥f i - f j∥),
  { obtain ⟨u, u_mono, one_lt_u, hu⟩ : ∃ (u : ℕ → ℝ), (∀ (m n : ℕ), m < n → u n < u m)
      ∧ (∀ (n : ℕ), 1 < u n) ∧ filter.tendsto u filter.at_top (𝓝 1) :=
        exists_seq_strict_antimono_tendsto (1 : ℝ),
    have A : ∀ n, F (u n) ∈ closed_ball (0 : fin N → E) (2 * u 0),
    { assume n,
      have : 0 ≤ 2 * u 0 :=
        mul_nonneg zero_le_two (zero_le_one.trans (one_lt_u 0).le),
      simp only [pi_norm_le_iff this, mem_closed_ball, dist_zero_right],
      assume i,
      apply ((hF (u n) (one_lt_u n)).1 i).trans,
      refine (mul_le_mul_left zero_lt_two).2 _,
      cases n, { exact le_rfl }, { exact (u_mono 0 n.succ (nat.succ_pos _)).le } },
    obtain ⟨f, -, φ, φ_mono, hf⟩ : ∃ (f ∈ closed_ball (0 : fin N → E) (2 * u 0)) (φ : ℕ → ℕ),
      strict_mono φ ∧ tendsto ((F ∘ u) ∘ φ) at_top (𝓝 f) :=
        is_compact.tendsto_subseq (proper_space.compact_ball _ _) A,
    refine ⟨f, λ i, _, λ i j hij, _⟩,
    { have A : tendsto (λ n, ∥F (u (φ n)) i∥) at_top (𝓝 (∥f i∥)) := (hf.apply i).norm,
      have B : tendsto (λ n, 2 * u (φ n)) at_top (𝓝 (2 * 1)) :=
        (hu.comp φ_mono.tendsto_at_top).const_mul _,
      rw mul_one at B,
      exact le_of_tendsto_of_tendsto' A B (λ n, (hF (u (φ n)) (one_lt_u _)).1 i) },
    { have A : tendsto (λ n, ∥F (u (φ n)) i - F (u (φ n)) j∥) at_top (𝓝 (∥f i - f j∥)) :=
        ((hf.apply i).sub (hf.apply j)).norm,
      have B : tendsto (λ n, (u (φ n))⁻¹) at_top (𝓝 (1⁻¹)) :=
        (hu.comp φ_mono.tendsto_at_top).inv' one_ne_zero,
      rw inv_one at B,
      exact le_of_tendsto_of_tendsto' B A (λ n, (hF (u (φ n)) (one_lt_u _)).2 i j hij) } },
  rcases this with ⟨f, hf, h'f⟩,
  have finj : function.injective f,
  { assume i j hij,
    by_contra,
    have : 1 ≤ ∥f i - f j∥ := h'f i j h,
    simp only [hij, norm_zero, sub_self] at this,
    exact lt_irrefl _ (this.trans_lt zero_lt_one) },
  let s := finset.image f finset.univ,
  have s_card : s.card = N,
    by { rw finset.card_image_of_injective _ finj, exact finset.card_fin N },
  have hs : ∀ c ∈ s, ∥c∥ ≤ 2,
    by simp only [hf, forall_apply_eq_imp_iff', forall_const, forall_exists_index, finset.mem_univ,
                  finset.mem_image],
  have h's : ∀ (c ∈ s) (d ∈ s), c ≠ d → 1 ≤ ∥c - d∥,
  { simp only [s, forall_apply_eq_imp_iff', forall_exists_index, finset.mem_univ, finset.mem_image,
      ne.def, exists_true_left, forall_apply_eq_imp_iff', forall_true_left],
    assume i j hij,
    have : i ≠ j := λ h, by { rw h at hij, exact hij rfl },
    exact h'f i j this },
  have : s.card ≤ multiplicity E := card_le_multiplicity hs h's,
  rw [s_card, hN] at this,
  exact lt_irrefl _ ((nat.lt_succ_self (multiplicity E)).trans_le this),
end

def good_τ : ℝ := classical.some (exists_good_τ E)

lemma one_lt_good_τ : 1 < good_τ E := (classical.some_spec (exists_good_τ E)).1

lemma card_le_multiplicity_τ {s : finset E} (hs : ∀ c ∈ s, ∥c∥ ≤ 2 * good_τ E)
  (h's : ∀ (c ∈ s) (d ∈ s), c ≠ d → (good_τ E)⁻¹ ≤ ∥c - d∥) :
  s.card ≤ multiplicity E :=
(classical.some_spec (exists_good_τ E)).2 s hs h's

#exit


lemma zoug {E : Type*} [normed_group E] [normed_space ℝ E] {N : ℕ} (c : ℕ → E) (r : ℕ → ℝ)
  (δ : ℝ) (τ : ℝ)
  (hcN : c N = 0)
  (hrN : r N = 1)
  (hcr : ∀ i < N, ∥c i∥ ≤ r i + r 1)
  (hcr' : ∀ i < N, r i ≤ ∥c i∥)
  (hc : ∀ (i ≤ N) (j ≤ N),
    (r i ≤ ∥c j - c i∥ ∧ r j ≤ τ * r i) ∨ (r j ≤ ∥c i - c j∥ ∧ r i ≤ τ * r j)) :
  ∃ (c' : ℕ → E), (∀ n ≤ N, ∥c' n∥ ≤ 2) ∧ (∀ i ≤ N, ∀ j ≤ N, i ≠ j → 1 - δ ≤ ∥c' i - c' j∥) :=
begin
  let c' : ℕ → E := λ i, if ∥c i∥ ≤ 2 then c i else (2 / ∥c i∥) • c i,
  have norm_c'_le : ∀ i, ∥c' i∥ ≤ 2,
  { assume i,
    simp only [c'],
    split_ifs, { exact h },
    by_cases hi : ∥c i∥ = 0;
    field_simp [norm_smul, hi] },
  refine ⟨c', λ n hn, norm_c'_le n, _⟩,
  assume i hi j hj hij,
  by_cases H : ∥c i∥ ≤ 2 ∧ ∥c j∥ ≤ 2,
  { simp only [c'],
    simp [c', H.1, H.2],


  } ,
end



#exit


namespace besicovitch

structure package (β : Type*) (α : Type*) [metric_space α] :=
(c : β → α)
(r : β → ℝ)
(r_pos : ∀ b, 0 < r b)
(r_bound : ℝ)
(r_le : ∀ b, r b ≤ r_bound)
(τ : ℝ)
(one_lt_tau : 1 < τ)
(N : ℕ)
(no_satellite : ∀ (c' : ℕ → α) (r' : ℕ → ℝ)
  (h_inter : ∀ i < N, (closed_ball (c' i) (r' i) ∩ closed_ball (c' N) (r' N)).nonempty)
  (h : ∀ i ≤ N, ∀ j ≤ N, i ≠ j → (r' i < dist (c' i) (c' j) ∧ r' j ≤ τ * r' i) ∨
    (r' j < dist (c' j) (c' i) ∧ r' i ≤ τ * r' j)),
  false)


variables {α : Type*} [metric_space α] {β : Type u} [nonempty β]
(p : package β α)
include p

namespace package

/-- Define inductively centers of large balls that are not contained in the union of already
chosen balls. -/
noncomputable def f : ordinal.{u} → β
| i :=
    -- `Z` is the set of points that are covered by already constructed balls
    let Z := ⋃ (j : {j // j < i}), closed_ball (p.c (f j)) (p.r (f j)),
    -- `R` is the supremum of the radii of balls with centers not in `Z`
    R := supr (λ b : {b : β // p.c b ∉ Z}, p.r b) in
    -- return an index `b` for which the center `c b` is not in `Z`, and the radius is at
    -- least `R / τ`, if such an index exists (and garbage otherwise).
    classical.epsilon (λ b : β, p.c b ∉ Z ∧ R ≤ p.τ * p.r b)
using_well_founded {dec_tac := `[exact j.2]}

/-- The set of points that are covered by the union of balls selected at steps `< i`. -/
def Union_up_to (i : ordinal.{u}) : set α :=
⋃ (j : {j // j < i}), closed_ball (p.c (p.f j)) (p.r (p.f j))

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

lemma index_lt (i : ordinal.{u}) (hi : i < p.last_step) :
  p.index i < p.N :=
begin
  induction i using ordinal.induction with i IH,
  let A : set ℕ := ⋃ (j : {j // j < i})
         (hj : (closed_ball (p.c (p.f j)) (p.r (p.f j))
            ∩ closed_ball (p.c (p.f i)) (p.r (p.f i))).nonempty), {p.index j},
  have index_i : p.index i = Inf (univ \ A), by rw [index],
  rw index_i,
  have N_mem : p.N ∈ univ \ A,
  { simp only [not_exists, true_and, exists_prop, mem_Union, mem_singleton_iff, mem_closed_ball,
      not_and, mem_univ, mem_diff, subtype.exists, subtype.coe_mk],
    assume j ji hj,
    exact (IH j ji (ji.trans hi)).ne' },
  suffices : Inf (univ \ A) ≠ p.N,
  { rcases (cInf_le (order_bot.bdd_below (univ \ A)) N_mem).lt_or_eq with H|H,
    { exact H },
    { exact (this H).elim } },
  assume Inf_eq_N,
  have : ∀ k, k < p.N → ∃ j, j < i
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
  let G : ℕ → ordinal := λ n, if n = p.N then i else g n,
  have index_G : ∀ n, n ≤ p.N → p.index (G n) = n,
  { assume n hn,
    rcases hn.eq_or_lt with rfl|H,
    { simp only [G], simp only [index_i, Inf_eq_N, if_true, eq_self_iff_true] },
    { simp only [G], simp only [H.ne, (hg n H).right.right.symm, if_false] } },
  have G_lt_last : ∀ n, n ≤ p.N → G n < p.last_step,
  { assume n hn,
    rcases hn.eq_or_lt with rfl|H,
    { simp only [G], simp only [hi, if_true, eq_self_iff_true], },
    { simp only [G], simp only [H.ne, (hg n H).left.trans hi, if_false] } },
  have fGn : ∀ n, n ≤ p.N →
    p.c (p.f (G n)) ∉ p.Union_up_to (G n) ∧ p.R (G n) ≤ p.τ * p.r (p.f (G n)),
  { assume n hn,
    have: p.f (G n) = classical.epsilon
      (λ t, p.c t ∉ p.Union_up_to (G n) ∧ p.R (G n) ≤ p.τ * p.r t), by { rw f, refl },
    rw this,
    have : ∃ t, p.c t ∉ p.Union_up_to (G n) ∧ p.R (G n) ≤ p.τ * p.r t,
      by simpa only [not_exists, exists_prop, not_and, not_lt, not_le, mem_set_of_eq,
        not_forall] using not_mem_of_lt_cInf (G_lt_last n hn) (order_bot.bdd_below _),
    exact classical.epsilon_spec this },
  apply p.no_satellite (p.c ∘ p.f ∘ G) (p.r ∘ p.f ∘ G),
  { assume a ha,
    have A : G a = g a, by simp only [ha.ne, forall_false_left, ite_eq_right_iff],
    have B : G p.N = i,
      by simp only [forall_false_left, eq_self_iff_true, not_true, ite_eq_left_iff],
    simp only [A, B, function.comp_app],
    exact (hg a ha).2.1 },
  { assume a ha b hb a_ne_b,
    wlog G_le : G a ≤ G b := le_total (G a) (G b) using [a b, b a] tactic.skip,
    { have G_lt : G a < G b,
      { rcases G_le.lt_or_eq with H|H, { exact H },
        rw [← index_G a ha, ← index_G b hb, H] at a_ne_b,
        exact (a_ne_b rfl).elim },
      left,
      split,
      { have := (fGn b hb).1,
        simp only [Union_up_to, not_exists, exists_prop, mem_Union, mem_closed_ball, not_and,
          not_le, subtype.exists, subtype.coe_mk] at this,
        simpa only [dist_comm] using this (G a) G_lt },
      { apply le_trans _ (fGn a ha).2,
        have B : p.c (p.f (G b)) ∉ p.Union_up_to (G a),
        { assume H, exact (fGn b hb).1 (p.monotone_Union_up_to G_le H) },
        let b' : {t // p.c t ∉ p.Union_up_to (G a)} := ⟨p.f (G b), B⟩,
        apply @le_csupr _ _ _ (λ t : {t // p.c t ∉ p.Union_up_to (G a)}, p.r t) _ b',
        refine ⟨p.r_bound, λ t ht, _⟩,
        simp only [exists_prop, mem_range, subtype.exists, subtype.coe_mk] at ht,
        rcases ht with ⟨u, hu⟩,
        rw ← hu.2,
        exact p.r_le _ } },
    { assume ha hb a_ne_b,
      rw or_comm,
      exact this hb ha a_ne_b.symm } },
end

end package

end besicovitch

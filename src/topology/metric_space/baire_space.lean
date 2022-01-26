/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.metric_space.basic


/-!
# Study of the Baire space

-/

noncomputable theory
open_locale classical
open topological_space

@[derive topological_space]
def baire_space : Type := ℕ → ℕ

namespace baire_space

lemma exists_index_ne_of_ne {x y : baire_space} (h : x ≠ y) :
  ∃ n, x n ≠ y n :=
begin
  contrapose! h,
  ext1 n,
  exact h n
end

@[irreducible, pp_nodot] def first_diff (x y : baire_space) : ℕ :=
if h : x ≠ y then nat.find (exists_index_ne_of_ne h) else 0

lemma apply_first_diff_ne {x y : baire_space} (h : x ≠ y) :
  x (first_diff x y) ≠ y (first_diff x y) :=
begin
  rw first_diff,
  split_ifs,
  exact nat.find_spec (exists_index_ne_of_ne h),
end

lemma apply_eq_of_lt_first_diff {x y : baire_space} {n : ℕ} (hn : n < first_diff x y) :
  x n = y n :=
begin
  rw first_diff at hn,
  split_ifs at hn,
  { convert nat.find_min (exists_index_ne_of_ne h) hn,
    simp },
  { exact (not_lt_zero' hn).elim }
end

lemma first_diff_comm (x y : baire_space) :
  first_diff x y = first_diff y x :=
begin
  rcases eq_or_ne x y with rfl|hxy, { refl },
  rcases lt_trichotomy (first_diff x y) (first_diff y x) with h|h|h,
  { exact (apply_first_diff_ne hxy (apply_eq_of_lt_first_diff h).symm).elim },
  { exact h },
  { exact (apply_first_diff_ne hxy.symm (apply_eq_of_lt_first_diff h).symm).elim }
end

lemma min_first_diff_le (x y z : baire_space) (h : x ≠ z) :
  min (first_diff x y) (first_diff y z) ≤ first_diff x z :=
begin
  by_contra' H,
  have : x (first_diff x z) = z (first_diff x z), from calc
    x (first_diff x z) = y (first_diff x z) :
      apply_eq_of_lt_first_diff (H.trans_le (min_le_left _ _))
    ... = z ((first_diff x z)) : apply_eq_of_lt_first_diff (H.trans_le (min_le_right _ _)),
  exact (apply_first_diff_ne h this).elim,
end

@[pp_nodot] protected def dist (x y : baire_space) : ℝ :=
if h : x ≠ y then (1/2 : ℝ) ^ (first_diff x y) else 0

lemma dist_eq_of_ne {x y : baire_space} (h : x ≠ y) :
  baire_space.dist x y = (1/2 : ℝ) ^ (first_diff x y) :=
by simp [baire_space.dist, h]

lemma dist_self (x : baire_space) : baire_space.dist x x = 0 :=
by simp [baire_space.dist]

lemma dist_comm (x y : baire_space) : baire_space.dist x y = baire_space.dist y x :=
by simp [baire_space.dist, @eq_comm _ x y, first_diff_comm]

lemma dist_nonneg (x y : baire_space) : 0 ≤ baire_space.dist x y :=
begin
  rcases eq_or_ne x y with rfl|h,
  { simp [baire_space.dist] },
  { simp [baire_space.dist, h] }
end

lemma dist_triangle_nonarch (x y z : baire_space) :
  baire_space.dist x z ≤ max (baire_space.dist x y) (baire_space.dist y z) :=
begin
  rcases eq_or_ne x z with rfl|hxz,
  { simp [dist_self x, dist_nonneg] },
  rcases eq_or_ne x y with rfl|hxy,
  { simp },
  rcases eq_or_ne y z with rfl|hyz,
  { simp },
  simp only [dist_eq_of_ne, hxz, hxy, hyz, inv_le_inv, one_div, inv_pow₀, zero_lt_bit0, pow_pos,
    ne.def, not_false_iff, le_max_iff, zero_lt_one, pow_le_pow_iff, one_lt_two,
    min_le_iff.1 (min_first_diff_le x y z hxz)],
end

lemma apply_eq_of_dist_lt {x y : baire_space} {N : ℕ} (h : baire_space.dist x y < (1/2) ^ N) {n : ℕ}
  (hn : n ≤ N) :
  x n = y n :=
begin
  rcases eq_or_ne x y with rfl|hne, { refl },
  have : N < first_diff x y,
    by simpa [dist_eq_of_ne hne, inv_lt_inv, pow_lt_pow_iff, one_lt_two] using h,
  exact apply_eq_of_lt_first_diff (hn.trans_lt this),
end

lemma zoug (s : set baire_space) :
  is_open s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, baire_space.dist x y < ε → y ∈ s :=
begin
  have A : is_topological_basis
    {S : set baire_space | ∃ (U : ℕ → set ℕ) (F : finset ℕ), S = (F : set ℕ).pi U},
  { have : is_topological_basis {S : set baire_space | ∃ (U : ℕ → set ℕ) (F : finset ℕ),
      (∀ i, i ∈ F → (U i) ∈ {s | is_open (s : set ℕ)}) ∧ S = (F : set ℕ).pi U } :=
        is_topological_basis_pi (λ i, topological_space.is_topological_basis_opens),
    simpa only [true_and, set.mem_univ, implies_true_iff, set.set_of_true, is_open_discrete] },
  split,
  { assume hs x hx,
    obtain ⟨_, ⟨U, F, rfl⟩, xU, Us⟩ : ∃ (v : set baire_space)
      (H : v ∈ {S : set baire_space | ∃ (U : ℕ → set ℕ) (F : finset ℕ), S = (F : set ℕ).pi U}),
        x ∈ v ∧ v ⊆ s := A.exists_subset_of_mem_open hx hs,
    rcases F.bdd_above with ⟨N, hN⟩,
    refine ⟨(1/2 : ℝ)^N, by simp, λ y hy, Us _⟩,
    simp only [set.mem_pi, finset.mem_coe] at xU ⊢,
    assume n hn,
    suffices : x n = y n, by simp [← this, xU n hn],
    exact apply_eq_of_dist_lt hy (hN hn) }
end

#exit

#check metric_space.of_metrizable

instance : pseudo_metric_space (baire_space) :=
{ dist := baire_space.dist,
  dist_self := λ x, by simp [has_dist.dist, baire_space.dist],
  dist_comm := λ x y, by simp [has_dist.dist, baire_space.dist, @eq_comm _ x y, first_diff_comm],
  dist_triangle := λ x y z, calc
    baire_space.dist x z ≤ max (baire_space.dist x y) (baire_space.dist y z) :
      dist_triangle_nonarch x y z
    ... ≤ baire_space.dist x y + baire_space.dist y z :
      max_le_add_of_nonneg (dist_nonneg x y) (dist_nonneg y z) },


end baire_space

/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .triangle

/-!
# The corners theorem

This file defines combinatorial corners and proves the two dimensional corners theorem.
-/

open finset
open_locale big_operators

variables {α ι : Type*} [add_comm_monoid α] [decidable_eq ι] [fintype ι] {ε : ℝ} {A : set (ℕ × ℕ)}
  {x y : ℕ × ℕ} {a b n : ℕ}

lemma sum_indicator_singleton {ι M : Type*} [add_comm_monoid M] {s : finset ι} {i : ι}
  (hi : i ∈ s)(f : ι → ι  → M) (g : ι → ι) :
  ∑ (j : ι) in s, ({i} : set ι).indicator (f j) (g j) = f i (g i) :=
begin
  sorry,
end

/-! ### Simplex domain -/

/-- The `ι`-th combinatorial simplex domain of size `n + 1`. -/
def simplex_domain (ι : Type*) [fintype ι] (n : ℕ) : Type* := {f : ι → ℕ // ∑ i, f i = n}

variables {s : set (simplex_domain ι n)} {f : ι → ℕ}

/-- Projects any point onto the simplex domain in one direction. -/
def simplex_domain.proj (f : ι → ℕ) (i : ι) (hf : ∑ j in univ.erase i, f j ≤ n) :
  simplex_domain ι n :=
begin
  refine ⟨finset.piecewise {i} (n - ∑ j in univ.erase i, f j) f, (sum_piecewise _ _ _ _).trans _⟩,
  rw [univ_inter, sum_singleton, sdiff_singleton_eq_erase, pi.sub_apply, sum_apply],
  simp only [nat.cast_id, pi.coe_nat],
  exact tsub_add_cancel_of_le hf,
end

/-- A corner in `s` a set of `simplex_domain ι n` is a point whose projections all are within `s` -/
def simplex_corners (s : set (simplex_domain ι n)) : set (ι → ℕ) :=
{f | if h : ∑ i, f i ≤ n
  then (∀ i, simplex_domain.proj f i ((sum_mono_set f $ erase_subset _ _).trans h) ∈ s) else false }

lemma mem_simplex_corners_iff {h : ∀ i, ∑ (j : ι) in univ.erase i, f j ≤ n} :
  f ∈ simplex_corners s ↔ ∑ i, f i ≤ n ∧
    ∀ i, simplex_domain.proj f i (h i) ∈ s :=
begin
  rw simplex_corners,
  sorry
end

/-- Projects any point onto the simplex domain in one direction. -/
def simplex_domain.line (i : ι) (a : ℕ) : set (simplex_domain ι n) := {g | g.val i = a}

/-! ### Simplex corners theorem -/

/-- The graph appearing in the simplex corners theorem. -/
def simplex_corners_graph (s : set (simplex_domain (fin 3) n)) : simple_graph (fin 3 × fin n) :=
simple_graph.from_rel (λ a b, simplex_domain.line a.1 a.2 ∩ simplex_domain.line b.1 b.2 ⊆ s)

-- lemma trivial_triangle_mem_simplex_corners_graph (hx : x ∈ A) {a b : fin n) :
--   half_corners_graph.adj n A (a, k) (b, k)

lemma corners_graph_triangle_free_far : (simplex_corners_graph s n).triangle_free_far ε :=

lemma half_corners_theorem {ε : ℝ} (hε : 0 < ε) :
  ∃ n : ℕ, ∀ A : finset (ℕ × ℕ), (∀ x y, (x, y) ∈ A → x + y ≤ n) →  ε * n^2 ≤ A.card →
    ∃ x y h, h ≠ 0 ∧ is_corner ↑A x y h :=
begin
  sorry
end

/-! ### Usual corners -/

/-- Combinatorial corners. -/
def higher_corners (A : set (ι → α)) : set ((ι → α) × α) :=
{x | x.1 ∈ A ∧ ∀ i, x.1 + set.indicator {i} (λ _, x.2) ∈ A}

/-- Two-dimensional combinatorial corner. -/
def is_corner (A : set (α × α)) : α → α → α → Prop :=
λ x y h, (x, y) ∈ A ∧ (x + h, y) ∈ A ∧ (x, y + h) ∈ A

/-! ### Half Corners theorem -/

/-- The graph appearing in the corners theorem. -/
def half_corners_graph (A : set (ℕ × ℕ)) (n : ℕ) : simple_graph (fin 3 × fin n) :=
simple_graph.from_rel (λ a b, begin
  exact a.1 = 0 ∧ b.1 = 1 ∧ (↑a.2, ↑b.2) ∈ A
      ∨ a.1 = 1 ∧ b.1 = 2 ∧ a.2 ≤ b.2 ∧ (↑b.2 - ↑a.2, ↑a.2) ∈ A
      ∨ a.1 = 2 ∧ b.1 = 0 ∧ b.2 ≤ a.2 ∧ (↑b.2, ↑a.2 - ↑b.2) ∈ A,
end)

-- lemma trivial_triangle_mem_half_corners_graph (hx : x ∈ A) {a b : fin n} :
--   half_corners_graph.adj n A (a, k) (b, k)

lemma corners_graph_triangle_free_far : (half_corners_graph A n).triangle_free_far ε := sorry

lemma half_corners_theorem {ε : ℝ} (hε : 0 < ε) :
  ∃ n : ℕ, ∀ A : finset (ℕ × ℕ), (∀ x y, (x, y) ∈ A → x + y ≤ n) →  ε * n^2 ≤ A.card →
    ∃ x y h, h ≠ 0 ∧ is_corner ↑A x y h :=
begin
  sorry
end

/-! ### Corners theorem-/

/-- The graph appearing in the corners theorem. -/
def corners_graph (A : set (ℕ × ℕ)) : simple_graph (fin 3 × ℕ) := sorry

-- lemma corners_graph_triangle_free_far : (corners_graph A).triangle_free_far ε

lemma corners_theorem {ε : ℝ} (hε : 0 < ε) :
  ∃ n : ℕ, ∀ A ⊆ (Iio n).product (Iio n), ε * n^2 ≤ A.card → ∃ x y h, h ≠ 0 ∧ is_corner ↑A x y h :=
begin
  sorry
end

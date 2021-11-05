/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .corner

/-!
# Roth's theorem

This file proves Roth's theorem
-/

open finset

variables {N : ℕ} (A : finset (fin (2 * N + 1)))

inductive roth_mod_graph :
  fin 3 × fin (2 * N + 1) → fin 3 × fin (2 * N + 1) → Prop
| xy {x y} : y - x ∈ A → roth_mod_graph (0, x) (1, y)
| yz {y z} : z - y ∈ A → roth_mod_graph (1, y) (2, z)
| xz {x z} : (z - x) * (N + 1 : fin (2 * N + 1)) ∈ A → roth_mod_graph (0, x) (2, z)

/-- The graph used in the proof of Roth's theorem. -/
def roth_graph : simple_graph (fin 3 × fin (2 * N + 1)) :=
simple_graph.from_rel (roth_mod_graph A)

open_locale classical

def three_aps : finset (finset (fin (2 * N + 1))) :=
A.powerset.filter (λ i, ∃ (a d : fin (2 * N + 1)), i = {a,a+d,a+2*d})

def nontrivial_three_aps :
  finset (finset (fin (2 * N + 1))) :=
A.powerset.filter (λ i, ∃ (a d : fin (2 * N + 1)), d ≠ 0 ∧ i = {a,a+d,a+2*d})

lemma nontrivial_three_aps_subset_three_aps :
  nontrivial_three_aps A ⊆ three_aps A :=
begin
  rintro t ht,
  simp only [nontrivial_three_aps, three_aps, mem_powerset, mem_filter] at ht ⊢,
  tauto
end

lemma m_le_card_three_aps : A.card ≤ (three_aps A).card :=
begin
  refine card_le_card_of_inj_on (λ i, {i}) _ _,
  { intros i hi,
    simp only [three_aps, mem_filter, mem_powerset, singleton_subset_iff, hi, true_and],
    refine ⟨i, 0, _⟩,
    simp },
  { intros a₁ ha₁ a₂ ha₂,
    apply singleton_injective }
end

-- lemma roth_triangle_free_far (ε : ℝ) (hA : ε * (2 * N + 1) ≤ A.card) :
--   (roth_graph A).triangle_free_far ε :=
-- begin
--   intros H hH hH',
--   sorry
-- end

-- lemma roth_mod (N : ℕ) :
--   ∃ δ : ℝ, 0 < δ ∧
--     ∀ (A : finset (fin (2 * N + 1))),
--       δ * (2 * N + 1) ≤ A.card →
--         ∃ (a d : fin (2 * N + 1)), d ≠ 0 ∧ a ∈ A ∧ a + d ∈ A ∧ a + 2 * d ∈ A :=
-- begin
--   refine ⟨sorry, sorry, λ A hA, _⟩,

-- end

-- def simplex_domain (ι : Type*) [fintype ι] (n : ℕ) : Type* := {f : ι → ℕ // ∑ i, f i = n}

open_locale big_operators

example (ι : Type*) (s : finset ι) {n : ℕ} (j : ι) (f : ι → ℕ) (hj : j ∈ s) :
  f j ≤ ∑ i in s, f i :=
begin
  apply single_le_sum (λ i hi, nat.zero_le _) hj,
end

noncomputable instance (ι : Type*) [fintype ι] {n : ℕ} : fintype (simplex_domain ι n) :=
begin
  let g : {f : ι → fin (n+1) // ∑ i, (f i).val = n} → simplex_domain ι n,
  { intro s,
    exact ⟨coe ∘ s.1, s.2⟩ },
  apply fintype.of_surjective g,
  rintro ⟨f, hf⟩,
  refine ⟨⟨λ i, ⟨f i, _⟩, _⟩, rfl⟩,
  rw [nat.lt_succ_iff, ←hf],
  refine single_le_sum (λ _ _, nat.zero_le _) (mem_univ _),
end

example (f : fin 3 → ℕ) : ∑ i, f i = f 0 + f 1 + f 2 :=
begin
  rw [fin.sum_univ_succ, fin.sum_univ_succ, fin.sum_univ_succ, fin.sum_univ_zero],
  ring
end

lemma convenient_corners {ε : ℝ} (hε : 0 < ε) :
  ∃ n : ℕ, ∀ n', n ≤ n' →
    ∀ A ⊆ (range n').product (range n'), ε * n'^2 ≤ A.card →
      ∃ x y h, 0 < h ∧ is_corner (A : set (ℕ × ℕ)) x y h :=
begin
  let ε' : ℝ := sorry,
  have hε' : 0 < ε' := sorry,
  obtain ⟨n, hn⟩ := strengthened_corners_theorem hε',
  refine ⟨n, λ n' hn' A hA hA', _⟩,
  let B : finset (simplex_domain (fin 3) n') := univ.filter (λ f, (f.1 0, f.1 1) ∈ A),
  obtain ⟨⟨c, hc₁⟩, hc₂ : 0 < c none, hc₃⟩ := hn n' hn' B _,
  have := hc₃ 0,
  simp only [set.sep_univ, coe_filter, set.mem_set_of_eq, coe_univ] at this,
  rw simplex_domain.proj_apply_self at this,
  rw simplex_domain.proj_apply_ne at this,
  dsimp at this,
  have := hc₃ 1,
  have := hc₃ 2,
end

lemma roth (δ : ℝ) (hδ : 0 < δ) :
  ∃ N : ℕ, ∀ n, N ≤ n →
    ∀ A ⊆ range n, δ * n ≤ A.card → ∃ a d, 0 < d ∧ a ∈ A ∧ a + d ∈ A ∧ a + 2 * d ∈ A :=
begin
  let δ' : ℝ := sorry,
  have hδ' : 0 < δ', sorry,
  obtain ⟨N, hN⟩ := strengthened_corners_theorem hδ',
  refine ⟨2 * N, λ n hn A hA hA', _⟩,
  let B : finset (simplex_domain (fin 3) (2 * n)) :=
    univ.filter (λ f, 2 * n ≤ f.1 0 + f.1 2 ∧ f.1 0 - f.1 1 ∈ A),
  have mem_B : ∀ {f : simplex_domain (fin 3) (2 * n)}, f ∈ B ↔ f.1 1 ≤ f.1 0 ∧ f.1 0 - f.1 1 ∈ A,
  {
    sorry
    },
  obtain ⟨⟨c, hc₀⟩, hc₁ : 0 < c _, hc₂⟩ := hN (2 * n) ((nat.le_mul_of_pos_left zero_lt_two).trans $
    hn.trans $ nat.le_mul_of_pos_left zero_lt_two) B _,
  { rw simplex_domain.corners at hc₂,
    let i := c (some 0),
    let j := c (some 1),
    let k := c (some 2),
    refine ⟨c (some 0) - c (some 1) - c none, c none, hc₁, _, _, _⟩,
    { have := (mem_B.1 (hc₂ 1)).2,
      rw [simplex_domain.proj_apply_self, simplex_domain.proj_apply_ne] at this,
      simp_rw [←hc₀] at this,
      simp at this,
      sorry,
      norm_num },
    { have := (mem_B.1 (hc₂ 2)).2,
      rw [simplex_domain.proj_apply_ne, simplex_domain.proj_apply_ne] at this,
      suffices hsum : c (some 0) - c (some 1) - c none + c none = c (some 0) - c (some 1),
      { rw hsum,
        exact this },
      sorry,
      norm_num,
      norm_num },
    { have := (mem_B.1 (hc₂ 0)).2,
      rw [simplex_domain.proj_apply_self, simplex_domain.proj_apply_ne] at this,
      simp_rw [←hc₀] at this,
      simp at this,
      sorry,
      norm_num } }
end

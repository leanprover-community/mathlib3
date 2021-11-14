/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import algebra.order.euclidean_absolute_value
import analysis.special_functions.pow
import combinatorics.pigeonhole

/-!
# Admissible absolute values
This file defines a structure `absolute_value.is_admissible` which we use to show the class number
of the ring of integers of a global field is finite.

## Main definitions

 * `absolute_value.is_admissible abv` states the absolute value `abv : R → ℤ`
   respects the Euclidean domain structure on `R`, and that a large enough set
   of elements of `R^n` contains a pair of elements whose remainders are
   pointwise close together.

## Main results

 * `absolute_value.abs_is_admissible` shows the "standard" absolute value on `ℤ`,
   mapping negative `x` to `-x`, is admissible.
 * `polynomial.card_pow_degree_is_admissible` shows `card_pow_degree`,
   mapping `p : polynomial 𝔽_q` to `q ^ degree p`, is admissible
-/

local infix ` ≺ `:50 := euclidean_domain.r

namespace absolute_value

variables {R : Type*} [euclidean_domain R]
variables (abv : absolute_value R ℤ)

/-- An absolute value `R → ℤ` is admissible if it respects the Euclidean domain
structure and a large enough set of elements in `R^n` will contain a pair of
elements whose remainders are pointwise close together. -/
structure is_admissible extends is_euclidean abv :=
(card : ℝ → ℕ)
(exists_partition' : ∀ (n : ℕ) {ε : ℝ} (hε : 0 < ε) {b : R} (hb : b ≠ 0) (A : fin n → R),
                     ∃ (t : fin n → fin (card ε)),
                     ∀ i₀ i₁, t i₀ = t i₁ → (abv (A i₁ % b - A i₀ % b) : ℝ) < abv b • ε)

attribute [protected] is_admissible.card

namespace is_admissible

variables {abv}

/-- For all `ε > 0` and finite families `A`, we can partition the remainders of `A` mod `b`
into `abv.card ε` sets, such that all elements in each part of remainders are close together. -/
lemma exists_partition {ι : Type*} [fintype ι] {ε : ℝ} (hε : 0 < ε) {b : R} (hb : b ≠ 0)
  (A : ι → R) (h : abv.is_admissible) :
  ∃ (t : ι → fin (h.card ε)),
  ∀ i₀ i₁, t i₀ = t i₁ → (abv (A i₁ % b - A i₀ % b) : ℝ) < abv b • ε :=
begin
  let e := fintype.equiv_fin ι,
  obtain ⟨t, ht⟩ := h.exists_partition' (fintype.card ι) hε hb (A ∘ e.symm),
  refine ⟨t ∘ e, λ i₀ i₁ h, _⟩,
  convert ht (e i₀) (e i₁) h; simp only [e.symm_apply_apply]
end

/-- Any large enough family of vectors in `R^n` has a pair of elements
whose remainders are close together, pointwise. -/
lemma exists_approx_aux (n : ℕ) (h : abv.is_admissible) :
  ∀ {ε : ℝ} (hε : 0 < ε) {b : R} (hb : b ≠ 0) (A : fin (h.card ε ^ n).succ → (fin n → R)),
  ∃ (i₀ i₁), (i₀ ≠ i₁) ∧ ∀ k, (abv (A i₁ k % b - A i₀ k % b) : ℝ) < abv b • ε :=
begin
  haveI := classical.dec_eq R,
  induction n with n ih,
  { intros ε hε b hb A,
    refine ⟨0, 1, _, _⟩,
    { simp },
    rintros ⟨i, ⟨⟩⟩ },
  intros ε hε b hb A,
  set M := h.card ε with hM,
  -- By the "nicer" pigeonhole principle, we can find a collection `s`
  -- of more than `M^n` remainders where the first components lie close together:
  obtain ⟨s, s_inj, hs⟩ : ∃ s : fin (M ^ n).succ → fin (M ^ n.succ).succ,
    function.injective s ∧
    ∀ i₀ i₁, (abv (A (s i₁) 0 % b - A (s i₀) 0 % b) : ℝ) < abv b • ε,
  { -- We can partition the `A`s into `M` subsets where
    -- the first components lie close together:
    obtain ⟨t, ht⟩ : ∃ (t : fin (M ^ n.succ).succ → fin M),
      ∀ i₀ i₁, t i₀ = t i₁ → (abv (A i₁ 0 % b - A i₀ 0 % b) : ℝ) < abv b • ε :=
      h.exists_partition hε hb (λ x, A x 0),
    -- Since the `M` subsets contain more than `M * M^n` elements total,
    -- there must be a subset that contains more than `M^n` elements.
    obtain ⟨s, hs⟩ := @fintype.exists_lt_card_fiber_of_mul_lt_card _ _ _ _ _ t (M ^ n)
      (by simpa only [fintype.card_fin, pow_succ] using nat.lt_succ_self (M ^ n.succ) ),
    refine ⟨λ i, (finset.univ.filter (λ x, t x = s)).to_list.nth_le i _, _, λ i₀ i₁, ht _ _ _⟩,
    { refine i.2.trans_le _, rwa finset.length_to_list },
    { intros i j h, ext, exact list.nodup_iff_nth_le_inj.mp (finset.nodup_to_list _) _ _ _ _ h },
    have : ∀ i h, (finset.univ.filter (λ x, t x = s)).to_list.nth_le i h ∈
      finset.univ.filter (λ x, t x = s),
    { intros i h, exact (finset.mem_to_list _).mp (list.nth_le_mem _ _ _) },
    obtain ⟨_, h₀⟩ := finset.mem_filter.mp (this i₀ _),
    obtain ⟨_, h₁⟩ := finset.mem_filter.mp (this i₁ _),
    exact h₀.trans h₁.symm },
  -- Since `s` is large enough, there are two elements of `A ∘ s`
  -- where the second components lie close together.
  obtain ⟨k₀, k₁, hk, h⟩ := ih hε hb (λ x, fin.tail (A (s x))),
  refine ⟨s k₀, s k₁, λ h, hk (s_inj h), λ i, fin.cases _ (λ i, _) i⟩,
  { exact hs k₀ k₁ },
  { exact h i },
end

/-- Any large enough family of vectors in `R^ι` has a pair of elements
whose remainders are close together, pointwise. -/
lemma exists_approx {ι : Type*} [fintype ι] {ε : ℝ} (hε : 0 < ε) {b : R} (hb : b ≠ 0)
  (h : abv.is_admissible)
  (A : fin (h.card ε ^ fintype.card ι).succ → ι → R) :
  ∃ (i₀ i₁), (i₀ ≠ i₁) ∧ ∀ k, (abv (A i₁ k % b - A i₀ k % b) : ℝ) < abv b • ε :=
begin
  let e := fintype.equiv_fin ι,
  obtain ⟨i₀, i₁, ne, h⟩ := h.exists_approx_aux (fintype.card ι) hε hb (λ x y, A x (e.symm y)),
  refine ⟨i₀, i₁, ne, λ k, _⟩,
  convert h (e k); simp only [e.symm_apply_apply]
end

end is_admissible

end absolute_value

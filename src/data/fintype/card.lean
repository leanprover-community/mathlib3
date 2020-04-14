/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/

import data.fintype.basic algebra.big_operators data.nat.choose tactic.ring

/-!
Results about "big operations" over a `fintype`, and consequent
results about cardinalities of certain types.

## Implementation note
This content had previously been in `data.fintype`, but was moved here to avoid
requiring `algebra.big_operators` (and hence many other imports) as a
dependency of `fintype`.
-/

universes u v

variables {α : Type*} {β : Type*} {γ : Type*}

namespace fintype

lemma card_eq_sum_ones {α} [fintype α] : fintype.card α = (finset.univ : finset α).sum (λ _, 1) :=
finset.card_eq_sum_ones _

end fintype

open finset

theorem fin.prod_univ_succ [comm_monoid β] {n:ℕ} (f : fin n.succ → β) :
  univ.prod f = f 0 * univ.prod (λ i:fin n, f i.succ) :=
begin
  rw [fin.univ_succ, prod_insert, prod_image],
  { intros x _ y _ hxy, exact fin.succ.inj hxy },
  { simpa using fin.succ_ne_zero }
end

@[simp, to_additive] theorem fin.prod_univ_zero [comm_monoid β] (f : fin 0 → β) : univ.prod f = 1 := rfl

theorem fin.sum_univ_succ [add_comm_monoid β] {n:ℕ} (f : fin n.succ → β) :
  univ.sum f = f 0 + univ.sum (λ i:fin n, f i.succ) :=
by apply @fin.prod_univ_succ (multiplicative β)

attribute [to_additive] fin.prod_univ_succ

theorem fin.prod_univ_cast_succ [comm_monoid β] {n:ℕ} (f : fin n.succ → β) :
  univ.prod f = univ.prod (λ i:fin n, f i.cast_succ) * f (fin.last n) :=
begin
  rw [fin.univ_cast_succ, prod_insert, prod_image, mul_comm],
  { intros x _ y _ hxy, exact fin.cast_succ_inj.mp hxy },
  { simpa using fin.cast_succ_ne_last }
end

theorem fin.sum_univ_cast_succ [add_comm_monoid β] {n:ℕ} (f : fin n.succ → β) :
  univ.sum f = univ.sum (λ i:fin n, f i.cast_succ) + f (fin.last n) :=
by apply @fin.prod_univ_cast_succ (multiplicative β)
attribute [to_additive] fin.prod_univ_cast_succ

@[simp] theorem fintype.card_sigma {α : Type*} (β : α → Type*)
  [fintype α] [∀ a, fintype (β a)] :
  fintype.card (sigma β) = univ.sum (λ a, fintype.card (β a)) :=
card_sigma _ _

-- FIXME ouch, this should be in the main file.
@[simp] theorem fintype.card_sum (α β : Type*) [fintype α] [fintype β] :
  fintype.card (α ⊕ β) = fintype.card α + fintype.card β :=
by rw [sum.fintype, fintype.of_equiv_card]; simp

@[simp] lemma fintype.card_pi_finset [decidable_eq α] [fintype α]
  {δ : α → Type*} (t : Π a, finset (δ a)) :
  (fintype.pi_finset t).card = finset.univ.prod (λ a, card (t a)) :=
by simp [fintype.pi_finset, card_map]

@[simp] lemma fintype.card_pi {β : α → Type*} [fintype α] [decidable_eq α]
  [f : Π a, fintype (β a)] : fintype.card (Π a, β a) = univ.prod (λ a, fintype.card (β a)) :=
fintype.card_pi_finset _

-- FIXME ouch, this should be in the main file.
@[simp] lemma fintype.card_fun [fintype α] [decidable_eq α] [fintype β] :
  fintype.card (α → β) = fintype.card β ^ fintype.card α :=
by rw [fintype.card_pi, finset.prod_const, nat.pow_eq_pow]; refl

@[simp] lemma card_vector [fintype α] (n : ℕ) :
  fintype.card (vector α n) = fintype.card α ^ n :=
by rw fintype.of_equiv_card; simp


@[simp, to_additive]
lemma finset.prod_attach_univ [fintype α] [comm_monoid β] (f : {a : α // a ∈ @univ α _} → β) :
  univ.attach.prod (λ x, f x) = univ.prod (λ x, f ⟨x, (mem_univ _)⟩) :=
prod_bij (λ x _, x.1) (λ _ _, mem_univ _) (λ _ _ , by simp) (by simp) (λ b _, ⟨⟨b, mem_univ _⟩, by simp⟩)

@[to_additive]
lemma finset.range_prod_eq_univ_prod [comm_monoid β] (n : ℕ) (f : ℕ → β) :
  (range n).prod f = univ.prod (λ (k : fin n), f k) :=
begin
  symmetry,
  refine prod_bij (λ k hk, k) _ _ _ _,
  { rintro ⟨k, hk⟩ _, simp * },
  { rintro ⟨k, hk⟩ _, simp * },
  { intros, rwa fin.eq_iff_veq },
  { intros k hk, rw mem_range at hk,
    exact ⟨⟨k, hk⟩, mem_univ _, rfl⟩ }
end

/-- Taking a product over `univ.pi t` is the same as taking the product over `fintype.pi_finset t`.
  `univ.pi t` and `fintype.pi_finset t` are essentially the same `finset`, but differ
  in the type of their element, `univ.pi t` is a `finset (Π a ∈ univ, t a)` and
  `fintype.pi_finset t` is a `finset (Π a, t a)`. -/
@[to_additive "Taking a sum over `univ.pi t` is the same as taking the sum over
  `fintype.pi_finset t`. `univ.pi t` and `fintype.pi_finset t` are essentially the same `finset`,
  but differ in the type of their element, `univ.pi t` is a `finset (Π a ∈ univ, t a)` and
  `fintype.pi_finset t` is a `finset (Π a, t a)`."]
lemma finset.prod_univ_pi [decidable_eq α] [fintype α] [comm_monoid β]
  {δ : α → Type*} {t : Π (a : α), finset (δ a)}
  (f : (Π (a : α), a ∈ (univ : finset α) → δ a) → β) :
  (univ.pi t).prod f = (fintype.pi_finset t).prod (λ x, f (λ a _, x a)) :=
prod_bij (λ x _ a, x a (mem_univ _))
  (by simp)
  (by simp)
  (by simp [function.funext_iff] {contextual := tt})
  (λ x hx, ⟨λ a _, x a, by simp * at *⟩)

/-- The product over `univ` of a sum can be written as a sum over the product of sets,
  `fintype.pi_finset`. `finset.prod_sum` is an alternative statement when the product is not
  over `univ` -/
lemma finset.prod_univ_sum [decidable_eq α] [fintype α] [comm_semiring β] {δ : α → Type u_1}
  [Π (a : α), decidable_eq (δ a)] {t : Π (a : α), finset (δ a)}
  {f : Π (a : α), δ a → β} :
  univ.prod (λ a, (t a).sum (λ b, f a b)) =
  (fintype.pi_finset t).sum (λ p, univ.prod (λ x, f x (p x))) :=
by simp only [finset.prod_attach_univ, prod_sum, finset.sum_univ_pi]

/-- Summing `a^s.card * b^(n-s.card)` over all finite subsets `s` of a fintype of cardinality `n`
gives `(a + b)^n`. The "good" proof involves expanding along all coordinates using the fact that
`x^n` is multilinear, but multilinear maps are only available now over rings, so we give instead
a proof reducing to the usual binomial theorem to have a result over semirings. -/
lemma fintype.sum_pow_mul_eq_add_pow
  (α : Type*) [fintype α] {R : Type*} [comm_semiring R] (a b : R) :
  finset.univ.sum (λ (s : finset α), a ^ s.card * b ^ (fintype.card α - s.card)) =
  (a + b) ^ (fintype.card α) :=
finset.sum_pow_mul_eq_add_pow _ _ _

lemma fin.sum_pow_mul_eq_add_pow {n : ℕ} {R : Type*} [comm_semiring R] (a b : R) :
  finset.univ.sum (λ (s : finset (fin n)), a ^ s.card * b ^ (n - s.card)) =
  (a + b) ^ n :=
by simpa using fintype.sum_pow_mul_eq_add_pow (fin n) a b

namespace list

lemma of_fn_prod_take [comm_monoid α] {n : ℕ} (f : fin n → α) (i : ℕ) :
  ((of_fn f).take i).prod = (finset.univ.filter (λ (j : fin n), j.val < i)).prod f :=
begin
  have A : ∀ (j : fin n), ¬ (j.val < 0) := λ j, not_lt_bot,
  induction i with i IH, { simp [A] },
  by_cases h : i < n,
  { have : i < length (of_fn f), by rwa [length_of_fn f],
    rw prod_take_succ _ _ this,
    have A : ((finset.univ : finset (fin n)).filter (λ j, j.val < i + 1))
      = ((finset.univ : finset (fin n)).filter (λ j, j.val < i)) ∪ _root_.singleton (⟨i, h⟩ : fin n),
        by { ext j, simp [nat.lt_succ_iff_lt_or_eq, fin.ext_iff, - add_comm] },
    have B : _root_.disjoint (finset.filter (λ (j : fin n), j.val < i) finset.univ)
      (_root_.singleton (⟨i, h⟩ : fin n)), by simp,
    rw [A, finset.prod_union B, IH],
    simp },
  { have A : (of_fn f).take i = (of_fn f).take i.succ,
    { rw ← length_of_fn f at h,
      have : length (of_fn f) ≤ i := not_lt.mp h,
      rw [take_all_of_le this, take_all_of_le (le_trans this (nat.le_succ _))] },
    have B : ∀ (j : fin n), (j.val < i.succ) = (j.val < i),
    { assume j,
      have : j.val < i := lt_of_lt_of_le j.2 (not_lt.mp h),
      simp [this, lt_trans this (nat.lt_succ_self _)] },
    simp [← A, B, IH] }
end

-- `to_additive` does not work on `of_fn_prod_take` because of `0 : ℕ` in the proof. Copy-paste the
-- proof instead...
lemma of_fn_sum_take [add_comm_monoid α] {n : ℕ} (f : fin n → α) (i : ℕ) :
  ((of_fn f).take i).sum = (finset.univ.filter (λ (j : fin n), j.val < i)).sum f :=
begin
  have A : ∀ (j : fin n), ¬ (j.val < 0) := λ j, not_lt_bot,
  induction i with i IH, { simp [A] },
  by_cases h : i < n,
  { have : i < length (of_fn f), by rwa [length_of_fn f],
    rw sum_take_succ _ _ this,
    have A : ((finset.univ : finset (fin n)).filter (λ j, j.val < i + 1))
      = ((finset.univ : finset (fin n)).filter (λ j, j.val < i)) ∪ _root_.singleton (⟨i, h⟩ : fin n),
        by { ext j, simp [nat.lt_succ_iff_lt_or_eq, fin.ext_iff, - add_comm] },
    have B : _root_.disjoint (finset.filter (λ (j : fin n), j.val < i) finset.univ)
      (_root_.singleton (⟨i, h⟩ : fin n)), by simp,
    rw [A, finset.sum_union B, IH],
    simp },
  { have A : (of_fn f).take i = (of_fn f).take i.succ,
    { rw ← length_of_fn f at h,
      have : length (of_fn f) ≤ i := not_lt.mp h,
      rw [take_all_of_le this, take_all_of_le (le_trans this (nat.le_succ _))] },
    have B : ∀ (j : fin n), (j.val < i.succ) = (j.val < i),
    { assume j,
      have : j.val < i := lt_of_lt_of_le j.2 (not_lt.mp h),
      simp [this, lt_trans this (nat.lt_succ_self _)] },
    simp [← A, B, IH] }
end

attribute [to_additive] of_fn_prod_take

@[to_additive]
lemma of_fn_prod [comm_monoid α] {n : ℕ} {f : fin n → α} :
  (of_fn f).prod = finset.univ.prod f :=
begin
  convert of_fn_prod_take f n,
  { rw [take_all_of_le (le_of_eq (length_of_fn f))] },
  { have : ∀ (j : fin n), j.val < n := λ j, j.2,
    simp [this] }
end

end list

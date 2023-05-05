/-
Copyright (c) 2020 Yury Kudryashov, Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Anne Baanen
-/
import data.fintype.big_operators
import data.fintype.fin
import data.list.fin_range
import logic.equiv.fin

/-!
# Big operators and `fin`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Some results about products and sums over the type `fin`.

The most important results are the induction formulas `fin.prod_univ_cast_succ`
and `fin.prod_univ_succ`, and the formula `fin.prod_const` for the product of a
constant function. These results have variants for sums instead of products.

## Main declarations

* `fin_function_fin_equiv`: An explicit equivalence between `fin n → fin m` and `fin (m ^ n)`.
-/

open_locale big_operators

open finset

variables {α : Type*} {β : Type*}

namespace finset

@[to_additive]
theorem prod_range [comm_monoid β] {n : ℕ} (f : ℕ → β) :
  ∏ i in finset.range n, f i = ∏ i : fin n, f i :=
prod_bij'
  (λ k w, ⟨k, mem_range.mp w⟩)
  (λ a ha, mem_univ _)
  (λ a ha, congr_arg _ (fin.coe_mk _).symm)
  (λ a m, a)
  (λ a m, mem_range.mpr a.prop)
  (λ a ha, fin.coe_mk _)
  (λ a ha, fin.eta _ _)

end finset

namespace fin

@[to_additive]
theorem prod_univ_def [comm_monoid β] {n : ℕ} (f : fin n → β) :
  ∏ i, f i = ((list.fin_range n).map f).prod :=
by simp [univ_def]

@[to_additive]
theorem prod_of_fn [comm_monoid β] {n : ℕ} (f : fin n → β) :
  (list.of_fn f).prod = ∏ i, f i :=
by rw [list.of_fn_eq_map, prod_univ_def]

/-- A product of a function `f : fin 0 → β` is `1` because `fin 0` is empty -/
@[to_additive "A sum of a function `f : fin 0 → β` is `0` because `fin 0` is empty"]
theorem prod_univ_zero [comm_monoid β] (f : fin 0 → β) : ∏ i, f i = 1 := rfl

/-- A product of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the product of `f x`, for some `x : fin (n + 1)` times the remaining product -/
@[to_additive "A sum of a function `f : fin (n + 1) → β` over all `fin (n + 1)` is the sum of `f x`,
for some `x : fin (n + 1)` plus the remaining product"]
theorem prod_univ_succ_above [comm_monoid β] {n : ℕ} (f : fin (n + 1) → β) (x : fin (n + 1)) :
  ∏ i, f i = f x * ∏ i : fin n, f (x.succ_above i) :=
by rw [univ_succ_above, prod_cons, finset.prod_map, rel_embedding.coe_fn_to_embedding]

/-- A product of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the product of `f 0` plus the remaining product -/
@[to_additive "A sum of a function `f : fin (n + 1) → β` over all `fin (n + 1)` is the sum of `f 0`
plus the remaining product"]
theorem prod_univ_succ [comm_monoid β] {n : ℕ} (f : fin (n + 1) → β) :
  ∏ i, f i = f 0 * ∏ i : fin n, f i.succ :=
prod_univ_succ_above f 0

/-- A product of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the product of `f (fin.last n)` plus the remaining product -/
@[to_additive "A sum of a function `f : fin (n + 1) → β` over all `fin (n + 1)` is the sum of
`f (fin.last n)` plus the remaining sum"]
theorem prod_univ_cast_succ [comm_monoid β] {n : ℕ} (f : fin (n + 1) → β) :
  ∏ i, f i = (∏ i : fin n, f i.cast_succ) * f (last n) :=
by simpa [mul_comm] using prod_univ_succ_above f (last n)

@[to_additive] lemma prod_cons [comm_monoid β] {n : ℕ} (x : β) (f : fin n → β) :
  ∏ i : fin n.succ, (cons x f : fin n.succ → β) i = x * ∏ i : fin n, f i :=
by simp_rw [prod_univ_succ, cons_zero, cons_succ]

@[to_additive sum_univ_one] theorem prod_univ_one [comm_monoid β] (f : fin 1 → β) :
  ∏ i, f i = f 0 :=
by simp

@[simp, to_additive] theorem prod_univ_two [comm_monoid β] (f : fin 2 → β) :
  ∏ i, f i = f 0 * f 1 :=
by simp [prod_univ_succ]

@[to_additive] theorem prod_univ_three [comm_monoid β] (f : fin 3 → β) :
  ∏ i, f i = f 0 * f 1 * f 2 :=
by { rw [prod_univ_cast_succ, prod_univ_two], refl }

@[to_additive] theorem prod_univ_four [comm_monoid β] (f : fin 4 → β) :
  ∏ i, f i = f 0 * f 1 * f 2 * f 3 :=
by { rw [prod_univ_cast_succ, prod_univ_three], refl }

@[to_additive] theorem prod_univ_five [comm_monoid β] (f : fin 5 → β) :
  ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 :=
by { rw [prod_univ_cast_succ, prod_univ_four], refl }

@[to_additive] theorem prod_univ_six [comm_monoid β] (f : fin 6 → β) :
  ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 :=
by { rw [prod_univ_cast_succ, prod_univ_five], refl }

@[to_additive] theorem prod_univ_seven [comm_monoid β] (f : fin 7 → β) :
  ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 :=
by { rw [prod_univ_cast_succ, prod_univ_six], refl }

@[to_additive] theorem prod_univ_eight [comm_monoid β] (f : fin 8 → β) :
  ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 * f 7 :=
by { rw [prod_univ_cast_succ, prod_univ_seven], refl }

lemma sum_pow_mul_eq_add_pow {n : ℕ} {R : Type*} [comm_semiring R] (a b : R) :
  ∑ s : finset (fin n), a ^ s.card * b ^ (n - s.card) = (a + b) ^ n :=
by simpa using fintype.sum_pow_mul_eq_add_pow (fin n) a b

lemma prod_const [comm_monoid α] (n : ℕ) (x : α) : ∏ i : fin n, x = x ^ n := by simp

lemma sum_const [add_comm_monoid α] (n : ℕ) (x : α) : ∑ i : fin n, x = n • x := by simp

@[to_additive] lemma prod_Ioi_zero {M : Type*} [comm_monoid M] {n : ℕ} {v : fin n.succ → M} :
  ∏ i in Ioi 0, v i = ∏ j : fin n, v j.succ :=
by rw [Ioi_zero_eq_map, finset.prod_map, rel_embedding.coe_fn_to_embedding, coe_succ_embedding]

@[to_additive]
lemma prod_Ioi_succ {M : Type*} [comm_monoid M] {n : ℕ} (i : fin n) (v : fin n.succ → M) :
  ∏ j in Ioi i.succ, v j = ∏ j in Ioi i, v j.succ :=
by rw [Ioi_succ, finset.prod_map, rel_embedding.coe_fn_to_embedding, coe_succ_embedding]

@[to_additive]
lemma prod_congr' {M : Type*} [comm_monoid M] {a b : ℕ} (f : fin b → M) (h : a = b) :
  ∏ (i : fin a), f (cast h i) = ∏ (i : fin b), f i :=
by { subst h, congr, ext, congr, ext, rw coe_cast, }

@[to_additive]
lemma prod_univ_add {M : Type*} [comm_monoid M] {a b : ℕ} (f : fin (a+b) → M) :
  ∏ (i : fin (a+b)), f i =
  (∏ (i : fin a), f (cast_add b i)) * ∏ (i : fin b), f (nat_add a i) :=
begin
  rw fintype.prod_equiv fin_sum_fin_equiv.symm f (λ i, f (fin_sum_fin_equiv.to_fun i)), swap,
  { intro x,
    simp only [equiv.to_fun_as_coe, equiv.apply_symm_apply], },
  apply fintype.prod_sum_type,
end

@[to_additive]
lemma prod_trunc {M : Type*} [comm_monoid M] {a b : ℕ} (f : fin (a+b) → M)
  (hf : ∀ (j : fin b), f (nat_add a j) = 1) :
  ∏ (i : fin (a+b)), f i =
  ∏ (i : fin a), f (cast_le (nat.le.intro rfl) i) :=
by simpa only [prod_univ_add, fintype.prod_eq_one _ hf, mul_one]

section partial_prod

variables [monoid α] {n : ℕ}

/-- For `f = (a₁, ..., aₙ)` in `αⁿ`, `partial_prod f` is `(1, a₁, a₁a₂, ..., a₁...aₙ)` in `αⁿ⁺¹`. -/
@[to_additive "For `f = (a₁, ..., aₙ)` in `αⁿ`, `partial_sum f` is
`(0, a₁, a₁ + a₂, ..., a₁ + ... + aₙ)` in `αⁿ⁺¹`."]
def partial_prod (f : fin n → α) (i : fin (n + 1)) : α :=
((list.of_fn f).take i).prod

@[simp, to_additive] lemma partial_prod_zero (f : fin n → α) :
  partial_prod f 0 = 1 :=
by simp [partial_prod]

@[to_additive] lemma partial_prod_succ (f : fin n → α) (j : fin n) :
  partial_prod f j.succ = partial_prod f j.cast_succ * (f j) :=
by simp [partial_prod, list.take_succ, list.of_fn_nth_val, dif_pos j.is_lt, ←option.coe_def]

@[to_additive] lemma partial_prod_succ' (f : fin (n + 1) → α) (j : fin (n + 1)) :
  partial_prod f j.succ = f 0 * partial_prod (fin.tail f) j :=
by simpa [partial_prod]

@[to_additive] lemma partial_prod_left_inv {G : Type*} [group G] (f : fin (n + 1) → G) :
  f 0 • partial_prod (λ i : fin n, (f i)⁻¹ * f i.succ) = f :=
funext $ λ x, fin.induction_on x (by simp) (λ x hx,
begin
  simp only [coe_eq_cast_succ, pi.smul_apply, smul_eq_mul] at hx ⊢,
  rw [partial_prod_succ, ←mul_assoc, hx, mul_inv_cancel_left],
end)


@[to_additive] lemma partial_prod_right_inv {G : Type*} [group G]
  (f : fin n → G) (i : fin n) :
  (partial_prod f i.cast_succ)⁻¹ * partial_prod f i.succ = f i :=
begin
  cases i with i hn,
  induction i with i hi generalizing hn,
  { simp [-fin.succ_mk, partial_prod_succ] },
  { specialize hi (lt_trans (nat.lt_succ_self i) hn),
    simp only [fin.coe_eq_cast_succ, fin.succ_mk, fin.cast_succ_mk] at hi ⊢,
    rw [←fin.succ_mk _ _ (lt_trans (nat.lt_succ_self _) hn), ←fin.succ_mk],
    simp only [partial_prod_succ, mul_inv_rev, fin.cast_succ_mk],
    assoc_rw [hi, inv_mul_cancel_left] }
end

/-- Let `(g₀, g₁, ..., gₙ)` be a tuple of elements in `Gⁿ⁺¹`.
Then if `k < j`, this says `(g₀g₁...gₖ₋₁)⁻¹ * g₀g₁...gₖ = gₖ`.
If `k = j`, it says `(g₀g₁...gₖ₋₁)⁻¹ * g₀g₁...gₖ₊₁ = gₖgₖ₊₁`.
If `k > j`, it says `(g₀g₁...gₖ)⁻¹ * g₀g₁...gₖ₊₁ = gₖ₊₁.`
Useful for defining group cohomology. -/
@[to_additive "Let `(g₀, g₁, ..., gₙ)` be a tuple of elements in `Gⁿ⁺¹`.
Then if `k < j`, this says `-(g₀ + g₁ + ... + gₖ₋₁) + (g₀ + g₁ + ... + gₖ) = gₖ`.
If `k = j`, it says `-(g₀ + g₁ + ... + gₖ₋₁) + (g₀ + g₁ + ... + gₖ₊₁) = gₖ + gₖ₊₁`.
If `k > j`, it says `-(g₀ + g₁ + ... + gₖ) + (g₀ + g₁ + ... + gₖ₊₁) = gₖ₊₁.`
Useful for defining group cohomology."]
lemma inv_partial_prod_mul_eq_contract_nth {G : Type*} [group G]
  (g : fin (n + 1) → G) (j : fin (n + 1)) (k : fin n) :
  (partial_prod g (j.succ.succ_above k.cast_succ))⁻¹ * partial_prod g (j.succ_above k).succ
    = j.contract_nth has_mul.mul g k :=
begin
  have := partial_prod_right_inv g,
  rcases lt_trichotomy (k : ℕ) j with (h|h|h),
  { rwa [succ_above_below, succ_above_below, this, contract_nth_apply_of_lt],
    { assumption },
    { rw [cast_succ_lt_iff_succ_le, succ_le_succ_iff, le_iff_coe_le_coe],
      exact le_of_lt h }},
  { rwa [succ_above_below, succ_above_above, partial_prod_succ, cast_succ_fin_succ, ←mul_assoc,
      this, contract_nth_apply_of_eq],
    { simpa only [le_iff_coe_le_coe, ←h] },
    { rw [cast_succ_lt_iff_succ_le, succ_le_succ_iff, le_iff_coe_le_coe],
      exact le_of_eq h }},
  { rwa [succ_above_above, succ_above_above, partial_prod_succ, partial_prod_succ,
      cast_succ_fin_succ, partial_prod_succ, inv_mul_cancel_left, contract_nth_apply_of_gt],
    { exact le_iff_coe_le_coe.2 (le_of_lt h) },
    { rw [le_iff_coe_le_coe, coe_succ],
      exact nat.succ_le_of_lt h }},
end

end partial_prod

end fin

/-- Equivalence between `fin n → fin m` and `fin (m ^ n)`. -/
@[simps] def fin_function_fin_equiv {m n : ℕ} : (fin n → fin m) ≃ fin (m ^ n) :=
equiv.of_right_inverse_of_card_le
  (le_of_eq $ by simp_rw [fintype.card_fun, fintype.card_fin])
  (λ f, ⟨∑ i, f i * m ^ (i : ℕ), begin
    induction n with n ih generalizing f,
    { simp },
    cases m,
    { exact is_empty_elim (f $ fin.last _) },
    simp_rw [fin.sum_univ_cast_succ, fin.coe_cast_succ, fin.coe_last],
    refine (add_lt_add_of_lt_of_le (ih _) $ mul_le_mul_right' (fin.is_le _) _).trans_eq _,
    rw [←one_add_mul, add_comm, pow_succ],
  end⟩)
  (λ a b, ⟨a / m ^ (b : ℕ) % m, begin
    cases n,
    { exact b.elim0 },
    cases m,
    { rw zero_pow n.succ_pos at a,
      exact a.elim0 },
    { exact nat.mod_lt _ m.succ_pos }
  end⟩)
  (λ a, begin
    dsimp,
    induction n with n ih generalizing a,
    { haveI : subsingleton (fin (m ^ 0)) := (fin.cast $ pow_zero _).to_equiv.subsingleton,
      exact subsingleton.elim _ _ },
    simp_rw [fin.forall_iff, fin.ext_iff, fin.coe_mk] at ih,
    ext,
    simp_rw [fin.coe_mk, fin.sum_univ_succ, fin.coe_zero, fin.coe_succ, pow_zero, nat.div_one,
      mul_one, pow_succ, ←nat.div_div_eq_div_mul, mul_left_comm _ m, ←mul_sum],
    rw [ih _ (nat.div_lt_of_lt_mul a.is_lt), nat.mod_add_div],
  end)

lemma fin_function_fin_equiv_apply {m n : ℕ} (f : fin n → fin m):
  (fin_function_fin_equiv f : ℕ) = ∑ (i : fin n), ↑(f i) * m ^ (i : ℕ) := rfl

lemma fin_function_fin_equiv_single {m n : ℕ} [ne_zero m] (i : fin n) (j : fin m) :
  (fin_function_fin_equiv (pi.single i j) : ℕ) = j * m ^ (i : ℕ) :=
begin
  rw [fin_function_fin_equiv_apply, fintype.sum_eq_single i, pi.single_eq_same],
  rintro x hx,
  rw [pi.single_eq_of_ne hx, fin.coe_zero, zero_mul],
end

/-- Equivalence between `Π i : fin m, fin (n i)` and `fin (∏ i : fin m, n i)`. -/
def fin_pi_fin_equiv {m : ℕ} {n : fin m → ℕ} :
  (Π i : fin m, fin (n i)) ≃ fin (∏ i : fin m, n i) :=
equiv.of_right_inverse_of_card_le
  (le_of_eq $ by simp_rw [fintype.card_pi, fintype.card_fin])
  (λ f, ⟨∑ i, f i * ∏ j, n (fin.cast_le i.is_lt.le j), begin
    induction m with m ih generalizing f,
    { simp },
    rw [fin.prod_univ_cast_succ, fin.sum_univ_cast_succ],
    suffices : ∀ (n : fin m → ℕ) (nn : ℕ) (f : Π i : fin m, fin (n i)) (fn : fin nn),
      ∑ i : fin m, ↑(f i) * ∏ j : fin i, n (fin.cast_le i.prop.le j) + ↑fn * ∏ j, n j
          < (∏ i : fin m, n i) * nn,
    { replace this := this (fin.init n) (n (fin.last _)) (fin.init f) (f (fin.last _)),
      rw ←fin.snoc_init_self f,
      simp only [←fin.snoc_init_self n] { single_pass := tt },
      simp_rw [fin.snoc_cast_succ, fin.init_snoc, fin.snoc_last, fin.snoc_init_self n],
      exact this },
    intros n nn f fn,
    cases nn,
    { exact is_empty_elim fn },
    refine (add_lt_add_of_lt_of_le (ih _) $ mul_le_mul_right' (fin.is_le _) _).trans_eq _,
    rw [←one_add_mul, mul_comm, add_comm],
  end⟩)
  (λ a b, ⟨a / (∏ j : fin b, n (fin.cast_le b.is_lt.le j)) % n b, begin
    cases m,
    { exact b.elim0 },
    cases h : n b with nb,
    { rw prod_eq_zero (finset.mem_univ _) h at a,
      exact is_empty_elim a },
    exact nat.mod_lt _ nb.succ_pos,
  end⟩)
  (begin
    intro a, revert a, dsimp only [fin.coe_mk],
    refine fin.cons_induction _ _ n,
    { intro a,
      haveI : subsingleton (fin (∏ i : fin 0, i.elim0)) :=
        (fin.cast $ prod_empty).to_equiv.subsingleton,
      exact subsingleton.elim _ _ },
    { intros n x xs ih a,
      simp_rw [fin.forall_iff, fin.ext_iff, fin.coe_mk] at ih,
      ext,
      simp_rw [fin.coe_mk, fin.sum_univ_succ, fin.cons_succ],
      have := λ i : fin n, fintype.prod_equiv (fin.cast $ fin.coe_succ i).to_equiv
        (λ j, (fin.cons x xs : _ → ℕ) (fin.cast_le (fin.is_lt _).le j))
        (λ j, (fin.cons x xs : _ → ℕ) (fin.cast_le (nat.succ_le_succ (fin.is_lt _).le) j))
        (λ j, rfl),
      simp_rw [this], clear this,
      dsimp only [fin.coe_zero],
      simp_rw [fintype.prod_empty, nat.div_one, mul_one, fin.cons_zero, fin.prod_univ_succ],
      change _ + ∑ y : _, ((_ / (x * _)) % _) * (x * _) = _,
      simp_rw [←nat.div_div_eq_div_mul, mul_left_comm (_ % _ : ℕ), ←mul_sum],
      convert nat.mod_add_div _ _,
      refine eq.trans _ (ih (a / x) (nat.div_lt_of_lt_mul $ a.is_lt.trans_eq _)),
      swap,
      { convert fin.prod_univ_succ (fin.cons x xs : (Π _, ℕ)),
        simp_rw fin.cons_succ },
      congr' with i,
      congr' with j,
      { cases j, refl },
      { cases j, refl } }
  end)

lemma fin_pi_fin_equiv_apply {m : ℕ} {n : fin m → ℕ} (f : Π i : fin m, fin (n i)):
  (fin_pi_fin_equiv f : ℕ) = ∑ i, f i * ∏ j, n (fin.cast_le i.is_lt.le j) := rfl

lemma fin_pi_fin_equiv_single {m : ℕ} {n : fin m → ℕ} [Π i, ne_zero (n i)]
  (i : fin m) (j : fin (n i)) :
  (fin_pi_fin_equiv (pi.single i j : Π i : fin m, fin (n i)) : ℕ)
    = j * ∏ j, n (fin.cast_le i.is_lt.le j) :=
begin
  rw [fin_pi_fin_equiv_apply, fintype.sum_eq_single i, pi.single_eq_same],
  rintro x hx,
  rw [pi.single_eq_of_ne hx, fin.coe_zero, zero_mul],
end

namespace list

section comm_monoid

variables [comm_monoid α]

@[to_additive]
lemma prod_take_of_fn {n : ℕ} (f : fin n → α) (i : ℕ) :
  ((of_fn f).take i).prod = ∏ j in finset.univ.filter (λ (j : fin n), j.val < i), f j :=
begin
  have A : ∀ (j : fin n), ¬ ((j : ℕ) < 0) := λ j, not_lt_bot,
  induction i with i IH, { simp [A] },
  by_cases h : i < n,
  { have : i < length (of_fn f), by rwa [length_of_fn f],
    rw prod_take_succ _ _ this,
    have A : ((finset.univ : finset (fin n)).filter (λ j, j.val < i + 1))
      = ((finset.univ : finset (fin n)).filter (λ j, j.val < i)) ∪ {(⟨i, h⟩ : fin n)},
        by { ext ⟨_, _⟩, simp [nat.lt_succ_iff_lt_or_eq] },
    have B : _root_.disjoint (finset.filter (λ (j : fin n), j.val < i) finset.univ)
      (singleton (⟨i, h⟩ : fin n)), by simp,
    rw [A, finset.prod_union B, IH],
    simp },
  { have A : (of_fn f).take i = (of_fn f).take i.succ,
    { rw ← length_of_fn f at h,
      have : length (of_fn f) ≤ i := not_lt.mp h,
      rw [take_all_of_le this, take_all_of_le (le_trans this (nat.le_succ _))] },
    have B : ∀ (j : fin n), ((j : ℕ) < i.succ) = ((j : ℕ) < i),
    { assume j,
      have : (j : ℕ) < i := lt_of_lt_of_le j.2 (not_lt.mp h),
      simp [this, lt_trans this (nat.lt_succ_self _)] },
    simp [← A, B, IH] }
end

@[to_additive]
lemma prod_of_fn {n : ℕ} {f : fin n → α} :
  (of_fn f).prod = ∏ i, f i :=
begin
  convert prod_take_of_fn f n,
  { rw [take_all_of_le (le_of_eq (length_of_fn f))] },
  { have : ∀ (j : fin n), (j : ℕ) < n := λ j, j.is_lt,
    simp [this] }
end

end comm_monoid

lemma alternating_sum_eq_finset_sum {G : Type*} [add_comm_group G] :
  ∀ (L : list G), alternating_sum L = ∑ i : fin L.length, (-1 : ℤ) ^ (i : ℕ) • L.nth_le i i.is_lt
| [] := by { rw [alternating_sum, finset.sum_eq_zero], rintro ⟨i, ⟨⟩⟩ }
| (g :: []) := by simp
| (g :: h :: L) :=
calc g + -h + L.alternating_sum
    = g + -h + ∑ i : fin L.length, (-1 : ℤ) ^ (i : ℕ) • L.nth_le i i.2 :
      congr_arg _ (alternating_sum_eq_finset_sum _)
... = ∑ i : fin (L.length + 2), (-1 : ℤ) ^ (i : ℕ) • list.nth_le (g :: h :: L) i _ :
begin
  rw [fin.sum_univ_succ, fin.sum_univ_succ, add_assoc],
  unfold_coes,
  simp [nat.succ_eq_add_one, pow_add],
  refl,
end

@[to_additive]
lemma alternating_prod_eq_finset_prod {G : Type*} [comm_group G] :
  ∀ (L : list G), alternating_prod L = ∏ i : fin L.length, (L.nth_le i i.2) ^ ((-1 : ℤ) ^ (i : ℕ))
| [] := by { rw [alternating_prod, finset.prod_eq_one], rintro ⟨i, ⟨⟩⟩ }
| (g :: []) :=
begin
  show g = ∏ i : fin 1, [g].nth_le i i.2 ^ (-1 : ℤ) ^ (i : ℕ),
  rw [fin.prod_univ_succ], simp,
end
| (g :: h :: L) :=
calc g * h⁻¹ * L.alternating_prod
    = g * h⁻¹ * ∏ i : fin L.length, L.nth_le i i.2 ^ (-1 : ℤ) ^ (i : ℕ) :
      congr_arg _ (alternating_prod_eq_finset_prod _)
... = ∏ i : fin (L.length + 2), list.nth_le (g :: h :: L) i _ ^ (-1 : ℤ) ^ (i : ℕ) :
begin
  rw [fin.prod_univ_succ, fin.prod_univ_succ, mul_assoc],
  unfold_coes,
  simp [nat.succ_eq_add_one, pow_add],
  refl,
end

end list

/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import algebra.order.chebyshev
import analysis.special_functions.pow
import order.partition.equipartition

/-!
# Numerical bounds for Szemerédi Regularity Lemma

This file gathers the numerical facts required by the proof of Szemerédi's regularity lemma.

This entire file is internal to the proof of Szemerédi Regularity Lemma.

## Main declarations

* `szemeredi_regularity.step_bound`: During the inductive step, a partition of size `n` is blown to
  size at most `step_bound n`.
* `szemeredi_regularity.initial_bound`: The size of the partition we start the induction with.
* `szemeredi_regularity.bound`: The upper bound on the size of the partition produced by our version
  of Szemerédi's regularity lemma.
-/

open finset fintype function real
open_locale big_operators

namespace szemeredi_regularity

/-- Auxiliary function for Szemerédi's regularity lemma. Blowing up a partition of size `n` during
the induction results in a partition of size at most `step_bound n`. -/
def step_bound (n : ℕ) : ℕ := n * 4 ^ n

lemma le_step_bound : id ≤ step_bound := λ n, nat.le_mul_of_pos_right $ pow_pos (by norm_num) n

lemma step_bound_mono : monotone step_bound :=
λ a b h, nat.mul_le_mul h $ nat.pow_le_pow_of_le_right (by norm_num) h

lemma step_bound_pos_iff {n : ℕ} : 0 < step_bound n ↔ 0 < n := zero_lt_mul_right $ by positivity

alias step_bound_pos_iff ↔ _ step_bound_pos

end szemeredi_regularity

open szemeredi_regularity

variables {α : Type*} [decidable_eq α] [fintype α] {P : finpartition (univ : finset α)}
  {u : finset α} {ε : ℝ}

local notation `m` := (card α/step_bound P.parts.card : ℕ)
local notation `a` := (card α/P.parts.card - m * 4^P.parts.card : ℕ)

namespace tactic
open positivity

private lemma eps_pos {ε : ℝ} {n : ℕ} (h : 100 ≤ 4 ^ n * ε^5) : 0 < ε :=
pow_bit1_pos_iff.1 $ pos_of_mul_pos_right (h.trans_lt' $ by norm_num) $ by positivity

private lemma m_pos [nonempty α] (hPα : P.parts.card * 16^P.parts.card ≤ card α) : 0 < m :=
nat.div_pos ((nat.mul_le_mul_left _ $ nat.pow_le_pow_of_le_left (by norm_num) _).trans hPα) $
  step_bound_pos (P.parts_nonempty $ univ_nonempty.ne_empty).card_pos

/-- Local extension for the `positivity` tactic: A few facts that are needed many times for the
proof of Szemerédi's regularity lemma. -/
meta def positivity_szemeredi_regularity : expr → tactic strictness
| `(%%n / step_bound (finpartition.parts %%P).card) := do
    p ← to_expr
      ``((finpartition.parts %%P).card * 16^(finpartition.parts %%P).card ≤ %%n)
      >>= find_assumption,
    positive <$> mk_app ``m_pos [p]
| ε := do
    typ ← infer_type ε,
    unify typ `(ℝ),
    p ← to_expr ``(100 ≤ 4 ^ _ * %%ε ^ 5) >>= find_assumption,
    positive <$> mk_app ``eps_pos [p]

end tactic

local attribute [positivity] tactic.positivity_szemeredi_regularity

namespace szemeredi_regularity

lemma m_pos [nonempty α] (hPα : P.parts.card * 16^P.parts.card ≤ card α) : 0 < m := by positivity

lemma coe_m_add_one_pos : 0 < (m : ℝ) + 1 := by positivity

lemma one_le_m_coe [nonempty α] (hPα : P.parts.card * 16^P.parts.card ≤ card α) : (1 : ℝ) ≤ m :=
nat.one_le_cast.2 $ m_pos hPα

lemma eps_pow_five_pos (hPε : 100 ≤ 4^P.parts.card * ε^5) : 0 < ε^5 :=
pos_of_mul_pos_right ((by norm_num : (0 : ℝ) < 100).trans_le hPε) $ pow_nonneg (by norm_num) _

lemma eps_pos (hPε : 100 ≤ 4^P.parts.card * ε^5) : 0 < ε :=
pow_bit1_pos_iff.1 $ eps_pow_five_pos hPε

lemma hundred_div_ε_pow_five_le_m [nonempty α] (hPα : P.parts.card * 16^P.parts.card ≤ card α)
  (hPε : 100 ≤ 4^P.parts.card * ε^5) :
  100 / ε^5 ≤ m :=
(div_le_of_nonneg_of_le_mul (eps_pow_five_pos hPε).le (by positivity) hPε).trans
begin
  norm_cast,
  rwa [nat.le_div_iff_mul_le'(step_bound_pos (P.parts_nonempty $ univ_nonempty.ne_empty).card_pos),
    step_bound, mul_left_comm, ←mul_pow],
end

lemma hundred_le_m [nonempty α] (hPα : P.parts.card * 16^P.parts.card ≤ card α)
  (hPε : 100 ≤ 4^P.parts.card * ε^5) (hε : ε ≤ 1) : 100 ≤ m :=
by exact_mod_cast (hundred_div_ε_pow_five_le_m hPα hPε).trans'
  (le_div_self (by norm_num) (by positivity) $ pow_le_one _ (by positivity) hε)

lemma a_add_one_le_four_pow_parts_card : a + 1 ≤ 4^P.parts.card :=
begin
  have h : 1 ≤ 4^P.parts.card := one_le_pow_of_one_le (by norm_num) _,
  rw [step_bound, ←nat.div_div_eq_div_mul, ←nat.le_sub_iff_right h, tsub_le_iff_left,
    ←nat.add_sub_assoc h],
  exact nat.le_pred_of_lt (nat.lt_div_mul_add h),
end

lemma card_aux₁ (hucard : u.card = m * 4^P.parts.card + a) :
  (4^P.parts.card - a) * m + a * (m + 1) = u.card :=
by rw [hucard, mul_add, mul_one, ←add_assoc, ←add_mul, nat.sub_add_cancel
  ((nat.le_succ _).trans a_add_one_le_four_pow_parts_card), mul_comm]

lemma card_aux₂ (hP : P.is_equipartition) (hu : u ∈ P.parts)
  (hucard : ¬u.card = m * 4^P.parts.card + a) :
  (4^P.parts.card - (a + 1)) * m + (a + 1) * (m + 1) = u.card :=
begin
  have : m * 4 ^ P.parts.card ≤ card α / P.parts.card,
  { rw [step_bound, ←nat.div_div_eq_div_mul],
    exact nat.div_mul_le_self _ _ },
  rw nat.add_sub_of_le this at hucard,
  rw [(hP.card_parts_eq_average hu).resolve_left hucard, mul_add, mul_one, ←add_assoc, ←add_mul,
    nat.sub_add_cancel a_add_one_le_four_pow_parts_card, ←add_assoc, mul_comm,
    nat.add_sub_of_le this, card_univ],
end

lemma pow_mul_m_le_card_part (hP : P.is_equipartition) (hu : u ∈ P.parts) :
  (4 : ℝ) ^ P.parts.card * m ≤ u.card :=
begin
  norm_cast,
  rw [step_bound, ←nat.div_div_eq_div_mul],
  exact (nat.mul_div_le _ _).trans (hP.average_le_card_part hu),
end

variables (P ε) (l : ℕ)

/-- Auxiliary function for Szemerédi's regularity lemma. The size of the partition by which we start
blowing. -/
noncomputable def initial_bound : ℕ := max 7 $ max l $ ⌊log (100 / ε^5) / log 4⌋₊ + 1

lemma le_initial_bound : l ≤ initial_bound ε l := (le_max_left _ _).trans $ le_max_right _ _
lemma seven_le_initial_bound : 7 ≤ initial_bound ε l := le_max_left _ _
lemma initial_bound_pos : 0 < initial_bound ε l :=
nat.succ_pos'.trans_le $ seven_le_initial_bound _ _

lemma hundred_lt_pow_initial_bound_mul {ε : ℝ} (hε : 0 < ε) (l : ℕ) :
  100 < 4^initial_bound ε l * ε^5 :=
begin
  rw [←rpow_nat_cast 4, ←div_lt_iff (pow_pos hε 5), lt_rpow_iff_log_lt _ zero_lt_four,
    ←div_lt_iff, initial_bound, nat.cast_max, nat.cast_max],
  { push_cast, exact lt_max_of_lt_right (lt_max_of_lt_right $ nat.lt_floor_add_one _) },
  { exact log_pos (by norm_num) },
  { exact div_pos (by norm_num) (pow_pos hε 5) }
end

/-- An explicit bound on the size of the equipartition whose existence is given by Szemerédi's
regularity lemma. -/
noncomputable def bound : ℕ :=
(step_bound^[⌊4 / ε^5⌋₊] $ initial_bound ε l) * 16 ^ (step_bound^[⌊4 / ε^5⌋₊] $ initial_bound ε l)

lemma initial_bound_le_bound : initial_bound ε l ≤ bound ε l :=
(id_le_iterate_of_id_le le_step_bound _ _).trans $ nat.le_mul_of_pos_right $ by positivity

lemma le_bound : l ≤ bound ε l := (le_initial_bound ε l).trans $ initial_bound_le_bound ε l
lemma bound_pos : 0 < bound ε l := (initial_bound_pos ε l).trans_le $ initial_bound_le_bound ε l

variables {ι 𝕜 : Type*} [linear_ordered_field 𝕜] (r : ι → ι → Prop) [decidable_rel r]
  {s t : finset ι} {x : 𝕜}

lemma mul_sq_le_sum_sq (hst : s ⊆ t) (f : ι → 𝕜) (hs : x^2 ≤ ((∑ i in s, f i) / s.card) ^ 2)
  (hs' : (s.card : 𝕜) ≠ 0) :
  (s.card : 𝕜) * x ^ 2 ≤ ∑ i in t, f i ^ 2 :=
(mul_le_mul_of_nonneg_left (hs.trans sum_div_card_sq_le_sum_sq_div_card) $
  nat.cast_nonneg _).trans $ (mul_div_cancel' _ hs').le.trans $ sum_le_sum_of_subset_of_nonneg hst $
    λ i _ _, sq_nonneg _

lemma add_div_le_sum_sq_div_card (hst : s ⊆ t) (f : ι → 𝕜) (d : 𝕜) (hx : 0 ≤ x)
  (hs : x ≤ |(∑ i in s, f i)/s.card - (∑ i in t, f i)/t.card|)
  (ht : d ≤ ((∑ i in t, f i)/t.card)^2) :
  d + s.card/t.card * x^2 ≤ (∑ i in t, f i^2)/t.card :=
begin
  obtain hscard | hscard := (s.card.cast_nonneg : (0 : 𝕜) ≤ s.card).eq_or_lt,
  { simpa [←hscard] using ht.trans sum_div_card_sq_le_sum_sq_div_card },
  have htcard : (0:𝕜) < t.card := hscard.trans_le (nat.cast_le.2 (card_le_of_subset hst)),
  have h₁ : x^2 ≤ ((∑ i in s, f i)/s.card - (∑ i in t, f i)/t.card)^2 :=
    sq_le_sq.2 (by rwa [abs_of_nonneg hx]),
  have h₂ : x^2 ≤ ((∑ i in s, (f i - (∑ j in t, f j)/t.card))/s.card)^2,
  { apply h₁.trans,
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, sub_div, mul_div_cancel_left _ hscard.ne'] },
  apply (add_le_add_right ht _).trans,
  rw [←mul_div_right_comm, le_div_iff htcard, add_mul, div_mul_cancel _ htcard.ne'],
  have h₃ := mul_sq_le_sum_sq hst (λ i, f i - (∑ j in t, f j) / t.card) h₂ hscard.ne',
  apply (add_le_add_left h₃ _).trans,
  simp [←mul_div_right_comm _ (t.card : 𝕜), sub_div' _ _ _ htcard.ne', ←sum_div, ←add_div, mul_pow,
    div_le_iff (sq_pos_of_ne_zero _ htcard.ne'), sub_sq, sum_add_distrib, ←sum_mul, ←mul_sum],
  ring_nf,
end

end szemeredi_regularity

namespace tactic
open positivity szemeredi_regularity

/-- Extension for the `positivity` tactic: `szemeredi_regularity.initial_bound` and
`szemeredi_regularity.bound` are always positive. -/
@[positivity]
meta def positivity_szemeredi_regularity_bound : expr → tactic strictness
| `(szemeredi_regularity.initial_bound %%ε %%l) := positive <$> mk_app ``initial_bound_pos [ε, l]
| `(szemeredi_regularity.bound %%ε %%l) := positive <$> mk_app ``bound_pos [ε, l]
| e := pp e >>= fail ∘ format.bracket "The expression `"
 "` isn't of the form `szemeredi_regularity.initial_bound ε l` nor `szemeredi_regularity.bound ε l`"

example (ε : ℝ) (l : ℕ) : 0 < szemeredi_regularity.initial_bound ε l := by positivity
example (ε : ℝ) (l : ℕ) : 0 < szemeredi_regularity.bound ε l := by positivity

end tactic

/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import algebra.order.ring.canonical
import data.nat.basic

/-!
# The natural numbers as a linearly ordered commutative semiring

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We also have a variety of lemmas which have been deferred from `data.nat.basic` because it is
easier to prove them with this ordered semiring instance available.

You may find that some theorems can be moved back to `data.nat.basic` by modifying their proofs.
-/

universes u v

/-! ### instances -/

instance nat.order_bot : order_bot ℕ :=
{ bot := 0, bot_le := nat.zero_le }

instance : linear_ordered_comm_semiring ℕ :=
{ lt                      := nat.lt,
  add_le_add_left         := @nat.add_le_add_left,
  le_of_add_le_add_left   := @nat.le_of_add_le_add_left,
  zero_le_one             := nat.le_of_lt (nat.zero_lt_succ 0),
  mul_lt_mul_of_pos_left  := @nat.mul_lt_mul_of_pos_left,
  mul_lt_mul_of_pos_right := @nat.mul_lt_mul_of_pos_right,
  decidable_eq            := nat.decidable_eq,
  exists_pair_ne          := ⟨0, 1, ne_of_lt nat.zero_lt_one⟩,
  ..nat.comm_semiring, ..nat.linear_order }

instance : linear_ordered_comm_monoid_with_zero ℕ :=
{ mul_le_mul_left := λ a b h c, nat.mul_le_mul_left c h,
  ..nat.linear_ordered_comm_semiring,
  ..(infer_instance : comm_monoid_with_zero ℕ)}

/-! Extra instances to short-circuit type class resolution and ensure computability -/
-- Not using `infer_instance` avoids `classical.choice` in the following two
instance : linear_ordered_semiring ℕ      := infer_instance
instance : strict_ordered_semiring ℕ      := infer_instance
instance : strict_ordered_comm_semiring ℕ := infer_instance
instance : ordered_semiring ℕ             := strict_ordered_semiring.to_ordered_semiring'
instance : ordered_comm_semiring ℕ        := strict_ordered_comm_semiring.to_ordered_comm_semiring'

instance : linear_ordered_cancel_add_comm_monoid ℕ := infer_instance

instance : canonically_ordered_comm_semiring ℕ :=
{ exists_add_of_le                  := λ a b h, (nat.le.dest h).imp $ λ _, eq.symm,
  le_self_add                       := nat.le_add_right,
  eq_zero_or_eq_zero_of_mul_eq_zero := λ a b, nat.eq_zero_of_mul_eq_zero,
  .. nat.nontrivial,
  .. nat.order_bot,
  .. (infer_instance : ordered_add_comm_monoid ℕ),
  .. (infer_instance : linear_ordered_semiring ℕ),
  .. (infer_instance : comm_semiring ℕ) }

instance : canonically_linear_ordered_add_monoid ℕ :=
{ .. (infer_instance : canonically_ordered_add_monoid ℕ),
  .. nat.linear_order }

variables {m n k l : ℕ}
namespace nat

/-! ### Equalities and inequalities involving zero and one -/

lemma one_le_iff_ne_zero : 1 ≤ n ↔ n ≠ 0 :=
(show 1 ≤ n ↔ 0 < n, from iff.rfl).trans pos_iff_ne_zero

lemma one_lt_iff_ne_zero_and_ne_one : ∀ {n : ℕ}, 1 < n ↔ n ≠ 0 ∧ n ≠ 1
| 0     := dec_trivial
| 1     := dec_trivial
| (n+2) := dec_trivial

protected theorem mul_ne_zero (n0 : n ≠ 0) (m0 : m ≠ 0) : n * m ≠ 0
| nm := (eq_zero_of_mul_eq_zero nm).elim n0 m0

@[simp] protected theorem mul_eq_zero : m * n = 0 ↔ m = 0 ∨ n = 0 :=
iff.intro eq_zero_of_mul_eq_zero (by simp [or_imp_distrib] {contextual := tt})

@[simp] protected theorem zero_eq_mul : 0 = m * n ↔ m = 0 ∨ n = 0 :=
by rw [eq_comm, nat.mul_eq_zero]

lemma eq_zero_of_double_le (h : 2 * n ≤ n) : n = 0 :=
add_right_eq_self.mp $ le_antisymm ((two_mul n).symm.trans_le h) le_add_self

lemma eq_zero_of_mul_le (hb : 2 ≤ n) (h : n * m ≤ m) : m = 0 :=
eq_zero_of_double_le $ le_trans (nat.mul_le_mul_right _ hb) h

lemma zero_max : max 0 n = n := max_eq_right (zero_le _)

@[simp] lemma min_eq_zero_iff : min m n = 0 ↔ m = 0 ∨ n = 0 :=
begin
  split,
  { intro h,
    cases le_total m n with H H,
    { simpa [H] using or.inl h },
    { simpa [H] using or.inr h } },
  { rintro (rfl|rfl);
    simp }
end

@[simp] lemma max_eq_zero_iff : max m n = 0 ↔ m = 0 ∧ n = 0 :=
begin
  split,
  { intro h,
    cases le_total m n with H H,
    { simp only [H, max_eq_right] at h,
      exact ⟨le_antisymm (H.trans h.le) (zero_le _), h⟩ },
    { simp only [H, max_eq_left] at h,
      exact ⟨h, le_antisymm (H.trans h.le) (zero_le _)⟩ } },
  { rintro ⟨rfl, rfl⟩,
    simp }
end

lemma add_eq_max_iff : m + n = max m n ↔ m = 0 ∨ n = 0 :=
begin
  rw ←min_eq_zero_iff,
  cases le_total m n with H H;
  simp [H]
end

lemma add_eq_min_iff : m + n = min m n ↔ m = 0 ∧ n = 0 :=
begin
  rw ←max_eq_zero_iff,
  cases le_total m n with H H;
  simp [H]
end

lemma one_le_of_lt (h : n < m) : 1 ≤ m := lt_of_le_of_lt (nat.zero_le _) h

theorem eq_one_of_mul_eq_one_right (H : m * n = 1) : m = 1 := eq_one_of_dvd_one ⟨n, H.symm⟩

theorem eq_one_of_mul_eq_one_left (H : m * n = 1) : n = 1 :=
eq_one_of_mul_eq_one_right (by rwa mul_comm)

/-! ### `succ` -/

lemma two_le_iff : ∀ n, 2 ≤ n ↔ n ≠ 0 ∧ n ≠ 1
| 0     := by simp
| 1     := by simp
| (n+2) := by simp

@[simp] lemma lt_one_iff {n : ℕ} : n < 1 ↔ n = 0 :=
lt_succ_iff.trans nonpos_iff_eq_zero

/-! ### `add` -/

theorem add_pos_left {m : ℕ} (h : 0 < m) (n : ℕ) : 0 < m + n :=
calc
  m + n > 0 + n : nat.add_lt_add_right h n
    ... = n     : nat.zero_add n
    ... ≥ 0     : zero_le n

theorem add_pos_right (m : ℕ) {n : ℕ} (h : 0 < n) : 0 < m + n :=
begin rw add_comm, exact add_pos_left h m end

theorem add_pos_iff_pos_or_pos (m n : ℕ) : 0 < m + n ↔ 0 < m ∨ 0 < n :=
iff.intro
  begin
    intro h,
    cases m with m,
    {simp [zero_add] at h, exact or.inr h},
    exact or.inl (succ_pos _)
  end
  begin
    intro h, cases h with mpos npos,
    { apply add_pos_left mpos },
    apply add_pos_right _ npos
  end

lemma add_eq_one_iff : m + n = 1 ↔ m = 0 ∧ n = 1 ∨ m = 1 ∧ n = 0 :=
by cases n; simp [succ_eq_add_one, ← add_assoc, succ_inj']

lemma add_eq_two_iff : m + n = 2 ↔ m = 0 ∧ n = 2 ∨ m = 1 ∧ n = 1 ∨ m = 2 ∧ n = 0 :=
by cases n; simp [(succ_ne_zero 1).symm, succ_eq_add_one, ← add_assoc, succ_inj', add_eq_one_iff]

lemma add_eq_three_iff :
  m + n = 3 ↔ m = 0 ∧ n = 3 ∨ m = 1 ∧ n = 2 ∨ m = 2 ∧ n = 1 ∨ m = 3 ∧ n = 0 :=
by cases n; simp [(succ_ne_zero 1).symm, succ_eq_add_one, ← add_assoc, succ_inj', add_eq_two_iff]

theorem le_add_one_iff : m ≤ n + 1 ↔ m ≤ n ∨ m = n + 1 :=
⟨λ h,
  match nat.eq_or_lt_of_le h with
  | or.inl h := or.inr h
  | or.inr h := or.inl $ nat.le_of_succ_le_succ h
  end,
  or.rec (λ h, le_trans h $ nat.le_add_right _ _) le_of_eq⟩

lemma le_and_le_add_one_iff : n ≤ m ∧ m ≤ n + 1 ↔ m = n ∨ m = n + 1 :=
begin
  rw [le_add_one_iff, and_or_distrib_left, ←le_antisymm_iff, eq_comm, and_iff_right_of_imp],
  rintro rfl,
  exact n.le_succ
end

lemma add_succ_lt_add (hab : m < n) (hcd : k < l) : m + k + 1 < n + l :=
begin
  rw add_assoc,
  exact add_lt_add_of_lt_of_le hab (nat.succ_le_iff.2 hcd)
end

/-! ### `pred` -/

lemma pred_le_iff : pred m ≤ n ↔ m ≤ succ n :=
⟨le_succ_of_pred_le, by { cases m, { exact λ _, zero_le n }, exact le_of_succ_le_succ }⟩

/-! ### `sub`

Most lemmas come from the `has_ordered_sub` instance on `ℕ`. -/

instance : has_ordered_sub ℕ :=
begin
  constructor,
  intros m n k,
  induction n with n ih generalizing k,
  { simp },
  { simp only [sub_succ, add_succ, succ_add, ih, pred_le_iff] }
end

lemma lt_pred_iff : n < pred m ↔ succ n < m := show n < m - 1 ↔ n + 1 < m, from lt_tsub_iff_right

lemma lt_of_lt_pred (h : m < n - 1) : m < n := lt_of_succ_lt (lt_pred_iff.1 h)

lemma le_or_le_of_add_eq_add_pred (h : k + l = m + n - 1) : m ≤ k ∨ n ≤ l :=
begin
  cases le_or_lt m k with h' h'; [left, right],
  { exact h' },
  { replace h' := add_lt_add_right h' l, rw h at h',
    cases n.eq_zero_or_pos with hn hn, { rw hn, exact zero_le l },
    rw [m.add_sub_assoc hn, add_lt_add_iff_left] at h',
    exact nat.le_of_pred_lt h' },
end

/-- A version of `nat.sub_succ` in the form `_ - 1` instead of `nat.pred _`. -/
lemma sub_succ' (m n : ℕ) : m - n.succ = m - n - 1 := rfl

/-! ### `mul` -/

lemma mul_eq_one_iff : ∀ {m n : ℕ}, m * n = 1 ↔ m = 1 ∧ n = 1
| 0     0     := dec_trivial
| 0     1     := dec_trivial
| 1     0     := dec_trivial
| (m+2) 0     := by simp
| 0     (n+2) := by simp
| (m+1) (n+1) := ⟨
  λ h, by simp only [add_mul, mul_add, mul_add, one_mul, mul_one,
    (add_assoc _ _ _).symm, nat.succ_inj', add_eq_zero_iff] at h; simp [h.1.2, h.2],
  λ h, by simp only [h, mul_one]⟩

lemma succ_mul_pos (m : ℕ) (hn : 0 < n) : 0 < (succ m) * n := mul_pos (succ_pos m) hn

theorem mul_self_le_mul_self (h : m ≤ n) : m * m ≤ n * n := mul_le_mul h h (zero_le _) (zero_le _)

theorem mul_self_lt_mul_self : Π {m n : ℕ}, m < n → m * m < n * n
| 0        n h := mul_pos h h
| (succ m) n h := mul_lt_mul h (le_of_lt h) (succ_pos _) (zero_le _)

theorem mul_self_le_mul_self_iff : m ≤ n ↔ m * m ≤ n * n :=
⟨mul_self_le_mul_self, le_imp_le_of_lt_imp_lt mul_self_lt_mul_self⟩

theorem mul_self_lt_mul_self_iff : m < n ↔ m * m < n * n :=
le_iff_le_iff_lt_iff_lt.1 mul_self_le_mul_self_iff

theorem le_mul_self : Π (n : ℕ), n ≤ n * n
| 0     := le_rfl
| (n+1) := by simp

lemma le_mul_of_pos_left (h : 0 < n) : m ≤ n * m :=
begin
  conv {to_lhs, rw [← one_mul(m)]},
  exact mul_le_mul_of_nonneg_right h.nat_succ_le dec_trivial,
end

lemma le_mul_of_pos_right (h : 0 < n) : m ≤ m * n :=
begin
  conv {to_lhs, rw [← mul_one(m)]},
  exact mul_le_mul_of_nonneg_left h.nat_succ_le dec_trivial,
end

theorem mul_self_inj : m * m = n * n ↔ m = n :=
le_antisymm_iff.trans (le_antisymm_iff.trans
  (and_congr mul_self_le_mul_self_iff mul_self_le_mul_self_iff)).symm

lemma le_add_pred_of_pos (n : ℕ) {i : ℕ} (hi : i ≠ 0) : n ≤ i + (n - 1) :=
begin
  refine le_trans _ (add_tsub_le_assoc),
  simp [add_comm, nat.add_sub_assoc, one_le_iff_ne_zero.2 hi]
end

@[simp] theorem lt_mul_self_iff : ∀ {n : ℕ}, n < n * n ↔ 1 < n
| 0 := iff_of_false (lt_irrefl _) zero_le_one.not_lt
| (n + 1) := lt_mul_iff_one_lt_left n.succ_pos

/-!
### Recursion and induction principles

This section is here due to dependencies -- the lemmas here require some of the lemmas
proved above, and some of the results in later sections depend on the definitions in this section.
-/

/-- Given a predicate on two naturals `P : ℕ → ℕ → Prop`, `P a b` is true for all `a < b` if
`P (a + 1) (a + 1)` is true for all `a`, `P 0 (b + 1)` is true for all `b` and for all
`a < b`, `P (a + 1) b` is true and `P a (b + 1)` is true implies `P (a + 1) (b + 1)` is true. -/
@[elab_as_eliminator]
lemma diag_induction (P : ℕ → ℕ → Prop) (ha : ∀ a, P (a + 1) (a + 1)) (hb : ∀ b, P 0 (b + 1))
  (hd : ∀ a b, a < b → P (a + 1) b → P a (b + 1) → P (a + 1) (b + 1)) :
  ∀ a b, a < b → P a b
| 0 (b + 1) h       := hb _
| (a + 1) (b + 1) h :=
begin
  apply hd _ _ ((add_lt_add_iff_right _).1 h),
  { have : a + 1 = b ∨ a + 1 < b,
    { rwa [← le_iff_eq_or_lt, ← nat.lt_succ_iff] },
    rcases this with rfl | _,
    { exact ha _ },
    apply diag_induction (a + 1) b this },
  apply diag_induction a (b + 1),
  apply lt_of_le_of_lt (nat.le_succ _) h,
end
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ p, p.1 + p.2.1)⟩] }

/-- A subset of `ℕ` containing `k : ℕ` and closed under `nat.succ` contains every `n ≥ k`. -/
lemma set_induction_bounded {S : set ℕ} (hk : k ∈ S) (h_ind: ∀ k : ℕ, k ∈ S → k + 1 ∈ S)
  (hnk : k ≤ n) : n ∈ S :=
@le_rec_on (λ n, n ∈ S) k n hnk h_ind hk

/-- A subset of `ℕ` containing zero and closed under `nat.succ` contains all of `ℕ`. -/
lemma set_induction {S : set ℕ} (hb : 0 ∈ S) (h_ind: ∀ k : ℕ, k ∈ S → k + 1 ∈ S) (n : ℕ) : n ∈ S :=
set_induction_bounded hb h_ind (zero_le n)

/-! ### `div` -/

protected lemma div_le_of_le_mul' (h : m ≤ k * n) : m / k ≤ n :=
(nat.eq_zero_or_pos k).elim
  (λ k0, by rw [k0, nat.div_zero]; apply zero_le)
  (λ k0, (mul_le_mul_left k0).1 $
    calc k * (m / k)
        ≤ m % k + k * (m / k) : nat.le_add_left _ _
    ... = m                   : mod_add_div _ _
    ... ≤ k * n               : h)

protected lemma div_le_self' (m n : ℕ) : m / n ≤ m :=
(nat.eq_zero_or_pos n).elim
  (λ n0, by rw [n0, nat.div_zero]; apply zero_le)
  (λ n0, nat.div_le_of_le_mul' $ calc
      m = 1 * m : (one_mul _).symm
    ... ≤ n * m : nat.mul_le_mul_right _ n0)

protected lemma div_lt_of_lt_mul (h : m < n * k) : m / n < k :=
lt_of_mul_lt_mul_left
  (calc n * (m / n) ≤ m % n + n * (m / n) : nat.le_add_left _ _
    ... = m : mod_add_div _ _
    ... < n * k : h)
  (nat.zero_le n)

lemma eq_zero_of_le_div (hn : 2 ≤ n) (h : m ≤ m / n) : m = 0 :=
eq_zero_of_mul_le hn $
  by rw mul_comm; exact (nat.le_div_iff_mul_le' (lt_of_lt_of_le dec_trivial hn)).1 h

lemma div_mul_div_le_div (m n k : ℕ) : ((m / k) * n) / m ≤ n / k :=
if hm0 : m = 0 then by simp [hm0]
else calc m / k * n / m ≤ n * m / k / m :
    nat.div_le_div_right (by rw [mul_comm];
        exact mul_div_le_mul_div_assoc _ _ _)
  ... = n / k : by rw [nat.div_div_eq_div_mul, mul_comm n, mul_comm k,
      nat.mul_div_mul _ _ (nat.pos_of_ne_zero hm0)]

lemma eq_zero_of_le_half (h : n ≤ n / 2) : n = 0 := eq_zero_of_le_div le_rfl h

lemma mul_div_mul_comm_of_dvd_dvd (hmk : k ∣ m) (hnl : l ∣ n) : m * n / (k * l) = m / k * (n / l) :=
begin
  rcases k.eq_zero_or_pos with rfl | hk0, { simp },
  rcases l.eq_zero_or_pos with rfl | hl0, { simp },
  obtain ⟨_, rfl⟩ := hmk,
  obtain ⟨_, rfl⟩ := hnl,
  rw [mul_mul_mul_comm, nat.mul_div_cancel_left _ hk0, nat.mul_div_cancel_left _ hl0,
      nat.mul_div_cancel_left _ (mul_pos hk0 hl0)]
end

lemma le_half_of_half_lt_sub {a b : ℕ} (h : a / 2 < a - b) : b ≤ a / 2 :=
begin
  rw nat.le_div_iff_mul_le two_pos,
  rw [nat.div_lt_iff_lt_mul two_pos, nat.mul_sub_right_distrib, lt_tsub_iff_right,
    mul_two a] at h,
  exact le_of_lt (nat.lt_of_add_lt_add_left h)
end

lemma half_le_of_sub_le_half {a b : ℕ} (h : a - b ≤ a / 2) : a / 2 ≤ b :=
begin
  rw [nat.le_div_iff_mul_le two_pos, nat.mul_sub_right_distrib, tsub_le_iff_right,
    mul_two, add_le_add_iff_left] at h,
  rw [← nat.mul_div_left b two_pos],
  exact nat.div_le_div_right h,
end

/-! ### `mod`, `dvd` -/

lemma two_mul_odd_div_two (hn : n % 2 = 1) : 2 * (n / 2) = n - 1 :=
by conv {to_rhs, rw [← nat.mod_add_div n 2, hn, add_tsub_cancel_left]}

lemma div_dvd_of_dvd (h : n ∣ m) : (m / n) ∣ m := ⟨n, (nat.div_mul_cancel h).symm⟩

protected lemma div_div_self (h : n ∣ m) (hm : m ≠ 0) : m / (m / n) = n :=
begin
  rcases h with ⟨_, rfl⟩,
  rw mul_ne_zero_iff at hm,
  rw [mul_div_right _ (nat.pos_of_ne_zero hm.1), mul_div_left _ (nat.pos_of_ne_zero hm.2)]
end

lemma mod_mul_right_div_self (m n k : ℕ) : m % (n * k) / n = (m / n) % k :=
begin
  rcases nat.eq_zero_or_pos n with rfl|hn, { simp },
  rcases nat.eq_zero_or_pos k with rfl|hk, { simp },
  conv_rhs { rw ← mod_add_div m (n * k) },
  rw [mul_assoc, add_mul_div_left _ _ hn, add_mul_mod_self_left,
    mod_eq_of_lt (nat.div_lt_of_lt_mul (mod_lt _ (mul_pos hn hk)))]
end

lemma mod_mul_left_div_self (m n k : ℕ) : m % (k * n) / n = (m / n) % k :=
by rw [mul_comm k, mod_mul_right_div_self]

lemma not_dvd_of_pos_of_lt (h1 : 0 < n) (h2 : n < m) : ¬ m ∣ n :=
begin
  rintros ⟨k, rfl⟩,
  rcases nat.eq_zero_or_pos k with (rfl | hk),
  { exact lt_irrefl 0 h1 },
  { exact not_lt.2 (le_mul_of_pos_right hk) h2 },
end

/--  If `m` and `n` are equal mod `k`, `m - n` is zero mod `k`. -/
lemma sub_mod_eq_zero_of_mod_eq (h : m % k = n % k) : (m - n) % k = 0 :=
by rw [←nat.mod_add_div m k, ←nat.mod_add_div n k, ←h, tsub_add_eq_tsub_tsub, add_tsub_cancel_left,
       ←mul_tsub, nat.mul_mod_right]

@[simp] lemma one_mod (n : ℕ) : 1 % (n + 2) = 1 := nat.mod_eq_of_lt (add_lt_add_right n.succ_pos 1)

lemma dvd_sub_mod (k : ℕ) : n ∣ (k - (k % n)) :=
⟨k / n, tsub_eq_of_eq_add_rev (nat.mod_add_div k n).symm⟩

lemma add_mod_eq_ite :
  (m + n) % k = if k ≤ m % k + n % k then m % k + n % k - k else m % k + n % k :=
begin
  cases k, { simp },
  rw nat.add_mod,
  split_ifs with h,
  { rw [nat.mod_eq_sub_mod h, nat.mod_eq_of_lt],
    exact (tsub_lt_iff_right h).mpr
        (nat.add_lt_add (m.mod_lt k.zero_lt_succ) (n.mod_lt k.zero_lt_succ)) },
  { exact nat.mod_eq_of_lt (lt_of_not_ge h) }
end

lemma div_mul_div_comm (hmn : n ∣ m) (hkl : l ∣ k) : (m / n) * (k / l) = (m * k) / (n * l) :=
have exi1 : ∃ x, m = n * x, from hmn,
have exi2 : ∃ y, k = l * y, from hkl,
if hn : n = 0 then by simp [hn]
else have 0 < n, from nat.pos_of_ne_zero hn,
if hl : l = 0 then by simp [hl]
else have 0 < l, from nat.pos_of_ne_zero hl,
begin
  cases exi1 with x hx, cases exi2 with y hy,
  rw [hx, hy, nat.mul_div_cancel_left, nat.mul_div_cancel_left],
  symmetry,
  apply nat.div_eq_of_eq_mul_left,
  apply mul_pos,
  repeat {assumption},
  cc
end

lemma div_eq_self : m / n = m ↔ m = 0 ∨ n = 1 :=
begin
  split,
  { intro,
    cases n,
    { simp * at * },
    { cases n,
      { right, refl },
      { left,
        have : m / (n + 2) ≤ m / 2 := div_le_div_left (by simp) dec_trivial,
        refine eq_zero_of_le_half _,
        simp * at * } } },
  { rintros (rfl|rfl); simp }
end

lemma div_eq_sub_mod_div : m / n = (m - m % n) / n :=
begin
  by_cases n0 : n = 0,
  { rw [n0, nat.div_zero, nat.div_zero] },
  { rw [← mod_add_div m n] { occs := occurrences.pos [2] },
    rw [add_tsub_cancel_left, mul_div_right _ (nat.pos_of_ne_zero n0)] }
end

/-- `m` is not divisible by `n` if it is between `n * k` and `n * (k + 1)` for some `k`. -/
lemma not_dvd_of_between_consec_multiples (h1 : n * k < m) (h2 : m < n * (k + 1)) : ¬ n ∣ m :=
begin
  rintro ⟨d, rfl⟩,
  exact monotone.ne_of_lt_of_lt_nat (covariant.monotone_of_const n) k h1 h2 d rfl
end

/-! ### `find` -/
section find

variables {p q : ℕ → Prop} [decidable_pred p] [decidable_pred q]

@[simp] lemma find_pos (h : ∃ n : ℕ, p n) : 0 < nat.find h ↔ ¬ p 0 :=
by rw [pos_iff_ne_zero, ne, nat.find_eq_zero]

lemma find_add {hₘ : ∃ m, p (m + n)} {hₙ : ∃ n, p n} (hn : n ≤ nat.find hₙ) :
  nat.find hₘ + n = nat.find hₙ :=
begin
  refine ((le_find_iff _ _).2 (λ m hm hpm, hm.not_le _)).antisymm _,
  { have hnm : n ≤ m := hn.trans (find_le hpm),
    refine add_le_of_le_tsub_right_of_le hnm (find_le _),
    rwa tsub_add_cancel_of_le hnm },
  { rw ←tsub_le_iff_right,
    refine (le_find_iff _ _).2 (λ m hm hpm, hm.not_le _),
    rw tsub_le_iff_right,
    exact find_le hpm }
end

end find

/-! ### `find_greatest` -/

section find_greatest

variables {P Q : ℕ → Prop} [decidable_pred P]

lemma find_greatest_eq_iff :
  nat.find_greatest P k = m ↔ m ≤ k ∧ (m ≠ 0 → P m) ∧ (∀ ⦃n⦄, m < n → n ≤ k → ¬P n) :=
begin
  induction k with k ihk generalizing m,
  { rw [eq_comm, iff.comm],
    simp only [nonpos_iff_eq_zero, ne.def, and_iff_left_iff_imp, find_greatest_zero],
    rintro rfl,
    exact ⟨λ h, (h rfl).elim, λ n hlt heq, (hlt.ne heq.symm).elim⟩ },
  { by_cases hk : P (k + 1),
    { rw [find_greatest_eq hk], split,
      { rintro rfl,
        exact ⟨le_rfl, λ _, hk, λ n hlt hle, (hlt.not_le hle).elim⟩ },
      { rintros ⟨hle, h0, hm⟩,
        rcases decidable.eq_or_lt_of_le hle with rfl|hlt,
        exacts [rfl, (hm hlt le_rfl hk).elim] } },
    { rw [find_greatest_of_not hk, ihk],
      split,
      { rintros ⟨hle, hP, hm⟩,
        refine ⟨hle.trans k.le_succ, hP, λ n hlt hle, _⟩,
        rcases decidable.eq_or_lt_of_le hle with rfl|hlt',
        exacts [hk, hm hlt $ lt_succ_iff.1 hlt'] },
      { rintros ⟨hle, hP, hm⟩,
        refine ⟨lt_succ_iff.1 (hle.lt_of_ne _), hP, λ n hlt hle, hm hlt (hle.trans k.le_succ)⟩,
        rintro rfl,
        exact hk (hP k.succ_ne_zero) } } }
end

lemma find_greatest_eq_zero_iff : nat.find_greatest P k = 0 ↔ ∀ ⦃n⦄, 0 < n → n ≤ k → ¬P n :=
by simp [find_greatest_eq_iff]

lemma find_greatest_spec (hmb : m ≤ n) (hm : P m) : P (nat.find_greatest P n) :=
begin
  by_cases h : nat.find_greatest P n = 0,
  { cases m, { rwa h },
    exact ((find_greatest_eq_zero_iff.1 h) m.zero_lt_succ hmb hm).elim },
  { exact (find_greatest_eq_iff.1 rfl).2.1 h }
end

lemma find_greatest_le (n : ℕ) : nat.find_greatest P n ≤ n := (find_greatest_eq_iff.1 rfl).1

lemma le_find_greatest (hmb : m ≤ n) (hm : P m) : m ≤ nat.find_greatest P n :=
le_of_not_lt $ λ hlt, (find_greatest_eq_iff.1 rfl).2.2 hlt hmb hm

lemma find_greatest_mono_right (P : ℕ → Prop) [decidable_pred P] : monotone (nat.find_greatest P) :=
begin
  refine monotone_nat_of_le_succ (λ n, _),
  rw [find_greatest_succ],
  split_ifs,
  { exact (find_greatest_le n).trans (le_succ _) },
  { refl }
end

lemma find_greatest_mono_left [decidable_pred Q] (hPQ : P ≤ Q) :
  nat.find_greatest P ≤ nat.find_greatest Q :=
begin
  intro n,
  induction n with n hn,
  { refl },
  by_cases P (n + 1),
  { rw [find_greatest_eq h, find_greatest_eq (hPQ _ h)] },
  { rw find_greatest_of_not h,
    exact hn.trans (nat.find_greatest_mono_right _ $ le_succ _) }
end

lemma find_greatest_mono [decidable_pred Q] (hPQ : P ≤ Q) (hmn : m ≤ n) :
  nat.find_greatest P m ≤ nat.find_greatest Q n :=
(nat.find_greatest_mono_right _ hmn).trans $ find_greatest_mono_left hPQ _

lemma find_greatest_is_greatest (hk : nat.find_greatest P n < k) (hkb : k ≤ n) : ¬ P k :=
(find_greatest_eq_iff.1 rfl).2.2 hk hkb

lemma find_greatest_of_ne_zero (h : nat.find_greatest P n = m) (h0 : m ≠ 0) : P m :=
(find_greatest_eq_iff.1 h).2.1 h0

end find_greatest

/-! ### `bit0` and `bit1` -/

protected theorem bit0_le {n m : ℕ} (h : n ≤ m) : bit0 n ≤ bit0 m := add_le_add h h

protected theorem bit1_le {n m : ℕ} (h : n ≤ m) : bit1 n ≤ bit1 m := succ_le_succ (add_le_add h h)

theorem bit_le : ∀ (b : bool) {m n : ℕ}, m ≤ n → bit b m ≤ bit b n
| tt _ _ h := nat.bit1_le h
| ff _ _ h := nat.bit0_le h

theorem bit0_le_bit : ∀ (b) {m n : ℕ}, m ≤ n → bit0 m ≤ bit b n
| tt _ _ h := le_of_lt $ nat.bit0_lt_bit1 h
| ff _ _ h := nat.bit0_le h

theorem bit_le_bit1 : ∀ (b) {m n : ℕ}, m ≤ n → bit b m ≤ bit1 n
| ff _ _ h := le_of_lt $ nat.bit0_lt_bit1 h
| tt _ _ h := nat.bit1_le h

theorem bit_lt_bit0 : ∀ (b) {m n : ℕ}, m < n → bit b m < bit0 n
| tt _ _ h := nat.bit1_lt_bit0 h
| ff _ _ h := nat.bit0_lt h

theorem bit_lt_bit (a b) (h : m < n) : bit a m < bit b n :=
lt_of_lt_of_le (bit_lt_bit0 _ h) (bit0_le_bit _ le_rfl)

@[simp] lemma bit0_le_bit1_iff : bit0 m ≤ bit1 n ↔ m ≤ n :=
⟨λ h, by rwa [← nat.lt_succ_iff, n.bit1_eq_succ_bit0, ← n.bit0_succ_eq,
  bit0_lt_bit0, nat.lt_succ_iff] at h, λ h, le_of_lt (nat.bit0_lt_bit1 h)⟩

@[simp] lemma bit0_lt_bit1_iff : bit0 m < bit1 n ↔ m ≤ n :=
⟨λ h, bit0_le_bit1_iff.1 (le_of_lt h), nat.bit0_lt_bit1⟩

@[simp] lemma bit1_le_bit0_iff : bit1 m ≤ bit0 n ↔ m < n :=
⟨λ h, by rwa [m.bit1_eq_succ_bit0, succ_le_iff, bit0_lt_bit0] at h,
  λ h, le_of_lt (nat.bit1_lt_bit0 h)⟩

@[simp] lemma bit1_lt_bit0_iff : bit1 m < bit0 n ↔ m < n :=
⟨λ h, bit1_le_bit0_iff.1 (le_of_lt h), nat.bit1_lt_bit0⟩

@[simp] lemma one_le_bit0_iff : 1 ≤ bit0 n ↔ 0 < n :=
by { convert bit1_le_bit0_iff, refl, }

@[simp] lemma one_lt_bit0_iff : 1 < bit0 n ↔ 1 ≤ n :=
by { convert bit1_lt_bit0_iff, refl, }

@[simp] lemma bit_le_bit_iff : ∀ {b : bool}, bit b m ≤ bit b n ↔ m ≤ n
| ff := bit0_le_bit0
| tt := bit1_le_bit1

@[simp] lemma bit_lt_bit_iff : ∀ {b : bool}, bit b m < bit b n ↔ m < n
| ff := bit0_lt_bit0
| tt := bit1_lt_bit1

@[simp] lemma bit_le_bit1_iff : ∀ {b : bool}, bit b m ≤ bit1 n ↔ m ≤ n
| ff := bit0_le_bit1_iff
| tt := bit1_le_bit1

/-! ### decidability of predicates -/

instance decidable_lo_hi (lo hi : ℕ) (P : ℕ → Prop) [H : decidable_pred P] :
  decidable (∀x, lo ≤ x → x < hi → P x) :=
decidable_of_iff (∀ x < hi - lo, P (lo + x))
⟨λal x hl hh, by { have := al (x - lo) ((tsub_lt_tsub_iff_right hl).mpr hh),
  rwa [add_tsub_cancel_of_le hl] at this, },
λal x h, al _ (nat.le_add_right _ _) (lt_tsub_iff_left.mp h)⟩

instance decidable_lo_hi_le (lo hi : ℕ) (P : ℕ → Prop) [H : decidable_pred P] :
  decidable (∀x, lo ≤ x → x ≤ hi → P x) :=
decidable_of_iff (∀x, lo ≤ x → x < hi + 1 → P x) $
ball_congr $ λ x hl, imp_congr lt_succ_iff iff.rfl

end nat

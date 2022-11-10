/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import algebra.ring.divisibility
import algebra.group_with_zero.divisibility
import algebra.order.ring.canonical
import algebra.order.with_zero
import data.nat.basic

/-!
# The natural numbers as a linearly ordered commutative semiring

We also have a variety of lemmas which have been deferred from `data.nat.basic` because it is
easier to prove them with this ordered semiring instance available.

You may find that some theorems can be moved back to `data.nat.basic` by modifying their proofs.
-/

universes u v

/-! ### instances -/

instance nat.order_bot : order_bot ℕ :=
{ bot := 0, bot_le := nat.zero_le }

instance nat.subtype.order_bot (s : set ℕ) [decidable_pred (∈ s)] [h : nonempty s] :
  order_bot s :=
{ bot := ⟨nat.find (nonempty_subtype.1 h), nat.find_spec (nonempty_subtype.1 h)⟩,
  bot_le := λ x, nat.find_min' _ x.2 }

instance nat.subtype.semilattice_sup (s : set ℕ) :
  semilattice_sup s :=
{ ..subtype.linear_order s,
  ..linear_order.to_lattice }

lemma nat.subtype.coe_bot {s : set ℕ} [decidable_pred (∈ s)]
  [h : nonempty s] : ((⊥ : s) : ℕ) = nat.find (nonempty_subtype.1 h) := rfl

instance : linear_ordered_comm_semiring ℕ :=
{ lt                         := nat.lt,
  add_le_add_left            := @nat.add_le_add_left,
  le_of_add_le_add_left      := @nat.le_of_add_le_add_left,
  zero_le_one                := nat.le_of_lt (nat.zero_lt_succ 0),
  mul_lt_mul_of_pos_left     := @nat.mul_lt_mul_of_pos_left,
  mul_lt_mul_of_pos_right    := @nat.mul_lt_mul_of_pos_right,
  decidable_eq               := nat.decidable_eq,
  exists_pair_ne             := ⟨0, 1, ne_of_lt nat.zero_lt_one⟩,
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
{ exists_add_of_le := λ a b h, (nat.le.dest h).imp $ λ _, eq.symm,
  le_self_add := nat.le_add_right,
  eq_zero_or_eq_zero_of_mul_eq_zero   := λ a b, nat.eq_zero_of_mul_eq_zero,
  .. nat.nontrivial,
  .. nat.order_bot,
  .. (infer_instance : ordered_add_comm_monoid ℕ),
  .. (infer_instance : linear_ordered_semiring ℕ),
  .. (infer_instance : comm_semiring ℕ) }

instance : canonically_linear_ordered_add_monoid ℕ :=
{ .. (infer_instance : canonically_ordered_add_monoid ℕ),
  .. nat.linear_order }

variables {m n k : ℕ}
namespace nat

/-! ### Equalities and inequalities involving zero and one -/

lemma one_le_iff_ne_zero {n : ℕ} : 1 ≤ n ↔ n ≠ 0 :=
(show 1 ≤ n ↔ 0 < n, from iff.rfl).trans pos_iff_ne_zero

lemma one_lt_iff_ne_zero_and_ne_one : ∀ {n : ℕ}, 1 < n ↔ n ≠ 0 ∧ n ≠ 1
| 0     := dec_trivial
| 1     := dec_trivial
| (n+2) := dec_trivial

protected theorem mul_ne_zero {n m : ℕ} (n0 : n ≠ 0) (m0 : m ≠ 0) : n * m ≠ 0
| nm := (eq_zero_of_mul_eq_zero nm).elim n0 m0

@[simp] protected theorem mul_eq_zero {a b : ℕ} : a * b = 0 ↔ a = 0 ∨ b = 0 :=
iff.intro eq_zero_of_mul_eq_zero (by simp [or_imp_distrib] {contextual := tt})

@[simp] protected theorem zero_eq_mul {a b : ℕ} : 0 = a * b ↔ a = 0 ∨ b = 0 :=
by rw [eq_comm, nat.mul_eq_zero]

lemma eq_zero_of_double_le {a : ℕ} (h : 2 * a ≤ a) : a = 0 :=
add_right_eq_self.mp $ le_antisymm ((two_mul a).symm.trans_le h) le_add_self

lemma eq_zero_of_mul_le {a b : ℕ} (hb : 2 ≤ b) (h : b * a ≤ a) : a = 0 :=
eq_zero_of_double_le $ le_trans (nat.mul_le_mul_right _ hb) h

lemma zero_max {m : ℕ} : max 0 m = m :=
max_eq_right (zero_le _)

@[simp] lemma min_eq_zero_iff {m n : ℕ} : min m n = 0 ↔ m = 0 ∨ n = 0 :=
begin
  split,
  { intro h,
    cases le_total n m with H H,
    { simpa [H] using or.inr h },
    { simpa [H] using or.inl h } },
  { rintro (rfl|rfl);
    simp }
end

@[simp] lemma max_eq_zero_iff {m n : ℕ} : max m n = 0 ↔ m = 0 ∧ n = 0 :=
begin
  split,
  { intro h,
    cases le_total n m with H H,
    { simp only [H, max_eq_left] at h,
      exact ⟨h, le_antisymm (H.trans h.le) (zero_le _)⟩ },
    { simp only [H, max_eq_right] at h,
      exact ⟨le_antisymm (H.trans h.le) (zero_le _), h⟩ } },
  { rintro ⟨rfl, rfl⟩,
    simp }
end

lemma add_eq_max_iff {n m : ℕ} :
  n + m = max n m ↔ n = 0 ∨ m = 0 :=
begin
  rw ←min_eq_zero_iff,
  cases le_total n m with H H;
  simp [H]
end

lemma add_eq_min_iff {n m : ℕ} :
  n + m = min n m ↔ n = 0 ∧ m = 0 :=
begin
  rw ←max_eq_zero_iff,
  cases le_total n m with H H;
  simp [H]
end

lemma one_le_of_lt {n m : ℕ} (h : n < m) : 1 ≤ m :=
lt_of_le_of_lt (nat.zero_le _) h

theorem eq_one_of_mul_eq_one_right {m n : ℕ} (H : m * n = 1) : m = 1 :=
eq_one_of_dvd_one ⟨n, H.symm⟩

theorem eq_one_of_mul_eq_one_left {m n : ℕ} (H : m * n = 1) : n = 1 :=
eq_one_of_mul_eq_one_right (by rwa mul_comm)

/-! ### `succ` -/

lemma two_le_iff : ∀ n, 2 ≤ n ↔ n ≠ 0 ∧ n ≠ 1
| 0 := by simp
| 1 := by simp
| (n+2) := by simp

@[simp] lemma lt_one_iff {n : ℕ} : n < 1 ↔ n = 0 :=
lt_succ_iff.trans le_zero_iff

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

lemma add_eq_one_iff : ∀ {a b : ℕ}, a + b = 1 ↔ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)
| 0     0     := dec_trivial
| 1     0     := dec_trivial
| (a+2) _     := by rw add_right_comm; exact dec_trivial
| _     (b+1) := by rw [← add_assoc]; simp only [nat.succ_inj', nat.succ_ne_zero]; simp

theorem le_add_one_iff {i j : ℕ} : i ≤ j + 1 ↔ (i ≤ j ∨ i = j + 1) :=
⟨λ h,
  match nat.eq_or_lt_of_le h with
  | or.inl h := or.inr h
  | or.inr h := or.inl $ nat.le_of_succ_le_succ h
  end,
  or.rec (λ h, le_trans h $ nat.le_add_right _ _) le_of_eq⟩

lemma le_and_le_add_one_iff {x a : ℕ} :
  a ≤ x ∧ x ≤ a + 1 ↔ x = a ∨ x = a + 1 :=
begin
  rw [le_add_one_iff, and_or_distrib_left, ←le_antisymm_iff, eq_comm, and_iff_right_of_imp],
  rintro rfl,
  exact a.le_succ,
end

lemma add_succ_lt_add {a b c d : ℕ} (hab : a < b) (hcd : c < d) : a + c + 1 < b + d :=
begin
  rw add_assoc,
  exact add_lt_add_of_lt_of_le hab (nat.succ_le_iff.2 hcd)
end

/-! ### `pred` -/

lemma pred_le_iff {n m : ℕ} : pred n ≤ m ↔ n ≤ succ m :=
⟨le_succ_of_pred_le, by { cases n, { exact λ h, zero_le m }, exact le_of_succ_le_succ }⟩

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

lemma lt_pred_iff {n m : ℕ} : n < pred m ↔ succ n < m :=
show n < m - 1 ↔ n + 1 < m, from lt_tsub_iff_right

lemma lt_of_lt_pred {a b : ℕ} (h : a < b - 1) : a < b :=
lt_of_succ_lt (lt_pred_iff.1 h)

lemma le_or_le_of_add_eq_add_pred {a b c d : ℕ} (h : c + d = a + b - 1) : a ≤ c ∨ b ≤ d :=
begin
  cases le_or_lt a c with h' h'; [left, right],
  { exact h', },
  { replace h' := add_lt_add_right h' d, rw h at h',
    cases b.eq_zero_or_pos with hb hb, { rw hb, exact zero_le d, },
    rw [a.add_sub_assoc hb, add_lt_add_iff_left] at h',
    exact nat.le_of_pred_lt h', },
end

/-- A version of `nat.sub_succ` in the form `_ - 1` instead of `nat.pred _`. -/
lemma sub_succ' (a b : ℕ) : a - b.succ = a - b - 1 := rfl

/-! ### `mul` -/

lemma mul_eq_one_iff : ∀ {a b : ℕ}, a * b = 1 ↔ a = 1 ∧ b = 1
| 0     0     := dec_trivial
| 0     1     := dec_trivial
| 1     0     := dec_trivial
| (a+2) 0     := by simp
| 0     (b+2) := by simp
| (a+1) (b+1) := ⟨
  λ h, by simp only [add_mul, mul_add, mul_add, one_mul, mul_one,
    (add_assoc _ _ _).symm, nat.succ_inj', add_eq_zero_iff] at h; simp [h.1.2, h.2],
  λ h, by simp only [h, mul_one]⟩

lemma succ_mul_pos (m : ℕ) (hn : 0 < n) : 0 < (succ m) * n :=
mul_pos (succ_pos m) hn

theorem mul_self_le_mul_self {n m : ℕ} (h : n ≤ m) : n * n ≤ m * m :=
mul_le_mul h h (zero_le _) (zero_le _)

theorem mul_self_lt_mul_self : Π {n m : ℕ}, n < m → n * n < m * m
| 0        m h := mul_pos h h
| (succ n) m h := mul_lt_mul h (le_of_lt h) (succ_pos _) (zero_le _)

theorem mul_self_le_mul_self_iff {n m : ℕ} : n ≤ m ↔ n * n ≤ m * m :=
⟨mul_self_le_mul_self, le_imp_le_of_lt_imp_lt mul_self_lt_mul_self⟩

theorem mul_self_lt_mul_self_iff {n m : ℕ} : n < m ↔ n * n < m * m :=
le_iff_le_iff_lt_iff_lt.1 mul_self_le_mul_self_iff

theorem le_mul_self : Π (n : ℕ), n ≤ n * n
| 0     := le_rfl
| (n+1) := by simp

lemma le_mul_of_pos_left {m n : ℕ} (h : 0 < n) : m ≤ n * m :=
begin
  conv {to_lhs, rw [← one_mul(m)]},
  exact mul_le_mul_of_nonneg_right h.nat_succ_le dec_trivial,
end

lemma le_mul_of_pos_right {m n : ℕ} (h : 0 < n) : m ≤ m * n :=
begin
  conv {to_lhs, rw [← mul_one(m)]},
  exact mul_le_mul_of_nonneg_left h.nat_succ_le dec_trivial,
end

theorem mul_self_inj {n m : ℕ} : n * n = m * m ↔ n = m :=
le_antisymm_iff.trans (le_antisymm_iff.trans
  (and_congr mul_self_le_mul_self_iff mul_self_le_mul_self_iff)).symm

lemma le_add_pred_of_pos (n : ℕ) {i : ℕ} (hi : i ≠ 0) : n ≤ i + (n - 1) :=
begin
  refine le_trans _ (add_tsub_le_assoc),
  simp [add_comm, nat.add_sub_assoc, one_le_iff_ne_zero.2 hi]
end

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
| 0 (b + 1) h := hb _
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

/-- A subset of `ℕ` containing `b : ℕ` and closed under `nat.succ` contains every `n ≥ b`. -/
lemma set_induction_bounded {b : ℕ} {S : set ℕ} (hb : b ∈ S) (h_ind: ∀ k : ℕ, k ∈ S → k + 1 ∈ S)
  {n : ℕ} (hbn : b ≤ n) : n ∈ S :=
@le_rec_on (λ n, n ∈ S) b n hbn h_ind hb

/-- A subset of `ℕ` containing zero and closed under `nat.succ` contains all of `ℕ`. -/
lemma set_induction {S : set ℕ} (hb : 0 ∈ S) (h_ind: ∀ k : ℕ, k ∈ S → k + 1 ∈ S) (n : ℕ) : n ∈ S :=
set_induction_bounded hb h_ind (zero_le n)

lemma set_eq_univ {S : set ℕ} : S = set.univ ↔ 0 ∈ S ∧ ∀ k : ℕ, k ∈ S → k + 1 ∈ S :=
⟨by rintro rfl; simp, λ ⟨h0, hs⟩, set.eq_univ_of_forall (set_induction h0 hs)⟩

/-! ### `div` -/


protected lemma div_le_of_le_mul' {m n : ℕ} {k} (h : m ≤ k * n) : m / k ≤ n :=
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

protected lemma div_lt_of_lt_mul {m n k : ℕ} (h : m < n * k) : m / n < k :=
lt_of_mul_lt_mul_left
  (calc n * (m / n) ≤ m % n + n * (m / n) : nat.le_add_left _ _
    ... = m : mod_add_div _ _
    ... < n * k : h)
  (nat.zero_le n)


protected lemma div_eq_zero_iff {a b : ℕ} (hb : 0 < b) : a / b = 0 ↔ a < b :=
⟨λ h, by rw [← mod_add_div a b, h, mul_zero, add_zero]; exact mod_lt _ hb,
  λ h, by rw [← mul_right_inj' hb.ne', ← @add_left_cancel_iff _ _ (a % b), mod_add_div,
    mod_eq_of_lt h, mul_zero, add_zero]⟩

protected lemma div_eq_zero {a b : ℕ} (hb : a < b) : a / b = 0 :=
(nat.div_eq_zero_iff $ (zero_le a).trans_lt hb).mpr hb

lemma eq_zero_of_le_div {a b : ℕ} (hb : 2 ≤ b) (h : a ≤ a / b) : a = 0 :=
eq_zero_of_mul_le hb $
  by rw mul_comm; exact (nat.le_div_iff_mul_le' (lt_of_lt_of_le dec_trivial hb)).1 h


lemma div_mul_div_le_div (a b c : ℕ) : ((a / c) * b) / a ≤ b / c :=
if ha0 : a = 0 then by simp [ha0]
else calc a / c * b / a ≤ b * a / c / a :
    nat.div_le_div_right (by rw [mul_comm];
        exact mul_div_le_mul_div_assoc _ _ _)
  ... = b / c : by rw [nat.div_div_eq_div_mul, mul_comm b, mul_comm c,
      nat.mul_div_mul _ _ (nat.pos_of_ne_zero ha0)]

lemma eq_zero_of_le_half {a : ℕ} (h : a ≤ a / 2) : a = 0 :=
eq_zero_of_le_div le_rfl h

protected lemma lt_div_iff_mul_lt {n d : ℕ} (hnd : d ∣ n) (a : ℕ) : a < n / d ↔ d * a < n :=
begin
  rcases d.eq_zero_or_pos with rfl | hd0, { simp [zero_dvd_iff.mp hnd] },
  rw [←mul_lt_mul_left hd0, ←nat.eq_mul_of_div_eq_right hnd rfl],
end

lemma div_eq_iff_eq_of_dvd_dvd {n x y : ℕ} (hn : n ≠ 0) (hx : x ∣ n) (hy : y ∣ n) :
  n / x = n / y ↔ x = y :=
begin
  split,
  { intros h,
    rw ←mul_right_inj' hn,
    apply nat.eq_mul_of_div_eq_left (dvd_mul_of_dvd_left hy x),
    rw [eq_comm, mul_comm, nat.mul_div_assoc _ hy],
    exact nat.eq_mul_of_div_eq_right hx h },
  { intros h, rw h },
end

lemma mul_div_mul_comm_of_dvd_dvd {a b c d : ℕ} (hac : c ∣ a) (hbd : d ∣ b) :
  a * b / (c * d) = a / c * (b / d) :=
begin
  rcases c.eq_zero_or_pos with rfl | hc0, { simp },
  rcases d.eq_zero_or_pos with rfl | hd0, { simp },
  obtain ⟨k1, rfl⟩ := hac,
  obtain ⟨k2, rfl⟩ := hbd,
  rw [mul_mul_mul_comm, nat.mul_div_cancel_left _ hc0, nat.mul_div_cancel_left _ hd0,
      nat.mul_div_cancel_left _ (mul_pos hc0 hd0)],
end


/-! ### `mod`, `dvd` -/

lemma two_mul_odd_div_two {n : ℕ} (hn : n % 2 = 1) : 2 * (n / 2) = n - 1 :=
by conv {to_rhs, rw [← nat.mod_add_div n 2, hn, add_tsub_cancel_left]}

lemma div_dvd_of_dvd {a b : ℕ} (h : b ∣ a) : (a / b) ∣ a :=
⟨b, (nat.div_mul_cancel h).symm⟩

protected lemma div_div_self {a b : ℕ} (h : b ∣ a) (ha : a ≠ 0) : a / (a / b) = b :=
begin
  rcases h with ⟨a, rfl⟩,
  rw mul_ne_zero_iff at ha,
  rw [nat.mul_div_right _ (nat.pos_of_ne_zero ha.1), nat.mul_div_left _ (nat.pos_of_ne_zero ha.2)]
end

lemma mod_mul_right_div_self (a b c : ℕ) : a % (b * c) / b = (a / b) % c :=
begin
  rcases nat.eq_zero_or_pos b with rfl|hb, { simp },
  rcases nat.eq_zero_or_pos c with rfl|hc, { simp },
  conv_rhs { rw ← mod_add_div a (b * c) },
  rw [mul_assoc, nat.add_mul_div_left _ _ hb, add_mul_mod_self_left,
    mod_eq_of_lt (nat.div_lt_of_lt_mul (mod_lt _ (mul_pos hb hc)))]
end

lemma mod_mul_left_div_self (a b c : ℕ) : a % (c * b) / b = (a / b) % c :=
by rw [mul_comm c, mod_mul_right_div_self]

@[simp] protected theorem dvd_one {n : ℕ} : n ∣ 1 ↔ n = 1 :=
⟨eq_one_of_dvd_one, λ e, e.symm ▸ dvd_rfl⟩

@[simp] protected theorem not_two_dvd_bit1 (n : ℕ) : ¬ 2 ∣ bit1 n :=
by { rw [bit1, nat.dvd_add_right two_dvd_bit0, nat.dvd_one], cc }

/-- A natural number `m` divides the sum `m + n` if and only if `m` divides `n`.-/
@[simp] protected lemma dvd_add_self_left {m n : ℕ} :
  m ∣ m + n ↔ m ∣ n :=
nat.dvd_add_right (dvd_refl m)

/-- A natural number `m` divides the sum `n + m` if and only if `m` divides `n`.-/
@[simp] protected lemma dvd_add_self_right {m n : ℕ} :
  m ∣ n + m ↔ m ∣ n :=
nat.dvd_add_left (dvd_refl m)

-- TODO: update `nat.dvd_sub` in core
lemma dvd_sub' {k m n : ℕ} (h₁ : k ∣ m) (h₂ : k ∣ n) : k ∣ m - n :=
begin
  cases le_total n m with H H,
  { exact dvd_sub H h₁ h₂ },
  { rw tsub_eq_zero_iff_le.mpr H,
    exact dvd_zero k },
end

lemma not_dvd_of_pos_of_lt {a b : ℕ} (h1 : 0 < b) (h2 : b < a) : ¬ a ∣ b :=
begin
  rintros ⟨c, rfl⟩,
  rcases nat.eq_zero_or_pos c with (rfl | hc),
  { exact lt_irrefl 0 h1 },
  { exact not_lt.2 (le_mul_of_pos_right hc) h2 },
end

lemma succ_div : ∀ (a b : ℕ), (a + 1) / b =
  a / b + if b ∣ a + 1 then 1 else 0
| a     0     := by simp
| 0     1     := by simp
| 0     (b+2) := have hb2 : b + 2 > 1, from dec_trivial,
  by simp [ne_of_gt hb2, div_eq_of_lt hb2]
| (a+1) (b+1) := begin
  rw [nat.div_def], conv_rhs { rw nat.div_def },
  by_cases hb_eq_a : b = a + 1,
  { simp [hb_eq_a, le_refl] },
  by_cases hb_le_a1 : b ≤ a + 1,
  { have hb_le_a : b ≤ a, from le_of_lt_succ (lt_of_le_of_ne hb_le_a1 hb_eq_a),
    have h₁ : (0 < b + 1 ∧ b + 1 ≤ a + 1 + 1),
      from ⟨succ_pos _, (add_le_add_iff_right _).2 hb_le_a1⟩,
    have h₂ : (0 < b + 1 ∧ b + 1 ≤ a + 1),
      from ⟨succ_pos _, (add_le_add_iff_right _).2 hb_le_a⟩,
    have dvd_iff : b + 1 ∣ a - b + 1 ↔  b + 1 ∣ a + 1 + 1,
    { rw [nat.dvd_add_iff_left (dvd_refl (b + 1)),
        ← add_tsub_add_eq_tsub_right a 1 b, add_comm (_ - _), add_assoc,
        tsub_add_cancel_of_le (succ_le_succ hb_le_a), add_comm 1] },
    have wf : a - b < a + 1, from lt_succ_of_le tsub_le_self,
    rw [if_pos h₁, if_pos h₂, add_tsub_add_eq_tsub_right, ← tsub_add_eq_add_tsub hb_le_a,
      by exact have _ := wf, succ_div (a - b),
      add_tsub_add_eq_tsub_right],
    simp [dvd_iff, succ_eq_add_one, add_comm 1, add_assoc] },
  { have hba : ¬ b ≤ a,
      from not_le_of_gt (lt_trans (lt_succ_self a) (lt_of_not_ge hb_le_a1)),
    have hb_dvd_a : ¬ b + 1 ∣ a + 2,
      from λ h, hb_le_a1 (le_of_succ_le_succ (le_of_dvd (succ_pos _) h)),
    simp [hba, hb_le_a1, hb_dvd_a], }
end

lemma succ_div_of_dvd {a b : ℕ} (hba : b ∣ a + 1) :
  (a + 1) / b = a / b + 1 :=
by rw [succ_div, if_pos hba]

lemma succ_div_of_not_dvd {a b : ℕ} (hba : ¬ b ∣ a + 1) :
  (a + 1) / b = a / b :=
by rw [succ_div, if_neg hba, add_zero]

lemma dvd_iff_div_mul_eq (n d : ℕ) : d ∣ n ↔ n / d * d = n :=
⟨λ h, nat.div_mul_cancel h, λ h, dvd.intro_left (n / d) h⟩

lemma dvd_iff_le_div_mul (n d : ℕ) : d ∣ n ↔ n ≤ n / d * d :=
((dvd_iff_div_mul_eq _ _).trans le_antisymm_iff).trans (and_iff_right (div_mul_le_self n d))

lemma dvd_iff_dvd_dvd (n d : ℕ) : d ∣ n ↔ ∀ k : ℕ, k ∣ d → k ∣ n :=
⟨λ h k hkd, dvd_trans hkd h, λ h, h _ dvd_rfl⟩

/--  If `a` and `b` are equal mod `c`, `a - b` is zero mod `c`. -/
lemma sub_mod_eq_zero_of_mod_eq {a b c : ℕ} (h : a % c = b % c) : (a - b) % c = 0 :=
by rw [←nat.mod_add_div a c, ←nat.mod_add_div b c, ←h, tsub_add_eq_tsub_tsub, add_tsub_cancel_left,
       ←mul_tsub, nat.mul_mod_right]

@[simp] lemma one_mod (n : ℕ) : 1 % (n + 2) = 1 := nat.mod_eq_of_lt (add_lt_add_right n.succ_pos 1)

lemma dvd_sub_mod (k : ℕ) : n ∣ (k - (k % n)) :=
⟨k / n, tsub_eq_of_eq_add_rev (nat.mod_add_div k n).symm⟩

lemma add_mod_eq_ite {a b n : ℕ} :
  (a + b) % n = if n ≤ a % n + b % n then a % n + b % n - n else a % n + b % n :=
begin
  cases n, { simp },
  rw nat.add_mod,
  split_ifs with h,
  { rw [nat.mod_eq_sub_mod h, nat.mod_eq_of_lt],
    exact (tsub_lt_iff_right h).mpr
        (nat.add_lt_add (a.mod_lt n.zero_lt_succ) (b.mod_lt n.zero_lt_succ)) },
  { exact nat.mod_eq_of_lt (lt_of_not_ge h) }
end

lemma dvd_div_of_mul_dvd {a b c : ℕ} (h : a * b ∣ c) : b ∣ c / a :=
if ha : a = 0 then
  by simp [ha]
else
  have ha : 0 < a, from nat.pos_of_ne_zero ha,
  have h1 : ∃ d, c = a * b * d, from h,
  let ⟨d, hd⟩ := h1 in
  have h2 : c / a = b * d, from nat.div_eq_of_eq_mul_right ha (by simpa [mul_assoc] using hd),
  show ∃ d, c / a = b * d, from ⟨d, h2⟩

@[simp] lemma dvd_div_iff {a b c : ℕ} (hbc : c ∣ b) : a ∣ b / c ↔ c * a ∣ b :=
⟨λ h, mul_dvd_of_dvd_div hbc h, λ h, dvd_div_of_mul_dvd h⟩

lemma div_mul_div_comm {a b c d : ℕ} (hab : b ∣ a) (hcd : d ∣ c) :
      (a / b) * (c / d) = (a * c) / (b * d) :=
have exi1 : ∃ x, a = b * x, from hab,
have exi2 : ∃ y, c = d * y, from hcd,
if hb : b = 0 then by simp [hb]
else have 0 < b, from nat.pos_of_ne_zero hb,
if hd : d = 0 then by simp [hd]
else have 0 < d, from nat.pos_of_ne_zero hd,
begin
  cases exi1 with x hx, cases exi2 with y hy,
  rw [hx, hy, nat.mul_div_cancel_left, nat.mul_div_cancel_left],
  symmetry,
  apply nat.div_eq_of_eq_mul_left,
  apply mul_pos,
  repeat {assumption},
  cc
end

@[simp]
lemma div_div_div_eq_div : ∀ {a b c : ℕ} (dvd : b ∣ a) (dvd2 : a ∣ c), (c / (a / b)) / b = c / a
| 0 _ := by simp
| (a + 1) 0 := λ _ dvd _, by simpa using dvd
| (a + 1) (c + 1) :=
have a_split : a + 1 ≠ 0 := succ_ne_zero a,
have c_split : c + 1 ≠ 0 := succ_ne_zero c,
λ b dvd dvd2,
begin
  rcases dvd2 with ⟨k, rfl⟩,
  rcases dvd with ⟨k2, pr⟩,
  have k2_nonzero : k2 ≠ 0 := λ k2_zero, by simpa [k2_zero] using pr,
  rw [nat.mul_div_cancel_left k (nat.pos_of_ne_zero a_split), pr,
    nat.mul_div_cancel_left k2 (nat.pos_of_ne_zero c_split), nat.mul_comm ((c + 1) * k2) k,
    ←nat.mul_assoc k (c + 1) k2, nat.mul_div_cancel _ (nat.pos_of_ne_zero k2_nonzero),
    nat.mul_div_cancel _ (nat.pos_of_ne_zero c_split)],
end

/-- If a small natural number is divisible by a larger natural number,
the small number is zero. -/
lemma eq_zero_of_dvd_of_lt {a b : ℕ} (w : a ∣ b) (h : b < a) : b = 0 :=
nat.eq_zero_of_dvd_of_div_eq_zero w
  ((nat.div_eq_zero_iff (lt_of_le_of_lt (zero_le b) h)).elim_right h)


lemma div_eq_self {a b : ℕ} : a / b = a ↔ a = 0 ∨ b = 1 :=
begin
  split,
  { intro,
    cases b,
    { simp * at * },
    { cases b,
      { right, refl },
      { left,
        have : a / (b + 2) ≤ a / 2 := div_le_div_left (by simp) dec_trivial,
        refine eq_zero_of_le_half _,
        simp * at * } } },
  { rintros (rfl|rfl); simp }
end

lemma div_eq_sub_mod_div {m n : ℕ} : m / n = (m - m % n) / n :=
begin
  by_cases n0 : n = 0,
  { rw [n0, nat.div_zero, nat.div_zero] },
  { rw [← mod_add_div m n] { occs := occurrences.pos [2] },
    rw [add_tsub_cancel_left, mul_div_right _ (nat.pos_of_ne_zero n0)] }
end

@[simp] lemma mod_div_self (m n : ℕ) : m % n / n = 0 :=
begin
  cases n,
  { exact (m % 0).div_zero },
  { exact nat.div_eq_zero (m.mod_lt n.succ_pos) }
end

/-- `n` is not divisible by `a` if it is between `a * k` and `a * (k + 1)` for some `k`. -/
lemma not_dvd_of_between_consec_multiples {n a k : ℕ} (h1 : a * k < n) (h2 : n < a * (k + 1)) :
  ¬ a ∣ n :=
begin
  rintro ⟨d, rfl⟩,
  exact monotone.ne_of_lt_of_lt_nat (covariant.monotone_of_const a) k h1 h2 d rfl,
end

/-- `n` is not divisible by `a` iff it is between `a * k` and `a * (k + 1)` for some `k`. -/
lemma not_dvd_iff_between_consec_multiples (n : ℕ) {a : ℕ} (ha : 0 < a) :
  (∃ k : ℕ, a * k < n ∧ n < a * (k + 1)) ↔ ¬ a ∣ n :=
begin
  refine ⟨λ ⟨k, hk1, hk2⟩, not_dvd_of_between_consec_multiples hk1 hk2,
          λ han, ⟨n/a, ⟨lt_of_le_of_ne (mul_div_le n a) _, lt_mul_div_succ _ ha⟩⟩⟩,
  exact mt (dvd.intro (n/a)) han,
end

/-- Two natural numbers are equal if and only if they have the same multiples. -/
lemma dvd_right_iff_eq {m n : ℕ} : (∀ a : ℕ, m ∣ a ↔ n ∣ a) ↔ m = n :=
⟨λ h, dvd_antisymm ((h _).mpr dvd_rfl) ((h _).mp dvd_rfl), λ h n, by rw h⟩

/-- Two natural numbers are equal if and only if they have the same divisors. -/
lemma dvd_left_iff_eq {m n : ℕ} : (∀ a : ℕ, a ∣ m ↔ a ∣ n) ↔ m = n :=
⟨λ h, dvd_antisymm ((h _).mp dvd_rfl) ((h _).mpr dvd_rfl), λ h n, by rw h⟩

/-- `dvd` is injective in the left argument -/
lemma dvd_left_injective : function.injective ((∣) : ℕ → ℕ → Prop) :=
λ m n h, dvd_right_iff_eq.mp $ λ a, iff_of_eq (congr_fun h a)

lemma div_lt_div_of_lt_of_dvd {a b d : ℕ} (hdb : d ∣ b) (h : a < b) : a / d < b / d :=
by { rw nat.lt_div_iff_mul_lt hdb, exact lt_of_le_of_lt (mul_div_le a d) h }

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

variables {P Q : ℕ → Prop} [decidable_pred P] {b : ℕ}

lemma find_greatest_eq_iff :
  nat.find_greatest P b = m ↔ m ≤ b ∧ (m ≠ 0 → P m) ∧ (∀ ⦃n⦄, m < n → n ≤ b → ¬P n) :=
begin
  induction b with b ihb generalizing m,
  { rw [eq_comm, iff.comm],
    simp only [nonpos_iff_eq_zero, ne.def, and_iff_left_iff_imp, find_greatest_zero],
    rintro rfl,
    exact ⟨λ h, (h rfl).elim, λ n hlt heq, (hlt.ne heq.symm).elim⟩ },
  { by_cases hb : P (b + 1),
    { rw [find_greatest_eq hb], split,
      { rintro rfl,
        exact ⟨le_rfl, λ _, hb, λ n hlt hle, (hlt.not_le hle).elim⟩ },
      { rintros ⟨hle, h0, hm⟩,
        rcases decidable.eq_or_lt_of_le hle with rfl|hlt,
        exacts [rfl, (hm hlt le_rfl hb).elim] } },
    { rw [find_greatest_of_not hb, ihb],
      split,
      { rintros ⟨hle, hP, hm⟩,
        refine ⟨hle.trans b.le_succ, hP, λ n hlt hle, _⟩,
        rcases decidable.eq_or_lt_of_le hle with rfl|hlt',
        exacts [hb, hm hlt $ lt_succ_iff.1 hlt'] },
      { rintros ⟨hle, hP, hm⟩,
        refine ⟨lt_succ_iff.1 (hle.lt_of_ne _), hP, λ n hlt hle, hm hlt (hle.trans b.le_succ)⟩,
        rintro rfl,
        exact hb (hP b.succ_ne_zero) } } }
end

lemma find_greatest_eq_zero_iff : nat.find_greatest P b = 0 ↔ ∀ ⦃n⦄, 0 < n → n ≤ b → ¬P n :=
by simp [find_greatest_eq_iff]

lemma find_greatest_spec (hmb : m ≤ b) (hm : P m) : P (nat.find_greatest P b) :=
begin
  by_cases h : nat.find_greatest P b = 0,
  { cases m, { rwa h },
    exact ((find_greatest_eq_zero_iff.1 h) m.zero_lt_succ hmb hm).elim },
  { exact (find_greatest_eq_iff.1 rfl).2.1 h }
end

lemma find_greatest_le (n : ℕ) : nat.find_greatest P n ≤ n := (find_greatest_eq_iff.1 rfl).1

lemma le_find_greatest (hmb : m ≤ b) (hm : P m) : m ≤ nat.find_greatest P b :=
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

lemma find_greatest_mono {a b : ℕ} [decidable_pred Q] (hPQ : P ≤ Q) (hab : a ≤ b) :
  nat.find_greatest P a ≤ nat.find_greatest Q b :=
(nat.find_greatest_mono_right _ hab).trans $ find_greatest_mono_left hPQ _

lemma find_greatest_is_greatest (hk : nat.find_greatest P b < k) (hkb : k ≤ b) : ¬ P k :=
(find_greatest_eq_iff.1 rfl).2.2 hk hkb

lemma find_greatest_of_ne_zero (h : nat.find_greatest P b = m) (h0 : m ≠ 0) : P m :=
(find_greatest_eq_iff.1 h).2.1 h0

end find_greatest

/-! ### `bit0` and `bit1` -/


protected theorem bit0_le {n m : ℕ} (h : n ≤ m) : bit0 n ≤ bit0 m :=
add_le_add h h

protected theorem bit1_le {n m : ℕ} (h : n ≤ m) : bit1 n ≤ bit1 m :=
succ_le_succ (add_le_add h h)

theorem bit_le : ∀ (b : bool) {n m : ℕ}, n ≤ m → bit b n ≤ bit b m
| tt n m h := nat.bit1_le h
| ff n m h := nat.bit0_le h

theorem bit0_le_bit : ∀ (b) {m n : ℕ}, m ≤ n → bit0 m ≤ bit b n
| tt m n h := le_of_lt $ nat.bit0_lt_bit1 h
| ff m n h := nat.bit0_le h

theorem bit_le_bit1 : ∀ (b) {m n : ℕ}, m ≤ n → bit b m ≤ bit1 n
| ff m n h := le_of_lt $ nat.bit0_lt_bit1 h
| tt m n h := nat.bit1_le h

theorem bit_lt_bit0 : ∀ (b) {n m : ℕ}, n < m → bit b n < bit0 m
| tt n m h := nat.bit1_lt_bit0 h
| ff n m h := nat.bit0_lt h

theorem bit_lt_bit (a b) {n m : ℕ} (h : n < m) : bit a n < bit b m :=
lt_of_lt_of_le (bit_lt_bit0 _ h) (bit0_le_bit _ le_rfl)

@[simp] lemma bit0_le_bit1_iff : bit0 k ≤ bit1 n ↔ k ≤ n :=
⟨λ h, by rwa [← nat.lt_succ_iff, n.bit1_eq_succ_bit0, ← n.bit0_succ_eq,
  bit0_lt_bit0, nat.lt_succ_iff] at h, λ h, le_of_lt (nat.bit0_lt_bit1 h)⟩

@[simp] lemma bit0_lt_bit1_iff : bit0 k < bit1 n ↔ k ≤ n :=
⟨λ h, bit0_le_bit1_iff.1 (le_of_lt h), nat.bit0_lt_bit1⟩

@[simp] lemma bit1_le_bit0_iff : bit1 k ≤ bit0 n ↔ k < n :=
⟨λ h, by rwa [k.bit1_eq_succ_bit0, succ_le_iff, bit0_lt_bit0] at h,
  λ h, le_of_lt (nat.bit1_lt_bit0 h)⟩

@[simp] lemma bit1_lt_bit0_iff : bit1 k < bit0 n ↔ k < n :=
⟨λ h, bit1_le_bit0_iff.1 (le_of_lt h), nat.bit1_lt_bit0⟩

@[simp] lemma one_le_bit0_iff : 1 ≤ bit0 n ↔ 0 < n :=
by { convert bit1_le_bit0_iff, refl, }

@[simp] lemma one_lt_bit0_iff : 1 < bit0 n ↔ 1 ≤ n :=
by { convert bit1_lt_bit0_iff, refl, }

@[simp] lemma bit_le_bit_iff : ∀ {b : bool}, bit b k ≤ bit b n ↔ k ≤ n
| ff := bit0_le_bit0
| tt := bit1_le_bit1

@[simp] lemma bit_lt_bit_iff : ∀ {b : bool}, bit b k < bit b n ↔ k < n
| ff := bit0_lt_bit0
| tt := bit1_lt_bit1

@[simp] lemma bit_le_bit1_iff : ∀ {b : bool}, bit b k ≤ bit1 n ↔ k ≤ n
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

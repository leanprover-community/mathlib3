/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Yaël Dillies
-/
import data.nat.pow
import tactic.by_contra
import algebra.order.floor

/-!
# Natural number logarithms

This file defines two `ℕ`-valued analogs of the logarithm of `n : R` with base `b`:
* `log b n`: Lower logarithm, or floor **log**. Greatest `k` such that `↑b^k ≤ n`.
* `clog b n`: Upper logarithm, or **c**eil **log**. Least `k` such that `n ≤ ↑b^k`.

These are interesting because, for `1 < b`, `nat.log b` and `nat.clog b` are respectively right and
left adjoints of `nat.pow b`. See `pow_le_iff_le_log` and `le_pow_iff_clog_le`.
-/

variables {R : Type*} [linear_ordered_semiring R] [floor_semiring R]

namespace nat

/-! ### Floor logarithm -/

private def log_aux (b : ℕ) : ℕ → ℕ
| n :=
  if h : b ≤ n ∧ 1 < b then
    have n / b < n,
      from div_lt_self ((zero_lt_one.trans h.2).trans_le h.1) h.2,
    log_aux (n / b) + 1
  else 0

/-- `log b n`, is the logarithm of an element of a `floor_semiring` `n` in base `b`. It returns the
largest `k : ℕ` such that `↑b^k ≤ n`, so if `↑b^k = n`, it returns exactly `k`. -/
@[pp_nodot]
def log (b : ℕ) (n : R) : ℕ := log_aux b ⌊n⌋₊

@[simp, norm_cast] lemma log_cast (b : ℕ) (n : ℕ) : log b (n : R) = log b n :=
begin
  rw [log, log, floor_coe],
  refl,
end

lemma log_eq_zero {b : ℕ} {n : R} (hnb : n < b ∨ b ≤ 1) : log b n = 0 :=
begin
  rw [log, log_aux, ite_eq_right_iff],
  rintro ⟨hnb', hb⟩,
  exfalso,
  cases hnb,
  { obtain hn | hn := le_total 0 n,
    { rw le_floor_iff hn at hnb',
      exact hnb.not_le hnb' },
    { rw floor_of_nonpos hn at hnb',
      exact (hb.trans_le hnb').not_le zero_le_one, }, },
  { exact hb.not_le hnb },
end

lemma log_of_one_lt_of_le {b : ℕ} {n : R} (h : 1 < b) (hn : ↑b ≤ n) :
  log b n = log b (⌊n⌋₊ / b) + 1 :=
begin
  rw [log, log, log_aux],
  exact if_pos ⟨le_floor hn, h⟩,
end

/-- A special case of `log_of_one_lt_of_le` for `R = ℕ` -/
lemma log_of_one_lt_of_le' {b n : ℕ} (h : 1 < b) (hn : b ≤ n) :
  log b n = log b (n / b) + 1 :=
log_of_one_lt_of_le h $ (nat.cast_le.mpr hn).trans_eq (nat.cast_id _)

lemma log_of_lt {b : ℕ} {n : R} (hnb : n < b) : log b n = 0 :=
log_eq_zero (or.inl hnb)

lemma log_of_left_le_one {b : ℕ} {n : R} (hb : b ≤ 1) : log b n = 0 :=
log_eq_zero (or.inr hb)

lemma log_eq_zero_iff {b : ℕ} {n : R} : log b n = 0 ↔ n < b ∨ b ≤ 1 :=
begin
  refine ⟨λ h_log, _, log_eq_zero⟩,
  by_contra' h,
  have := log_of_one_lt_of_le h.2 h.1,
  rw h_log at this,
  exact succ_ne_zero _ this.symm
end

lemma log_eq_one_iff {b : ℕ} {n : R} : log b n = 1 ↔ n < b * b ∧ 1 < b ∧ ↑b ≤ n :=
-- This is best possible: if b = 2, n = 5, then 1 < b and b ≤ n but n > b * b.
begin
  refine ⟨λ h_log, _, _⟩,
  { have bound : 1 < b ∧ ↑b ≤ n,
    { contrapose h_log,
      rw [not_and_distrib, not_lt, not_le, or_comm, ←log_eq_zero_iff] at h_log,
      rw h_log,
      exact nat.zero_ne_one, },
    cases bound with one_lt_b b_le_n,
    refine ⟨_, one_lt_b, b_le_n⟩,
    rw [log_of_one_lt_of_le one_lt_b b_le_n, succ_inj',
        log_eq_zero_iff, nat.div_lt_iff_lt_mul _ _ (lt_trans zero_lt_one one_lt_b), nat.cast_id,
          floor_lt (b.cast_nonneg.trans b_le_n), nat.cast_mul] at h_log,
    exact h_log.resolve_right (λ b_small, lt_irrefl _ (lt_of_lt_of_le one_lt_b b_small)), },
  { rintros ⟨h, one_lt_b, b_le_n⟩,
    rw [log_of_one_lt_of_le one_lt_b b_le_n, succ_inj',
        log_eq_zero_iff, nat.div_lt_iff_lt_mul _ _ (lt_trans zero_lt_one one_lt_b), nat.cast_id,
        floor_lt (b.cast_nonneg.trans b_le_n), nat.cast_mul],
    exact or.inl h, },
end

@[simp] lemma log_zero_left (n : R) : log 0 n = 0 :=
log_of_left_le_one zero_le_one

@[simp] lemma log_zero_right (b : ℕ) : log b (0 : R) = 0 :=
begin
  cases b,
  { exact log_zero_left _},
  { exact log_of_lt (nat.cast_pos.mpr b.zero_lt_succ) }
end

@[simp] lemma log_one_left (n : R) : log 1 n = 0 :=
log_of_left_le_one le_rfl

@[simp] lemma log_one_right (b : ℕ) : log b (1 : R) = 0 :=
if h : b ≤ 1 then
  log_of_left_le_one h
else
  log_of_lt $ nat.cast_one.symm.trans_lt $ nat.cast_lt.mpr $ not_le.mp $ h

lemma pow_le_iff_le_log {b : ℕ} (hb : 1 < b) {x : ℕ} {y : ℕ} (hy : 1 ≤ y) :
  b^x ≤ y ↔ x ≤ log b y :=
begin
  show b^x ≤ y ↔ x ≤ log_aux b y,
  induction y using nat.strong_induction_on with y ih generalizing x,
  cases x,
  { exact iff_of_true hy (zero_le _) },
  rw [log_aux], split_ifs,
  { have b_pos : 0 < b := zero_le_one.trans_lt hb,
    rw [succ_eq_add_one, add_le_add_iff_right, ←ih (y / b) (div_lt_self hy hb)
      (nat.div_pos h.1 b_pos), le_div_iff_mul_le _ _ b_pos, pow_succ'] },
  { refine iff_of_false (λ hby, h ⟨le_trans _ hby, hb⟩) (not_succ_le_zero _),
    convert pow_mono hb.le (zero_lt_succ x),
    exact (pow_one b).symm }
end

/-- `pow ↑b` and `log b` (almost) form a Galois connection. -/
lemma pow_cast_le_iff_le_log {b : ℕ} (hb : 1 < b) {x : ℕ} {y : R} (hy : 1 ≤ y) :
  ↑b^x ≤ y ↔ x ≤ log b y :=
begin
  suffices : ∀ y', 1 ≤ y' → (b ^ x ≤ y' ↔ x ≤ log_aux b y'),
  { rw [←nat.cast_pow, ← le_floor_iff (zero_le_one.trans hy), log],
    rw ←floor_pos at hy,
    exact this _ hy, },
  intro y,
  exact pow_le_iff_le_log hb,
end

lemma log_pow {b : ℕ} (hb : 1 < b) (x : ℕ) : log b (b ^ x) = x :=
eq_of_forall_le_iff $ λ z, begin
  rw ←pow_le_iff_le_log hb (one_le_pow x _ (zero_lt_one.trans hb)),
  exact (pow_right_strict_mono hb).le_iff_le
end

variables (R)

attribute [norm_cast] cast_pow

/-- See `nat.log_pow` for the case with `R = ℕ`. -/
lemma log_pow_cast {b : ℕ} (hb : 1 < b) (x : ℕ) : log b ((b : R) ^ x) = x :=
by exact_mod_cast log_pow hb x

variables {R}

lemma log_pos {b : ℕ} {n : R} (hb : 1 < b) (hn : ↑b ≤ n) : 0 < log b n :=
begin
  have : 1 ≤ n,
  { exact_mod_cast ((nat.cast_lt.mpr hb).trans_le hn).le},
  rwa [←succ_le_iff, ←pow_cast_le_iff_le_log hb this, pow_one],
end

lemma log_mul_base (b : ℕ) (n : R) (hb : 1 < b) (hn : 1 ≤ n) : log b (n * b) = log b n + 1 :=
eq_of_forall_le_iff $ λ z, begin
  cases z,
  { simp },
  have hb' : 1 < (b : R) := by exact_mod_cast hb,
  have : 1 ≤ n * ↑b := one_le_mul_of_one_le_of_one_le hn hb'.le,
  rw [←pow_cast_le_iff_le_log hb this, pow_succ',
      (strict_mono_mul_right_of_pos (zero_le_one.trans_lt hb')).le_iff_le,
      pow_cast_le_iff_le_log hb hn, nat.succ_le_succ_iff],
end

lemma lt_pow_succ_log_self {b : ℕ} (hb : 1 < b) (x : R) :
  x < b ^ (log b x).succ :=
begin
  have hb' : (1 : R) < b := by exact_mod_cast hb,
  cases le_total x 1 with hx hx,
  { rw [log_of_lt (hx.trans_lt hb'), pow_one],
    exact hx.trans_lt hb' },
  rw [←not_le, pow_cast_le_iff_le_log hb hx, not_le],
  exact lt_succ_self _,
end

lemma pow_log_le_self {b : ℕ} (hb : 1 < b) {x : R} (hx : 1 ≤ x) : ↑b ^ log b x ≤ x :=
(pow_cast_le_iff_le_log hb hx).2 le_rfl

lemma log_le_log_of_le {b} {n m : R} (h : n ≤ m) : log b n ≤ log b m :=
begin
  cases le_or_lt b 1 with hb hb,
  { rw log_of_left_le_one hb, exact zero_le _ },
  { cases le_total n 1 with hn hn,
    { rw log_of_lt (hn.trans_lt $ by exact_mod_cast hb), exact zero_le _},
    { rw ←pow_cast_le_iff_le_log hb (hn.trans h),
      exact (pow_log_le_self hb hn).trans h } }
end

lemma log_le_log_of_left_ge {b c : ℕ} {n : R} (hc : 1 < c) (hb : c ≤ b) : log b n ≤ log c n :=
begin
  have hc' : (1 : R) < c := by exact_mod_cast hc,
  have hb' : (c : R) ≤ b := by exact_mod_cast hb,
  cases le_total n 1 with hn hn,
  { simp [log_of_lt (hn.trans_lt hc'), log_of_lt (hn.trans_lt (hc'.trans_le hb'))] },
  rw ← pow_cast_le_iff_le_log hc hn,
  calc
    (c : R) ^ log b n ≤ b ^ log b n : pow_le_pow_of_le_left (zero_lt_one.trans hc').le hb' _
                  ... ≤ n           : pow_log_le_self (lt_of_lt_of_le hc hb) hn
end

lemma log_monotone {b : ℕ} : monotone (λ n : R, log b n) :=
λ n y, log_le_log_of_le

lemma log_antitone_left {n : R} : antitone_on (λ b, log b n) (set.Ioi 1) :=
λ _ hc _ _ hb, log_le_log_of_left_ge (set.mem_Iio.1 hc) hb

@[simp] lemma log_div_mul_self (b n : ℕ) : log b (n / b * b) = log b n :=
begin
  refine eq_of_forall_le_iff (λ z, _),
  split,
  { intro h,
    exact h.trans (log_monotone (div_mul_le_self _ _)) },
  { intro h,
    rcases b with _|_|b,
    { simpa using h },
    { simpa using h },
    rcases n.zero_le.eq_or_lt with rfl|hn,
    { simpa using h },
    cases le_or_lt b.succ.succ n with hb hb,
    { cases z,
      { simp },
      have : 0 < b.succ.succ := nat.succ_pos',
      rw [←pow_le_iff_le_log _ (nat.succ_le_of_lt _), pow_succ'] at h ⊢,
      { rwa [(strict_mono_mul_right_of_pos this).le_iff_le,
             nat.le_div_iff_mul_le _ _ nat.succ_pos'] },
      all_goals { simp [hn, nat.div_pos hb nat.succ_pos'] } },
    { simpa [div_eq_of_lt, hb, log_eq_zero] using h } }
end

@[simp] lemma log_div_base (b n : ℕ) : log b (n / b) = log b n - 1 :=
begin
  cases lt_or_le n b with h h,
  { simp [div_eq_of_lt, h, log_eq_zero] },
  rcases n.zero_le.eq_or_lt with rfl|hn,
  { simp },
  rcases b with _|_|b,
  { simp },
  { simp },
  rw [←succ_inj', ←succ_inj'],
  simp_rw succ_eq_add_one,
  rw [nat.sub_add_cancel, ←log_mul_base];
  { simp [succ_le_iff, log_pos, h, nat.div_pos] },
end


private lemma add_pred_div_lt {b n : ℕ} (hb : 1 < b) (hn : 2 ≤ n) : (n + b - 1)/b < n :=
begin
  rw [div_lt_iff_lt_mul _ _ (zero_lt_one.trans hb), ←succ_le_iff, ←pred_eq_sub_one,
    succ_pred_eq_of_pos (add_pos (zero_lt_one.trans hn) (zero_lt_one.trans hb))],
  exact add_le_mul hn hb,
end

/-! ### Ceil logarithm -/

private def clog_aux (b : ℕ) : ℕ → ℕ
| n :=
  if h : 1 < b ∧ 1 < n then
    have (n + b - 1)/b < n := add_pred_div_lt h.1 h.2,
    clog_aux ((n + b - 1)/b) + 1
  else 0

/-- `clog b n`, is the upper logarithm of `n` in base `b`. It returns the smallest
`k : ℕ` such that `n ≤ b^k`, so if `↑b^k = n`, it returns exactly `k`. -/
@[pp_nodot] def clog (b : ℕ) (n : R) : ℕ := clog_aux b ⌈n⌉₊

@[simp, norm_cast] lemma clog_cast (b : ℕ) (n : ℕ) : clog b (n : R) = clog b n :=
begin
  rw [clog, clog, ceil_coe],
  refl,
end

lemma clog_of_left_le_one {b : ℕ} (hb : b ≤ 1) (n : R) : clog b n = 0 :=
by rw [clog, clog_aux, if_neg (λ h : 1 < b ∧ 1 < ⌈n⌉₊, h.1.not_le hb)]

lemma clog_of_right_le_one {n : R} (hn : n ≤ 1) (b : ℕ) : clog b n = 0 :=
by rw [clog, clog_aux,
  if_neg (λ h : 1 < b ∧ 1 < ⌈n⌉₊, h.2.not_le $ ceil_le.mpr $ hn.trans_eq nat.cast_one.symm)]

@[simp] lemma clog_zero_left (n : R) : clog 0 n = 0 :=
clog_of_left_le_one zero_le_one _

@[simp] lemma clog_zero_right (b : ℕ) : clog b (0 : R) = 0 :=
clog_of_right_le_one zero_le_one _

@[simp] lemma clog_one_left (n : R) : clog 1 n = 0 :=
clog_of_left_le_one le_rfl _

@[simp] lemma clog_one_right (b : ℕ) : clog b (1 : R) = 0 :=
clog_of_right_le_one le_rfl _

lemma clog_of_one_lt {b : ℕ} {n : R} (hb : 1 < b) (hn : 1 < n) :
  clog b n = clog b ((⌈n⌉₊ + b - 1)/b) + 1 :=
begin
  rw [clog, clog_aux, if_pos (⟨hb, lt_ceil.mpr _⟩ : 1 < b ∧ 1 < ⌈n⌉₊), clog],
  refl, -- needs floor of nat lemma
  exact_mod_cast hn,
end

lemma clog_pos {b : ℕ} {n : R} (hb : 1 < b) (hn : 1 < n) : 0 < clog b n :=
by { rw clog_of_one_lt hb hn, exact zero_lt_succ _ }

lemma clog_eq_one {b : ℕ} {n : R} (hn : 1 < n) (h : n ≤ b) : clog b n = 1 :=
begin
  have hb : 1 < b := by exact_mod_cast hn.trans_le h,
  rw [clog_of_one_lt (by exact_mod_cast hn.trans_le h) hn, clog_of_right_le_one],
  have n_pos : 0 < n := zero_lt_one.trans hn,
  have b_pos : 0 < b := zero_lt_one.trans hb,
  rw [←lt_succ_iff, nat.div_lt_iff_lt_mul _ _ (by exact_mod_cast n_pos.trans_le h), ←succ_le_iff,
    ←pred_eq_sub_one, succ_pred_eq_of_pos (add_pos (lt_ceil.2 n_pos) b_pos), succ_mul,
    one_mul],
  exact add_le_add_right (ceil_le.mpr h) _,
end

/--`clog b` and `pow b` form a Galois connection. -/
lemma le_pow_iff_clog_le {b : ℕ} (hb : 1 < b) {x : ℕ} {y : ℕ} :
  x ≤ b^y ↔ clog b x ≤ y :=
begin
  show x ≤ b^y ↔ clog_aux b x ≤ y,
  induction x using nat.strong_induction_on with x ih generalizing y,
  cases y,
  { rw [pow_zero],
    refine ⟨λ h, (clog_of_right_le_one h b).le, _⟩,
    simp_rw ←not_lt,
    contrapose!,
    exact clog_pos hb },
  have b_pos : 0 < b := zero_lt_two.trans_le hb,
  rw [clog_aux], split_ifs,
  { rw [succ_eq_add_one, add_le_add_iff_right, ←ih ((x + b - 1)/b) (add_pred_div_lt hb h.2),
      nat.div_le_iff_le_mul_add_pred b_pos,
      ← pow_succ, add_tsub_assoc_of_le (nat.succ_le_of_lt b_pos), add_le_add_iff_right] },
  { exact iff_of_true ((not_lt.1 (not_and.1 h hb)).trans $ succ_le_of_lt $ pow_pos b_pos _)
    (zero_le _) }
end

/--`clog b` and `pow b` form a Galois connection. -/
lemma le_pow_cast_iff_clog_le {b : ℕ} (hb : 1 < b) {x : R} {y : ℕ} :
  x ≤ b^y ↔ clog b x ≤ y :=
begin
  suffices : ∀ x, (x ≤ b^y ↔ clog_aux b x ≤ y),
  { rw [←nat.cast_pow, ← ceil_le, clog],
    exact this _, },
  intros x,
  exact_mod_cast le_pow_iff_clog_le hb,
end

lemma clog_pow (b x : ℕ) (hb : 1 < b) : clog b (b ^ x) = x :=
eq_of_forall_ge_iff $ λ z,
  by { rw ←le_pow_iff_clog_le hb, exact (pow_right_strict_mono hb).le_iff_le }

variables (R)

/-- See `nat.clog_pow` for the case with `R = ℕ`. -/
lemma clog_pow_cast (b x : ℕ) (hb : 1 < b) : clog b ((b : R) ^ x) = x :=
by exact_mod_cast clog_pow b x hb

variables {R}

lemma pow_pred_clog_lt_self {b : ℕ} (hb : 1 < b) {x : R} (hx : 1 < x) :
  ↑b ^ (clog b x).pred < x :=
begin
  rw [←not_le, le_pow_cast_iff_clog_le hb, not_le],
  exact pred_lt (clog_pos hb hx).ne',
end

lemma le_pow_clog {b : ℕ} (hb : 1 < b) (x : R) : x ≤ b ^ clog b x :=
(le_pow_cast_iff_clog_le hb).2 le_rfl

lemma clog_le_clog_of_le (b : ℕ) {n m : R} (h : n ≤ m) : clog b n ≤ clog b m :=
begin
  cases le_or_lt b 1 with hb hb,
  { rw clog_of_left_le_one hb, exact zero_le _ },
  { rw ←le_pow_cast_iff_clog_le hb,
    exact h.trans (le_pow_clog hb _) }
end

lemma clog_le_clog_of_left_ge {b c : ℕ} {n : R} (hc : 1 < c) (hb : c ≤ b) : clog b n ≤ clog c n :=
begin
  rw ← le_pow_cast_iff_clog_le (lt_of_lt_of_le hc hb),
  calc
    n ≤ c ^ clog c n : le_pow_clog hc _
  ... ≤ b ^ clog c n :
          by exact_mod_cast pow_le_pow_of_le_left (le_of_lt $ zero_lt_one.trans hc) hb _
end

lemma clog_monotone (b : ℕ) : monotone (clog b : R → ℕ) :=
λ x y, clog_le_clog_of_le _

lemma clog_antitone_left {n : R} : antitone_on (λ b : ℕ, clog b n) (set.Ioi 1) :=
λ _ hc _ _ hb, clog_le_clog_of_left_ge (set.mem_Iio.1 hc) hb

lemma log_le_clog (b : ℕ) (n : R) : log b n ≤ clog b n :=
begin
  obtain hb | hb := le_or_lt b 1,
  { rw log_of_left_le_one hb,
    exact zero_le _},
  cases le_or_lt 1 n with hn hn,
  { refine (pow_right_strict_mono hb).le_iff_le.1 _,
    exact_mod_cast (pow_log_le_self hb hn).trans (le_pow_clog hb _) },
  { refine (log_of_lt (hn.trans _)).trans_le (zero_le _),
    exact_mod_cast hb },
end

end nat

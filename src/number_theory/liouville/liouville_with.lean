import analysis.special_functions.pow
import number_theory.liouville.basic
import topology.instances.irrational

/-!
-/

open filter metric real set
open_locale filter topological_space

def liouville_with (p x : ℝ) : Prop :=
∃ C, ∃ᶠ n : ℕ in at_top, ∃ m : ℤ, x ≠ m / n ∧ |x - m / n| < C / n ^ p

namespace liouville_with

variables {p q x y : ℝ} {r : ℚ} {m : ℤ} {n : ℕ}

lemma exists_pos (h : liouville_with p x) :
  ∃ (C : ℝ) (h₀ : 0 < C),
    ∃ᶠ n : ℕ in at_top, 1 ≤ n ∧ ∃ m : ℤ, x ≠ m / n ∧ |x - m / n| < C / n ^ p :=
begin
  rcases h with ⟨C, hC⟩,
  refine ⟨max C 1, zero_lt_one.trans_le $ le_max_right _ _, _⟩,
  refine (hC.and_eventually (eventually_ge_at_top 1)).mono _,
  rintro n ⟨⟨m, hne, hlt⟩, hle⟩,
  refine ⟨hle, ⟨m, hne, hlt.trans_le _⟩⟩,
  exact div_le_div_of_le (rpow_nonneg_of_nonneg n.cast_nonneg _) (le_max_left _ _)
end

lemma mono (h : liouville_with p x) (hle : q ≤ p) : liouville_with q x :=
begin
  rcases h.exists_pos with ⟨C, hC₀, hC⟩,
  refine ⟨C, hC.mono _⟩, rintro n ⟨hn, m, hne, hlt⟩,
  refine ⟨m, hne, hlt.trans_le $ div_le_div_of_le_left hC₀.le _ _⟩,
  exacts [rpow_pos_of_pos (nat.cast_pos.2 hn) _,
    rpow_le_rpow_of_exponent_le (nat.one_le_cast.2 hn) hle]
end

/-- If `x` satisfies Liouville condition with exponent `p` and `q < p`, then `x`
satisfies Liouville condition with exponent `q` and constant `1`. -/
lemma frequently_lt_rpow_neg (h : liouville_with p x) (hlt : q < p) :
  ∃ᶠ n : ℕ in at_top, ∃ m : ℤ, x ≠ m / n ∧ |x - m / n| < n ^ (-q) :=
begin
  rcases h.exists_pos with ⟨C, hC₀, hC⟩,
  have : ∀ᶠ n : ℕ in at_top, C < n ^ (p - q),
    by simpa only [(∘), neg_sub, one_div] using ((tendsto_rpow_at_top (sub_pos.2 hlt)).comp
      tendsto_coe_nat_at_top_at_top).eventually (eventually_gt_at_top C),
  refine (hC.and_eventually this).mono _,
  rintro n ⟨⟨hn, m, hne, hlt⟩, hnC⟩,
  replace hn : (0 : ℝ) < n := nat.cast_pos.2 hn,
  refine ⟨m, hne, hlt.trans $ (div_lt_iff $ rpow_pos_of_pos hn _).2 _⟩,
  rwa [mul_comm, ← rpow_add hn, ← sub_eq_add_neg]
end

lemma mul_rat (h : liouville_with p x) (hr : r ≠ 0) : liouville_with p (x * r) :=
begin
  rcases h.exists_pos with ⟨C, hC₀, hC⟩,
  refine ⟨r.denom ^ p * (|r| * C), (tendsto_id.nsmul_at_top r.pos).frequently (hC.mono _)⟩,
  rintro n ⟨hn, m, hne, hlt⟩,
  have A : (↑(r.num * m) : ℝ) / ↑(r.denom • id n) = (m / n) * r,
    by simp [← div_mul_div, ← r.cast_def, mul_comm],
  refine ⟨r.num * m, _, _⟩,
  { rw A, simp [hne, hr] },
  { rw [A, ← sub_mul, abs_mul],
    simp only [smul_eq_mul, id.def, nat.cast_mul],
    refine (mul_lt_mul_of_pos_right hlt $ abs_pos.2 $ rat.cast_ne_zero.2 hr).trans_le _,
    rw [mul_rpow, mul_div_mul_left, mul_comm, mul_div_assoc],
    exacts [(rpow_pos_of_pos (nat.cast_pos.2 r.pos) _).ne', nat.cast_nonneg _, nat.cast_nonneg _] }
end

lemma mul_rat_iff (hr : r ≠ 0) : liouville_with p (x * r) ↔ liouville_with p x :=
⟨λ h, by simpa only [mul_assoc, ← rat.cast_mul, mul_inv_cancel hr, rat.cast_one, mul_one]
  using h.mul_rat (inv_ne_zero hr), λ h, h.mul_rat hr⟩

lemma rat_mul_iff (hr : r ≠ 0) : liouville_with p (r * x) ↔ liouville_with p x :=
by rw [mul_comm, mul_rat_iff hr]

lemma rat_mul (h : liouville_with p x) (hr : r ≠ 0) : liouville_with p (r * x) :=
(rat_mul_iff hr).2 h

lemma mul_int_iff (hm : m ≠ 0) : liouville_with p (x * m) ↔ liouville_with p x :=
by rw [← rat.cast_coe_int, mul_rat_iff (int.cast_ne_zero.2 hm)]

lemma mul_int (h : liouville_with p x) (hm : m ≠ 0) : liouville_with p (x * m) :=
(mul_int_iff hm).2 h

lemma int_mul_iff (hm : m ≠ 0) : liouville_with p (m * x) ↔ liouville_with p x :=
by rw [mul_comm, mul_int_iff hm]

lemma int_mul (h : liouville_with p x) (hm : m ≠ 0) : liouville_with p (m * x) :=
(int_mul_iff hm).2 h

lemma mul_nat_iff (hn : n ≠ 0) : liouville_with p (x * n) ↔ liouville_with p x :=
by rw [← rat.cast_coe_nat, mul_rat_iff (nat.cast_ne_zero.2 hn)]

lemma mul_nat (h : liouville_with p x) (hn : n ≠ 0) : liouville_with p (x * n) :=
(mul_nat_iff hn).2 h

lemma nat_mul_iff (hn : n ≠ 0) : liouville_with p (n * x) ↔  liouville_with p x:=
by rw [mul_comm, mul_nat_iff hn]

lemma nat_mul (h : liouville_with p x) (hn : n ≠ 0) : liouville_with p (n * x) :=
by { rw mul_comm, exact h.mul_nat hn }

lemma add_rat (h : liouville_with p x) (r : ℚ) : liouville_with p (x + r) :=
begin
  rcases h.exists_pos with ⟨C, hC₀, hC⟩,
  refine ⟨r.denom ^ p * C, (tendsto_id.nsmul_at_top r.pos).frequently (hC.mono _)⟩,
  rintro n ⟨hn, m, hne, hlt⟩,
  have hr : (0 : ℝ) < r.denom, from nat.cast_pos.2 r.pos,
  have hn' : (n : ℝ) ≠ 0, from nat.cast_ne_zero.2 (zero_lt_one.trans_le hn).ne',
  have : (↑(r.denom * m + r.num * n : ℤ) / ↑(r.denom • id n) : ℝ) = m / n + r,
    by simp [add_div, hr.ne', mul_div_mul_left, mul_div_mul_right, hn', ← rat.cast_def],
  refine ⟨r.denom * m + r.num * n, _⟩, rw [this, add_sub_add_right_eq_sub],
  refine ⟨by simpa, hlt.trans_le (le_of_eq _)⟩,
  have : (r.denom ^ p : ℝ) ≠ 0, from (rpow_pos_of_pos hr _).ne',
  simp [mul_rpow, nat.cast_nonneg, mul_div_mul_left, this]
end

@[simp] lemma add_rat_iff : liouville_with p (x + r) ↔ liouville_with p x :=
⟨λ h, by simpa using h.add_rat (-r), λ h, h.add_rat r⟩

@[simp] lemma rat_add_iff : liouville_with p (r + x) ↔ liouville_with p x :=
by rw [add_comm, add_rat_iff]

lemma rat_add (h : liouville_with p x) (r : ℚ) : liouville_with p (r + x) :=
add_comm x r ▸ h.add_rat r

@[simp] lemma add_int_iff : liouville_with p (x + m) ↔ liouville_with p x :=
by rw [← rat.cast_coe_int m, add_rat_iff]

@[simp] lemma int_add_iff : liouville_with p (m + x) ↔ liouville_with p x :=
by rw [add_comm, add_int_iff]

@[simp] lemma add_nat_iff : liouville_with p (x + n) ↔ liouville_with p x :=
by rw [← rat.cast_coe_nat n, add_rat_iff]

@[simp] lemma nat_add_iff : liouville_with p (n + x) ↔ liouville_with p x :=
by rw [add_comm, add_nat_iff]

lemma add_int (h : liouville_with p x) (m : ℤ) : liouville_with p (x + m) := add_int_iff.2 h

lemma int_add (h : liouville_with p x) (m : ℤ) : liouville_with p (m + x) := int_add_iff.2 h

lemma add_nat (h : liouville_with p x) (n : ℕ) : liouville_with p (x + n) := h.add_int n

lemma nat_add (h : liouville_with p x) (n : ℕ) : liouville_with p (n + x) := h.int_add n

protected lemma neg (h : liouville_with p x) : liouville_with p (-x) :=
begin
  rcases h with ⟨C, hC⟩,
  refine ⟨C, hC.mono _⟩,
  rintro n ⟨m, hne, hlt⟩,
  use (-m), simp [neg_div, abs_sub_comm _ x, *]
end

@[simp] lemma neg_iff : liouville_with p (-x) ↔ liouville_with p x :=
⟨λ h, neg_neg x ▸ h.neg, liouville_with.neg⟩

@[simp] lemma sub_rat_iff : liouville_with p (x - r) ↔ liouville_with p x :=
by rw [sub_eq_add_neg, ← rat.cast_neg, add_rat_iff]

lemma sub_rat (h : liouville_with p x) (r : ℚ) : liouville_with p (x - r) :=
sub_rat_iff.2 h

@[simp] lemma sub_int_iff : liouville_with p (x - m) ↔ liouville_with p x :=
by rw [← rat.cast_coe_int, sub_rat_iff]

lemma sub_int (h : liouville_with p x) (m : ℤ) : liouville_with p (x - m) := sub_int_iff.2 h

@[simp] lemma sub_nat_iff : liouville_with p (x - n) ↔ liouville_with p x :=
by rw [← rat.cast_coe_nat, sub_rat_iff]

lemma sub_nat (h : liouville_with p x) (n : ℕ) : liouville_with p (x - n) := sub_nat_iff.2 h

@[simp] lemma rat_sub_iff : liouville_with p (r - x) ↔ liouville_with p x :=
by simp [sub_eq_add_neg]

lemma rat_sub (h : liouville_with p x) (r : ℚ) : liouville_with p (r - x) := rat_sub_iff.2 h

@[simp] lemma int_sub_iff : liouville_with p (m - x) ↔ liouville_with p x :=
by simp [sub_eq_add_neg]

lemma int_sub (h : liouville_with p x) (m : ℤ) : liouville_with p (m - x) := int_sub_iff.2 h

@[simp] lemma nat_sub_iff : liouville_with p (n - x) ↔ liouville_with p x :=
by simp [sub_eq_add_neg]

lemma nat_sub (h : liouville_with p x) (n : ℕ) : liouville_with p (n - x) := nat_sub_iff.2 h

end liouville_with

namespace liouville

variables {x : ℝ}

lemma frequently_exists_num (hx : liouville x) (n : ℕ) :
  ∃ᶠ b : ℕ in at_top, ∃ a : ℤ, x ≠ a / b ∧ |x - a / b| < 1 / b ^ n :=
begin
  refine not_not.1 (λ H, _),
  simp only [liouville, not_forall, not_exists, not_frequently, not_and, not_lt,
    eventually_at_top] at H,
  rcases H with ⟨N, hN⟩,
  have : ∀ b > (1 : ℕ), ∀ᶠ m : ℕ in at_top, ∀ a : ℤ, (1 / b ^ m : ℝ) ≤ |x - a / b|,
  { intros b hb,
    have hb0' : (b : ℚ) ≠ 0 := (zero_lt_one.trans (nat.one_lt_cast.2 hb)).ne',
    replace hb : (1 : ℝ) < b := nat.one_lt_cast.2 hb,
    have hb0 : (0 : ℝ) < b := zero_lt_one.trans hb,
    have H : tendsto (λ m, 1 / b ^ m : ℕ → ℝ) at_top (𝓝 0),
    { simp only [one_div],
      exact tendsto_inv_at_top_zero.comp (tendsto_pow_at_top_at_top_of_one_lt hb) },
    refine (H.eventually (hx.irrational.eventually_forall_le_dist_cast_div b)).mono _,
    exact λ m hm a, hm a },
  have : ∀ᶠ m : ℕ in at_top, ∀ b < N, 1 < b → ∀ a : ℤ, (1 / b ^ m : ℝ) ≤ |x - a / b|,
    from (finite_lt_nat N).eventually_all.2 (λ b hb, eventually_imp_distrib_left.2 (this b)),
  rcases (this.and (eventually_ge_at_top n)).exists with ⟨m, hm, hnm⟩,
  rcases hx m with ⟨a, b, hb, hne, hlt⟩,
  lift b to ℕ using zero_le_one.trans hb.le, norm_cast at hb, push_cast at hne hlt,
  cases le_or_lt N b,
  { refine (hN b h a hne).not_lt (hlt.trans_le _),
    replace hb : (1 : ℝ) < b := nat.one_lt_cast.2 hb,
    have hb0 : (0 : ℝ) < b := zero_lt_one.trans hb,
    exact one_div_le_one_div_of_le (pow_pos hb0 _) (pow_le_pow hb.le hnm) },
  { exact (hm b h hb _).not_lt hlt }
end

protected lemma liouville_with (hx : liouville x) (p : ℝ) : liouville_with p x :=
begin
  suffices : liouville_with ⌈p⌉₊ x, from this.mono (le_nat_ceil p),
  refine ⟨1, ((hx.frequently_exists_num ⌈p⌉₊).and_eventually (eventually_gt_at_top 1)).mono _⟩,
  rintro b ⟨⟨a, hne, hlt⟩, hb⟩,
  refine ⟨a, hne, _⟩,
  rwa rpow_nat_cast
end

end liouville

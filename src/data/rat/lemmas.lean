/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import data.rat.defs
import data.int.cast.lemmas
import data.int.div
import algebra.group_with_zero.units.lemmas
import tactic.nth_rewrite

/-!
# Further lemmas for the Rational Numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/

namespace rat
open_locale rat

theorem num_dvd (a) {b : ℤ} (b0 : b ≠ 0) : (a /. b).num ∣ a :=
begin
  cases e : a /. b with n d h c,
  rw [rat.num_denom', rat.mk_eq b0
    (ne_of_gt (int.coe_nat_pos.2 h))] at e,
  refine (int.nat_abs_dvd.1 $ int.dvd_nat_abs.1 $ int.coe_nat_dvd.2 $
    c.dvd_of_dvd_mul_right _),
  have := congr_arg int.nat_abs e,
  simp only [int.nat_abs_mul, int.nat_abs_of_nat] at this, simp [this]
end

theorem denom_dvd (a b : ℤ) : ((a /. b).denom : ℤ) ∣ b :=
begin
  by_cases b0 : b = 0, {simp [b0]},
  cases e : a /. b with n d h c,
  rw [num_denom', mk_eq b0 (ne_of_gt (int.coe_nat_pos.2 h))] at e,
  refine (int.dvd_nat_abs.1 $ int.coe_nat_dvd.2 $ c.symm.dvd_of_dvd_mul_left _),
  rw [← int.nat_abs_mul, ← int.coe_nat_dvd, int.dvd_nat_abs, ← e], simp
end

lemma num_denom_mk {q : ℚ} {n d : ℤ} (hd : d ≠ 0) (qdf : q = n /. d) :
  ∃ c : ℤ, n = c * q.num ∧ d = c * q.denom :=
begin
  obtain rfl|hn := eq_or_ne n 0,
  { simp [qdf] },
  have : q.num * d = n * ↑(q.denom),
  { refine (rat.mk_eq _ hd).mp _,
    { exact int.coe_nat_ne_zero.mpr (rat.denom_ne_zero _) },
    { rwa [num_denom] } },
  have hqdn : q.num ∣ n,
  { rw qdf, exact rat.num_dvd _ hd },
  refine ⟨n / q.num, _, _⟩,
  { rw int.div_mul_cancel hqdn },
  { refine int.eq_mul_div_of_mul_eq_mul_of_dvd_left _ hqdn this,
    rw qdf,
    exact rat.num_ne_zero_of_ne_zero ((mk_ne_zero hd).mpr hn) }
end

theorem mk_pnat_num (n : ℤ) (d : ℕ+) :
  (mk_pnat n d).num = n / nat.gcd n.nat_abs d :=
by cases d; refl

theorem mk_pnat_denom (n : ℤ) (d : ℕ+) :
  (mk_pnat n d).denom = d / nat.gcd n.nat_abs d :=
by cases d; refl

lemma num_mk (n d : ℤ) :
  (n /. d).num = d.sign * n / n.gcd d :=
begin
  rcases d with ((_ | _) | _);
    simp [rat.mk, mk_nat, mk_pnat, nat.succ_pnat, int.sign, int.gcd,
      -nat.cast_succ, -int.coe_nat_succ, int.zero_div]
end

lemma denom_mk (n d : ℤ) :
  (n /. d).denom = if d = 0 then 1 else d.nat_abs / n.gcd d :=
begin
  rcases d with ((_ | _) | _);
  simp [rat.mk, mk_nat, mk_pnat, nat.succ_pnat, int.sign, int.gcd,
    -nat.cast_succ, -int.coe_nat_succ]
end

theorem mk_pnat_denom_dvd (n : ℤ) (d : ℕ+) :
  (mk_pnat n d).denom ∣ d.1 :=
begin
  rw mk_pnat_denom,
  apply nat.div_dvd_of_dvd,
  apply nat.gcd_dvd_right
end

theorem add_denom_dvd (q₁ q₂ : ℚ) : (q₁ + q₂).denom ∣ q₁.denom * q₂.denom :=
by { cases q₁, cases q₂, apply mk_pnat_denom_dvd }

theorem mul_denom_dvd (q₁ q₂ : ℚ) : (q₁ * q₂).denom ∣ q₁.denom * q₂.denom :=
by { cases q₁, cases q₂, apply mk_pnat_denom_dvd }

theorem mul_num (q₁ q₂ : ℚ) : (q₁ * q₂).num =
  (q₁.num * q₂.num) / nat.gcd (q₁.num * q₂.num).nat_abs (q₁.denom * q₂.denom) :=
by cases q₁; cases q₂; refl

theorem mul_denom (q₁ q₂ : ℚ) : (q₁ * q₂).denom =
  (q₁.denom * q₂.denom) / nat.gcd (q₁.num * q₂.num).nat_abs (q₁.denom * q₂.denom) :=
by cases q₁; cases q₂; refl

theorem mul_self_num (q : ℚ) : (q * q).num = q.num * q.num :=
by rw [mul_num, int.nat_abs_mul, nat.coprime.gcd_eq_one, int.coe_nat_one, int.div_one];
exact (q.cop.mul_right q.cop).mul (q.cop.mul_right q.cop)

theorem mul_self_denom (q : ℚ) : (q * q).denom = q.denom * q.denom :=
by rw [rat.mul_denom, int.nat_abs_mul, nat.coprime.gcd_eq_one, nat.div_one];
exact (q.cop.mul_right q.cop).mul (q.cop.mul_right q.cop)

lemma add_num_denom (q r : ℚ) : q + r =
  ((q.num * r.denom + q.denom * r.num : ℤ)) /. (↑q.denom * ↑r.denom : ℤ) :=
have hqd : (q.denom : ℤ) ≠ 0, from int.coe_nat_ne_zero_iff_pos.2 q.3,
have hrd : (r.denom : ℤ) ≠ 0, from int.coe_nat_ne_zero_iff_pos.2 r.3,
by conv_lhs { rw [←@num_denom q, ←@num_denom r, rat.add_def hqd hrd] };
  simp [mul_comm]

section casts

lemma exists_eq_mul_div_num_and_eq_mul_div_denom (n : ℤ) {d : ℤ} (d_ne_zero : d ≠ 0) :
  ∃ (c : ℤ), n = c * ((n : ℚ) / d).num ∧ (d : ℤ) = c * ((n : ℚ) / d).denom :=
begin
  have : ((n : ℚ) / d) = rat.mk n d, by rw [←rat.mk_eq_div],
  exact rat.num_denom_mk d_ne_zero this
end

lemma mul_num_denom' (q r : ℚ) :
  (q * r).num * q.denom * r.denom = q.num * r.num * (q * r).denom :=
begin
  let s := (q.num * r.num) /. (q.denom * r.denom : ℤ),
  have hs : (q.denom * r.denom : ℤ) ≠ 0 := int.coe_nat_ne_zero_iff_pos.mpr (mul_pos q.pos r.pos),
  obtain ⟨c, ⟨c_mul_num, c_mul_denom⟩⟩ :=
    exists_eq_mul_div_num_and_eq_mul_div_denom (q.num * r.num) hs,
  rw [c_mul_num, mul_assoc, mul_comm],
  nth_rewrite 0 c_mul_denom,
  repeat {rw mul_assoc},
  apply mul_eq_mul_left_iff.2,
  rw or_iff_not_imp_right,
  intro c_pos,
  have h : _ = s := @mul_def q.num q.denom r.num r.denom
    (int.coe_nat_ne_zero_iff_pos.mpr q.pos)
    (int.coe_nat_ne_zero_iff_pos.mpr  r.pos),
  rw [num_denom, num_denom] at h,
  rw h,
  rw mul_comm,
  apply rat.eq_iff_mul_eq_mul.mp,
  rw ←mk_eq_div,
end

lemma add_num_denom' (q r : ℚ) :
  (q + r).num * q.denom * r.denom = (q.num * r.denom + r.num * q.denom) * (q + r).denom :=
begin
  let s := mk (q.num * r.denom + r.num * q.denom) (q.denom * r.denom : ℤ),
  have hs : (q.denom * r.denom : ℤ) ≠ 0 := int.coe_nat_ne_zero_iff_pos.mpr (mul_pos q.pos r.pos),
  obtain ⟨c, ⟨c_mul_num, c_mul_denom⟩⟩ := exists_eq_mul_div_num_and_eq_mul_div_denom
    (q.num * r.denom + r.num * q.denom) hs,
  rw [c_mul_num, mul_assoc, mul_comm],
  nth_rewrite 0 c_mul_denom,
  repeat {rw mul_assoc},
  apply mul_eq_mul_left_iff.2,
  rw or_iff_not_imp_right,
  intro c_pos,
  have h : _ = s := @add_def q.num q.denom r.num r.denom
    (int.coe_nat_ne_zero_iff_pos.mpr q.pos)
    (int.coe_nat_ne_zero_iff_pos.mpr  r.pos),
  rw [num_denom, num_denom] at h,
  rw h,
  rw mul_comm,
  apply rat.eq_iff_mul_eq_mul.mp,
  rw ←mk_eq_div,
end

lemma substr_num_denom' (q r : ℚ) :
  (q - r).num * q.denom * r.denom = (q.num * r.denom - r.num * q.denom) * (q - r).denom :=
by rw [sub_eq_add_neg, sub_eq_add_neg, ←neg_mul, ←num_neg_eq_neg_num, ←denom_neg_eq_denom r,
  add_num_denom' q (-r)]

end casts

lemma inv_def' {q : ℚ} : q⁻¹ = (q.denom : ℚ) / q.num :=
by { conv_lhs { rw ←@num_denom q }, rw [inv_def, mk_eq_div, int.cast_coe_nat] }

protected lemma inv_neg (q : ℚ) : (-q)⁻¹ = -q⁻¹ := by { rw ←@num_denom q, simp [-num_denom] }

@[simp] lemma mul_denom_eq_num {q : ℚ} : q * q.denom = q.num :=
begin
  suffices : mk (q.num) ↑(q.denom) * mk ↑(q.denom) 1 = mk (q.num) 1, by
  { conv { for q [1] { rw ←(@num_denom q) }}, rwa [coe_int_eq_mk, coe_nat_eq_mk] },
  have : (q.denom : ℤ) ≠ 0, from ne_of_gt (by exact_mod_cast q.pos),
  rw [(rat.mul_def this one_ne_zero), (mul_comm (q.denom : ℤ) 1), (div_mk_div_cancel_left this)]
end

lemma denom_div_cast_eq_one_iff (m n : ℤ) (hn : n ≠ 0) :
  ((m : ℚ) / n).denom = 1 ↔ n ∣ m :=
begin
  replace hn : (n:ℚ) ≠ 0, by rwa [ne.def, ← int.cast_zero, coe_int_inj],
  split,
  { intro h,
    lift ((m : ℚ) / n) to ℤ using h with k hk,
    use k,
    rwa [eq_div_iff_mul_eq hn, ← int.cast_mul, mul_comm, eq_comm, coe_int_inj] at hk },
  { rintros ⟨d, rfl⟩,
    rw [int.cast_mul, mul_comm, mul_div_cancel _ hn, rat.coe_int_denom] }
end

lemma num_div_eq_of_coprime {a b : ℤ} (hb0 : 0 < b) (h : nat.coprime a.nat_abs b.nat_abs) :
  (a / b : ℚ).num = a :=
begin
  lift b to ℕ using le_of_lt hb0,
  norm_cast at hb0 h,
  rw [← rat.mk_eq_div, ← rat.mk_pnat_eq a b hb0, rat.mk_pnat_num, pnat.mk_coe, h.gcd_eq_one,
    int.coe_nat_one, int.div_one]
end

lemma denom_div_eq_of_coprime {a b : ℤ} (hb0 : 0 < b) (h : nat.coprime a.nat_abs b.nat_abs) :
  ((a / b : ℚ).denom : ℤ) = b :=
begin
  lift b to ℕ using le_of_lt hb0,
  norm_cast at hb0 h,
  rw [← rat.mk_eq_div, ← rat.mk_pnat_eq a b hb0, rat.mk_pnat_denom, pnat.mk_coe, h.gcd_eq_one,
    nat.div_one]
end

lemma div_int_inj {a b c d : ℤ} (hb0 : 0 < b) (hd0 : 0 < d)
  (h1 : nat.coprime a.nat_abs b.nat_abs) (h2 : nat.coprime c.nat_abs d.nat_abs)
  (h : (a : ℚ) / b = (c : ℚ) / d) : a = c ∧ b = d :=
begin
  apply and.intro,
  { rw [← (num_div_eq_of_coprime hb0 h1), h, num_div_eq_of_coprime hd0 h2] },
  { rw [← (denom_div_eq_of_coprime hb0 h1), h, denom_div_eq_of_coprime hd0 h2] }
end

@[norm_cast] lemma coe_int_div_self (n : ℤ) : ((n / n : ℤ) : ℚ) = n / n :=
begin
  by_cases hn : n = 0,
  { subst hn, simp only [int.cast_zero, int.zero_div, zero_div] },
  { have : (n : ℚ) ≠ 0, { rwa ← coe_int_inj at hn },
    simp only [int.div_self hn, int.cast_one, ne.def, not_false_iff, div_self this] }
end

@[norm_cast] lemma coe_nat_div_self (n : ℕ) : ((n / n : ℕ) : ℚ) = n / n :=
coe_int_div_self n

lemma coe_int_div (a b : ℤ) (h : b ∣ a) : ((a / b : ℤ) : ℚ) = a / b :=
begin
  rcases h with ⟨c, rfl⟩,
  simp only [mul_comm b, int.mul_div_assoc c (dvd_refl b), int.cast_mul, mul_div_assoc,
    coe_int_div_self]
end

lemma coe_nat_div (a b : ℕ) (h : b ∣ a) : ((a / b : ℕ) : ℚ) = a / b :=
begin
  rcases h with ⟨c, rfl⟩,
  simp only [mul_comm b, nat.mul_div_assoc c (dvd_refl b), nat.cast_mul, mul_div_assoc,
    coe_nat_div_self]
end

lemma inv_coe_int_num_of_pos {a : ℤ} (ha0 : 0 < a) : (a : ℚ)⁻¹.num = 1 :=
begin
  rw [rat.inv_def', rat.coe_int_num, rat.coe_int_denom, nat.cast_one, ←int.cast_one],
  apply num_div_eq_of_coprime ha0,
  rw int.nat_abs_one,
  exact nat.coprime_one_left _,
end

lemma inv_coe_nat_num_of_pos {a : ℕ} (ha0 : 0 < a) : (a : ℚ)⁻¹.num = 1 :=
inv_coe_int_num_of_pos (by exact_mod_cast ha0 : 0 < (a : ℤ))

lemma inv_coe_int_denom_of_pos {a : ℤ} (ha0 : 0 < a) : ((a : ℚ)⁻¹.denom : ℤ) = a :=
begin
  rw [rat.inv_def', rat.coe_int_num, rat.coe_int_denom, nat.cast_one, ←int.cast_one],
  apply denom_div_eq_of_coprime ha0,
  rw int.nat_abs_one,
  exact nat.coprime_one_left _,
end

lemma inv_coe_nat_denom_of_pos {a : ℕ} (ha0 : 0 < a) : (a : ℚ)⁻¹.denom = a :=
begin
  rw [← int.coe_nat_eq_coe_nat_iff, ← int.cast_coe_nat a, inv_coe_int_denom_of_pos],
  rwa [← nat.cast_zero, nat.cast_lt]
end

@[simp] lemma inv_coe_int_num (a : ℤ) : (a : ℚ)⁻¹.num = int.sign a :=
begin
  induction a using int.induction_on;
  simp [←int.neg_succ_of_nat_coe', int.neg_succ_of_nat_coe, -neg_add_rev, rat.inv_neg,
        int.coe_nat_add_one_out, -nat.cast_succ, inv_coe_nat_num_of_pos, -int.cast_neg_succ_of_nat,
        @eq_comm ℤ 1, int.sign_eq_one_of_pos]
end

@[simp] lemma inv_coe_nat_num (a : ℕ) : (a : ℚ)⁻¹.num = int.sign a :=
inv_coe_int_num a

@[simp] lemma inv_coe_int_denom (a : ℤ) : (a : ℚ)⁻¹.denom = if a = 0 then 1 else a.nat_abs :=
begin
  induction a using int.induction_on;
  simp [←int.neg_succ_of_nat_coe', int.neg_succ_of_nat_coe, -neg_add_rev, rat.inv_neg,
        int.coe_nat_add_one_out, -nat.cast_succ, inv_coe_nat_denom_of_pos,
        -int.cast_neg_succ_of_nat]
end

@[simp] lemma inv_coe_nat_denom (a : ℕ) : (a : ℚ)⁻¹.denom = if a = 0 then 1 else a :=
by simpa using inv_coe_int_denom a

protected lemma «forall» {p : ℚ → Prop} : (∀ r, p r) ↔ ∀ a b : ℤ, p (a / b) :=
⟨λ h _ _, h _,
  λ h q, (show q = q.num / q.denom, from by simp [rat.div_num_denom]).symm ▸ (h q.1 q.2)⟩

protected lemma «exists» {p : ℚ → Prop} : (∃ r, p r) ↔ ∃ a b : ℤ, p (a / b) :=
⟨λ ⟨r, hr⟩, ⟨r.num, r.denom, by rwa [← mk_eq_div, num_denom]⟩, λ ⟨a, b, h⟩, ⟨_, h⟩⟩

/-!
### Denominator as `ℕ+`
-/
section pnat_denom

/-- Denominator as `ℕ+`. -/
def pnat_denom (x : ℚ) : ℕ+ := ⟨x.denom, x.pos⟩

@[simp] lemma coe_pnat_denom (x : ℚ) : (x.pnat_denom : ℕ) = x.denom := rfl

@[simp] lemma mk_pnat_pnat_denom_eq (x : ℚ) : mk_pnat x.num x.pnat_denom = x :=
by rw [pnat_denom, mk_pnat_eq, num_denom]

lemma pnat_denom_eq_iff_denom_eq {x : ℚ} {n : ℕ+} : x.pnat_denom = n ↔ x.denom = ↑n :=
subtype.ext_iff

@[simp] lemma pnat_denom_one : (1 : ℚ).pnat_denom = 1 := rfl

@[simp] lemma pnat_denom_zero : (0 : ℚ).pnat_denom = 1 := rfl

end pnat_denom

end rat

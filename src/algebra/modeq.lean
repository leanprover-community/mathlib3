/-
Copyright (c) 2023 Yaël Dillies, Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Eric Wieser
-/
import algebra.module.basic
import data.int.modeq

/-!
# Equality modulo an element

## TODO

Delete `int.modeq` in favour of `add_comm_group.modeq`.
-/

namespace add_comm_group
variables {α : Type*}

section add_comm_group
variables [add_comm_group α] {p a a₁ a₂ b b₁ b₂ c : α} {n : ℤ}

/-- `a ≡ b [PMOD p]` means that `b` is congruent to `a` modulo `p`.

Equivalently (as shown further down the file), `b` does not lie in the open interval `(a, a + p)`
modulo `p`, or `to_Ico_mod hp a` disagrees with `to_Ioc_mod hp a` at `b`, or `to_Ico_div hp a`
disagrees with `to_Ioc_div hp a` at `b`. -/
def modeq (p a b : α) : Prop := ∃ z : ℤ, b - a = z • p

notation a ` ≡ `:50 b ` [PMOD `:50 p `]`:0 := modeq p a b

@[refl] lemma modeq_refl (a : α) : a ≡ a [PMOD p] := ⟨0, by simp⟩

lemma modeq_rfl : a ≡ a [PMOD p] := modeq_refl _

lemma modeq_comm : a ≡ b [PMOD p] ↔ b ≡ a [PMOD p] :=
(equiv.neg _).exists_congr_left.trans $ by simp [modeq, ←neg_eq_iff_eq_neg]

alias modeq_comm ↔ modeq.symm _

lemma modeq.trans : a ≡ b [PMOD p] → b ≡ c [PMOD p] → a ≡ c [PMOD p] :=
λ ⟨m, hm⟩ ⟨n, hn⟩, ⟨m + n, by simp [add_smul, ←hm, ←hn]⟩

instance : is_refl _ (modeq p) := ⟨modeq_refl⟩

@[simp] lemma neg_modeq_neg : -a ≡ -b [PMOD p] ↔ a ≡ b [PMOD p] :=
modeq_comm.trans $ by simp [modeq]

alias neg_modeq_neg ↔ modeq.of_neg modeq.neg

@[simp] lemma modeq_neg : a ≡ b [PMOD -p] ↔ a ≡ b [PMOD p] :=
modeq_comm.trans $ by simp [modeq, ←neg_eq_iff_eq_neg]

alias modeq_neg ↔ modeq.of_neg' modeq.neg'

@[simp] lemma zsmul_modeq_zsmul [no_zero_smul_divisors ℤ α] (hn : n ≠ 0) :
  n • a ≡ n • b [PMOD (n • p)] ↔ a ≡ b [PMOD p] :=
exists_congr $ λ m, by rw [←smul_sub, smul_comm, smul_right_inj hn]; apply_instance

alias zsmul_modeq_zsmul ↔ modeq.zsmul_cancel _

lemma modeq_sub (a b : α) : a ≡ b [PMOD b - a] := ⟨1, (one_smul _ _).symm⟩

@[simp] lemma modeq_zero : a ≡ b [PMOD 0] ↔ a = b := by simp [modeq, sub_eq_zero, eq_comm]

namespace modeq

protected lemma of_zsmul : a ≡ b [PMOD (n • p)] → a ≡ b [PMOD p] :=
λ ⟨m, hm⟩, ⟨m * n, by rwa [mul_smul]⟩

protected lemma zsmul : a ≡ b [PMOD p] → n • a ≡ n • b [PMOD (n • p)] :=
Exists.imp $ λ m hm, by rw [←smul_sub, hm, smul_comm]

protected lemma add : a₁ ≡ b₁ [PMOD p] → a₂ ≡ b₂ [PMOD p] → a₁ + a₂ ≡ b₁ + b₂ [PMOD p] :=
λ ⟨m, hm⟩ ⟨n, hn⟩, ⟨m + n, by rw [add_sub_add_comm, hm, hn, add_smul]⟩

protected lemma sub (h₁ : a₁ ≡ b₁ [PMOD p]) (h₂ : a₂ ≡ b₂ [PMOD p]) : a₁ - a₂ ≡ b₁ - b₂ [PMOD p] :=
by simpa only [sub_eq_add_neg] using h₁.add h₂.neg

protected lemma add_left (c : α) (h : a ≡ b [PMOD p]) : c + a ≡ c + b [PMOD p] := modeq_rfl.add h
protected lemma sub_left (c : α) (h : a ≡ b [PMOD p]) : c - a ≡ c - b [PMOD p] := modeq_rfl.sub h
protected lemma add_right (c : α) (h : a ≡ b [PMOD p]) : a + c ≡ b + c [PMOD p] := h.add modeq_rfl
protected lemma sub_right (c : α) (h : a ≡ b [PMOD p]) : a - c ≡ b - c [PMOD p] := h.sub modeq_rfl

protected lemma add_left_cancel (h₁ : a₁ ≡ b₁ [PMOD p]) (h : a₁ + a₂ ≡ b₁ + b₂ [PMOD p]) :
  a₂ ≡ b₂ [PMOD p] :=
by simpa using h.sub h₁

protected lemma add_right_cancel (h₂ : a₂ ≡ b₂ [PMOD p]) (h : a₁ + a₂ ≡ b₁ + b₂ [PMOD p]) :
  a₁ ≡ b₁ [PMOD p] :=
by simpa using h.sub h₂

protected lemma add_left_cancel' (c : α) (h : c + a ≡ c + b [PMOD p]) : a ≡ b [PMOD p] :=
modeq_rfl.add_left_cancel h

protected lemma add_right_cancel' (c : α) (h : a + c ≡ b + c [PMOD p]) : a ≡ b [PMOD p] :=
modeq_rfl.add_right_cancel h

end modeq

@[simp] lemma add_modeq_left : n + a ≡ a [PMOD p] := modeq.symm $ modeq_iff_dvd.2 $ by simp
@[simp] lemma add_modeq_right : a + n ≡ a [PMOD p] := modeq.symm $ modeq_iff_dvd.2 $ by simp

lemma modeq_and_modeq_iff_modeq_mul {a b m n : ℤ} (hmn : m.nat_abs.coprime n.nat_abs) :
  a ≡ b [PMOD m] ∧ a ≡ b [PMOD p] ↔ (a ≡ b [PMOD m * n]) :=
⟨λ h, begin
    rw [modeq_iff_dvd, modeq_iff_dvd] at h,
    rw [modeq_iff_dvd, ← nat_abs_dvd, ← dvd_nat_abs,
      coe_nat_dvd, nat_abs_mul],
    refine hmn.mul_dvd_of_dvd_of_dvd _ _;
    rw [← coe_nat_dvd, nat_abs_dvd, dvd_nat_abs]; tauto
  end,
λ h, ⟨h.of_mul_right _, h.of_mul_left _⟩⟩

lemma gcd_a_modeq (a b : ℕ) : (a : ℤ) * nat.gcd_a a b ≡ nat.gcd a b [PMOD b] :=
by { rw [← add_zero ((a : ℤ) * _), nat.gcd_eq_gcd_ab],
  exact (dvd_mul_right _ _).zero_modeq_int.add_left _ }

lemma modeq_add_fac {a b n : ℤ} (c : ℤ) (ha : a ≡ b [PMOD p]) : a + n*c ≡ b [PMOD p] :=
calc a + n*c ≡ b + n*c [PMOD p] : ha.add_right _
         ... ≡ b + 0 [PMOD p] : (dvd_mul_right _ _).modeq_zero_int.add_left _
         ... ≡ b [PMOD p] : by rw add_zero

lemma modeq_add_fac_self {a t n : ℤ} : a + n * t ≡ a [PMOD p] :=
modeq_add_fac _ modeq_rfl

lemma mod_coprime {a b : ℕ} (hab : nat.coprime a b) : ∃ y : ℤ, a * y ≡ 1 [PMOD b] :=
⟨ nat.gcd_a a b,
  have hgcd : nat.gcd a b = 1, from nat.coprime.gcd_eq_one hab,
  calc
   ↑a * nat.gcd_a a b ≡ ↑a * nat.gcd_a a b + ↑b * nat.gcd_b a b [PMOD ↑b] : modeq.symm $
                      modeq_add_fac _ $ modeq_refl _
              ... ≡ 1 [PMOD ↑b] : by rw [← nat.gcd_eq_gcd_ab, hgcd]; reflexivity ⟩

lemma exists_unique_equiv (a : ℤ) {b : ℤ} (hb : 0 < b) : ∃ z : ℤ, 0 ≤ z ∧ z < b ∧ z ≡ a [PMOD b] :=
⟨ a % b, mod_nonneg _ (ne_of_gt hb),
  have a % b < |b|, from mod_lt _ (ne_of_gt hb),
  by rwa abs_of_pos hb at this,
  by simp [modeq] ⟩

lemma exists_unique_equiv_nat (a : ℤ) {b : ℤ} (hb : 0 < b) : ∃ z : ℕ, ↑z < b ∧ ↑z ≡ a [PMOD b] :=
let ⟨z, hz1, hz2, hz3⟩ := exists_unique_equiv a hb in
⟨z.nat_abs, by split; rw [←of_nat_eq_coe, of_nat_nat_abs_eq_of_nonneg hz1]; assumption⟩

lemma modeq_iff_eq_add_zsmul : a ≡ b [PMOD p] ↔ ∃ z : ℤ, b = a + z • p :=
by simp_rw [modeq, sub_eq_iff_eq_add']

lemma not_modeq_iff_ne_add_zsmul : ¬a ≡ b [PMOD p] ↔ ∀ z : ℤ, b ≠ a + z • p :=
by rw [modeq_iff_eq_add_zsmul, not_exists]

lemma modeq_iff_eq_mod_zmultiples : a ≡ b [PMOD p] ↔ (b : α ⧸ add_subgroup.zmultiples p) = a :=
by simp_rw [modeq_iff_eq_add_zsmul, quotient_add_group.eq_iff_sub_mem,
    add_subgroup.mem_zmultiples_iff, eq_sub_iff_add_eq', eq_comm]

lemma not_modeq_iff_ne_mod_zmultiples :
  ¬a ≡ b [PMOD p] ↔ (b : α ⧸ add_subgroup.zmultiples p) ≠ a :=
modeq_iff_eq_mod_zmultiples.not

end add_comm_group

@[simp] lemma modeq_iff_int_modeq {a b n : ℤ} : a ≡ b [PMOD n] ↔ a ≡ b [ZMOD n] :=
by simp [modeq, dvd_iff_exists_eq_mul_left, int.modeq_iff_dvd]

section ring
variables [ring α] [char_zero α]

@[simp, norm_cast]
lemma int_cast_modeq_int_cast {a b n : ℤ} : a ≡ b [PMOD (n : α)] ↔ a ≡ b [PMOD n] :=
by simp_rw [modeq, zsmul_eq_mul]; norm_cast

@[simp, norm_cast]
lemma nat_cast_modeq_nat_cast {a b n : ℕ} : a ≡ b [PMOD (n : α)] ↔ a ≡ b [MOD n] :=
by simp_rw [←int.coe_nat_modeq_iff, ←modeq_iff_int_modeq, ←@int_cast_modeq_int_cast α,
  int.cast_coe_nat]

alias int_cast_modeq_int_cast ↔ modeq.of_int_cast modeq.int_cast
alias nat_cast_modeq_nat_cast ↔ _root_.nat.modeq.of_nat_cast modeq.nat_cast

end ring
end add_comm_group

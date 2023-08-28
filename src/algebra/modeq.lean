/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.int.modeq
import group_theory.quotient_group

/-!
# Equality modulo an element

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines equality modulo an element in a commutative group.

## Main definitions

* `a ≡ b [PMOD p]`: `a` and `b` are congruent modulo a`p`.

## See also

`smodeq` is a generalisation to arbitrary submodules.

## TODO

Delete `int.modeq` in favour of `add_comm_group.modeq`. Generalise `smodeq` to `add_subgroup` and
redefine `add_comm_group.modeq` using it. Once this is done, we can rename `add_comm_group.modeq`
to `add_subgroup.modeq` and multiplicativise it. Longer term, we could generalise to submonoids and
also unify with `nat.modeq`.
-/

namespace add_comm_group
variables {α : Type*}

section add_comm_group
variables [add_comm_group α] {p a a₁ a₂ b b₁ b₂ c : α} {n : ℕ} {z : ℤ}

/-- `a ≡ b [PMOD p]` means that `b` is congruent to `a` modulo `p`.

Equivalently (as shown in `algebra.order.to_interval_mod`), `b` does not lie in the open interval
`(a, a + p)` modulo `p`, or `to_Ico_mod hp a` disagrees with `to_Ioc_mod hp a` at `b`, or
`to_Ico_div hp a` disagrees with `to_Ioc_div hp a` at `b`. -/
def modeq (p a b : α) : Prop := ∃ z : ℤ, b - a = z • p

notation a ` ≡ `:50 b ` [PMOD `:50 p `]`:0 := modeq p a b

@[refl, simp] lemma modeq_refl (a : α) : a ≡ a [PMOD p] := ⟨0, by simp⟩

lemma modeq_rfl : a ≡ a [PMOD p] := modeq_refl _

lemma modeq_comm : a ≡ b [PMOD p] ↔ b ≡ a [PMOD p] :=
(equiv.neg _).exists_congr_left.trans $ by simp [modeq, ←neg_eq_iff_eq_neg]

alias modeq_comm ↔ modeq.symm _

attribute [symm] modeq.symm

@[trans] lemma modeq.trans : a ≡ b [PMOD p] → b ≡ c [PMOD p] → a ≡ c [PMOD p] :=
λ ⟨m, hm⟩ ⟨n, hn⟩, ⟨m + n, by simp [add_smul, ←hm, ←hn]⟩

instance : is_refl _ (modeq p) := ⟨modeq_refl⟩

@[simp] lemma neg_modeq_neg : -a ≡ -b [PMOD p] ↔ a ≡ b [PMOD p] :=
modeq_comm.trans $ by simp [modeq]

alias neg_modeq_neg ↔ modeq.of_neg modeq.neg

@[simp] lemma modeq_neg : a ≡ b [PMOD -p] ↔ a ≡ b [PMOD p] :=
modeq_comm.trans $ by simp [modeq, ←neg_eq_iff_eq_neg]

alias modeq_neg ↔ modeq.of_neg' modeq.neg'

lemma modeq_sub (a b : α) : a ≡ b [PMOD b - a] := ⟨1, (one_smul _ _).symm⟩

@[simp] lemma modeq_zero : a ≡ b [PMOD 0] ↔ a = b := by simp [modeq, sub_eq_zero, eq_comm]

@[simp] lemma self_modeq_zero : p ≡ 0 [PMOD p] := ⟨-1, by simp⟩

@[simp] lemma zsmul_modeq_zero (z : ℤ) : z • p ≡ 0 [PMOD p] := ⟨-z, by simp⟩
lemma add_zsmul_modeq (z : ℤ) : a + z • p ≡ a [PMOD p] := ⟨-z, by simp⟩
lemma zsmul_add_modeq (z : ℤ) : z • p + a ≡ a [PMOD p] := ⟨-z, by simp⟩
lemma add_nsmul_modeq (n : ℕ) : a + n • p ≡ a [PMOD p] := ⟨-n, by simp⟩
lemma nsmul_add_modeq (n : ℕ) : n • p + a ≡ a [PMOD p] := ⟨-n, by simp⟩

namespace modeq

protected lemma add_zsmul (z : ℤ) : a ≡ b [PMOD p] → a + z • p ≡ b [PMOD p] :=
(add_zsmul_modeq _).trans
protected lemma zsmul_add (z : ℤ) : a ≡ b [PMOD p] → z • p + a ≡ b [PMOD p] :=
(zsmul_add_modeq _).trans
protected lemma add_nsmul (n : ℕ) : a ≡ b [PMOD p] → a + n • p ≡ b [PMOD p] :=
(add_nsmul_modeq _).trans
protected lemma nsmul_add (n : ℕ) : a ≡ b [PMOD p] → n • p + a ≡ b [PMOD p] :=
(nsmul_add_modeq _).trans

protected lemma of_zsmul : a ≡ b [PMOD (z • p)] → a ≡ b [PMOD p] :=
λ ⟨m, hm⟩, ⟨m * z, by rwa [mul_smul]⟩

protected lemma of_nsmul : a ≡ b [PMOD (n • p)] → a ≡ b [PMOD p] :=
λ ⟨m, hm⟩, ⟨m * n, by rwa [mul_smul, coe_nat_zsmul]⟩

protected lemma zsmul : a ≡ b [PMOD p] → z • a ≡ z • b [PMOD (z • p)] :=
Exists.imp $ λ m hm, by rw [←smul_sub, hm, smul_comm]

protected lemma nsmul : a ≡ b [PMOD p] → n • a ≡ n • b [PMOD (n • p)] :=
Exists.imp $ λ m hm, by rw [←smul_sub, hm, smul_comm]

end modeq

@[simp] lemma zsmul_modeq_zsmul [no_zero_smul_divisors ℤ α] (hn : z ≠ 0) :
  z • a ≡ z • b [PMOD (z • p)] ↔ a ≡ b [PMOD p] :=
exists_congr $ λ m, by rw [←smul_sub, smul_comm, smul_right_inj hn]; apply_instance

@[simp] lemma nsmul_modeq_nsmul [no_zero_smul_divisors ℕ α] (hn : n ≠ 0) :
  n • a ≡ n • b [PMOD (n • p)] ↔ a ≡ b [PMOD p] :=
exists_congr $ λ m, by rw [←smul_sub, smul_comm, smul_right_inj hn]; apply_instance

alias zsmul_modeq_zsmul ↔ modeq.zsmul_cancel _
alias nsmul_modeq_nsmul ↔ modeq.nsmul_cancel _

namespace modeq

@[simp] protected lemma add_iff_left :
  a₁ ≡ b₁ [PMOD p] → (a₁ + a₂ ≡ b₁ + b₂ [PMOD p] ↔ a₂ ≡ b₂ [PMOD p]) :=
λ ⟨m, hm⟩, (equiv.add_left m).symm.exists_congr_left.trans $
  by simpa [add_sub_add_comm, hm, add_smul]

@[simp] protected lemma add_iff_right :
  a₂ ≡ b₂ [PMOD p] → (a₁ + a₂ ≡ b₁ + b₂ [PMOD p] ↔ a₁ ≡ b₁ [PMOD p]) :=
λ ⟨m, hm⟩, (equiv.add_right m).symm.exists_congr_left.trans $
  by simpa [add_sub_add_comm, hm, add_smul]

@[simp] protected lemma sub_iff_left :
  a₁ ≡ b₁ [PMOD p] → (a₁ - a₂ ≡ b₁ - b₂ [PMOD p] ↔ a₂ ≡ b₂ [PMOD p]) :=
λ ⟨m, hm⟩, (equiv.sub_left m).symm.exists_congr_left.trans $
  by simpa [sub_sub_sub_comm, hm, sub_smul]

@[simp] protected lemma sub_iff_right :
  a₂ ≡ b₂ [PMOD p] → (a₁ - a₂ ≡ b₁ - b₂ [PMOD p] ↔ a₁ ≡ b₁ [PMOD p]) :=
λ ⟨m, hm⟩, (equiv.sub_right m).symm.exists_congr_left.trans $
  by simpa [sub_sub_sub_comm, hm, sub_smul]

alias modeq.add_iff_left ↔ add_left_cancel add
alias modeq.add_iff_right ↔ add_right_cancel _
alias modeq.sub_iff_left ↔ sub_left_cancel sub
alias modeq.sub_iff_right ↔ sub_right_cancel _

attribute [protected] add_left_cancel add_right_cancel add sub_left_cancel sub_right_cancel sub

protected lemma add_left (c : α) (h : a ≡ b [PMOD p]) : c + a ≡ c + b [PMOD p] := modeq_rfl.add h
protected lemma sub_left (c : α) (h : a ≡ b [PMOD p]) : c - a ≡ c - b [PMOD p] := modeq_rfl.sub h
protected lemma add_right (c : α) (h : a ≡ b [PMOD p]) : a + c ≡ b + c [PMOD p] := h.add modeq_rfl
protected lemma sub_right (c : α) (h : a ≡ b [PMOD p]) : a - c ≡ b - c [PMOD p] := h.sub modeq_rfl

protected lemma add_left_cancel' (c : α) : c + a ≡ c + b [PMOD p] → a ≡ b [PMOD p] :=
modeq_rfl.add_left_cancel

protected lemma add_right_cancel' (c : α) : a + c ≡ b + c [PMOD p] → a ≡ b [PMOD p] :=
modeq_rfl.add_right_cancel

protected lemma sub_left_cancel' (c : α) : c - a ≡ c - b [PMOD p] → a ≡ b [PMOD p] :=
modeq_rfl.sub_left_cancel

protected lemma sub_right_cancel' (c : α) : a - c ≡ b - c [PMOD p] → a ≡ b [PMOD p] :=
modeq_rfl.sub_right_cancel

end modeq

lemma modeq_sub_iff_add_modeq' : a ≡ b - c [PMOD p] ↔ c + a ≡ b [PMOD p] := by simp [modeq, sub_sub]
lemma modeq_sub_iff_add_modeq : a ≡ b - c [PMOD p] ↔ a + c ≡ b [PMOD p] :=
modeq_sub_iff_add_modeq'.trans $ by rw add_comm
lemma sub_modeq_iff_modeq_add' : a - b ≡ c [PMOD p] ↔ a ≡ b + c [PMOD p] :=
modeq_comm.trans $ modeq_sub_iff_add_modeq'.trans modeq_comm
lemma sub_modeq_iff_modeq_add : a - b ≡ c [PMOD p] ↔ a ≡ c + b [PMOD p] :=
modeq_comm.trans $ modeq_sub_iff_add_modeq.trans modeq_comm

@[simp] lemma sub_modeq_zero : a - b ≡ 0 [PMOD p] ↔ a ≡ b [PMOD p] :=
by simp [sub_modeq_iff_modeq_add]

@[simp] lemma add_modeq_left : a + b ≡ a [PMOD p] ↔ b ≡ 0 [PMOD p] :=
by simp [←modeq_sub_iff_add_modeq']

@[simp] lemma add_modeq_right : a + b ≡ b [PMOD p] ↔ a ≡ 0 [PMOD p] :=
by simp [←modeq_sub_iff_add_modeq]

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

@[simp] lemma modeq_iff_int_modeq {a b z : ℤ} : a ≡ b [PMOD z] ↔ a ≡ b [ZMOD z] :=
by simp [modeq, dvd_iff_exists_eq_mul_left, int.modeq_iff_dvd]

section add_comm_group_with_one
variables [add_comm_group_with_one α] [char_zero α]

@[simp, norm_cast]
lemma int_cast_modeq_int_cast {a b z : ℤ} : a ≡ b [PMOD (z : α)] ↔ a ≡ b [PMOD z] :=
by simp_rw [modeq, ←int.cast_mul_eq_zsmul_cast]; norm_cast

@[simp, norm_cast]
lemma nat_cast_modeq_nat_cast {a b n : ℕ} : a ≡ b [PMOD (n : α)] ↔ a ≡ b [MOD n] :=
by simp_rw [←int.coe_nat_modeq_iff, ←modeq_iff_int_modeq, ←@int_cast_modeq_int_cast α,
  int.cast_coe_nat]

alias int_cast_modeq_int_cast ↔ modeq.of_int_cast modeq.int_cast
alias nat_cast_modeq_nat_cast ↔ _root_.nat.modeq.of_nat_cast modeq.nat_cast

end add_comm_group_with_one
end add_comm_group

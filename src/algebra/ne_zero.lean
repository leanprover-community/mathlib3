/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import algebra.algebra.basic

/-!
# `ne_zero` typeclass

We create a typeclass `ne_zero n` which carries around the fact that `(n : R) ≠ 0`.

## Main declarations

* `ne_zero`: `n ≠ 0` as a typeclass.

-/

/-- A type-class version of `n ≠ 0`.  -/
class ne_zero {R} [has_zero R] (n : R) : Prop := (out : n ≠ 0)

lemma ne_zero.ne {R} [has_zero R] (n : R) [h : ne_zero n] : n ≠ 0 := h.out

lemma ne_zero.ne' (n : ℕ) (R) [add_monoid_with_one R] [h : ne_zero (n : R)] :
  (n : R) ≠ 0 := h.out

lemma ne_zero_iff {R : Type*} [has_zero R] {n : R} : ne_zero n ↔ n ≠ 0 :=
⟨λ h, h.out, ne_zero.mk⟩

lemma not_ne_zero {R : Type*} [has_zero R] {n : R} : ¬ ne_zero n ↔ n = 0 :=
by simp [ne_zero_iff]

namespace ne_zero

variables {R S M F : Type*} {r : R} {x y : M} {n p : ℕ} {a : ℕ+}

instance pnat : ne_zero (a : ℕ) := ⟨a.ne_zero⟩
instance succ : ne_zero (n + 1) := ⟨n.succ_ne_zero⟩

lemma of_pos [preorder M] [has_zero M] (h : 0 < x) : ne_zero x := ⟨h.ne'⟩
lemma of_gt  [canonically_ordered_add_monoid M] (h : x < y) : ne_zero y := of_pos $ pos_of_gt h

instance char_zero [ne_zero n] [add_monoid_with_one M] [char_zero M] : ne_zero (n : M) :=
⟨nat.cast_ne_zero.mpr $ ne_zero.ne n⟩

@[priority 100] instance invertible [mul_zero_one_class M] [nontrivial M] [invertible x] :
  ne_zero x := ⟨nonzero_of_invertible x⟩

instance coe_trans [has_zero M] [has_coe R S] [has_coe_t S M] [h : ne_zero (r : M)] :
  ne_zero ((r : S) : M) := ⟨h.out⟩

lemma trans [has_zero M] [has_coe R S] [has_coe_t S M] (h : ne_zero ((r : S) : M)) :
  ne_zero (r : M) := ⟨h.out⟩

lemma of_map [has_zero R] [has_zero M] [zero_hom_class F R M] (f : F) [ne_zero (f r)] :
  ne_zero r := ⟨λ h, ne (f r) $ by convert map_zero f⟩

lemma nat_of_ne_zero [semiring R] [semiring S] [ring_hom_class F R S] (f : F)
  [hn : ne_zero (n : S)] : ne_zero (n : R) :=
begin
  apply ne_zero.of_map f,
  simp [hn]
end

lemma of_injective [has_zero R] [h : ne_zero r] [has_zero M] [zero_hom_class F R M]
  {f : F} (hf : function.injective f) : ne_zero (f r) :=
⟨by { rw ←map_zero f, exact hf.ne (ne r) }⟩

lemma nat_of_injective [non_assoc_semiring M] [non_assoc_semiring R] [h : ne_zero (n : R)]
  [ring_hom_class F R M] {f : F} (hf : function.injective f) : ne_zero (n : M) :=
 ⟨λ h, (ne_zero.ne' n R) $ hf $ by simpa⟩

lemma pos (r : R) [canonically_ordered_add_monoid R] [ne_zero r] : 0 < r :=
(zero_le r).lt_of_ne $ ne_zero.out.symm

variables (R M)

lemma of_no_zero_smul_divisors (n : ℕ) [comm_ring R] [ne_zero (n : R)] [ring M] [nontrivial M]
  [algebra R M] [no_zero_smul_divisors R M] : ne_zero (n : M) :=
nat_of_injective $ no_zero_smul_divisors.algebra_map_injective R M

lemma of_ne_zero_coe [add_monoid_with_one R] [h : ne_zero (n : R)] : ne_zero n :=
⟨by {casesI h, rintro rfl, by simpa using h}⟩

lemma pos_of_ne_zero_coe [add_monoid_with_one R] [ne_zero (n : R)] : 0 < n :=
(ne_zero.of_ne_zero_coe R).out.bot_lt

end ne_zero

lemma eq_zero_or_ne_zero {α} [has_zero α] (a : α) : a = 0 ∨ ne_zero a :=
(eq_or_ne a 0).imp_right ne_zero.mk

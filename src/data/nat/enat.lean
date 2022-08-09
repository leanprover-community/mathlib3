/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import data.nat.lattice
import data.nat.succ_pred

/-!
# Definition and basic properties of extended natural numbers
-/

@[derive [has_zero, add_comm_monoid_with_one, canonically_ordered_comm_semiring, nontrivial,
  canonically_linear_ordered_add_monoid, has_sub, has_ordered_sub, complete_linear_order,
  linear_ordered_add_comm_monoid_with_top, succ_order]]
def enat : Type := with_top ℕ

notation `ℕ∞` := enat

namespace enat

variables {m n : ℕ∞}

@[simp, norm_cast] lemma coe_zero : ((0 : ℕ) : ℕ∞) = 0 := rfl
@[simp, norm_cast] lemma coe_one : ((1 : ℕ) : ℕ∞) = 1 := rfl
@[simp, norm_cast] lemma coe_add (m n : ℕ) : ↑(m + n) = (m + n : ℕ∞) := rfl
@[simp, norm_cast] lemma coe_sub (m n : ℕ) : ↑(m - n) = (m - n : ℕ∞) := rfl
@[simp, norm_cast] lemma coe_mul (m n : ℕ) : ↑(m * n) = (m * n : ℕ∞) := with_top.coe_mul

instance : can_lift ℕ∞ ℕ := with_top.can_lift

/-- Conversion of `ℕ∞` to `ℕ` sending `∞` to `0`. -/
def to_nat : monoid_with_zero_hom ℕ∞ ℕ :=
{ to_fun := with_top.untop' 0,
  map_one' := rfl,
  map_zero' := rfl,
  map_mul' := with_top.untop'_zero_mul }

@[simp] lemma succ_def (m : ℕ∞) : order.succ m = m + 1 := by cases m; refl

lemma add_one_le_of_lt (h : m < n) : m + 1 ≤ n :=
m.succ_def ▸ order.succ_le_of_lt h

lemma add_one_le_iff (hm : m ≠ ⊤) : m + 1 ≤ n ↔ m < n :=
m.succ_def ▸ (order.succ_le_iff_of_not_is_max $ by rwa [is_max_iff_eq_top])

lemma one_le_iff_pos : 1 ≤ n ↔ 0 < n := add_one_le_iff with_top.zero_ne_top

lemma le_of_lt_add_one (h : m < n + 1) : m ≤ n := order.le_of_lt_succ $ n.succ_def.symm ▸ h

@[elab_as_eliminator]
lemma nat_induction {P : ℕ∞ → Prop} (a : ℕ∞) (h0 : P 0) (hsuc : ∀ n : ℕ, P n → P n.succ)
  (htop : (∀ n : ℕ, P n) → P ⊤) : P a :=
begin
  have A : ∀ n : ℕ, P n := λ n, nat.rec_on n h0 hsuc,
  cases a,
  exacts [htop A, A a]
end

end enat

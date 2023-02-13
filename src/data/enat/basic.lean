/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import data.nat.succ_pred
import algebra.char_zero.lemmas
import algebra.order.sub.with_top
import algebra.order.ring.with_top

/-!
# Definition and basic properties of extended natural numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `enat` (notation: `ℕ∞`) to be `with_top ℕ` and prove some basic lemmas
about this type.
-/

/-- Extended natural numbers `ℕ∞ = with_top ℕ`. -/
@[derive [has_zero, add_comm_monoid_with_one, canonically_ordered_comm_semiring, nontrivial,
  linear_order, order_bot, order_top, has_bot, has_top, canonically_linear_ordered_add_monoid,
  has_sub, has_ordered_sub, linear_ordered_add_comm_monoid_with_top, succ_order, well_founded_lt,
  has_well_founded, char_zero, has_coe_t ℕ]]
def enat : Type := with_top ℕ

notation `ℕ∞` := enat

namespace enat

instance : inhabited ℕ∞ := ⟨0⟩
instance : is_well_order ℕ∞ (<) := { }

variables {m n : ℕ∞}

@[simp, norm_cast] lemma coe_zero : ((0 : ℕ) : ℕ∞) = 0 := rfl
@[simp, norm_cast] lemma coe_one : ((1 : ℕ) : ℕ∞) = 1 := rfl
@[simp, norm_cast] lemma coe_add (m n : ℕ) : ↑(m + n) = (m + n : ℕ∞) := rfl
@[simp, norm_cast] lemma coe_sub (m n : ℕ) : ↑(m - n) = (m - n : ℕ∞) := rfl
@[simp, norm_cast] lemma coe_mul (m n : ℕ) : ↑(m * n) = (m * n : ℕ∞) := with_top.coe_mul

instance can_lift : can_lift ℕ∞ ℕ coe (λ n, n ≠ ⊤) := with_top.can_lift

/-- Conversion of `ℕ∞` to `ℕ` sending `∞` to `0`. -/
def to_nat : monoid_with_zero_hom ℕ∞ ℕ :=
{ to_fun := with_top.untop' 0,
  map_one' := rfl,
  map_zero' := rfl,
  map_mul' := with_top.untop'_zero_mul }

@[simp] lemma to_nat_coe (n : ℕ) : to_nat n = n := rfl
@[simp] lemma to_nat_top : to_nat ⊤ = 0 := rfl

@[simp] lemma coe_to_nat_eq_self : ↑n.to_nat = n ↔ n ≠ ⊤ :=
with_top.rec_top_coe (by simp) (by simp) n

alias coe_to_nat_eq_self ↔ _ coe_to_nat

lemma coe_to_nat_le_self (n : ℕ∞) : ↑(to_nat n) ≤ n := with_top.rec_top_coe le_top (λ k, le_rfl) n

lemma to_nat_add {m n : ℕ∞} (hm : m ≠ ⊤) (hn : n ≠ ⊤) : to_nat (m + n) = to_nat m + to_nat n :=
by { lift m to ℕ using hm, lift n to ℕ using hn, refl }

lemma to_nat_sub {n : ℕ∞} (hn : n ≠ ⊤) (m : ℕ∞) : to_nat (m - n) = to_nat m - to_nat n :=
begin
  lift n to ℕ using hn,
  induction m using with_top.rec_top_coe,
  { rw [with_top.top_sub_coe, to_nat_top, zero_tsub] },
  { rw [← coe_sub, to_nat_coe, to_nat_coe, to_nat_coe] }
end

lemma to_nat_eq_iff {m : ℕ∞} {n : ℕ} (hn : n ≠ 0) : m.to_nat = n ↔ m = n :=
by induction m using with_top.rec_top_coe; simp [hn.symm]

@[simp] lemma succ_def (m : ℕ∞) : order.succ m = m + 1 := by cases m; refl

lemma add_one_le_of_lt (h : m < n) : m + 1 ≤ n :=
m.succ_def ▸ order.succ_le_of_lt h

lemma add_one_le_iff (hm : m ≠ ⊤) : m + 1 ≤ n ↔ m < n :=
m.succ_def ▸ (order.succ_le_iff_of_not_is_max $ by rwa [is_max_iff_eq_top])

lemma one_le_iff_pos : 1 ≤ n ↔ 0 < n := add_one_le_iff with_top.zero_ne_top

lemma one_le_iff_ne_zero : 1 ≤ n ↔ n ≠ 0 := one_le_iff_pos.trans pos_iff_ne_zero

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

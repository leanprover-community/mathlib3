/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Neil Strickland
-/
import order.basic
import algebra.ne_zero

/-!
# The positive natural numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains the definitions, and basic results.
Most algebraic facts are deferred to `data.pnat.basic`, as they need more imports.
-/

/-- `ℕ+` is the type of positive natural numbers. It is defined as a subtype,
  and the VM representation of `ℕ+` is the same as `ℕ` because the proof
  is not stored. -/
@[derive [decidable_eq, linear_order]]
def pnat := {n : ℕ // 0 < n}
notation `ℕ+` := pnat

instance : has_one ℕ+ := ⟨⟨1, nat.zero_lt_one⟩⟩

instance coe_pnat_nat : has_coe ℕ+ ℕ := ⟨subtype.val⟩
instance : has_repr ℕ+ := ⟨λ n, repr n.1⟩

namespace pnat

@[simp] theorem mk_coe (n h) : ((⟨n, h⟩ : ℕ+) : ℕ) = n := rfl

/-- Predecessor of a `ℕ+`, as a `ℕ`. -/
def nat_pred (i : ℕ+) : ℕ := i - 1

@[simp] lemma nat_pred_eq_pred {n : ℕ} (h : 0 < n) : nat_pred (⟨n, h⟩ : ℕ+) = n.pred := rfl

end pnat

namespace nat

/-- Convert a natural number to a positive natural number. The
  positivity assumption is inferred by `dec_trivial`. -/
def to_pnat (n : ℕ) (h : 0 < n . tactic.exact_dec_trivial) : ℕ+ := ⟨n, h⟩

/-- Write a successor as an element of `ℕ+`. -/
def succ_pnat (n : ℕ) : ℕ+ := ⟨succ n, succ_pos n⟩

@[simp] theorem succ_pnat_coe (n : ℕ) : (succ_pnat n : ℕ) = succ n := rfl

@[simp] theorem nat_pred_succ_pnat (n : ℕ) : n.succ_pnat.nat_pred = n := rfl

@[simp] theorem _root_.pnat.succ_pnat_nat_pred (n : ℕ+) : n.nat_pred.succ_pnat = n :=
subtype.eq $ succ_pred_eq_of_pos n.2

/-- Convert a natural number to a pnat. `n+1` is mapped to itself,
  and `0` becomes `1`. -/
def to_pnat' (n : ℕ) : ℕ+ := succ_pnat (pred n)

@[simp] theorem to_pnat'_coe : ∀ (n : ℕ),
 ((to_pnat' n) : ℕ) = ite (0 < n) n 1
| 0 := rfl
| (m + 1) := by {rw [if_pos (succ_pos m)], refl}

end nat

namespace pnat

open nat

/-- We now define a long list of structures on ℕ+ induced by
 similar structures on ℕ. Most of these behave in a completely
 obvious way, but there are a few things to be said about
 subtraction, division and powers.
-/

@[simp] lemma mk_le_mk (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
  (⟨n, hn⟩ : ℕ+) ≤ ⟨k, hk⟩ ↔ n ≤ k := iff.rfl

@[simp] lemma mk_lt_mk (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
  (⟨n, hn⟩ : ℕ+) < ⟨k, hk⟩ ↔ n < k := iff.rfl

@[simp, norm_cast] lemma coe_le_coe (n k : ℕ+) : (n : ℕ) ≤ k ↔ n ≤ k := iff.rfl

@[simp, norm_cast] lemma coe_lt_coe (n k : ℕ+) : (n : ℕ) < k ↔ n < k := iff.rfl

@[simp] theorem pos (n : ℕ+) : 0 < (n : ℕ) := n.2

theorem eq {m n : ℕ+} : (m : ℕ) = n → m = n := subtype.eq

lemma coe_injective : function.injective (coe : ℕ+ → ℕ) := subtype.coe_injective

@[simp] theorem ne_zero (n : ℕ+) : (n : ℕ) ≠ 0 := n.2.ne'

instance _root_.ne_zero.pnat {a : ℕ+} : _root_.ne_zero (a : ℕ) := ⟨a.ne_zero⟩

theorem to_pnat'_coe {n : ℕ} : 0 < n → (n.to_pnat' : ℕ) = n := succ_pred_eq_of_pos

@[simp] theorem coe_to_pnat' (n : ℕ+) : (n : ℕ).to_pnat' = n := eq (to_pnat'_coe n.pos)

@[simp] lemma one_le (n : ℕ+) : (1 : ℕ+) ≤ n := n.2

@[simp] lemma not_lt_one (n : ℕ+) : ¬ n < 1 := not_lt_of_le n.one_le

instance : inhabited ℕ+ := ⟨1⟩

-- Some lemmas that rewrite `pnat.mk n h`, for `n` an explicit numeral, into explicit numerals.
@[simp] lemma mk_one {h} : (⟨1, h⟩ : ℕ+) = (1 : ℕ+) := rfl

@[norm_cast] theorem one_coe : ((1 : ℕ+) : ℕ) = 1 := rfl

@[simp, norm_cast] lemma coe_eq_one_iff {m : ℕ+} : (m : ℕ) = 1 ↔ m = 1 :=
subtype.coe_injective.eq_iff' one_coe

instance : has_well_founded ℕ+ := ⟨(<), measure_wf coe⟩

/-- Strong induction on `ℕ+`. -/
def strong_induction_on {p : ℕ+ → Sort*} : ∀ (n : ℕ+) (h : ∀ k, (∀ m, m < k → p m) → p k), p n
| n := λ IH, IH _ (λ a h, strong_induction_on a IH)
using_well_founded { dec_tac := `[assumption] }

/-- We define `m % k` and `m / k` in the same way as for `ℕ`
  except that when `m = n * k` we take `m % k = k` and
  `m / k = n - 1`.  This ensures that `m % k` is always positive
  and `m = (m % k) + k * (m / k)` in all cases.  Later we
  define a function `div_exact` which gives the usual `m / k`
  in the case where `k` divides `m`.
-/
def mod_div_aux : ℕ+ → ℕ → ℕ → ℕ+ × ℕ
| k 0 q := ⟨k, q.pred⟩
| k (r + 1) q := ⟨⟨r + 1, nat.succ_pos r⟩, q⟩

/-- `mod_div m k = (m % k, m / k)`.
  We define `m % k` and `m / k` in the same way as for `ℕ`
  except that when `m = n * k` we take `m % k = k` and
  `m / k = n - 1`.  This ensures that `m % k` is always positive
  and `m = (m % k) + k * (m / k)` in all cases.  Later we
  define a function `div_exact` which gives the usual `m / k`
  in the case where `k` divides `m`.
-/
def mod_div (m k : ℕ+) : ℕ+ × ℕ := mod_div_aux k ((m : ℕ) % (k : ℕ)) ((m : ℕ) / (k : ℕ))

/-- We define `m % k` in the same way as for `ℕ`
  except that when `m = n * k` we take `m % k = k` This ensures that `m % k` is always positive.
-/
def mod (m k : ℕ+) : ℕ+ := (mod_div m k).1

/-- We define `m / k` in the same way as for `ℕ` except that when `m = n * k` we take
  `m / k = n - 1`. This ensures that `m = (m % k) + k * (m / k)` in all cases. Later we
  define a function `div_exact` which gives the usual `m / k` in the case where `k` divides `m`.
-/
def div (m k : ℕ+) : ℕ  := (mod_div m k).2

theorem mod_coe (m k : ℕ+) :
 ((mod m k) : ℕ) = ite ((m : ℕ) % (k : ℕ) = 0) (k : ℕ) ((m : ℕ) % (k : ℕ)) :=
begin
  dsimp [mod, mod_div],
  cases (m : ℕ) % (k : ℕ),
  { rw [if_pos rfl], refl },
  { rw [if_neg n.succ_ne_zero], refl }
end

theorem div_coe (m k : ℕ+) :
 ((div m k) : ℕ) = ite ((m : ℕ) % (k : ℕ) = 0) ((m : ℕ) / (k : ℕ)).pred ((m : ℕ) / (k : ℕ)) :=
begin
  dsimp [div, mod_div],
  cases (m : ℕ) % (k : ℕ),
  { rw [if_pos rfl], refl },
  { rw [if_neg n.succ_ne_zero], refl }
end

/-- If `h : k | m`, then `k * (div_exact m k) = m`. Note that this is not equal to `m / k`. -/
def div_exact (m k : ℕ+) : ℕ+ :=
 ⟨(div m k).succ, nat.succ_pos _⟩

end pnat

section can_lift

instance nat.can_lift_pnat : can_lift ℕ ℕ+ coe ((<) 0) :=
⟨λ n hn, ⟨nat.to_pnat' n, pnat.to_pnat'_coe hn⟩⟩

instance int.can_lift_pnat : can_lift ℤ ℕ+ coe ((<) 0) :=
⟨λ n hn, ⟨nat.to_pnat' (int.nat_abs n),
  by rw [coe_coe, nat.to_pnat'_coe, if_pos (int.nat_abs_pos_of_ne_zero hn.ne'),
    int.nat_abs_of_nonneg hn.le]⟩⟩

end can_lift

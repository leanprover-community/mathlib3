/-
Copyright (c) 2021 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import algebra.periodic
import data.nat.count
import data.nat.interval

/-!
# Periodic Functions on ℕ

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file identifies a few functions on `ℕ` which are periodic, and also proves a lemma about
periodic predicates which helps determine their cardinality when filtering intervals over them.
-/

namespace nat

open nat function

lemma periodic_gcd (a : ℕ) : periodic (gcd a) a :=
by simp only [forall_const, gcd_add_self_right, eq_self_iff_true, periodic]

lemma periodic_coprime (a : ℕ) : periodic (coprime a) a :=
by simp only [coprime_add_self_right, forall_const, iff_self, eq_iff_iff, periodic]

lemma periodic_mod (a : ℕ) : periodic (λ n, n % a) a :=
by simp only [forall_const, eq_self_iff_true, add_mod_right, periodic]

lemma _root_.function.periodic.map_mod_nat {α : Type*} {f : ℕ → α} {a : ℕ} (hf : periodic f a) :
  ∀ n, f (n % a) = f n :=
λ n, by conv_rhs { rw [← nat.mod_add_div n a, mul_comm, ← nat.nsmul_eq_mul, hf.nsmul] }

section multiset
open multiset

/-- An interval of length `a` filtered over a periodic predicate of period `a` has cardinality
equal to the number naturals below `a` for which `p a` is true. -/
lemma filter_multiset_Ico_card_eq_of_periodic (n a : ℕ) (p : ℕ → Prop) [decidable_pred p]
  (pp : periodic p a) :
  (filter p (Ico n (n+a))).card = a.count p :=
begin
  rw [count_eq_card_filter_range, finset.card, finset.filter_val, finset.range_val,
    ←multiset_Ico_map_mod n, ←map_count_true_eq_filter_card, ←map_count_true_eq_filter_card,
    map_map, function.comp],
  simp only [pp.map_mod_nat],
end

end multiset

section finset
open finset

/-- An interval of length `a` filtered over a periodic predicate of period `a` has cardinality
equal to the number naturals below `a` for which `p a` is true. -/
lemma filter_Ico_card_eq_of_periodic (n a : ℕ) (p : ℕ → Prop) [decidable_pred p]
  (pp : periodic p a) :
  ((Ico n (n + a)).filter p).card = a.count p :=
filter_multiset_Ico_card_eq_of_periodic n a p pp

end finset

end nat

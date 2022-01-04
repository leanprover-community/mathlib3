import tactic

import data.equiv.basic
import group_theory.perm.cycle_type
import group_theory.specific_groups.alternating


variables {α : Type*} [decidable_eq α] [fintype α]
variables {M : Type*} [comm_monoid M]

section general_ring
variables {R : Type*} [ring R]

lemma odd_pow_of_neg_one {n : ℕ} (hn : odd n) :
  (-1 : units R)^n = -1 :=
units.eq_iff.mp (by simpa using nat.neg_one_pow_of_odd hn)

lemma even_pow_of_neg_one {n : ℕ} (hn : even n) :
  (-1 : units R)^n = 1 :=
units.eq_iff.mp (by simpa using nat.neg_one_pow_of_even hn)

end general_ring

/- Boring lemmas for powers of (-1 : units ℤ) -/
namespace int.units

lemma neg_one_ne_one' : (-1 : units ℤ) ≠ 1 :=
begin
  dec_trivial
end

lemma neq_one_is_neg_one' {u : units ℤ} (hu : u ≠ 1) : u = -1 :=
begin
    dec_trivial!
end

lemma pow_of_neg_one_is_one_of_even_iff {n : ℕ} :
  even n ↔ (-1 : units ℤ)^n = 1  :=
begin
  split, exact even_pow_of_neg_one,
  intro h, rw  nat.even_iff_not_odd,
  intro h', rw odd_pow_of_neg_one h' at h,
  revert h, dec_trivial,
end

lemma pow_of_neg_one_is_neg_one_of_odd_iff {n : ℕ} :
  odd n ↔ (-1 : units ℤ)^n = -1  :=
begin
  split, exact odd_pow_of_neg_one,
  intro h, rw nat.odd_iff_not_even,
  intro h', rw even_pow_of_neg_one h' at h,
  revert h, dec_trivial,
 end

end int.units


open subgroup equiv.perm equiv alternating_group

lemma is_cycle_type_of_even {f : perm α} :
  f.sign = 1 ↔ even (f.cycle_type.sum + f.cycle_type.card) :=
begin
  rw int.units.pow_of_neg_one_is_one_of_even_iff,
  suffices : (-1)^(f.cycle_type.sum + f.cycle_type.card) = f.sign,
  rw this,
  rw equiv.perm.sign_of_cycle_type,
  rw multiset.map_congr _,
    swap,  exact λn,  (-1) * (-1)^n,
    swap, { intros n h, rw units.neg_eq_neg_one_mul , },
  rw multiset.prod_map_mul,
  rw add_comm,
  rw pow_add,
  apply congr_arg2,
  { rw ← multiset.prod_repeat ,
    apply congr_arg,
    rw multiset.map_const  },
  generalize : f.cycle_type = m,
  apply multiset.induction_on m,
    simp,
    intros n m h, simp [h,pow_add],
end

lemma test4' {m : multiset ℕ} {a : M} : (multiset.map (λ n, a^n) m).prod = a ^ (m.sum) :=
multiset.induction_on m (by simp) (λ n m h, by simp [h,pow_add])

/-
Copyright (c) 2023 Yaël Dillies, Gareth Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Gareth Ma
-/
import data.nat.gcd.basic
import tactic.norm_num
import data.set.finite

/-!
# The Yellowstone permutation

This file defines the Yellowstone permutation and proves it is a permutation.

## References

* https://cs.uwaterloo.ca/journals/JIS/VOL18/Sloane/sloane9.pdf
-/

namespace nat
variables {a b : ℕ}

/-- The data of a step of the calculation of the Yellowstone permutation. Just here to make
projections have nice names. -/
structure yellowstone_data :=
(l : list ℕ)
(a b : ℕ)
(hab : a.coprime b)
(ha : a ≠ 1)
(hb : b ≠ 1)

private lemma aux (hab : a.coprime b) (ha : a ≠ 1) :
  ({c | ¬ a.coprime c ∧ b.coprime c ∧ c ≠ 1} : set ℕ).infinite :=
sorry

private lemma aux' (hab : a.coprime b) (ha : a ≠ 1) (l : list ℕ) :
  ∃ c, c ∉ l ∧ ¬ a.coprime c ∧ b.coprime c ∧ c ≠ 1 :=
by simpa [and_comm] using set.not_subset.1 (λ h, aux hab ha $ l.to_finset.finite_to_set.subset h)

/-- Auxiliary definition for `nat.yellowstone`. `yellowstone (l, a, b)` is `(a :: l, b, c)` where
`c` is the least natural coprime with `b`, not coprime with `a` and not appearing in `l`. -/
def yellowstone_step (d : yellowstone_data) : yellowstone_data :=
{ l := d.a :: d.l,
  a := d.b,
  b := nat.find $ aux' d.hab d.ha $ d.b :: d.a :: d.l,
  hab := (nat.find_spec $ aux' d.hab d.ha $ d.b :: d.a :: d.l).2.2.1,
  ha := d.hb,
  hb := (nat.find_spec $ aux' d.hab d.ha $ d.b :: d.a :: d.l).2.2.2 }

/-- The **Yellowstone permutation**. A098550. The first terms are `0, 1, 2, 3`. Then
`yellowstone (n + 2)` is the first natural number not yet appearing in the sequence which is coprime
with `yellowstone (n + 1)` but not with `yellowstone n`. -/
def yellowstone : ℕ → ℕ
| 0 := 0
| 1 := 1
| (n + 2) :=
  (yellowstone_step^[n]
    { l := [1, 0],
      a := 2,
      b := 3,
      hab := coprime_iff_gcd_eq_one.2 $ by norm_num,
      ha := dec_trivial,
      hb := dec_trivial }).a

#eval yellowstone 0 -- 0
#eval yellowstone 1 -- 1
#eval yellowstone 2 -- 2
#eval yellowstone 3 -- 3
#eval yellowstone 4 -- 4
#eval yellowstone 5 -- 9
#eval yellowstone 6 -- 8
#eval yellowstone 7 -- 15
#eval yellowstone 8 -- 14
#eval yellowstone 9 -- 5
#eval yellowstone 10 -- 6
#eval yellowstone 11 -- 25
#eval yellowstone 12 -- 12
#eval yellowstone 13 -- 35
#eval yellowstone 14 -- 16
#eval yellowstone 15 -- 7
#eval yellowstone 16 -- 10
#eval yellowstone 17 -- 21
#eval yellowstone 18 -- 20
#eval yellowstone 19 -- 27
#eval yellowstone 20 -- 22

-- Sadly, `yellowstone 20 = 22` is not `rfl` because well-founded recursion does not reduce,
-- and `nat.coprime` uses `nat.gcd` which is defined via well-founded recursion.
-- The solution is to write a `norm_num` extension for `yellowstone`, which shouldn't be too hard.

end nat

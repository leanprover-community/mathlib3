/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import algebra.ne_zero
import data.nat.modeq
import data.fintype.lattice

/-!
# Definition of `zmod n` + basic results.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides the basic details of `zmod n`, including its commutative ring structure.

## Implementation details

This used to be inlined into data/zmod/basic.lean. This file imports `char_p/basic`, which is an
issue; all `char_p` instances create an `algebra (zmod p) R` instance; however, this instance may
not be definitionally equal to other `algebra` instances (for example, `galois_field` also has an
`algebra` instance as it is defined as a `splitting_field`). The way to fix this is to use the
forgetful inheritance pattern, and make `char_p` carry the data of what the `smul` should be (so
for example, the `smul` on the `galois_field` `char_p` instance should be equal to the `smul` from
its `splitting_field` structure); there is only one possible `zmod p` algebra for any `p`, so this
is not an issue mathematically. For this to be possible, however, we need `char_p/basic` to be
able to import some part of `zmod`.

-/

namespace fin

/-!
## Ring structure on `fin n`

We define a commutative ring structure on `fin n`, but we do not register it as instance.
Afterwords, when we define `zmod n` in terms of `fin n`, we use these definitions
to register the ring structure on `zmod n` as type class instance.
-/

open nat.modeq int

/-- Multiplicative commutative semigroup structure on `fin n`. -/
instance (n : ℕ) : comm_semigroup (fin n) :=
{ mul_assoc := λ ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩, fin.eq_of_veq
    (calc ((a * b) % n * c) ≡ a * b * c [MOD n] : (nat.mod_modeq _ _).mul_right _
      ... ≡ a * (b * c) [MOD n] : by rw mul_assoc
      ... ≡ a * (b * c % n) [MOD n] : (nat.mod_modeq _ _).symm.mul_left _),
  mul_comm := fin.mul_comm,
  ..fin.has_mul }

private lemma left_distrib_aux (n : ℕ) : ∀ a b c : fin n, a * (b + c) = a * b + a * c :=
λ ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩, fin.eq_of_veq
(calc a * ((b + c) % n) ≡ a * (b + c) [MOD n] : (nat.mod_modeq _ _).mul_left _
  ... ≡ a * b + a * c [MOD n] : by rw mul_add
  ... ≡ (a * b) % n + (a * c) % n [MOD n] :
        (nat.mod_modeq _ _).symm.add (nat.mod_modeq _ _).symm)

/-- Commutative ring structure on `fin n`. -/
instance (n : ℕ) [ne_zero n] : comm_ring (fin n) :=
{ one_mul := fin.one_mul,
  mul_one := fin.mul_one,
  left_distrib := left_distrib_aux n,
  right_distrib := λ a b c, by rw [mul_comm, left_distrib_aux, mul_comm _ b, mul_comm]; refl,
  ..fin.add_monoid_with_one,
  ..fin.add_comm_group n,
  ..fin.comm_semigroup n }

end fin

/-- The integers modulo `n : ℕ`. -/
def zmod : ℕ → Type
| 0     := ℤ
| (n+1) := fin (n+1)

instance zmod.decidable_eq : Π (n : ℕ), decidable_eq (zmod n)
| 0     := int.decidable_eq
| (n+1) := fin.decidable_eq _

instance zmod.has_repr : Π (n : ℕ), has_repr (zmod n)
| 0     := int.has_repr
| (n+1) := fin.has_repr _

namespace zmod

instance fintype : Π (n : ℕ) [ne_zero n], fintype (zmod n)
| 0    h  := by exactI (ne_zero.ne 0 rfl).elim
| (n+1) _ := fin.fintype (n+1)

instance infinite : infinite (zmod 0) :=
int.infinite

@[simp] lemma card (n : ℕ) [fintype (zmod n)] : fintype.card (zmod n) = n :=
begin
  casesI n,
  { exact (not_finite (zmod 0)).elim },
  { convert fintype.card_fin (n+1) }
end

/- We define each field by cases, to ensure that the eta-expanded `zmod.comm_ring` is defeq to the
original, this helps avoid diamonds with instances coming from classes extending `comm_ring` such as
field. -/
instance comm_ring (n : ℕ) : comm_ring (zmod n) :=
{ add := nat.cases_on n ((@has_add.add) int _) (λ n, @has_add.add (fin n.succ) _),
  add_assoc := nat.cases_on n (@add_assoc int _) (λ n, @add_assoc (fin n.succ) _),
  zero := nat.cases_on n (0 : int) (λ n, (0 : fin n.succ)),
  zero_add := nat.cases_on n (@zero_add int _) (λ n, @zero_add (fin n.succ) _),
  add_zero := nat.cases_on n (@add_zero int _) (λ n, @add_zero (fin n.succ) _),
  neg := nat.cases_on n ((@has_neg.neg) int _) (λ n, @has_neg.neg (fin n.succ) _),
  sub := nat.cases_on n ((@has_sub.sub) int _) (λ n, @has_sub.sub (fin n.succ) _),
  sub_eq_add_neg := nat.cases_on n (@sub_eq_add_neg int _) (λ n, @sub_eq_add_neg (fin n.succ) _),
  zsmul := nat.cases_on n ((@comm_ring.zsmul) int _) (λ n, @comm_ring.zsmul (fin n.succ) _),
  zsmul_zero' := nat.cases_on n (@comm_ring.zsmul_zero' int _)
    (λ n, @comm_ring.zsmul_zero' (fin n.succ) _),
  zsmul_succ' := nat.cases_on n (@comm_ring.zsmul_succ' int _)
    (λ n, @comm_ring.zsmul_succ' (fin n.succ) _),
  zsmul_neg' := nat.cases_on n (@comm_ring.zsmul_neg' int _)
    (λ n, @comm_ring.zsmul_neg' (fin n.succ) _),
  nsmul := nat.cases_on n ((@comm_ring.nsmul) int _) (λ n, @comm_ring.nsmul (fin n.succ) _),
  nsmul_zero' := nat.cases_on n (@comm_ring.nsmul_zero' int _)
    (λ n, @comm_ring.nsmul_zero' (fin n.succ) _),
  nsmul_succ' := nat.cases_on n (@comm_ring.nsmul_succ' int _)
    (λ n, @comm_ring.nsmul_succ' (fin n.succ) _),
  add_left_neg := by { cases n, exacts [@add_left_neg int _, @add_left_neg (fin n.succ) _] },
  add_comm := nat.cases_on n (@add_comm int _) (λ n, @add_comm (fin n.succ) _),
  mul := nat.cases_on n ((@has_mul.mul) int _) (λ n, @has_mul.mul (fin n.succ) _),
  mul_assoc := nat.cases_on n (@mul_assoc int _) (λ n, @mul_assoc (fin n.succ) _),
  one := nat.cases_on n (1 : int) (λ n, (1 : fin n.succ)),
  one_mul := nat.cases_on n (@one_mul int _) (λ n, @one_mul (fin n.succ) _),
  mul_one := nat.cases_on n (@mul_one int _) (λ n, @mul_one (fin n.succ) _),
  nat_cast := nat.cases_on n (coe : ℕ → ℤ) (λ n, (coe : ℕ → fin n.succ)),
  nat_cast_zero := nat.cases_on n (@nat.cast_zero int _) (λ n, @nat.cast_zero (fin n.succ) _),
  nat_cast_succ := nat.cases_on n (@nat.cast_succ int _) (λ n, @nat.cast_succ (fin n.succ) _),
  int_cast := nat.cases_on n (coe : ℤ → ℤ) (λ n, (coe : ℤ → fin n.succ)),
  int_cast_of_nat := nat.cases_on n (@int.cast_of_nat int _) (λ n, @int.cast_of_nat (fin n.succ) _),
  int_cast_neg_succ_of_nat := nat.cases_on n (@int.cast_neg_succ_of_nat int _)
    (λ n, @int.cast_neg_succ_of_nat (fin n.succ) _),
  left_distrib := nat.cases_on n (@left_distrib int _ _ _) (λ n, @left_distrib (fin n.succ) _ _ _),
  right_distrib :=
    nat.cases_on n (@right_distrib int _ _ _) (λ n, @right_distrib (fin n.succ) _ _ _),
  mul_comm := nat.cases_on n (@mul_comm int _) (λ n, @mul_comm (fin n.succ) _) }

instance inhabited (n : ℕ) : inhabited (zmod n) := ⟨0⟩

end zmod

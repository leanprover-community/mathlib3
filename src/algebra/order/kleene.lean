/-
Copyright (c) 2022 Siddhartha Prasad, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Prasad, Yaël Dillies
-/
import algebra.order.ring.canonical
import algebra.ring.pi
import algebra.ring.prod
import order.complete_lattice

/-!
# Kleene Algebras

This file defines idempotent semirings and Kleene algebras, which are used extensively in the theory
of computation.

An idempotent semiring is a semiring whose addition is idempotent. An idempotent semiring is
naturally a semilattice by setting `a ≤ b` if `a + b = b`.

A Kleene algebra is an idempotent semiring equipped with an additional unary operator `∗`, the
Kleene star.

## Main declarations

* `idem_semiring`: Idempotent semiring
* `idem_comm_semiring`: Idempotent commutative semiring
* `kleene_algebra`: Idempotent commutative semiring

## References

* (Kozen, D. . A completeness theorem for Kleene algebras and the algebra of regular events.)
  [https://www.cs.cornell.edu/~kozen/Papers/ka.pdf].
* https://planetmath.org/idempotentsemiring
* https://encyclopediaofmath.org/wiki/Idempotent_semi-ring
* https://planetmath.org/kleene_algebra

## TODO

Instances for `add_opposite`, `mul_opposite`

## Tags

kleene algebra, idempotent semiring
-/

set_option old_structure_cmd true

open function

universe u
variables {α β ι : Type*} {π : ι → Type*}

/-- An idempotent semiring is a semiring with the additional property that addition is idempotent.
-/
@[protect_proj]
class idem_semiring (α : Type u) extends semiring α, semilattice_sup α :=
(sup := (+))
(sup_eq_add : ∀ a b : α, a ⊔ b = a + b . try_refl_tac)
(bot : α := 0)
(bot_le : ∀ a, bot ≤ a)

/-- An idempotent commutative semiring is a commutative semiring with the additional property that
addition is idempotent. -/
@[protect_proj]
class idem_comm_semiring (α : Type u) extends comm_semiring α, idem_semiring α

/-- Notation typeclass for the Kleene star `∗`. -/
@[protect_proj]
class has_kstar (α : Type*) :=
(kstar : α → α)

postfix `∗`:1025 := has_kstar.kstar

/-- A Kleene Algebra is an idempotent semiring with an additional unary operator `kstar` (for Kleene
star) that satisfies the following properties:
* `1 + a * a∗ ≤ a∗`
* `1 + a∗ * a ≤ a∗`
* If `a * c + b ≤ c`, then `a∗ * b ≤ c`
* If `c * a + b ≤ c`, then `b * a∗ ≤ c`
-/
@[protect_proj]
class kleene_algebra (α : Type*) extends idem_semiring α, has_kstar α :=
(one_add_mul_kstar_le : ∀ a : α, 1 + a * a∗ ≤ a∗)
(one_add_kstar_mul_le : ∀ a : α, 1 + a∗ * a ≤ a∗)
(kstar_mul_le_self : ∀ a b : α, a * b ≤ b → a∗ * b ≤ b)
(mul_kstar_le_self : ∀ a b : α, b * a ≤ b → b * a∗ ≤ b)

@[priority 100] -- See note [lower instance priority]
instance idem_semiring.to_order_bot [idem_semiring α] : order_bot α := { ..‹idem_semiring α› }

/-- Construct an idempotent semiring from an idempotent addition. -/
def idem_semiring.of_semiring [semiring α] (h : ∀ a : α, a + a = a) : idem_semiring α :=
{ le := λ a b, a + b = b,
  le_refl := h,
  le_trans := λ a b c (hab : _ = _) (hbc : _ = _), by { change _ = _, rw [←hbc, ←add_assoc, hab] },
  le_antisymm := λ a b (hab : _ = _) (hba : _ = _), by rwa [←hba, add_comm],
  sup := (+),
  le_sup_left := λ a b, by { change _ = _, rw [←add_assoc, h] },
  le_sup_right := λ a b, by { change _ = _, rw [add_comm, add_assoc, h] },
  sup_le := λ a b c hab (hbc : _ = _), by { change _ = _, rwa [add_assoc, hbc] },
  bot := 0,
  bot_le := zero_add,
  ..‹semiring α› }

section idem_semiring
variables [idem_semiring α] {a b c : α}

lemma sup_eq_add (a b : α) : a ⊔ b = a + b := idem_semiring.sup_eq_add _ _
@[simp] lemma add_idem (a : α) : a + a = a := by rw [←sup_eq_add, sup_idem]

lemma nsmul_eq_self : ∀ {n : ℕ} (hn : n ≠ 0) (a : α), n • a = a
| 0 h := (h rfl).elim
| 1 h := one_nsmul
| (n + 2) h := λ a, by rw [succ_nsmul, nsmul_eq_self n.succ_ne_zero, add_idem]

lemma add_eq_left_iff_le : a + b = a ↔ b ≤ a := by rw [←sup_eq_add, sup_eq_left]
lemma add_eq_right_iff_le : a + b = b ↔ a ≤ b := by rw [←sup_eq_add, sup_eq_right]

alias add_eq_left_iff_le ↔ _ has_le.le.add_eq_left
alias add_eq_right_iff_le ↔ _ has_le.le.add_eq_right

@[simp] lemma add_le_iff : a + b ≤ c ↔ a ≤ c ∧ b ≤ c := by rw [←sup_eq_add, sup_le_iff]

@[priority 100] -- See note [lower instance priority]
instance idem_semiring.to_canonically_ordered_add_monoid : canonically_ordered_add_monoid α :=
{ add_le_add_left := λ a b hbc c, by { simp_rw ←sup_eq_add, exact sup_le_sup_left hbc _ },
  exists_add_of_le := λ a b h, ⟨b, h.add_eq_right.symm⟩,
  le_self_add := λ a b, add_eq_right_iff_le.1 $ by rw [←add_assoc, add_idem],
  ..‹idem_semiring α› }

@[priority 100] -- See note [lower instance priority]
instance idem_semiring.to_covariant_class_mul_le : covariant_class α α (*) (≤) :=
⟨λ a b c hbc, add_eq_left_iff_le.1 $ by rw [←mul_add, hbc.add_eq_left]⟩

@[priority 100] -- See note [lower instance priority]
instance idem_semiring.to_covariant_class_swap_mul_le : covariant_class α α (swap (*)) (≤) :=
⟨λ a b c hbc, add_eq_left_iff_le.1 $ by rw [←add_mul, hbc.add_eq_left]⟩

end idem_semiring

section kleene_algebra
variables [kleene_algebra α] {a b c : α}

lemma one_add_mul_kstar_le : 1 + a * a∗ ≤ a∗ := kleene_algebra.one_add_mul_kstar_le _
lemma one_add_kstar_mul_le : 1 + a∗ * a ≤ a∗ := kleene_algebra.one_add_kstar_mul_le _
lemma kstar_mul_le_self : a * b ≤ b → a∗ * b ≤ b := kleene_algebra.kstar_mul_le_self _ _
lemma mul_kstar_le_self : b * a ≤ b → b * a∗ ≤ b := kleene_algebra.mul_kstar_le_self _ _
@[simp] lemma one_le_kstar : 1 ≤ a∗ := le_of_add_le_left one_add_mul_kstar_le

lemma mul_kstar_le (hb : b ≤ c) (ha : c * a ≤ c) : b * a∗ ≤ c :=
(mul_le_mul_right' hb _).trans $ mul_kstar_le_self ha

lemma kstar_mul_le (hb : b ≤ c) (ha : a * c ≤ c) : a∗ * b ≤ c :=
(mul_le_mul_left' hb _).trans $ kstar_mul_le_self ha

lemma kstar_le_of_mul_le_left (hb : 1 ≤ b) : b * a ≤ b → a∗ ≤ b := by simpa using mul_kstar_le hb
lemma kstar_le_of_mul_le_right (hb : 1 ≤ b) : a * b ≤ b → a∗ ≤ b := by simpa using kstar_mul_le hb

-- Yaël: I don't think you need this lemma
-- /-- a∗ * b is the least prefixpoint of the monotone map `x ↦ b + a * x`. -/
-- lemma lfp_monotone : b + a∗ * a * b ≤ a∗ * b :=
-- by simpa [add_mul] using mul_le_mul_right' one_add_kstar_mul_le b

@[simp] lemma le_kstar : a ≤ a∗ :=
le_trans (le_mul_of_one_le_left' one_le_kstar) $ le_of_add_le_right one_add_kstar_mul_le

@[mono] lemma kstar_mono : monotone (has_kstar.kstar : α → α) :=
λ a b h, kstar_le_of_mul_le_left one_le_kstar $ kstar_mul_le (h.trans le_kstar) $
  le_of_add_le_right one_add_mul_kstar_le

@[simp] lemma kstar_eq_one : a∗ = 1 ↔ a ≤ 1 :=
⟨le_kstar.trans_eq, λ h, one_le_kstar.antisymm' $ kstar_le_of_mul_le_left le_rfl $ by rwa one_mul⟩

@[simp] lemma kstar_zero : (0 : α)∗ = 1 := kstar_eq_one.2 zero_le_one
@[simp] lemma kstar_one : (1 : α)∗ = 1 := kstar_eq_one.2 le_rfl

@[simp] lemma kstar_mul_kstar (a : α) : a∗ * a∗ = a∗ :=
(mul_kstar_le le_rfl $ le_of_add_le_right one_add_kstar_mul_le).antisymm $
  le_mul_of_one_le_left' one_le_kstar

@[simp] lemma kstar_eq_self : a∗ = a ↔ a * a = a ∧ 1 ≤ a :=
⟨λ h, ⟨by rw [←h, kstar_mul_kstar], one_le_kstar.trans_eq h⟩, λ h,
  (kstar_le_of_mul_le_left h.2 h.1.le).antisymm le_kstar⟩

@[simp] lemma kstar_idem (a : α) : a∗∗ = a∗ := kstar_eq_self.2 ⟨kstar_mul_kstar _, one_le_kstar⟩

end kleene_algebra

namespace prod

instance [idem_semiring α] [idem_semiring β] : idem_semiring (α × β) :=
{ sup_eq_add := λ a b, ext (sup_eq_add _ _) (sup_eq_add _ _),
  ..prod.semiring, ..prod.semilattice_sup _ _, ..prod.order_bot _ _ }

instance [idem_comm_semiring α] [idem_comm_semiring β] : idem_comm_semiring (α × β) :=
{ ..prod.comm_semiring, ..prod.idem_semiring }

variables [kleene_algebra α] [kleene_algebra β]

instance : kleene_algebra (α × β) :=
{ kstar := λ a, (a.1∗, a.2∗),
  one_add_mul_kstar_le := λ a, ⟨one_add_mul_kstar_le, one_add_mul_kstar_le⟩,
  one_add_kstar_mul_le := λ a, ⟨one_add_kstar_mul_le, one_add_kstar_mul_le⟩,
  kstar_mul_le_self := λ a b h, ⟨kstar_mul_le_self h.1, kstar_mul_le_self h.2⟩,
  mul_kstar_le_self := λ a b h, ⟨mul_kstar_le_self h.1, mul_kstar_le_self h.2⟩,
  ..prod.idem_semiring }

lemma kstar_def (a : α × β) : a∗ = (a.1∗, a.2∗) := rfl
@[simp] lemma fst_kstar (a : α × β) : a∗.1 = a.1∗ := rfl
@[simp] lemma snd_kstar (a : α × β) : a∗.2 = a.2∗ := rfl

end prod

namespace pi

instance [Π i, idem_semiring (π i)] : idem_semiring (Π i, π i) :=
{ sup_eq_add := λ a b, funext $ λ i, sup_eq_add _ _,
  ..pi.semiring, ..pi.semilattice_sup, ..pi.order_bot }

instance [Π i, idem_comm_semiring (π i)] : idem_comm_semiring (Π i, π i) :=
{ ..pi.comm_semiring, ..pi.idem_semiring }

variables [Π i, kleene_algebra (π i)]

instance : kleene_algebra (Π i, π i) :=
{ kstar := λ a i, (a i)∗,
  one_add_mul_kstar_le := λ a i, one_add_mul_kstar_le,
  one_add_kstar_mul_le := λ a i, one_add_kstar_mul_le,
  kstar_mul_le_self := λ a b h i, kstar_mul_le_self $ h _,
  mul_kstar_le_self := λ a b h i, mul_kstar_le_self $ h _,
  ..pi.idem_semiring }

lemma kstar_def (a : Π i, π i) : a∗ = λ i, (a i)∗ := rfl
@[simp] lemma kstar_apply (a : Π i, π i) (i : ι) : a∗ i = (a i)∗ := rfl

end pi

namespace function.injective

/-- Pullback an `idem_semiring` instance along an injective function. -/
@[reducible] -- See note [reducible non-instances]
protected def idem_semiring [idem_semiring α] [has_zero β] [has_one β] [has_add β] [has_mul β]
  [has_pow β ℕ] [has_smul ℕ β] [has_nat_cast β] [has_sup β] [has_bot β]
  (f : β → α) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) (sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (bot : f ⊥ = ⊥) :
  idem_semiring β :=
{ sup_eq_add := λ a b, hf $ by erw [sup, add, sup_eq_add],
  bot := ⊥,
  bot_le := λ a, bot.trans_le $ @bot_le _ _ _ $ f a,
  ..hf.semiring f zero one add mul nsmul npow nat_cast, ..hf.semilattice_sup _ sup, ..‹has_bot β› }

/-- Pullback an `idem_comm_semiring` instance along an injective function. -/
@[reducible] -- See note [reducible non-instances]
protected def idem_comm_semiring [idem_comm_semiring α] [has_zero β] [has_one β] [has_add β]
  [has_mul β] [has_pow β ℕ] [has_smul ℕ β] [has_nat_cast β] [has_sup β] [has_bot β]
  (f : β → α) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) (sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (bot : f ⊥ = ⊥) :
  idem_comm_semiring β :=
{ ..hf.comm_semiring f zero one add mul nsmul npow nat_cast,
  ..hf.idem_semiring f zero one add mul nsmul npow nat_cast sup bot }

/-- Pullback an `idem_comm_semiring` instance along an injective function. -/
@[reducible] -- See note [reducible non-instances]
protected def kleene_algebra [kleene_algebra α] [has_zero β] [has_one β] [has_add β]
  [has_mul β] [has_pow β ℕ] [has_smul ℕ β] [has_nat_cast β] [has_sup β] [has_bot β] [has_kstar β]
  (f : β → α) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) (sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (bot : f ⊥ = ⊥)
  (kstar : ∀ a, f a∗ = (f a)∗) :
  kleene_algebra β :=
{ one_add_mul_kstar_le := λ a,
    by { change f _ ≤ _, erw [add, one, mul, kstar], exact one_add_mul_kstar_le },
  one_add_kstar_mul_le := λ a,
    by { change f _ ≤ _, erw [add, one, mul, kstar], exact one_add_kstar_mul_le },
  kstar_mul_le_self := λ a b (h : f _ ≤ _),
    by { change f _ ≤ _, erw [mul, kstar], erw mul at h, exact kstar_mul_le_self h },
  mul_kstar_le_self := λ a b (h : f _ ≤ _),
    by { change f _ ≤ _, erw [mul, kstar], erw mul at h, exact mul_kstar_le_self h },
  ..hf.idem_semiring f zero one add mul nsmul npow nat_cast sup bot, ..‹has_kstar β› }

end function.injective

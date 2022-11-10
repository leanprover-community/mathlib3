/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
import algebra.group_with_zero.power
import algebra.parity
import data.rat.nnrat

/-!
# Lemmas about division (semi)rings and (semi)fields

-/

open function order_dual set
open_locale nnrat

set_option old_structure_cmd true

universe u
variables {α β K : Type*}

/-- The default definition of the coercion `(↑(a : ℚ≥0) : K)` for a division semiring `K` is defined
as `(a / b : K) = (a : K) * (b : K)⁻¹`. Use `coe` instead of `nnrat.cast_rec` for better
definitional behaviour. -/
def nnrat.cast_rec [has_lift_t ℕ K] [has_mul K] [has_inv K] : ℚ≥0 → K := λ q, ↑q.num * (↑q.denom)⁻¹

/-- The default definition of the coercion `(↑(a : ℚ) : K)` for a division ring `K`
is defined as `(a / b : K) = (a : K) * (b : K)⁻¹`.
Use `coe` instead of `rat.cast_rec` for better definitional behaviour.
-/
def rat.cast_rec [has_lift_t ℕ K] [has_lift_t ℤ K] [has_mul K] [has_inv K] : ℚ → K :=
λ q, ↑q.1 * (↑q.2)⁻¹

/-- Type class for the canonical homomorphism `ℚ≥0 → K`. -/
@[protect_proj]
class has_nnrat_cast (K : Type u) :=
(nnrat_cast : ℚ≥0 → K)

/--
Type class for the canonical homomorphism `ℚ → K`.
-/
@[protect_proj]
class has_rat_cast (K : Type u) :=
(rat_cast : ℚ → K)

/-- Construct the canonical injection from `ℚ≥0` into an arbitrary division semiring. If the
semifield has positive characteristic `p`, we define `1 / p = 1 / 0 = 0` for consistency with our
division by zero convention. -/
@[priority 900] -- see Note [coercion into rings]
instance nnrat.cast_coe [has_nnrat_cast K] : has_coe_t ℚ≥0 K :=⟨has_nnrat_cast.nnrat_cast⟩

/-- Construct the canonical injection from `ℚ` into an arbitrary division ring. If the field has
positive characteristic `p`, we define `1 / p = 1 / 0 = 0` for consistency with our division by zero
convention. -/
@[priority 900] -- see Note [coercion into rings]
instance rat.cast_coe {K : Type*} [has_rat_cast K] : has_coe_t ℚ K := ⟨has_rat_cast.rat_cast⟩

/-- The default definition of the scalar multiplication `(a : ℚ≥0) • (x : K)` for a division
semiring `K` is given by `a • x = (↑ a) * x`.
Use `(a : ℚ≥0) • (x : K)` instead of `qsmul_rec` for better definitional behaviour. -/
def nnqsmul_rec (coe : ℚ≥0 → K) [has_mul K] (a : ℚ≥0) (x : K) : K := coe a * x

/-- The default definition of the scalar multiplication `(a : ℚ) • (x : K)` for a division ring `K`
is given by `a • x = (↑ a) * x`.
Use `(a : ℚ) • (x : K)` instead of `qsmul_rec` for better definitional behaviour.
-/
def qsmul_rec (coe : ℚ → K) [has_mul K] (a : ℚ) (x : K) : K :=
coe a * x

/-- A `division_semiring` is a `semiring` with multiplicative inverses for nonzero elements. -/
@[protect_proj, ancestor semiring group_with_zero]
class division_semiring (α : Type u) extends semiring α, group_with_zero α, has_nnrat_cast α :=
(nnrat_cast := nnrat.cast_rec)
(nnrat_cast_eq : ∀ q, nnrat_cast q = q.num / q.denom . try_refl_tac)
(nnqsmul : ℚ≥0 → α → α := nnqsmul_rec nnrat_cast)
(nnqsmul_eq_mul : ∀ a x, nnqsmul a x = nnrat_cast a * x . try_refl_tac)

/-- A `division_ring` is a `ring` with multiplicative inverses for nonzero elements.

An instance of `division_ring K` includes maps `of_rat : ℚ → K` and `qsmul : ℚ → K → K`.
If the division ring has positive characteristic p, we define `of_rat (1 / p) = 1 / 0 = 0`
for consistency with our division by zero convention.
The fields `of_rat` and `qsmul` are needed to implement the
`algebra_rat [division_ring K] : algebra ℚ K` instance, since we need to control the specific
definitions for some special cases of `K` (in particular `K = ℚ` itself).
See also Note [forgetful inheritance].
-/
@[protect_proj, ancestor ring div_inv_monoid nontrivial]
class division_ring (K : Type u)
  extends ring K, div_inv_monoid K, nontrivial K, has_nnrat_cast K, has_rat_cast K :=
(mul_inv_cancel : ∀ {a : K}, a ≠ 0 → a * a⁻¹ = 1)
(inv_zero : (0 : K)⁻¹ = 0)
(nnrat_cast := nnrat.cast_rec)
(nnrat_cast_eq : ∀ q, nnrat_cast q = q.num / q.denom . try_refl_tac)
(nnqsmul : ℚ≥0 → K → K := nnqsmul_rec nnrat_cast)
(nnqsmul_eq_mul : ∀ a x, nnqsmul a x = nnrat_cast a * x . try_refl_tac)
(rat_cast := rat.cast_rec)
(rat_cast_mk : ∀ (a : ℤ) (b : ℕ) h1 h2, rat_cast ⟨a, b, h1, h2⟩ = a * b⁻¹ . try_refl_tac)
(qsmul : ℚ → K → K := qsmul_rec rat_cast)
(qsmul_eq_mul' : ∀ (a : ℚ) (x : K), qsmul a x = rat_cast a * x . try_refl_tac)

@[priority 100] -- see Note [lower instance priority]
instance division_ring.to_division_semiring [division_ring α] : division_semiring α :=
{ ..‹division_ring α›, ..(infer_instance : semiring α) }

section division_ring
variables [division_ring α] {n : ℤ}

@[simp] lemma zpow_bit1_neg (x : α) (n : ℤ) : (-x) ^ bit1 n = - x ^ bit1 n :=
by rw [zpow_bit1', zpow_bit1', neg_mul_neg, neg_mul_eq_mul_neg]

lemma odd.neg_zpow (h : odd n) (a : α) : (-a) ^ n = - a ^ n :=
by { obtain ⟨k, rfl⟩ := h.exists_bit1, exact zpow_bit1_neg _ _ }

lemma odd.neg_one_zpow (h : odd n) : (-1 : α) ^ n = -1 := by rw [h.neg_zpow, one_zpow]

end division_ring

/-- A `semifield` is a `comm_semiring` with multiplicative inverses for nonzero elements. -/
@[protect_proj, ancestor comm_semiring division_semiring comm_group_with_zero]
class semifield (α : Type*) extends comm_semiring α, division_semiring α, comm_group_with_zero α

/-- A `field` is a `comm_ring` with multiplicative inverses for nonzero elements.

An instance of `field K` includes maps `of_rat : ℚ → K` and `qsmul : ℚ → K → K`.
If the field has positive characteristic p, we define `of_rat (1 / p) = 1 / 0 = 0`
for consistency with our division by zero convention.
The fields `of_rat` and `qsmul are needed to implement the
`algebra_rat [division_ring K] : algebra ℚ K` instance, since we need to control the specific
definitions for some special cases of `K` (in particular `K = ℚ` itself).
See also Note [forgetful inheritance].
-/
@[protect_proj, ancestor comm_ring div_inv_monoid nontrivial]
class field (K : Type u) extends comm_ring K, division_ring K

section division_semiring
variables [division_semiring α] {a b c d : α}

namespace nnrat

lemma cast_def : ∀ q : ℚ≥0, (q : α) = q.num / q.denom := division_semiring.nnrat_cast_eq

@[priority 100]
instance division_semiring.to_has_nnqsmul : has_smul ℚ≥0 α := ⟨division_semiring.nnqsmul⟩

lemma smul_def : ∀ (q : ℚ≥0) (a : α), q • a = ↑q * a := division_semiring.nnqsmul_eq_mul

end nnrat

lemma add_div (a b c : α) : (a + b) / c = a / c + b / c := by simp_rw [div_eq_mul_inv, add_mul]

@[field_simps] lemma div_add_div_same (a b c : α) : a / c + b / c = (a + b) / c :=
(add_div _ _ _).symm

lemma same_add_div (h : b ≠ 0) : (b + a) / b = 1 + a / b := by rw [←div_self h, add_div]
lemma div_add_same (h : b ≠ 0) : (a + b) / b = a / b + 1 := by rw [←div_self h, add_div]
lemma one_add_div (h : b ≠ 0 ) : 1 + a / b = (b + a) / b := (same_add_div h).symm
lemma div_add_one (h : b ≠ 0) : a / b + 1 = (a + b) / b := (div_add_same h).symm

lemma one_div_mul_add_mul_one_div_eq_one_div_add_one_div (ha : a ≠ 0) (hb : b ≠ 0) :
  (1 / a) * (a + b) * (1 / b) = 1 / a + 1 / b :=
by rw [mul_add, one_div_mul_cancel ha, add_mul, one_mul, mul_assoc, mul_one_div_cancel hb, mul_one,
  add_comm]

lemma add_div_eq_mul_add_div (a b : α) (hc : c ≠ 0) : a + b / c = (a * c + b) / c :=
(eq_div_iff_mul_eq hc).2 $ by rw [right_distrib, (div_mul_cancel _ hc)]

@[field_simps] lemma add_div' (a b c : α) (hc : c ≠ 0) : b + a / c = (b * c + a) / c :=
by rw [add_div, mul_div_cancel _ hc]

@[field_simps] lemma div_add' (a b c : α) (hc : c ≠ 0) : a / c + b = (a + b * c) / c :=
by rwa [add_comm, add_div', add_comm]

lemma commute.div_add_div (hbc : commute b c) (hbd : commute b d) (hb : b ≠ 0) (hd : d ≠ 0) :
  a / b + c / d = (a * d + b * c) / (b * d) :=
by rw [add_div, mul_div_mul_right _ b hd, hbc.eq, hbd.eq, mul_div_mul_right c d hb]

end division_semiring

section division_monoid
variables [division_monoid K] [has_distrib_neg K] {a b : K}

lemma one_div_neg_one_eq_neg_one : (1:K) / (-1) = -1 :=
have (-1) * (-1) = (1:K), by rw [neg_mul_neg, one_mul],
eq.symm (eq_one_div_of_mul_eq_one_right this)

lemma one_div_neg_eq_neg_one_div (a : K) : 1 / (- a) = - (1 / a) :=
calc
  1 / (- a) = 1 / ((-1) * a)        : by rw neg_eq_neg_one_mul
        ... = (1 / a) * (1 / (- 1)) : by rw one_div_mul_one_div_rev
        ... = (1 / a) * (-1)        : by rw one_div_neg_one_eq_neg_one
        ... = - (1 / a)             : by rw [mul_neg, mul_one]

lemma div_neg_eq_neg_div (a b : K) : b / (- a) = - (b / a) :=
calc
  b / (- a) = b * (1 / (- a)) : by rw [← inv_eq_one_div, division_def]
        ... = b * -(1 / a)    : by rw one_div_neg_eq_neg_one_div
        ... = -(b * (1 / a))  : by rw neg_mul_eq_mul_neg
        ... = - (b / a)       : by rw mul_one_div

lemma neg_div (a b : K) : (-b) / a = - (b / a) :=
by rw [neg_eq_neg_one_mul, mul_div_assoc, ← neg_eq_neg_one_mul]

@[field_simps] lemma neg_div' (a b : K) : - (b / a) = (-b) / a :=
by simp [neg_div]

lemma neg_div_neg_eq (a b : K) : (-a) / (-b) = a / b :=
by rw [div_neg_eq_neg_div, neg_div, neg_neg]

lemma neg_inv : - a⁻¹ = (- a)⁻¹ :=
by rw [inv_eq_one_div, inv_eq_one_div, div_neg_eq_neg_div]

lemma div_neg (a : K) : a / -b = -(a / b) :=
by rw [← div_neg_eq_neg_div]

lemma inv_neg : (-a)⁻¹ = -(a⁻¹) :=
by rw neg_inv

end division_monoid

section division_ring
variables [division_ring K] {a b : K}

@[simp] lemma div_neg_self {a : K} (h : a ≠ 0) : a / -a = -1 :=
by rw [div_neg_eq_neg_div, div_self h]

@[simp] lemma neg_div_self {a : K} (h : a ≠ 0) : (-a) / a = -1 :=
by rw [neg_div, div_self h]

lemma div_sub_div_same (a b c : K) : (a / c) - (b / c) = (a - b) / c :=
by rw [sub_eq_add_neg, ← neg_div, div_add_div_same, sub_eq_add_neg]

lemma same_sub_div {a b : K} (h : b ≠ 0) : (b - a) / b = 1 - a / b :=
by simpa only [← @div_self _ _ b h] using (div_sub_div_same b a b).symm

lemma one_sub_div {a b : K} (h : b ≠ 0) : 1 - a / b = (b - a) / b := (same_sub_div h).symm

lemma div_sub_same {a b : K} (h : b ≠ 0) : (a - b) / b = a / b - 1 :=
by simpa only [← @div_self _ _ b h] using (div_sub_div_same a b b).symm

lemma div_sub_one {a b : K} (h : b ≠ 0) : a / b - 1 = (a - b) / b := (div_sub_same h).symm

lemma sub_div (a b c : K) : (a - b) / c = a / c - b / c :=
(div_sub_div_same _ _ _).symm

lemma one_div_mul_sub_mul_one_div_eq_one_div_add_one_div (ha : a ≠ 0) (hb : b ≠ 0) :
          (1 / a) * (b - a) * (1 / b) = 1 / a - 1 / b :=
by rw [(mul_sub_left_distrib (1 / a)), (one_div_mul_cancel ha), mul_sub_right_distrib,
       one_mul, mul_assoc, (mul_one_div_cancel hb), mul_one]

@[priority 100] -- see Note [lower instance priority]
instance division_ring.is_domain : is_domain K :=
{ ..‹division_ring K›,
  ..(by apply_instance : no_zero_divisors K) }

end division_ring

section semifield
variables [semifield α] {a b c d : α}

lemma div_add_div (a : α) (c : α) (hb : b ≠ 0) (hd : d ≠ 0) :
  (a / b) + (c / d) = ((a * d) + (b * c)) / (b * d) :=
(commute.all b _).div_add_div (commute.all _ _) hb hd

lemma one_div_add_one_div (ha : a ≠ 0) (hb : b ≠ 0) : 1 / a + 1 / b = (a + b) / (a * b) :=
by rw [div_add_div _ _ ha hb, one_mul, mul_one, add_comm]

lemma inv_add_inv (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ + b⁻¹ = (a + b) / (a * b) :=
by rw [inv_eq_one_div, inv_eq_one_div, one_div_add_one_div ha hb]

end semifield

section field

variable [field K]

local attribute [simp] mul_assoc mul_comm mul_left_comm

@[field_simps] lemma div_sub_div (a : K) {b : K} (c : K) {d : K} (hb : b ≠ 0) (hd : d ≠ 0) :
  (a / b) - (c / d) = ((a * d) - (b * c)) / (b * d) :=
begin
  simp [sub_eq_add_neg],
  rw [neg_eq_neg_one_mul, ← mul_div_assoc, div_add_div _ _ hb hd,
      ← mul_assoc, mul_comm b, mul_assoc, ← neg_eq_neg_one_mul]
end

lemma inv_sub_inv {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ - b⁻¹ = (b - a) / (a * b) :=
by rw [inv_eq_one_div, inv_eq_one_div, div_sub_div _ _ ha hb, one_mul, mul_one]

@[field_simps] lemma sub_div' (a b c : K) (hc : c ≠ 0) : b - a / c = (b * c - a) / c :=
by simpa using div_sub_div b a one_ne_zero hc

@[field_simps] lemma div_sub' (a b c : K) (hc : c ≠ 0) : a / c - b = (a - c * b) / c :=
by simpa using div_sub_div a b hc one_ne_zero

@[priority 100] -- see Note [lower instance priority]
instance field.is_domain : is_domain K :=
{ ..division_ring.is_domain }

end field

namespace ring_hom

protected lemma injective [division_ring α] [semiring β] [nontrivial β] (f : α →+* β) :
  injective f :=
(injective_iff_map_eq_zero f).2 $ λ x, (map_eq_zero f).1

end ring_hom

section noncomputable_defs

variables {R : Type*} [nontrivial R]

/-- Constructs a `division_ring` structure on a `ring` consisting only of units and 0. -/
noncomputable def division_ring_of_is_unit_or_eq_zero [hR : ring R]
  (h : ∀ (a : R), is_unit a ∨ a = 0) : division_ring R :=
{ .. (group_with_zero_of_is_unit_or_eq_zero h), .. hR }

/-- Constructs a `field` structure on a `comm_ring` consisting only of units and 0.
See note [reducible non-instances]. -/
@[reducible]
noncomputable def field_of_is_unit_or_eq_zero [hR : comm_ring R]
  (h : ∀ (a : R), is_unit a ∨ a = 0) : field R :=
{ .. (group_with_zero_of_is_unit_or_eq_zero h), .. hR }

end noncomputable_defs

/-- Pullback a `division_semiring` along an injective function. -/
@[reducible] -- See note [reducible non-instances]
protected def function.injective.division_semiring [division_semiring β] [has_zero α] [has_mul α]
  [has_add α] [has_one α] [has_inv α] [has_div α] [has_smul ℕ α] [has_smul ℚ≥0 α] [has_pow α ℕ]
  [has_pow α ℤ] [has_nat_cast α] [has_nnrat_cast α]
  (f : α → β) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (inv : ∀ x, f (x⁻¹) = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (nnqsmul : ∀ x (n : ℚ≥0), f (n • x) = n • f x)
  (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ x (n : ℤ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) (nnrat_cast : ∀ n : ℚ≥0, f n = n) :
  division_semiring α :=
{ nnrat_cast := coe,
  nnrat_cast_eq := λ q, hf $ by erw [nnrat_cast, nnrat.cast_def, div, nat_cast, nat_cast],
  nnqsmul := (•),
  nnqsmul_eq_mul := λ a x, hf $ by erw [nnqsmul, mul, nnrat_cast, nnrat.smul_def],
  .. hf.group_with_zero f zero one mul inv div npow zpow,
  .. hf.semiring f zero one add mul nsmul npow nat_cast }

/-- Pullback a `division_ring` along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.division_ring [division_ring K] {K'}
  [has_zero K'] [has_one K'] [has_add K'] [has_mul K'] [has_neg K'] [has_sub K'] [has_inv K']
  [has_div K'] [has_smul ℕ K'] [has_smul ℤ K'] [has_smul ℚ≥0 K'] [has_smul ℚ K'] [has_pow K' ℕ]
  [has_pow K' ℤ] [has_nat_cast K'] [has_int_cast K'] [has_nnrat_cast K'] [has_rat_cast K']
  (f : K' → K) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
  (inv : ∀ x, f (x⁻¹) = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ x (n : ℤ), f (n • x) = n • f x)
  (nnqsmul : ∀ x (n : ℚ≥0), f (n • x) = n • f x) (qsmul : ∀ x (n : ℚ), f (n • x) = n • f x)
  (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ x (n : ℤ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) (nnrat_cast : ∀ n : ℚ≥0, f n = n)
  (rat_cast : ∀ n : ℚ, f n = n) :
  division_ring K' :=
{ rat_cast := coe,
  rat_cast_mk := λ a b h1 h2, hf (by erw [rat_cast, mul, inv, int_cast, nat_cast];
                                     exact division_ring.rat_cast_mk a b h1 h2),
  qsmul := (•),
  qsmul_eq_mul' := λ a x, hf (by erw [qsmul, mul, rat.smul_def, rat_cast]),
  .. hf.division_semiring f zero one add mul inv div nsmul nnqsmul npow zpow nat_cast nnrat_cast,
  .. hf.ring f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast }

/-- Pullback a `field` along an injective function. -/
@[reducible] -- See note [reducible non-instances]
protected def function.injective.semifield [semifield β] [has_zero α] [has_mul α] [has_add α]
  [has_one α] [has_inv α] [has_div α] [has_smul ℕ α] [has_smul ℚ≥0 α] [has_pow α ℕ] [has_pow α ℤ]
  [has_nat_cast α] [has_nnrat_cast α]
  (f : α → β) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (inv : ∀ x, f (x⁻¹) = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (nnqsmul : ∀ x (n : ℚ≥0), f (n • x) = n • f x)
  (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ x (n : ℤ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) (nnrat_cast : ∀ n : ℚ≥0, f n = n) :
  semifield α :=
{ .. hf.division_semiring f zero one add mul inv div nsmul nnqsmul npow zpow nat_cast nnrat_cast,
  .. hf.comm_semiring f zero one add mul nsmul npow nat_cast }

/-- Pullback a `field` along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.field [field K] {K'}
  [has_zero K'] [has_mul K'] [has_add K'] [has_neg K'] [has_sub K'] [has_one K'] [has_inv K']
  [has_div K'] [has_smul ℕ K'] [has_smul ℤ K'] [has_smul ℚ≥0 K'] [has_smul ℚ K'] [has_pow K' ℕ]
  [has_pow K' ℤ] [has_nat_cast K'] [has_int_cast K'] [has_nnrat_cast K'] [has_rat_cast K']
  (f : K' → K) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
  (inv : ∀ x, f (x⁻¹) = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ x (n : ℤ), f (n • x) = n • f x)
  (nnqsmul : ∀ x (n : ℚ≥0), f (n • x) = n • f x) (qsmul : ∀ x (n : ℚ), f (n • x) = n • f x)
  (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ x (n : ℤ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) (nnrat_cast : ∀ n : ℚ≥0, f n = n)
  (rat_cast : ∀ n : ℚ, f n = n) :
  field K' :=
{ rat_cast := coe,
  rat_cast_mk := λ a b h1 h2, hf (by erw [rat_cast, mul, inv, int_cast, nat_cast];
                                     exact division_ring.rat_cast_mk a b h1 h2),
  qsmul := (•),
  qsmul_eq_mul' := λ a x, hf (by erw [qsmul, mul, rat.smul_def, rat_cast]),
  .. hf.division_semiring f zero one add mul inv div nsmul nnqsmul npow zpow nat_cast nnrat_cast,
  .. hf.comm_ring f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast }

/-! ### Order dual -/

instance [h : has_rat_cast α] : has_rat_cast αᵒᵈ := h
instance [h : division_semiring α] : division_semiring αᵒᵈ := h
instance [h : division_ring α] : division_ring αᵒᵈ := h
instance [h : semifield α] : semifield αᵒᵈ := h
instance [h : field α] : field αᵒᵈ := h

@[simp] lemma to_dual_rat_cast [has_rat_cast α] (n : ℚ) : to_dual (n : α) = n := rfl
@[simp] lemma of_dual_rat_cast [has_rat_cast α] (n : ℚ) : (of_dual n : α) = n := rfl

/-! ### Lexicographic order -/

instance [h : has_rat_cast α] : has_rat_cast (lex α) := h
instance [h : division_semiring α] : division_semiring (lex α) := h
instance [h : division_ring α] : division_ring (lex α) := h
instance [h : semifield α] : semifield (lex α) := h
instance [h : field α] : field (lex α) := h

@[simp] lemma to_lex_rat_cast [has_rat_cast α] (n : ℚ) : to_lex (n : α) = n := rfl
@[simp] lemma of_lex_rat_cast [has_rat_cast α] (n : ℚ) : (of_lex n : α) = n := rfl

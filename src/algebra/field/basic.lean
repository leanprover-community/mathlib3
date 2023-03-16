/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
import algebra.field.defs
import algebra.group_with_zero.units.lemmas
import algebra.hom.ring
import algebra.ring.inj_surj

/-!
# Lemmas about division (semi)rings and (semi)fields

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/

open function order_dual set

set_option old_structure_cmd true

universe u
variables {α β K : Type*}

section division_semiring
variables [division_semiring α] {a b c : α}

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

/-- See `inv_sub_inv` for the more convenient version when `K` is commutative. -/
lemma inv_sub_inv' {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ - b⁻¹ = a⁻¹ * (b - a) * b⁻¹ :=
by rw [mul_sub, sub_mul, mul_inv_cancel_right₀ hb, inv_mul_cancel ha, one_mul]

lemma one_div_mul_sub_mul_one_div_eq_one_div_add_one_div (ha : a ≠ 0) (hb : b ≠ 0) :
          (1 / a) * (b - a) * (1 / b) = 1 / a - 1 / b :=
by rw [(mul_sub_left_distrib (1 / a)), (one_div_mul_cancel ha), mul_sub_right_distrib,
       one_mul, mul_assoc, (mul_one_div_cancel hb), mul_one]

@[priority 100] -- see Note [lower instance priority]
instance division_ring.is_domain : is_domain K :=
no_zero_divisors.to_is_domain _

end division_ring

section semifield
variables [semifield α] {a b c d : α}

lemma div_add_div (a : α) (c : α) (hb : b ≠ 0) (hd : d ≠ 0) :
  (a / b) + (c / d) = ((a * d) + (b * c)) / (b * d) :=
by rw [← mul_div_mul_right _ b hd, ← mul_div_mul_left c d hb, div_add_div_same]

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
  [has_add α] [has_one α] [has_inv α] [has_div α] [has_smul ℕ α] [has_pow α ℕ] [has_pow α ℤ]
  [has_nat_cast α]
  (f : α → β) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (inv : ∀ x, f (x⁻¹) = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x)
  (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ x (n : ℤ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) :
  division_semiring α :=
{ .. hf.group_with_zero f zero one mul inv div npow zpow,
  .. hf.semiring f zero one add mul nsmul npow nat_cast }

/-- Pullback a `division_ring` along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.division_ring [division_ring K] {K'}
  [has_zero K'] [has_one K'] [has_add K'] [has_mul K'] [has_neg K'] [has_sub K'] [has_inv K']
  [has_div K'] [has_smul ℕ K'] [has_smul ℤ K'] [has_smul ℚ K'] [has_pow K' ℕ] [has_pow K' ℤ]
  [has_nat_cast K'] [has_int_cast K'] [has_rat_cast K']
  (f : K' → K) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
  (inv : ∀ x, f (x⁻¹) = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ x (n : ℤ), f (n • x) = n • f x)
  (qsmul : ∀ x (n : ℚ), f (n • x) = n • f x)
  (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ x (n : ℤ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) (rat_cast : ∀ n : ℚ, f n = n) :
  division_ring K' :=
{ rat_cast := coe,
  rat_cast_mk := λ a b h1 h2, hf (by erw [rat_cast, mul, inv, int_cast, nat_cast];
                                     exact division_ring.rat_cast_mk a b h1 h2),
  qsmul := (•),
  qsmul_eq_mul' := λ a x, hf (by erw [qsmul, mul, rat.smul_def, rat_cast]),
  .. hf.group_with_zero f zero one mul inv div npow zpow,
  .. hf.ring f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast }

/-- Pullback a `field` along an injective function. -/
@[reducible] -- See note [reducible non-instances]
protected def function.injective.semifield [semifield β] [has_zero α] [has_mul α] [has_add α]
  [has_one α] [has_inv α] [has_div α] [has_smul ℕ α] [has_pow α ℕ] [has_pow α ℤ]
  [has_nat_cast α]
  (f : α → β) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (inv : ∀ x, f (x⁻¹) = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x)
  (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ x (n : ℤ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) :
  semifield α :=
{ .. hf.comm_group_with_zero f zero one mul inv div npow zpow,
  .. hf.comm_semiring f zero one add mul nsmul npow nat_cast }

/-- Pullback a `field` along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.field [field K] {K'}
  [has_zero K'] [has_mul K'] [has_add K'] [has_neg K'] [has_sub K'] [has_one K'] [has_inv K']
  [has_div K'] [has_smul ℕ K'] [has_smul ℤ K'] [has_smul ℚ K'] [has_pow K' ℕ] [has_pow K' ℤ]
  [has_nat_cast K'] [has_int_cast K'] [has_rat_cast K']
  (f : K' → K) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
  (inv : ∀ x, f (x⁻¹) = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ x (n : ℤ), f (n • x) = n • f x)
  (qsmul : ∀ x (n : ℚ), f (n • x) = n • f x)
  (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ x (n : ℤ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) (rat_cast : ∀ n : ℚ, f n = n) :
  field K' :=
{ rat_cast := coe,
  rat_cast_mk := λ a b h1 h2, hf (by erw [rat_cast, mul, inv, int_cast, nat_cast];
                                     exact division_ring.rat_cast_mk a b h1 h2),
  qsmul := (•),
  qsmul_eq_mul' := λ a x, hf (by erw [qsmul, mul, rat.smul_def, rat_cast]),
  .. hf.comm_group_with_zero f zero one mul inv div npow zpow,
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

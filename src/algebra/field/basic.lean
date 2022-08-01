/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
import algebra.hom.ring
import data.rat.defs

/-!
# Division (semi)rings and (semi)fields

This file introduces fields and division rings (also known as skewfields) and proves some basic
statements about them. For a more extensive theory of fields, see the `field_theory` folder.

## Main definitions

* `division_semiring`: Nontrivial semiring with multiplicative inverses for nonzero elements.
* `division_ring`: : Nontrivial ring with multiplicative inverses for nonzero elements.
* `semifield`: Commutative division semiring.
* `field`: Commutative division ring.
* `is_field`: Predicate on a (semi)ring that it is a (semi)field, i.e. that the multiplication is
  commutative, that it has more than one element and that all non-zero elements have a
  multiplicative inverse. In contrast to `field`, which contains the data of a function associating
  to an element of the field its multiplicative inverse, this predicate only assumes the existence
  and can therefore more easily be used to e.g. transfer along ring isomorphisms.

## Implementation details

By convention `0⁻¹ = 0` in a field or division ring. This is due to the fact that working with total
functions has the advantage of not constantly having to check that `x ≠ 0` when writing `x⁻¹`. With
this convention in place, some statements like `(a + b) * c⁻¹ = a * c⁻¹ + b * c⁻¹` still remain
true, while others like the defining property `a * a⁻¹ = 1` need the assumption `a ≠ 0`. If you are
a beginner in using Lean and are confused by that, you can read more about why this convention is
taken in Kevin Buzzard's
[blogpost](https://xenaproject.wordpress.com/2020/07/05/division-by-zero-in-type-theory-a-faq/)

A division ring or field is an example of a `group_with_zero`. If you cannot find
a division ring / field lemma that does not involve `+`, you can try looking for
a `group_with_zero` lemma instead.

## Tags

field, division ring, skew field, skew-field, skewfield
-/

open function set

set_option old_structure_cmd true

universe u
variables {α β K : Type*}

/-- The default definition of the coercion `(↑(a : ℚ) : K)` for a division ring `K`
is defined as `(a / b : K) = (a : K) * (b : K)⁻¹`.
Use `coe` instead of `rat.cast_rec` for better definitional behaviour.
-/
def rat.cast_rec [has_lift_t ℕ K] [has_lift_t ℤ K] [has_mul K] [has_inv K] : ℚ → K
| ⟨a, b, _, _⟩ := ↑a * (↑b)⁻¹

/--
Type class for the canonical homomorphism `ℚ → K`.
-/
@[protect_proj]
class has_rat_cast (K : Type u) :=
(rat_cast : ℚ → K)

/-- The default definition of the scalar multiplication `(a : ℚ) • (x : K)` for a division ring `K`
is given by `a • x = (↑ a) * x`.
Use `(a : ℚ) • (x : K)` instead of `qsmul_rec` for better definitional behaviour.
-/
def qsmul_rec (coe : ℚ → K) [has_mul K] (a : ℚ) (x : K) : K :=
coe a * x

/-- A `division_semiring` is a `semiring` with multiplicative inverses for nonzero elements. -/
@[protect_proj, ancestor semiring group_with_zero]
class division_semiring (α : Type*) extends semiring α, group_with_zero α

/-- A `division_ring` is a `ring` with multiplicative inverses for nonzero elements.

An instance of `division_ring K` includes maps `of_rat : ℚ → K` and `qsmul : ℚ → K → K`.
If the division ring has positive characteristic p, we define `of_rat (1 / p) = 1 / 0 = 0`
for consistency with our division by zero convention.
The fields `of_rat` and `qsmul are needed to implement the
`algebra_rat [division_ring K] : algebra ℚ K` instance, since we need to control the specific
definitions for some special cases of `K` (in particular `K = ℚ` itself).
See also Note [forgetful inheritance].
-/
@[protect_proj, ancestor ring div_inv_monoid nontrivial]
class division_ring (K : Type u) extends ring K, div_inv_monoid K, nontrivial K, has_rat_cast K :=
(mul_inv_cancel : ∀ {a : K}, a ≠ 0 → a * a⁻¹ = 1)
(inv_zero : (0 : K)⁻¹ = 0)
(rat_cast := rat.cast_rec)
(rat_cast_mk : ∀ (a : ℤ) (b : ℕ) h1 h2, rat_cast ⟨a, b, h1, h2⟩ = a * b⁻¹ . try_refl_tac)
(qsmul : ℚ → K → K := qsmul_rec rat_cast)
(qsmul_eq_mul' : ∀ (a : ℚ) (x : K), qsmul a x = rat_cast a * x . try_refl_tac)

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

@[priority 100] -- see Note [lower instance priority]
instance division_ring.to_division_semiring [division_ring α] : division_semiring α :=
{ ..‹division_ring α›, ..(infer_instance : semiring α) }

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

section division_ring
variables [division_ring K] {a b : K}

namespace rat

/-- Construct the canonical injection from `ℚ` into an arbitrary
  division ring. If the field has positive characteristic `p`,
  we define `1 / p = 1 / 0 = 0` for consistency with our
  division by zero convention. -/
-- see Note [coercion into rings]
@[priority 900] instance cast_coe {K : Type*} [has_rat_cast K] : has_coe_t ℚ K :=
⟨has_rat_cast.rat_cast⟩

theorem cast_mk' (a b h1 h2) : ((⟨a, b, h1, h2⟩ : ℚ) : K) = a * b⁻¹ :=
division_ring.rat_cast_mk _ _ _ _

theorem cast_def : ∀ (r : ℚ), (r : K) = r.num / r.denom
| ⟨a, b, h1, h2⟩ := (cast_mk' _ _ _ _).trans (div_eq_mul_inv _ _).symm

@[priority 100]
instance smul_division_ring : has_smul ℚ K :=
⟨division_ring.qsmul⟩

lemma smul_def (a : ℚ) (x : K) : a • x = ↑a * x := division_ring.qsmul_eq_mul' a x

end rat

local attribute [simv]
  division_def mul_comm mul_assoc
  mul_left_comm mul_inv_cancel inv_mul_cancel

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
by simv [neg_div]

lemma neg_div_neg_eq (a b : K) : (-a) / (-b) = a / b :=
by rw [div_neg_eq_neg_div, neg_div, neg_neg]

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

lemma neg_inv : - a⁻¹ = (- a)⁻¹ :=
by rw [inv_eq_one_div, inv_eq_one_div, div_neg_eq_neg_div]

lemma sub_div (a b c : K) : (a - b) / c = a / c - b / c :=
(div_sub_div_same _ _ _).symm

lemma div_neg (a : K) : a / -b = -(a / b) :=
by rw [← div_neg_eq_neg_div]

lemma inv_neg : (-a)⁻¹ = -(a⁻¹) :=
by rw neg_inv

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
by rw [← mul_div_mul_right _ b hd, ← mul_div_mul_left c d hb, div_add_div_same]

lemma one_div_add_one_div (ha : a ≠ 0) (hb : b ≠ 0) : 1 / a + 1 / b = (a + b) / (a * b) :=
by rw [div_add_div _ _ ha hb, one_mul, mul_one, add_comm]

lemma inv_add_inv (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ + b⁻¹ = (a + b) / (a * b) :=
by rw [inv_eq_one_div, inv_eq_one_div, one_div_add_one_div ha hb]

end semifield

section field

variable [field K]

@[priority 100] -- see Note [lower instance priority]
instance field.to_semifield : semifield K :=
{ .. ‹field K›, .. (infer_instance : semiring K) }

local attribute [simv] mul_assoc mul_comm mul_left_comm

@[field_simps] lemma div_sub_div (a : K) {b : K} (c : K) {d : K} (hb : b ≠ 0) (hd : d ≠ 0) :
  (a / b) - (c / d) = ((a * d) - (b * c)) / (b * d) :=
begin
  simv [sub_eq_add_neg],
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

section is_field

/-- A predicate to express that a (semi)ring is a (semi)field.

This is mainly useful because such a predicate does not contain data,
and can therefore be easily transported along ring isomorphisms.
Additionaly, this is useful when trying to prove that
a particular ring structure extends to a (semi)field. -/
structure is_field (R : Type u) [semiring R] : Prop :=
(exists_pair_ne : ∃ (x y : R), x ≠ y)
(mul_comm : ∀ (x y : R), x * y = y * x)
(mul_inv_cancel : ∀ {a : R}, a ≠ 0 → ∃ b, a * b = 1)

/-- Transferring from `semifield` to `is_field`. -/
lemma semifield.to_is_field (R : Type u) [semifield R] : is_field R :=
{ mul_inv_cancel := λ a ha, ⟨a⁻¹, mul_inv_cancel ha⟩,
  ..‹semifield R› }

/-- Transferring from `field` to `is_field`. -/
lemma field.to_is_field (R : Type u) [field R] : is_field R := semifield.to_is_field _

@[simp] lemma is_field.nontrivial {R : Type u} [semiring R] (h : is_field R) : nontrivial R :=
⟨h.exists_pair_ne⟩

@[simp] lemma not_is_field_of_subsingleton (R : Type u) [semiring R] [subsingleton R] :
  ¬is_field R :=
λ h, let ⟨x, y, h⟩ := h.exists_pair_ne in h (subsingleton.elim _ _)

open_locale classical

/-- Transferring from `is_field` to `semifield`. -/
noncomputable def is_field.to_semifield {R : Type u} [semiring R] (h : is_field R) : semifield R :=
{ inv := λ a, if ha : a = 0 then 0 else classical.some (is_field.mul_inv_cancel h ha),
  inv_zero := dif_pos rfl,
  mul_inv_cancel := λ a ha,
    begin
      convert classical.some_spec (is_field.mul_inv_cancel h ha),
      exact dif_neg ha
    end,
  .. ‹semiring R›, ..h }

/-- Transferring from `is_field` to `field`. -/
noncomputable def is_field.to_field {R : Type u} [ring R] (h : is_field R) : field R :=
{ .. ‹ring R›, ..is_field.to_semifield h }

/-- For each field, and for each nonzero element of said field, there is a unique inverse.
Since `is_field` doesn't remember the data of an `inv` function and as such,
a lemma that there is a unique inverse could be useful.
-/
lemma uniq_inv_of_is_field (R : Type u) [ring R] (hf : is_field R) :
  ∀ (x : R), x ≠ 0 → ∃! (y : R), x * y = 1 :=
begin
  intros x hx,
  apply exists_unique_of_exists_of_unique,
  { exact hf.mul_inv_cancel hx },
  { intros y z hxy hxz,
    calc y = y * (x * z) : by rw [hxz, mul_one]
       ... = (x * y) * z : by rw [← mul_assoc, hf.mul_comm y x]
       ... = z           : by rw [hxy, one_mul] }
end

end is_field

namespace ring_hom
section semiring
variables [semiring α] [division_semiring β]

@[simp] lemma map_units_inv (f : α →+* β) (u : αˣ) : f ↑u⁻¹ = (f ↑u)⁻¹ :=
(f : α →* β).map_units_inv u

variables [nontrivial α] (f : β →+* α) {a : β}

@[simp] lemma map_eq_zero : f a = 0 ↔ a = 0 := f.to_monoid_with_zero_hom.map_eq_zero
lemma map_ne_zero : f a ≠ 0 ↔ a ≠ 0 := f.to_monoid_with_zero_hom.map_ne_zero

end semiring

section division_semiring
variables [division_semiring α] [division_semiring β] (f : α →+* β) (a b : α)

lemma map_inv : f a⁻¹ = (f a)⁻¹ := f.to_monoid_with_zero_hom.map_inv _
lemma map_div : f (a / b) = f a / f b := f.to_monoid_with_zero_hom.map_div _ _

end division_semiring

protected lemma injective [division_ring α] [semiring β] [nontrivial β] (f : α →+* β) :
  injective f :=
(injective_iff_map_eq_zero f).2 $ λ x, f.map_eq_zero.1

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

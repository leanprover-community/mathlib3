/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
-/
import algebra.group.to_additive
import tactic.basic

/-!
# Typeclasses for (semi)groups and monoid

In this file we define typeclasses for algebraic structures with one binary operation.
The classes are named `(add_)?(comm_)?(semigroup|monoid|group)`, where `add_` means that
the class uses additive notation and `comm_` means that the class assumes that the binary
operation is commutative.

The file does not contain any lemmas except for

* axioms of typeclasses restated in the root namespace;
* lemmas required for instances.

For basic lemmas about these classes see `algebra.group.basic`.
-/

set_option default_priority 100
set_option old_structure_cmd true

universe u

/- Additive "sister" structures.
   Example, add_semigroup mirrors semigroup.
   These structures exist just to help automation.
   In an alternative design, we could have the binary operation as an
   extra argument for semigroup, monoid, group, etc. However, the lemmas
   would be hard to index since they would not contain any constant.
   For example, mul_assoc would be

   lemma mul_assoc {α : Type u} {op : α → α → α} [semigroup α op] :
                   ∀ a b c : α, op (op a b) c = op a (op b c) :=
    semigroup.mul_assoc

   The simplifier cannot effectively use this lemma since the pattern for
   the left-hand-side would be

        ?op (?op ?a ?b) ?c

   Remark: we use a tactic for transporting theorems from the multiplicative fragment
   to the additive one.
-/

/-- A semigroup is a type with an associative `(*)`. -/
@[protect_proj, ancestor has_mul] class semigroup (G : Type u) extends has_mul G :=
(mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
/-- An additive semigroup is a type with an associative `(+)`. -/
@[protect_proj, ancestor has_add] class add_semigroup (G : Type u) extends has_add G :=
(add_assoc : ∀ a b c : G, a + b + c = a + (b + c))
attribute [to_additive add_semigroup] semigroup

section semigroup
variables {G : Type u} [semigroup G]

@[no_rsimp, to_additive]
lemma mul_assoc : ∀ a b c : G, a * b * c = a * (b * c) :=
semigroup.mul_assoc

attribute [no_rsimp] add_assoc -- TODO(Mario): find out why this isn't copying

@[to_additive]
instance semigroup.to_is_associative : is_associative G (*) :=
⟨mul_assoc⟩

end semigroup

/-- A commutative semigroup is a type with an associative commutative `(*)`. -/
@[protect_proj, ancestor semigroup]
class comm_semigroup (G : Type u) extends semigroup G :=
(mul_comm : ∀ a b : G, a * b = b * a)

/-- A commutative additive semigroup is a type with an associative commutative `(+)`. -/
@[protect_proj, ancestor add_semigroup]
class add_comm_semigroup (G : Type u) extends add_semigroup G :=
(add_comm : ∀ a b : G, a + b = b + a)
attribute [to_additive add_comm_semigroup] comm_semigroup

section comm_semigroup
variables {G : Type u} [comm_semigroup G]

@[no_rsimp, to_additive]
lemma mul_comm : ∀ a b : G, a * b = b * a :=
comm_semigroup.mul_comm
attribute [no_rsimp] add_comm

@[to_additive]
instance comm_semigroup.to_is_commutative : is_commutative G (*) :=
⟨mul_comm⟩

end comm_semigroup

/-- A `left_cancel_semigroup` is a semigroup such that `a * b = a * c` implies `b = c`. -/
@[protect_proj, ancestor semigroup]
class left_cancel_semigroup (G : Type u) extends semigroup G :=
(mul_left_cancel : ∀ a b c : G, a * b = a * c → b = c)
/-- An `add_left_cancel_semigroup` is an additive semigroup such that
`a + b = a + c` implies `b = c`. -/
@[protect_proj, ancestor add_semigroup]
class add_left_cancel_semigroup (G : Type u) extends add_semigroup G :=
(add_left_cancel : ∀ a b c : G, a + b = a + c → b = c)
attribute [to_additive add_left_cancel_semigroup] left_cancel_semigroup

section left_cancel_semigroup
variables {G : Type u} [left_cancel_semigroup G] {a b c : G}

@[to_additive]
lemma mul_left_cancel : a * b = a * c → b = c :=
left_cancel_semigroup.mul_left_cancel a b c

@[to_additive]
lemma mul_left_cancel_iff : a * b = a * c ↔ b = c :=
⟨mul_left_cancel, congr_arg _⟩

@[to_additive]
theorem mul_right_injective (a : G) : function.injective ((*) a) :=
λ b c, mul_left_cancel

@[simp, to_additive]
theorem mul_right_inj (a : G) {b c : G} : a * b = a * c ↔ b = c :=
⟨mul_left_cancel, congr_arg _⟩

end left_cancel_semigroup

/-- A `right_cancel_semigroup` is a semigroup such that `a * b = c * b` implies `a = c`. -/
@[protect_proj, ancestor semigroup]
class right_cancel_semigroup (G : Type u) extends semigroup G :=
(mul_right_cancel : ∀ a b c : G, a * b = c * b → a = c)

/-- An `add_right_cancel_semigroup` is an additive semigroup such that
`a + b = c + b` implies `a = c`. -/
@[protect_proj, ancestor add_semigroup]
class add_right_cancel_semigroup (G : Type u) extends add_semigroup G :=
(add_right_cancel : ∀ a b c : G, a + b = c + b → a = c)
attribute [to_additive add_right_cancel_semigroup] right_cancel_semigroup

section right_cancel_semigroup
variables {G : Type u} [right_cancel_semigroup G] {a b c : G}

@[to_additive]
lemma mul_right_cancel : a * b = c * b → a = c :=
right_cancel_semigroup.mul_right_cancel a b c

@[to_additive]
lemma mul_right_cancel_iff : b * a = c * a ↔ b = c :=
⟨mul_right_cancel, congr_arg _⟩

@[to_additive]
theorem mul_left_injective (a : G) : function.injective (λ x, x * a) :=
λ b c, mul_right_cancel

@[simp, to_additive]
theorem mul_left_inj (a : G) {b c : G} : b * a = c * a ↔ b = c :=
⟨mul_right_cancel, congr_arg _⟩

end right_cancel_semigroup

/-- A `monoid` is a `semigroup` with an element `1` such that `1 * a = a * 1 = a`. -/
@[ancestor semigroup has_one]
class monoid (M : Type u) extends semigroup M, has_one M :=
(one_mul : ∀ a : M, 1 * a = a) (mul_one : ∀ a : M, a * 1 = a)
/-- An `add_monoid` is an `add_semigroup` with an element `0` such that `0 + a = a + 0 = a`. -/
@[ancestor add_semigroup has_zero]
class add_monoid (M : Type u) extends add_semigroup M, has_zero M :=
(zero_add : ∀ a : M, 0 + a = a) (add_zero : ∀ a : M, a + 0 = a)
attribute [to_additive add_monoid] monoid

section monoid
variables {M : Type u} [monoid M]

@[ematch, simp, to_additive]
lemma one_mul : ∀ a : M, 1 * a = a :=
monoid.one_mul

@[ematch, simp, to_additive]
lemma mul_one : ∀ a : M, a * 1 = a :=
monoid.mul_one

attribute [ematch] add_zero zero_add -- TODO(Mario): Make to_additive transfer this

@[to_additive add_monoid_to_is_left_id]
instance monoid_to_is_left_id : is_left_id M (*) 1 :=
⟨ monoid.one_mul ⟩

@[to_additive add_monoid_to_is_right_id]
instance monoid_to_is_right_id : is_right_id M (*) 1 :=
⟨ monoid.mul_one ⟩

@[to_additive]
lemma left_inv_eq_right_inv {a b c : M} (hba : b * a = 1) (hac : a * c = 1) : b = c :=
by rw [←one_mul c, ←hba, mul_assoc, hac, mul_one b]

end monoid

/-- A commutative monoid is a monoid with commutative `(*)`. -/
@[protect_proj, ancestor monoid comm_semigroup]
class comm_monoid (M : Type u) extends monoid M, comm_semigroup M

/-- An additive commutative monoid is an additive monoid with commutative `(+)`. -/
@[protect_proj, ancestor add_monoid add_comm_semigroup]
class add_comm_monoid (M : Type u) extends add_monoid M, add_comm_semigroup M
attribute [to_additive add_comm_monoid] comm_monoid

/-- A monoid in which multiplication is left-cancellative. -/
@[protect_proj, ancestor left_cancel_semigroup monoid]
class left_cancel_monoid (M : Type u) extends left_cancel_semigroup M, monoid M

/-- An additive monoid in which addition is left-cancellative.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `add_left_cancel_semigroup` is not enough. -/
@[protect_proj, ancestor add_left_cancel_semigroup add_monoid]
class add_left_cancel_monoid (M : Type u) extends add_left_cancel_semigroup M, add_monoid M
-- TODO: I found 1 (one) lemma assuming `[add_left_cancel_monoid]`.
-- Should we port more lemmas to this typeclass?

attribute [to_additive add_left_cancel_monoid] left_cancel_monoid

/-- A `group` is a `monoid` with an operation `⁻¹` satisfying `a⁻¹ * a = 1`. -/
@[protect_proj, ancestor monoid has_inv]
class group (α : Type u) extends monoid α, has_inv α :=
(mul_left_inv : ∀ a : α, a⁻¹ * a = 1)
/-- An `add_group` is an `add_monoid` with a unary `-` satisfying `-a + a = 0`. -/
@[protect_proj, ancestor add_monoid has_neg]
class add_group (α : Type u) extends add_monoid α, has_neg α :=
(add_left_neg : ∀ a : α, -a + a = 0)
attribute [to_additive add_group] group

section group
variables {G : Type u} [group G] {a b c : G}

@[simp, to_additive]
lemma mul_left_inv : ∀ a : G, a⁻¹ * a = 1 :=
group.mul_left_inv

@[to_additive] lemma inv_mul_self (a : G) : a⁻¹ * a = 1 := mul_left_inv a

@[simp, to_additive]
lemma inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b :=
by rw [← mul_assoc, mul_left_inv, one_mul]

@[simp, to_additive]
lemma inv_eq_of_mul_eq_one (h : a * b = 1) : a⁻¹ = b :=
left_inv_eq_right_inv (inv_mul_self a) h

@[simp, to_additive]
lemma inv_inv (a : G) : (a⁻¹)⁻¹ = a :=
inv_eq_of_mul_eq_one (mul_left_inv a)

@[simp, to_additive]
lemma mul_right_inv (a : G) : a * a⁻¹ = 1 :=
have a⁻¹⁻¹ * a⁻¹ = 1 := mul_left_inv a⁻¹,
by rwa [inv_inv] at this

@[to_additive] lemma mul_inv_self (a : G) : a * a⁻¹ = 1 := mul_right_inv a

@[simp, to_additive]
lemma mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a :=
by rw [mul_assoc, mul_right_inv, mul_one]

@[to_additive to_left_cancel_add_semigroup]
instance group.to_left_cancel_semigroup : left_cancel_semigroup G :=
{ mul_left_cancel := λ a b c h, by rw [← inv_mul_cancel_left a b, h, inv_mul_cancel_left],
  ..‹group G› }

@[to_additive to_right_cancel_add_semigroup]
instance group.to_right_cancel_semigroup : right_cancel_semigroup G :=
{ mul_right_cancel := λ a b c h, by rw [← mul_inv_cancel_right a b, h, mul_inv_cancel_right],
  ..‹group G› }

end group

section add_group

variables {G : Type u} [add_group G]

@[reducible] protected def algebra.sub (a b : G) : G :=
a + -b

instance add_group_has_sub : has_sub G :=
⟨algebra.sub⟩

lemma sub_eq_add_neg (a b : G) : a - b = a + -b :=
rfl

instance add_group.to_add_left_cancel_monoid : add_left_cancel_monoid G :=
{ ..‹add_group G›, .. add_group.to_left_cancel_add_semigroup }

end add_group

/-- A commutative group is a group with commutative `(*)`. -/
@[protect_proj, ancestor group comm_monoid]
class comm_group (G : Type u) extends group G, comm_monoid G
/-- An additive commutative group is an additive group with commutative `(+)`. -/
@[protect_proj, ancestor add_group add_comm_monoid]
class add_comm_group (G : Type u) extends add_group G, add_comm_monoid G
attribute [to_additive add_comm_group] comm_group
attribute [instance, priority 300] add_comm_group.to_add_comm_monoid

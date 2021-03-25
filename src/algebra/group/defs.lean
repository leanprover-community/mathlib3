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

section has_mul

variables {G : Type u} [has_mul G]

/-- `left_mul g` denotes left multiplication by `g` -/
@[to_additive "`left_add g` denotes left addition by `g`"]
def left_mul : G → G → G := λ g : G, λ x : G, g * x

/-- `right_mul g` denotes right multiplication by `g` -/
@[to_additive "`right_add g` denotes right addition by `g`"]
def right_mul : G → G → G := λ g : G, λ x : G, x * g

end has_mul

/-- A semigroup is a type with an associative `(*)`. -/
@[protect_proj, ancestor has_mul] class semigroup (G : Type u) extends has_mul G :=
(mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
/-- An additive semigroup is a type with an associative `(+)`. -/
@[protect_proj, ancestor has_add] class add_semigroup (G : Type u) extends has_add G :=
(add_assoc : ∀ a b c : G, a + b + c = a + (b + c))
attribute [to_additive] semigroup

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
attribute [to_additive] comm_semigroup

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
(mul_right_injective a).eq_iff

@[to_additive]
theorem mul_ne_mul_right (a : G) {b c : G} : a * b ≠ a * c ↔ b ≠ c :=
(mul_right_injective a).ne_iff

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
(mul_left_injective a).eq_iff

@[to_additive]
theorem mul_ne_mul_left (a : G) {b c : G} : b * a ≠ c * a ↔ b ≠ c :=
(mul_left_injective a).ne_iff

end right_cancel_semigroup

/-- Typeclass for expressing that a type `M` with multiplication and a one satisfies
`1 * a = a` and `a * 1 = a` for all `a : M`. -/
@[ancestor has_one has_mul]
class mul_one_class (M : Type u) extends has_one M, has_mul M :=
(one_mul : ∀ (a : M), 1 * a = a)
(mul_one : ∀ (a : M), a * 1 = a)

/-- Typeclass for expressing that a type `M` with addition and a zero satisfies
`0 + a = a` and `a + 0 = a` for all `a : M`. -/
@[ancestor has_zero has_add]
class add_zero_class (M : Type u) extends has_zero M, has_add M :=
(zero_add : ∀ (a : M), 0 + a = a)
(add_zero : ∀ (a : M), a + 0 = a)

attribute [to_additive] mul_one_class

section mul_one_class
variables {M : Type u} [mul_one_class M]

@[ematch, simp, to_additive]
lemma one_mul : ∀ a : M, 1 * a = a :=
mul_one_class.one_mul

@[ematch, simp, to_additive]
lemma mul_one : ∀ a : M, a * 1 = a :=
mul_one_class.mul_one

attribute [ematch] add_zero zero_add -- TODO(Mario): Make to_additive transfer this

end mul_one_class

/-- A `monoid` is a `semigroup` with an element `1` such that `1 * a = a * 1 = a`. -/
@[ancestor semigroup mul_one_class]
class monoid (M : Type u) extends semigroup M, mul_one_class M

/-- An `add_monoid` is an `add_semigroup` with an element `0` such that `0 + a = a + 0 = a`. -/
@[ancestor add_semigroup add_zero_class]
class add_monoid (M : Type u) extends add_semigroup M, add_zero_class M

attribute [to_additive] monoid

section monoid
variables {M : Type u} [monoid M]

@[to_additive]
instance monoid_to_is_left_id : is_left_id M (*) 1 :=
⟨ monoid.one_mul ⟩

@[to_additive]
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
attribute [to_additive] comm_monoid

section left_cancel_monoid

/-- An additive monoid in which addition is left-cancellative.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `add_left_cancel_semigroup` is not enough. -/
@[protect_proj, ancestor add_left_cancel_semigroup add_monoid]
class add_left_cancel_monoid (M : Type u) extends add_left_cancel_semigroup M, add_monoid M
-- TODO: I found 1 (one) lemma assuming `[add_left_cancel_monoid]`.
-- Should we port more lemmas to this typeclass?

/-- A monoid in which multiplication is left-cancellative. -/
@[protect_proj, ancestor left_cancel_semigroup monoid, to_additive add_left_cancel_monoid]
class left_cancel_monoid (M : Type u) extends left_cancel_semigroup M, monoid M

/-- Commutative version of add_left_cancel_monoid. -/
@[protect_proj, ancestor add_left_cancel_monoid add_comm_monoid]
class add_left_cancel_comm_monoid (M : Type u) extends add_left_cancel_monoid M, add_comm_monoid M

/-- Commutative version of left_cancel_monoid. -/
@[protect_proj, ancestor left_cancel_monoid comm_monoid, to_additive add_left_cancel_comm_monoid]
class left_cancel_comm_monoid (M : Type u) extends left_cancel_monoid M, comm_monoid M

end left_cancel_monoid

section right_cancel_monoid

/-- An additive monoid in which addition is right-cancellative.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `add_right_cancel_semigroup` is not enough. -/
@[protect_proj, ancestor add_right_cancel_semigroup add_monoid]
class add_right_cancel_monoid (M : Type u) extends add_right_cancel_semigroup M, add_monoid M

/-- A monoid in which multiplication is right-cancellative. -/
@[protect_proj, ancestor right_cancel_semigroup monoid, to_additive add_right_cancel_monoid]
class right_cancel_monoid (M : Type u) extends right_cancel_semigroup M, monoid M

/-- Commutative version of add_right_cancel_monoid. -/
@[protect_proj, ancestor add_right_cancel_monoid add_comm_monoid]
class add_right_cancel_comm_monoid (M : Type u) extends add_right_cancel_monoid M, add_comm_monoid M

/-- Commutative version of right_cancel_monoid. -/
@[protect_proj, ancestor right_cancel_monoid comm_monoid, to_additive add_right_cancel_comm_monoid]
class right_cancel_comm_monoid (M : Type u) extends right_cancel_monoid M, comm_monoid M

end right_cancel_monoid

section cancel_monoid

/-- An additive monoid in which addition is cancellative on both sides.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `add_right_cancel_semigroup` is not enough. -/
@[protect_proj, ancestor add_left_cancel_monoid add_right_cancel_monoid]
class add_cancel_monoid (M : Type u)
  extends add_left_cancel_monoid M, add_right_cancel_monoid M

/-- A monoid in which multiplication is cancellative. -/
@[protect_proj, ancestor left_cancel_monoid right_cancel_monoid, to_additive add_cancel_monoid]
class cancel_monoid (M : Type u) extends left_cancel_monoid M, right_cancel_monoid M

/-- Commutative version of add_cancel_monoid. -/
@[protect_proj, ancestor add_left_cancel_comm_monoid add_right_cancel_comm_monoid]
class add_cancel_comm_monoid (M : Type u)
  extends add_left_cancel_comm_monoid M, add_right_cancel_comm_monoid M

/-- Commutative version of cancel_monoid. -/
@[protect_proj, ancestor left_cancel_comm_monoid right_cancel_comm_monoid,
  to_additive add_cancel_comm_monoid]
class cancel_comm_monoid (M : Type u) extends left_cancel_comm_monoid M, right_cancel_comm_monoid M

end cancel_monoid

/-- `try_refl_tac` solves goals of the form `∀ a b, f a b = g a b`,
if they hold by definition. -/
meta def try_refl_tac : tactic unit := `[intros; refl]

/-- A `div_inv_monoid` is a `monoid` with operations `/` and `⁻¹` satisfying
`div_eq_mul_inv : ∀ a b, a / b = a * b⁻¹`.

This is the immediate common ancestor of `group` and `group_with_zero`,
in order to deduplicate the name `div_eq_mul_inv`.
The default for `div` is such that `a / b = a * b⁻¹` holds by definition.

Adding `div` as a field rather than defining `a / b := a * b⁻¹` allows us to
avoid certain classes of unification failures, for example:
Let `foo X` be a type with a `∀ X, has_div (foo X)` instance but no
`∀ X, has_inv (foo X)`, e.g. when `foo X` is a `euclidean_domain`. Suppose we
also have an instance `∀ X [cromulent X], group_with_zero (foo X)`. Then the
`(/)` coming from `group_with_zero_has_div` cannot be definitionally equal to
the `(/)` coming from `foo.has_div`.
-/
@[protect_proj, ancestor monoid has_inv has_div]
class div_inv_monoid (G : Type u) extends monoid G, has_inv G, has_div G :=
(div := λ a b, a * b⁻¹)
(div_eq_mul_inv : ∀ a b : G, a / b = a * b⁻¹ . try_refl_tac)

/-- A `sub_neg_monoid` is an `add_monoid` with unary `-` and binary `-` operations
satisfying `sub_eq_add_neg : ∀ a b, a - b = a + -b`.

The default for `sub` is such that `a - b = a + -b` holds by definition.

Adding `sub` as a field rather than defining `a - b := a + -b` allows us to
avoid certain classes of unification failures, for example:
Let `foo X` be a type with a `∀ X, has_sub (foo X)` instance but no
`∀ X, has_neg (foo X)`. Suppose we also have an instance
`∀ X [cromulent X], add_group (foo X)`. Then the `(-)` coming from
`add_group.has_sub` cannot be definitionally equal to the `(-)` coming from
`foo.has_sub`.
-/
@[protect_proj, ancestor add_monoid has_neg has_sub]
class sub_neg_monoid (G : Type u) extends add_monoid G, has_neg G, has_sub G :=
(sub := λ a b, a + -b)
(sub_eq_add_neg : ∀ a b : G, a - b = a + -b . try_refl_tac)

attribute [to_additive sub_neg_monoid] div_inv_monoid

@[to_additive]
lemma div_eq_mul_inv {G : Type u} [div_inv_monoid G] :
  ∀ a b : G, a / b = a * b⁻¹ :=
div_inv_monoid.div_eq_mul_inv

/-- A `group` is a `monoid` with an operation `⁻¹` satisfying `a⁻¹ * a = 1`.

There is also a division operation `/` such that `a / b = a * b⁻¹`,
with a default so that `a / b = a * b⁻¹` holds by definition.
-/
@[protect_proj, ancestor div_inv_monoid]
class group (G : Type u) extends div_inv_monoid G :=
(mul_left_inv : ∀ a : G, a⁻¹ * a = 1)

/-- An `add_group` is an `add_monoid` with a unary `-` satisfying `-a + a = 0`.

There is also a binary operation `-` such that `a - b = a + -b`,
with a default so that `a - b = a + -b` holds by definition.
-/
@[protect_proj, ancestor sub_neg_monoid]
class add_group (A : Type u) extends sub_neg_monoid A :=
(add_left_neg : ∀ a : A, -a + a = 0)

attribute [to_additive] group

/-- Abbreviation for `@div_inv_monoid.to_monoid _ (@group.to_div_inv_monoid _ _)`.

Useful because it corresponds to the fact that `Grp` is a subcategory of `Mon`.
Not an instance since it duplicates `@div_inv_monoid.to_monoid _ (@group.to_div_inv_monoid _ _)`.
-/
@[to_additive
"Abbreviation for `@sub_neg_monoid.to_add_monoid _ (@add_group.to_sub_neg_monoid _ _)`.

Useful because it corresponds to the fact that `AddGroup` is a subcategory of `AddMon`.
Not an instance since it duplicates
`@sub_neg_monoid.to_add_monoid _ (@add_group.to_sub_neg_monoid _ _)`."]
def group.to_monoid (G : Type u) [group G] : monoid G :=
@div_inv_monoid.to_monoid _ (@group.to_div_inv_monoid _ _)

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

@[priority 100, to_additive]    -- see Note [lower instance priority]
instance group.to_cancel_monoid : cancel_monoid G :=
{ mul_right_cancel := λ a b c h, by rw [← mul_inv_cancel_right a b, h, mul_inv_cancel_right],
  mul_left_cancel := λ a b c h, by rw [← inv_mul_cancel_left a b, h, inv_mul_cancel_left],
  ..‹group G› }

end group

/-- A commutative group is a group with commutative `(*)`. -/
@[protect_proj, ancestor group comm_monoid]
class comm_group (G : Type u) extends group G, comm_monoid G
/-- An additive commutative group is an additive group with commutative `(+)`. -/
@[protect_proj, ancestor add_group add_comm_monoid]
class add_comm_group (G : Type u) extends add_group G, add_comm_monoid G
attribute [to_additive] comm_group
attribute [instance, priority 300] add_comm_group.to_add_comm_monoid

section comm_group

variables {G : Type u} [comm_group G]

@[priority 100, to_additive]    -- see Note [lower instance priority]
instance comm_group.to_cancel_comm_monoid : cancel_comm_monoid G :=
{ ..‹comm_group G›,
  ..group.to_cancel_monoid }

end comm_group

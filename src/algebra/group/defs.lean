/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
-/
import algebra.group.to_additive
import tactic.basic

/-!
# Typeclasses for (semi)groups and monoids

In this file we define typeclasses for algebraic structures with one binary operation.
The classes are named `(add_)?(comm_)?(semigroup|monoid|group)`, where `add_` means that
the class uses additive notation and `comm_` means that the class assumes that the binary
operation is commutative.

The file does not contain any lemmas except for

* axioms of typeclasses restated in the root namespace;
* lemmas required for instances.

For basic lemmas about these classes see `algebra.group.basic`.

We also introduce notation classes `has_scalar` and `has_vadd` for multiplicative and additive
actions and register the following instances:

- `has_pow M ℕ`, for monoids `M`, and `has_pow G ℤ` for groups `G`;
- `has_scalar ℕ M` for additive monoids `M`, and `has_scalar ℤ G` for additive groups `G`.

## Notation

- `+`, `-`, `*`, `/`, `^` : the usual arithmetic operations; the underlying functions are
  `has_add.add`, `has_neg.neg`/`has_sub.sub`, `has_mul.mul`, `has_div.div`, and `has_pow.pow`.
- `a • b` is used as notation for `has_scalar.smul a b`.
- `a +ᵥ b` is used as notation for `has_vadd.vadd a b`.

-/

open function

/-- Type class for the `+ᵥ` notation. -/
class has_vadd (G : Type*) (P : Type*) := (vadd : G → P → P)

/-- Type class for the `-ᵥ` notation. -/
class has_vsub (G : out_param Type*) (P : Type*) := (vsub : P → P → G)

/-- Typeclass for types with a scalar multiplication operation, denoted `•` (`\bu`) -/
@[ext, to_additive has_vadd]
class has_scalar (M : Type*) (α : Type*) := (smul : M → α → α)

infix ` +ᵥ `:65 := has_vadd.vadd
infix ` -ᵥ `:65 := has_vsub.vsub
infixr ` • `:73 := has_scalar.smul

attribute [to_additive_reorder 1] has_pow
attribute [to_additive_reorder 1 4] has_pow.pow
attribute [to_additive has_scalar] has_pow
attribute [to_additive has_scalar.smul] has_pow.pow

set_option old_structure_cmd true

universe u

variables {G : Type*}

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

mk_simp_attribute field_simps "The simpset `field_simps` is used by the tactic `field_simp` to
reduce an expression in a field to an expression of the form `n / d` where `n` and `d` are
division-free."

section has_mul
variables [has_mul G]

/-- `left_mul g` denotes left multiplication by `g` -/
@[to_additive "`left_add g` denotes left addition by `g`"]
def left_mul : G → G → G := λ g : G, λ x : G, g * x

/-- `right_mul g` denotes right multiplication by `g` -/
@[to_additive "`right_add g` denotes right addition by `g`"]
def right_mul : G → G → G := λ g : G, λ x : G, x * g

end has_mul

/-- A semigroup is a type with an associative `(*)`. -/
@[protect_proj, ancestor has_mul, ext] class semigroup (G : Type u) extends has_mul G :=
(mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
/-- An additive semigroup is a type with an associative `(+)`. -/
@[protect_proj, ancestor has_add, ext] class add_semigroup (G : Type u) extends has_add G :=
(add_assoc : ∀ a b c : G, a + b + c = a + (b + c))
attribute [to_additive] semigroup

section semigroup
variables [semigroup G]

@[no_rsimp, to_additive]
lemma mul_assoc : ∀ a b c : G, a * b * c = a * (b * c) :=
semigroup.mul_assoc

@[to_additive]
instance semigroup.to_is_associative : is_associative G (*) :=
⟨mul_assoc⟩

end semigroup

/-- A commutative semigroup is a type with an associative commutative `(*)`. -/
@[protect_proj, ancestor semigroup, ext]
class comm_semigroup (G : Type u) extends semigroup G :=
(mul_comm : ∀ a b : G, a * b = b * a)

/-- A commutative additive semigroup is a type with an associative commutative `(+)`. -/
@[protect_proj, ancestor add_semigroup, ext]
class add_comm_semigroup (G : Type u) extends add_semigroup G :=
(add_comm : ∀ a b : G, a + b = b + a)
attribute [to_additive] comm_semigroup

section comm_semigroup
variables [comm_semigroup G]

@[no_rsimp, to_additive]
lemma mul_comm : ∀ a b : G, a * b = b * a :=
comm_semigroup.mul_comm

@[to_additive]
instance comm_semigroup.to_is_commutative : is_commutative G (*) :=
⟨mul_comm⟩

end comm_semigroup

/-- A `left_cancel_semigroup` is a semigroup such that `a * b = a * c` implies `b = c`. -/
@[protect_proj, ancestor semigroup, ext]
class left_cancel_semigroup (G : Type u) extends semigroup G :=
(mul_left_cancel : ∀ a b c : G, a * b = a * c → b = c)
/-- An `add_left_cancel_semigroup` is an additive semigroup such that
`a + b = a + c` implies `b = c`. -/
@[protect_proj, ancestor add_semigroup, ext]
class add_left_cancel_semigroup (G : Type u) extends add_semigroup G :=
(add_left_cancel : ∀ a b c : G, a + b = a + c → b = c)
attribute [to_additive add_left_cancel_semigroup] left_cancel_semigroup

section left_cancel_semigroup
variables [left_cancel_semigroup G] {a b c : G}

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
@[protect_proj, ancestor semigroup, ext]
class right_cancel_semigroup (G : Type u) extends semigroup G :=
(mul_right_cancel : ∀ a b c : G, a * b = c * b → a = c)

/-- An `add_right_cancel_semigroup` is an additive semigroup such that
`a + b = c + b` implies `a = c`. -/
@[protect_proj, ancestor add_semigroup, ext]
class add_right_cancel_semigroup (G : Type u) extends add_semigroup G :=
(add_right_cancel : ∀ a b c : G, a + b = c + b → a = c)
attribute [to_additive add_right_cancel_semigroup] right_cancel_semigroup

section right_cancel_semigroup
variables [right_cancel_semigroup G] {a b c : G}

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

@[ext, to_additive]
lemma mul_one_class.ext {M : Type u} : ∀ ⦃m₁ m₂ : mul_one_class M⦄, m₁.mul = m₂.mul → m₁ = m₂ :=
begin
  rintros ⟨one₁, mul₁, one_mul₁, mul_one₁⟩ ⟨one₂, mul₂, one_mul₂, mul_one₂⟩ (rfl : mul₁ = mul₂),
  congr,
  exact (one_mul₂ one₁).symm.trans (mul_one₁ one₂),
end

section mul_one_class
variables {M : Type u} [mul_one_class M]

@[ematch, simp, to_additive]
lemma one_mul : ∀ a : M, 1 * a = a :=
mul_one_class.one_mul

@[ematch, simp, to_additive]
lemma mul_one : ∀ a : M, a * 1 = a :=
mul_one_class.mul_one

@[to_additive]
instance mul_one_class.to_is_left_id : is_left_id M (*) 1 :=
⟨ mul_one_class.one_mul ⟩

@[to_additive]
instance mul_one_class.to_is_right_id : is_right_id M (*) 1 :=
⟨ mul_one_class.mul_one ⟩

end mul_one_class



section
variables {M : Type u}

-- use `x * npow_rec n x` and not `npow_rec n x * x` in the definition to make sure that
-- definitional unfolding of `npow_rec` is blocked, to avoid deep recursion issues.
/-- The fundamental power operation in a monoid. `npow_rec n a = a*a*...*a` n times.
Use instead `a ^ n`,  which has better definitional behavior. -/
def npow_rec [has_one M] [has_mul M] : ℕ → M → M
| 0     a := 1
| (n+1) a := a * npow_rec n a

/-- The fundamental scalar multiplication in an additive monoid. `nsmul_rec n a = a+a+...+a` n
times. Use instead `n • a`, which has better definitional behavior. -/
def nsmul_rec [has_zero M] [has_add M] : ℕ → M → M
| 0     a := 0
| (n+1) a := a + nsmul_rec n a

attribute [to_additive] npow_rec

end

/-- Suppose that one can put two mathematical structures on a type, a rich one `R` and a poor one
`P`, and that one can deduce the poor structure from the rich structure through a map `F` (called a
forgetful functor) (think `R = metric_space` and `P = topological_space`). A possible
implementation would be to have a type class `rich` containing a field `R`, a type class `poor`
containing a field `P`, and an instance from `rich` to `poor`. However, this creates diamond
problems, and a better approach is to let `rich` extend `poor` and have a field saying that
`F R = P`.

To illustrate this, consider the pair `metric_space` / `topological_space`. Consider the topology
on a product of two metric spaces. With the first approach, it could be obtained by going first from
each metric space to its topology, and then taking the product topology. But it could also be
obtained by considering the product metric space (with its sup distance) and then the topology
coming from this distance. These would be the same topology, but not definitionally, which means
that from the point of view of Lean's kernel, there would be two different `topological_space`
instances on the product. This is not compatible with the way instances are designed and used:
there should be at most one instance of a kind on each type. This approach has created an instance
diamond that does not commute definitionally.

The second approach solves this issue. Now, a metric space contains both a distance, a topology, and
a proof that the topology coincides with the one coming from the distance. When one defines the
product of two metric spaces, one uses the sup distance and the product topology, and one has to
give the proof that the sup distance induces the product topology. Following both sides of the
instance diamond then gives rise (definitionally) to the product topology on the product space.

Another approach would be to have the rich type class take the poor type class as an instance
parameter. It would solve the diamond problem, but it would lead to a blow up of the number
of type classes one would need to declare to work with complicated classes, say a real inner
product space, and would create exponential complexity when working with products of
such complicated spaces, that are avoided by bundling things carefully as above.

Note that this description of this specific case of the product of metric spaces is oversimplified
compared to mathlib, as there is an intermediate typeclass between `metric_space` and
`topological_space` called `uniform_space`. The above scheme is used at both levels, embedding a
topology in the uniform space structure, and a uniform structure in the metric space structure.

Note also that, when `P` is a proposition, there is no such issue as any two proofs of `P` are
definitionally equivalent in Lean.

To avoid boilerplate, there are some designs that can automatically fill the poor fields when
creating a rich structure if one doesn't want to do something special about them. For instance,
in the definition of metric spaces, default tactics fill the uniform space fields if they are
not given explicitly. One can also have a helper function creating the rich structure from a
structure with fewer fields, where the helper function fills the remaining fields. See for instance
`uniform_space.of_core` or `real_inner_product.of_core`.

For more details on this question, called the forgetful inheritance pattern, see [Competing
inheritance paths in dependent type theory: a case study in functional
analysis](https://hal.inria.fr/hal-02463336).
-/
library_note "forgetful inheritance"

/-- `try_refl_tac` solves goals of the form `∀ a b, f a b = g a b`,
if they hold by definition. -/
meta def try_refl_tac : tactic unit := `[intros; refl]

/-!
### Design note on `add_monoid` and `monoid`

An `add_monoid` has a natural `ℕ`-action, defined by `n • a = a + ... + a`, that we want to declare
as an instance as it makes it possible to use the language of linear algebra. However, there are
often other natural `ℕ`-actions. For instance, for any semiring `R`, the space of polynomials
`polynomial R` has a natural `R`-action defined by multiplication on the coefficients. This means
that `polynomial ℕ` would have two natural `ℕ`-actions, which are equal but not defeq. The same
goes for linear maps, tensor products, and so on (and even for `ℕ` itself).

To solve this issue, we embed an `ℕ`-action in the definition of an `add_monoid` (which is by
default equal to the naive action `a + ... + a`, but can be adjusted when needed), and declare
a `has_scalar ℕ α` instance using this action. See Note [forgetful inheritance] for more
explanations on this pattern.

For example, when we define `polynomial R`, then we declare the `ℕ`-action to be by multiplication
on each coefficient (using the `ℕ`-action on `R` that comes from the fact that `R` is
an `add_monoid`). In this way, the two natural `has_scalar ℕ (polynomial ℕ)` instances are defeq.

The tactic `to_additive` transfers definitions and results from multiplicative monoids to additive
monoids. To work, it has to map fields to fields. This means that we should also add corresponding
fields to the multiplicative structure `monoid`, which could solve defeq problems for powers if
needed. These problems do not come up in practice, so most of the time we will not need to adjust
the `npow` field when defining multiplicative objects.

A basic theory for the power function on monoids and the `ℕ`-action on additive monoids is built in
the file `algebra.group_power.basic`. For now, we only register the most basic properties that we
need right away.

In the definition, we use `n.succ` instead of `n + 1` in the `nsmul_succ'` and `npow_succ'` fields
to make sure that `to_additive` is not confused (otherwise, it would try to convert `1 : ℕ`
to `0 : ℕ`).
-/

/-- An `add_monoid` is an `add_semigroup` with an element `0` such that `0 + a = a + 0 = a`. -/
@[ancestor add_semigroup add_zero_class]
class add_monoid (M : Type u) extends add_semigroup M, add_zero_class M :=
(nsmul : ℕ → M → M := nsmul_rec)
(nsmul_zero' : ∀ x, nsmul 0 x = 0 . try_refl_tac)
(nsmul_succ' : ∀ (n : ℕ) x, nsmul n.succ x = x + nsmul n x . try_refl_tac)

/-- A `monoid` is a `semigroup` with an element `1` such that `1 * a = a * 1 = a`. -/
@[ancestor semigroup mul_one_class, to_additive]
class monoid (M : Type u) extends semigroup M, mul_one_class M :=
(npow : ℕ → M → M := npow_rec)
(npow_zero' : ∀ x, npow 0 x = 1 . try_refl_tac)
(npow_succ' : ∀ (n : ℕ) x, npow n.succ x = x * npow n x . try_refl_tac)

instance monoid.has_pow {M : Type*} [monoid M] : has_pow M ℕ := ⟨λ x n, monoid.npow n x⟩

instance add_monoid.has_scalar_nat {M : Type*} [add_monoid M] : has_scalar ℕ M :=
⟨add_monoid.nsmul⟩

attribute [to_additive add_monoid.has_scalar_nat] monoid.has_pow

section

variables {M : Type*} [monoid M]

@[simp, to_additive nsmul_eq_smul]
lemma npow_eq_pow (n : ℕ) (x : M) : monoid.npow n x = x^n := rfl

-- the attributes are intentionally out of order. `zero_smul` proves `zero_nsmul`.
@[to_additive zero_nsmul, simp]
theorem pow_zero (a : M) : a^0 = 1 := monoid.npow_zero' _

@[to_additive succ_nsmul]
theorem pow_succ (a : M) (n : ℕ) : a^(n+1) = a * a^n := monoid.npow_succ' n a

end

section monoid
variables {M : Type u} [monoid M]

@[to_additive]
lemma left_inv_eq_right_inv {a b c : M} (hba : b * a = 1) (hac : a * c = 1) : b = c :=
by rw [←one_mul c, ←hba, mul_assoc, hac, mul_one b]

end monoid

/-- An additive commutative monoid is an additive monoid with commutative `(+)`. -/
@[protect_proj, ancestor add_monoid add_comm_semigroup]
class add_comm_monoid (M : Type u) extends add_monoid M, add_comm_semigroup M

/-- A commutative monoid is a monoid with commutative `(*)`. -/
@[protect_proj, ancestor monoid comm_semigroup, to_additive]
class comm_monoid (M : Type u) extends monoid M, comm_semigroup M

section left_cancel_monoid

/-- An additive monoid in which addition is left-cancellative.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `add_left_cancel_semigroup` is not enough. -/
@[protect_proj, ancestor add_left_cancel_semigroup add_monoid]
class add_left_cancel_monoid (M : Type u) extends add_left_cancel_semigroup M, add_monoid M

/-- A monoid in which multiplication is left-cancellative. -/
@[protect_proj, ancestor left_cancel_semigroup monoid, to_additive add_left_cancel_monoid]
class left_cancel_monoid (M : Type u) extends left_cancel_semigroup M, monoid M

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

/-- Commutative version of `add_cancel_monoid`. -/
@[protect_proj, ancestor add_left_cancel_monoid add_comm_monoid]
class add_cancel_comm_monoid (M : Type u) extends add_left_cancel_monoid M, add_comm_monoid M

/-- Commutative version of `cancel_monoid`. -/
@[protect_proj, ancestor left_cancel_monoid comm_monoid, to_additive add_cancel_comm_monoid]
class cancel_comm_monoid (M : Type u) extends left_cancel_monoid M, comm_monoid M

@[priority 100, to_additive] -- see Note [lower instance priority]
instance cancel_comm_monoid.to_cancel_monoid (M : Type u) [cancel_comm_monoid M] :
  cancel_monoid M :=
{ mul_right_cancel := λ a b c h, mul_left_cancel $ by rw [mul_comm, h, mul_comm],
  .. ‹cancel_comm_monoid M› }

end cancel_monoid

/-- The fundamental power operation in a group. `zpow_rec n a = a*a*...*a` n times, for integer `n`.
Use instead `a ^ n`,  which has better definitional behavior. -/
def zpow_rec {M : Type*} [has_one M] [has_mul M] [has_inv M] : ℤ → M → M
| (int.of_nat n) a := npow_rec n a
| -[1+ n]    a := (npow_rec n.succ a) ⁻¹

/-- The fundamental scalar multiplication in an additive group. `zsmul_rec n a = a+a+...+a` n
times, for integer `n`. Use instead `n • a`, which has better definitional behavior. -/
def zsmul_rec {M : Type*} [has_zero M] [has_add M] [has_neg M]: ℤ → M → M
| (int.of_nat n) a := nsmul_rec n a
| -[1+ n]    a := - (nsmul_rec n.succ a)

attribute [to_additive] zpow_rec

section has_involutive_inv

-- ensure that we don't go via these typeclasses to find `has_inv` on groups and groups with zero
set_option extends_priority 50

/-- Auxiliary typeclass for types with an involutive `has_neg`. -/
@[ancestor has_neg]
class has_involutive_neg (A : Type*) extends has_neg A :=
(neg_neg : ∀ x : A, - -x = x)

/-- Auxiliary typeclass for types with an involutive `has_inv`. -/
@[ancestor has_inv, to_additive]
class has_involutive_inv (G : Type*) extends has_inv G :=
(inv_inv : ∀ x : G, x⁻¹⁻¹ = x)

variables [has_involutive_inv G]

@[simp, to_additive] lemma inv_inv (a : G) : a⁻¹⁻¹ = a := has_involutive_inv.inv_inv _

end has_involutive_inv

/-!
### Design note on `div_inv_monoid`/`sub_neg_monoid` and `division_monoid`/`subtraction_monoid`

Those two pairs of made-up classes fulfill slightly different roles.

`div_inv_monoid`/`sub_neg_monoid` provides the minimum amount of information to define the
`ℤ` action (`zpow` or `zsmul`). Further, it provides a `div` field, matching the forgetful
inheritance pattern. This is useful to shorten extension clauses of stronger structures (`group`,
`group_with_zero`, `division_ring`, `field`) and for a few structures with a rather weak
pseudo-inverse (`matrix`).

`division_monoid`/`subtraction_monoid` is targeted at structures with stronger pseudo-inverses. It
is an ad hoc collection of axioms that are mainly respected by three things:
* Groups
* Groups with zero
* The pointwise monoids `set α`, `finset α`, `filter α`

It acts as a middle ground for structures with an inversion operator that plays well with
multiplication, except for the fact that it might not be a true inverse (`a / a ≠ 1` in general).
The axioms are pretty arbitrary (many other combinations are equivalent to it), but they are
independent:
* Without `division_monoid.div_eq_mul_inv`, you can define `/` arbitrarily.
* Without `division_monoid.inv_inv`, you can consider `with_top unit` with `a⁻¹ = ⊤` for all `a`.
* Without `division_monoid.mul_inv_rev`, you can consider `with_top α` with `a⁻¹ = a` for all `a`
  where `α` non commutative.
* Without `division_monoid.inv_eq_of_mul`, you can consider any `comm_monoid` with `a⁻¹ = a` for all
  `a`.

As a consequence, a few natural structures do not fit in this framework. For example, `ennreal`
respects everything except for the fact that `(0 * ∞)⁻¹ = 0⁻¹ = ∞` while `∞⁻¹ * 0⁻¹ = 0 * ∞ = 0`.
-/

/-- A `div_inv_monoid` is a `monoid` with operations `/` and `⁻¹` satisfying
`div_eq_mul_inv : ∀ a b, a / b = a * b⁻¹`.

This deduplicates the name `div_eq_mul_inv`.
The default for `div` is such that `a / b = a * b⁻¹` holds by definition.

Adding `div` as a field rather than defining `a / b := a * b⁻¹` allows us to
avoid certain classes of unification failures, for example:
Let `foo X` be a type with a `∀ X, has_div (foo X)` instance but no
`∀ X, has_inv (foo X)`, e.g. when `foo X` is a `euclidean_domain`. Suppose we
also have an instance `∀ X [cromulent X], group_with_zero (foo X)`. Then the
`(/)` coming from `group_with_zero_has_div` cannot be definitionally equal to
the `(/)` coming from `foo.has_div`.

In the same way, adding a `zpow` field makes it possible to avoid definitional failures
in diamonds. See the definition of `monoid` and Note [forgetful inheritance] for more
explanations on this.
-/
@[protect_proj, ancestor monoid has_inv has_div]
class div_inv_monoid (G : Type u) extends monoid G, has_inv G, has_div G :=
(div := λ a b, a * b⁻¹)
(div_eq_mul_inv : ∀ a b : G, a / b = a * b⁻¹ . try_refl_tac)
(zpow : ℤ → G → G := zpow_rec)
(zpow_zero' : ∀ (a : G), zpow 0 a = 1 . try_refl_tac)
(zpow_succ' :
  ∀ (n : ℕ) (a : G), zpow (int.of_nat n.succ) a = a * zpow (int.of_nat n) a . try_refl_tac)
(zpow_neg' :
  ∀ (n : ℕ) (a : G), zpow (-[1+ n]) a = (zpow n.succ a)⁻¹ . try_refl_tac)

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

In the same way, adding a `zsmul` field makes it possible to avoid definitional failures
in diamonds. See the definition of `add_monoid` and Note [forgetful inheritance] for more
explanations on this.
-/
@[protect_proj, ancestor add_monoid has_neg has_sub]
class sub_neg_monoid (G : Type u) extends add_monoid G, has_neg G, has_sub G :=
(sub := λ a b, a + -b)
(sub_eq_add_neg : ∀ a b : G, a - b = a + -b . try_refl_tac)
(zsmul : ℤ → G → G := zsmul_rec)
(zsmul_zero' : ∀ (a : G), zsmul 0 a = 0 . try_refl_tac)
(zsmul_succ' :
  ∀ (n : ℕ) (a : G), zsmul (int.of_nat n.succ) a = a + zsmul (int.of_nat n) a . try_refl_tac)
(zsmul_neg' :
  ∀ (n : ℕ) (a : G), zsmul (-[1+ n]) a = - (zsmul n.succ a) . try_refl_tac)

attribute [to_additive sub_neg_monoid] div_inv_monoid

instance div_inv_monoid.has_pow {M} [div_inv_monoid M] : has_pow M ℤ :=
⟨λ x n, div_inv_monoid.zpow n x⟩

instance sub_neg_monoid.has_scalar_int {M} [sub_neg_monoid M] : has_scalar ℤ M :=
⟨sub_neg_monoid.zsmul⟩

attribute [to_additive sub_neg_monoid.has_scalar_int] div_inv_monoid.has_pow

section div_inv_monoid
variables [div_inv_monoid G] {a b : G}

@[simp, to_additive zsmul_eq_smul]
lemma zpow_eq_pow (n : ℤ) (x : G) : div_inv_monoid.zpow n x = x^n := rfl

@[simp, to_additive zero_zsmul]
theorem zpow_zero (a : G) : a ^ (0:ℤ) = 1 := div_inv_monoid.zpow_zero' a

@[simp, norm_cast, to_additive coe_nat_zsmul]
theorem zpow_coe_nat (a : G) : ∀ n : ℕ, a ^ (n:ℤ) = a ^ n
| 0 := (zpow_zero _).trans (pow_zero _).symm
| (n + 1) :=
  calc a ^ (↑(n + 1) : ℤ) = a * a ^ (n : ℤ) : div_inv_monoid.zpow_succ' _ _
                      ... = a * a ^ n       : congr_arg ((*) a) (zpow_coe_nat n)
                      ... = a ^ (n + 1)     : (pow_succ _ _).symm

@[to_additive of_nat_zsmul]
theorem zpow_of_nat (a : G) (n : ℕ) : a ^ (int.of_nat n) = a ^ n :=
zpow_coe_nat a n

@[simp, to_additive]
theorem zpow_neg_succ_of_nat (a : G) (n : ℕ) : a ^ -[1+n] = (a ^ (n + 1))⁻¹ :=
by { rw ← zpow_coe_nat, exact div_inv_monoid.zpow_neg' n a }

/-- Dividing by an element is the same as multiplying by its inverse.

This is a duplicate of `div_inv_monoid.div_eq_mul_inv` ensuring that the types unfold better.
-/
@[to_additive "Subtracting an element is the same as adding by its negative.

This is a duplicate of `sub_neg_monoid.sub_eq_mul_neg` ensuring that the types unfold better."]
lemma div_eq_mul_inv (a b : G) : a / b = a * b⁻¹ := div_inv_monoid.div_eq_mul_inv _ _

alias div_eq_mul_inv ← division_def

end div_inv_monoid

/-- A `subtraction_monoid` is a `sub_neg_monoid` with involutive negation and such that
`-(a + b) = -b + -a` and `a + b = 0 → -a = b`. -/
@[protect_proj, ancestor sub_neg_monoid has_involutive_neg]
class subtraction_monoid (G : Type u) extends sub_neg_monoid G, has_involutive_neg G :=
(neg_add_rev (a b : G) : -(a + b) = -b + -a)
/- Despite the asymmetry of `neg_eq_of_add`, the symmetric version is true thanks to the
involutivity of negation. -/
(neg_eq_of_add (a b : G) : a + b = 0 → -a = b)

/-- A `division_monoid` is a `div_inv_monoid` with involutive inversion and such that
`(a * b)⁻¹ = b⁻¹ * a⁻¹` and `a * b = 1 → a⁻¹ = b`.

This is the immediate common ancestor of `group` and `group_with_zero`. -/
@[protect_proj, ancestor div_inv_monoid has_involutive_inv, to_additive subtraction_monoid]
class division_monoid (G : Type u) extends div_inv_monoid G, has_involutive_inv G :=
(mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹)
/- Despite the asymmetry of `inv_eq_of_mul`, the symmetric version is true thanks to the
involutivity of inversion. -/
(inv_eq_of_mul (a b : G) : a * b = 1 → a⁻¹ = b)

section division_monoid
variables [division_monoid G] {a b : G}

@[simp, to_additive neg_add_rev] lemma mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
division_monoid.mul_inv_rev _ _

@[to_additive]
lemma inv_eq_of_mul_eq_one_right : a * b = 1 → a⁻¹ = b := division_monoid.inv_eq_of_mul _ _

end division_monoid

/-- Commutative `subtraction_monoid`. -/
@[protect_proj, ancestor subtraction_monoid add_comm_monoid]
class subtraction_comm_monoid (G : Type u) extends subtraction_monoid G, add_comm_monoid G

/-- Commutative `division_monoid`.

This is the immediate common ancestor of `comm_group` and `comm_group_with_zero`. -/
@[protect_proj, ancestor division_monoid comm_monoid, to_additive subtraction_comm_monoid]
class division_comm_monoid (G : Type u) extends division_monoid G, comm_monoid G

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
See note [reducible non-instances]. -/
@[reducible, to_additive
"Abbreviation for `@sub_neg_monoid.to_add_monoid _ (@add_group.to_sub_neg_monoid _ _)`.

Useful because it corresponds to the fact that `AddGroup` is a subcategory of `AddMon`.
Not an instance since it duplicates
`@sub_neg_monoid.to_add_monoid _ (@add_group.to_sub_neg_monoid _ _)`."]
def group.to_monoid (G : Type u) [group G] : monoid G :=
@div_inv_monoid.to_monoid _ (@group.to_div_inv_monoid _ _)

section group
variables [group G] {a b c : G}

@[simp, to_additive]
lemma mul_left_inv : ∀ a : G, a⁻¹ * a = 1 :=
group.mul_left_inv

@[to_additive] lemma inv_mul_self (a : G) : a⁻¹ * a = 1 := mul_left_inv a

@[to_additive] private lemma inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b :=
left_inv_eq_right_inv (inv_mul_self a) h

@[simp, to_additive]
lemma mul_right_inv (a : G) : a * a⁻¹ = 1 :=
by rw [←mul_left_inv a⁻¹, inv_eq_of_mul (mul_left_inv a)]

@[to_additive] lemma mul_inv_self (a : G) : a * a⁻¹ = 1 := mul_right_inv a

@[simp, to_additive] lemma inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b :=
by rw [←mul_assoc, mul_left_inv, one_mul]

@[simp, to_additive] lemma mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b :=
by rw [←mul_assoc, mul_right_inv, one_mul]

@[simp, to_additive] lemma mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a :=
by rw [mul_assoc, mul_right_inv, mul_one]

@[simp, to_additive] lemma inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a :=
by rw [mul_assoc, mul_left_inv, mul_one]

@[priority 100, to_additive]
instance group.to_division_monoid : division_monoid G :=
{ inv_inv := λ a, inv_eq_of_mul (mul_left_inv a),
  mul_inv_rev := λ a b, inv_eq_of_mul $ by rw [mul_assoc, mul_inv_cancel_left, mul_right_inv],
  inv_eq_of_mul := λ _ _, inv_eq_of_mul,
  ..‹group G› }

@[priority 100, to_additive]    -- see Note [lower instance priority]
instance group.to_cancel_monoid : cancel_monoid G :=
{ mul_right_cancel := λ a b c h, by rw [← mul_inv_cancel_right a b, h, mul_inv_cancel_right],
  mul_left_cancel := λ a b c h, by rw [← inv_mul_cancel_left a b, h, inv_mul_cancel_left],
  ..‹group G› }

end group

@[to_additive]
lemma group.to_div_inv_monoid_injective {G : Type*} :
  function.injective (@group.to_div_inv_monoid G) :=
begin
  rintros ⟨⟩ ⟨⟩ h,
  replace h := div_inv_monoid.mk.inj h,
  dsimp at h,
  rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
  refl
end

/-- A commutative group is a group with commutative `(*)`. -/
@[protect_proj, ancestor group comm_monoid]
class comm_group (G : Type u) extends group G, comm_monoid G
/-- An additive commutative group is an additive group with commutative `(+)`. -/
@[protect_proj, ancestor add_group add_comm_monoid]
class add_comm_group (G : Type u) extends add_group G, add_comm_monoid G
attribute [to_additive] comm_group
attribute [instance, priority 300] add_comm_group.to_add_comm_monoid

@[to_additive]
lemma comm_group.to_group_injective {G : Type u} :
  function.injective (@comm_group.to_group G) :=
begin
  rintros ⟨⟩ ⟨⟩ h,
  replace h := group.mk.inj h,
  dsimp at h,
  rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
  refl
end

section comm_group

variables [comm_group G]

@[priority 100, to_additive]    -- see Note [lower instance priority]
instance comm_group.to_cancel_comm_monoid : cancel_comm_monoid G :=
{ ..‹comm_group G›,
  ..group.to_cancel_monoid }

@[priority 100, to_additive]    -- see Note [lower instance priority]
instance comm_group.to_division_comm_monoid : division_comm_monoid G :=
{ ..‹comm_group G›,
  ..group.to_division_monoid }

end comm_group

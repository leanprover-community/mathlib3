/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kevin Buzzard, Scott Morrison, Johan Commelin, Chris Hughes,
  Johannes Hölzl, Yury Kudryashov
-/
import algebra.group.commute
import algebra.group_with_zero.defs
import data.fun_like.basic

/-!
# Monoid and group homomorphisms

This file defines the bundled structures for monoid and group homomorphisms. Namely, we define
`monoid_hom` (resp., `add_monoid_hom`) to be bundled homomorphisms between multiplicative (resp.,
additive) monoids or groups.

We also define coercion to a function, and  usual operations: composition, identity homomorphism,
pointwise multiplication and pointwise inversion.

This file also defines the lesser-used (and notation-less) homomorphism types which are used as
building blocks for other homomorphisms:

* `zero_hom`
* `one_hom`
* `add_hom`
* `mul_hom`
* `monoid_with_zero_hom`

## Notations

* `→+`: Bundled `add_monoid` homs. Also use for `add_group` homs.
* `→*`: Bundled `monoid` homs. Also use for `group` homs.
* `→*₀`: Bundled `monoid_with_zero` homs. Also use for `group_with_zero` homs.
* `→ₙ*`: Bundled `semigroup` homs.

## Implementation notes

There's a coercion from bundled homs to fun, and the canonical
notation is to use the bundled hom as a function via this coercion.

There is no `group_hom` -- the idea is that `monoid_hom` is used.
The constructor for `monoid_hom` needs a proof of `map_one` as well
as `map_mul`; a separate constructor `monoid_hom.mk'` will construct
group homs (i.e. monoid homs between groups) given only a proof
that multiplication is preserved,

Implicit `{}` brackets are often used instead of type class `[]` brackets.  This is done when the
instances can be inferred because they are implicit arguments to the type `monoid_hom`.  When they
can be inferred from the type it is faster to use this method than to use type class inference.

Historically this file also included definitions of unbundled homomorphism classes; they were
deprecated and moved to `deprecated/group`.

## Tags

monoid_hom, add_monoid_hom

-/

variables {M : Type*} {N : Type*} {P : Type*} -- monoids
variables {G : Type*} {H : Type*} -- groups
variables {F : Type*} -- homs

-- for easy multiple inheritance
set_option old_structure_cmd true

section zero

/-- `zero_hom M N` is the type of functions `M → N` that preserve zero.

When possible, instead of parametrizing results over `(f : zero_hom M N)`,
you should parametrize over `(F : Type*) [zero_hom_class F M N] (f : F)`.

When you extend this structure, make sure to also extend `zero_hom_class`.
-/
structure zero_hom (M : Type*) (N : Type*) [has_zero M] [has_zero N] :=
(to_fun : M → N)
(map_zero' : to_fun 0 = 0)

/-- `zero_hom_class F M N` states that `F` is a type of zero-preserving homomorphisms.

You should extend this typeclass when you extend `zero_hom`.
-/
class zero_hom_class (F : Type*) (M N : out_param $ Type*)
  [has_zero M] [has_zero N] extends fun_like F M (λ _, N) :=
(map_zero : ∀ (f : F), f 0 = 0)

-- Instances and lemmas are defined below through `@[to_additive]`.

end zero

section add


/-- `add_hom M N` is the type of functions `M → N` that preserve addition.

When possible, instead of parametrizing results over `(f : add_hom M N)`,
you should parametrize over `(F : Type*) [add_hom_class F M N] (f : F)`.

When you extend this structure, make sure to extend `add_hom_class`.
-/
structure add_hom (M : Type*) (N : Type*) [has_add M] [has_add N] :=
(to_fun : M → N)
(map_add' : ∀ x y, to_fun (x + y) = to_fun x + to_fun y)

/-- `add_hom_class F M N` states that `F` is a type of addition-preserving homomorphisms.
You should declare an instance of this typeclass when you extend `add_hom`.
-/
class add_hom_class (F : Type*) (M N : out_param $ Type*)
  [has_add M] [has_add N] extends fun_like F M (λ _, N) :=
(map_add : ∀ (f : F) (x y : M), f (x + y) = f x + f y)

-- Instances and lemmas are defined below through `@[to_additive]`.

end add

section add_zero

/-- `M →+ N` is the type of functions `M → N` that preserve the `add_zero_class` structure.

`add_monoid_hom` is also used for group homomorphisms.

When possible, instead of parametrizing results over `(f : M →+ N)`,
you should parametrize over `(F : Type*) [add_monoid_hom_class F M N] (f : F)`.

When you extend this structure, make sure to extend `add_monoid_hom_class`.
-/
@[ancestor zero_hom add_hom]
structure add_monoid_hom (M : Type*) (N : Type*) [add_zero_class M] [add_zero_class N]
  extends zero_hom M N, add_hom M N

attribute [nolint doc_blame] add_monoid_hom.to_add_hom
attribute [nolint doc_blame] add_monoid_hom.to_zero_hom

infixr ` →+ `:25 := add_monoid_hom

/-- `add_monoid_hom_class F M N` states that `F` is a type of `add_zero_class`-preserving
homomorphisms.

You should also extend this typeclass when you extend `add_monoid_hom`.
-/
@[ancestor add_hom_class zero_hom_class]
class add_monoid_hom_class (F : Type*) (M N : out_param $ Type*)
  [add_zero_class M] [add_zero_class N]
  extends add_hom_class F M N, zero_hom_class F M N

-- Instances and lemmas are defined below through `@[to_additive]`.

end add_zero

section one

variables [has_one M] [has_one N]

/-- `one_hom M N` is the type of functions `M → N` that preserve one.

When possible, instead of parametrizing results over `(f : one_hom M N)`,
you should parametrize over `(F : Type*) [one_hom_class F M N] (f : F)`.

When you extend this structure, make sure to also extend `one_hom_class`.
-/
@[to_additive]
structure one_hom (M : Type*) (N : Type*) [has_one M] [has_one N] :=
(to_fun : M → N)
(map_one' : to_fun 1 = 1)

/-- `one_hom_class F M N` states that `F` is a type of one-preserving homomorphisms.
You should extend this typeclass when you extend `one_hom`.
-/
@[to_additive]
class one_hom_class (F : Type*) (M N : out_param $ Type*)
  [has_one M] [has_one N]
  extends fun_like F M (λ _, N) :=
(map_one : ∀ (f : F), f 1 = 1)

@[to_additive]
instance one_hom.one_hom_class : one_hom_class (one_hom M N) M N :=
{ coe := one_hom.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_one := one_hom.map_one' }

@[simp, to_additive] lemma map_one [one_hom_class F M N] (f : F) : f 1 = 1 :=
one_hom_class.map_one f

@[to_additive] lemma map_eq_one_iff [one_hom_class F M N] (f : F)
  (hf : function.injective f) {x : M} : f x = 1 ↔ x = 1 :=
hf.eq_iff' (map_one f)

@[to_additive]
lemma map_ne_one_iff {R S F : Type*} [has_one R] [has_one S] [one_hom_class F R S]
  (f : F) (hf : function.injective f) {x : R} :
  f x ≠ 1 ↔ x ≠ 1 :=
(map_eq_one_iff f hf).not

@[to_additive]
lemma ne_one_of_map {R S F : Type*} [has_one R] [has_one S] [one_hom_class F R S]
  {f : F} {x : R} (hx : f x ≠ 1) : x ≠ 1 :=
ne_of_apply_ne f $ ne_of_ne_of_eq hx (map_one f).symm

@[to_additive]
instance [one_hom_class F M N] : has_coe_t F (one_hom M N) :=
⟨λ f, { to_fun := f, map_one' := map_one f }⟩

end one

section mul

variables [has_mul M] [has_mul N]

/-- `M →ₙ* N` is the type of functions `M → N` that preserve multiplication. The `ₙ` in the notation
stands for "non-unital" because it is intended to match the notation for `non_unital_alg_hom` and
`non_unital_ring_hom`, so a `mul_hom` is a non-unital monoid hom.

When possible, instead of parametrizing results over `(f : M →ₙ* N)`,
you should parametrize over `(F : Type*) [mul_hom_class F M N] (f : F)`.
When you extend this structure, make sure to extend `mul_hom_class`.
-/
@[to_additive]
structure mul_hom (M : Type*) (N : Type*) [has_mul M] [has_mul N] :=
(to_fun : M → N)
(map_mul' : ∀ x y, to_fun (x * y) = to_fun x * to_fun y)

infixr ` →ₙ* `:25 := mul_hom

/-- `mul_hom_class F M N` states that `F` is a type of multiplication-preserving homomorphisms.

You should declare an instance of this typeclass when you extend `mul_hom`.
-/
@[to_additive]
class mul_hom_class (F : Type*) (M N : out_param $ Type*)
  [has_mul M] [has_mul N] extends fun_like F M (λ _, N) :=
(map_mul : ∀ (f : F) (x y : M), f (x * y) = f x * f y)

@[to_additive]
instance mul_hom.mul_hom_class : mul_hom_class (M →ₙ* N) M N :=
{ coe := mul_hom.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_mul := mul_hom.map_mul' }

@[simp, to_additive] lemma map_mul [mul_hom_class F M N] (f : F) (x y : M) :
  f (x * y) = f x * f y :=
mul_hom_class.map_mul f x y

@[to_additive]
instance [mul_hom_class F M N] : has_coe_t F (M →ₙ* N) :=
⟨λ f, { to_fun := f, map_mul' := map_mul f }⟩

end mul

section mul_one

variables [mul_one_class M] [mul_one_class N]

/-- `M →* N` is the type of functions `M → N` that preserve the `monoid` structure.
`monoid_hom` is also used for group homomorphisms.

When possible, instead of parametrizing results over `(f : M →+ N)`,
you should parametrize over `(F : Type*) [monoid_hom_class F M N] (f : F)`.

When you extend this structure, make sure to extend `monoid_hom_class`.
-/
@[ancestor one_hom mul_hom, to_additive]
structure monoid_hom (M : Type*) (N : Type*) [mul_one_class M] [mul_one_class N]
  extends one_hom M N, M →ₙ* N

attribute [nolint doc_blame] monoid_hom.to_mul_hom
attribute [nolint doc_blame] monoid_hom.to_one_hom

infixr ` →* `:25 := monoid_hom

/-- `monoid_hom_class F M N` states that `F` is a type of `monoid`-preserving homomorphisms.
You should also extend this typeclass when you extend `monoid_hom`. -/
@[ancestor mul_hom_class one_hom_class, to_additive
"`add_monoid_hom_class F M N` states that `F` is a type of `add_monoid`-preserving homomorphisms.
You should also extend this typeclass when you extend `add_monoid_hom`."]
class monoid_hom_class (F : Type*) (M N : out_param $ Type*)
  [mul_one_class M] [mul_one_class N]
  extends mul_hom_class F M N, one_hom_class F M N

@[to_additive]
instance monoid_hom.monoid_hom_class : monoid_hom_class (M →* N) M N :=
{ coe := monoid_hom.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_mul := monoid_hom.map_mul',
  map_one := monoid_hom.map_one' }

@[to_additive]
instance [monoid_hom_class F M N] : has_coe_t F (M →* N) :=
⟨λ f, { to_fun := f, map_one' := map_one f, map_mul' := map_mul f }⟩

@[to_additive]
lemma map_mul_eq_one [monoid_hom_class F M N] (f : F) {a b : M} (h : a * b = 1) :
  f a * f b = 1 :=
by rw [← map_mul, h, map_one]

/-- Group homomorphisms preserve inverse. -/
@[simp, to_additive "Additive group homomorphisms preserve negation."]
theorem map_inv [group G] [group H] [monoid_hom_class F G H]
  (f : F) (g : G) : f g⁻¹ = (f g)⁻¹ :=
eq_inv_of_mul_eq_one_left $ map_mul_eq_one f $ inv_mul_self g

/-- Group homomorphisms preserve division. -/
@[simp, to_additive "Additive group homomorphisms preserve subtraction."]
theorem map_mul_inv [group G] [group H] [monoid_hom_class F G H]
  (f : F) (g h : G) : f (g * h⁻¹) = f g * (f h)⁻¹ :=
by rw [map_mul, map_inv]

/-- Group homomorphisms preserve division. -/
@[simp, to_additive "Additive group homomorphisms preserve subtraction."]
lemma map_div [group G] [group H] [monoid_hom_class F G H]
  (f : F) (x y : G) : f (x / y) = f x / f y :=
by rw [div_eq_mul_inv, div_eq_mul_inv, map_mul_inv]

@[to_additive]
theorem map_div' [div_inv_monoid G] [div_inv_monoid H] [monoid_hom_class F G H] (f : F)
  (hf : ∀ x, f (x⁻¹) = (f x)⁻¹) (a b : G) : f (a / b) = f a / f b :=
by rw [div_eq_mul_inv, div_eq_mul_inv, map_mul, hf]

-- to_additive puts the arguments in the wrong order, so generate an auxiliary lemma, then
-- swap its arguments.
@[to_additive map_nsmul.aux, simp] theorem map_pow [monoid G] [monoid H] [monoid_hom_class F G H]
  (f : F) (a : G) :
  ∀ (n : ℕ), f (a ^ n) = (f a) ^ n
| 0     := by rw [pow_zero, pow_zero, map_one]
| (n+1) := by rw [pow_succ, pow_succ, map_mul, map_pow]

@[simp] theorem map_nsmul [add_monoid G] [add_monoid H] [add_monoid_hom_class F G H]
  (f : F) (n : ℕ) (a : G) : f (n • a) = n • (f a) :=
map_nsmul.aux f a n

attribute [to_additive_reorder 8, to_additive] map_pow

@[to_additive]
theorem map_zpow' [div_inv_monoid G] [div_inv_monoid H] [monoid_hom_class F G H]
  (f : F) (hf : ∀ (x : G), f (x⁻¹) = (f x)⁻¹) (a : G) :
  ∀ n : ℤ, f (a ^ n) = (f a) ^ n
| (n : ℕ) := by rw [zpow_coe_nat, map_pow, zpow_coe_nat]
| -[1+n]  := by rw [zpow_neg_succ_of_nat, hf, map_pow, ← zpow_neg_succ_of_nat]

-- to_additive puts the arguments in the wrong order, so generate an auxiliary lemma, then
-- swap its arguments.
/-- Group homomorphisms preserve integer power. -/
@[to_additive map_zsmul.aux, simp]
theorem map_zpow [group G] [group H] [monoid_hom_class F G H] (f : F) (g : G) (n : ℤ) :
  f (g ^ n) = (f g) ^ n :=
map_zpow' f (map_inv f) g n

/-- Additive group homomorphisms preserve integer scaling. -/
theorem map_zsmul [add_group G] [add_group H] [add_monoid_hom_class F G H] (f : F) (n : ℤ) (g : G) :
  f (n • g) = n • f g :=
map_zsmul.aux f g n

attribute [to_additive_reorder 8, to_additive] map_zpow

end mul_one

section mul_zero_one

variables [mul_zero_one_class M] [mul_zero_one_class N]

/-- `M →*₀ N` is the type of functions `M → N` that preserve
the `monoid_with_zero` structure.

`monoid_with_zero_hom` is also used for group homomorphisms.

When possible, instead of parametrizing results over `(f : M →*₀ N)`,
you should parametrize over `(F : Type*) [monoid_with_zero_hom_class F M N] (f : F)`.

When you extend this structure, make sure to extend `monoid_with_zero_hom_class`.
-/
@[ancestor zero_hom monoid_hom]
structure monoid_with_zero_hom (M : Type*) (N : Type*) [mul_zero_one_class M] [mul_zero_one_class N]
  extends zero_hom M N, monoid_hom M N

attribute [nolint doc_blame] monoid_with_zero_hom.to_monoid_hom
attribute [nolint doc_blame] monoid_with_zero_hom.to_zero_hom

infixr ` →*₀ `:25 := monoid_with_zero_hom

/-- `monoid_with_zero_hom_class F M N` states that `F` is a type of
`monoid_with_zero`-preserving homomorphisms.

You should also extend this typeclass when you extend `monoid_with_zero_hom`.
-/
class monoid_with_zero_hom_class (F : Type*) (M N : out_param $ Type*)
  [mul_zero_one_class M] [mul_zero_one_class N]
  extends monoid_hom_class F M N, zero_hom_class F M N

instance monoid_with_zero_hom.monoid_with_zero_hom_class :
  monoid_with_zero_hom_class (M →*₀ N) M N :=
{ coe := monoid_with_zero_hom.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_mul := monoid_with_zero_hom.map_mul',
  map_one := monoid_with_zero_hom.map_one',
  map_zero := monoid_with_zero_hom.map_zero' }

instance [monoid_with_zero_hom_class F M N] : has_coe_t F (M →*₀ N) :=
⟨λ f, { to_fun := f, map_one' := map_one f, map_zero' := map_zero f, map_mul' := map_mul f }⟩

end mul_zero_one

-- completely uninteresting lemmas about coercion to function, that all homs need
section coes

/-! Bundled morphisms can be down-cast to weaker bundlings -/
@[to_additive]
instance monoid_hom.has_coe_to_one_hom {mM : mul_one_class M} {mN : mul_one_class N} :
  has_coe (M →* N) (one_hom M N) := ⟨monoid_hom.to_one_hom⟩
@[to_additive]
instance monoid_hom.has_coe_to_mul_hom {mM : mul_one_class M} {mN : mul_one_class N} :
  has_coe (M →* N) (M →ₙ* N) := ⟨monoid_hom.to_mul_hom⟩
instance monoid_with_zero_hom.has_coe_to_monoid_hom
  {mM : mul_zero_one_class M} {mN : mul_zero_one_class N} :
  has_coe (M →*₀ N) (M →* N) := ⟨monoid_with_zero_hom.to_monoid_hom⟩
instance monoid_with_zero_hom.has_coe_to_zero_hom
  {mM : mul_zero_one_class M} {mN : mul_zero_one_class N} :
  has_coe (M →*₀ N) (zero_hom M N) := ⟨monoid_with_zero_hom.to_zero_hom⟩

/-! The simp-normal form of morphism coercion is `f.to_..._hom`. This choice is primarily because
this is the way things were before the above coercions were introduced. Bundled morphisms defined
elsewhere in Mathlib may choose `↑f` as their simp-normal form instead. -/
@[simp, to_additive]
lemma monoid_hom.coe_eq_to_one_hom {mM : mul_one_class M} {mN : mul_one_class N} (f : M →* N) :
  (f : one_hom M N) = f.to_one_hom := rfl
@[simp, to_additive]
lemma monoid_hom.coe_eq_to_mul_hom {mM : mul_one_class M} {mN : mul_one_class N} (f : M →* N) :
  (f : M →ₙ* N) = f.to_mul_hom := rfl
@[simp]
lemma monoid_with_zero_hom.coe_eq_to_monoid_hom
  {mM : mul_zero_one_class M} {mN : mul_zero_one_class N} (f : M →*₀ N) :
  (f : M →* N) = f.to_monoid_hom := rfl
@[simp]
lemma monoid_with_zero_hom.coe_eq_to_zero_hom
  {mM : mul_zero_one_class M} {mN : mul_zero_one_class N} (f : M →*₀ N) :
  (f : zero_hom M N) = f.to_zero_hom := rfl

-- Fallback `has_coe_to_fun` instances to help the elaborator
@[to_additive]
instance {mM : has_one M} {mN : has_one N} : has_coe_to_fun (one_hom M N) (λ _, M → N) :=
⟨one_hom.to_fun⟩
@[to_additive]
instance {mM : has_mul M} {mN : has_mul N} : has_coe_to_fun (M →ₙ* N) (λ _, M → N) :=
⟨mul_hom.to_fun⟩
@[to_additive]
instance {mM : mul_one_class M} {mN : mul_one_class N} : has_coe_to_fun (M →* N) (λ _, M → N) :=
⟨monoid_hom.to_fun⟩
instance {mM : mul_zero_one_class M} {mN : mul_zero_one_class N} :
  has_coe_to_fun (M →*₀ N) (λ _, M → N) :=
⟨monoid_with_zero_hom.to_fun⟩

-- these must come after the coe_to_fun definitions
initialize_simps_projections zero_hom (to_fun → apply)
initialize_simps_projections add_hom (to_fun → apply)
initialize_simps_projections add_monoid_hom (to_fun → apply)

initialize_simps_projections one_hom (to_fun → apply)
initialize_simps_projections mul_hom (to_fun → apply)
initialize_simps_projections monoid_hom (to_fun → apply)
initialize_simps_projections monoid_with_zero_hom (to_fun → apply)

@[simp, to_additive]
lemma one_hom.to_fun_eq_coe [has_one M] [has_one N] (f : one_hom M N) : f.to_fun = f := rfl
@[simp, to_additive]
lemma mul_hom.to_fun_eq_coe [has_mul M] [has_mul N] (f : M →ₙ* N) : f.to_fun = f := rfl
@[simp, to_additive]
lemma monoid_hom.to_fun_eq_coe [mul_one_class M] [mul_one_class N]
  (f : M →* N) : f.to_fun = f := rfl
@[simp]
lemma monoid_with_zero_hom.to_fun_eq_coe [mul_zero_one_class M] [mul_zero_one_class N]
  (f : M →*₀ N) : f.to_fun = f := rfl

@[simp, to_additive]
lemma one_hom.coe_mk [has_one M] [has_one N]
  (f : M → N) (h1) : (one_hom.mk f h1 : M → N) = f := rfl
@[simp, to_additive]
lemma mul_hom.coe_mk [has_mul M] [has_mul N]
  (f : M → N) (hmul) : (mul_hom.mk f hmul : M → N) = f := rfl
@[simp, to_additive]
lemma monoid_hom.coe_mk [mul_one_class M] [mul_one_class N]
  (f : M → N) (h1 hmul) : (monoid_hom.mk f h1 hmul : M → N) = f := rfl
@[simp]
lemma monoid_with_zero_hom.coe_mk [mul_zero_one_class M] [mul_zero_one_class N]
  (f : M → N) (h0 h1 hmul) : (monoid_with_zero_hom.mk f h0 h1 hmul : M → N) = f := rfl

@[simp, to_additive]
lemma monoid_hom.to_one_hom_coe [mul_one_class M] [mul_one_class N] (f : M →* N) :
  (f.to_one_hom : M → N) = f := rfl
@[simp, to_additive]
lemma monoid_hom.to_mul_hom_coe [mul_one_class M] [mul_one_class N] (f : M →* N) :
  (f.to_mul_hom : M → N) = f := rfl
@[simp]
lemma monoid_with_zero_hom.to_zero_hom_coe [mul_zero_one_class M] [mul_zero_one_class N]
  (f : M →*₀ N) :
  (f.to_zero_hom : M → N) = f := rfl
@[simp]
lemma monoid_with_zero_hom.to_monoid_hom_coe [mul_zero_one_class M] [mul_zero_one_class N]
  (f : M →*₀ N) :
  (f.to_monoid_hom : M → N) = f := rfl

@[ext, to_additive]
lemma one_hom.ext [has_one M] [has_one N] ⦃f g : one_hom M N⦄ (h : ∀ x, f x = g x) : f = g :=
fun_like.ext _ _ h
@[ext, to_additive]
lemma mul_hom.ext [has_mul M] [has_mul N] ⦃f g : M →ₙ* N⦄ (h : ∀ x, f x = g x) : f = g :=
fun_like.ext _ _ h
@[ext, to_additive]
lemma monoid_hom.ext [mul_one_class M] [mul_one_class N]
  ⦃f g : M →* N⦄ (h : ∀ x, f x = g x) : f = g :=
fun_like.ext _ _ h
@[ext]
lemma monoid_with_zero_hom.ext [mul_zero_one_class M] [mul_zero_one_class N] ⦃f g : M →*₀ N⦄
  (h : ∀ x, f x = g x) : f = g :=
fun_like.ext _ _ h

section deprecated

/-- Deprecated: use `fun_like.congr_fun` instead. -/
@[to_additive "Deprecated: use `fun_like.congr_fun` instead."]
theorem one_hom.congr_fun [has_one M] [has_one N]
  {f g : one_hom M N} (h : f = g) (x : M) : f x = g x :=
fun_like.congr_fun h x
/-- Deprecated: use `fun_like.congr_fun` instead. -/
@[to_additive "Deprecated: use `fun_like.congr_fun` instead."]
theorem mul_hom.congr_fun [has_mul M] [has_mul N]
  {f g : M →ₙ* N} (h : f = g) (x : M) : f x = g x :=
fun_like.congr_fun h x
/-- Deprecated: use `fun_like.congr_fun` instead. -/
@[to_additive "Deprecated: use `fun_like.congr_fun` instead."]
theorem monoid_hom.congr_fun [mul_one_class M] [mul_one_class N]
  {f g : M →* N} (h : f = g) (x : M) : f x = g x :=
fun_like.congr_fun h x
/-- Deprecated: use `fun_like.congr_fun` instead. -/
theorem monoid_with_zero_hom.congr_fun [mul_zero_one_class M] [mul_zero_one_class N] {f g : M →*₀ N}
  (h : f = g) (x : M) : f x = g x :=
fun_like.congr_fun h x

/-- Deprecated: use `fun_like.congr_arg` instead. -/
@[to_additive "Deprecated: use `fun_like.congr_arg` instead."]
theorem one_hom.congr_arg [has_one M] [has_one N]
  (f : one_hom M N) {x y : M} (h : x = y) : f x = f y :=
fun_like.congr_arg f h
/-- Deprecated: use `fun_like.congr_arg` instead. -/
@[to_additive "Deprecated: use `fun_like.congr_arg` instead."]
theorem mul_hom.congr_arg [has_mul M] [has_mul N]
  (f : M →ₙ* N) {x y : M} (h : x = y) : f x = f y :=
fun_like.congr_arg f h
/-- Deprecated: use `fun_like.congr_arg` instead. -/
@[to_additive "Deprecated: use `fun_like.congr_arg` instead."]
theorem monoid_hom.congr_arg [mul_one_class M] [mul_one_class N]
  (f : M →* N) {x y : M} (h : x = y) : f x = f y :=
fun_like.congr_arg f h
/-- Deprecated: use `fun_like.congr_arg` instead. -/
theorem monoid_with_zero_hom.congr_arg [mul_zero_one_class M] [mul_zero_one_class N] (f : M →*₀ N)
  {x y : M} (h : x = y) : f x = f y :=
fun_like.congr_arg f h

/-- Deprecated: use `fun_like.coe_injective` instead. -/
@[to_additive "Deprecated: use `fun_like.coe_injective` instead."]
lemma one_hom.coe_inj [has_one M] [has_one N] ⦃f g : one_hom M N⦄ (h : (f : M → N) = g) : f = g :=
fun_like.coe_injective h
/-- Deprecated: use `fun_like.coe_injective` instead. -/
@[to_additive "Deprecated: use `fun_like.coe_injective` instead."]
lemma mul_hom.coe_inj [has_mul M] [has_mul N] ⦃f g : M →ₙ* N⦄ (h : (f : M → N) = g) : f = g :=
fun_like.coe_injective h
/-- Deprecated: use `fun_like.coe_injective` instead. -/
@[to_additive "Deprecated: use `fun_like.coe_injective` instead."]
lemma monoid_hom.coe_inj [mul_one_class M] [mul_one_class N]
  ⦃f g : M →* N⦄ (h : (f : M → N) = g) : f = g :=
fun_like.coe_injective h
/-- Deprecated: use `fun_like.coe_injective` instead. -/
lemma monoid_with_zero_hom.coe_inj [mul_zero_one_class M] [mul_zero_one_class N]
  ⦃f g : M →*₀ N⦄ (h : (f : M → N) = g) : f = g :=
fun_like.coe_injective h

/-- Deprecated: use `fun_like.ext_iff` instead. -/
@[to_additive "Deprecated: use `fun_like.ext_iff` instead."]
lemma one_hom.ext_iff [has_one M] [has_one N] {f g : one_hom M N} : f = g ↔ ∀ x, f x = g x :=
fun_like.ext_iff
/-- Deprecated: use `fun_like.ext_iff` instead. -/
@[to_additive]
lemma mul_hom.ext_iff [has_mul M] [has_mul N] {f g : M →ₙ* N} : f = g ↔ ∀ x, f x = g x :=
fun_like.ext_iff
/-- Deprecated: use `fun_like.ext_iff` instead. -/
@[to_additive]
lemma monoid_hom.ext_iff [mul_one_class M] [mul_one_class N]
  {f g : M →* N} : f = g ↔ ∀ x, f x = g x :=
fun_like.ext_iff
/-- Deprecated: use `fun_like.ext_iff` instead. -/
lemma monoid_with_zero_hom.ext_iff [mul_zero_one_class M] [mul_zero_one_class N] {f g : M →*₀ N} :
  f = g ↔ ∀ x, f x = g x :=
fun_like.ext_iff
end deprecated

@[simp, to_additive]
lemma one_hom.mk_coe [has_one M] [has_one N]
  (f : one_hom M N) (h1) : one_hom.mk f h1 = f :=
one_hom.ext $ λ _, rfl
@[simp, to_additive]
lemma mul_hom.mk_coe [has_mul M] [has_mul N]
  (f : M →ₙ* N) (hmul) : mul_hom.mk f hmul = f :=
mul_hom.ext $ λ _, rfl
@[simp, to_additive]
lemma monoid_hom.mk_coe [mul_one_class M] [mul_one_class N]
  (f : M →* N) (h1 hmul) : monoid_hom.mk f h1 hmul = f :=
monoid_hom.ext $ λ _, rfl
@[simp]
lemma monoid_with_zero_hom.mk_coe [mul_zero_one_class M] [mul_zero_one_class N] (f : M →*₀ N)
  (h0 h1 hmul) : monoid_with_zero_hom.mk f h0 h1 hmul = f :=
monoid_with_zero_hom.ext $ λ _, rfl

end coes

/-- Copy of a `one_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
@[to_additive "Copy of a `zero_hom` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities."]
protected def one_hom.copy {hM : has_one M} {hN : has_one N} (f : one_hom M N) (f' : M → N)
  (h : f' = f) : one_hom M N :=
{ to_fun := f',
  map_one' := h.symm ▸ f.map_one' }

/-- Copy of a `mul_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
@[to_additive "Copy of an `add_hom` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities."]
protected def mul_hom.copy {hM : has_mul M} {hN : has_mul N} (f : M →ₙ* N) (f' : M → N)
  (h : f' = f) : M →ₙ* N :=
{ to_fun := f',
  map_mul' := h.symm ▸ f.map_mul' }

/-- Copy of a `monoid_hom` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
@[to_additive "Copy of an `add_monoid_hom` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities."]
protected def monoid_hom.copy {hM : mul_one_class M} {hN : mul_one_class N} (f : M →* N)
  (f' : M → N) (h : f' = f) : M →* N :=
{ ..f.to_one_hom.copy f' h, ..f.to_mul_hom.copy f' h }

/-- Copy of a `monoid_hom` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def monoid_with_zero_hom.copy {hM : mul_zero_one_class M} {hN : mul_zero_one_class N}
  (f : M →*₀ N) (f' : M → N) (h : f' = f) : M →* N :=
{ ..f.to_zero_hom.copy f' h, ..f.to_monoid_hom.copy f' h }

@[to_additive]
protected lemma one_hom.map_one [has_one M] [has_one N] (f : one_hom M N) : f 1 = 1 := f.map_one'
/-- If `f` is a monoid homomorphism then `f 1 = 1`. -/
@[to_additive]
protected lemma monoid_hom.map_one [mul_one_class M] [mul_one_class N] (f : M →* N) :
  f 1 = 1 := f.map_one'
protected lemma monoid_with_zero_hom.map_one [mul_zero_one_class M] [mul_zero_one_class N]
  (f : M →*₀ N) : f 1 = 1 := f.map_one'

/-- If `f` is an additive monoid homomorphism then `f 0 = 0`. -/
add_decl_doc add_monoid_hom.map_zero
protected lemma monoid_with_zero_hom.map_zero [mul_zero_one_class M] [mul_zero_one_class N]
  (f : M →*₀ N) : f 0 = 0 := f.map_zero'

@[to_additive]
protected lemma mul_hom.map_mul [has_mul M] [has_mul N]
  (f : M →ₙ* N) (a b : M) : f (a * b) = f a * f b := f.map_mul' a b
/-- If `f` is a monoid homomorphism then `f (a * b) = f a * f b`. -/
@[to_additive]
protected lemma monoid_hom.map_mul [mul_one_class M] [mul_one_class N]
  (f : M →* N) (a b : M) : f (a * b) = f a * f b := f.map_mul' a b
protected lemma monoid_with_zero_hom.map_mul [mul_zero_one_class M] [mul_zero_one_class N]
  (f :  M →*₀ N) (a b : M) : f (a * b) = f a * f b := f.map_mul' a b

/-- If `f` is an additive monoid homomorphism then `f (a + b) = f a + f b`. -/
add_decl_doc add_monoid_hom.map_add

namespace monoid_hom
variables {mM : mul_one_class M} {mN : mul_one_class N} {mP : mul_one_class P}
variables [group G] [comm_group H] [monoid_hom_class F M N]

include mM mN

/-- Given a monoid homomorphism `f : M →* N` and an element `x : M`, if `x` has a right inverse,
then `f x` has a right inverse too. For elements invertible on both sides see `is_unit.map`. -/
@[to_additive "Given an add_monoid homomorphism `f : M →+ N` and an element `x : M`, if `x` has
a right inverse, then `f x` has a right inverse too."]
lemma map_exists_right_inv (f : F) {x : M} (hx : ∃ y, x * y = 1) :
  ∃ y, f x * y = 1 :=
let ⟨y, hy⟩ := hx in ⟨f y, map_mul_eq_one f hy⟩

/-- Given a monoid homomorphism `f : M →* N` and an element `x : M`, if `x` has a left inverse,
then `f x` has a left inverse too. For elements invertible on both sides see `is_unit.map`. -/
@[to_additive "Given an add_monoid homomorphism `f : M →+ N` and an element `x : M`, if `x` has
a left inverse, then `f x` has a left inverse too. For elements invertible on both sides see
`is_add_unit.map`."]
lemma map_exists_left_inv (f : F) {x : M} (hx : ∃ y, y * x = 1) :
  ∃ y, y * f x = 1 :=
let ⟨y, hy⟩ := hx in ⟨f y, map_mul_eq_one f hy⟩

end monoid_hom

/-- Inversion on a commutative group, considered as a monoid homomorphism. -/
@[to_additive "Inversion on a commutative additive group, considered as an additive
monoid homomorphism."]
def comm_group.inv_monoid_hom {G : Type*} [comm_group G] : G →* G :=
{ to_fun := has_inv.inv,
  map_one' := inv_one,
  map_mul' := mul_inv }

/-- The identity map from a type with 1 to itself. -/
@[to_additive, simps]
def one_hom.id (M : Type*) [has_one M] : one_hom M M :=
{ to_fun := λ x, x, map_one' := rfl, }
/-- The identity map from a type with multiplication to itself. -/
@[to_additive, simps]
def mul_hom.id (M : Type*) [has_mul M] : M →ₙ* M :=
{ to_fun := λ x, x, map_mul' := λ _ _, rfl, }
/-- The identity map from a monoid to itself. -/
@[to_additive, simps]
def monoid_hom.id (M : Type*) [mul_one_class M] : M →* M :=
{ to_fun := λ x, x, map_one' := rfl, map_mul' := λ _ _, rfl, }
/-- The identity map from a monoid_with_zero to itself. -/
@[simps]
def monoid_with_zero_hom.id (M : Type*) [mul_zero_one_class M] : M →*₀ M :=
{ to_fun := λ x, x, map_zero' := rfl, map_one' := rfl, map_mul' := λ _ _, rfl, }

/-- The identity map from an type with zero to itself. -/
add_decl_doc zero_hom.id
/-- The identity map from an type with addition to itself. -/
add_decl_doc add_hom.id
/-- The identity map from an additive monoid to itself. -/
add_decl_doc add_monoid_hom.id

/-- Composition of `one_hom`s as a `one_hom`. -/
@[to_additive]
def one_hom.comp [has_one M] [has_one N] [has_one P]
  (hnp : one_hom N P) (hmn : one_hom M N) : one_hom M P :=
{ to_fun := hnp ∘ hmn, map_one' := by simp, }
/-- Composition of `mul_hom`s as a `mul_hom`. -/
@[to_additive]
def mul_hom.comp [has_mul M] [has_mul N] [has_mul P]
  (hnp : N →ₙ* P) (hmn : M →ₙ* N) : M →ₙ* P :=
{ to_fun := hnp ∘ hmn, map_mul' := by simp, }

/-- Composition of monoid morphisms as a monoid morphism. -/
@[to_additive]
def monoid_hom.comp [mul_one_class M] [mul_one_class N] [mul_one_class P]
  (hnp : N →* P) (hmn : M →* N) : M →* P :=
{ to_fun := hnp ∘ hmn, map_one' := by simp, map_mul' := by simp, }

/-- Composition of `monoid_with_zero_hom`s as a `monoid_with_zero_hom`. -/
def monoid_with_zero_hom.comp [mul_zero_one_class M] [mul_zero_one_class N] [mul_zero_one_class P]
  (hnp : N →*₀ P) (hmn : M →*₀ N) : M →*₀ P :=
{ to_fun := hnp ∘ hmn, map_zero' := by simp, map_one' := by simp, map_mul' := by simp, }

/-- Composition of `zero_hom`s as a `zero_hom`. -/
add_decl_doc zero_hom.comp
/-- Composition of `add_hom`s as a `add_hom`. -/
add_decl_doc add_hom.comp
/-- Composition of additive monoid morphisms as an additive monoid morphism. -/
add_decl_doc add_monoid_hom.comp

@[simp, to_additive] lemma one_hom.coe_comp [has_one M] [has_one N] [has_one P]
  (g : one_hom N P) (f : one_hom M N) :
  ⇑(g.comp f) = g ∘ f := rfl
@[simp, to_additive] lemma mul_hom.coe_comp [has_mul M] [has_mul N] [has_mul P]
  (g : N →ₙ* P) (f : M →ₙ* N) :
  ⇑(g.comp f) = g ∘ f := rfl
@[simp, to_additive] lemma monoid_hom.coe_comp [mul_one_class M] [mul_one_class N] [mul_one_class P]
  (g : N →* P) (f : M →* N) :
  ⇑(g.comp f) = g ∘ f := rfl
@[simp] lemma monoid_with_zero_hom.coe_comp [mul_zero_one_class M] [mul_zero_one_class N]
  [mul_zero_one_class P] (g : N →*₀ P) (f : M →*₀ N) :
  ⇑(g.comp f) = g ∘ f := rfl

@[to_additive] lemma one_hom.comp_apply [has_one M] [has_one N] [has_one P]
  (g : one_hom N P) (f : one_hom M N) (x : M) :
  g.comp f x = g (f x) := rfl
@[to_additive] lemma mul_hom.comp_apply [has_mul M] [has_mul N] [has_mul P]
  (g : N →ₙ* P) (f : M →ₙ* N) (x : M) :
  g.comp f x = g (f x) := rfl
@[to_additive] lemma monoid_hom.comp_apply [mul_one_class M] [mul_one_class N] [mul_one_class P]
  (g : N →* P) (f : M →* N) (x : M) :
  g.comp f x = g (f x) := rfl
lemma monoid_with_zero_hom.comp_apply [mul_zero_one_class M] [mul_zero_one_class N]
  [mul_zero_one_class P] (g : N →*₀ P) (f : M →*₀ N) (x : M) :
  g.comp f x = g (f x) := rfl

/-- Composition of monoid homomorphisms is associative. -/
@[to_additive] lemma one_hom.comp_assoc {Q : Type*} [has_one M] [has_one N] [has_one P] [has_one Q]
  (f : one_hom M N) (g : one_hom N P) (h : one_hom P Q) :
  (h.comp g).comp f = h.comp (g.comp f) := rfl
@[to_additive] lemma mul_hom.comp_assoc {Q : Type*} [has_mul M] [has_mul N] [has_mul P] [has_mul Q]
  (f : M →ₙ* N) (g : N →ₙ* P) (h : P →ₙ* Q) :
  (h.comp g).comp f = h.comp (g.comp f) := rfl
@[to_additive] lemma monoid_hom.comp_assoc {Q : Type*}
  [mul_one_class M] [mul_one_class N] [mul_one_class P] [mul_one_class Q]
  (f : M →* N) (g : N →* P) (h : P →* Q) :
  (h.comp g).comp f = h.comp (g.comp f) := rfl
lemma monoid_with_zero_hom.comp_assoc {Q : Type*}
  [mul_zero_one_class M] [mul_zero_one_class N] [mul_zero_one_class P] [mul_zero_one_class Q]
  (f : M →*₀ N) (g : N →*₀ P) (h : P →*₀ Q) :
  (h.comp g).comp f = h.comp (g.comp f) := rfl

@[to_additive]
lemma one_hom.cancel_right [has_one M] [has_one N] [has_one P]
  {g₁ g₂ : one_hom N P} {f : one_hom M N} (hf : function.surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, one_hom.ext $ hf.forall.2 (one_hom.ext_iff.1 h), λ h, h ▸ rfl⟩
@[to_additive]
lemma mul_hom.cancel_right [has_mul M] [has_mul N] [has_mul P]
  {g₁ g₂ : N →ₙ* P} {f : M →ₙ* N} (hf : function.surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, mul_hom.ext $ hf.forall.2 (mul_hom.ext_iff.1 h), λ h, h ▸ rfl⟩
@[to_additive]
lemma monoid_hom.cancel_right
  [mul_one_class M] [mul_one_class N] [mul_one_class P]
  {g₁ g₂ : N →* P} {f : M →* N} (hf : function.surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, monoid_hom.ext $ hf.forall.2 (monoid_hom.ext_iff.1 h), λ h, h ▸ rfl⟩
lemma monoid_with_zero_hom.cancel_right [mul_zero_one_class M] [mul_zero_one_class N]
  [mul_zero_one_class P] {g₁ g₂ : N →*₀ P} {f : M →*₀ N} (hf : function.surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, monoid_with_zero_hom.ext $ hf.forall.2 (monoid_with_zero_hom.ext_iff.1 h),
 λ h, h ▸ rfl⟩

@[to_additive]
lemma one_hom.cancel_left [has_one M] [has_one N] [has_one P]
  {g : one_hom N P} {f₁ f₂ : one_hom M N} (hg : function.injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, one_hom.ext $ λ x, hg $ by rw [← one_hom.comp_apply, h, one_hom.comp_apply],
 λ h, h ▸ rfl⟩
@[to_additive]
lemma mul_hom.cancel_left [has_mul M] [has_mul N] [has_mul P]
  {g : N →ₙ* P} {f₁ f₂ : M →ₙ* N} (hg : function.injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, mul_hom.ext $ λ x, hg $ by rw [← mul_hom.comp_apply, h, mul_hom.comp_apply],
 λ h, h ▸ rfl⟩
@[to_additive]
lemma monoid_hom.cancel_left [mul_one_class M] [mul_one_class N] [mul_one_class P]
  {g : N →* P} {f₁ f₂ : M →* N} (hg : function.injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, monoid_hom.ext $ λ x, hg $ by rw [← monoid_hom.comp_apply, h, monoid_hom.comp_apply],
 λ h, h ▸ rfl⟩
lemma monoid_with_zero_hom.cancel_left [mul_zero_one_class M] [mul_zero_one_class N]
  [mul_zero_one_class P] {g : N →*₀ P} {f₁ f₂ : M →*₀ N} (hg : function.injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, monoid_with_zero_hom.ext $ λ x, hg $ by rw [
        ← monoid_with_zero_hom.comp_apply, h, monoid_with_zero_hom.comp_apply],
 λ h, h ▸ rfl⟩

@[to_additive]
lemma monoid_hom.to_one_hom_injective [mul_one_class M] [mul_one_class N] :
  function.injective (monoid_hom.to_one_hom : (M →* N) → one_hom M N) :=
λ f g h, monoid_hom.ext $ one_hom.ext_iff.mp h
@[to_additive]
lemma monoid_hom.to_mul_hom_injective [mul_one_class M] [mul_one_class N] :
  function.injective (monoid_hom.to_mul_hom : (M →* N) → M →ₙ* N) :=
λ f g h, monoid_hom.ext $ mul_hom.ext_iff.mp h
lemma monoid_with_zero_hom.to_monoid_hom_injective [mul_zero_one_class M] [mul_zero_one_class N] :
  function.injective (monoid_with_zero_hom.to_monoid_hom : (M →*₀ N) → M →* N) :=
λ f g h, monoid_with_zero_hom.ext $ monoid_hom.ext_iff.mp h
lemma monoid_with_zero_hom.to_zero_hom_injective [mul_zero_one_class M] [mul_zero_one_class N] :
  function.injective (monoid_with_zero_hom.to_zero_hom : (M →*₀ N) → zero_hom M N) :=
λ f g h, monoid_with_zero_hom.ext $ zero_hom.ext_iff.mp h

@[simp, to_additive] lemma one_hom.comp_id [has_one M] [has_one N]
  (f : one_hom M N) : f.comp (one_hom.id M) = f := one_hom.ext $ λ x, rfl
@[simp, to_additive] lemma mul_hom.comp_id [has_mul M] [has_mul N]
  (f : M →ₙ* N) : f.comp (mul_hom.id M) = f := mul_hom.ext $ λ x, rfl
@[simp, to_additive] lemma monoid_hom.comp_id [mul_one_class M] [mul_one_class N]
  (f : M →* N) : f.comp (monoid_hom.id M) = f := monoid_hom.ext $ λ x, rfl
@[simp] lemma monoid_with_zero_hom.comp_id [mul_zero_one_class M] [mul_zero_one_class N]
  (f : M →*₀ N) : f.comp (monoid_with_zero_hom.id M) = f :=
monoid_with_zero_hom.ext $ λ x, rfl

@[simp, to_additive] lemma one_hom.id_comp [has_one M] [has_one N]
  (f : one_hom M N) : (one_hom.id N).comp f = f := one_hom.ext $ λ x, rfl
@[simp, to_additive] lemma mul_hom.id_comp [has_mul M] [has_mul N]
  (f : M →ₙ* N) : (mul_hom.id N).comp f = f := mul_hom.ext $ λ x, rfl
@[simp, to_additive] lemma monoid_hom.id_comp [mul_one_class M] [mul_one_class N]
  (f : M →* N) : (monoid_hom.id N).comp f = f := monoid_hom.ext $ λ x, rfl
@[simp] lemma monoid_with_zero_hom.id_comp [mul_zero_one_class M] [mul_zero_one_class N]
  (f : M →*₀ N) : (monoid_with_zero_hom.id N).comp f = f :=
monoid_with_zero_hom.ext $ λ x, rfl

@[to_additive add_monoid_hom.map_nsmul]
protected theorem monoid_hom.map_pow [monoid M] [monoid N] (f : M →* N) (a : M) (n : ℕ) :
  f (a ^ n) = (f a) ^ n :=
map_pow f a n

@[to_additive]
protected theorem monoid_hom.map_zpow' [div_inv_monoid M] [div_inv_monoid N] (f : M →* N)
  (hf : ∀ x, f (x⁻¹) = (f x)⁻¹) (a : M) (n : ℤ) :
  f (a ^ n) = (f a) ^ n :=
map_zpow' f hf a n

section End

namespace monoid

variables (M) [mul_one_class M]

/-- The monoid of endomorphisms. -/
protected def End := M →* M

namespace End

instance : monoid (monoid.End M) :=
{ mul := monoid_hom.comp,
  one := monoid_hom.id M,
  mul_assoc := λ _ _ _, monoid_hom.comp_assoc _ _ _,
  mul_one := monoid_hom.comp_id,
  one_mul := monoid_hom.id_comp }

instance : inhabited (monoid.End M) := ⟨1⟩

instance : has_coe_to_fun (monoid.End M) (λ _, M → M) := ⟨monoid_hom.to_fun⟩

end End

@[simp] lemma coe_one : ((1 : monoid.End M) : M → M) = id := rfl
@[simp] lemma coe_mul (f g) : ((f * g : monoid.End M) : M → M) = f ∘ g := rfl

end monoid

namespace add_monoid

variables (A : Type*) [add_zero_class A]

/-- The monoid of endomorphisms. -/
protected def End := A →+ A

namespace End

instance : monoid (add_monoid.End A) :=
{ mul := add_monoid_hom.comp,
  one := add_monoid_hom.id A,
  mul_assoc := λ _ _ _, add_monoid_hom.comp_assoc _ _ _,
  mul_one := add_monoid_hom.comp_id,
  one_mul := add_monoid_hom.id_comp }

instance : inhabited (add_monoid.End A) := ⟨1⟩

instance : has_coe_to_fun (add_monoid.End A) (λ _, A → A) := ⟨add_monoid_hom.to_fun⟩

end End

@[simp] lemma coe_one : ((1 : add_monoid.End A) : A → A) = id := rfl
@[simp] lemma coe_mul (f g) : ((f * g : add_monoid.End A) : A → A) = f ∘ g := rfl

end add_monoid

end End

/-- `1` is the homomorphism sending all elements to `1`. -/
@[to_additive]
instance [has_one M] [has_one N] : has_one (one_hom M N) := ⟨⟨λ _, 1, rfl⟩⟩
/-- `1` is the multiplicative homomorphism sending all elements to `1`. -/
@[to_additive]
instance [has_mul M] [mul_one_class N] : has_one (M →ₙ* N) :=
⟨⟨λ _, 1, λ _ _, (one_mul 1).symm⟩⟩
/-- `1` is the monoid homomorphism sending all elements to `1`. -/
@[to_additive]
instance [mul_one_class M] [mul_one_class N] : has_one (M →* N) :=
⟨⟨λ _, 1, rfl, λ _ _, (one_mul 1).symm⟩⟩

/-- `0` is the homomorphism sending all elements to `0`. -/
add_decl_doc zero_hom.has_zero
/-- `0` is the additive homomorphism sending all elements to `0`. -/
add_decl_doc add_hom.has_zero
/-- `0` is the additive monoid homomorphism sending all elements to `0`. -/
add_decl_doc add_monoid_hom.has_zero

@[simp, to_additive] lemma one_hom.one_apply [has_one M] [has_one N]
  (x : M) : (1 : one_hom M N) x = 1 := rfl
@[simp, to_additive] lemma monoid_hom.one_apply [mul_one_class M] [mul_one_class N]
  (x : M) : (1 : M →* N) x = 1 := rfl

@[simp, to_additive] lemma one_hom.one_comp [has_one M] [has_one N] [has_one P] (f : one_hom M N) :
  (1 : one_hom N P).comp f = 1 := rfl
@[simp, to_additive] lemma one_hom.comp_one [has_one M] [has_one N] [has_one P] (f : one_hom N P) :
  f.comp (1 : one_hom M N) = 1 :=
by { ext, simp only [one_hom.map_one, one_hom.coe_comp, function.comp_app, one_hom.one_apply] }

@[to_additive]
instance [has_one M] [has_one N] : inhabited (one_hom M N) := ⟨1⟩
@[to_additive]
instance [has_mul M] [mul_one_class N] : inhabited (M →ₙ* N) := ⟨1⟩
@[to_additive]
instance [mul_one_class M] [mul_one_class N] : inhabited (M →* N) := ⟨1⟩
-- unlike the other homs, `monoid_with_zero_hom` does not have a `1` or `0`
instance [mul_zero_one_class M] : inhabited (M →*₀ M) := ⟨monoid_with_zero_hom.id M⟩

namespace mul_hom

/-- Given two mul morphisms `f`, `g` to a commutative semigroup, `f * g` is the mul morphism
sending `x` to `f x * g x`. -/
@[to_additive]
instance [has_mul M] [comm_semigroup N] : has_mul (M →ₙ* N) :=
⟨λ f g,
  { to_fun := λ m, f m * g m,
    map_mul' := begin intros, show f (x * y) * g (x * y) = f x * g x * (f y * g y),
      rw [f.map_mul, g.map_mul, ←mul_assoc, ←mul_assoc, mul_right_comm (f x)], end }⟩

/-- Given two additive morphisms `f`, `g` to an additive commutative semigroup, `f + g` is the
additive morphism sending `x` to `f x + g x`. -/
add_decl_doc add_hom.has_add

@[simp, to_additive] lemma mul_apply {M N} {mM : has_mul M} {mN : comm_semigroup N}
  (f g : M →ₙ* N) (x : M) :
  (f * g) x = f x * g x := rfl

@[to_additive] lemma mul_comp [has_mul M] [has_mul N] [comm_semigroup P]
  (g₁ g₂ : N →ₙ* P) (f : M →ₙ* N) :
  (g₁ * g₂).comp f = g₁.comp f * g₂.comp f := rfl
@[to_additive] lemma comp_mul [has_mul M] [comm_semigroup N] [comm_semigroup P]
  (g : N →ₙ* P) (f₁ f₂ : M →ₙ* N) :
  g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂ :=
by { ext, simp only [mul_apply, function.comp_app, map_mul, coe_comp] }

end mul_hom

namespace monoid_hom
variables [mM : mul_one_class M] [mN : mul_one_class N] [mP : mul_one_class P]
variables [group G] [comm_group H]

/-- Given two monoid morphisms `f`, `g` to a commutative monoid, `f * g` is the monoid morphism
sending `x` to `f x * g x`. -/
@[to_additive]
instance {M N} {mM : mul_one_class M} [comm_monoid N] : has_mul (M →* N) :=
⟨λ f g,
  { to_fun := λ m, f m * g m,
    map_one' := show f 1 * g 1 = 1, by simp,
    map_mul' := begin intros, show f (x * y) * g (x * y) = f x * g x * (f y * g y),
      rw [f.map_mul, g.map_mul, ←mul_assoc, ←mul_assoc, mul_right_comm (f x)], end }⟩

/-- Given two additive monoid morphisms `f`, `g` to an additive commutative monoid, `f + g` is the
additive monoid morphism sending `x` to `f x + g x`. -/
add_decl_doc add_monoid_hom.has_add

@[simp, to_additive] lemma mul_apply {M N} {mM : mul_one_class M} {mN : comm_monoid N}
  (f g : M →* N) (x : M) :
  (f * g) x = f x * g x := rfl

@[simp, to_additive] lemma one_comp [mul_one_class M] [mul_one_class N] [mul_one_class P]
  (f : M →* N) : (1 : N →* P).comp f = 1 := rfl
@[simp, to_additive] lemma comp_one [mul_one_class M] [mul_one_class N] [mul_one_class P]
  (f : N →* P) : f.comp (1 : M →* N) = 1 :=
by { ext, simp only [map_one, coe_comp, function.comp_app, one_apply] }

@[to_additive] lemma mul_comp [mul_one_class M] [mul_one_class N] [comm_monoid P]
  (g₁ g₂ : N →* P) (f : M →* N) :
  (g₁ * g₂).comp f = g₁.comp f * g₂.comp f := rfl
@[to_additive] lemma comp_mul [mul_one_class M] [comm_monoid N] [comm_monoid P]
  (g : N →* P) (f₁ f₂ : M →* N) :
  g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂ :=
by { ext, simp only [mul_apply, function.comp_app, map_mul, coe_comp] }

/-- If two homomorphism from a group to a monoid are equal at `x`, then they are equal at `x⁻¹`. -/
@[to_additive "If two homomorphism from an additive group to an additive monoid are equal at `x`,
then they are equal at `-x`." ]
lemma eq_on_inv {G} [group G] [monoid M] [monoid_hom_class F G M] {f g : F} {x : G}
  (h : f x = g x) : f x⁻¹ = g x⁻¹ :=
left_inv_eq_right_inv (map_mul_eq_one f $ inv_mul_self x) $
  h.symm ▸ map_mul_eq_one g $ mul_inv_self x

/-- Group homomorphisms preserve inverse. -/
@[to_additive]
protected theorem map_inv {G H} [group G] [group H] (f : G →* H) (g : G) : f g⁻¹ = (f g)⁻¹ :=
map_inv f g

/-- Group homomorphisms preserve integer power. -/
@[to_additive "Additive group homomorphisms preserve integer scaling."]
protected theorem map_zpow {G H} [group G] [group H] (f : G →* H) (g : G) (n : ℤ) :
  f (g ^ n) = (f g) ^ n :=
map_zpow f g n

/-- Group homomorphisms preserve division. -/
@[to_additive "Additive group homomorphisms preserve subtraction."]
protected theorem map_div {G H} [group G] [group H] (f : G →* H) (g h : G) :
  f (g / h) = f g / f h :=
map_div f g h

/-- Group homomorphisms preserve division. -/
@[to_additive]
protected theorem map_mul_inv {G H} [group G] [group H] (f : G →* H) (g h : G) :
  f (g * h⁻¹) = (f g) * (f h)⁻¹ :=
map_mul_inv f g h

/-- A homomorphism from a group to a monoid is injective iff its kernel is trivial.
For the iff statement on the triviality of the kernel, see `injective_iff_map_eq_one'`.  -/
@[to_additive "A homomorphism from an additive group to an additive monoid is injective iff
its kernel is trivial. For the iff statement on the triviality of the kernel,
see `injective_iff_map_eq_zero'`."]
lemma _root_.injective_iff_map_eq_one {G H} [group G] [mul_one_class H] [monoid_hom_class F G H]
  (f : F) : function.injective f ↔ (∀ a, f a = 1 → a = 1) :=
⟨λ h x, (map_eq_one_iff f h).mp,
 λ h x y hxy, mul_inv_eq_one.1 $ h _ $ by rw [map_mul, hxy, ← map_mul, mul_inv_self, map_one]⟩

/-- A homomorphism from a group to a monoid is injective iff its kernel is trivial,
stated as an iff on the triviality of the kernel.
For the implication, see `injective_iff_map_eq_one`. -/
@[to_additive "A homomorphism from an additive group to an additive monoid is injective iff its
kernel is trivial, stated as an iff on the triviality of the kernel. For the implication, see
`injective_iff_map_eq_zero`."]
lemma _root_.injective_iff_map_eq_one' {G H} [group G] [mul_one_class H] [monoid_hom_class F G H]
  (f : F) : function.injective f ↔ (∀ a, f a = 1 ↔ a = 1) :=
(injective_iff_map_eq_one f).trans $ forall_congr $ λ a, ⟨λ h, ⟨h, λ H, H.symm ▸ map_one f⟩, iff.mp⟩

include mM
/-- Makes a group homomorphism from a proof that the map preserves multiplication. -/
@[to_additive "Makes an additive group homomorphism from a proof that the map preserves addition.",
  simps {fully_applied := ff}]
def mk' (f : M → G) (map_mul : ∀ a b : M, f (a * b) = f a * f b) : M →* G :=
{ to_fun := f,
  map_mul' := map_mul,
  map_one' := mul_left_eq_self.1 $ by rw [←map_mul, mul_one] }

omit mM

/-- Makes a group homomorphism from a proof that the map preserves right division `λ x y, x * y⁻¹`.
See also `monoid_hom.of_map_div` for a version using `λ x y, x / y`.
-/
@[to_additive "Makes an additive group homomorphism from a proof that the map preserves
the operation `λ a b, a + -b`. See also `add_monoid_hom.of_map_sub` for a version using
`λ a b, a - b`."]
def of_map_mul_inv {H : Type*} [group H] (f : G → H)
  (map_div : ∀ a b : G, f (a * b⁻¹) = f a * (f b)⁻¹) :
  G →* H :=
mk' f $ λ x y,
calc f (x * y) = f x * (f $ 1 * 1⁻¹ * y⁻¹)⁻¹ : by simp only [one_mul, inv_one, ← map_div, inv_inv]
... = f x * f y : by { simp only [map_div], simp only [mul_right_inv, one_mul, inv_inv] }

@[simp, to_additive] lemma coe_of_map_mul_inv {H : Type*} [group H] (f : G → H)
  (map_div : ∀ a b : G, f (a * b⁻¹) = f a * (f b)⁻¹) :
  ⇑(of_map_mul_inv f map_div) = f :=
rfl

/-- Define a morphism of additive groups given a map which respects ratios. -/
@[to_additive /-"Define a morphism of additive groups given a map which respects difference."-/]
def of_map_div {H : Type*} [group H] (f : G → H) (hf : ∀ x y, f (x / y) = f x / f y) : G →* H :=
of_map_mul_inv f (by simpa only [div_eq_mul_inv] using hf)

@[simp, to_additive]
lemma coe_of_map_div {H : Type*} [group H] (f : G → H) (hf : ∀ x y, f (x / y) = f x / f y) :
  ⇑(of_map_div f hf) = f :=
rfl

/-- If `f` is a monoid homomorphism to a commutative group, then `f⁻¹` is the homomorphism sending
`x` to `(f x)⁻¹`. -/
@[to_additive]
instance {M G} [mul_one_class M] [comm_group G] : has_inv (M →* G) :=
⟨λ f, mk' (λ g, (f g)⁻¹) $ λ a b, by rw [←mul_inv, f.map_mul]⟩

/-- If `f` is an additive monoid homomorphism to an additive commutative group, then `-f` is the
homomorphism sending `x` to `-(f x)`. -/
add_decl_doc add_monoid_hom.has_neg

@[simp, to_additive] lemma inv_apply {M G} {mM : mul_one_class M} {gG : comm_group G}
  (f : M →* G) (x : M) :
  f⁻¹ x = (f x)⁻¹ := rfl

@[simp, to_additive] lemma inv_comp {M N A} {mM : mul_one_class M} {gN : mul_one_class N}
  {gA : comm_group A} (φ : N →* A) (ψ : M →* N) : φ⁻¹.comp ψ = (φ.comp ψ)⁻¹ :=
by { ext, simp only [function.comp_app, inv_apply, coe_comp] }

@[simp, to_additive] lemma comp_inv {M A B} {mM : mul_one_class M} {mA : comm_group A}
  {mB : comm_group B} (φ : A →* B) (ψ : M →* A) : φ.comp ψ⁻¹ = (φ.comp ψ)⁻¹ :=
by { ext, simp only [function.comp_app, inv_apply, map_inv, coe_comp] }

/-- If `f` and `g` are monoid homomorphisms to a commutative group, then `f / g` is the homomorphism
sending `x` to `(f x) / (g x)`. -/
@[to_additive]
instance {M G} [mul_one_class M] [comm_group G] : has_div (M →* G) :=
⟨λ f g, mk' (λ x, f x / g x) $ λ a b,
  by simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]⟩

/-- If `f` and `g` are monoid homomorphisms to an additive commutative group, then `f - g`
is the homomorphism sending `x` to `(f x) - (g x)`. -/
add_decl_doc add_monoid_hom.has_sub

@[simp, to_additive] lemma div_apply {M G} {mM : mul_one_class M} {gG : comm_group G}
  (f g : M →* G) (x : M) :
  (f / g) x = f x / g x := rfl

end monoid_hom

/-- Given two monoid with zero morphisms `f`, `g` to a commutative monoid, `f * g` is the monoid
with zero morphism sending `x` to `f x * g x`. -/
instance {M N} {hM : mul_zero_one_class M} [comm_monoid_with_zero N] : has_mul (M →*₀ N) :=
⟨λ f g,
  { to_fun := λ a, f a * g a,
    map_zero' := by rw [map_zero, zero_mul],
    ..(f * g : M →* N) }⟩

section commute

variables [has_mul M] [has_mul N] {a x y : M}

@[simp, to_additive]
protected lemma semiconj_by.map [mul_hom_class F M N] (h : semiconj_by a x y) (f : F) :
  semiconj_by (f a) (f x) (f y) :=
by simpa only [semiconj_by, map_mul] using congr_arg f h

@[simp, to_additive]
protected lemma commute.map [mul_hom_class F M N] (h : commute x y) (f : F) :
  commute (f x) (f y) :=
h.map f

end commute

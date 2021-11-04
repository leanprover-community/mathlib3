/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kevin Buzzard, Scott Morrison, Johan Commelin, Chris Hughes,
  Johannes Hölzl, Yury Kudryashov
-/

import algebra.group_power.basic

/-!
# Instances on spaces of monoid and group morphisms

We endow the space of monoid morphisms `M →* N` with a `comm_monoid` structure when the target is
commutative, through pointwise multiplication, and with a `comm_group` structure when the target
is a commutative group. We also prove the same instances for additive situations.

Since these structures permit morphisms of morphisms, we also provide some composition-like
operations.

Finally, we provide the `ring` structure on `add_monoid.End`.
-/

universes uM uN uP uQ
variables {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ}

/-- `(M →* N)` is a `comm_monoid` if `N` is commutative. -/
@[to_additive "`(M →+ N)` is an `add_comm_monoid` if `N` is commutative."]
instance [mul_one_class M] [comm_monoid N] : comm_monoid (M →* N) :=
{ mul := (*),
  mul_assoc := by intros; ext; apply mul_assoc,
  one := 1,
  one_mul := by intros; ext; apply one_mul,
  mul_one := by intros; ext; apply mul_one,
  mul_comm := by intros; ext; apply mul_comm,
  npow := λ n f,
  { to_fun := λ x, npow n (f x),
    map_one' := by simp,
    map_mul' := λ x y, by simp [mul_pow] },
  npow_zero' := λ f, by { ext x, simp },
  npow_succ' := λ n f, by { ext x, simp [pow_succ] } }

/-- If `G` is a commutative group, then `M →* G` is a commutative group too. -/
@[to_additive "If `G` is an additive commutative group, then `M →+ G` is an additive commutative
group too."]
instance {M G} [mul_one_class M] [comm_group G] : comm_group (M →* G) :=
{ inv := has_inv.inv,
  div := has_div.div,
  div_eq_mul_inv := by { intros, ext, apply div_eq_mul_inv },
  mul_left_inv := by intros; ext; apply mul_left_inv,
  zpow := λ n f, { to_fun := λ x, zpow n (f x),
    map_one' := by simp,
    map_mul' := λ x y, by simp [mul_zpow] },
  zpow_zero' := λ f, by { ext x, simp },
  zpow_succ' := λ n f, by { ext x, simp [zpow_of_nat, pow_succ] },
  zpow_neg'  := λ n f, by { ext x, simp },
  ..monoid_hom.comm_monoid }

instance [add_comm_monoid M] : semiring (add_monoid.End M) :=
{ zero_mul := λ x, add_monoid_hom.ext $ λ i, rfl,
  mul_zero := λ x, add_monoid_hom.ext $ λ i, add_monoid_hom.map_zero _,
  left_distrib := λ x y z, add_monoid_hom.ext $ λ i, add_monoid_hom.map_add _ _ _,
  right_distrib := λ x y z, add_monoid_hom.ext $ λ i, rfl,
  .. add_monoid.End.monoid M,
  .. add_monoid_hom.add_comm_monoid }

instance [add_comm_group M] : ring (add_monoid.End M) :=
{ .. add_monoid.End.semiring,
  .. add_monoid_hom.add_comm_group }

/-!
### Morphisms of morphisms

The structures above permit morphisms that themselves produce morphisms, provided the codomain
is commutative.
-/

namespace monoid_hom

@[to_additive]
lemma ext_iff₂ {mM : mul_one_class M} {mN : mul_one_class N} {mP : comm_monoid P}
  {f g : M →* N →* P} :
  f = g ↔ (∀ x y, f x y = g x y) :=
monoid_hom.ext_iff.trans $ forall_congr $ λ _, monoid_hom.ext_iff

/-- `flip` arguments of `f : M →* N →* P` -/
@[to_additive "`flip` arguments of `f : M →+ N →+ P`"]
def flip {mM : mul_one_class M} {mN : mul_one_class N} {mP : comm_monoid P} (f : M →* N →* P) :
  N →* M →* P :=
{ to_fun := λ y, ⟨λ x, f x y, by rw [f.map_one, one_apply], λ x₁ x₂, by rw [f.map_mul, mul_apply]⟩,
  map_one' := ext $ λ x, (f x).map_one,
  map_mul' := λ y₁ y₂, ext $ λ x, (f x).map_mul y₁ y₂ }

@[simp, to_additive] lemma flip_apply
  {mM : mul_one_class M} {mN : mul_one_class N} {mP : comm_monoid P}
  (f : M →* N →* P) (x : M) (y : N) :
  f.flip y x = f x y :=
rfl

@[to_additive]
lemma map_one₂ {mM : mul_one_class M} {mN : mul_one_class N} {mP : comm_monoid P}
  (f : M →* N →* P) (n : N) : f 1 n = 1 :=
(flip f n).map_one

@[to_additive]
lemma map_mul₂ {mM : mul_one_class M} {mN : mul_one_class N} {mP : comm_monoid P}
  (f : M →* N →* P) (m₁ m₂ : M) (n : N) : f (m₁ * m₂) n = f m₁ n * f m₂ n :=
(flip f n).map_mul _ _

@[to_additive]
lemma map_inv₂ {mM : group M} {mN : mul_one_class N} {mP : comm_group P}
  (f : M →* N →* P) (m : M) (n : N) : f m⁻¹ n = (f m n)⁻¹ :=
(flip f n).map_inv _

@[to_additive]
lemma map_div₂ {mM : group M} {mN : mul_one_class N} {mP : comm_group P}
  (f : M →* N →* P) (m₁ m₂ : M) (n : N) : f (m₁ / m₂) n = f m₁ n / f m₂ n :=
(flip f n).map_div _ _

/-- Evaluation of a `monoid_hom` at a point as a monoid homomorphism. See also `monoid_hom.apply`
for the evaluation of any function at a point. -/
@[to_additive "Evaluation of an `add_monoid_hom` at a point as an additive monoid homomorphism.
See also `add_monoid_hom.apply` for the evaluation of any function at a point.", simps]
def eval [mul_one_class M] [comm_monoid N] : M →* (M →* N) →* N := (monoid_hom.id (M →* N)).flip

/-- The expression `λ g m, g (f m)` as a `monoid_hom`.
Equivalently, `(λ g, monoid_hom.comp g f)` as a `monoid_hom`. -/
@[to_additive "The expression `λ g m, g (f m)` as a `add_monoid_hom`.
Equivalently, `(λ g, monoid_hom.comp g f)` as a `add_monoid_hom`.

This also exists in a `linear_map` version, `linear_map.lcomp`.", simps]
def comp_hom' [mul_one_class M] [mul_one_class N] [comm_monoid P] (f : M →* N) :
  (N →* P) →* M →* P :=
flip $ eval.comp f

/-- Composition of monoid morphisms (`monoid_hom.comp`) as a monoid morphism.

Note that unlike `monoid_hom.comp_hom'` this requires commutativity of `N`. -/
@[to_additive "Composition of additive monoid morphisms (`add_monoid_hom.comp`) as an additive
monoid morphism.

Note that unlike `add_monoid_hom.comp_hom'` this requires commutativity of `N`.

This also exists in a `linear_map` version, `linear_map.llcomp`.", simps]
def comp_hom [mul_one_class M] [comm_monoid N] [comm_monoid P] :
  (N →* P) →* (M →* N) →* (M →* P) :=
{ to_fun := λ g, { to_fun := g.comp, map_one' := comp_one g, map_mul' := comp_mul g },
  map_one' := by { ext1 f, exact one_comp f },
  map_mul' := λ g₁ g₂, by { ext1 f, exact mul_comp g₁ g₂ f } }

/-- Flipping arguments of monoid morphisms (`monoid_hom.flip`) as a monoid morphism. -/
@[to_additive "Flipping arguments of additive monoid morphisms (`add_monoid_hom.flip`)
as an additive monoid morphism.", simps]
def flip_hom {mM : mul_one_class M} {mN : mul_one_class N} {mP : comm_monoid P}
  : (M →* N →* P) →* (N →* M →* P) :=
{ to_fun := monoid_hom.flip, map_one' := rfl, map_mul' := λ f g, rfl }

/-- The expression `λ m q, f m (g q)` as a `monoid_hom`.

Note that the expression `λ q n, f (g q) n` is simply `monoid_hom.comp`. -/
@[to_additive "The expression `λ m q, f m (g q)` as an `add_monoid_hom`.

Note that the expression `λ q n, f (g q) n` is simply `add_monoid_hom.comp`.

This also exists as a `linear_map` version, `linear_map.compl₂`"]
def compl₂ [mul_one_class M] [mul_one_class N] [comm_monoid P] [comm_monoid Q]
  (f : M →* N →* P) (g : Q →* N) : M →* Q →* P :=
(comp_hom' g).comp f

@[simp, to_additive]
lemma compl₂_apply [mul_one_class M] [mul_one_class N] [comm_monoid P] [comm_monoid Q]
  (f : M →* N →* P) (g : Q →* N) (m : M) (q : Q) :
  (compl₂ f g) m q = f m (g q) := rfl

/-- The expression `λ m n, g (f m n)` as a `monoid_hom`. -/
@[to_additive "The expression `λ m n, g (f m n)` as an `add_monoid_hom`.

This also exists as a linear_map version, `linear_map.compr₂`"]
def compr₂ [mul_one_class M] [mul_one_class N] [comm_monoid P] [comm_monoid Q]
  (f : M →* N →* P) (g : P →* Q) : M →* N →* Q :=
(comp_hom g).comp f

@[simp, to_additive]
lemma compr₂_apply [mul_one_class M] [mul_one_class N] [comm_monoid P] [comm_monoid Q]
  (f : M →* N →* P) (g : P →* Q) (m : M) (n : N) :
  (compr₂ f g) m n = g (f m n) := rfl

end monoid_hom

/-!
### Miscellaneous definitions

Due to the fact this file imports `algebra.group_power.basic`, it is not possible to import it in
some of the lower-level files like `algebra.ring.basic`. The following lemmas should be rehomed
if the import structure permits them to be.
-/

section semiring

variables {R S : Type*} [semiring R] [semiring S]

/-- Multiplication of an element of a (semi)ring is an `add_monoid_hom` in both arguments.

This is a more-strongly bundled version of `add_monoid_hom.mul_left` and `add_monoid_hom.mul_right`.

A stronger version of this exists for algebras as `algebra.lmul`.
-/
def add_monoid_hom.mul : R →+ R →+ R :=
{ to_fun := add_monoid_hom.mul_left,
  map_zero' := add_monoid_hom.ext $ zero_mul,
  map_add' := λ a b, add_monoid_hom.ext $ add_mul a b }

lemma add_monoid_hom.mul_apply (x y : R) : add_monoid_hom.mul x y = x * y := rfl

@[simp]
lemma add_monoid_hom.coe_mul :
  ⇑(add_monoid_hom.mul : R →+ R →+ R) = add_monoid_hom.mul_left := rfl

@[simp]
lemma add_monoid_hom.coe_flip_mul :
  ⇑(add_monoid_hom.mul : R →+ R →+ R).flip = add_monoid_hom.mul_right := rfl

/-- An `add_monoid_hom` preserves multiplication if pre- and post- composition with
`add_monoid_hom.mul` are equivalent. By converting the statement into an equality of
`add_monoid_hom`s, this lemma allows various specialized `ext` lemmas about `→+` to then be applied.
-/
lemma add_monoid_hom.map_mul_iff (f : R →+ S) :
  (∀ x y, f (x * y) = f x * f y) ↔
    (add_monoid_hom.mul : R →+ R →+ R).compr₂ f = (add_monoid_hom.mul.comp f).compl₂ f :=
iff.symm add_monoid_hom.ext_iff₂

end semiring

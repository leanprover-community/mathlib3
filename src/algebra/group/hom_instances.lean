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
commutative, through pointwise multipliplication, and with a `comm_group` structure when the target
is a commutative group. We also prove the same instances for additive situations.
-/

universes uM uN uP
variables {M : Type uM} {N : Type uN} {P : Type uP}

lemma nat.succ_eq_one_add (n : ℕ) : n.succ = 1 + n :=
by rw [nat.succ_eq_add_one, nat.add_comm]

/-- `(M →* N)` is a `comm_monoid` if `N` is commutative. -/
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

/-- `(M →+ N)` is an `add_comm_monoid` if `N` is commutative. -/
instance [add_zero_class M] [add_comm_monoid N] : add_comm_monoid (M →+ N) :=
{ add := (+),
  add_assoc := by intros; ext; apply add_assoc,
  zero := 0,
  zero_add := by intros; ext; apply zero_add,
  add_zero := by intros; ext; apply add_zero,
  add_comm := by intros; ext; apply add_comm,
  nsmul := λ n f,
  { to_fun := λ x, nsmul n (f x),
    map_zero' := by simp [nsmul_zero],
    map_add' := λ x y, by simp [nsmul_add] },
  nsmul_zero' := λ f, by { ext x, simp [zero_nsmul], },
  nsmul_succ' := λ n f, by { ext x, simp [nat.succ_eq_one_add, add_nsmul] } }

attribute [to_additive] monoid_hom.comm_monoid

namespace monoid_hom

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

/-- Evaluation of a `monoid_hom` at a point as a monoid homomorphism. See also `monoid_hom.apply`
for the evaluation of any function at a point. -/
@[to_additive "Evaluation of an `add_monoid_hom` at a point as an additive monoid homomorphism.
See also `add_monoid_hom.apply` for the evaluation of any function at a point.", simps]
def eval [mul_one_class M] [comm_monoid N] : M →* (M →* N) →* N := (monoid_hom.id (M →* N)).flip

/-- Composition of monoid morphisms (`monoid_hom.comp`) as a monoid morphism. -/
@[to_additive "Composition of additive monoid morphisms
(`add_monoid_hom.comp`) as an additive monoid morphism.", simps]
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

end monoid_hom

/-- If `G` is a commutative group, then `M →* G` a commutative group too. -/
instance {M G} [mul_one_class M] [comm_group G] : comm_group (M →* G) :=
{ inv := has_inv.inv,
  div := has_div.div,
  div_eq_mul_inv := by { intros, ext, apply div_eq_mul_inv },
  mul_left_inv := by intros; ext; apply mul_left_inv,
  gpow := λ n f, { to_fun := λ x, gpow n (f x),
    map_one' := by simp,
    map_mul' := λ x y, by simp [mul_gpow] },
  gpow_zero' := λ f, by { ext x, simp },
  gpow_succ' := λ n f, by { ext x, simp [gpow_of_nat, pow_succ] },
  gpow_neg'  := λ n f, by { ext x, simp },
  ..monoid_hom.comm_monoid }

/-- If `G` is an additive commutative group, then `M →+ G` an additive commutative group too. -/
instance {M G} [add_zero_class M] [add_comm_group G] : add_comm_group (M →+ G) :=
{ neg := has_neg.neg,
  sub := has_sub.sub,
  sub_eq_add_neg := by { intros, ext, apply sub_eq_add_neg },
  add_left_neg := by intros; ext; apply add_left_neg,
  gsmul := λ n f, { to_fun := λ x, gsmul n (f x),
    map_zero' := by simp,
    map_add' := λ x y, by simp [gsmul_add] },
  gsmul_zero' := λ f, by { ext x, simp },
  gsmul_succ' := λ n f, by { ext x, simp [gsmul_of_nat, nat.succ_eq_one_add, add_nsmul] },
  gsmul_neg'  := λ n f, by { ext x, simp },
  ..add_monoid_hom.add_comm_monoid }

attribute [to_additive] monoid_hom.comm_group

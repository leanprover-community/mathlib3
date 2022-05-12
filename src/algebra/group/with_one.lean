/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johan Commelin
-/
import algebra.hom.equiv
import algebra.ring.basic
import logic.equiv.basic
import logic.equiv.option

/-!
# Adjoining a zero/one to semigroups and related algebraic structures

This file contains different results about adjoining an element to an algebraic structure which then
behaves like a zero or a one. An example is adjoining a one to a semigroup to obtain a monoid. That
this provides an example of an adjunction is proved in `algebra.category.Mon.adjunctions`.

Another result says that adjoining to a group an element `zero` gives a `group_with_zero`. For more
information about these structures (which are not that standard in informal mathematics, see
`algebra.group_with_zero.basic`)
-/

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

/-- Add an extra element `1` to a type -/
@[to_additive "Add an extra element `0` to a type"]
def with_one (α) := option α

namespace with_one

instance [has_repr α] : has_repr (with_zero α) :=
⟨λ o, match o with | none := "0" | (some a) := "↑" ++ repr a end⟩

@[to_additive]
instance [has_repr α] : has_repr (with_one α) :=
⟨λ o, match o with | none := "1" | (some a) := "↑" ++ repr a end⟩

@[to_additive]
instance : monad with_one := option.monad

@[to_additive]
instance : has_one (with_one α) := ⟨none⟩

@[to_additive]
instance [has_mul α] : has_mul (with_one α) := ⟨option.lift_or_get (*)⟩

@[to_additive] instance [has_inv α] : has_inv (with_one α) := ⟨λ a, option.map has_inv.inv a⟩

@[to_additive] instance [has_involutive_inv α] : has_involutive_inv (with_one α) :=
{ inv_inv := λ a, (option.map_map _ _ _).trans $ by simp_rw [inv_comp_inv, option.map_id, id],
  ..with_one.has_inv }

@[to_additive]
instance : inhabited (with_one α) := ⟨1⟩

@[to_additive]
instance [nonempty α] : nontrivial (with_one α) := option.nontrivial

@[to_additive]
instance : has_coe_t α (with_one α) := ⟨some⟩

@[to_additive]
lemma some_eq_coe {a : α} : (some a : with_one α) = ↑a := rfl

@[simp, to_additive]
lemma coe_ne_one {a : α} : (a : with_one α) ≠ (1 : with_one α) :=
option.some_ne_none a

@[simp, to_additive]
lemma one_ne_coe {a : α} : (1 : with_one α) ≠ a :=
coe_ne_one.symm

@[to_additive]
lemma ne_one_iff_exists {x : with_one α} : x ≠ 1 ↔ ∃ (a : α), ↑a = x :=
option.ne_none_iff_exists

@[to_additive]
instance : can_lift (with_one α) α :=
{ coe := coe,
  cond := λ a, a ≠ 1,
  prf := λ a, ne_one_iff_exists.1 }

@[simp, norm_cast, to_additive]
lemma coe_inj {a b : α} : (a : with_one α) = b ↔ a = b :=
option.some_inj

@[elab_as_eliminator, to_additive]
protected lemma cases_on {P : with_one α → Prop} :
  ∀ (x : with_one α), P 1 → (∀ a : α, P a) → P x :=
option.cases_on

-- the `show` statements in the proofs are important, because otherwise the generated lemmas
-- `with_one.mul_one_class._proof_{1,2}` have an ill-typed statement after `with_one` is made
-- irreducible.
@[to_additive]
instance [has_mul α] : mul_one_class (with_one α) :=
{ mul := (*),
  one := (1),
  one_mul   := show ∀ x : with_one α, 1 * x = x, from (option.lift_or_get_is_left_id _).1,
  mul_one   := show ∀ x : with_one α, x * 1 = x, from (option.lift_or_get_is_right_id _).1 }

@[to_additive]
instance [semigroup α] : monoid (with_one α) :=
{ mul_assoc := (option.lift_or_get_assoc _).1,
  ..with_one.mul_one_class }

example [semigroup α] :
  @monoid.to_mul_one_class _ (@with_one.monoid α _) = @with_one.mul_one_class α _ := rfl

@[to_additive]
instance [comm_semigroup α] : comm_monoid (with_one α) :=
{ mul_comm := (option.lift_or_get_comm _).1,
  ..with_one.monoid }

section
-- workaround: we make `with_one`/`with_zero` irreducible for this definition, otherwise `simps`
-- will unfold it in the statement of the lemma it generates.
local attribute [irreducible] with_one with_zero
/-- `coe` as a bundled morphism -/
@[to_additive "`coe` as a bundled morphism", simps apply]
def coe_mul_hom [has_mul α] : α →ₙ* (with_one α) :=
{ to_fun := coe, map_mul' := λ x y, rfl }

end

section lift

variables [has_mul α] [mul_one_class β]

/-- Lift a semigroup homomorphism `f` to a bundled monoid homorphism. -/
@[to_additive "Lift an add_semigroup homomorphism `f` to a bundled add_monoid homorphism."]
def lift : (α →ₙ* β) ≃ (with_one α →* β) :=
{ to_fun := λ f,
  { to_fun := λ x, option.cases_on x 1 f,
    map_one' := rfl,
    map_mul' := λ x y,
      with_one.cases_on x (by { rw one_mul, exact (one_mul _).symm }) $ λ x,
      with_one.cases_on y (by { rw mul_one, exact (mul_one _).symm }) $ λ y,
      f.map_mul x y },
  inv_fun := λ F, F.to_mul_hom.comp coe_mul_hom,
  left_inv := λ f, mul_hom.ext $ λ x, rfl,
  right_inv := λ F, monoid_hom.ext $ λ x, with_one.cases_on x F.map_one.symm $ λ x, rfl }

variables (f : α →ₙ* β)

@[simp, to_additive]
lemma lift_coe (x : α) : lift f x = f x := rfl

@[simp, to_additive]
lemma lift_one : lift f 1 = 1 := rfl

@[to_additive]
theorem lift_unique (f : with_one α →* β) : f = lift (f.to_mul_hom.comp coe_mul_hom) :=
(lift.apply_symm_apply f).symm

end lift

attribute [irreducible] with_one

section map

variables [has_mul α] [has_mul β] [has_mul γ]

/-- Given a multiplicative map from `α → β` returns a monoid homomorphism
  from `with_one α` to `with_one β` -/
@[to_additive "Given an additive map from `α → β` returns an add_monoid homomorphism
  from `with_zero α` to `with_zero β`"]
def map (f : α →ₙ* β) : with_one α →* with_one β :=
lift (coe_mul_hom.comp f)

@[simp, to_additive] lemma map_coe (f : α →ₙ* β) (a : α) : map f (a : with_one α) = f a :=
lift_coe _ _

@[simp, to_additive]
lemma map_id : map (mul_hom.id α) = monoid_hom.id (with_one α) :=
by { ext, induction x using with_one.cases_on; refl }

@[to_additive]
lemma map_map (f : α →ₙ* β) (g : β →ₙ* γ) (x) :
  map g (map f x) = map (g.comp f) x :=
by { induction x using with_one.cases_on; refl }

@[simp, to_additive]
lemma map_comp (f : α →ₙ* β) (g : β →ₙ* γ) :
  map (g.comp f) = (map g).comp (map f) :=
monoid_hom.ext $ λ x, (map_map f g x).symm

/-- A version of `equiv.option_congr` for `with_one`. -/
@[to_additive "A version of `equiv.option_congr` for `with_zero`.", simps apply]
def _root_.mul_equiv.with_one_congr (e : α ≃* β) : with_one α ≃* with_one β :=
{ to_fun := map e.to_mul_hom,
  inv_fun := map e.symm.to_mul_hom,
  left_inv := λ x, (map_map _ _ _).trans $ by induction x using with_one.cases_on; { simp },
  right_inv := λ x, (map_map _ _ _).trans $ by induction x using with_one.cases_on; { simp },
  .. map e.to_mul_hom }

@[simp]
lemma _root_.mul_equiv.with_one_congr_refl : (mul_equiv.refl α).with_one_congr = mul_equiv.refl _ :=
mul_equiv.to_monoid_hom_injective map_id

@[simp]
lemma _root_.mul_equiv.with_one_congr_symm (e : α ≃* β) :
  e.with_one_congr.symm = e.symm.with_one_congr := rfl

@[simp]
lemma _root_.mul_equiv.with_one_congr_trans (e₁ : α ≃* β) (e₂ : β ≃* γ) :
  e₁.with_one_congr.trans e₂.with_one_congr = (e₁.trans e₂).with_one_congr :=
mul_equiv.to_monoid_hom_injective (map_comp _ _).symm

end map

@[simp, norm_cast, to_additive]
lemma coe_mul [has_mul α] (a b : α) : ((a * b : α) : with_one α) = a * b := rfl

@[simp, norm_cast, to_additive]
lemma coe_inv [has_inv α] (a : α) : ((a⁻¹ : α) : with_one α) = a⁻¹ := rfl

end with_one

namespace with_zero

instance [one : has_one α] : has_one (with_zero α) :=
{ ..one }

@[simp, norm_cast] lemma coe_one [has_one α] : ((1 : α) : with_zero α) = 1 := rfl

instance [has_mul α] : mul_zero_class (with_zero α) :=
{ mul       := λ o₁ o₂, o₁.bind (λ a, option.map (λ b, a * b) o₂),
  zero_mul  := λ a, rfl,
  mul_zero  := λ a, by cases a; refl,
  ..with_zero.has_zero }

@[simp, norm_cast] lemma coe_mul {α : Type u} [has_mul α]
  {a b : α} : ((a * b : α) : with_zero α) = a * b := rfl

@[simp] lemma zero_mul {α : Type u} [has_mul α]
  (a : with_zero α) : 0 * a = 0 := rfl

@[simp] lemma mul_zero {α : Type u} [has_mul α]
  (a : with_zero α) : a * 0 = 0 := by cases a; refl

instance [semigroup α] : semigroup_with_zero (with_zero α) :=
{ mul_assoc := λ a b c, match a, b, c with
    | none,   _,      _      := rfl
    | some a, none,   _      := rfl
    | some a, some b, none   := rfl
    | some a, some b, some c := congr_arg some (mul_assoc _ _ _)
    end,
  ..with_zero.mul_zero_class }

instance [comm_semigroup α] : comm_semigroup (with_zero α) :=
{ mul_comm := λ a b, match a, b with
    | none,   _      := (mul_zero _).symm
    | some a, none   := rfl
    | some a, some b := congr_arg some (mul_comm _ _)
    end,
  ..with_zero.semigroup_with_zero }

instance [mul_one_class α] : mul_zero_one_class (with_zero α) :=
{ one_mul := λ a, match a with
    | none   := rfl
    | some a := congr_arg some $ one_mul _
    end,
  mul_one := λ a, match a with
    | none   := rfl
    | some a := congr_arg some $ mul_one _
    end,
  ..with_zero.mul_zero_class,
  ..with_zero.has_one }

instance [has_one α] [has_pow α ℕ] : has_pow (with_zero α) ℕ :=
⟨λ x n, match x, n with
  | none, 0 := 1
  | none, n + 1 := 0
  | some x, n := ↑(x ^ n)
  end⟩

@[simp, norm_cast] lemma coe_pow [has_one α] [has_pow α ℕ] {a : α} (n : ℕ) :
  ↑(a ^ n : α) = (↑a ^ n : with_zero α) := rfl

instance [monoid α] : monoid_with_zero (with_zero α) :=
{ npow := λ n x, x ^ n,
  npow_zero' := λ x, match x with
    | none   := rfl
    | some x := congr_arg some $ pow_zero _
    end,
  npow_succ' := λ n x, match x with
    | none   := rfl
    | some x := congr_arg some $ pow_succ _ _
    end,
  .. with_zero.mul_zero_one_class,
  .. with_zero.semigroup_with_zero }

instance [comm_monoid α] : comm_monoid_with_zero (with_zero α) :=
{ ..with_zero.monoid_with_zero, ..with_zero.comm_semigroup }

/-- Given an inverse operation on `α` there is an inverse operation
  on `with_zero α` sending `0` to `0`-/
instance [has_inv α] : has_inv (with_zero α) := ⟨λ a, option.map has_inv.inv a⟩

@[simp, norm_cast] lemma coe_inv [has_inv α] (a : α) : ((a⁻¹ : α) : with_zero α) = a⁻¹ := rfl

@[simp] lemma inv_zero [has_inv α] : (0 : with_zero α)⁻¹ = 0 := rfl

instance [has_involutive_inv α] : has_involutive_inv (with_zero α) :=
{ inv_inv := λ a, (option.map_map _ _ _).trans $ by simp_rw [inv_comp_inv, option.map_id, id],
  ..with_zero.has_inv }

instance [has_div α] : has_div (with_zero α) :=
⟨λ o₁ o₂, o₁.bind (λ a, option.map (λ b, a / b) o₂)⟩

@[norm_cast] lemma coe_div [has_div α] (a b : α) : ↑(a / b : α) = (a / b : with_zero α) := rfl

instance [has_one α] [has_pow α ℤ] : has_pow (with_zero α) ℤ :=
⟨λ x n, match x, n with
  | none, int.of_nat 0            := 1
  | none, int.of_nat (nat.succ n) := 0
  | none, int.neg_succ_of_nat n   := 0
  | some x, n                     := ↑(x ^ n)
  end⟩

@[simp, norm_cast] lemma coe_zpow [div_inv_monoid α] {a : α} (n : ℤ) :
  ↑(a ^ n : α) = (↑a ^ n : with_zero α) := rfl

instance [div_inv_monoid α] : div_inv_monoid (with_zero α) :=
{ div_eq_mul_inv := λ a b, match a, b with
    | none,   _      := rfl
    | some a, none   := rfl
    | some a, some b := congr_arg some (div_eq_mul_inv _ _)
    end,
  zpow := λ n x, x ^ n,
  zpow_zero' := λ x, match x with
    | none   := rfl
    | some x := congr_arg some $ zpow_zero _
    end,
  zpow_succ' := λ n x, match x with
    | none   := rfl
    | some x := congr_arg some $ div_inv_monoid.zpow_succ' _ _
    end,
  zpow_neg' := λ n x, match x with
    | none   := rfl
    | some x := congr_arg some $ div_inv_monoid.zpow_neg' _ _
    end,
  .. with_zero.has_div,
  .. with_zero.has_inv,
  .. with_zero.monoid_with_zero, }

instance [division_monoid α] : division_monoid (with_zero α) :=
{ mul_inv_rev := λ a b, match a, b with
    | none,   none   := rfl
    | none,   some b := rfl
    | some a, none   := rfl
    | some a, some b := congr_arg some $ mul_inv_rev _ _
    end,
  inv_eq_of_mul := λ a b, match a, b with
    | none,   none   := λ _, rfl
    | none,   some b := by contradiction
    | some a, none   := by contradiction
    | some a, some b := λ h, congr_arg some $ inv_eq_of_mul_eq_one_right $ option.some_injective _ h
    end,
  .. with_zero.div_inv_monoid, .. with_zero.has_involutive_inv }

instance [division_comm_monoid α] : division_comm_monoid (with_zero α) :=
{ .. with_zero.division_monoid, .. with_zero.comm_semigroup }

section group
variables [group α]

@[simp] lemma inv_one : (1 : with_zero α)⁻¹ = 1 :=
show ((1⁻¹ : α) : with_zero α) = 1, by simp

/-- if `G` is a group then `with_zero G` is a group with zero. -/
instance : group_with_zero (with_zero α) :=
{ inv_zero := inv_zero,
  mul_inv_cancel := λ a ha, by { lift a to α using ha, norm_cast, apply mul_right_inv },
  .. with_zero.monoid_with_zero,
  .. with_zero.div_inv_monoid,
  .. with_zero.nontrivial }

end group

instance [comm_group α] : comm_group_with_zero (with_zero α) :=
{ .. with_zero.group_with_zero, .. with_zero.comm_monoid_with_zero }

instance [semiring α] : semiring (with_zero α) :=
{ left_distrib := λ a b c, begin
    cases a with a, {refl},
    cases b with b; cases c with c; try {refl},
    exact congr_arg some (left_distrib _ _ _)
  end,
  right_distrib := λ a b c, begin
    cases c with c,
    { change (a + b) * 0 = a * 0 + b * 0, simp },
    cases a with a; cases b with b; try {refl},
    exact congr_arg some (right_distrib _ _ _)
  end,
  ..with_zero.add_comm_monoid,
  ..with_zero.mul_zero_class,
  ..with_zero.monoid_with_zero }

attribute [irreducible] with_zero

end with_zero

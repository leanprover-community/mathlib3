/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johan Commelin
-/
import order.with_bot
import algebra.ring.defs

/-!
# Adjoining a zero/one to semigroups and related algebraic structures

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains different results about adjoining an element to an algebraic structure which then
behaves like a zero or a one. An example is adjoining a one to a semigroup to obtain a monoid. That
this provides an example of an adjunction is proved in `algebra.category.Mon.adjunctions`.

Another result says that adjoining to a group an element `zero` gives a `group_with_zero`. For more
information about these structures (which are not that standard in informal mathematics, see
`algebra.group_with_zero.basic`)

## Implementation notes

At various points in this file, `id $` is used in at the start of a proof field in a structure. This
ensures that the generated `_proof_1` lemmas are stated in terms of the algebraic operations and
not `option.map`, as the latter does not typecheck once `with_zero`/`with_one` is irreducible.
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
{ inv_inv := id $ λ a, (option.map_map _ _ _).trans $ by simp_rw [inv_comp_inv, option.map_id, id],
  ..with_one.has_inv }

@[to_additive] instance [has_inv α] : inv_one_class (with_one α) :=
{ inv_one := rfl,
  ..with_one.has_one,
  ..with_one.has_inv }

@[to_additive]
instance : inhabited (with_one α) := ⟨1⟩

@[to_additive]
instance [nonempty α] : nontrivial (with_one α) := option.nontrivial

@[to_additive]
instance : has_coe_t α (with_one α) := ⟨some⟩

/-- Recursor for `with_one` using the preferred forms `1` and `↑a`. -/
@[elab_as_eliminator,
  to_additive "Recursor for `with_zero` using the preferred forms `0` and `↑a`."]
def rec_one_coe {C : with_one α → Sort*} (h₁ : C 1) (h₂ : Π (a : α), C a) :
  Π (n : with_one α), C n :=
option.rec h₁ h₂

/-- Deconstruct a `x : with_one α` to the underlying value in `α`, given a proof that `x ≠ 1`. -/
@[to_additive unzero
  "Deconstruct a `x : with_zero α` to the underlying value in `α`, given a proof that `x ≠ 0`."]
def unone {x : with_one α} (hx : x ≠ 1) : α := with_bot.unbot x hx

@[simp, to_additive unzero_coe]
lemma unone_coe {x : α} (hx : (x : with_one α) ≠ 1) : unone hx = x := rfl

@[simp, to_additive coe_unzero]
lemma coe_unone {x : with_one α} (hx : x ≠ 1) : ↑(unone hx) = x := with_bot.coe_unbot x hx

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
instance can_lift : can_lift (with_one α) α coe (λ a, a ≠ 1) :=
{ prf := λ a, ne_one_iff_exists.1 }

@[simp, norm_cast, to_additive]
lemma coe_inj {a b : α} : (a : with_one α) = b ↔ a = b :=
option.some_inj

@[elab_as_eliminator, to_additive]
protected lemma cases_on {P : with_one α → Prop} :
  ∀ (x : with_one α), P 1 → (∀ a : α, P a) → P x :=
option.cases_on

@[to_additive]
instance [has_mul α] : mul_one_class (with_one α) :=
{ mul := (*),
  one := (1),
  one_mul := id $ (option.lift_or_get_is_left_id _).1,
  mul_one := id $ (option.lift_or_get_is_right_id _).1 }

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

attribute [irreducible] with_one

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
{ mul       := option.map₂ (*),
  zero_mul  := id $ option.map₂_none_left (*),
  mul_zero  := id $ option.map₂_none_right (*),
  ..with_zero.has_zero }

@[simp, norm_cast] lemma coe_mul {α : Type u} [has_mul α]
  {a b : α} : ((a * b : α) : with_zero α) = a * b := rfl

instance [has_mul α] : no_zero_divisors (with_zero α) :=
⟨λ a b, id $ option.map₂_eq_none_iff.1⟩

instance [semigroup α] : semigroup_with_zero (with_zero α) :=
{ mul_assoc := id $ λ _ _ _, option.map₂_assoc mul_assoc,
  ..with_zero.mul_zero_class }

instance [comm_semigroup α] : comm_semigroup (with_zero α) :=
{ mul_comm := id $ λ _ _, option.map₂_comm mul_comm,
  ..with_zero.semigroup_with_zero }

instance [mul_one_class α] : mul_zero_one_class (with_zero α) :=
{ one_mul := id $ option.map₂_left_identity one_mul,
  mul_one := id $ option.map₂_right_identity mul_one,
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
{ inv_inv := id $ λ a, (option.map_map _ _ _).trans $ by simp_rw [inv_comp_inv, option.map_id, id],
  ..with_zero.has_inv }

instance [inv_one_class α] : inv_one_class (with_zero α) :=
{ inv_one := show ((1⁻¹ : α) : with_zero α) = 1, by simp,
  ..with_zero.has_one,
  ..with_zero.has_inv }

instance [has_div α] : has_div (with_zero α) := ⟨option.map₂ (/)⟩

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

instance [div_inv_one_monoid α] : div_inv_one_monoid (with_zero α) :=
{ ..with_zero.div_inv_monoid,
  ..with_zero.inv_one_class }

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

instance [add_monoid_with_one α] : add_monoid_with_one (with_zero α) :=
{ nat_cast := λ n, if n = 0 then 0 else (n.cast : α),
  nat_cast_zero := rfl,
  nat_cast_succ := λ n, begin
    cases n,
    show (((1 : ℕ) : α) : with_zero α) = 0 + 1, by rw [nat.cast_one, coe_one, zero_add],
    show (((n + 2 : ℕ) : α) : with_zero α) = ((n + 1 : ℕ) : α) + 1,
    by rw [nat.cast_succ, coe_add, coe_one],
  end,
  .. with_zero.add_monoid, ..with_zero.has_one }

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
  ..with_zero.add_monoid_with_one,
  ..with_zero.add_comm_monoid,
  ..with_zero.mul_zero_class,
  ..with_zero.monoid_with_zero }

attribute [irreducible] with_zero

end with_zero

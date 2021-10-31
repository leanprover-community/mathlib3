/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.equiv.mul_add
import tactic.pi_instances

/-!
# `ulift` instances for groups and monoids

This file defines instances for group, monoid, semigroup and related structures on `ulift` types.

(Recall `ulift α` is just a "copy" of a type `α` in a higher universe.)

We use `tactic.pi_instance_derive_field`, even though it wasn't intended for this purpose,
which seems to work fine.

We also provide `ulift.mul_equiv : ulift R ≃* R` (and its additive analogue).
-/

universes u v
variables {α : Type u} {x y : ulift.{v} α}

namespace ulift

@[to_additive] instance has_one [has_one α] : has_one (ulift α) := ⟨⟨1⟩⟩
@[simp, to_additive] lemma one_down [has_one α] : (1 : ulift α).down = 1 := rfl

@[to_additive] instance has_mul [has_mul α] : has_mul (ulift α) := ⟨λ f g, ⟨f.down * g.down⟩⟩
@[simp, to_additive] lemma mul_down [has_mul α] : (x * y).down = x.down * y.down := rfl

@[to_additive] instance has_div [has_div α] : has_div (ulift α) := ⟨λ f g, ⟨f.down / g.down⟩⟩
@[simp, to_additive] lemma div_down [has_div α] : (x / y).down = x.down / y.down := rfl

@[to_additive] instance has_inv [has_inv α] : has_inv (ulift α) := ⟨λ f, ⟨f.down⁻¹⟩⟩
@[simp, to_additive] lemma inv_down [has_inv α] : x⁻¹.down = (x.down)⁻¹ := rfl

/--
The multiplicative equivalence between `ulift α` and `α`.
-/
@[to_additive "The additive equivalence between `ulift α` and `α`."]
def mul_equiv [has_mul α] : ulift α ≃* α :=
{ to_fun := ulift.down,
  inv_fun := ulift.up,
  map_mul' := λ x y, rfl,
  left_inv := by tidy,
  right_inv := by tidy, }

@[to_additive]
instance semigroup [semigroup α] : semigroup (ulift α) :=
by refine_struct { mul := (*), .. }; tactic.pi_instance_derive_field

@[to_additive]
instance comm_semigroup [comm_semigroup α] : comm_semigroup (ulift α) :=
by refine_struct { mul := (*), .. }; tactic.pi_instance_derive_field

@[to_additive]
instance mul_one_class [mul_one_class α] : mul_one_class (ulift α) :=
by refine_struct { mul := (*), one := (1 : ulift α), .. }; tactic.pi_instance_derive_field

@[to_additive]
instance monoid [monoid α] : monoid (ulift α) :=
by refine_struct { one := (1 : ulift α), mul := (*), npow := λ n f, ⟨npow n f.down⟩ };
tactic.pi_instance_derive_field

@[to_additive]
instance comm_monoid [comm_monoid α] : comm_monoid (ulift α) :=
by refine_struct { one := (1 : ulift α), mul := (*), npow := λ n f, ⟨npow n f.down⟩ };
tactic.pi_instance_derive_field

@[to_additive]
instance group [group α] : group (ulift α) :=
by refine_struct { one := (1 : ulift α), mul := (*), inv := has_inv.inv, div := has_div.div,
  npow := λ n f, ⟨npow n f.down⟩, zpow := λ n f, ⟨zpow n f.down⟩ }; tactic.pi_instance_derive_field

@[to_additive]
instance comm_group [comm_group α] : comm_group (ulift α) :=
by refine_struct { one := (1 : ulift α), mul := (*), inv := has_inv.inv, div := has_div.div,
  npow := λ n f, ⟨npow n f.down⟩, zpow := λ n f, ⟨zpow n f.down⟩ }; tactic.pi_instance_derive_field

@[to_additive add_left_cancel_semigroup]
instance left_cancel_semigroup [left_cancel_semigroup α] :
  left_cancel_semigroup (ulift α) :=
begin
  refine_struct { mul := (*) }; tactic.pi_instance_derive_field,
  have := congr_arg ulift.down ‹_›,
  assumption,
end

@[to_additive add_right_cancel_semigroup]
instance right_cancel_semigroup [right_cancel_semigroup α] :
  right_cancel_semigroup (ulift α) :=
begin
  refine_struct { mul := (*) }; tactic.pi_instance_derive_field,
  have := congr_arg ulift.down ‹_›,
  assumption,
end

-- TODO we don't do `ordered_cancel_comm_monoid` or `ordered_comm_group`
-- We'd need to add instances for `ulift` in `order.basic`.

end ulift

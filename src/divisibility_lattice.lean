/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson.
-/

import order.conditionally_complete_lattice
import order.lattice
import tactic.pi_instances

/-!
# Divisibility Lattices

## Notations

## Implementation Notes
Trying to make a standard typeclass for structures with a sensibly defined dvd relation, as well as gcd, coprime, etc.
Experimenting with type tags, and

## References

-/

set_option old_structure_cmd true

open_locale classical

section divisibility_lattice

variable (α : Type)
/--A canonically ordered additive monoid which is also a lattice-/
class add_lattice extends lattice α, canonically_ordered_add_monoid α

/--A preorder with the symbol | -/
class dvd_preorder extends has_dvd α :=
(dvd_refl : ∀ a : α, a ∣ a)
(dvd_trans : ∀ a b c : α, a ∣ b → b ∣ c → a ∣ c)

/--A partial order with the symbol | -/
class dvd_order extends dvd_preorder α :=
(dvd_antisymm : ∀ a b : α, a ∣ b → b ∣ a → a = b)

/--A multiplicative analog of canonically_ordered_add_monoid-/
class dvd_monoid extends comm_monoid α, has_dvd α :=
(dvd_iff_exists_mul : ∀ a b : α, a ∣ b ↔ ∃ c : α, b = a * c)

class dvd_lattice extends dvd_monoid α :=
(gcd : α → α → α)
(inf_le_left : ∀ (a b : α), gcd a b ∣ a)
(inf_le_right : ∀ (a b : α), gcd a b ∣ b)
(le_inf : ∀ (a b c : α), a ∣ b → a ∣ c → a ∣ gcd b c)
(lcm : α → α → α)
(dvd_lcm_left : ∀ (a b : α), a ∣ lcm a b)
(dvd_lcm_right : ∀ (a b : α), b ∣ lcm a b)
(lcm_dvd : ∀ (a b c : α), a ∣ c → b ∣ c → lcm a b ∣ c)
(coprime : α → α → Prop)
(coprime_iff_gcd_one : ∀ (a b : α), coprime a b ↔ gcd a b = 1)

@[instance]
instance dvd_monoid.dvd_preorder [dvd_monoid α] : dvd_preorder α :=
begin
  refine dvd_preorder.mk has_dvd.dvd _ _; simp_rw dvd_monoid.dvd_iff_exists_mul; intros,
  { existsi (1 : α), simp },
  { cases a_1 with d hd, cases a_2 with e he, existsi d * e, rw [← mul_assoc, he, hd] }
end


@[instance]
instance additive.has_le [dvd_preorder α] : has_le (additive α) :=
{ le := λ x y, has_dvd.dvd x.to_mul y.to_mul }

@[instance]
instance multiplicative.has_dvd [has_le α] :
  has_dvd (multiplicative α) :=
{ dvd := λ x y, has_le.le x.to_add y.to_add }

@[instance]
instance multiplicative.dvd_preorder [preorder α] :
  dvd_preorder (multiplicative α) :=
{ dvd_refl := by { unfold has_dvd.dvd, apply le_refl },
  dvd_trans := by { unfold has_dvd.dvd, apply le_trans },
  ..multiplicative.has_dvd α }

@[instance]
instance additive.preorder [dvd_preorder α] :
  preorder (additive α) :=
{ le_refl := dvd_preorder.dvd_refl,
  le_trans := dvd_preorder.dvd_trans,
  ..additive.has_le α }

@[instance]
instance multiplicative.dvd_order [partial_order α] :
  dvd_order (multiplicative α) :=
{ dvd_antisymm := by { unfold has_dvd.dvd, apply le_antisymm },
  ..multiplicative.dvd_preorder α }

/--
@[instance]
instance dvd_monoid.canonically_ordered_add_monoid [dvd_monoid α] [dvd_order α] :
  canonically_ordered_add_monoid (additive α) :=
{ lt_of_add_lt_add_left := by {  },
  le_iff_exists_add     := by { unfold has_add.add, apply dvd_monoid.dvd_iff_exists_mul },
  add_le_add_left       := by { unfold has_add.add, rw le_iff_exists_add, },
  bot                   := 0,
  bot_le                := by { unfold has_le.le,  },
  ..additive.add_comm_monoid,
  ..additive.partial_order α }
  -/

@[instance]
instance additive.partial_order [dvd_order α] :
  partial_order (additive α) :=
{ le_antisymm := dvd_order.dvd_antisymm,
  ..additive.preorder α }



end divisibility_lattice

section order_iso_lattice

variables (α β: Type)

structure order_iso' [preorder α] [preorder β] :=
(to_equiv : α ≃ β)
(le_iff_le : ∀ a₁ a₂ : α, to_equiv.to_fun a₁ ≤ to_equiv.to_fun a₂ ↔ a₁ ≤ a₂ )

variables {α β}

def order_iso'.to_fun [preorder α] [preorder β] (f : order_iso' α β) : α → β := f.to_equiv.to_fun

instance [preorder α] [preorder β] : has_coe_to_fun (order_iso' α β) := ⟨ _, order_iso'.to_fun ⟩

lemma order_iso'.coe_eq_equiv_to_fun [preorder α] [preorder β] (f : order_iso' α β) :
  (f : α → β) = f.to_equiv.to_fun := rfl

lemma order_iso'.coe_monotone [partial_order α] [partial_order β] (f : order_iso' α β) :
  monotone f := by { unfold monotone, simp_rw [f.coe_eq_equiv_to_fun, f.le_iff_le], simp }

def order_iso'.inv_fun [preorder α] [preorder β] (f : order_iso' α β) : β → α := f.to_equiv.inv_fun

lemma order_iso'.monotone_inv_fun [partial_order α] [partial_order β] (f : order_iso' α β) :
  monotone f.inv_fun :=
begin
  unfold monotone, unfold order_iso'.inv_fun,
  intros, rw [← f.le_iff_le, f.to_equiv.right_inv, f.to_equiv.right_inv], apply a_1
end

variables [lattice α] [lattice β] {f : order_iso' α β}

lemma order_iso'.inf_map {a₁ a₂ : α} : f (a₁ ⊓ a₂) = f (a₁) ⊓ f (a₂) :=
begin
  apply lattice.le_antisymm,
  { apply lattice.le_inf; refine f.coe_monotone _, apply inf_le_left, apply inf_le_right },
  { rw ← f.to_equiv.right_inv f a₁ ⊓ f a₂, rw f.le_iff_le, },
end


end order_iso_lattice

/-
Copyright (c) 2019 Abhimanyu Pallavi Sudhir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhimanyu Pallavi Sudhir, Yury Kudryashov
-/
import order.filter.ultrafilter
import order.filter.germ

/-!
# Ultraproducts

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

If `φ` is an ultrafilter, then the space of germs of functions `f : α → β` at `φ` is called
the *ultraproduct*. In this file we prove properties of ultraproducts that rely on `φ` being an
ultrafilter. Definitions and properties that work for any filter should go to `order.filter.germ`.

## Tags

ultrafilter, ultraproduct
-/

universes u v
variables {α : Type u} {β : Type v} {φ : ultrafilter α}
open_locale classical

namespace filter

local notation `∀*` binders `, ` r:(scoped p, filter.eventually p φ) := r

namespace germ

open ultrafilter

local notation `β*` := germ (φ : filter α) β

instance [division_semiring β] : division_semiring β* :=
{ mul_inv_cancel := λ f, induction_on f $ λ f hf, coe_eq.2 $ (φ.em (λ y, f y = 0)).elim
    (λ H, (hf $ coe_eq.2 H).elim) (λ H, H.mono $ λ x, mul_inv_cancel),
  inv_zero := coe_eq.2 $ by simp only [(∘), inv_zero],
  ..germ.semiring, ..germ.div_inv_monoid, ..germ.nontrivial }

instance [division_ring β] : division_ring β* := { ..germ.ring, ..germ.division_semiring }
instance [semifield β] : semifield β* := { ..germ.comm_semiring, ..germ.division_semiring }
instance [field β] : field β* := { ..germ.comm_ring, ..germ.division_ring }

lemma coe_lt [preorder β] {f g : α → β} : (f : β*) < g ↔ ∀* x, f x < g x :=
by simp only [lt_iff_le_not_le, eventually_and, coe_le, eventually_not, eventually_le]

lemma coe_pos [preorder β] [has_zero β] {f : α → β} : 0 < (f : β*) ↔ ∀* x, 0 < f x := coe_lt

lemma const_lt [preorder β] {x y : β} : x < y → (↑x : β*) < ↑y := coe_lt.mpr ∘ lift_rel_const

@[simp, norm_cast]
lemma const_lt_iff [preorder β] {x y : β} : (↑x : β*) < ↑y ↔ x < y :=
coe_lt.trans lift_rel_const_iff

lemma lt_def [preorder β] : ((<) : β* → β* → Prop) = lift_rel (<) :=
by { ext ⟨f⟩ ⟨g⟩, exact coe_lt }

instance [has_sup β] : has_sup β* := ⟨map₂ (⊔)⟩
instance [has_inf β] : has_inf β* := ⟨map₂ (⊓)⟩

@[simp, norm_cast] lemma const_sup [has_sup β] (a b : β) : ↑(a ⊔ b) = (↑a ⊔ ↑b : β*) := rfl
@[simp, norm_cast] lemma const_inf [has_inf β] (a b : β) : ↑(a ⊓ b) = (↑a ⊓ ↑b : β*) := rfl

instance [semilattice_sup β] : semilattice_sup β* :=
{ sup := (⊔),
  le_sup_left := λ f g, induction_on₂ f g $ λ f g,
    eventually_of_forall $ λ x, le_sup_left,
  le_sup_right := λ f g, induction_on₂ f g $ λ f g,
    eventually_of_forall $ λ x, le_sup_right,
  sup_le := λ f₁ f₂ g, induction_on₃ f₁ f₂ g $ λ f₁ f₂ g h₁ h₂,
    h₂.mp $ h₁.mono $ λ x, sup_le,
  .. germ.partial_order }

instance [semilattice_inf β] : semilattice_inf β* :=
{ inf := (⊓),
  inf_le_left := λ f g, induction_on₂ f g $ λ f g,
    eventually_of_forall $ λ x, inf_le_left,
  inf_le_right := λ f g, induction_on₂ f g $ λ f g,
    eventually_of_forall $ λ x, inf_le_right,
  le_inf := λ f₁ f₂ g, induction_on₃ f₁ f₂ g $ λ f₁ f₂ g h₁ h₂,
    h₂.mp $ h₁.mono $ λ x, le_inf,
  .. germ.partial_order }

instance [lattice β] : lattice β* :=
{ .. germ.semilattice_sup, .. germ.semilattice_inf }

instance [distrib_lattice β] : distrib_lattice β* :=
{ le_sup_inf := λ f g h, induction_on₃ f g h $ λ f g h, eventually_of_forall $ λ _, le_sup_inf,
  .. germ.semilattice_sup, .. germ.semilattice_inf }

instance [has_le β] [is_total β (≤)] : is_total β* (≤) :=
⟨λ f g, induction_on₂ f g $ λ f g, eventually_or.1 $ eventually_of_forall $ λ x, total_of _ _ _⟩

/-- If `φ` is an ultrafilter then the ultraproduct is a linear order. -/
noncomputable instance [linear_order β] : linear_order β* := lattice.to_linear_order _

@[to_additive]
instance [ordered_comm_monoid β] : ordered_comm_monoid β* :=
{ mul_le_mul_left := λ f g, induction_on₂ f g $ λ f g H h, induction_on h $ λ h,
    H.mono $ λ x H, mul_le_mul_left' H _,
  .. germ.partial_order, .. germ.comm_monoid }

@[to_additive]
instance [ordered_cancel_comm_monoid β] : ordered_cancel_comm_monoid β* :=
{ le_of_mul_le_mul_left := λ f g h, induction_on₃ f g h $ λ f g h H,
    H.mono $ λ x, le_of_mul_le_mul_left',
  .. germ.partial_order, .. germ.ordered_comm_monoid }

@[to_additive]
instance [ordered_comm_group β] : ordered_comm_group β* :=
{ .. germ.ordered_cancel_comm_monoid, .. germ.comm_group }

@[to_additive]
noncomputable instance [linear_ordered_comm_group β] : linear_ordered_comm_group β* :=
{ .. germ.ordered_comm_group, .. germ.linear_order }

instance [ordered_semiring β] : ordered_semiring β* :=
{ zero_le_one := const_le zero_le_one,
  mul_le_mul_of_nonneg_left := λ x y z, induction_on₃ x y z $ λ f g h hfg hh, hh.mp $
    hfg.mono $ λ a, mul_le_mul_of_nonneg_left,
  mul_le_mul_of_nonneg_right := λ x y z, induction_on₃ x y z $ λ f g h hfg hh, hh.mp $
    hfg.mono $ λ a, mul_le_mul_of_nonneg_right,
  ..germ.semiring, ..germ.ordered_add_comm_monoid }

instance [ordered_comm_semiring β] : ordered_comm_semiring β* :=
{ ..germ.ordered_semiring, ..germ.comm_semiring }

instance [ordered_ring β] : ordered_ring β* :=
{ zero_le_one := const_le zero_le_one,
  mul_nonneg := λ x y, induction_on₂ x y $ λ f g hf hg, hg.mp $ hf.mono $ λ a, mul_nonneg,
  ..germ.ring, ..germ.ordered_add_comm_group }

instance [ordered_comm_ring β] : ordered_comm_ring β* :=
{ ..germ.ordered_ring, ..germ.ordered_comm_semiring }

instance [strict_ordered_semiring β] : strict_ordered_semiring β* :=
{ mul_lt_mul_of_pos_left := λ x y z, induction_on₃ x y z $ λ f g h hfg hh, coe_lt.2 $
   (coe_lt.1 hh).mp $ (coe_lt.1 hfg).mono $ λ a, mul_lt_mul_of_pos_left,
  mul_lt_mul_of_pos_right := λ x y z, induction_on₃ x y z $ λ f g h hfg hh, coe_lt.2 $
   (coe_lt.1 hh).mp $ (coe_lt.1 hfg).mono $ λ a, mul_lt_mul_of_pos_right,
  ..germ.ordered_semiring, ..germ.ordered_cancel_add_comm_monoid, ..germ.nontrivial }

instance [strict_ordered_comm_semiring β] : strict_ordered_comm_semiring β* :=
{ .. germ.strict_ordered_semiring, ..germ.ordered_comm_semiring }

instance [strict_ordered_ring β] : strict_ordered_ring β* :=
{ zero_le_one := const_le zero_le_one,
  mul_pos := λ x y, induction_on₂ x y $ λ f g hf hg, coe_pos.2 $
    (coe_pos.1 hg).mp $ (coe_pos.1 hf).mono $ λ x, mul_pos,
  ..germ.ring, ..germ.strict_ordered_semiring }

instance [strict_ordered_comm_ring β] : strict_ordered_comm_ring β* :=
{ .. germ.strict_ordered_ring, ..germ.ordered_comm_ring }

noncomputable instance [linear_ordered_ring β] : linear_ordered_ring β* :=
{ ..germ.strict_ordered_ring, ..germ.linear_order }

noncomputable instance [linear_ordered_field β] : linear_ordered_field β* :=
{ .. germ.linear_ordered_ring, .. germ.field }

noncomputable instance [linear_ordered_comm_ring β] : linear_ordered_comm_ring β* :=
{ .. germ.linear_ordered_ring, .. germ.comm_monoid }

lemma max_def [linear_order β] (x y : β*) : max x y = map₂ max x y :=
induction_on₂ x y $ λ a b,
begin
  cases le_total (a : β*) b,
  { rw [max_eq_right h, map₂_coe, coe_eq], exact h.mono (λ i hi, (max_eq_right hi).symm) },
  { rw [max_eq_left h, map₂_coe, coe_eq], exact h.mono (λ i hi, (max_eq_left hi).symm) }
end

lemma min_def [K : linear_order β] (x y : β*) : min x y = map₂ min x y :=
induction_on₂ x y $ λ a b,
begin
  cases le_total (a : β*) b,
  { rw [min_eq_left h, map₂_coe, coe_eq], exact h.mono (λ i hi, (min_eq_left hi).symm) },
  { rw [min_eq_right h, map₂_coe, coe_eq], exact h.mono (λ i hi, (min_eq_right hi).symm) }
end

lemma abs_def [linear_ordered_add_comm_group β] (x : β*) : |x| = map abs x :=
induction_on x $ λ a, by exact rfl

@[simp] lemma const_max [linear_order β] (x y : β) : (↑(max x y : β) : β*) = max ↑x ↑y :=
by rw [max_def, map₂_const]

@[simp] lemma const_min [linear_order β] (x y : β) : (↑(min x y : β) : β*) = min ↑x ↑y :=
by rw [min_def, map₂_const]

@[simp] lemma const_abs [linear_ordered_add_comm_group β] (x : β) :
  (↑(|x|) : β*) = |↑x| :=
by rw [abs_def, map_const]

end germ

end filter

/-
Copyright (c) 2019 Abhimanyu Pallavi Sudhir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhimanyu Pallavi Sudhir, Yury Kudryashov
-/
import order.filter.ultrafilter
import order.filter.germ

/-!
# Ultraproducts

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

/-- If `φ` is an ultrafilter then the ultraproduct is a division ring. -/
instance [division_ring β] : division_ring β* :=
{ mul_inv_cancel := λ f, induction_on f $ λ f hf, coe_eq.2 $ (φ.em (λ y, f y = 0)).elim
    (λ H, (hf $ coe_eq.2 H).elim) (λ H, H.mono $ λ x, mul_inv_cancel),
  inv_zero := coe_eq.2 $ by simp only [(∘), inv_zero],
  .. germ.ring, .. germ.div_inv_monoid, .. germ.nontrivial }

/-- If `φ` is an ultrafilter then the ultraproduct is a field. -/
instance [field β] : field β* :=
{ .. germ.comm_ring, .. germ.division_ring }

/-- If `φ` is an ultrafilter then the ultraproduct is a linear order. -/
noncomputable instance [linear_order β] : linear_order β* :=
{ le_total := λ f g, induction_on₂ f g $ λ f g, eventually_or.1 $ eventually_of_forall $
    λ x, le_total _ _,
  decidable_le := by apply_instance,
  .. germ.partial_order }

@[simp, norm_cast] lemma const_div [division_ring β] (x y : β) : (↑(x / y) : β*) = ↑x / ↑y := rfl

lemma coe_lt [preorder β] {f g : α → β} : (f : β*) < g ↔ ∀* x, f x < g x :=
by simp only [lt_iff_le_not_le, eventually_and, coe_le, eventually_not, eventually_le]

lemma coe_pos [preorder β] [has_zero β] {f : α → β} : 0 < (f : β*) ↔ ∀* x, 0 < f x :=
coe_lt

lemma const_lt [preorder β] {x y : β} : (↑x : β*) < ↑y ↔ x < y :=
coe_lt.trans lift_rel_const_iff

lemma lt_def [preorder β] : ((<) : β* → β* → Prop) = lift_rel (<) :=
by { ext ⟨f⟩ ⟨g⟩, exact coe_lt }

/-- If `φ` is an ultrafilter then the ultraproduct is an ordered ring. -/
instance [ordered_ring β] : ordered_ring β* :=
{ zero_le_one := const_le zero_le_one,
  mul_pos := λ x y, induction_on₂ x y $ λ f g hf hg, coe_pos.2 $
    (coe_pos.1 hg).mp $ (coe_pos.1 hf).mono $ λ x, mul_pos,
  .. germ.ring, .. germ.ordered_add_comm_group, .. germ.nontrivial }

/-- If `φ` is an ultrafilter then the ultraproduct is a linear ordered ring. -/
noncomputable instance [linear_ordered_ring β] : linear_ordered_ring β* :=
{ .. germ.ordered_ring, .. germ.linear_order, .. germ.nontrivial }

/-- If `φ` is an ultrafilter then the ultraproduct is a linear ordered field. -/
noncomputable instance [linear_ordered_field β] : linear_ordered_field β* :=
{ .. germ.linear_ordered_ring, .. germ.field }

/-- If `φ` is an ultrafilter then the ultraproduct is a linear ordered commutative ring. -/
noncomputable instance [linear_ordered_comm_ring β] :
  linear_ordered_comm_ring β* :=
{ .. germ.linear_ordered_ring, .. germ.comm_monoid }

/-- If `φ` is an ultrafilter then the ultraproduct is a decidable linear ordered commutative
group. -/
noncomputable instance [linear_ordered_add_comm_group β] : linear_ordered_add_comm_group β* :=
{ .. germ.ordered_add_comm_group, .. germ.linear_order }

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

lemma lattice_of_linear_order_eq_filter_germ_lattice [linear_order β] :
  (@lattice_of_linear_order (filter.germ ↑φ β) filter.germ.linear_order) = filter.germ.lattice :=
lattice.ext (λ x y, iff.rfl)

end germ

end filter

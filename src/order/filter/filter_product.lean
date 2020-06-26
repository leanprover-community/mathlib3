/-
Copyright (c) 2019 Abhimanyu Pallavi Sudhir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhimanyu Pallavi Sudhir
-/
import order.filter.ultrafilter
import order.filter.germ
import algebra.pi_instances

/-!
# Ultraproducts

If `φ` is an ultrafilter, then the space of germs of functions `f : α → β` at `φ` is called
the *ultraproduct*. In this file we prove properties of ultraproducts that rely on `φ` being an
ultrafilter. Definitions and properties that work for any filter should go to `order.filter.germ`.

## Tags

ultrafilter, ultraproduct
-/

universes u v
variables {α : Type u} {β : Type v} {φ : filter α}
open_locale classical

namespace filter

local notation `∀*` binders `, ` r:(scoped p, filter.eventually p φ) := r

namespace germ

local notation `β*` := germ φ β

/-- If `φ` is an ultrafilter then the ultraproduct is a division ring.
This cannot be an instance, since it depends on `φ` being an ultrafilter. -/
protected def division_ring [division_ring β] (U : is_ultrafilter φ) : division_ring β* :=
{ mul_inv_cancel := λ f, induction_on f $ λ f hf, coe_eq.2 $ (U.em (λ y, f y = 0)).elim
    (λ H, (hf $ coe_eq.2 H).elim) (λ H, H.mono $ λ x, mul_inv_cancel),
  inv_mul_cancel := λ f, induction_on f $ λ f hf, coe_eq.2 $ (U.em (λ y, f y = 0)).elim
    (λ H, (hf $ coe_eq.2 H).elim) (λ H, H.mono $ λ x, inv_mul_cancel),
  inv_zero := coe_eq.2 $ by simp only [(∘), inv_zero],
  .. germ.ring, .. germ.has_inv, .. germ.nonzero U.1 }

/-- If `φ` is an ultrafilter then the ultraproduct is a field.
This cannot be an instance, since it depends on `φ` being an ultrafilter. -/
protected def field [field β] (U : is_ultrafilter φ) : field β* :=
{ .. germ.comm_ring, .. germ.division_ring U }

/-- If `φ` is an ultrafilter then the ultraproduct is a linear order.
This cannot be an instance, since it depends on `φ` being an ultrafilter. -/
protected def linear_order [linear_order β] (U : is_ultrafilter φ) : linear_order β* :=
{ le_total := λ f g, induction_on₂ f g $ λ f g, U.eventually_or.1 $ eventually_of_forall _ $
    λ x, le_total _ _,
  .. germ.partial_order }

@[simp, norm_cast] lemma const_div [division_ring β] (U : is_ultrafilter φ) (x y : β) :
  (↑(x / y) : β*) = @has_div.div _ (@division_ring_has_div _ (germ.division_ring U)) ↑x ↑y :=
rfl

lemma coe_lt [preorder β] (U : is_ultrafilter φ) {f g : α → β} :
  (f : β*) < g ↔ ∀* x, f x < g x :=
by simp only [lt_iff_le_not_le, eventually_and, coe_le, U.eventually_not, eventually_le]

lemma coe_pos [preorder β] [has_zero β] (U : is_ultrafilter φ) {f : α → β} :
  0 < (f : β*) ↔ ∀* x, 0 < f x :=
coe_lt U

lemma const_lt [preorder β] (U : is_ultrafilter φ) {x y : β} :
  (↑x : β*) < ↑y ↔ x < y :=
(coe_lt U).trans $ lift_rel_const_iff U.1

lemma lt_def [preorder β] (U : is_ultrafilter φ) :
  ((<) : β* → β* → Prop) = lift_rel (<) :=
by { ext ⟨f⟩ ⟨g⟩, exact coe_lt U }

/-- If `φ` is an ultrafilter then the ultraproduct is an ordered ring.
This cannot be an instance, since it depends on `φ` being an ultrafilter. -/
protected def ordered_ring [ordered_ring β] (U : is_ultrafilter φ) : ordered_ring β* :=
{ mul_pos := λ x y, induction_on₂ x y $ λ f g hf hg, (coe_pos U).2 $
    ((coe_pos U).1 hg).mp $ ((coe_pos U).1 hf).mono $ λ x, mul_pos,
  .. germ.ring, .. germ.ordered_add_comm_group,
  .. germ.nonzero U.1 }

/-- If `φ` is an ultrafilter then the ultraproduct is a linear ordered ring.
This cannot be an instance, since it depends on `φ` being an ultrafilter. -/
protected def linear_ordered_ring [linear_ordered_ring β] (U : is_ultrafilter φ) :
  linear_ordered_ring β* :=
{ zero_lt_one := by rw lt_def U; show (∀* i, (0 : β) < 1); simp [zero_lt_one],
  .. germ.ordered_ring U, .. germ.linear_order U }

/-- If `φ` is an ultrafilter then the ultraproduct is a linear ordered field.
This cannot be an instance, since it depends on `φ` being an ultrafilter. -/
protected def linear_ordered_field [linear_ordered_field β] (U : is_ultrafilter φ) :
  linear_ordered_field β* :=
{ .. germ.linear_ordered_ring U, .. germ.field U }

/-- If `φ` is an ultrafilter then the ultraproduct is a linear ordered commutative ring.
This cannot be an instance, since it depends on `φ` being an ultrafilter. -/
protected def linear_ordered_comm_ring [linear_ordered_comm_ring β] (U : is_ultrafilter φ) :
  linear_ordered_comm_ring β* :=
{ .. germ.linear_ordered_ring U, .. germ.comm_monoid }

/-- If `φ` is an ultrafilter then the ultraproduct is a decidable linear order.
This cannot be an instance, since it depends on `φ` being an ultrafilter. -/
protected noncomputable def decidable_linear_order [decidable_linear_order β]
  (U : is_ultrafilter φ) :
  decidable_linear_order β* :=
{ decidable_le := by apply_instance,
  .. germ.linear_order U }

/-- If `φ` is an ultrafilter then the ultraproduct is a decidable linear ordered commutative group.
This cannot be an instance, since it depends on `φ` being an ultrafilter. -/
protected noncomputable def decidable_linear_ordered_add_comm_group
  [decidable_linear_ordered_add_comm_group β] (U : is_ultrafilter φ) :
  decidable_linear_ordered_add_comm_group β* :=
{ .. germ.ordered_add_comm_group, .. germ.decidable_linear_order U }

/-- If `φ` is an ultrafilter then the ultraproduct is a decidable linear ordered commutative ring.
This cannot be an instance, since it depends on `φ` being an ultrafilter. -/
protected noncomputable def decidable_linear_ordered_comm_ring
  [decidable_linear_ordered_comm_ring β] (U : is_ultrafilter φ) :
  decidable_linear_ordered_comm_ring β* :=
{ .. germ.linear_ordered_comm_ring U,
  .. germ.decidable_linear_ordered_add_comm_group U }

/-- If `φ` is an ultrafilter then the ultraproduct is a discrete linear ordered field.
This cannot be an instance, since it depends on `φ` being an ultrafilter. -/
protected noncomputable def discrete_linear_ordered_field [discrete_linear_ordered_field β]
  (U : is_ultrafilter φ) : discrete_linear_ordered_field β* :=
{ .. germ.linear_ordered_field U, .. germ.decidable_linear_ordered_comm_ring U,
  .. germ.field U }

lemma max_def [K : decidable_linear_order β] (U : is_ultrafilter φ) (x y : β*) :
  @max β* (germ.decidable_linear_order U) x y = map₂ max x y :=
quotient.induction_on₂' x y $ λ a b, by unfold max;
begin
  split_ifs,
  exact quotient.sound'(by filter_upwards [h] λ i hi, (max_eq_right hi).symm),
  exact quotient.sound'(by filter_upwards [@le_of_not_le _ (germ.linear_order U) _ _ h]
    λ i hi, (max_eq_left hi).symm),
end

lemma min_def [K : decidable_linear_order β] (U : is_ultrafilter φ) (x y : β*) :
  @min β* (germ.decidable_linear_order U) x y = map₂ min x y :=
quotient.induction_on₂' x y $ λ a b, by unfold min;
begin
  split_ifs,
  exact quotient.sound'(by filter_upwards [h] λ i hi, (min_eq_left hi).symm),
  exact quotient.sound'(by filter_upwards [@le_of_not_le _ (germ.linear_order U) _ _ h]
    λ i hi, (min_eq_right hi).symm),
end

lemma abs_def [decidable_linear_ordered_add_comm_group β] (U : is_ultrafilter φ) (x : β*) :
  @abs _ (germ.decidable_linear_ordered_add_comm_group U) x = map abs x :=
quotient.induction_on' x $ λ a, by unfold abs; rw max_def;
exact quotient.sound' (show ∀* i, abs _ = _, by simp)

@[simp] lemma const_max [decidable_linear_order β] (U : is_ultrafilter φ) (x y : β) :
  (↑(max x y : β) : β*) = @max _ (germ.decidable_linear_order U) ↑x ↑y :=
begin
  unfold max, split_ifs,
  { refl },
  { exact false.elim (h_1 $ const_le h) },
  { exact false.elim (h ((const_le_iff U.1).mp h_1)) },
  { refl }
end

@[simp] lemma const_min [decidable_linear_order β] (U : is_ultrafilter φ) (x y : β) :
  (↑(min x y : β) : β*) = @min _ (germ.decidable_linear_order U) ↑x ↑y :=
begin
  unfold min, split_ifs; try { refl }; apply false.elim,
  { exact  (h_1 $ const_le h) },
  { exact (h $ (const_le_iff U.1).mp h_1) },
end

@[simp] lemma const_abs [decidable_linear_ordered_add_comm_group β] (U : is_ultrafilter φ) (x : β) :
  (↑(abs x) : β*) = @abs _ (germ.decidable_linear_ordered_add_comm_group U) ↑x :=
const_max U x (-x)

end germ

end filter

import tactic
import data.real.basic
import algebra.ordered_ring
import algebra.ordered_field
import algebra.linear_ordered_comm_group_with_zero

import data.nat.basic
import order.bounded_lattice

universe u

variables (R : Type*) [linear_order R]

lemma a :
  @lattice.to_semilattice_inf _ (@lattice_of_linear_order (with_top R) with_top.linear_order) =
  @semilattice_inf_top.to_semilattice_inf (with_top R) with_top.semilattice_inf :=
rfl
local attribute [-instance] semilattice_inf_top.to_semilattice_inf
local attribute [-instance] with_top.lattice
lemma b :
  @semilattice_inf_top.to_semilattice_inf (with_top R) with_top.semilattice_inf =
  -- @lattice.to_semilattice_inf _ (@lattice_of_linear_order (with_top R) with_top.linear_order) =
  (by apply_instance) := by refl

set_option pp.all true
lemma ok :
  nat.decidable_eq = @decidable_eq_of_decidable_le ℕ (by apply_instance) (by apply_instance) :=
by refl --fails
#print ok
lemma ok2 :
@sub_neg_monoid.to_has_neg ℝ (
@add_group.to_sub_neg_monoid ℝ (
@add_comm_group.to_add_group ℝ (
(@ordered_add_comm_group.to_add_comm_group ℝ (
@ordered_ring.to_ordered_add_comm_group ℝ (--to_add_group.to_sub_neg_monoid.to_has_neg
@linear_ordered_ring.to_ordered_ring ℝ
real.linear_ordered_ring))))))
= real.has_neg
:= by refl

local attribute [-instance] nat.decidable_eq
local attribute [-instance] nat.linear_order
local attribute [-instance] nat.canonically_linear_ordered_add_monoid
local attribute [-instance] nat.linear_ordered_comm_monoid_with_zero
-- local attribute [-instance] nat.linear_ordered_semiring
-- local attribute [-instance] linear_ordered_cancel_add_comm_monoid.to_linear_ordered_add_comm_monoid
local attribute [-instance] nat.linear_ordered_cancel_add_comm_monoid
local attribute [-instance] linear_ordered_add_comm_monoid.to_linear_order
local attribute [-instance] linear_ordered_comm_monoid.to_linear_order
example :
  nat.decidable_eq = @decidable_eq_of_decidable_le ℕ (by apply_instance) (by apply_instance) :=
by refl --fails

-- how to make this a linter?

open tactic
run_cmd (do is_def_eq `(nat.decidable_eq) `(nat.decidable_eq) >> trace "hi")
run_cmd (do is_def_eq `(nat.decidable_eq) `(@decidable_eq_of_decidable_le ℕ (by apply_instance) (by apply_instance)) >> trace "hi")
run_cmd (do instances)
run_cmd (do set_attribute `)

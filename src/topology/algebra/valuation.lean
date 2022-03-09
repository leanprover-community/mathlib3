/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/

import topology.algebra.nonarchimedean.bases
import topology.algebra.uniform_filter_basis
import ring_theory.valuation.basic

/-!
# The topology on a valued ring

In this file, we define the non archimedean topology induced by a valuation on a ring.
The main definition is a `valued` type class which equips a ring with a valuation taking
values in a group with zero. Other instances are then deduced from this.
-/

open_locale classical topological_space
open set valuation
noncomputable theory

universes v u

/-- A valued ring is a ring that comes equipped with a distinguished valuation. The class `valued`
is designed for the situation that there is a canonical valuation on the ring. It allows such a
valuation to be registered as a typeclass; this is used for instance by `valued.topological_space`.

TODO: show that there always exists an equivalent valuation taking values in a type belonging to
the same universe as the ring. -/
class valued (R : Type u) [ring R] (Γ₀ : out_param (Type v))
  [linear_ordered_comm_group_with_zero Γ₀] :=
(v : valuation R Γ₀)

namespace valued
variables {R : Type u} [ring R] (Γ₀ : Type v) [linear_ordered_comm_group_with_zero Γ₀]
  [hv : valued R Γ₀]

include hv

/-- The basis of open subgroups for the topology on a valued ring.-/
lemma subgroups_basis :
  ring_subgroups_basis (λ γ : Γ₀ˣ, (valued.v.lt_add_subgroup γ : add_subgroup R)) :=
{ inter := begin
    rintros γ₀ γ₁,
    use min γ₀ γ₁,
    simp [valuation.lt_add_subgroup] ; tauto
  end,
  mul := begin
    rintros γ,
    cases exists_square_le γ with γ₀ h,
    use γ₀,
    rintro - ⟨r, s, r_in, s_in, rfl⟩,
    calc (v (r*s) : Γ₀) = v r * v s : valuation.map_mul _ _ _
             ... < γ₀*γ₀ : mul_lt_mul₀ r_in s_in
             ... ≤ γ : by exact_mod_cast h
  end,
  left_mul := begin
    rintros x γ,
    rcases group_with_zero.eq_zero_or_unit (v x) with Hx | ⟨γx, Hx⟩,
    { use (1 : Γ₀ˣ),
      rintros y (y_in : (v y : Γ₀) < 1),
      change v (x * y) < _,
      rw [valuation.map_mul, Hx, zero_mul],
      exact units.zero_lt γ },
    { simp only [image_subset_iff, set_of_subset_set_of, preimage_set_of_eq, valuation.map_mul],
      use γx⁻¹*γ,
      rintros y (vy_lt : v y < ↑(γx⁻¹ * γ)),
      change (v (x * y) : Γ₀) < γ,
      rw [valuation.map_mul, Hx, mul_comm],
      rw [units.coe_mul, mul_comm] at vy_lt,
      simpa using mul_inv_lt_of_lt_mul₀ vy_lt }
  end,
  right_mul := begin
    rintros x γ,
    rcases group_with_zero.eq_zero_or_unit (v x) with Hx | ⟨γx, Hx⟩,
    { use 1,
      rintros y (y_in : (v y : Γ₀) < 1),
      change v (y * x) < _,
      rw [valuation.map_mul, Hx, mul_zero],
      exact units.zero_lt γ },
    { use γx⁻¹*γ,
      rintros y (vy_lt : v y < ↑(γx⁻¹ * γ)),
      change (v (y * x) : Γ₀) < γ,
      rw [valuation.map_mul, Hx],
      rw [units.coe_mul, mul_comm] at vy_lt,
      simpa using mul_inv_lt_of_lt_mul₀ vy_lt }
  end }

/-- The topological space structure on a valued ring.

NOTE: The `dangerous_instance` linter does not check whether the metavariables only occur in
arguments marked with `out_param`, so in this instance it gives a false positive. -/
@[nolint dangerous_instance, priority 100]
instance : topological_space R := (subgroups_basis Γ₀).topology

variable {Γ₀}

lemma mem_nhds {s : set R} {x : R} :
  (s ∈ 𝓝 x) ↔ ∃ (γ : Γ₀ˣ), {y | (v (y - x) : Γ₀) < γ } ⊆ s :=
by simpa [((subgroups_basis Γ₀).has_basis_nhds x).mem_iff]

lemma mem_nhds_zero {s : set R} :
  (s ∈ 𝓝 (0 : R)) ↔ ∃ γ : Γ₀ˣ, {x | v x < (γ : Γ₀) } ⊆ s :=
by simp [valued.mem_nhds, sub_zero]

lemma loc_const {x : R} (h : (v x : Γ₀) ≠ 0) : {y : R | v y = v x} ∈ 𝓝 x :=
begin
  rw valued.mem_nhds,
  rcases units.exists_iff_ne_zero.mpr h with ⟨γ, hx⟩,
  use γ,
  rw hx,
  intros y y_in,
  exact valuation.map_eq_of_sub_lt _ y_in
end

/-- The uniform structure on a valued ring.

NOTE: The `dangerous_instance` linter does not check whether the metavariables only occur in
arguments marked with `out_param`, so in this instance it gives a false positive.-/
@[nolint dangerous_instance, priority 100]
instance uniform_space : uniform_space R := topological_add_group.to_uniform_space R

/-- A valued ring is a uniform additive group.-/
@[priority 100]
instance uniform_add_group : uniform_add_group R := topological_add_group_is_uniform

lemma cauchy_iff {F : filter R} :
  cauchy F ↔ F.ne_bot ∧ ∀ γ : Γ₀ˣ, ∃ M ∈ F, ∀ x y ∈ M, (v (y - x) : Γ₀) < γ :=
begin
  rw add_group_filter_basis.cauchy_iff,
  apply and_congr iff.rfl,
  simp_rw (subgroups_basis Γ₀).mem_add_group_filter_basis_iff,
  split,
  { intros h γ,
    exact h _ ((subgroups_basis Γ₀).mem_add_group_filter_basis _) },
  { rintros h - ⟨γ, rfl⟩,
    exact h γ }
end
end valued

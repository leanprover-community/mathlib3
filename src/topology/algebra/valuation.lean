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
values in a group with zero (living in the same universe). Other instances are then deduced from
this.
-/

open_locale classical topological_space
open set valuation
noncomputable theory

universe u

/-- A valued ring is a ring that comes equipped with a distinguished valuation.-/
class valued (R : Type u) [ring R] :=
(Γ₀ : Type u)
[grp : linear_ordered_comm_group_with_zero Γ₀]
(v : valuation R Γ₀)

attribute [instance] valued.grp

namespace valued
variables {R : Type*} [ring R] [valued R]

/-- The basis of open subgroups for the topology on a valued ring.-/
lemma subgroups_basis : ring_subgroups_basis (λ γ : units (Γ₀ R), valued.v.lt_add_subgroup γ) :=
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
    calc v (r*s) = v r * v s : valuation.map_mul _ _ _
             ... < γ₀*γ₀ : mul_lt_mul₀ r_in s_in
             ... ≤ γ : by exact_mod_cast h
  end,
  left_mul := begin
    rintros x γ,
    rcases group_with_zero.eq_zero_or_unit (v x) with Hx | ⟨γx, Hx⟩,
    { use 1,
      rintros y (y_in : v y < 1),
      change v (x * y) < _,
      rw [valuation.map_mul, Hx, zero_mul],
      exact units.zero_lt γ },
    { simp only [image_subset_iff, set_of_subset_set_of, preimage_set_of_eq, valuation.map_mul],
      use γx⁻¹*γ,
      rintros y (vy_lt : v y < ↑(γx⁻¹ * γ)),
      change v (x * y) < γ,
      rw [valuation.map_mul, Hx, mul_comm],
      rw [units.coe_mul, mul_comm] at vy_lt,
      simpa using mul_inv_lt_of_lt_mul₀ vy_lt }
  end,
  right_mul := begin
    rintros x γ,
    rcases group_with_zero.eq_zero_or_unit (v x) with Hx | ⟨γx, Hx⟩,
    { use 1,
      rintros y (y_in : v y < 1),
      change v (y * x) < _,
      rw [valuation.map_mul, Hx, mul_zero],
      exact units.zero_lt γ },
    { use γx⁻¹*γ,
      rintros y (vy_lt : v y < ↑(γx⁻¹ * γ)),
      change v (y * x) < γ,
      rw [valuation.map_mul, Hx],
      rw [units.coe_mul, mul_comm] at vy_lt,
      simpa using mul_inv_lt_of_lt_mul₀ vy_lt }
  end }

@[priority 100]
instance : topological_space R := subgroups_basis.topology

lemma mem_nhds {s : set R} {x : R} :
  (s ∈ 𝓝 x) ↔ ∃ γ : units (valued.Γ₀ R), {y | v (y - x) < γ } ⊆ s :=
by simpa [(subgroups_basis.has_basis_nhds x).mem_iff]

lemma mem_nhds_zero {s : set R} :
  (s ∈ 𝓝 (0 : R)) ↔ ∃ γ : units (Γ₀ R), {x | v x < (γ : Γ₀ R) } ⊆ s :=
by simp [valued.mem_nhds, sub_zero]

lemma loc_const {x : R} (h : v x ≠ 0) : {y : R | v y = v x} ∈ 𝓝 x :=
begin
  rw valued.mem_nhds,
  rcases units.exists_iff_ne_zero.mpr h with ⟨γ, hx⟩,
  use γ,
  rw hx,
  intros y y_in,
  exact valuation.map_eq_of_sub_lt _ y_in
end

/-- The uniform structure on a valued ring.-/
@[priority 100]
instance uniform_space : uniform_space R := topological_add_group.to_uniform_space R

/-- A valued ring is a uniform additive group.-/
@[priority 100]
instance uniform_add_group : uniform_add_group R := topological_add_group_is_uniform

lemma cauchy_iff {F : filter R} :
  cauchy F ↔ F.ne_bot ∧ ∀ γ : units (Γ₀ R), ∃ M ∈ F, ∀ x y, x ∈ M → y ∈ M → v (y - x) < γ :=
begin
    rw add_group_filter_basis.cauchy_iff,
    apply and_congr iff.rfl,
    simp_rw subgroups_basis.mem_add_group_filter_basis_iff,
    split,
    { intros h γ,
      exact h _ (subgroups_basis.mem_add_group_filter_basis _) },
    { rintros h - ⟨γ, rfl⟩,
      exact h γ }
end
end valued

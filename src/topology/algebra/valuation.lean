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

open_locale classical topological_space uniformity
open set valuation
noncomputable theory

universes v u

variables {R : Type u} [ring R] {Γ₀ : Type v} [linear_ordered_comm_group_with_zero Γ₀]

namespace valuation

variables (v : valuation R Γ₀)

/-- The basis of open subgroups for the topology on a ring determined by a valuation. -/
lemma subgroups_basis :
  ring_subgroups_basis (λ γ : Γ₀ˣ, (v.lt_add_subgroup γ : add_subgroup R)) :=
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

end valuation

/-- A valued ring is a ring that comes equipped with a distinguished valuation. The class `valued`
is designed for the situation that there is a canonical valuation on the ring.

TODO: show that there always exists an equivalent valuation taking values in a type belonging to
the same universe as the ring.

See Note [forgetful inheritance] for why we extend `uniform_space`. -/
class valued (R : Type u) [ring R] (Γ₀ : out_param (Type v))
  [linear_ordered_comm_group_with_zero Γ₀] extends uniform_space R :=
(v : valuation R Γ₀)
-- On second thought perhaps `is_uniform_valuation` would be better replaced with a topological
-- condition characterising the neighbourhoods of (0 : R).
(is_uniform_valuation : ∀ s, s ∈ 𝓤 R ↔ ∃ (γ : Γ₀ˣ), { p : R × R | v (p.2 - p.1) < γ } ⊆ s)

/-- The `dangerous_instance` linter does not check whether the metavariables only occur in
arguments marked with `out_param`, so in this instance it gives a false positive.-/
attribute [nolint dangerous_instance] valued.to_uniform_space

namespace valued

/-- Alternative `valued` constructor for use when there is no preferred `uniform_space`
structure. -/
def mk' (v : valuation R Γ₀) : valued R Γ₀ :=
{ v := v,
  to_uniform_space := @topological_add_group.to_uniform_space R _ v.subgroups_basis.topology _,
  is_uniform_valuation :=
  begin
    letI := @topological_add_group.to_uniform_space R _ v.subgroups_basis.topology _,
    intros s,
    suffices : (𝓤 R).has_basis (λ _, true) (λ (γ : Γ₀ˣ), { p : R × R | v (p.2 - p.1) < (γ : Γ₀) }),
    { rw this.mem_iff,
      exact exists_congr (λ γ, by simp), },
    exact v.subgroups_basis.has_basis_nhds_zero.comap _,
  end }

variables (R Γ₀) [_i : valued R Γ₀]
include _i

lemma has_basis_uniformity :
  (𝓤 R).has_basis (λ _, true) (λ (γ : Γ₀ˣ), { p : R × R | v (p.2 - p.1) < (γ : Γ₀) }) :=
by simp [filter.has_basis_iff, is_uniform_valuation]

lemma uniformity_eq :
  𝓤 R = (@topological_add_group.to_uniform_space R _ v.subgroups_basis.topology _).uniformity :=
(has_basis_uniformity R Γ₀).eq_of_same_basis $ v.subgroups_basis.has_basis_nhds_zero.comap _

lemma to_uniform_space_eq :
  to_uniform_space = @topological_add_group.to_uniform_space R _ v.subgroups_basis.topology _ :=
uniform_space_eq (uniformity_eq R Γ₀)

lemma to_topological_space_eq :
  (by apply_instance : topological_space R) = v.subgroups_basis.topology :=
begin
  rw to_uniform_space_eq,
  congr,
end

lemma has_basis_nhds_zero :
  (𝓝 (0 : R)).has_basis (λ _, true) (λ (γ : Γ₀ˣ), { x | v x < (γ : Γ₀) }) :=
begin
  rw to_topological_space_eq,
  exact v.subgroups_basis.has_basis_nhds_zero,
end

variables {R Γ₀}

lemma mem_nhds {s : set R} {x : R} :
  (s ∈ 𝓝 x) ↔ ∃ (γ : Γ₀ˣ), {y | (v (y - x) : Γ₀) < γ } ⊆ s :=
begin
  rw to_topological_space_eq,
  simpa [(v.subgroups_basis.has_basis_nhds x).mem_iff],
end

lemma mem_nhds_zero {s : set R} :
  (s ∈ 𝓝 (0 : R)) ↔ ∃ γ : Γ₀ˣ, {x | v x < (γ : Γ₀) } ⊆ s :=
by simp [mem_nhds, sub_zero]

lemma loc_const {x : R} (h : (v x : Γ₀) ≠ 0) : {y : R | v y = v x} ∈ 𝓝 x :=
begin
  rw mem_nhds,
  rcases units.exists_iff_ne_zero.mpr h with ⟨γ, hx⟩,
  use γ,
  rw hx,
  intros y y_in,
  exact valuation.map_eq_of_sub_lt _ y_in
end

@[priority 100]
instance to_uniform_add_group : uniform_add_group R :=
(to_uniform_space_eq R Γ₀).symm ▸ @topological_add_group_is_uniform _ _ v.subgroups_basis.topology _

@[priority 100]
instance : topological_ring R :=
(to_uniform_space_eq R Γ₀).symm ▸ v.subgroups_basis.to_ring_filter_basis.is_topological_ring

lemma cauchy_iff {F : filter R} :
  cauchy F ↔ F.ne_bot ∧ ∀ γ : Γ₀ˣ, ∃ M ∈ F, ∀ x y ∈ M, (v (y - x) : Γ₀) < γ :=
begin
  rw [to_uniform_space_eq, add_group_filter_basis.cauchy_iff],
  apply and_congr iff.rfl,
  simp_rw valued.v.subgroups_basis.mem_add_group_filter_basis_iff,
  split,
  { intros h γ,
    exact h _ (valued.v.subgroups_basis.mem_add_group_filter_basis _) },
  { rintros h - ⟨γ, rfl⟩,
    exact h γ }
end

lemma separated_of_zero_sep
  (H : ∀ x : R, x ≠ 0 → ∃ U ∈ 𝓝 (0 : R), x ∉ U) : separated_space R :=
begin
  -- TODO Tidy up this proof: looks like missing fact about uniform add group structure
  rw to_uniform_space_eq,
  convert topological_add_group.separated_of_zero_sep H,
  rw to_topological_space_eq,
end

end valued

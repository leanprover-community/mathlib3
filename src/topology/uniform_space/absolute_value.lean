/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import algebra.absolute_value
import topology.uniform_space.basic

/-!
# Uniform structure induced by an absolute value

We build a uniform space structure on a commutative ring `R` equipped with an absolute value into
a linear ordered field `𝕜`. Of course in the case `R` is `ℚ`, `ℝ` or `ℂ` and
`𝕜 = ℝ`, we get the same thing as the metric space construction, and the general construction
follows exactly the same path.

## Implementation details

Note that we import `data.real.cau_seq` because this is where absolute values are defined, but
the current file does not depend on real numbers. TODO: extract absolute values from that
`data.real` folder.

## References

* [N. Bourbaki, *Topologie générale*][bourbaki1966]

## Tags

absolute value, uniform spaces
-/

open set function filter uniform_space
open_locale filter

namespace is_absolute_value
variables {𝕜 : Type*} [linear_ordered_field 𝕜]
variables {R : Type*} [comm_ring R] (abv : R → 𝕜) [is_absolute_value abv]

/-- The uniformity coming from an absolute value. -/
def uniform_space_core : uniform_space.core R :=
{ uniformity := (⨅ ε>0, 𝓟 {p:R×R | abv (p.2 - p.1) < ε}),
  refl := le_infi $ assume ε, le_infi $ assume ε_pos, principal_mono.2
    (λ ⟨x, y⟩ h, by simpa [show x = y, from h, abv_zero abv]),
  symm := tendsto_infi.2 $ assume ε, tendsto_infi.2 $ assume h,
    tendsto_infi' ε $ tendsto_infi' h $ tendsto_principal_principal.2 $ λ ⟨x, y⟩ h,
      have h : abv (y - x) < ε, by simpa [-sub_eq_add_neg] using h,
      by rwa abv_sub abv at h,
  comp := le_infi $ assume ε, le_infi $ assume h, lift'_le
    (mem_infi_of_mem (ε / 2) $ mem_infi_of_mem (div_pos h zero_lt_two) (subset.refl _)) $
    have ∀ (a b c : R), abv (c-a) < ε / 2 → abv (b-c) < ε / 2 → abv (b-a) < ε,
      from assume a b c hac hcb,
       calc abv (b - a) ≤ _ : abv_sub_le abv b c a
        ... = abv (c - a) + abv (b - c) : add_comm _ _
        ... < ε / 2 + ε / 2 : add_lt_add hac hcb
        ... = ε : by rw [div_add_div_same, add_self_div_two],
    by simpa [comp_rel] }

/-- The uniform structure coming from an absolute value. -/
def uniform_space : uniform_space R :=
uniform_space.of_core (uniform_space_core abv)

theorem mem_uniformity {s : set (R×R)} :
  s ∈ (uniform_space_core abv).uniformity ↔
  (∃ε>0, ∀{a b:R}, abv (b - a) < ε → (a, b) ∈ s) :=
begin
  suffices : s ∈ (⨅ ε: {ε : 𝕜 // ε > 0}, 𝓟 {p:R×R | abv (p.2 - p.1) < ε.val}) ↔ _,
  { rw infi_subtype at this,
    exact this },
  rw mem_infi_of_directed,
  { simp [subset_def] },
  { rintros ⟨r, hr⟩ ⟨p, hp⟩,
    exact ⟨⟨min r p, lt_min hr hp⟩, by simp [lt_min_iff, (≥)] {contextual := tt}⟩, },
end

end is_absolute_value

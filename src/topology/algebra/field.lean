/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison
-/
import topology.algebra.ring
import topology.algebra.group_with_zero

/-!
# Topological fields

A topological division ring is a topological ring whose inversion function is continuous at every
non-zero element.

-/


namespace topological_ring
open topological_space function
variables (R : Type*) [ring R]

variables  [topological_space R]

/-- The induced topology on units of a topological ring.
This is not a global instance since other topologies could be relevant. Instead there is a class
`induced_units` asserting that something equivalent to this construction holds. -/
def topological_space_units : topological_space (units R) := induced (coe : units R → R) ‹_›

/-- Asserts the topology on units is the induced topology.

 Note: this is not always the correct topology.
 Another good candidate is the subspace topology of $R \times R$,
 with the units embedded via $u \mapsto (u, u^{-1})$.
 These topologies are not (propositionally) equal in general. -/
class induced_units [t : topological_space $ units R] : Prop :=
(top_eq : t = induced (coe : units R → R) ‹_›)

variables [topological_space $ units R]

lemma units_topology_eq [induced_units R] :
  ‹topological_space (units R)› = induced (coe : units R → R) ‹_› :=
induced_units.top_eq

lemma induced_units.continuous_coe [induced_units R] : continuous (coe : units R → R) :=
(units_topology_eq R).symm ▸ continuous_induced_dom

lemma units_embedding [induced_units R] :
  embedding (coe : units R → R) :=
{ induced := units_topology_eq R,
  inj := λ x y h, units.ext h }

instance top_monoid_units [topological_ring R] [induced_units R] :
  has_continuous_mul (units R) :=
⟨begin
  let mulR := (λ (p : R × R), p.1*p.2),
  let mulRx := (λ (p : units R × units R), p.1*p.2),
  have key : coe ∘ mulRx = mulR ∘ (λ p, (p.1.val, p.2.val)), from rfl,
  rw [continuous_iff_le_induced, units_topology_eq R, prod_induced_induced,
      induced_compose, key, ← induced_compose],
  apply induced_mono,
  rw ← continuous_iff_le_induced,
  exact continuous_mul,
end⟩
end topological_ring

variables (K : Type*) [division_ring K] [topological_space K]

/-- A topological division ring is a division ring with a topology where all operations are
    continuous, including inversion. -/
class topological_division_ring extends topological_ring K : Prop :=
(continuous_inv : ∀ x : K, x ≠ 0 → continuous_at (λ x : K, x⁻¹ : K → K) x)

namespace topological_division_ring
open filter set
/-!
In this section, we show that units of a topological division ring endowed with the
induced topology form a topological group. These are not global instances because
one could want another topology on units. To turn on this feature, use:

```lean
local attribute [instance]
topological_ring.topological_space_units topological_division_ring.units_top_group
```
-/

local attribute [instance] topological_ring.topological_space_units

@[priority 100] instance induced_units : topological_ring.induced_units K := ⟨rfl⟩

variables [topological_division_ring K]

lemma units_top_group : topological_group (units K) :=
{ continuous_inv := begin
     have : (coe : units K → K) ∘ (λ x, x⁻¹ : units K → units K) =
            (λ x, x⁻¹ : K → K) ∘ (coe : units K → K), from funext units.coe_inv',
     rw continuous_iff_continuous_at,
     intros x,
     rw [continuous_at, nhds_induced, nhds_induced, tendsto_iff_comap, comap_comm this],
     apply comap_mono,
     rw [← tendsto_iff_comap, units.coe_inv'],
     exact topological_division_ring.continuous_inv (x : K) x.ne_zero
   end ,
  ..topological_ring.top_monoid_units K}

local attribute [instance] units_top_group

lemma continuous_units_inv : continuous (λ x : units K, (↑(x⁻¹) : K)) :=
(topological_ring.induced_units.continuous_coe K).comp topological_group.continuous_inv

end topological_division_ring


section affine_homeomorph
/-!
This section is about affine homeomorphisms from a topological field `𝕜` to itself.
Technically it does not require `𝕜` to be a topological field, a topological ring that
happens to be a field is enough.
-/
variables {𝕜 : Type*} [field 𝕜] [topological_space 𝕜] [topological_ring 𝕜]

/--
The map `λ x, a * x + b`, as a homeomorphism from `𝕜` (a topological field) to itself, when `a ≠ 0`.
-/
@[simps]
def affine_homeomorph (a b : 𝕜) (h : a ≠ 0) : 𝕜 ≃ₜ 𝕜 :=
{ to_fun := λ x, a * x + b,
  inv_fun := λ y, (y - b) / a,
  left_inv := λ x, by { simp only [add_sub_cancel], exact mul_div_cancel_left x h, },
  right_inv := λ y, by { simp [mul_div_cancel' _ h], }, }

end affine_homeomorph

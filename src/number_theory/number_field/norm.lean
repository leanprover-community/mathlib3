/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Eric Rodriguez
-/

import number_theory.number_field.basic
import ring_theory.norm

/-!
# Norm in number fields
Given a finite extension of number fields, we define the norm morphism as a function between the
rings of integers.

## Main definitions
* `ring_of_integers.norm K` : `algebra.norm` as a morphism `(𝓞 L) →* (𝓞 K)`.
## Main results
* `algebra.dvd_norm` : if `L/K` is a finite Galois extension of fields, then, for all `(x : 𝓞 L)`
  we have that `x ∣ algebra_map (𝓞 K) (𝓞 L) (norm K x)`.

-/

open_locale number_field big_operators

open finset number_field algebra

namespace ring_of_integers

variables {L : Type*} (K : Type*) [field K] [field L] [algebra K L] [finite_dimensional K L]

/-- `algebra.norm` as a morphism betwen the rings of integers. -/
@[simps] noncomputable def norm [is_separable K L] : (𝓞 L) →* (𝓞 K) :=
((algebra.norm K).restrict (𝓞 L)).cod_restrict (𝓞 K) (λ x, is_integral_norm K x.2)

local attribute [instance] number_field.ring_of_integers_algebra

lemma coe_algebra_map_norm [is_separable K L] (x : 𝓞 L) :
  (algebra_map (𝓞 K) (𝓞 L) (norm K x) : L) = algebra_map K L (algebra.norm K (x : L)) := rfl

lemma is_unit_norm [is_galois K L] {x : 𝓞 L} :
  is_unit (norm K x) ↔ is_unit x :=
begin
  classical,
  refine ⟨λ hx, _, is_unit.map _⟩,
  replace hx : is_unit (algebra_map (𝓞 K) (𝓞 L) $ norm K x) := hx.map (algebra_map (𝓞 K) $ 𝓞 L),
  refine @is_unit_of_mul_is_unit_right (𝓞 L) _
         ⟨(univ \ { alg_equiv.refl }).prod (λ (σ : L ≃ₐ[K] L), σ x),
          prod_mem (λ σ hσ, map_is_integral (σ : L →+* L).to_int_alg_hom x.2)⟩ _ _,
  convert hx using 1,
  ext,
  push_cast,
  convert_to (univ \ { alg_equiv.refl }).prod (λ (σ : L ≃ₐ[K] L), σ x) * (∏ (σ : L ≃ₐ[K] L) in
    {alg_equiv.refl}, σ (x : L)) = _,
  { rw [prod_singleton, alg_equiv.coe_refl, id] },
  { rw [prod_sdiff $ subset_univ _, ←norm_eq_prod_automorphisms, coe_algebra_map_norm] }
end

/-- If `L/K` is a finite Galois extension of fields, then, for all `(x : 𝓞 L)` we have that
`x ∣ algebra_map (𝓞 K) (𝓞 L) (norm K x)`. -/
lemma dvd_norm [is_galois K L] (x : 𝓞 L) : x ∣ algebra_map (𝓞 K) (𝓞 L) (norm K x) :=
begin
  classical,
  have hint : (∏ (σ : L ≃ₐ[K] L) in univ.erase alg_equiv.refl, σ x) ∈ 𝓞 L :=
    subalgebra.prod_mem _ (λ σ hσ, (mem_ring_of_integers _ _).2
    (map_is_integral σ (ring_of_integers.is_integral_coe x))),
  refine ⟨⟨_, hint⟩, subtype.ext _⟩,
  rw [coe_algebra_map_norm K x, norm_eq_prod_automorphisms],
  simp [← finset.mul_prod_erase _ _ (mem_univ alg_equiv.refl)]
end

end ring_of_integers

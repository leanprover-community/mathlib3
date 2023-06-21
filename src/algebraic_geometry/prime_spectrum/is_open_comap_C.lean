/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import algebraic_geometry.prime_spectrum.basic
import ring_theory.polynomial.basic
/-!
> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The morphism `Spec R[x] --> Spec R` induced by the natural inclusion `R --> R[x]` is an open map.

The main result is the first part of the statement of Lemma 00FB in the Stacks Project.

https://stacks.math.columbia.edu/tag/00FB
-/

open ideal polynomial prime_spectrum set
open_locale polynomial

namespace algebraic_geometry

namespace polynomial

variables {R : Type*} [comm_ring R] {f : R[X]}

/-- Given a polynomial `f ∈ R[x]`, `image_of_Df` is the subset of `Spec R` where at least one
of the coefficients of `f` does not vanish.  Lemma `image_of_Df_eq_comap_C_compl_zero_locus`
proves that `image_of_Df` is the image of `(zero_locus {f})ᶜ` under the morphism
`comap C : Spec R[x] → Spec R`. -/
def image_of_Df (f) : set (prime_spectrum R) :=
  {p : prime_spectrum R | ∃ i : ℕ , (coeff f i) ∉ p.as_ideal}

lemma is_open_image_of_Df : is_open (image_of_Df f) :=
begin
  rw [image_of_Df, set_of_exists (λ i (x : prime_spectrum R), coeff f i ∉ x.as_ideal)],
  exact is_open_Union (λ i, is_open_basic_open),
end

/-- If a point of `Spec R[x]` is not contained in the vanishing set of `f`, then its image in
`Spec R` is contained in the open set where at least one of the coefficients of `f` is non-zero.
This lemma is a reformulation of `exists_C_coeff_not_mem`. -/
lemma comap_C_mem_image_of_Df {I : prime_spectrum R[X]}
  (H : I ∈ (zero_locus {f} : set (prime_spectrum R[X]))ᶜ ) :
  prime_spectrum.comap (polynomial.C : R →+* R[X]) I ∈ image_of_Df f :=
exists_C_coeff_not_mem (mem_compl_zero_locus_iff_not_mem.mp H)

/-- The open set `image_of_Df f` coincides with the image of `basic_open f` under the
morphism `C⁺ : Spec R[x] → Spec R`. -/
lemma image_of_Df_eq_comap_C_compl_zero_locus :
  image_of_Df f = prime_spectrum.comap (C : R →+* R[X]) '' (zero_locus {f})ᶜ :=
begin
  ext x,
  refine ⟨λ hx, ⟨⟨map C x.as_ideal, (is_prime_map_C_of_is_prime x.is_prime)⟩, ⟨_, _⟩⟩, _⟩,
  { rw [mem_compl_iff, mem_zero_locus, singleton_subset_iff],
    cases hx with i hi,
    exact λ a, hi (mem_map_C_iff.mp a i) },
  { ext x,
    refine ⟨λ h, _, λ h, subset_span (mem_image_of_mem C.1 h)⟩,
    rw ← @coeff_C_zero R x _,
    exact mem_map_C_iff.mp h 0 },
  { rintro ⟨xli, complement, rfl⟩,
    exact comap_C_mem_image_of_Df complement }
end

/--  The morphism `C⁺ : Spec R[x] → Spec R` is open.
Stacks Project "Lemma 00FB", first part.

https://stacks.math.columbia.edu/tag/00FB
-/
theorem is_open_map_comap_C :
  is_open_map (prime_spectrum.comap (C : R →+* R[X])) :=
begin
  rintros U ⟨s, z⟩,
  rw [← compl_compl U, ← z, ← Union_of_singleton_coe s, zero_locus_Union, compl_Inter, image_Union],
  simp_rw [← image_of_Df_eq_comap_C_compl_zero_locus],
  exact is_open_Union (λ f, is_open_image_of_Df),
end

end polynomial

end algebraic_geometry

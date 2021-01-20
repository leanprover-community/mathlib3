/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import algebraic_geometry.prime_spectrum
import ring_theory.polynomial.basic
/-!
The morphism `Spec R[x] --> Spec R` induced by the natural inclusion `R --> R[x]` is an open map.
-/

open ideal polynomial prime_spectrum set

namespace algebraic_geometry

namespace polynomial

variables {R : Type*} [comm_ring R]

/-- Given a polynomial `f ∈ R[x]`, `image_of_Df` is the subset of `Spec R` where at least one
of the coefficients of `f` does not vanish.  We will prove that `image_of_Df` is the image of
`(zero_locus {f})ᶜ` under the morphism `comap C : Spec R[x] → Spec R`. -/
def image_of_Df (f : polynomial R) : set (prime_spectrum R) :=
  {p : prime_spectrum R | ∃ i : ℕ , (coeff f i) ∉ p.as_ideal}

lemma is_open_image_of_Df (f : polynomial R) : is_open (image_of_Df f) :=
begin
  rw [image_of_Df, set_of_exists (λ i (x : prime_spectrum R), coeff f i ∉ x.val)],
  exact is_open_Union (λ i, is_open_basic_open),
end

lemma mem_compl_zero_locus_iff_not_mem {f : R} {I : prime_spectrum R} :
  I ∈ (zero_locus {f} : set (prime_spectrum R))ᶜ ↔ f ∉ I.as_ideal :=
by rw [mem_compl_eq, mem_zero_locus, singleton_subset_iff]; refl

/-- If a point of `Spec R[x]` is not contained in the vanishing set of `f`,
then its image in `Spec R` is contained in the open where at least one of the coefficients
of `f` is non-zero.  Such an open set is called `image_of_Df f` and actually coincides
with the image of `basic_open f`.
This lemma is a reformulation of `exists_coeff_not_mem_C_inverse`. -/
lemma comap_C_mem_image_of_Df {f : polynomial R} {I : prime_spectrum (polynomial R)}
  (H : I ∈ (zero_locus {f} : set (prime_spectrum (polynomial R)))ᶜ ) :
  comap (polynomial.C : R →+* polynomial R) I ∈ image_of_Df f :=
exists_coeff_not_mem_C_inverse (mem_compl_zero_locus_iff_not_mem.mp H)

theorem is_open_map_C_comap :
  is_open_map (comap (C : R →+* polynomial R)) :=
begin
  rintros U ⟨fs, cl⟩,
  rw [← compl_compl U, ← cl, ← Union_of_singleton_coe fs, zero_locus_Union, compl_Inter,
    image_Union],
  refine is_open_Union (λ f, _),
  convert is_open_image_of_Df f.1,
  refine ext (λ x, ⟨_, λ hx, ⟨⟨map C x.val, (is_prime_C_map_of_is_prime x.property)⟩, ⟨_, _⟩⟩⟩),
  { rintro ⟨xli, complement, rfl⟩,
    exact C_comap_mem_image_of_Df complement },
  { rw [mem_compl_eq, mem_zero_locus, singleton_subset_iff],
    cases hx with i hi,
    exact λ a, hi (mem_map_C_iff.mp a i) },
  { refine subtype.ext (ext (λ x, ⟨λ h, _, λ h, subset_span (mem_image_of_mem C.1 h)⟩)),
    rw ← @coeff_C_zero R x _,
    exact mem_map_C_iff.mp h 0 }
end

end polynomial

end algebraic_geometry

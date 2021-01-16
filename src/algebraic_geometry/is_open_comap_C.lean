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

open ideal polynomial prime_spectrum set integral_domain

local attribute [instance] classical.prop_decidable

variables {R : Type*} [comm_ring R] {P : ideal R}

/-- Given a polynomial `f ∈ R[x]`, `image_of_Df` is the subset of `Spec R` where at least one
of the coefficients of `f` does not vanish.  We will prove that `image_of_Df` is the image of
`(zero_locus {f})ᶜ` under the morphism `comap C : Spec R[x] → Spec R`. -/
def image_of_Df (f : polynomial R) : set (prime_spectrum R) :=
  {p : prime_spectrum R | ∃ i : ℕ , (coeff f i) ∉ p.as_ideal}

lemma is_open_image_of_Df (f : polynomial R) : is_open (image_of_Df f) :=
begin
  rw [image_of_Df, set_of_exists (λ i (x : prime_spectrum R), coeff f i ∉ x.val)],
  exact is_open_Union (λ i, std_aff_is_open (coeff f i)),
end

lemma mem_span_C_coeff (f : polynomial R) :
  f ∈ span {tt : polynomial R | ∃ i : ℕ ,tt = (C (coeff f i))} :=
begin
  conv_lhs {rw as_sum_support f},
  refine submodule.sum_mem _ (λ i hi, _),
  rw [← C_mul_X_pow_eq_monomial, mul_comm],
  exact submodule.smul_mem _ _ (submodule.subset_span ⟨i, rfl⟩),
end

lemma span_le_of_coeff_mem_comap {f : polynomial R} {I : ideal (polynomial R)}
  (hfi : ∀ (i : ℕ), f.coeff i ∈ (comap (C : R →+* polynomial R) I)) :
  (span {g : polynomial R | ∃ (i : ℕ), g = C (f.coeff i)}) ≤ I :=
begin
  refine bInter_subset_of_mem _,
  rintros _ ⟨i, rfl⟩,
  exact (submodule.mem_coe I).mpr (hfi i),
end

/-- The image of `Df` is contained in an open set (with which it actually coincides). -/
lemma exists_coeff_not_mem_C_comap {f : polynomial R} {I : prime_spectrum (polynomial R)} :
  f ∉ I.as_ideal → ∃ i : ℕ , coeff f i ∉ (comap (C : R →+* polynomial R) I).as_ideal :=
begin
  contrapose!,
  exact λ hfi, (span_le_of_coeff_mem_comap hfi) (mem_span_C_coeff f),
end

/-- If a point of `Spec R[x]` is not contained in the vanishing set of `f`,
then its image in `Spec R` is contained in the open where at least one of the coefficients
of `f` is non-zero. This lemma is a reformulation of `exists_coeff_not_mem_comap_C`. -/
lemma C_comap_mem_image_of_Df {f : polynomial R} {I : prime_spectrum (polynomial R)}
  (H : I ∈ (prime_spectrum.zero_locus {f} : set (prime_spectrum (polynomial R)))ᶜ ) :
  prime_spectrum.comap (polynomial.C : R →+* polynomial R) I ∈ image_of_Df f :=
begin
  refine exists_coeff_not_mem_C_comap (λ h, (H ((I.mem_zero_locus {f}).mp _))),
  rintro _ ⟨rfl⟩,
  exact h,
end

-- to src/data/set/lattice, PR#5691.
-- If this PR is merged into master, then this lemma can be removed
lemma bUnion_of_singleton_of_coe {α : Type*} (s : set α) :
  (⋃ (i : s), {i} : set α) = s :=
ext $ by simp

theorem is_open_map_C_comap :
  is_open_map (comap (C : R →+* polynomial R)) :=
begin
  rintros U ⟨fs, cl⟩,
  rw [← compl_compl U, ← cl, ← bUnion_of_singleton_of_coe fs, zero_locus_Union, compl_Inter,
    image_Union],
  refine is_open_Union (λ f, _),
  convert is_open_image_of_Df f.1,
  refine ext (λ x, ⟨_, λ hx, ⟨⟨map C x.1, (is_prime_C_map_of_is_prime x.2)⟩, ⟨_, _⟩⟩⟩),
  { rintro ⟨xli, complement, rfl⟩,
    exact C_comap_mem_image_of_Df complement },
  { rw [mem_compl_eq, mem_zero_locus, singleton_subset_iff],
    cases hx with i hi,
    exact λ a, hi (mem_map_C_iff.mp a i) },
  { refine subtype.ext (ext (λ x, ⟨λ h, _, λ h, submodule.subset_span (mem_image_of_mem C.1 h)⟩)),
    rw ← @coeff_C_zero R x _,
    exact mem_map_C_iff.mp h 0 }
end

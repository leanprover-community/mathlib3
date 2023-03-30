/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison
-/
import algebra.group.ext
import category_theory.simple
import category_theory.linear.basic
import category_theory.endomorphism
import algebra.algebra.spectrum

/-!
# Schur's lemma
We first prove the part of Schur's Lemma that holds in any preadditive category with kernels,
that any nonzero morphism between simple objects
is an isomorphism.

Second, we prove Schur's lemma for `𝕜`-linear categories with finite dimensional hom spaces,
over an algebraically closed field `𝕜`:
the hom space `X ⟶ Y` between simple objects `X` and `Y` is at most one dimensional,
and is 1-dimensional iff `X` and `Y` are isomorphic.
-/

namespace category_theory

open category_theory.limits

variables {C : Type*} [category C]
variables [preadditive C]

-- See also `epi_of_nonzero_to_simple`, which does not require `preadditive C`.
lemma mono_of_nonzero_from_simple [has_kernels C] {X Y : C} [simple X] {f : X ⟶ Y} (w : f ≠ 0) :
  mono f :=
preadditive.mono_of_kernel_zero (kernel_zero_of_nonzero_from_simple w)

/--
The part of **Schur's lemma** that holds in any preadditive category with kernels:
that a nonzero morphism between simple objects is an isomorphism.
-/
lemma is_iso_of_hom_simple [has_kernels C] {X Y : C} [simple X] [simple Y] {f : X ⟶ Y} (w : f ≠ 0) :
  is_iso f :=
begin
  haveI := mono_of_nonzero_from_simple w,
  exact is_iso_of_mono_of_nonzero w
end

/--
As a corollary of Schur's lemma for preadditive categories,
any morphism between simple objects is (exclusively) either an isomorphism or zero.
-/
lemma is_iso_iff_nonzero [has_kernels C] {X Y : C} [simple X] [simple Y] (f : X ⟶ Y) :
  is_iso f ↔ f ≠ 0 :=
⟨λ I,
  begin
    introI h,
    apply id_nonzero X,
    simp only [←is_iso.hom_inv_id f, h, zero_comp],
  end,
  λ w, is_iso_of_hom_simple w⟩

/--
In any preadditive category with kernels,
the endomorphisms of a simple object form a division ring.
-/
noncomputable
instance [has_kernels C] {X : C} [simple X] : division_ring (End X) :=
by classical; exact
{ inv := λ f, if h : f = 0 then 0 else by { haveI := is_iso_of_hom_simple h, exact inv f, },
  exists_pair_ne := ⟨𝟙 X, 0, id_nonzero _⟩,
  inv_zero := dif_pos rfl,
  mul_inv_cancel := λ f h, begin
    haveI := is_iso_of_hom_simple h,
    convert is_iso.inv_hom_id f,
    exact dif_neg h,
  end,
  ..(infer_instance : ring (End X)) }

open finite_dimensional

section
variables (𝕜 : Type*) [division_ring 𝕜]

/--
Part of **Schur's lemma** for `𝕜`-linear categories:
the hom space between two non-isomorphic simple objects is 0-dimensional.
-/
lemma finrank_hom_simple_simple_eq_zero_of_not_iso
  [has_kernels C] [linear 𝕜 C] {X Y : C} [simple X] [simple Y]
  (h : (X ≅ Y) → false):
  finrank 𝕜 (X ⟶ Y) = 0 :=
begin
  haveI := subsingleton_of_forall_eq (0 : X ⟶ Y) (λ f, begin
    have p := not_congr (is_iso_iff_nonzero f),
    simp only [not_not, ne.def] at p,
    refine p.mp (λ _, by exactI h (as_iso f)),
  end),
  exact finrank_zero_of_subsingleton,
end

end

variables (𝕜 : Type*) [field 𝕜]
variables [is_alg_closed 𝕜] [linear 𝕜 C]

-- In the proof below we have some difficulty using `I : finite_dimensional 𝕜 (X ⟶ X)`
-- where we need a `finite_dimensional 𝕜 (End X)`.
-- These are definitionally equal, but without eta reduction Lean can't see this.
-- To get around this, we use `convert I`,
-- then check the various instances agree field-by-field,

/--
An auxiliary lemma for Schur's lemma.

If `X ⟶ X` is finite dimensional, and every nonzero endomorphism is invertible,
then `X ⟶ X` is 1-dimensional.
-/
-- We prove this with the explicit `is_iso_iff_nonzero` assumption,
-- rather than just `[simple X]`, as this form is useful for
-- Müger's formulation of semisimplicity.
lemma finrank_endomorphism_eq_one
  {X : C} (is_iso_iff_nonzero : ∀ f : X ⟶ X, is_iso f ↔ f ≠ 0)
  [I : finite_dimensional 𝕜 (X ⟶ X)] :
  finrank 𝕜 (X ⟶ X) = 1 :=
begin
  have id_nonzero := (is_iso_iff_nonzero (𝟙 X)).mp (by apply_instance),
  apply finrank_eq_one (𝟙 X),
  { exact id_nonzero, },
  { intro f,
    haveI : nontrivial (End X) := nontrivial_of_ne _ _ id_nonzero,
    obtain ⟨c, nu⟩ := @spectrum.nonempty_of_is_alg_closed_of_finite_dimensional 𝕜 (End X) _ _ _ _ _
      (by { convert I, ext, refl, ext, refl, }) (End.of f),
    use c,
    rw [spectrum.mem_iff, is_unit.sub_iff, is_unit_iff_is_iso, is_iso_iff_nonzero, ne.def,
      not_not, sub_eq_zero, algebra.algebra_map_eq_smul_one] at nu,
    exact nu.symm, },
end

variables [has_kernels C]

/--
**Schur's lemma** for endomorphisms in `𝕜`-linear categories.
-/
lemma finrank_endomorphism_simple_eq_one
  (X : C) [simple X] [I : finite_dimensional 𝕜 (X ⟶ X)] :
  finrank 𝕜 (X ⟶ X) = 1 :=
finrank_endomorphism_eq_one 𝕜 is_iso_iff_nonzero

lemma endomorphism_simple_eq_smul_id
  {X : C} [simple X] [I : finite_dimensional 𝕜 (X ⟶ X)] (f : X ⟶ X) :
  ∃ c : 𝕜, c • 𝟙 X = f :=
(finrank_eq_one_iff_of_nonzero' (𝟙 X) (id_nonzero X)).mp (finrank_endomorphism_simple_eq_one 𝕜 X) f

/--
Endomorphisms of a simple object form a field if they are finite dimensional.
This can't be an instance as `𝕜` would be undetermined.
-/
noncomputable
def field_End_of_finite_dimensional (X : C) [simple X] [I : finite_dimensional 𝕜 (X ⟶ X)] :
  field (End X) :=
by classical; exact
{ mul_comm := λ f g, begin
    obtain ⟨c, rfl⟩ := endomorphism_simple_eq_smul_id 𝕜 f,
    obtain ⟨d, rfl⟩ := endomorphism_simple_eq_smul_id 𝕜 g,
    simp [←mul_smul, mul_comm c d],
  end,
  ..(infer_instance : division_ring (End X)) }

/--
**Schur's lemma** for `𝕜`-linear categories:
if hom spaces are finite dimensional, then the hom space between simples is at most 1-dimensional.

See `finrank_hom_simple_simple_eq_one_iff` and `finrank_hom_simple_simple_eq_zero_iff` below
for the refinements when we know whether or not the simples are isomorphic.
-/
-- There is a symmetric argument that uses `[finite_dimensional 𝕜 (Y ⟶ Y)]` instead,
-- but we don't bother proving that here.
lemma finrank_hom_simple_simple_le_one
  (X Y : C) [finite_dimensional 𝕜 (X ⟶ X)] [simple X] [simple Y] :
  finrank 𝕜 (X ⟶ Y) ≤ 1 :=
begin
  cases subsingleton_or_nontrivial (X ⟶ Y) with h,
  { resetI,
    rw finrank_zero_of_subsingleton,
    exact zero_le_one },
  { obtain ⟨f, nz⟩ := (nontrivial_iff_exists_ne 0).mp h,
    haveI fi := (is_iso_iff_nonzero f).mpr nz,
    apply finrank_le_one f,
    intro g,
    obtain ⟨c, w⟩ := endomorphism_simple_eq_smul_id 𝕜 (g ≫ inv f),
    exact ⟨c, by simpa using w =≫ f⟩, },
end

lemma finrank_hom_simple_simple_eq_one_iff
  (X Y : C) [finite_dimensional 𝕜 (X ⟶ X)] [finite_dimensional 𝕜 (X ⟶ Y)] [simple X] [simple Y] :
  finrank 𝕜 (X ⟶ Y) = 1 ↔ nonempty (X ≅ Y) :=
begin
  fsplit,
  { intro h,
    rw finrank_eq_one_iff' at h,
    obtain ⟨f, nz, -⟩ := h,
    rw ←is_iso_iff_nonzero at nz,
    exactI ⟨as_iso f⟩, },
  { rintro ⟨f⟩,
    have le_one := finrank_hom_simple_simple_le_one 𝕜 X Y,
    have zero_lt : 0 < finrank 𝕜 (X ⟶ Y) :=
      finrank_pos_iff_exists_ne_zero.mpr ⟨f.hom, (is_iso_iff_nonzero f.hom).mp infer_instance⟩,
    linarith, }
end

lemma finrank_hom_simple_simple_eq_zero_iff
  (X Y : C) [finite_dimensional 𝕜 (X ⟶ X)] [finite_dimensional 𝕜 (X ⟶ Y)] [simple X] [simple Y] :
  finrank 𝕜 (X ⟶ Y) = 0 ↔ is_empty (X ≅ Y) :=
begin
  rw [← not_nonempty_iff, ← not_congr (finrank_hom_simple_simple_eq_one_iff 𝕜 X Y)],
  refine ⟨λ h, by { rw h, simp, }, λ h, _⟩,
  have := finrank_hom_simple_simple_le_one 𝕜 X Y,
  interval_cases finrank 𝕜 (X ⟶ Y) with h',
  { exact h', },
  { exact false.elim (h h'), },
end

open_locale classical

lemma finrank_hom_simple_simple
  (X Y : C) [∀ X Y : C, finite_dimensional 𝕜 (X ⟶ Y)] [simple X] [simple Y] :
  finrank 𝕜 (X ⟶ Y) = if nonempty (X ≅ Y) then 1 else 0 :=
begin
  split_ifs,
  exact (finrank_hom_simple_simple_eq_one_iff 𝕜 X Y).2 h,
  exact (finrank_hom_simple_simple_eq_zero_iff 𝕜 X Y).2 (not_nonempty_iff.mp h),
end

end category_theory

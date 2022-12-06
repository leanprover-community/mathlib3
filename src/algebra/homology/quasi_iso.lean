/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Joël Riou
-/
import algebra.homology.homotopy
import algebra.homology.exact

/-!
# Quasi-isomorphisms

A chain map is a quasi-isomorphism if it induces isomorphisms on homology.

## Future work

Define the derived category as the localization at quasi-isomorphisms?
-/

open category_theory
open category_theory.limits

universes v u

variables {ι : Type*}
variables {V : Type u} [category.{v} V] [has_zero_morphisms V] {c : complex_shape ι}

section

variables {C D E : homological_complex V c}
  [∀ i, C.has_homology i] [∀ i, D.has_homology i] [∀ i, E.has_homology i]
/--
A chain map is a quasi-isomorphism if it induces isomorphisms on homology.
-/
class quasi_iso (f : C ⟶ D) : Prop :=
(is_iso : ∀ i, is_iso (homology_map f i))

attribute [instance] quasi_iso.is_iso

@[priority 100]
instance quasi_iso_of_iso (f : C ⟶ D) [is_iso f] : quasi_iso f :=
{ is_iso := λ i, infer_instance, }

instance quasi_iso_comp (f : C ⟶ D) [quasi_iso f] (g : D ⟶ E) [quasi_iso g] : quasi_iso (f ≫ g) :=
{ is_iso := λ i, by { rw homology_map_comp, apply_instance, }, }

lemma quasi_iso_of_comp_left (f : C ⟶ D) [quasi_iso f] (g : D ⟶ E) [quasi_iso (f ≫ g)] :
  quasi_iso g :=
{ is_iso := λ i, is_iso.of_is_iso_fac_left (homology_map_comp f g i).symm, }

lemma quasi_iso_of_comp_right (f : C ⟶ D) (g : D ⟶ E) [quasi_iso g] [quasi_iso (f ≫ g)] :
  quasi_iso f :=
{ is_iso := λ i, is_iso.of_is_iso_fac_right (homology_map_comp f g i).symm }

lemma is_iso_homology_map_iff_short_complex_quasi_iso (f : C ⟶ D) (i : ι) :
  is_iso (homology_map f i) ↔
      short_complex.quasi_iso ((homological_complex.short_complex_functor V c i).map f) :=
by refl

lemma quasi_iso_iff_short_complex_quasi_iso (f : C ⟶ D) :
  quasi_iso f ↔ ∀ (i : ι),
    short_complex.quasi_iso ((homological_complex.short_complex_functor V c i).map f) :=
begin
  simp only [← is_iso_homology_map_iff_short_complex_quasi_iso],
  split,
  { exact λ hf, hf.is_iso, },
  { exact λ hf, ⟨hf⟩, },
end

lemma is_iso_homology_map_iff_short_complex_quasi_iso' (f : C ⟶ D)
  {i j k : ι} (hij : c.rel i j) (hjk : c.rel j k)
  [((homological_complex.short_complex_functor' V c i j k).obj C).has_homology]
  [((homological_complex.short_complex_functor' V c i j k).obj D).has_homology] :
  is_iso (homology_map f j) ↔
    short_complex.quasi_iso ((homological_complex.short_complex_functor' V c i j k).map f) :=
short_complex.iff_of_arrow_mk_iso _ _
  (arrow.iso_of_nat_iso (homological_complex.short_complex_functor_nat_iso V c hij hjk)
    (arrow.mk f))

end

namespace homotopy_equiv

section
variables {W : Type*} [category W] [preadditive W]
variables {C D : homological_complex W c}
  [∀ i, C.has_homology i] [∀ i, D.has_homology i]

/-- An homotopy equivalence is a quasi-isomorphism. -/
lemma to_quasi_iso (e : homotopy_equiv C D) : quasi_iso e.hom :=
⟨λ i, is_iso.of_iso (e.to_homology_iso i)⟩

lemma to_quasi_iso_inv (e : homotopy_equiv C D) (i : ι) :
  (@as_iso _ _ _ _ _ (e.to_quasi_iso.1 i)).inv = homology_map e.inv i :=
begin
  symmetry,
  rw [← iso.hom_comp_eq_id, as_iso_hom, ← homology_map_comp,
    homology_map_eq_of_homotopy' e.homotopy_hom_inv_id, homology_map_id],
end

end
end homotopy_equiv
namespace homological_complex.hom
section to_single₀
variables {W : Type*} [category W] [abelian W]

section
variables {X : chain_complex W ℕ} {Y : W} (f : X ⟶ ((chain_complex.single₀ _).obj Y))
  [hf : quasi_iso f]

/-- If a chain map `f : X ⟶ Y[0]` is a quasi-isomorphism, then the cokernel of the differential
`d : X₁ → X₀` is isomorphic to `Y.` -/
noncomputable
def to_single₀_cokernel_at_zero_iso : cokernel (X.d 1 0) ≅ Y :=
(X.homology_zero_iso.symm.trans ((@as_iso _ _ _ _ _ (hf.1 0)).trans
  ((chain_complex.homology_functor_0_single₀ W).app Y)))

lemma to_single₀_cokernel_at_zero_iso_hom_eq [hf : quasi_iso f] :
  f.to_single₀_cokernel_at_zero_iso.hom = cokernel.desc (X.d 1 0) (f.f 0)
    (by rw ←f.2 1 0 rfl; exact comp_zero) :=
begin
  dsimp [to_single₀_cokernel_at_zero_iso],
  simp only [chain_complex.homology_map_zero, category.assoc, iso.inv_hom_id_assoc],
  erw chain_complex.homology_zero_iso_inv_comp_homology_single₀_zero_hom Y,
  ext,
  dsimp,
  simp only [cokernel.π_desc_assoc, category.assoc, cokernel.π_desc, category.comp_id],
end

lemma to_single₀_epi_at_zero [hf : quasi_iso f] :
  epi (f.f 0) :=
begin
  constructor,
  intros Z g h Hgh,
  rw [←cokernel.π_desc (X.d 1 0) (f.f 0) (by rw ←f.2 1 0 rfl; exact comp_zero),
    ←to_single₀_cokernel_at_zero_iso_hom_eq] at Hgh,
  rw (@cancel_epi _ _ _ _ _ _ (epi_comp _ _) _ _).1 Hgh,
end

lemma to_single₀_exact_d_f_at_zero [hf : quasi_iso f] :
  exact (X.d 1 0) (f.f 0) :=
begin
  have w : X.d 1 0 ≫ f.f 0 = 0,
  { rw [← f.comm 1 0, chain_complex.single₀_obj_X_d, comp_zero], },
  rw [exact_iff_exact_short_complex _ _ w,
    short_complex.exact_iff_mono_cokernel_desc,
    ← to_single₀_cokernel_at_zero_iso_hom_eq],
  apply_instance,
end

lemma to_single₀_exact_at_succ [hf : quasi_iso f] (n : ℕ) :
  exact (X.d (n + 2) (n + 1)) (X.d (n + 1) n) :=
begin
  rw [exact_iff_exact_short_complex _ _ (X.d_comp_d _ _ _)],
  erw short_complex.exact_iff_of_iso ((homological_complex.short_complex_functor_nat_iso W (complex_shape.down ℕ)
    (rfl : (n+1)+1 = n+2) (rfl : n+1 = n+1)).app X).symm,
  rw short_complex.exact_iff_homology_zero,
  haveI := hf.is_iso (n+1), -- why is it necessary?
  exact nonempty.intro (as_iso (homology_map f (n+1)) ≪≫
    chain_complex.homology_single₀_succ Y n),
end

end
section
variables {X : cochain_complex W ℕ} {Y : W}
  (f : (cochain_complex.single₀ _).obj Y ⟶ X)

/-- If a cochain map `f : Y[0] ⟶ X` is a quasi-isomorphism, then the kernel of the differential
`d : X₀ → X₁` is isomorphic to `Y.` -/
noncomputable def from_single₀_kernel_at_zero_iso [hf : quasi_iso f] : kernel (X.d 0 1) ≅ Y :=
(X.homology_zero_iso.symm.trans ((@as_iso _ _ _ _ _ (hf.1 0)).symm.trans
  ((cochain_complex.homology_functor_0_single₀ W).app Y)))

lemma from_single₀_kernel_at_zero_iso_inv_eq [hf : quasi_iso f] :
  f.from_single₀_kernel_at_zero_iso.inv = kernel.lift (X.d 0 1) (f.f 0)
    (by rw f.2 0 1 rfl; exact zero_comp) :=
begin
  dsimp [from_single₀_kernel_at_zero_iso],
  simp only [cochain_complex.homology_map_zero, category.assoc, iso.inv_hom_id, category.comp_id],
  erw cochain_complex.homology_single₀_zero_inv_comp_homology_zero_iso_hom_assoc Y,
  ext,
  dsimp,
  simp only [category.assoc, kernel.lift_ι, kernel.lift_ι_assoc, category.id_comp],
end

lemma from_single₀_mono_at_zero [hf : quasi_iso f] :
  mono (f.f 0) :=
begin
  constructor,
  intros Z g h Hgh,
  rw [←kernel.lift_ι (X.d 0 1) (f.f 0) (by rw f.2 0 1 rfl; exact zero_comp),
    ←from_single₀_kernel_at_zero_iso_inv_eq] at Hgh,
  rw (@cancel_mono _ _ _ _ _ _ (mono_comp _ _) _ _).1 Hgh,
end

lemma from_single₀_exact_f_d_at_zero [hf : quasi_iso f] :
  exact (f.f 0) (X.d 0 1) :=
begin
  have w : f.f 0 ≫ X.d 0 1 = 0,
  { rw [f.comm 0 1, cochain_complex.single₀_obj_X_d, zero_comp], },
  rw [exact_iff_exact_short_complex _ _ w,
    short_complex.exact_iff_epi_kernel_lift,
    ← from_single₀_kernel_at_zero_iso_inv_eq],
  apply_instance,
end

lemma from_single₀_exact_at_succ [hf : quasi_iso f] (n : ℕ) :
  exact (X.d n (n + 1)) (X.d (n + 1) (n + 2)) :=
begin
  rw [exact_iff_exact_short_complex _ _ (X.d_comp_d _ _ _)],
  erw short_complex.exact_iff_of_iso ((homological_complex.short_complex_functor_nat_iso W (complex_shape.up ℕ)
    (rfl : n+1 = n+1) (rfl : (n+1)+1 = n+2)).app X).symm,
  rw short_complex.exact_iff_homology_zero,
  haveI := hf.is_iso (n+1), -- why is it necessary?
  refine nonempty.intro ((as_iso (homology_map f (n+1))).symm ≪≫
    cochain_complex.homology_single₀_succ Y n),
end

end
end to_single₀
end homological_complex.hom

variables {A : Type*} [category A] [abelian A] {B : Type*} [category B] [abelian B]
  (F : A ⥤ B) [functor.additive F] [preserves_finite_limits F] [preserves_finite_colimits F]
  [faithful F]

lemma category_theory.functor.quasi_iso_of_map_quasi_iso
  {C D : homological_complex A c} (f : C ⟶ D)
  (hf : quasi_iso ((F.map_homological_complex _).map f)) : quasi_iso f :=
begin
  simp only [quasi_iso_iff_short_complex_quasi_iso] at hf ⊢,
  intro i,
  let α := (homological_complex.short_complex_functor _ _ i).map f,
  change short_complex.quasi_iso α,
  rw ← short_complex.quasi_iso_map_iff_of_preserves_left_homology α F,
  exact hf i,
end

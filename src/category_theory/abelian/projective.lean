/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison, Jakob von Raumer
-/
import category_theory.abelian.exact
import category_theory.abelian.homology
import category_theory.preadditive.projective_resolution

/-!
# Abelian categories with enough projectives have projective resolutions

When `C` is abelian `projective.d f` and `f` are exact.
Hence, starting from an epimorphism `P ⟶ X`, where `P` is projective,
we can apply `projective.d` repeatedly to obtain a projective resolution of `X`.
-/

noncomputable theory

open category_theory
open category_theory.limits
open opposite

universes v u v' u'

namespace category_theory

open category_theory.projective

variables {C : Type u} [category.{v} C] [abelian C]

/--
When `C` is abelian, `projective.d f` and `f` are exact.
-/
lemma exact_d_f [enough_projectives C] {X Y : C} (f : X ⟶ Y) : exact (d f) f :=
(abelian.exact_iff _ _).2 $
  ⟨by simp, zero_of_epi_comp (π _) $ by rw [←category.assoc, cokernel.condition]⟩

/-- The preadditive Co-Yoneda functor on `P` preserves colimits if `P` is projective. -/
def preserves_finite_colimits_preadditive_coyoneda_obj_of_projective (P : C)
  [hP : projective P] : preserves_finite_colimits (preadditive_coyoneda_obj (op P)) :=
begin
  letI := (projective_iff_preserves_epimorphisms_preadditive_coyoneda_obj' P).mp hP,
  apply functor.preserves_finite_colimits_of_preserves_epis_and_kernels,
end

/-- An object is projective if its preadditive Co-Yoneda functor preserves finite colimits. -/
lemma projective_of_preserves_finite_colimits_preadditive_coyoneda_obj (P : C)
  [hP : preserves_finite_colimits (preadditive_coyoneda_obj (op P))] : projective P :=
begin
  rw projective_iff_preserves_epimorphisms_preadditive_coyoneda_obj',
  apply_instance
end

namespace ProjectiveResolution

/-!
Our goal is to define `ProjectiveResolution.of Z : ProjectiveResolution Z`.
The `0`-th object in this resolution will just be `projective.over Z`,
i.e. an arbitrarily chosen projective object with a map to `Z`.
After that, we build the `n+1`-st object as `projective.syzygies`
applied to the previously constructed morphism,
and the map to the `n`-th object as `projective.d`.
-/
variables [enough_projectives C]

/-- Auxiliary definition for `ProjectiveResolution.of`. -/
@[simps]
def of_complex (Z : C) : chain_complex C ℕ :=
chain_complex.mk'
  (projective.over Z) (projective.syzygies (projective.π Z)) (projective.d (projective.π Z))
  (λ ⟨X, Y, f⟩, ⟨projective.syzygies f, projective.d f, (exact_d_f f).w⟩)

/--
In any abelian category with enough projectives,
`ProjectiveResolution.of Z` constructs a projective resolution of the object `Z`.
-/
@[irreducible] def of (Z : C) : ProjectiveResolution Z :=
{ complex := of_complex Z,
  π := chain_complex.mk_hom _ _ (projective.π Z) 0
    (by { simp, exact (exact_d_f (projective.π Z)).w.symm, })
    (λ n _, ⟨0, by ext⟩),
  projective := by { rintros (_|_|_|n); apply projective.projective_over, },
  exact₀ := by simpa using exact_d_f (projective.π Z),
  exact := by { rintros (_|n); { simp, apply exact_d_f, }, },
  epi := projective.π_epi Z, }

@[priority 100]
instance (Z : C) : has_projective_resolution Z :=
{ out := ⟨of Z⟩ }

@[priority 100]
instance : has_projective_resolutions C :=
{ out := λ Z, by apply_instance }

end ProjectiveResolution
end category_theory

namespace homotopy_equiv

variables {C : Type u} [category C]
section

variables [has_zero_object C] [preadditive C] [has_equalizers C] [has_images C]

open category_theory category_theory.limits

/-- If a chain complex `C` is homotopy equivalent to a complex concentrated at 0 (for some
object `X`), the cokernel of the differential `d : C₁ → C₀` is isomorphic to `X.` -/
def cokernel_at_zero_single₀
  [has_cokernels C] [has_image_maps C] {X : chain_complex C ℕ} {Y : C}
  (H : homotopy_equiv X ((chain_complex.single₀ _).obj Y)) : cokernel (X.d 1 0) ≅ Y :=
(X.homology_zero_iso.symm.trans ((@as_iso _ _ _ _ _ (H.to_quasi_iso.1 0)).trans
  ((chain_complex.homology_functor_0_single₀ C).app Y)))

lemma cokernel_at_zero_single₀_hom_eq
  [has_cokernels C] [has_image_maps C] {X : chain_complex C ℕ} {Y : C}
  (H : homotopy_equiv X ((chain_complex.single₀ _).obj Y)) :
  H.cokernel_at_zero_single₀.hom = cokernel.desc (X.d 1 0) (H.1.f 0)
    (by rw ←H.1.2 1 0 rfl; exact comp_zero) :=
begin
  ext,
  dunfold cokernel_at_zero_single₀ chain_complex.homology_zero_iso homology_of_zero_right
    homology.map_iso chain_complex.homology_functor_0_single₀ cokernel.map,
  dsimp,
  simp only [cokernel.π_desc, category.assoc, homology.map_desc],
  simp only [←category.assoc, cokernel.π_desc],
  simp only [category.assoc, homology.desc, cokernel.π_desc],
  suffices : (iso.refl (X.X 0)).inv ≫ H.1.f 0 = H.1.f 0,
  begin
    by simpa,
  end,
  rw [iso.refl_inv, category.id_comp],
end

end
section
variables [abelian C]

def of_homotopy_equiv_single₀ [has_cokernels C] {X : chain_complex C ℕ}
  (HX : ∀ n, category_theory.projective (X.X n)) (Y : C)
  (H : _root_.homotopy_equiv X ((chain_complex.single₀ _).obj Y)) :
  ProjectiveResolution Y :=
{ complex := X,
  π := H.hom,
  projective := HX,
  exact₀ :=
  begin
    rw preadditive.exact_iff_homology_zero,
  have h : X.d 1 0 ≫ H.hom.f 0 = 0,
  { simp only [← H.1.2 1 0 rfl, chain_complex.single₀_obj_X_d, comp_zero], },
  refine ⟨h, nonempty.intro (homology_iso_kernel_desc _ _ _ ≪≫ _)⟩,
  { suffices : is_iso (cokernel.desc _ _ h),
    { haveI := this, apply kernel.of_mono, },
      rw ←cokernel_at_zero_single₀_hom_eq,
      apply_instance }
  end,
  exact := λ n, (preadditive.exact_iff_homology_zero _ _).2
    ⟨X.d_comp_d _ _ _, ⟨(chain_complex.homology_succ_iso _ _).symm.trans
    ((homology_obj_iso_of_homotopy_equiv H _).trans homology_zero_zero)⟩⟩,
  epi := ⟨λ Z g h Hgh,
    begin
    have : H.inv.f 0 ≫ H.hom.f 0 = 𝟙 _ := by rw [←homological_complex.comp_f, H.4.3 0]; simp,
    rw [←category.id_comp g, ←category.id_comp h, ←this,
      category.assoc, category.assoc, Hgh]
    end⟩ }
#check (chain_complex.single₀_map_homological_complex _).app
#check is_equivalence
#check functor.preserves_epimorphisms

lemma hmm {D : Type u'} [category.{v} D] [abelian D] (F : C ⥤ D)
  [hF : is_equivalence F] (Y : C) (hY : projective Y) : projective (F.obj Y) :=
begin
  constructor,
  intros E X f e he,
  have := (hF.2.app Y).hom ≫ F.inv.map f,
  haveI : epi (F.inv.map e) :=
  by unfreezingI { exact (functor.preserves_epimorphsisms_of_adjunction
      F.inv.as_equivalence.to_adjunction).1 e },
  rcases @hY.1 ((hF.2.app Y).hom ≫ F.inv.map f) (F.inv.map e),
  use F.map w ≫ (hF.3.app E).hom,
  have := hF.4 Y,
end
--should be generalised I suppose!
def hmmm {D : Type u'} [category.{v} D] [abelian D] (F : C ⥤ D)
  [is_equivalence F] [F.additive]
  (X : C) (P : ProjectiveResolution X) : ProjectiveResolution (F.obj X) :=
{ complex := (F.map_homological_complex _).obj P.complex,
  π := (F.map_homological_complex _).map P.π ≫
    ((chain_complex.single₀_map_homological_complex F).app X).hom,
  projective := _,
  exact₀ := _,
  exact := _,
  epi := _ }

end
end homotopy_equiv

/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Amelia Livingston
-/
import algebra.homology.additive
import category_theory.abelian.pseudoelements
import category_theory.limits.preserves.shapes.kernels
import category_theory.limits.preserves.shapes.images

/-!
> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.


The object `homology f g w`, where `w : f ≫ g = 0`, can be identified with either a
cokernel or a kernel. The isomorphism with a cokernel is `homology_iso_cokernel_lift`, which
was obtained elsewhere. In the case of an abelian category, this file shows the isomorphism
with a kernel as well.

We use these isomorphisms to obtain the analogous api for `homology`:
- `homology.ι` is the map from `homology f g w` into the cokernel of `f`.
- `homology.π'` is the map from `kernel g` to `homology f g w`.
- `homology.desc'` constructs a morphism from `homology f g w`, when it is viewed as a cokernel.
- `homology.lift` constructs a morphism to `homology f g w`, when it is viewed as a kernel.
- Various small lemmas are proved as well, mimicking the API for (co)kernels.
With these definitions and lemmas, the isomorphisms between homology and a (co)kernel need not
be used directly.
-/

open category_theory.limits
open category_theory

noncomputable theory

universes v u
variables {A : Type u} [category.{v} A] [abelian A]

variables {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0)

namespace category_theory.abelian

/-- The cokernel of `kernel.lift g f w`. This is isomorphic to `homology f g w`.
  See `homology_iso_cokernel_lift`. -/
abbreviation homology_c : A :=
cokernel (kernel.lift g f w)

/-- The kernel of `cokernel.desc f g w`. This is isomorphic to `homology f g w`.
  See `homology_iso_kernel_desc`. -/
abbreviation homology_k : A :=
kernel (cokernel.desc f g w)

/-- The canonical map from `homology_c` to `homology_k`.
  This is an isomorphism, and it is used in obtaining the API for `homology f g w`
  in the bottom of this file. -/
abbreviation homology_c_to_k : homology_c f g w ⟶ homology_k f g w :=
cokernel.desc _ (kernel.lift _ (kernel.ι _ ≫ cokernel.π _) (by simp)) begin
  apply limits.equalizer.hom_ext,
  simp,
end

local attribute [instance] pseudoelement.hom_to_fun pseudoelement.has_zero

instance : mono (homology_c_to_k f g w) :=
begin
  apply pseudoelement.mono_of_zero_of_map_zero,
  intros a ha,
  obtain ⟨a,rfl⟩ := pseudoelement.pseudo_surjective_of_epi (cokernel.π (kernel.lift g f w)) a,
  apply_fun (kernel.ι (cokernel.desc f g w)) at ha,
  simp only [←pseudoelement.comp_apply, cokernel.π_desc,
    kernel.lift_ι, pseudoelement.apply_zero] at ha,
  simp only [pseudoelement.comp_apply] at ha,
  obtain ⟨b,hb⟩ : ∃ b, f b = _ := (pseudoelement.pseudo_exact_of_exact (exact_cokernel f)).2 _ ha,
  rsuffices ⟨c, rfl⟩ : ∃ c, kernel.lift g f w c = a,
  { simp [← pseudoelement.comp_apply] },
  use b,
  apply_fun kernel.ι g,
  swap, { apply pseudoelement.pseudo_injective_of_mono },
  simpa [← pseudoelement.comp_apply]
end

instance : epi (homology_c_to_k f g w) :=
begin
  apply pseudoelement.epi_of_pseudo_surjective,
  intros a,
  let b := kernel.ι (cokernel.desc f g w) a,
  obtain ⟨c,hc⟩ : ∃ c, cokernel.π f c = b,
    apply pseudoelement.pseudo_surjective_of_epi (cokernel.π f),
  have : g c = 0,
  { dsimp [b] at hc,
    rw [(show g = cokernel.π f ≫ cokernel.desc f g w, by simp), pseudoelement.comp_apply, hc],
    simp [← pseudoelement.comp_apply] },
  obtain ⟨d,hd⟩ : ∃ d, kernel.ι g d = c,
  { apply (pseudoelement.pseudo_exact_of_exact exact_kernel_ι).2 _ this },
  use cokernel.π (kernel.lift g f w) d,
  apply_fun kernel.ι (cokernel.desc f g w),
  swap, { apply pseudoelement.pseudo_injective_of_mono },
  simp only [←pseudoelement.comp_apply, cokernel.π_desc, kernel.lift_ι],
  simp only [pseudoelement.comp_apply, hd, hc],
end

instance (w : f ≫ g = 0) : is_iso (homology_c_to_k f g w) := is_iso_of_mono_of_epi _

end category_theory.abelian

/-- The homology associated to `f` and `g` is isomorphic to a kernel. -/
def homology_iso_kernel_desc : homology f g w ≅ kernel (cokernel.desc f g w) :=
homology_iso_cokernel_lift _ _ _ ≪≫ as_iso (category_theory.abelian.homology_c_to_k _ _ _)

namespace homology

-- `homology.π` is taken
/-- The canonical map from the kernel of `g` to the homology of `f` and `g`. -/
def π' : kernel g ⟶ homology f g w :=
cokernel.π _ ≫ (homology_iso_cokernel_lift _ _ _).inv

/-- The canonical map from the homology of `f` and `g` to the cokernel of `f`. -/
def ι : homology f g w ⟶ cokernel f :=
(homology_iso_kernel_desc _ _ _).hom ≫ kernel.ι _

/-- Obtain a morphism from the homology, given a morphism from the kernel. -/
def desc' {W : A} (e : kernel g ⟶ W) (he : kernel.lift g f w ≫ e = 0) :
  homology f g w ⟶ W :=
(homology_iso_cokernel_lift _ _ _).hom ≫ cokernel.desc _ e he

/-- Obtain a moprhism to the homology, given a morphism to the kernel. -/
def lift {W : A} (e : W ⟶ cokernel f) (he : e ≫ cokernel.desc f g w = 0) :
  W ⟶ homology f g w :=
kernel.lift _ e he ≫ (homology_iso_kernel_desc _ _ _).inv

@[simp, reassoc]
lemma π'_desc' {W : A} (e : kernel g ⟶ W) (he : kernel.lift g f w ≫ e = 0) :
  π' f g w ≫ desc' f g w e he = e :=
by { dsimp [π', desc'], simp }

@[simp, reassoc]
lemma lift_ι {W : A} (e : W ⟶ cokernel f) (he : e ≫ cokernel.desc f g w = 0) :
  lift f g w e he ≫ ι _ _ _ = e :=
by { dsimp [ι, lift], simp }

@[simp, reassoc]
lemma condition_π' : kernel.lift g f w ≫ π' f g w = 0 :=
by { dsimp [π'], simp }

@[simp, reassoc]
lemma condition_ι : ι f g w ≫ cokernel.desc f g w = 0 :=
by { dsimp [ι], simp }

@[ext]
lemma hom_from_ext {W : A} (a b : homology f g w ⟶ W)
  (h : π' f g w ≫ a = π' f g w ≫ b) : a = b :=
begin
  dsimp [π'] at h,
  apply_fun (λ e, (homology_iso_cokernel_lift f g w).inv ≫ e),
  swap,
  { intros i j hh,
    apply_fun (λ e, (homology_iso_cokernel_lift f g w).hom ≫ e) at hh,
    simpa using hh },
  simp only [category.assoc] at h,
  exact coequalizer.hom_ext h,
end

@[ext]
lemma hom_to_ext {W : A} (a b : W ⟶ homology f g w)
  (h : a ≫ ι f g w = b ≫ ι f g w) : a = b :=
begin
  dsimp [ι] at h,
  apply_fun (λ e, e ≫ (homology_iso_kernel_desc f g w).hom),
  swap,
  { intros i j hh,
    apply_fun (λ e, e ≫ (homology_iso_kernel_desc f g w).inv) at hh,
    simpa using hh },
  simp only [← category.assoc] at h,
  exact equalizer.hom_ext h,
end

@[simp, reassoc]
lemma π'_ι : π' f g w ≫ ι f g w = kernel.ι _ ≫ cokernel.π _ :=
by { dsimp [π', ι, homology_iso_kernel_desc], simp }

@[simp, reassoc]
lemma π'_eq_π : (kernel_subobject_iso _).hom ≫ π' f g w = π _ _ _ :=
begin
  dsimp [π', homology_iso_cokernel_lift],
  simp only [← category.assoc],
  rw iso.comp_inv_eq,
  dsimp [π, homology_iso_cokernel_image_to_kernel'],
  simp,
end

section

variables {X' Y' Z' : A} (f' : X' ⟶ Y') (g' : Y' ⟶ Z') (w' : f' ≫ g' = 0)

@[simp, reassoc]
lemma π'_map (α β h) :
  π' _ _ _ ≫ map w w' α β h = kernel.map _ _ α.right β.right (by simp [h,β.w.symm]) ≫ π' _ _ _ :=
begin
  apply_fun (λ e, (kernel_subobject_iso _).hom ≫ e),
  swap,
  { intros i j hh,
    apply_fun (λ e, (kernel_subobject_iso _).inv ≫ e) at hh,
    simpa using hh },
  dsimp [map],
  simp only [π'_eq_π_assoc],
  dsimp [π],
  simp only [cokernel.π_desc],
  rw [← iso.inv_comp_eq, ← category.assoc],
  have : (limits.kernel_subobject_iso g).inv ≫ limits.kernel_subobject_map β =
    kernel.map _ _ β.left β.right β.w.symm ≫ (kernel_subobject_iso _).inv,
  { rw [iso.inv_comp_eq, ← category.assoc, iso.eq_comp_inv],
    ext,
    dsimp,
    simp },
  rw this,
  simp only [category.assoc],
  dsimp [π', homology_iso_cokernel_lift],
  simp only [cokernel_iso_of_eq_inv_comp_desc, cokernel.π_desc_assoc],
  congr' 1,
  { congr, exact h.symm },
  { rw [iso.inv_comp_eq, ← category.assoc, iso.eq_comp_inv],
    dsimp [homology_iso_cokernel_image_to_kernel'],
    simp }
end

lemma map_eq_desc'_lift_left (α β h) : map w w' α β h =
  homology.desc' _ _ _ (homology.lift _ _ _ (kernel.ι _ ≫ β.left ≫ cokernel.π _) (by simp))
  (by { ext, simp only [←h, category.assoc, zero_comp, lift_ι, kernel.lift_ι_assoc],
    erw ← reassoc_of α.w, simp } ) :=
begin
  apply homology.hom_from_ext,
  simp only [π'_map, π'_desc'],
  dsimp [π', lift],
  rw iso.eq_comp_inv,
  dsimp [homology_iso_kernel_desc],
  ext,
  simp [h],
end

lemma map_eq_lift_desc'_left (α β h) : map w w' α β h =
  homology.lift _ _ _ (homology.desc' _ _ _ (kernel.ι _ ≫ β.left ≫ cokernel.π _)
  (by { simp only [kernel.lift_ι_assoc, ← h], erw ← reassoc_of α.w, simp }))
  (by { ext, simp }) :=
by { rw map_eq_desc'_lift_left, ext, simp }

lemma map_eq_desc'_lift_right (α β h) : map w w' α β h =
  homology.desc' _ _ _ (homology.lift _ _ _ (kernel.ι _ ≫ α.right ≫ cokernel.π _) (by simp [h]))
  (by { ext, simp only [category.assoc, zero_comp, lift_ι, kernel.lift_ι_assoc],
    erw ← reassoc_of α.w, simp } ) :=
by { rw map_eq_desc'_lift_left, ext, simp [h] }

lemma map_eq_lift_desc'_right (α β h) : map w w' α β h =
  homology.lift _ _ _ (homology.desc' _ _ _ (kernel.ι _ ≫ α.right ≫ cokernel.π _)
  (by { simp only [kernel.lift_ι_assoc], erw ← reassoc_of α.w, simp }))
  (by { ext, simp [h] }) :=
by { rw map_eq_desc'_lift_right, ext, simp }

@[simp, reassoc]
lemma map_ι (α β h) :
  map w w' α β h ≫ ι f' g' w' = ι f g w ≫ cokernel.map f f' α.left β.left (by simp [h, β.w.symm]) :=
begin
  rw [map_eq_lift_desc'_left, lift_ι],
  ext,
  simp only [← category.assoc],
  rw [π'_ι, π'_desc', category.assoc, category.assoc, cokernel.π_desc],
end

end
end homology

namespace category_theory.functor

variables {ι : Type*} {c : complex_shape ι} {B : Type*} [category B] [abelian B] (F : A ⥤ B)
  [functor.additive F] [preserves_finite_limits F] [preserves_finite_colimits F]

/-- When `F` is an exact additive functor, `F(Hᵢ(X)) ≅ Hᵢ(F(X))` for `X` a complex. -/
noncomputable def homology_iso (C : homological_complex A c) (j : ι) :
  F.obj (C.homology j) ≅ ((F.map_homological_complex _).obj C).homology j :=
(preserves_cokernel.iso _ _).trans (cokernel.map_iso _ _ ((F.map_iso (image_subobject_iso _)).trans
  ((preserves_image.iso _ _).symm.trans (image_subobject_iso _).symm))
  ((F.map_iso (kernel_subobject_iso _)).trans ((preserves_kernel.iso _ _).trans
  (kernel_subobject_iso _).symm))
  begin
    dsimp,
    ext,
    simp only [category.assoc, image_to_kernel_arrow],
    erw [kernel_subobject_arrow', kernel_comparison_comp_ι, image_subobject_arrow'],
    simp [←F.map_comp],
  end)

/-- If `F` is an exact additive functor, then `F` commutes with `Hᵢ` (up to natural isomorphism). -/
noncomputable def homology_functor_iso (i : ι) :
  homology_functor A c i ⋙ F ≅ F.map_homological_complex c ⋙ homology_functor B c i :=
nat_iso.of_components (λ X, homology_iso F X i)
begin
  intros X Y f,
  dsimp,
  rw [←iso.inv_comp_eq, ←category.assoc, ←iso.eq_comp_inv],
  refine coequalizer.hom_ext _,
  dsimp [homology_iso],
  simp only [homology.map, ←category.assoc, cokernel.π_desc],
  simp only [category.assoc, cokernel_comparison_map_desc, cokernel.π_desc,
    π_comp_cokernel_comparison, ←F.map_comp],
  erw ←kernel_subobject_iso_comp_kernel_map_assoc,
  simp only [homological_complex.hom.sq_from_right,
    homological_complex.hom.sq_from_left, F.map_homological_complex_map_f, F.map_comp],
  dunfold homological_complex.d_from homological_complex.hom.next,
  dsimp,
  rw [kernel_map_comp_preserves_kernel_iso_inv_assoc, ←F.map_comp_assoc,
    ←kernel_map_comp_kernel_subobject_iso_inv],
  any_goals { simp },
end

end category_theory.functor

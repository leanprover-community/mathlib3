/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import algebra.homology.image_to_kernel

/-!
# Exact sequences

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In a category with zero morphisms, images, and equalizers we say that `f : A ⟶ B` and `g : B ⟶ C`
are exact if `f ≫ g = 0` and the natural map `image f ⟶ kernel g` is an epimorphism.

In any preadditive category this is equivalent to the homology at `B` vanishing.

However in general it is weaker than other reasonable definitions of exactness,
particularly that
1. the inclusion map `image.ι f` is a kernel of `g` or
2. `image f ⟶ kernel g` is an isomorphism or
3. `image_subobject f = kernel_subobject f`.
However when the category is abelian, these all become equivalent;
these results are found in `category_theory/abelian/exact.lean`.

# Main results
* Suppose that cokernels exist and that `f` and `g` are exact.
  If `s` is any kernel fork over `g` and `t` is any cokernel cofork over `f`,
  then `fork.ι s ≫ cofork.π t = 0`.
* Precomposing the first morphism with an epimorphism retains exactness.
  Postcomposing the second morphism with a monomorphism retains exactness.
* If `f` and `g` are exact and `i` is an isomorphism,
  then `f ≫ i.hom` and `i.inv ≫ g` are also exact.

# Future work
* Short exact sequences, split exact sequences, the splitting lemma (maybe only for abelian
  categories?)
* Two adjacent maps in a chain complex are exact iff the homology vanishes

-/

universes v v₂ u u₂

open category_theory
open category_theory.limits

variables {V : Type u} [category.{v} V]
variables [has_images V]

namespace category_theory

/--
Two morphisms `f : A ⟶ B`, `g : B ⟶ C` are called exact if `w : f ≫ g = 0` and the natural map
`image_to_kernel f g w : image_subobject f ⟶ kernel_subobject g` is an epimorphism.

In any preadditive category, this is equivalent to `w : f ≫ g = 0` and `homology f g w ≅ 0`.

In an abelian category, this is equivalent to `image_to_kernel f g w` being an isomorphism,
and hence equivalent to the usual definition,
`image_subobject f = kernel_subobject g`.
-/
-- One nice feature of this definition is that we have
-- `epi f → exact g h → exact (f ≫ g) h` and `exact f g → mono h → exact f (g ≫ h)`,
-- which do not necessarily hold in a non-abelian category with the usual definition of `exact`.
structure exact [has_zero_morphisms V] [has_kernels V] {A B C : V} (f : A ⟶ B) (g : B ⟶ C) : Prop :=
(w : f ≫ g = 0)
(epi : epi (image_to_kernel f g w))

-- This works as an instance even though `exact` itself is not a class, as long as the goal is
-- literally of the form `epi (image_to_kernel f g h.w)` (where `h : exact f g`). If the proof of
-- `f ≫ g = 0` looks different, we are out of luck and have to add the instance by hand.
attribute [instance] exact.epi
attribute [reassoc] exact.w

section
variables [has_zero_object V] [preadditive V] [has_kernels V] [has_cokernels V]
open_locale zero_object

/--
In any preadditive category,
composable morphisms `f g` are exact iff they compose to zero and the homology vanishes.
-/
lemma preadditive.exact_iff_homology_zero {A B C : V} (f : A ⟶ B) (g : B ⟶ C) :
  exact f g ↔ ∃ w : f ≫ g = 0, nonempty (homology f g w ≅ 0) :=
⟨λ h, ⟨h.w, ⟨cokernel.of_epi _⟩⟩,
  λ h, begin
    obtain ⟨w, ⟨i⟩⟩ := h,
    exact ⟨w, preadditive.epi_of_cokernel_zero ((cancel_mono i.hom).mp (by ext))⟩,
  end⟩

lemma preadditive.exact_of_iso_of_exact {A₁ B₁ C₁ A₂ B₂ C₂ : V}
  (f₁ : A₁ ⟶ B₁) (g₁ : B₁ ⟶ C₁) (f₂ : A₂ ⟶ B₂) (g₂ : B₂ ⟶ C₂)
  (α : arrow.mk f₁ ≅ arrow.mk f₂) (β : arrow.mk g₁ ≅ arrow.mk g₂) (p : α.hom.right = β.hom.left)
  (h : exact f₁ g₁) :
  exact f₂ g₂ :=
begin
  rw preadditive.exact_iff_homology_zero at h ⊢,
  rcases h with ⟨w₁, ⟨i⟩⟩,
  suffices w₂ : f₂ ≫ g₂ = 0, from ⟨w₂, ⟨(homology.map_iso w₁ w₂ α β p).symm.trans i⟩⟩,
  rw [← cancel_epi α.hom.left, ← cancel_mono β.inv.right, comp_zero, zero_comp, ← w₁],
  simp only [← arrow.mk_hom f₁, ← arrow.left_hom_inv_right α.hom,
      ← arrow.mk_hom g₁, ← arrow.left_hom_inv_right β.hom, p],
  simp only [arrow.mk_hom, is_iso.inv_hom_id_assoc, category.assoc, ← arrow.inv_right,
    is_iso.iso.inv_hom]
end

/-- A reformulation of `preadditive.exact_of_iso_of_exact` that does not involve the arrow
category. -/
lemma preadditive.exact_of_iso_of_exact' {A₁ B₁ C₁ A₂ B₂ C₂ : V}
  (f₁ : A₁ ⟶ B₁) (g₁ : B₁ ⟶ C₁) (f₂ : A₂ ⟶ B₂) (g₂ : B₂ ⟶ C₂)
  (α : A₁ ≅ A₂) (β : B₁ ≅ B₂) (γ : C₁ ≅ C₂) (hsq₁ : α.hom ≫ f₂ = f₁ ≫ β.hom)
  (hsq₂ : β.hom ≫ g₂ = g₁ ≫ γ.hom)
  (h : exact f₁ g₁) :
  exact f₂ g₂ :=
preadditive.exact_of_iso_of_exact f₁ g₁ f₂ g₂ (arrow.iso_mk α β hsq₁) (arrow.iso_mk β γ hsq₂) rfl h

lemma preadditive.exact_iff_exact_of_iso {A₁ B₁ C₁ A₂ B₂ C₂ : V}
  (f₁ : A₁ ⟶ B₁) (g₁ : B₁ ⟶ C₁) (f₂ : A₂ ⟶ B₂) (g₂ : B₂ ⟶ C₂)
  (α : arrow.mk f₁ ≅ arrow.mk f₂) (β : arrow.mk g₁ ≅ arrow.mk g₂) (p : α.hom.right = β.hom.left) :
  exact f₁ g₁ ↔ exact f₂ g₂ :=
⟨preadditive.exact_of_iso_of_exact _ _ _ _ _ _ p,
preadditive.exact_of_iso_of_exact _ _ _ _ α.symm β.symm
  begin
    rw ← cancel_mono α.hom.right,
    simp only [iso.symm_hom, ← comma.comp_right, α.inv_hom_id],
    simp only [p, ←comma.comp_left, arrow.id_right, arrow.id_left, iso.inv_hom_id],
    refl
  end⟩

end

section
variables [has_zero_morphisms V] [has_kernels V]

lemma comp_eq_zero_of_image_eq_kernel {A B C : V} (f : A ⟶ B) (g : B ⟶ C)
  (p : image_subobject f = kernel_subobject g) : f ≫ g = 0 :=
begin
  rw [←image_subobject_arrow_comp f, category.assoc],
  convert comp_zero,
  rw p,
  simp,
end

lemma image_to_kernel_is_iso_of_image_eq_kernel {A B C : V} (f : A ⟶ B) (g : B ⟶ C)
  (p : image_subobject f = kernel_subobject g) :
  is_iso (image_to_kernel f g (comp_eq_zero_of_image_eq_kernel f g p)) :=
begin
  refine ⟨⟨subobject.of_le _ _ p.ge, _⟩⟩,
  dsimp [image_to_kernel],
  simp only [subobject.of_le_comp_of_le, subobject.of_le_refl],
  simp,
end

-- We'll prove the converse later, when `V` is abelian.
lemma exact_of_image_eq_kernel {A B C : V} (f : A ⟶ B) (g : B ⟶ C)
  (p : image_subobject f = kernel_subobject g) : exact f g :=
{ w := comp_eq_zero_of_image_eq_kernel f g p,
  epi := begin
    haveI := image_to_kernel_is_iso_of_image_eq_kernel f g p,
    apply_instance,
  end }

end

variables {A B C D : V} {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D}
local attribute [instance] epi_comp

section
variables [has_zero_morphisms V] [has_equalizers V]

lemma exact_comp_hom_inv_comp (i : B ≅ D) (h : exact f g) : exact (f ≫ i.hom) (i.inv ≫ g) :=
begin
  refine ⟨by simp [h.w], _⟩,
  rw image_to_kernel_comp_hom_inv_comp,
  haveI := h.epi,
  apply_instance,
end

lemma exact_comp_inv_hom_comp (i : D ≅ B) (h : exact f g) : exact (f ≫ i.inv) (i.hom ≫ g) :=
exact_comp_hom_inv_comp i.symm h

lemma exact_comp_hom_inv_comp_iff (i : B ≅ D) : exact (f ≫ i.hom) (i.inv ≫ g) ↔ exact f g :=
⟨λ h, by simpa using exact_comp_inv_hom_comp i h, exact_comp_hom_inv_comp i⟩

lemma exact_epi_comp (hgh : exact g h) [epi f] : exact (f ≫ g) h :=
begin
  refine ⟨by simp [hgh.w], _⟩,
  rw image_to_kernel_comp_left,
  apply_instance,
end

@[simp]
lemma exact_iso_comp [is_iso f] : exact (f ≫ g) h ↔ exact g h :=
⟨λ w, by { rw ←is_iso.inv_hom_id_assoc f g, exact exact_epi_comp w }, λ w, exact_epi_comp w⟩

lemma exact_comp_mono (hfg : exact f g) [mono h] : exact f (g ≫ h) :=
begin
  refine ⟨by simp [hfg.w_assoc], _⟩,
  rw image_to_kernel_comp_right f g h hfg.w,
  apply_instance,
end

/-- The dual of this lemma is only true when `V` is abelian, see `abelian.exact_epi_comp_iff`. -/
lemma exact_comp_mono_iff [mono h] : exact f (g ≫ h) ↔ exact f g :=
begin
  refine ⟨λ hfg, ⟨zero_of_comp_mono h (by rw [category.assoc, hfg.1]), _⟩, λ h, exact_comp_mono h⟩,
  rw ← (iso.eq_comp_inv _).1 (image_to_kernel_comp_mono _ _ h hfg.1),
  haveI := hfg.2, apply_instance
end

@[simp]
lemma exact_comp_iso [is_iso h] : exact f (g ≫ h) ↔ exact f g :=
exact_comp_mono_iff

lemma exact_kernel_subobject_arrow : exact (kernel_subobject f).arrow f :=
begin
  refine ⟨by simp, _⟩,
  apply @is_iso.epi_of_iso _ _ _ _ _ _,
  exact ⟨⟨factor_thru_image_subobject _, by { ext, simp, }, by { ext, simp, }⟩⟩,
end

lemma exact_kernel_ι : exact (kernel.ι f) f :=
by { rw [←kernel_subobject_arrow', exact_iso_comp], exact exact_kernel_subobject_arrow }

instance (h : exact f g) : epi (factor_thru_kernel_subobject g f h.w) :=
begin
  rw ←factor_thru_image_subobject_comp_image_to_kernel,
  apply epi_comp,
end

instance (h : exact f g) : epi (kernel.lift g f h.w) :=
begin
  rw ←factor_thru_kernel_subobject_comp_kernel_subobject_iso,
  apply epi_comp
end

variables (A)

lemma kernel_subobject_arrow_eq_zero_of_exact_zero_left (h : exact (0 : A ⟶ B) g) :
  (kernel_subobject g).arrow = 0 :=
begin
  rw [←cancel_epi (image_to_kernel (0 : A ⟶ B) g h.w),
    ←cancel_epi (factor_thru_image_subobject (0 : A ⟶ B))],
  simp
end

lemma kernel_ι_eq_zero_of_exact_zero_left (h : exact (0 : A ⟶ B) g) :
  kernel.ι g = 0 :=
by { rw ←kernel_subobject_arrow', simp [kernel_subobject_arrow_eq_zero_of_exact_zero_left A h], }

lemma exact_zero_left_of_mono [has_zero_object V] [mono g] : exact (0 : A ⟶ B) g :=
⟨by simp, image_to_kernel_epi_of_zero_of_mono _⟩

end

section has_cokernels
variables [has_zero_morphisms V] [has_equalizers V] [has_cokernels V] (f g)

@[simp, reassoc] lemma kernel_comp_cokernel (h : exact f g) : kernel.ι g ≫ cokernel.π f = 0 :=
begin
  rw [←kernel_subobject_arrow', category.assoc],
  convert comp_zero,
  apply zero_of_epi_comp (image_to_kernel f g h.w) _,
  rw [image_to_kernel_arrow_assoc, ←image_subobject_arrow, category.assoc, ←iso.eq_inv_comp],
  ext,
  simp,
end

lemma comp_eq_zero_of_exact (h : exact f g) {X Y : V} {ι : X ⟶ B} (hι : ι ≫ g = 0) {π : B ⟶ Y}
  (hπ : f ≫ π = 0) : ι ≫ π = 0 :=
by rw [←kernel.lift_ι _ _ hι, ←cokernel.π_desc _ _ hπ, category.assoc,
  kernel_comp_cokernel_assoc _ _ h, zero_comp, comp_zero]

@[simp, reassoc] lemma fork_ι_comp_cofork_π (h : exact f g) (s : kernel_fork g)
  (t : cokernel_cofork f) : fork.ι s ≫ cofork.π t = 0 :=
comp_eq_zero_of_exact f g h (kernel_fork.condition s) (cokernel_cofork.condition t)

end has_cokernels

section
variables [has_zero_object V]

open_locale zero_object

section
variables [has_zero_morphisms V] [has_kernels V]

lemma exact_of_zero {A C : V} (f : A ⟶ 0) (g : 0 ⟶ C) : exact f g :=
begin
  obtain rfl : f = 0 := by ext,
  obtain rfl : g = 0 := by ext,
  fsplit,
  { simp, },
  { exact image_to_kernel_epi_of_zero_of_mono 0, },
end

lemma exact_zero_mono {B C : V} (f : B ⟶ C) [mono f] : exact (0 : (0 ⟶ B)) f :=
⟨by simp, infer_instance⟩

lemma exact_epi_zero {A B : V} (f : A ⟶ B) [epi f] : exact f (0 : (B ⟶ 0)) :=
⟨by simp, infer_instance⟩

end

section
variables [preadditive V]

lemma mono_iff_exact_zero_left [has_kernels V] {B C : V} (f : B ⟶ C) :
  mono f ↔ exact (0 : (0 ⟶ B)) f :=
⟨λ h, by exactI exact_zero_mono _,
  λ h, preadditive.mono_of_kernel_iso_zero
      ((kernel_subobject_iso f).symm ≪≫ iso_zero_of_epi_zero (by simpa using h.epi))⟩

lemma epi_iff_exact_zero_right [has_equalizers V] {A B : V} (f : A ⟶ B) :
  epi f ↔ exact f (0 : (B ⟶ 0)) :=
⟨λ h, by exactI exact_epi_zero _,
  λ h, begin
    have e₁ := h.epi,
    rw image_to_kernel_zero_right at e₁,
    have e₂ : epi (((image_subobject f).arrow ≫ inv (kernel_subobject 0).arrow) ≫
      (kernel_subobject 0).arrow) := @epi_comp _ _ _ _ _ _ e₁ _ _,
    rw [category.assoc, is_iso.inv_hom_id, category.comp_id] at e₂,
    rw [←image_subobject_arrow] at e₂,
    resetI,
    haveI : epi (image.ι f) := epi_of_epi (image_subobject_iso f).hom (image.ι f),
    apply epi_of_epi_image,
  end⟩

end

end

namespace functor
variables [has_zero_morphisms V] [has_kernels V] {W : Type u₂} [category.{v₂} W]
variables [has_images W] [has_zero_morphisms W] [has_kernels W]

/-- A functor reflects exact sequences if any composable pair of morphisms that is mapped to an
    exact pair is itself exact. -/
class reflects_exact_sequences (F : V ⥤ W) :=
(reflects : ∀ {A B C : V} (f : A ⟶ B) (g : B ⟶ C), exact (F.map f) (F.map g) → exact f g)

lemma exact_of_exact_map (F : V ⥤ W) [reflects_exact_sequences F] {A B C : V} {f : A ⟶ B}
  {g : B ⟶ C} (hfg : exact (F.map f) (F.map g)) : exact f g :=
reflects_exact_sequences.reflects f g hfg

end functor

end category_theory

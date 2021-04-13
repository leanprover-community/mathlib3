/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.homology2.homological_complex
import category_theory.subobject.specific_objects

universes v u

open category_theory category_theory.limits

variables {ι : Type*}
variables {V : Type u} [category.{v} V] [has_zero_morphisms V]

open_locale classical
noncomputable theory

section
variables {A B C : V} (f : A ⟶ B) [has_image f] (g : B ⟶ C) [has_kernel g]

lemma image_le_kernel (w : f ≫ g = 0) :
  image_subobject f ≤ kernel_subobject g :=
image_subobject_le_mk _ _ (kernel.lift _ _ w) (by simp)

def image_to_kernel (w : f ≫ g = 0) :
  (image_subobject f : V) ⟶ (kernel_subobject g : V) :=
(subobject.of_le _ _ (image_le_kernel _ _ w))

/-- Prefer `image_to_kernel`. -/
@[simp] lemma subobject_of_le_as_image_to_kernel (w : f ≫ g = 0) (h) :
  subobject.of_le (image_subobject f) (kernel_subobject g) h = image_to_kernel f g w :=
rfl

@[simp, reassoc]
lemma image_to_kernel_arrow (w : f ≫ g = 0) :
  image_to_kernel f g w ≫ (kernel_subobject g).arrow = (image_subobject f).arrow :=
by simp [image_to_kernel]

end

section
variables [has_images V] [has_equalizers V]
variables {A B C : V} (f : A ⟶ B) (g : B ⟶ C)

@[simp]
lemma image_to_kernel_zero_left [has_zero_object V] {w} :
  image_to_kernel (0 : A ⟶ B) g w = 0 :=
by { ext, simp, }

lemma image_to_kernel_zero_right {w} :
  image_to_kernel f (0 : B ⟶ C) w =
    (image_subobject f).arrow ≫ inv (kernel_subobject (0 : B ⟶ C)).arrow :=
by { ext, simp }

lemma image_to_kernel_comp_right {D : V} (h : C ⟶ D) (w : f ≫ g = 0) :
  image_to_kernel f (g ≫ h) (by simp [reassoc_of w]) =
    image_to_kernel f g w ≫ subobject.of_le _ _ (kernel_subobject_comp_le g h) :=
by { ext, simp }

lemma image_to_kernel_comp_left {Z : V} (h : Z ⟶ A) (w : f ≫ g = 0) :
  image_to_kernel (h ≫ f) g (by simp [w]) =
    subobject.of_le _ _ (image_subobject_comp_le h f) ≫ image_to_kernel f g w :=
by { ext, simp }

@[simp]
lemma image_to_kernel_comp_mono {D : V} (h : C ⟶ D) [mono h] (w) :
  image_to_kernel f (g ≫ h) w =
  image_to_kernel f g ((cancel_mono h).mp (by simpa using w : (f ≫ g) ≫ h = 0 ≫ h)) ≫
    (subobject.iso_of_eq _ _ (kernel_subobject_comp_mono g h)).inv :=
by { ext, simp, }

@[simp]
lemma image_to_kernel_epi_comp {Z : V} (h : Z ⟶ A) [epi h] (w) :
  image_to_kernel (h ≫ f) g w =
  subobject.of_le _ _ (image_subobject_comp_le h f) ≫
    image_to_kernel f g ((cancel_epi h).mp (by simpa using w : h ≫ f ≫ g = h ≫ 0)) :=
by { ext, simp, }

@[simp]
lemma image_to_kernel_comp_hom_inv_comp {Z : V} {i : B ≅ Z} (w) :
  image_to_kernel (f ≫ i.hom) (i.inv ≫ g) w =
  begin end ≫ image_to_kernel f g (by simpa using w) ≫
    begin end :=
by { ext, simp }

local attribute [instance] has_zero_object.has_zero

/--
`image_to_kernel` for `A --0--> B --g--> C`, where `g` is a mono is itself an epi
(i.e. the sequence is exact at `B`).
-/
lemma image_to_kernel_epi_of_zero_of_mono [mono g] [has_zero_object V] :
  epi (image_to_kernel (0 : A ⟶ B) g (by simp)) :=
epi_of_target_iso_zero _ (kernel.of_mono g)

/--
`image_to_kernel` for `A --f--> B --0--> C`, where `g` is an epi is itself an epi
(i.e. the sequence is exact at `B`).
-/
lemma image_to_kernel_epi_of_epi_of_zero [epi f] :
  epi (image_to_kernel f (0 : B ⟶ C) (by simp)) :=
begin
  simp only [image_to_kernel_zero_right],
  haveI := epi_image_of_epi f,
  apply epi_comp,
end

end

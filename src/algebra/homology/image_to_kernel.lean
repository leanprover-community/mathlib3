/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.subobject.limits

/-!
# Image-to-kernel comparison maps

Whenever `f : A ⟶ B` and `g : B ⟶ C` satisfy `w : f ≫ g = 0`,
we have `image_le_kernel f g w : image_subobject f ≤ kernel_subobject g`
(assuming the appropriate images and kernels exist).

`image_to_kernel f g w` is the corresponding morphism between objects in `C`.

We define `homology f g w` of such a pair as the cokernel of `image_to_kernel f g w`.
-/

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

/--
The canonical morphism `image_subobject f ⟶ kernel_subobject g` when `f ≫ g = 0`.
-/
@[derive mono]
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

-- This is less useful as a `simp` lemma than it initially appears,
-- as it "loses" the information the morphism factors through the image.
lemma factor_thru_image_subobject_comp_image_to_kernel (w : f ≫ g = 0) :
  factor_thru_image_subobject f ≫ image_to_kernel f g w = factor_thru_kernel_subobject g f w :=
by { ext, simp, }

end

section
variables {A B C : V} (f : A ⟶ B) (g : B ⟶ C)

@[simp]
lemma image_to_kernel_zero_left [has_kernels V] [has_zero_object V] {w} :
  image_to_kernel (0 : A ⟶ B) g w = 0 :=
by { ext, simp, }

lemma image_to_kernel_zero_right [has_images V] {w} :
  image_to_kernel f (0 : B ⟶ C) w =
    (image_subobject f).arrow ≫ inv (kernel_subobject (0 : B ⟶ C)).arrow :=
by { ext, simp }

section
variables [has_kernels V] [has_images V]

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

end

@[simp]
lemma image_to_kernel_comp_hom_inv_comp [has_equalizers V] [has_images V] {Z : V} {i : B ≅ Z} (w) :
  image_to_kernel (f ≫ i.hom) (i.inv ≫ g) w =
  (image_subobject_comp_iso _ _).hom ≫ image_to_kernel f g (by simpa using w) ≫
    (kernel_subobject_iso_comp i.inv g).inv :=
by { ext, simp, }

open_locale zero_object

/--
`image_to_kernel` for `A --0--> B --g--> C`, where `g` is a mono is itself an epi
(i.e. the sequence is exact at `B`).
-/
instance image_to_kernel_epi_of_zero_of_mono [has_kernels V] [has_zero_object V] [mono g] :
  epi (image_to_kernel (0 : A ⟶ B) g (by simp)) :=
epi_of_target_iso_zero _ (kernel_subobject_iso g ≪≫ kernel.of_mono g)

/--
`image_to_kernel` for `A --f--> B --0--> C`, where `g` is an epi is itself an epi
(i.e. the sequence is exact at `B`).
-/
instance image_to_kernel_epi_of_epi_of_zero [has_images V] [epi f] :
  epi (image_to_kernel f (0 : B ⟶ C) (by simp)) :=
begin
  simp only [image_to_kernel_zero_right],
  haveI := epi_image_of_epi f,
  rw ←image_subobject_arrow,
  refine @epi_comp _ _ _ _ _ _ (epi_comp _ _) _ _,
end

end

section
variables {A B C : V} (f : A ⟶ B) [has_image f] (g : B ⟶ C) [has_kernel g]

/--
The homology of a pair of morphisms `f : A ⟶ B` and `g : B ⟶ C` satisfying `f ≫ g = 0`
is the cokernel of the `image_to_kernel` morphism for `f` and `g`.
-/
def homology {A B C : V} (f : A ⟶ B) [has_image f] (g : B ⟶ C) [has_kernel g]
  (w : f ≫ g = 0) [has_cokernel (image_to_kernel f g w)] : V :=
cokernel (image_to_kernel f g w)

section
variables (w : f ≫ g = 0) [has_cokernel (image_to_kernel f g w)]

/-- The morphism from cycles to homology. -/
def homology.π : (kernel_subobject g : V) ⟶ homology f g w :=
cokernel.π _

@[simp] lemma homology.condition : image_to_kernel f g w ≫ homology.π f g w = 0 :=
cokernel.condition _

/--
To construct a map out of homology, it suffices to construct a map out of the cycles
which vanishes on boundaries.
-/
def homology.desc {D : V} (k : (kernel_subobject g : V) ⟶ D) (p : image_to_kernel f g w ≫ k = 0) :
  homology f g w ⟶ D :=
cokernel.desc _ k p

@[simp, reassoc]
lemma homology.π_desc
  {D : V} (k : (kernel_subobject g : V) ⟶ D) (p : image_to_kernel f g w ≫ k = 0) :
  homology.π f g w ≫ homology.desc f g w k p = k :=
by { simp [homology.π, homology.desc], }

/-- To check two morphisms out of `homology f g w` are equal, it suffices to check on cycles. -/
@[ext]
lemma homology.ext {D : V} {k k' : homology f g w ⟶ D}
  (p : homology.π f g w ≫ k = homology.π f g w ≫ k') : k = k' :=
by { ext, exact p, }

/-- `homology 0 0 _` is just the middle object. -/
@[simps]
def homology_zero_zero [has_zero_object V]
  [has_image (0 : A ⟶ B)] [has_cokernel (image_to_kernel (0 : A ⟶ B) (0 : B ⟶ C) (by simp))] :
  homology (0 : A ⟶ B) (0 : B ⟶ C) (by simp) ≅ B :=
{ hom := homology.desc (0 : A ⟶ B) (0 : B ⟶ C) (by simp) (kernel_subobject 0).arrow (by simp),
  inv := inv (kernel_subobject 0).arrow ≫ homology.π _ _ _, }

end

section
variables {f g} (w : f ≫ g = 0)
  {A' B' C' : V} {f' : A' ⟶ B'} [has_image f'] {g' : B' ⟶ C'} [has_kernel g'] (w' : f' ≫ g' = 0)
  (α : arrow.mk f ⟶ arrow.mk f') [has_image_map α] (β : arrow.mk g ⟶ arrow.mk g')

/--
Given compatible commutative squares between
a pair `f g` and a pair `f' g'` satisfying `f ≫ g = 0` and `f' ≫ g' = 0`,
the `image_to_kernel` morphisms intertwine the induced map on kernels and the induced map on images.
-/
@[reassoc]
lemma image_subobject_map_comp_image_to_kernel (p : α.right = β.left) :
  image_to_kernel f g w ≫ kernel_subobject_map β =
    image_subobject_map α ≫ image_to_kernel f' g' w' :=
by { ext, simp [p], }

variables [has_cokernel (image_to_kernel f g w)] [has_cokernel (image_to_kernel f' g' w')]

/--
Given compatible commutative squares between
a pair `f g` and a pair `f' g'` satisfying `f ≫ g = 0` and `f' ≫ g' = 0`,
we get a morphism on homology.
-/
def homology.map (p : α.right = β.left) :
  homology f g w ⟶ homology f' g' w' :=
cokernel.desc _ (kernel_subobject_map β ≫ cokernel.π _)
  begin
    rw [image_subobject_map_comp_image_to_kernel_assoc w w' α β p],
    simp,
  end

@[simp, reassoc]
lemma homology.π_map (p : α.right = β.left) :
  homology.π f g w ≫ homology.map w w' α β p = kernel_subobject_map β ≫ homology.π f' g' w' :=
by { simp [homology.π, homology.map], }

@[simp, reassoc]
lemma homology.map_desc (p : α.right = β.left)
  {D : V} (k : (kernel_subobject g' : V) ⟶ D) (z : image_to_kernel f' g' w' ≫ k = 0) :
  homology.map w w' α β p ≫ homology.desc f' g' w' k z =
    homology.desc f g w (kernel_subobject_map β ≫ k)
      (by simp [image_subobject_map_comp_image_to_kernel_assoc w w' α β p, z]) :=
by { ext, simp, }

end

end

section
variables {A B C : V} {f : A ⟶ B} {g : B ⟶ C} (w : f ≫ g = 0)
  {f' : A ⟶ B} {g' : B ⟶ C} (w' : f' ≫ g' = 0)
  [has_kernels V] [has_cokernels V] [has_images V] [has_image_maps V]

/--
`homology f g w ≅ homology f' g' w'` if `f = f'` and `g = g'`.
(Note the objects are not changing here.)
-/
@[simps]
def homology.congr (pf : f = f') (pg : g = g') : homology f g w ≅ homology f' g' w' :=
{ hom := homology.map w w' { left := 𝟙 _, right := 𝟙 _, } { left := 𝟙 _, right := 𝟙 _, } rfl,
  inv := homology.map w' w { left := 𝟙 _, right := 𝟙 _, } { left := 𝟙 _, right := 𝟙 _, } rfl,
  hom_inv_id' := begin
    ext,
    simp_rw [category.comp_id, homology.π_map_assoc, homology.π_map,
      ←category.assoc, ←kernel_subobject_map_comp],
    convert category.id_comp _,
    convert kernel_subobject_map_id,
    ext; simp,
  end,
  inv_hom_id' := begin
    ext,
    simp_rw [category.comp_id, homology.π_map_assoc, homology.π_map,
      ←category.assoc, ←kernel_subobject_map_comp],
    convert category.id_comp _,
    convert kernel_subobject_map_id,
    ext; simp,
  end, }

end

/-!
We provide a variant `image_to_kernel' : image f ⟶ kernel g`,
and use this to give alternative formulas for `homology f g w`.
-/
section image_to_kernel'
variables {A B C : V} (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0)
  [has_kernels V] [has_images V]

/--
While `image_to_kernel f g w` provides a morphism
`image_subobject f ⟶ kernel_subobject g`
in terms of the subobject API,
this variant provides a morphism
`image f ⟶ kernel g`,
which is sometimes more convenient.
-/
def image_to_kernel' (w : f ≫ g = 0) : image f ⟶ kernel g :=
kernel.lift g (image.ι f) (by { ext, simpa using w, })

@[simp] lemma image_subobject_iso_image_to_kernel' (w : f ≫ g = 0) :
  (image_subobject_iso f).hom ≫ image_to_kernel' f g w =
    image_to_kernel f g w ≫ (kernel_subobject_iso g).hom :=
by { ext, simp [image_to_kernel'], }

@[simp] lemma image_to_kernel'_kernel_subobject_iso (w : f ≫ g = 0) :
  image_to_kernel' f g w ≫ (kernel_subobject_iso g).inv =
    (image_subobject_iso f).inv ≫ image_to_kernel f g w :=
by { ext, simp [image_to_kernel'], }

variables [has_cokernels V]

/--
`homology f g w` can be computed as the cokernel of `image_to_kernel' f g w`.
-/
def homology_iso_cokernel_image_to_kernel' (w : f ≫ g = 0) :
  homology f g w ≅ cokernel (image_to_kernel' f g w) :=
{ hom := cokernel.map _ _ (image_subobject_iso f).hom (kernel_subobject_iso g).hom (by tidy),
  inv := cokernel.map _ _ (image_subobject_iso f).inv (kernel_subobject_iso g).inv (by tidy),
  hom_inv_id' := begin
    apply coequalizer.hom_ext,
    simp only [iso.hom_inv_id_assoc, cokernel.π_desc, cokernel.π_desc_assoc, category.assoc,
      coequalizer_as_cokernel],
    exact (category.comp_id _).symm,
  end, }

variables [has_equalizers V]

/--
`homology f g w` can be computed as the cokernel of `kernel.lift g f w`.
-/
def homology_iso_cokernel_lift (w : f ≫ g = 0) :
  homology f g w ≅ cokernel (kernel.lift g f w) :=
begin
  refine homology_iso_cokernel_image_to_kernel' f g w ≪≫ _,
  have p : factor_thru_image f ≫ image_to_kernel' f g w = kernel.lift g f w,
  { ext, simp [image_to_kernel'], },
  exact (cokernel_epi_comp _ _).symm ≪≫ cokernel_iso_of_eq p,
end

end image_to_kernel'

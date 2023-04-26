/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.subobject.limits

/-!
# Image-to-kernel comparison maps

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

@[simp, reassoc, elementwise]
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

@[simp, reassoc, elementwise]
lemma homology.π_desc
  {D : V} (k : (kernel_subobject g : V) ⟶ D) (p : image_to_kernel f g w ≫ k = 0) :
  homology.π f g w ≫ homology.desc f g w k p = k :=
by { simp [homology.π, homology.desc], }

/-- To check two morphisms out of `homology f g w` are equal, it suffices to check on cycles. -/
@[ext]
lemma homology.ext {D : V} {k k' : homology f g w ⟶ D}
  (p : homology.π f g w ≫ k = homology.π f g w ≫ k') : k = k' :=
by { ext, exact p, }

/-- The cokernel of the map `Im f ⟶ Ker 0` is isomorphic to the cokernel of `f.` -/
def homology_of_zero_right [has_cokernel (image_to_kernel f (0 : B ⟶ C) comp_zero)]
  [has_cokernel f] [has_cokernel (image.ι f)] [epi (factor_thru_image f)] :
  homology f (0 : B ⟶ C) comp_zero ≅ cokernel f :=
(cokernel.map_iso _ _ (image_subobject_iso _) ((kernel_subobject_iso 0).trans
  kernel_zero_iso_source) (by simp)).trans (cokernel_image_ι _)

/-- The kernel of the map `Im 0 ⟶ Ker f` is isomorphic to the kernel of `f.` -/
def homology_of_zero_left [has_zero_object V] [has_kernels V] [has_image (0 : A ⟶ B)]
  [has_cokernel (image_to_kernel (0 : A ⟶ B) g zero_comp)] :
  homology (0 : A ⟶ B) g zero_comp ≅ kernel g :=
((cokernel_iso_of_eq $ image_to_kernel_zero_left _).trans cokernel_zero_iso_target).trans
  (kernel_subobject_iso _)

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
  {A₁ B₁ C₁ : V} {f₁ : A₁ ⟶ B₁} [has_image f₁] {g₁ : B₁ ⟶ C₁} [has_kernel g₁] (w₁ : f₁ ≫ g₁ = 0)
  {A₂ B₂ C₂ : V} {f₂ : A₂ ⟶ B₂} [has_image f₂] {g₂ : B₂ ⟶ C₂} [has_kernel g₂] (w₂ : f₂ ≫ g₂ = 0)
  {A₃ B₃ C₃ : V} {f₃ : A₃ ⟶ B₃} [has_image f₃] {g₃ : B₃ ⟶ C₃} [has_kernel g₃] (w₃ : f₃ ≫ g₃ = 0)
  (α₁ : arrow.mk f₁ ⟶ arrow.mk f₂) [has_image_map α₁] (β₁ : arrow.mk g₁ ⟶ arrow.mk g₂)
  (α₂ : arrow.mk f₂ ⟶ arrow.mk f₃) [has_image_map α₂] (β₂ : arrow.mk g₂ ⟶ arrow.mk g₃)

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
variables [has_cokernel (image_to_kernel f₁ g₁ w₁)]
variables [has_cokernel (image_to_kernel f₂ g₂ w₂)]
variables [has_cokernel (image_to_kernel f₃ g₃ w₃)]

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
    simp only [cokernel.condition, comp_zero],
  end

@[simp, reassoc, elementwise]
lemma homology.π_map (p : α.right = β.left) :
  homology.π f g w ≫ homology.map w w' α β p = kernel_subobject_map β ≫ homology.π f' g' w' :=
by simp only [homology.π, homology.map, cokernel.π_desc]

@[simp, reassoc, elementwise]
lemma homology.map_desc (p : α.right = β.left)
  {D : V} (k : (kernel_subobject g' : V) ⟶ D) (z : image_to_kernel f' g' w' ≫ k = 0) :
  homology.map w w' α β p ≫ homology.desc f' g' w' k z =
    homology.desc f g w (kernel_subobject_map β ≫ k)
      (by simp only [image_subobject_map_comp_image_to_kernel_assoc w w' α β p, z, comp_zero]) :=
by ext; simp only [homology.π_desc, homology.π_map_assoc]

@[simp]
lemma homology.map_id : homology.map w w (𝟙 _) (𝟙 _) rfl = 𝟙 _ :=
by ext; simp only [homology.π_map, kernel_subobject_map_id, category.id_comp, category.comp_id]

/-- Auxiliary lemma for homology computations. -/
lemma homology.comp_right_eq_comp_left
  {V : Type*} [category V] {A₁ B₁ C₁ A₂ B₂ C₂ A₃ B₃ C₃ : V}
  {f₁ : A₁ ⟶ B₁} {g₁ : B₁ ⟶ C₁} {f₂ : A₂ ⟶ B₂} {g₂ : B₂ ⟶ C₂} {f₃ : A₃ ⟶ B₃} {g₃ : B₃ ⟶ C₃}
  {α₁ : arrow.mk f₁ ⟶ arrow.mk f₂} {β₁ : arrow.mk g₁ ⟶ arrow.mk g₂}
  {α₂ : arrow.mk f₂ ⟶ arrow.mk f₃} {β₂ : arrow.mk g₂ ⟶ arrow.mk g₃}
  (p₁ : α₁.right = β₁.left) (p₂ : α₂.right = β₂.left) :
  (α₁ ≫ α₂).right = (β₁ ≫ β₂).left :=
by simp only [comma.comp_left, comma.comp_right, p₁, p₂]

@[reassoc]
lemma homology.map_comp (p₁ : α₁.right = β₁.left) (p₂ : α₂.right = β₂.left) :
  homology.map w₁ w₂ α₁ β₁ p₁ ≫ homology.map w₂ w₃ α₂ β₂ p₂ =
    homology.map w₁ w₃ (α₁ ≫ α₂) (β₁ ≫ β₂) (homology.comp_right_eq_comp_left p₁ p₂) :=
by ext; simp only [kernel_subobject_map_comp, homology.π_map_assoc, homology.π_map, category.assoc]

/-- An isomorphism between two three-term complexes induces an isomorphism on homology. -/
def homology.map_iso (α : arrow.mk f₁ ≅ arrow.mk f₂) (β : arrow.mk g₁ ≅ arrow.mk g₂)
  (p : α.hom.right = β.hom.left) :
  homology f₁ g₁ w₁ ≅ homology f₂ g₂ w₂ :=
{ hom := homology.map w₁ w₂ α.hom β.hom p,
  inv := homology.map w₂ w₁ α.inv β.inv
  (by { rw [← cancel_mono (α.hom.right), ← comma.comp_right, α.inv_hom_id, comma.id_right, p,
      ← comma.comp_left, β.inv_hom_id, comma.id_left], refl }),
  hom_inv_id' := by { rw [homology.map_comp], convert homology.map_id _; rw [iso.hom_inv_id] },
  inv_hom_id' := by { rw [homology.map_comp], convert homology.map_id _; rw [iso.inv_hom_id] } }

end

end

section
variables {A B C : V} {f : A ⟶ B} {g : B ⟶ C} (w : f ≫ g = 0)
  {f' : A ⟶ B} {g' : B ⟶ C} (w' : f' ≫ g' = 0)
  [has_kernels V] [has_cokernels V] [has_images V] [has_image_maps V]

/-- Custom tactic to golf and speedup boring proofs in `homology.congr`. -/
private meta def aux_tac : tactic unit :=
`[ dsimp only [auto_param_eq], erw [category.id_comp, category.comp_id], cases pf, cases pg, refl ]

/--
`homology f g w ≅ homology f' g' w'` if `f = f'` and `g = g'`.
(Note the objects are not changing here.)
-/
@[simps]
def homology.congr (pf : f = f') (pg : g = g') : homology f g w ≅ homology f' g' w' :=
{ hom := homology.map w w' ⟨𝟙 _, 𝟙 _, by aux_tac⟩ ⟨𝟙 _, 𝟙 _, by aux_tac⟩ rfl,
  inv := homology.map w' w ⟨𝟙 _, 𝟙 _, by aux_tac⟩ ⟨𝟙 _, 𝟙 _, by aux_tac⟩ rfl,
  hom_inv_id' := begin
    cases pf, cases pg, rw [homology.map_comp, ← homology.map_id],
    congr' 1; exact category.comp_id _,
  end,
  inv_hom_id' := begin
    cases pf, cases pg, rw [homology.map_comp, ← homology.map_id],
    congr' 1; exact category.comp_id _,
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
{ hom := cokernel.map _ _ (image_subobject_iso f).hom (kernel_subobject_iso g).hom
    (by simp only [image_subobject_iso_image_to_kernel']),
  inv := cokernel.map _ _ (image_subobject_iso f).inv (kernel_subobject_iso g).inv
    (by simp only [image_to_kernel'_kernel_subobject_iso]),
  hom_inv_id' := begin
    apply coequalizer.hom_ext,
    simp only [iso.hom_inv_id_assoc, cokernel.π_desc, cokernel.π_desc_assoc, category.assoc,
      coequalizer_as_cokernel],
    exact (category.comp_id _).symm,
  end,
  inv_hom_id' := by { ext1, simp only [iso.inv_hom_id_assoc, cokernel.π_desc, category.comp_id,
    cokernel.π_desc_assoc, category.assoc], } }

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

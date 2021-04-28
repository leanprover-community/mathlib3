/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import algebra.homology.image_to_kernel

/-!
# Exact sequences

In a category with zero morphisms, images, and equalizers we say that `f : A ⟶ B` and `g : B ⟶ C`
are exact if `f ≫ g = 0` and the natural map `image f ⟶ kernel g` is an epimorphism.

In any preadditive category this is equivalent to the homology at `B` vanishing.

However in general it is weaker than other reasonable definitions of exactness,
particularly that
1. the inclusion map `image.ι f` is a kernel of `g` or
2. `image f ⟶ kernel g` is an isomorphism or
3. `image_subobject f = kernel_subobject f`.
However when the cateory is abelian, these all become equivalent;
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

universes v u

open category_theory
open category_theory.limits

variables {V : Type u} [category.{v} V]
variables [has_equalizers V] [has_images V]

namespace category_theory

/--
Two morphisms `f : A ⟶ B`, `g : B ⟶ C` are called exact if `w : f ≫ g = 0` and the natural map
`image_to_kernel f g w : image_subobject f ⟶ kernel_subobject g` is an epimorphism.

In any preadditive category, this is equivalent to `homology f g w ≅ 0`.

In an abelian category, this is equivalent to `image_to_kernel f g w` being an isomorphism,
and hence equivalent to the usual definition,
`image_subobject f = kernel_subobject g`.
-/
-- One nice feature of this definition is that we have
-- `epi f → exact g h → exact (f ≫ g) h` and `exact f g → mono h → exact f (g ≫ h)`,
-- which do not necessarily hold in a non-abelian category with the usual definition of `exact`.
class exact [has_zero_morphisms V] {A B C : V} (f : A ⟶ B) (g : B ⟶ C) : Prop :=
(w : f ≫ g = 0)
(epi : epi (image_to_kernel f g w))

attribute [instance] exact.epi
attribute [simp, reassoc] exact.w

section
variables [has_zero_object V] [preadditive V] [has_cokernels V]
local attribute [instance] has_zero_object.has_zero

/--
In any preadditive category,
composable morphisms `f g` are exact iff the composee to zero and the homology vanishes.
-/
lemma preadditive.exact_iff_homology_zero {A B C : V} (f : A ⟶ B) (g : B ⟶ C) :
  exact f g ↔ ∃ w : f ≫ g = 0, nonempty (homology f g w ≅ 0) :=
⟨λ h, ⟨h.w, ⟨cokernel.of_epi _⟩⟩,
  λ h, begin
    obtain ⟨w, ⟨i⟩⟩ := h,
    exact ⟨w, preadditive.epi_of_cokernel_zero _ ((cancel_mono i.hom).mp (by ext))⟩,
  end⟩

end

variables [has_zero_morphisms V]

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

section
variables {A B C D : V} {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D}

local attribute [instance] epi_comp

instance exact_comp_hom_inv_comp [exact f g] (i : B ≅ D) : exact (f ≫ i.hom) (i.inv ≫ g) :=
begin
  refine ⟨by simp, _⟩,
  rw image_to_kernel_comp_hom_inv_comp,
  apply_instance,
end

instance exact_comp_inv_hom_comp [exact f g] (i : D ≅ B) : exact (f ≫ i.inv) (i.hom ≫ g) :=
category_theory.exact_comp_hom_inv_comp i.symm

lemma exact_comp_hom_inv_comp_iff (i : B ≅ D) : exact (f ≫ i.hom) (i.inv ≫ g) ↔ exact f g :=
begin
  refine ⟨_, by { introI, apply_instance }⟩,
  introI,
  have : exact ((f ≫ i.hom) ≫ i.inv) (i.hom ≫ i.inv ≫ g) := infer_instance,
  simpa using this
end

lemma exact_epi_comp [exact g h] [epi f] : exact (f ≫ g) h :=
begin
  refine ⟨by simp, _⟩,
  rw image_to_kernel_comp_left,
  apply_instance,
end

@[simp]
lemma exact_iso_comp [is_iso f] : exact (f ≫ g) h ↔ exact g h :=
⟨λ w, by { rw ←is_iso.inv_hom_id_assoc f g, exactI exact_epi_comp, }, λ w, by exactI exact_epi_comp⟩

lemma exact_comp_mono [exact f g] [mono h] : exact f (g ≫ h) :=
begin
  refine ⟨by simp, _⟩,
  rw image_to_kernel_comp_right f g h exact.w,
  apply_instance,
end

@[simp]
lemma exact_comp_iso [is_iso h] : exact f (g ≫ h) ↔ exact f g :=
⟨λ w, begin
    rw [←category.comp_id g, ←is_iso.hom_inv_id h, ←category.assoc],
    exactI exact_comp_mono,
  end,
  λ w, by exactI exact_comp_mono⟩

lemma exact_kernel_subobject_arrow : exact (kernel_subobject f).arrow f :=
begin
  refine ⟨by simp, _⟩,
  apply @is_iso.epi_of_iso _ _ _ _ _ _,
  exact ⟨⟨factor_thru_image_subobject _, by { ext, simp, }, by { ext, simp, }⟩⟩,
end

lemma exact_kernel_ι : exact (kernel.ι f) f :=
by { rw [←kernel_subobject_arrow', exact_iso_comp], exact exact_kernel_subobject_arrow }

section
variables (A)

example : epi (factor_thru_image (0 : A ⟶ B)) := factor_thru_image.category_theory.epi 0

lemma kernel_subobject_arrow_eq_zero_of_exact_zero_left [exact (0 : A ⟶ B) g] :
  (kernel_subobject g).arrow = 0 :=
begin
  rw [←cancel_epi (image_to_kernel (0 : A ⟶ B) g exact.w),
    ←cancel_epi (factor_thru_image_subobject (0 : A ⟶ B))],
  simp
end

lemma kernel_ι_eq_zero_of_exact_zero_left [exact (0 : A ⟶ B) g] :
  kernel.ι g = 0 :=
by { rw ←kernel_subobject_arrow', simp [kernel_subobject_arrow_eq_zero_of_exact_zero_left A], }

lemma exact_zero_left_of_mono [has_zero_object V] [mono g] : exact (0 : A ⟶ B) g :=
⟨by simp, image_to_kernel_epi_of_zero_of_mono _⟩

end

end

section has_cokernels
variables [has_cokernels V] {A B C : V} (f : A ⟶ B) (g : B ⟶ C)

@[simp, reassoc] lemma kernel_comp_cokernel [exact f g] : kernel.ι g ≫ cokernel.π f = 0 :=
begin
  rw [←kernel_subobject_arrow', category.assoc],
  convert comp_zero,
  apply zero_of_epi_comp (image_to_kernel f g exact.w) _,
  rw [image_to_kernel_arrow_assoc, ←image_subobject_arrow, category.assoc, ←iso.eq_inv_comp],
  ext,
  simp,
end

lemma comp_eq_zero_of_exact [exact f g] {X Y : V} {ι : X ⟶ B} (hι : ι ≫ g = 0) {π : B ⟶ Y}
  (hπ : f ≫ π = 0) : ι ≫ π = 0 :=
by rw [←kernel.lift_ι _ _ hι, ←cokernel.π_desc _ _ hπ, category.assoc, kernel_comp_cokernel_assoc,
  zero_comp, comp_zero]

@[simp, reassoc] lemma fork_ι_comp_cofork_π [exact f g] (s : kernel_fork g)
  (t : cokernel_cofork f) : fork.ι s ≫ cofork.π t = 0 :=
comp_eq_zero_of_exact f g (kernel_fork.condition s) (cokernel_cofork.condition t)

end has_cokernels

section
local attribute [instance] has_zero_object.has_zero

lemma exact_of_zero [has_zero_object V] {A C : V} (f : A ⟶ 0) (g : 0 ⟶ C) : exact f g :=
begin
  obtain rfl : f = 0 := by ext,
  obtain rfl : g = 0 := by ext,
  fsplit,
  { simp, },
  { exact image_to_kernel_epi_of_zero_of_mono 0, },
end

end

end category_theory

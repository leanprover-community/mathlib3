/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import algebra.homology.short_complex.exact
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

open category_theory category_theory.limits category_theory.category
open_locale zero_object

variables {V : Type u} [category.{v} V]

namespace category_theory

section

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
variable [has_zero_morphisms V]


structure exact {A B C : V} (f : A ⟶ B) (g : B ⟶ C) : Prop :=
(w : f ≫ g = 0)
(exact : (short_complex.mk f g w).exact)

lemma exact.has_homology {A B C : V} {f : A ⟶ B} {g : B ⟶ C} (h : exact f g) :
  (short_complex.mk f g h.w).has_homology :=
h.exact.has_homology

attribute [reassoc] exact.w

section
open_locale zero_object

lemma exact_iff_exact_short_complex {A B C : V}
  (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0) :
  exact f g ↔ (short_complex.mk f g w).exact :=
⟨λ h, h.exact, λ h, ⟨w, h⟩⟩

lemma exact_iff_homology_zero [has_zero_object V] {A B C : V}
  (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0)
  [(short_complex.mk f g w).has_homology] :
  exact f g ↔ nonempty (homology f g w ≅ 0) :=
by rw [exact_iff_exact_short_complex, short_complex.exact_iff_homology_zero]

lemma exact_of_iso_of_exact {A₁ B₁ C₁ A₂ B₂ C₂ : V}
  (f₁ : A₁ ⟶ B₁) (g₁ : B₁ ⟶ C₁) (f₂ : A₂ ⟶ B₂) (g₂ : B₂ ⟶ C₂)
  (α : A₁ ≅ A₂) (β : B₁ ≅ B₂) (γ : C₁ ≅ C₂) (hsq₁ : α.hom ≫ f₂ = f₁ ≫ β.hom)
  (hsq₂ : β.hom ≫ g₂ = g₁ ≫ γ.hom)
  (h : exact f₁ g₁) :
  exact f₂ g₂ :=
begin
  haveI := h.exact.has_homology,
  have w₁ := h.w,
  have w₂ : f₂ ≫ g₂ = 0,
  { simp only [← cancel_epi α.hom, reassoc_of hsq₁, hsq₂, reassoc_of w₁, zero_comp, comp_zero], },
  let e : short_complex.mk f₁ g₁ h.w ≅ short_complex.mk f₂ g₂ w₂ :=
    short_complex.mk_iso α β γ hsq₁ hsq₂,
  haveI := short_complex.has_homology_of_iso e,
  rw exact_iff_exact_short_complex f₁ g₁ w₁ at h,
  rw exact_iff_exact_short_complex f₂ g₂ w₂,
  rw short_complex.exact_iff_of_iso e.symm,
  exact h,
end

lemma exact_iff_exact_of_iso {A₁ B₁ C₁ A₂ B₂ C₂ : V}
  (f₁ : A₁ ⟶ B₁) (g₁ : B₁ ⟶ C₁) (f₂ : A₂ ⟶ B₂) (g₂ : B₂ ⟶ C₂)
  (α : A₁ ≅ A₂) (β : B₁ ≅ B₂) (γ : C₁ ≅ C₂) (hsq₁ : α.hom ≫ f₂ = f₁ ≫ β.hom)
  (hsq₂ : β.hom ≫ g₂ = g₁ ≫ γ.hom) :
  exact f₁ g₁ ↔ exact f₂ g₂ :=
begin
  split,
  { exact exact_of_iso_of_exact f₁ g₁ f₂ g₂ α β γ hsq₁ hsq₂, },
  { refine exact_of_iso_of_exact f₂ g₂ f₁ g₁ α.symm β.symm γ.symm _ _,
    { simp only [← cancel_mono β.hom, category.assoc, ← hsq₁,
        iso.symm_hom, iso.inv_hom_id_assoc, iso.inv_hom_id, category.comp_id], },
    { simp only [← cancel_mono γ.hom, category.assoc, ← hsq₂,
        iso.symm_hom, iso.inv_hom_id_assoc, iso.inv_hom_id, category.comp_id], }, },
end

lemma exact.op {A B C : V} {f : A ⟶ B} {g : B ⟶ C}
  (h : exact f g) : exact g.op f.op :=
begin
  have w := h.w,
  have w' : g.op ≫ f.op = 0 := by simpa only [← op_comp, w],
  rw exact_iff_exact_short_complex _ _ w at h,
  simpa only [exact_iff_exact_short_complex _ _ w'] using h.op,
end

lemma exact.unop {A B C : Vᵒᵖ} {f : A ⟶ B} {g : B ⟶ C}
  (h : exact f g) : exact g.unop f.unop :=
begin
  have w := h.w,
  have w' : g.unop ≫ f.unop = 0 := by simpa only [← unop_comp, w],
  rw exact_iff_exact_short_complex _ _ w at h,
  simpa only [exact_iff_exact_short_complex _ _ w'] using h.unop',
end

lemma exact.op_iff {A B C : V} (f : A ⟶ B) (g : B ⟶ C) :
  exact g.op f.op ↔ exact f g :=
⟨exact.unop, exact.op⟩

lemma exact.unop_iff {A B C : Vᵒᵖ} (f : A ⟶ B) (g : B ⟶ C) :
  exact g.unop f.unop ↔ exact f g :=
⟨exact.op, exact.unop⟩

section
variables [has_zero_morphisms V]

lemma comp_eq_zero_of_image_eq_kernel {A B C : V} (f : A ⟶ B) (g : B ⟶ C)
  [has_image f] [has_kernel g]
  (p : image_subobject f = kernel_subobject g) : f ≫ g = 0 :=
begin
  rw [←image_subobject_arrow_comp f, category.assoc],
  convert comp_zero,
  rw p,
  simp,
end

lemma image_to_kernel_is_iso_of_image_eq_kernel {A B C : V} (f : A ⟶ B) (g : B ⟶ C)
  [has_image f] [has_kernel g]
  (p : image_subobject f = kernel_subobject g) :
  is_iso (image_to_kernel f g (comp_eq_zero_of_image_eq_kernel f g p)) :=
begin
  refine ⟨⟨subobject.of_le _ _ p.ge, _⟩⟩,
  dsimp [image_to_kernel],
  simp only [subobject.of_le_comp_of_le, subobject.of_le_refl],
  simp,
end

/-
-- We'll prove the converse later, when `V` is abelian.
lemma exact_of_image_eq_kernel {A B C : V} (f : A ⟶ B) (g : B ⟶ C)
  (p : image_subobject f = kernel_subobject g) : exact f g :=
{ w := comp_eq_zero_of_image_eq_kernel f g p,
  epi := begin
    haveI := image_to_kernel_is_iso_of_image_eq_kernel f g p,
    apply_instance,
  end }-/

end

variables {A B C D : V} {f : A ⟶ B} {g : B ⟶ C} (h : C ⟶ D)
local attribute [instance] epi_comp

section

lemma exact_comp_hom_inv_comp (i : B ≅ D) (h : exact f g) : exact (f ≫ i.hom) (i.inv ≫ g) :=
exact_of_iso_of_exact f g (f ≫ i.hom) (i.inv ≫ g) (iso.refl _) i (iso.refl _)
  (by simp) (by simp) h

lemma exact_comp_inv_hom_comp (i : D ≅ B) (h : exact f g) : exact (f ≫ i.inv) (i.hom ≫ g) :=
exact_comp_hom_inv_comp i.symm h

variables (f g)

lemma exact_comp_hom_inv_comp_iff (i : B ≅ D) : exact (f ≫ i.hom) (i.inv ≫ g) ↔ exact f g :=
⟨λ h, by simpa using exact_comp_inv_hom_comp i h, exact_comp_hom_inv_comp i⟩

lemma exact_iff_of_epi_of_is_iso_of_mono {A' B' C' : V} (f' : A' ⟶ B') (g' : B' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C') [epi a] [is_iso b] [mono c]
  (comm₁ : a ≫ f' = f ≫ b) (comm₂ : b ≫ g' = g ≫ c) :
  exact f g ↔ exact f' g' :=
begin
  split,
  { intro h,
    have w' : f' ≫ g' = 0,
    { simp only [← cancel_epi a, reassoc_of comm₁, comm₂, reassoc_of h.w, zero_comp, comp_zero], },
    let φ : short_complex.mk f g h.w ⟶ short_complex.mk f' g' w' := ⟨a, b, c, comm₁, comm₂⟩,
    rw exact_iff_exact_short_complex _ _ w',
    rw ← short_complex.exact_iff_of_epi_of_is_iso_of_mono φ,
    rw ← exact_iff_exact_short_complex _ _ h.w,
    exact h, },
  { intro h',
    have w : f ≫ g = 0,
    { simp only [← cancel_mono c, assoc, ← comm₂, ← reassoc_of comm₁, h'.w,
        comp_zero, zero_comp], },
    let φ : short_complex.mk f g w ⟶ short_complex.mk f' g' h'.w := ⟨a, b, c, comm₁, comm₂⟩,
    rw exact_iff_exact_short_complex _ _ w,
    rw short_complex.exact_iff_of_epi_of_is_iso_of_mono φ,
    rw ← exact_iff_exact_short_complex _ _ h'.w,
    exact h', },
end

@[simp]
lemma exact_epi_comp_iff [epi f] : exact (f ≫ g) h ↔ exact g h :=
exact_iff_of_epi_of_is_iso_of_mono (f ≫ g) h g h f (𝟙 C) (𝟙 D) (by simp) (by simp)

lemma exact_epi_comp (hgh : exact g h) [epi f] : exact (f ≫ g) h :=
(exact_epi_comp_iff f g h).2 hgh

--@[simp]
--lemma exact_iso_comp [is_iso f] : exact (f ≫ g) h ↔ exact g h :=
--exact_epi_comp_iff _ _ _


lemma exact_comp_mono_iff [mono h] : exact f (g ≫ h) ↔ exact f g :=
(exact_iff_of_epi_of_is_iso_of_mono f g f (g ≫ h) (𝟙 A) (𝟙 B) h (by simp) (by simp)).symm

variables {f g}

lemma exact_comp_mono (hfg : exact f g) [mono h] : exact f (g ≫ h) :=
(exact_comp_mono_iff f g h).2 hfg

--@[simp]
--lemma exact_comp_iso [is_iso h] : exact f (g ≫ h) ↔ exact f g :=
--by apply exact_comp_mono_iff

/-lemma exact_kernel_subobject_arrow : exact (kernel_subobject f).arrow f :=
begin
  refine ⟨by simp, _⟩,
  apply @is_iso.epi_of_iso _ _ _ _ _ _,
  exact ⟨⟨factor_thru_image_subobject _, by { ext, simp, }, by { ext, simp, }⟩⟩,
end-/

lemma exact_kernel_sequence' (c : kernel_fork f) (hc : is_limit c)
  [has_zero_object V]
  [(short_complex.mk c.ι f (kernel_fork.condition c)).has_homology] :
  exact c.ι f :=
⟨kernel_fork.condition _,
  (short_complex.left_homology_data.kernel_sequence' f c hc).exact_iff.2 (is_zero_zero _)⟩

lemma exact_kernel_ι [has_zero_object V] [has_kernel f]
  [h : (short_complex.mk (kernel.ι f) f (kernel.condition f)).has_homology] :
  exact (kernel.ι f) f :=
@exact_kernel_sequence' _ _ _ _ _ f _ (kernel_is_kernel f) _ h

/-
instance (h : exact f g) : epi (factor_thru_kernel_subobject g f h.w) :=
begin
  rw ←factor_thru_image_subobject_comp_image_to_kernel,
  apply epi_comp,
end

instance (h : exact f g) : epi (kernel.lift g f h.w) :=
begin
  rw ←factor_thru_kernel_subobject_comp_kernel_subobject_iso,
  apply epi_comp
end-/

variables (A)

/-
lemma kernel_subobject_arrow_eq_zero_of_exact_zero_left [has_kernel g]
  (h : exact (0 : A ⟶ B) g) [epi (image_to_kernel (0 : A ⟶ B) g h.w)]
  [epi (factor_thru_image_subobject (0 : A ⟶ B))] :
  (kernel_subobject g).arrow = 0 :=
begin
  rw [←cancel_epi (image_to_kernel (0 : A ⟶ B) g h.w),
    ←cancel_epi (factor_thru_image_subobject (0 : A ⟶ B))],
  simp
end

lemma kernel_ι_eq_zero_of_exact_zero_left [has_kernel g]
(h : exact (0 : A ⟶ B) g)
  [epi (image_to_kernel (0 : A ⟶ B) g h.w)]
  [epi (factor_thru_image_subobject (0 : A ⟶ B))] :
  kernel.ι g = 0 :=
by { rw ←kernel_subobject_arrow', simp [kernel_subobject_arrow_eq_zero_of_exact_zero_left A h], }
-/

end

section has_cokernels
--variables [has_zero_morphisms V] [has_equalizers V] [has_cokernels V] (f g)

@[simp, reassoc] lemma kernel_comp_cokernel (h : exact f g) [has_kernel g] [has_cokernel f] :
  kernel.ι g ≫ cokernel.π f = 0 :=
begin
  haveI := h.has_homology,
  simpa only [← (short_complex.mk f g h.w).exact_iff_kernel_ι_comp_cokernel_π_zero] using h.exact,
end

lemma comp_eq_zero_of_exact (h : exact f g) {X Y : V} {ι : X ⟶ B} (hι : ι ≫ g = 0) {π : B ⟶ Y}
  (hπ : f ≫ π = 0) : ι ≫ π = 0 :=
h.exact.comp_eq_zero hι hπ

@[simp, reassoc] lemma fork_ι_comp_cofork_π (h : exact f g) (s : kernel_fork g)
  (t : cokernel_cofork f) : fork.ι s ≫ cofork.π t = 0 :=
comp_eq_zero_of_exact h (kernel_fork.condition s) (cokernel_cofork.condition t)

end has_cokernels

lemma exact_of_zero [has_zero_object V] {A C : V} (f : A ⟶ 0) (g : 0 ⟶ C) : exact f g :=
begin
  obtain rfl : f = 0 := by ext,
  exact ⟨zero_comp, short_complex.exact_of_is_zero_X₂ _ (is_zero_zero _)⟩,
end

end

end

section
variables [preadditive V]

lemma exact_zero_mono [has_zero_object V] {B C : V} (f : B ⟶ C) [mono f] :
  exact (0 : 0 ⟶ B) f :=
begin
  rw [exact_iff_exact_short_complex _ _ zero_comp, short_complex.exact_iff_mono],
  { dsimp, apply_instance, },
  { refl, },
end

lemma exact_epi_zero [has_zero_object V] {A B : V} (f : A ⟶ B) [epi f] :
  exact f (0 : B ⟶ 0) :=
begin
  rw [exact_iff_exact_short_complex _ _ comp_zero, short_complex.exact_iff_epi],
  { dsimp, apply_instance, },
  { refl, },
end

lemma mono_iff_exact_zero_left [has_zero_object V] (Z : V) {B C : V} (f : B ⟶ C) :
  mono f ↔ exact (0 : Z ⟶ B) f :=
begin
  rw [exact_iff_exact_short_complex _ _ zero_comp, short_complex.exact_iff_mono],
  refl,
end

lemma exact_zero_left_of_mono [has_zero_object V] (Z : V) {B C : V} (f : B ⟶ C) [mono f] :
  exact (0 : Z ⟶ B) f :=
by simpa only [← mono_iff_exact_zero_left Z]

lemma mono_iff_exact_zero_left' [has_zero_object V] {B C : V} (f : B ⟶ C) :
  mono f ↔ exact (0 : 0 ⟶ B) f :=
mono_iff_exact_zero_left _ _

lemma epi_iff_exact_zero_right [has_zero_object V] (Z : V) {A B : V} (f : A ⟶ B) :
  epi f ↔ exact f (0 : B ⟶ Z) :=
begin
  rw [exact_iff_exact_short_complex _ _ comp_zero, short_complex.exact_iff_epi],
  refl,
end

lemma epi_iff_exact_zero_right' [has_zero_object V] {A B : V} (f : A ⟶ B) :
  epi f ↔ exact f (0 : B ⟶ 0) :=
epi_iff_exact_zero_right _ _

lemma exact_zero_right_of_epi [has_zero_object V] (Z : V) {B C : V} (f : B ⟶ C) [epi f] :
  exact f (0 : C ⟶ Z) :=
by simpa only [← epi_iff_exact_zero_right Z]

lemma mono_iff_kernel_ι_eq_zero {A B : V} (f : A ⟶ B) [has_kernel f] [has_zero_object V] :
  mono f ↔ kernel.ι f = 0 :=
begin
  rw mono_iff_is_zero_kernel,
  split,
  { intro h,
    exact is_zero.eq_of_src h _ _, },
  { intro h,
    simp only [limits.is_zero.iff_id_eq_zero, ← cancel_mono (kernel.ι f), h, comp_zero], },
end

lemma tfae_mono (Z : V) {A B : V} (f : A ⟶ B) [has_kernel f] [has_zero_object V] :
  tfae [mono f, kernel.ι f = 0, exact (0 : Z ⟶ A) f] :=
begin
  tfae_have : 1 ↔ 2,
  { rw mono_iff_kernel_ι_eq_zero, },
  tfae_have : 3 ↔ 1,
  { rw mono_iff_exact_zero_left, },
  tfae_finish,
end

lemma epi_iff_cokernel_π_eq_zero {A B : V} (f : A ⟶ B) [has_cokernel f] [has_zero_object V] :
  epi f ↔ cokernel.π f = 0 :=
begin
  rw epi_iff_is_zero_cokernel,
  split,
  { intro h,
    exact is_zero.eq_of_tgt h _ _, },
  { intro h,
    simp only [limits.is_zero.iff_id_eq_zero, ← cancel_epi (cokernel.π f), comp_id, h, comp_zero], }
end

lemma tfae_epi (Z : V) {A B : V} (f : A ⟶ B) [has_cokernel f] [has_zero_object V] :
  tfae [epi f, cokernel.π f = 0, exact f (0 : B ⟶ Z)] :=
begin
  tfae_have : 1 ↔ 2,
  { rw epi_iff_cokernel_π_eq_zero, },
  tfae_have : 3 ↔ 1,
  { rw epi_iff_exact_zero_right, },
  tfae_finish,
end

end

namespace functor
variables {W : Type u₂} [category.{v₂} W] [has_zero_morphisms V] [has_zero_morphisms W]

lemma map_exact (F : V ⥤ W) [F.preserves_zero_morphisms]
  {A B C : V} (f : A ⟶ B) (g : B ⟶ C) (h : exact f g)
  [F.preserves_left_homology_of (short_complex.mk _ _ h.w)]
  [F.preserves_right_homology_of (short_complex.mk _ _ h.w)] :
  exact (F.map f) (F.map g) :=
begin
  have w' : F.map f ≫ F.map g = 0 := by simp only [← F.map_comp, h.w, F.map_zero],
  have h' : (short_complex.mk _ _ h.w).exact,
  { simpa only [← exact_iff_exact_short_complex] using h, },
  simpa only [exact_iff_exact_short_complex _ _ w']
    using short_complex.exact_map_of_preserves_homology h' F,
end

class preserves_exact_sequences (F : V ⥤ W) :=
(preserves : ∀ {A B C : V} (f : A ⟶ B) (g : B ⟶ C), exact f g → exact (F.map f) (F.map g))

lemma exact_map_of_exact (F : V ⥤ W) [preserves_exact_sequences F] {A B C : V} {f : A ⟶ B}
  {g : B ⟶ C} (hfg : exact f g) : exact (F.map f) (F.map g) :=
preserves_exact_sequences.preserves f g hfg

instance preserves_exact_sequences_of_preserves_homology
  (F : V ⥤ W) [F.preserves_zero_morphisms]
  [F.preserves_homology] :
  preserves_exact_sequences F :=
⟨λ A B C f g h, map_exact F f g h⟩

lemma exact_of_exact_map_of_preserves_homology (F : V ⥤ W) [F.preserves_zero_morphisms]
  {A B C : V} (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0) (h : exact (F.map f) (F.map g))
  [(short_complex.mk _ _ w).has_homology]
  [F.preserves_left_homology_of (short_complex.mk _ _ w)]
  [F.preserves_right_homology_of (short_complex.mk _ _ w)] [faithful F] :
  exact f g :=
begin
  have e := (short_complex.mk _ _ w).exact_map_iff_of_preserves_homology F,
  simp only [short_complex.map, ← exact_iff_exact_short_complex] at e,
  simpa only [e] using h,
end

/-- A functor reflects exact sequences if any composable pair of morphisms that is mapped to an
    exact pair is itself exact. -/
class reflects_exact_sequences (F : V ⥤ W) :=
(reflects : ∀ {A B C : V} (f : A ⟶ B) (g : B ⟶ C), exact (F.map f) (F.map g) → exact f g)

instance reflects_exact_sequences_of_preserves_homology
  (F : V ⥤ W) [F.preserves_zero_morphisms] [category_with_homology V]
  [F.preserves_homology] [faithful F]:
  reflects_exact_sequences F :=
⟨λ A B C f g h, exact_of_exact_map_of_preserves_homology F f g
  (F.map_injective (by simp only [F.map_comp, h.w, F.map_zero])) h⟩

lemma exact_of_exact_map (F : V ⥤ W) [reflects_exact_sequences F] {A B C : V} {f : A ⟶ B}
  {g : B ⟶ C} (hfg : exact (F.map f) (F.map g)) : exact f g :=
reflects_exact_sequences.reflects f g hfg

end functor

end category_theory

import algebra.homology.short_complex.exact
import category_theory.subobject.limits

namespace category_theory
noncomputable theory

open category limits

variables {C : Type*} [category C]

lemma subobject.is_iso_of_le_iff {X : C} {K₁ K₂ : subobject X} (le : K₁ ≤ K₂) :
  is_iso (subobject.of_le _ _ le) ↔ K₁ = K₂ :=
begin
  split,
  { introI,
    exact le_antisymm le (subobject.le_of_comm (inv (subobject.of_le _ _ le))
      (by simp only [is_iso.inv_comp_eq, subobject.of_le_arrow])), },
  { intro h,
    subst h,
    rw subobject.of_le_refl,
    apply_instance, },
end

section

variables [has_zero_morphisms C] (S : short_complex C)

variables {X₁ X₂ X₃ : C} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)

lemma image_le_kernel_iff [has_kernel g] [has_image f] :
  image_subobject f ≤ kernel_subobject g ↔ f ≫ g = 0 :=
begin
  split,
  { intro h,
    simp only [← image.fac f, ← image_subobject_arrow' f, ← subobject.of_le_arrow h,
      ← kernel_subobject_arrow g, assoc, kernel.condition, comp_zero], },
  { intro w,
    exact image_subobject_le_mk _ _ (kernel.lift _ _ w) (by simp), },
end

end

namespace short_complex

section

variables [has_zero_morphisms C] (S : short_complex C)

variables [has_image S.f] [has_kernel S.g]

lemma image_le_kernel : image_subobject S.f ≤ kernel_subobject S.g :=
by simpa only [image_le_kernel_iff] using S.zero

@[simp, reassoc]
lemma image_ι_comp_g : image.ι S.f ≫ S.g = 0 :=
by simp only [← image_subobject_arrow' S.f, ← subobject.of_le_arrow S.image_le_kernel, assoc,
  kernel_subobject_arrow_comp, comp_zero]

def image_to_kernel : image S.f ⟶ kernel S.g := kernel.lift S.g (image.ι S.f) S.image_ι_comp_g

@[simp, reassoc]
lemma image_to_kernel_comp_kernel_ι : S.image_to_kernel ≫ kernel.ι S.g = image.ι S.f :=
kernel.lift_ι _ _ _

instance : mono S.image_to_kernel := mono_of_mono_fac S.image_to_kernel_comp_kernel_ι

variables [has_cokernel S.image_to_kernel] [epi (factor_thru_image S.f)]

@[simp]
def left_homology_data.of_image_to_kernel :
  S.left_homology_data :=
begin
  let f' := kernel.lift S.g S.f S.zero,
  have hf' : f' = factor_thru_image S.f ≫ S.image_to_kernel,
  { simp only [← cancel_mono (kernel.ι S.g), kernel.lift_ι, assoc,
      image_to_kernel_comp_kernel_ι, image.fac], },
  have wπ : f' ≫ cokernel.π S.image_to_kernel = 0,
  { simp only [hf', assoc, cokernel.condition, comp_zero], },
  have hπ := cokernel_cofork.is_colimit.of_π (cokernel.π S.image_to_kernel) wπ
    (λ A x hx, cokernel.desc _ x
      (by rw [← cancel_epi (factor_thru_image S.f), comp_zero, ← reassoc_of hf', hx]))
    (λ A x hx, cokernel.π_desc _ _ _)
    (λ A x hx b hb, by { dsimp,
      rw [← cancel_epi (cokernel.π S.image_to_kernel), hb, cokernel.π_desc], }),
  exact
  { K := kernel S.g,
    H := cokernel S.image_to_kernel,
    i := kernel.ι S.g,
    π := cokernel.π S.image_to_kernel,
    wi := kernel.condition _,
    hi := kernel_is_kernel _,
    wπ := wπ,
    hπ := hπ, },
end

@[priority 100]
instance has_left_homology_of_image_to_kernel : S.has_left_homology :=
has_left_homology.mk' (left_homology_data.of_image_to_kernel S)

@[simp]
def left_homology_iso_cokernel_image_to_kernel :
  S.left_homology ≅ cokernel S.image_to_kernel :=
(left_homology_data.of_image_to_kernel S).left_homology_iso

@[simp]
def homology_iso_cokernel_image_to_kernel [S.has_homology] :
  S.homology ≅ cokernel S.image_to_kernel :=
(left_homology_data.of_image_to_kernel S).homology_iso

end

section preadditive

variables [preadditive C] (S : short_complex C)
  [has_image S.f] [has_kernel S.g] [has_cokernel S.image_to_kernel]
  [epi (factor_thru_image S.f)]

lemma is_zero_left_homology_iff_epi_image_to_kernel [has_zero_object C] :
  is_zero S.left_homology ↔ epi S.image_to_kernel :=
by rw [epi_iff_is_zero_cokernel S.image_to_kernel,
  S.left_homology_iso_cokernel_image_to_kernel.is_zero_iff]

lemma is_zero_left_homology_iff_is_iso_image_eq_kernel [has_zero_object C] [balanced C] :
  is_zero S.left_homology ↔ is_iso S.image_to_kernel :=
begin
  rw is_zero_left_homology_iff_epi_image_to_kernel,
  split,
  { introI,
    apply is_iso_of_mono_of_epi, },
  { introI, apply_instance, },
end

lemma is_zero_left_homology_iff_image_eq_kernel [has_zero_object C] [balanced C] :
  is_zero S.left_homology ↔ image_subobject S.f = kernel_subobject S.g :=
begin
  rw [is_zero_left_homology_iff_is_iso_image_eq_kernel,
    ← subobject.is_iso_of_le_iff S.image_le_kernel],
  let e₁ := image_subobject_iso S.f,
  let e₂ := kernel_subobject_iso S.g,
  let φ := subobject.of_le _ _ S.image_le_kernel,
  have eq : S.image_to_kernel = e₁.inv ≫ φ ≫ e₂.hom,
  { simp only [← cancel_mono (kernel.ι S.g), image_to_kernel_comp_kernel_ι, assoc,
      kernel_subobject_arrow, subobject.of_le_arrow, image_subobject_arrow'], },
  split,
  { rw eq,
    introI,
    haveI := is_iso.of_is_iso_comp_left e₁.inv (φ ≫ e₂.hom),
    exact is_iso.of_is_iso_comp_right φ e₂.hom, },
  { introI,
    rw eq,
    apply_instance, },
end

lemma exact_iff_epi_image_to_kernel [has_zero_object C] [S.has_homology] :
  S.exact ↔ epi S.image_to_kernel :=
by rw [S.exact_iff_is_zero_left_homology, is_zero_left_homology_iff_epi_image_to_kernel]

lemma exact_iff_is_iso_image_eq_kernel [has_zero_object C] [balanced C] [S.has_homology] :
  S.exact ↔ is_iso S.image_to_kernel :=
by rw [S.exact_iff_is_zero_left_homology, is_zero_left_homology_iff_is_iso_image_eq_kernel]

lemma exact_iff_image_eq_kernel [has_zero_object C] [balanced C] [S.has_homology] :
  S.exact ↔ image_subobject S.f = kernel_subobject S.g :=
by rw [S.exact_iff_is_zero_left_homology, is_zero_left_homology_iff_image_eq_kernel]

lemma exact.of_pseudo_exact' [has_zero_object C] [S.has_homology]
  (h : ∀ ⦃A : C⦄ (x₂ : A ⟶ S.X₂) (hx₂ : x₂ ≫ S.g = 0),
    ∃ (A' : C) (π : A' ⟶ A) (hπ : epi π) (x₁ : A' ⟶ S.X₁), π ≫ x₂ = x₁ ≫ S.f) : S.exact :=
begin
  rw exact_iff_epi_to_cycles,
  obtain ⟨A', π, hπ, x₁, hx₁⟩ := h S.cycles_i (by simp),
  have eq : π = x₁ ≫ S.to_cycles,
  { rw [← cancel_mono S.cycles_i, hx₁],
    simp only [assoc, to_cycles_i], },
  subst eq,
  haveI := hπ,
  exact epi_of_epi x₁ _,
end

end preadditive

end short_complex

end category_theory

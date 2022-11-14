import algebra.homology.short_complex_preadditive
import category_theory.abelian.basic

noncomputable theory

open category_theory category_theory.limits category_theory.category

namespace category_theory.limits

def cokernel_cofork.cocone_point_iso_of_epi_of_is_iso {C : Type*} [category C] [has_zero_morphisms C]
  {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y') (p : X ⟶ X') (q : Y ⟶ Y') [epi p] [is_iso q]
  (comm : f ≫ q = p ≫ f') {c : cokernel_cofork f} {c' : cokernel_cofork f'}
  (hc : is_colimit c) (hc' : is_colimit c') : c.X ≅ c'.X :=
{ hom := hc.desc (cokernel_cofork.of_π (q ≫ c'.π)
  (by simp only [reassoc_of comm, comm, cokernel_cofork.condition, comp_zero])),
  inv := hc'.desc (cokernel_cofork.of_π (inv q ≫ c.π)
    (by { simp only [← cancel_epi p, ← assoc, ← comm],
      simp only [assoc, is_iso.hom_inv_id, comp_id, cokernel_cofork.condition, comp_zero], })),
  hom_inv_id' := begin
    haveI := cokernel_cofork.is_colimit.epi_π hc,
    simp only [← cancel_epi c.π, cokernel_cofork.is_colimit.π_desc_assoc hc, assoc,
      cokernel_cofork.π_of_π, cokernel_cofork.is_colimit.π_desc, is_iso.hom_inv_id_assoc],
    erw comp_id,
  end,
  inv_hom_id' := begin
    haveI := cokernel_cofork.is_colimit.epi_π hc',
    simp only [← cancel_epi c'.π, assoc, cokernel_cofork.is_colimit.π_desc_assoc,
      cokernel_cofork.π_of_π, cokernel_cofork.is_colimit.π_desc, is_iso.inv_hom_id_assoc],
    erw comp_id,
  end, }

@[simp, reassoc]
lemma cokernel_cofork.comp_cocone_point_iso_of_epi_of_is_iso_hom
  {C : Type*} [category C] [has_zero_morphisms C]
  {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y') (p : X ⟶ X') (q : Y ⟶ Y') [epi p] [is_iso q]
  (comm : f ≫ q = p ≫ f') {c : cokernel_cofork f} {c' : cokernel_cofork f'}
  (hc : is_colimit c) (hc' : is_colimit c') :
  c.π ≫ (cokernel_cofork.cocone_point_iso_of_epi_of_is_iso f f' p q comm hc hc').hom =
    q ≫ c'.π :=
begin
  dsimp [cokernel_cofork.cocone_point_iso_of_epi_of_is_iso],
  simp only [cokernel_cofork.is_colimit.π_desc, cokernel_cofork.π_of_π],
end

@[simp, reassoc]
lemma cokernel_cofork.comp_cocone_point_iso_of_epi_of_is_iso_inv
  {C : Type*} [category C] [has_zero_morphisms C]
  {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y') (p : X ⟶ X') (q : Y ⟶ Y') [epi p] [is_iso q]
  (comm : f ≫ q = p ≫ f') {c : cokernel_cofork f} {c' : cokernel_cofork f'}
  (hc : is_colimit c) (hc' : is_colimit c') :
  c'.π ≫ (cokernel_cofork.cocone_point_iso_of_epi_of_is_iso f f' p q comm hc hc').inv =
    inv q ≫ c.π :=
begin
  dsimp [cokernel_cofork.cocone_point_iso_of_epi_of_is_iso],
  simp only [cokernel_cofork.is_colimit.π_desc, cokernel_cofork.π_of_π],
end

end category_theory.limits

open category_theory.limits

variables {C : Type*} [category C] [abelian C]

namespace short_complex

@[simp]
def abelian_image_to_kernel (S : short_complex C) :
  abelian.image S.f ⟶ kernel S.g :=
kernel.lift S.g (abelian.image.ι S.f)
  (by simp only [← cancel_epi (abelian.factor_thru_image S.f), abelian.image.fac_assoc,
    zero, comp_zero])

@[simp]
def left_homology_data.of_abelian (S : short_complex C) :
  S.left_homology_data :=
begin
  let γ := kernel.ι S.g ≫ cokernel.π S.f,
  let f' := kernel.lift S.g S.f S.zero,
  have hf' : f' = kernel.lift γ f'
    (by simp only [kernel.lift_ι_assoc, cokernel.condition]) ≫ kernel.ι γ,
  { simp only [kernel.lift_ι], },
  have hπ₀ : f' ≫ cokernel.π (kernel.ι γ) = 0,
  { rw [hf', assoc, cokernel.condition (kernel.ι γ), comp_zero], },
  let α := kernel.lift S.g (abelian.image.ι S.f)
    (by simp only [← cancel_epi (abelian.factor_thru_image S.f),
      abelian.image.fac_assoc, zero, comp_zero]),
  haveI : mono (α ≫ kernel.ι S.g),
  { rw [kernel.lift_ι], apply_instance, },
  haveI : mono α := mono_of_mono α (kernel.ι S.g),
  have αγ : α ≫ γ = 0 := by simp only [kernel.lift_ι_assoc, kernel.condition],
  have hα : is_limit (kernel_fork.of_ι α αγ) :=
    kernel_fork.is_limit.of_ι _ _
      (λ A k hk, kernel.lift _ (k ≫ kernel.ι S.g) (by rw [assoc, hk]))
      (λ A k hk, by simp only [← cancel_mono (kernel.ι S.g), assoc, kernel.lift_ι])
      (λ A k hk b hb, by simp only [← cancel_mono α, ← cancel_mono (kernel.ι S.g),
        hb, assoc, kernel.lift_ι]),
  let e : abelian.image S.f ≅ kernel γ :=
    is_limit.cone_point_unique_up_to_iso hα (kernel_is_kernel γ),
  have fac : f' = abelian.factor_thru_image S.f ≫ e.hom ≫ kernel.ι γ,
  { rw hf',
    simp only [← assoc, cancel_mono (kernel.ι γ), ← cancel_mono e.inv],
    simp only [is_limit.lift_comp_cone_point_unique_up_to_iso_inv, assoc, iso.hom_inv_id, comp_id],
    erw [← cancel_mono α, ← cancel_mono (kernel.ι S.g),
      hα.fac _ walking_parallel_pair.zero],
    simp only [fork.of_ι_π_app, kernel.lift_ι, assoc, abelian.image.fac], },
  have hπ : is_colimit (cokernel_cofork.of_π _ hπ₀) := cokernel_cofork.is_colimit.of_π _ _
    (λ A x hx, cokernel.desc _ x begin
      simp only [← cancel_epi e.hom, ← cancel_epi (abelian.factor_thru_image S.f), comp_zero],
      simpa only [fac, assoc] using hx,
    end)
    (λ A x hx, cokernel.π_desc _ _ _)
    (λ A x hx b hb, by { ext, simp only [hb, cokernel.π_desc], }),
  exact
  { K := kernel S.g,
    H := abelian.coimage (kernel.ι S.g ≫ cokernel.π S.f),
    i := kernel.ι _,
    π := cokernel.π _,
    hi₀ := kernel.condition _,
    hi := kernel_is_kernel _,
    hπ₀ := begin
      change f' ≫ _ = _,
      rw [hf', assoc, cokernel.condition (kernel.ι γ), comp_zero],
    end,
    hπ := hπ, },
end

def left_homology_data.abelian_H_iso_cokernel_abelian_image_to_kernel (S : short_complex C) :
  (left_homology_data.of_abelian S).H ≅ cokernel S.abelian_image_to_kernel :=
begin
  let h := left_homology_data.of_abelian S,
  let e := cokernel_cofork.cocone_point_iso_of_epi_of_is_iso h.f' S.abelian_image_to_kernel
    (abelian.factor_thru_image S.f) (𝟙 _) (by simpa only [← cancel_mono (kernel.ι S.g),
      abelian_image_to_kernel, comp_id, assoc, kernel.lift_ι] using h.f'_i) h.hπ' (cokernel_is_cokernel _),
  exact e,
end

lemma left_homology_data.cokernel_π_comp_abelian_H_iso_cokernel_image_to_kernel_hom
  (S : short_complex C) :
  cokernel.π _ ≫ (left_homology_data.abelian_H_iso_cokernel_abelian_image_to_kernel S).hom =
  cokernel.π  _ :=
begin
  let h := left_homology_data.of_abelian S,
  have eq := cokernel_cofork.comp_cocone_point_iso_of_epi_of_is_iso_hom h.f' S.abelian_image_to_kernel
    (abelian.factor_thru_image S.f) (𝟙 _) (by simpa only [← cancel_mono (kernel.ι S.g),
      abelian_image_to_kernel, comp_id, assoc, kernel.lift_ι] using h.f'_i) h.hπ' (cokernel_is_cokernel _),
  dsimp at eq,
  rw id_comp at eq,
  exact eq,
end

@[simp]
def right_homology_data.of_abelian (S : short_complex C) :
  S.right_homology_data :=
begin
  let γ := kernel.ι S.g ≫ cokernel.π S.f,
  let g' := cokernel.desc S.f S.g S.zero,
  have hg' : g' = cokernel.π γ ≫ cokernel.desc γ g'
    (by simp only [assoc, cokernel.π_desc, kernel.condition]),
  { simp only [cokernel.π_desc], },
  have hι₀ : kernel.ι (cokernel.π γ) ≫ g' = 0,
  { rw [hg', kernel.condition_assoc, zero_comp], },
  let β := cokernel.desc S.f (abelian.coimage.π S.g)
    (by simp only [← cancel_mono (abelian.factor_thru_coimage S.g),
      assoc, cokernel.π_desc, zero, zero_comp]),
  haveI : epi (cokernel.π S.f ≫ β),
  { rw [cokernel.π_desc], apply_instance, },
  haveI : epi β := epi_of_epi (cokernel.π S.f) β,
  have γβ : γ ≫ β = 0 := by simp only [assoc, cokernel.π_desc, cokernel.condition],
  have hβ : is_colimit (cokernel_cofork.of_π β γβ) := cokernel_cofork.is_colimit.of_π _ _
    (λ A k hk, cokernel.desc _ (cokernel.π S.f ≫ k) (by rw [← assoc, hk]))
    (λ A k hk, by simp only [← cancel_epi (cokernel.π S.f),
      cokernel.π_desc_assoc, cokernel.π_desc])
    (λ A k hk b hb, by simp only [← cancel_epi β, ← cancel_epi (cokernel.π S.f), hb,
      cokernel.π_desc_assoc, cokernel.π_desc]),
  let e : abelian.coimage S.g ≅ cokernel γ :=
    is_colimit.cocone_point_unique_up_to_iso hβ (cokernel_is_cokernel γ),
  have fac : g' = cokernel.π γ ≫ e.inv ≫ abelian.factor_thru_coimage S.g,
  { rw hg',
    simp only [cancel_epi (cokernel.π γ), ← cancel_epi e.hom,
      is_colimit.cocone_point_unique_up_to_iso_hom_desc, iso.hom_inv_id_assoc],
    erw [← cancel_epi β, ← cancel_epi (cokernel.π S.f),
      hβ.fac _ walking_parallel_pair.one],
    simp only [cokernel.π_desc, cofork.of_π_ι_app, cokernel.π_desc, cokernel.π_desc_assoc], },
  have hι : is_limit (kernel_fork.of_ι _ hι₀) := kernel_fork.is_limit.of_ι _ _
    (λ A x hx, kernel.lift _ x (by simp only [← cancel_mono e.inv,
      ← cancel_mono (abelian.factor_thru_coimage S.g), assoc, zero_comp, ← fac, hx]))
    (λ A x hx, kernel.lift_ι _ _ _)
    (λ A x hx b hb, by { ext, simp only [hb, kernel.lift_ι]}),
  exact
  { Q := cokernel S.f,
    H := abelian.image (kernel.ι S.g ≫ cokernel.π S.f),
    p := cokernel.π _,
    ι := kernel.ι _,
    hp₀ := cokernel.condition _,
    hp := cokernel_is_cokernel _,
    hι₀ := begin
      change _ ≫ g' = _,
      simp only [fac, kernel.condition_assoc, zero_comp],
    end,
    hι := hι, },
end

@[simps]
def homology_data.of_abelian (S : short_complex C) :
  S.homology_data :=
{ left := left_homology_data.of_abelian S,
  right := right_homology_data.of_abelian S,
  iso := abelian.coimage_iso_image (kernel.ι S.g ≫ cokernel.π S.f),
  comm := abelian.coimage_image_factorisation _, }

variable (C)

lemma _root_.category_with_homology.of_abelian : category_with_homology C :=
λ S, has_homology.mk' (homology_data.of_abelian S)

instance : category_with_homology C := category_with_homology.of_abelian C

variable {C}

def cokernel_image_to_kernel_iso_homology (S : short_complex C) :
  cokernel S.abelian_image_to_kernel ≅ S.homology :=
(left_homology_data.abelian_H_iso_cokernel_abelian_image_to_kernel S).symm ≪≫
  (left_homology_data.of_abelian S).homology_iso.symm

end short_complex

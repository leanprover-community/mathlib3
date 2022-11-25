import algebra.homology.short_complex.functors

noncomputable theory

open category_theory category_theory.limits category_theory.category

variables {J C : Type*} [category J] [category C] [has_zero_morphisms C]

namespace short_complex

def is_limit_of_is_limit_π {F : J ⥤ short_complex C} (c : cone F)
  (h₁ : is_limit (π₁.map_cone c)) (h₂ : is_limit (π₂.map_cone c))
  (h₃ : is_limit (π₃.map_cone c)) : is_limit c :=
{ lift := λ s, begin
    refine hom.mk (h₁.lift (π₁.map_cone s)) (h₂.lift (π₂.map_cone s))
      (h₃.lift (π₃.map_cone s)) _ _,
    { refine h₂.hom_ext (λ j, _),
      dsimp,
      simp only [assoc],
      have eq₁ := h₁.fac (π₁.map_cone s) j,
      have eq₂ := h₂.fac (π₂.map_cone s) j,
      have eq₃ := (c.π.app j).comm₁₂,
      have eq₄ := (s.π.app j).comm₁₂,
      dsimp at eq₁ eq₂ eq₃ eq₄,
      rw [← eq₃, reassoc_of eq₁, eq₂, eq₄], },
    { refine h₃.hom_ext (λ j, _),
      dsimp,
      simp only [assoc],
      have eq₁ := h₂.fac (π₂.map_cone s) j,
      have eq₂ := h₃.fac (π₃.map_cone s) j,
      have eq₃ := (c.π.app j).comm₂₃,
      have eq₄ := (s.π.app j).comm₂₃,
      dsimp at eq₁ eq₂ eq₃ eq₄,
      rw [← eq₃, reassoc_of eq₁, eq₂, eq₄], },
  end,
  fac' := λ s j, begin
    ext,
    { exact h₁.fac (π₁.map_cone s) j, },
    { exact h₂.fac (π₂.map_cone s) j, },
    { exact h₃.fac (π₃.map_cone s) j, },
  end,
  uniq' := λ s m hm, begin
    ext,
    { exact h₁.uniq (π₁.map_cone s) _ (λ j, π₁.congr_map (hm j)), },
    { exact h₂.uniq (π₂.map_cone s) _ (λ j, π₂.congr_map (hm j)), },
    { exact h₃.uniq (π₃.map_cone s) _ (λ j, π₃.congr_map (hm j)), },
  end, }

instance has_limit_of_has_limit_π (F : J ⥤ short_complex C)
  [has_limit (F ⋙ π₁)] [has_limit (F ⋙ π₂)] [has_limit (F ⋙ π₃)] :
  has_limit F :=
begin
  let S := short_complex.mk (lim_map (𝟙 F ◫ π₁_to_π₂)) (lim_map (𝟙 F ◫ π₂_to_π₃)) (by tidy),
  let c : cone F := cone.mk S
  { app := λ j, hom.mk (limit.π _ _) (limit.π _ _) (limit.π _ _) (by tidy) (by tidy),
    naturality' := λ j₁ j₂ f, begin
      ext,
      all_goals { dsimp, erw [id_comp, limit.w], },
    end, },
  exact ⟨⟨⟨_, is_limit_of_is_limit_π c
    (is_limit.of_iso_limit (limit.is_limit _) (cones.ext (iso.refl _) (by tidy)))
    (is_limit.of_iso_limit (limit.is_limit _) (cones.ext (iso.refl _) (by tidy)))
    (is_limit.of_iso_limit (limit.is_limit _) (cones.ext (iso.refl _) (by tidy)))⟩⟩⟩,
end

instance has_limits_of_shape [has_limits_of_shape J C] :
  has_limits_of_shape J (short_complex C) := { }

end short_complex

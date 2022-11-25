import algebra.homology.short_complex.functors

noncomputable theory

open category_theory category_theory.limits category_theory.category

variables {J C : Type*} [category J] [category C] [has_zero_morphisms C]
  {F : J ⥤ short_complex C}

namespace short_complex

def is_limit_of_is_limit_π (c : cone F)
  (h₁ : is_limit (π₁.map_cone c)) (h₂ : is_limit (π₂.map_cone c))
  (h₃ : is_limit (π₃.map_cone c)) : is_limit c :=
{ lift := λ s, begin
    have eq₁ := h₁.fac (π₁.map_cone s),
    have eq₂ := h₂.fac (π₂.map_cone s),
    have eq₃ := h₃.fac (π₃.map_cone s),
    have eq₄ := λ j, (c.π.app j).comm₁₂,
    have eq₅ := λ j, (s.π.app j).comm₁₂,
    have eq₆ := λ j, (c.π.app j).comm₂₃,
    have eq₇ := λ j, (s.π.app j).comm₂₃,
    dsimp at eq₁ eq₂ eq₃ eq₄ eq₅ eq₆ eq₇,
    exact hom.mk (h₁.lift (π₁.map_cone s)) (h₂.lift (π₂.map_cone s))
      (h₃.lift (π₃.map_cone s))
      (h₂.hom_ext (λ j,
        by { dsimp, simp only [assoc, ← eq₄, reassoc_of eq₁, eq₂, eq₅], }))
      (h₃.hom_ext (λ j,
        by { dsimp, simp only [assoc, ← eq₆, reassoc_of eq₂, eq₃, eq₇], })),
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

section

variables (F) [has_limit (F ⋙ π₁)] [has_limit (F ⋙ π₂)] [has_limit (F ⋙ π₃)]

def limit_cone : cone F :=
cone.mk (short_complex.mk (lim_map (𝟙 F ◫ π₁_to_π₂)) (lim_map (𝟙 F ◫ π₂_to_π₃)) (by tidy))
  { app := λ j, hom.mk (limit.π _ _) (limit.π _ _) (limit.π _ _) (by tidy) (by tidy),
    naturality' := λ j₁ j₂ f, begin
      ext,
      all_goals { dsimp, erw [id_comp, limit.w], },
    end, }

def π₁_map_cone_limit_cone_is_limit : is_limit (π₁.map_cone (limit_cone F)) :=
(is_limit.of_iso_limit (limit.is_limit _) (cones.ext (iso.refl _) (by tidy)))
def π₂_map_cone_limit_cone_is_limit : is_limit (π₂.map_cone (limit_cone F)) :=
(is_limit.of_iso_limit (limit.is_limit _) (cones.ext (iso.refl _) (by tidy)))
def π₃_map_cone_limit_cone_is_limit : is_limit (π₃.map_cone (limit_cone F)) :=
(is_limit.of_iso_limit (limit.is_limit _) (cones.ext (iso.refl _) (by tidy)))

def limit_cone_is_limit : is_limit (limit_cone F) :=
is_limit_of_is_limit_π _ (π₁_map_cone_limit_cone_is_limit F)
  (π₂_map_cone_limit_cone_is_limit F) (π₃_map_cone_limit_cone_is_limit F)

instance has_limit_of_has_limit_π : has_limit F := ⟨⟨⟨_, limit_cone_is_limit _⟩⟩⟩

instance : preserves_limit F π₁ :=
preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F) (π₁_map_cone_limit_cone_is_limit F)
instance : preserves_limit F π₂ :=
preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F) (π₂_map_cone_limit_cone_is_limit F)
instance : preserves_limit F π₃ :=
preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F) (π₃_map_cone_limit_cone_is_limit F)

end

instance has_limits_of_shape [has_limits_of_shape J C] :
  has_limits_of_shape J (short_complex C) := { }


def is_colimit_of_is_colimit_π {F : J ⥤ short_complex C} (c : cocone F)
  (h₁ : is_colimit (π₁.map_cocone c)) (h₂ : is_colimit (π₂.map_cocone c))
  (h₃ : is_colimit (π₃.map_cocone c)) : is_colimit c :=
{ desc := λ s, begin
    have eq₁ := h₁.fac (π₁.map_cocone s),
    have eq₂ := h₂.fac (π₂.map_cocone s),
    have eq₃ := h₃.fac (π₃.map_cocone s),
    have eq₄ := λ j, (c.ι.app j).comm₁₂,
    have eq₅ := λ j, (s.ι.app j).comm₁₂,
    have eq₆ := λ j, (c.ι.app j).comm₂₃,
    have eq₇ := λ j, (s.ι.app j).comm₂₃,
    dsimp at eq₁ eq₂ eq₃ eq₄ eq₅ eq₆ eq₇,
    exact hom.mk (h₁.desc (π₁.map_cocone s)) (h₂.desc (π₂.map_cocone s))
      (h₃.desc (π₃.map_cocone s))
      (h₁.hom_ext (λ j, (by { dsimp, rw [reassoc_of eq₁, eq₅, reassoc_of eq₄, eq₂], })))
      (h₂.hom_ext (λ j, (by { dsimp, rw [reassoc_of eq₂, eq₇, reassoc_of eq₆, eq₃], }))),
  end,
  fac' := λ s j, begin
    ext,
    { exact h₁.fac (π₁.map_cocone s) j, },
    { exact h₂.fac (π₂.map_cocone s) j, },
    { exact h₃.fac (π₃.map_cocone s) j, },
  end,
  uniq' := λ s m hm, begin
    ext,
    { exact h₁.uniq (π₁.map_cocone s) m.τ₁ (λ j, π₁.congr_map (hm j)), },
    { exact h₂.uniq (π₂.map_cocone s) m.τ₂ (λ j, π₂.congr_map (hm j)), },
    { exact h₃.uniq (π₃.map_cocone s) m.τ₃ (λ j, π₃.congr_map (hm j)), },
  end, }

section

variables (F) [has_colimit (F ⋙ π₁)] [has_colimit (F ⋙ π₂)] [has_colimit (F ⋙ π₃)]

def colimit_cocone : cocone F :=
cocone.mk (short_complex.mk (colim_map (𝟙 F ◫ π₁_to_π₂)) (colim_map (𝟙 F ◫ π₂_to_π₃)) (by tidy))
  { app := λ j, hom.mk (colimit.ι (F ⋙ π₁) _) (colimit.ι (F ⋙ π₂) _)
      (colimit.ι (F ⋙ π₃) _) (by tidy) (by tidy),
    naturality' := λ j₁ j₂ f, begin
      ext,
      { dsimp, erw [comp_id, colimit.w (F ⋙ π₁) f], },
      { dsimp, erw [comp_id, colimit.w (F ⋙ π₂) f], },
      { dsimp, erw [comp_id, colimit.w (F ⋙ π₃) f], },
    end, }

def π₁_map_cocone_colimit_cocone_is_colimit : is_colimit (π₁.map_cocone (colimit_cocone F)) :=
(is_colimit.of_iso_colimit (colimit.is_colimit _) (cocones.ext (iso.refl _) (by tidy)))
def π₂_map_cocone_colimit_cocone_is_colimit : is_colimit (π₂.map_cocone (colimit_cocone F)) :=
(is_colimit.of_iso_colimit (colimit.is_colimit _) (cocones.ext (iso.refl _) (by tidy)))
def π₃_map_cocone_colimit_cocone_is_colimit : is_colimit (π₃.map_cocone (colimit_cocone F)) :=
(is_colimit.of_iso_colimit (colimit.is_colimit _) (cocones.ext (iso.refl _) (by tidy)))

def colimit_cocone_is_colimit : is_colimit (colimit_cocone F) :=
is_colimit_of_is_colimit_π _  (π₁_map_cocone_colimit_cocone_is_colimit F)
  (π₂_map_cocone_colimit_cocone_is_colimit F) (π₃_map_cocone_colimit_cocone_is_colimit F)

instance has_colimit_of_has_colimit_π : has_colimit F := ⟨⟨⟨_, colimit_cocone_is_colimit _⟩⟩⟩

instance : preserves_colimit F π₁ :=
preserves_colimit_of_preserves_colimit_cocone (colimit_cocone_is_colimit F)
  (π₁_map_cocone_colimit_cocone_is_colimit F)
instance : preserves_colimit F π₂ :=
preserves_colimit_of_preserves_colimit_cocone (colimit_cocone_is_colimit F)
  (π₂_map_cocone_colimit_cocone_is_colimit F)
instance : preserves_colimit F π₃ :=
preserves_colimit_of_preserves_colimit_cocone (colimit_cocone_is_colimit F)
  (π₃_map_cocone_colimit_cocone_is_colimit F)

end

instance has_colimits_of_shape [has_colimits_of_shape J C] :
  has_colimits_of_shape J (short_complex C) := { }

end short_complex

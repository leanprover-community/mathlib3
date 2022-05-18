import category_theory.limits.shapes.biproducts

noncomputable theory

open category_theory

namespace category_theory.limits

variables {C : Type*} [category C] [has_zero_object C] [has_zero_morphisms C]

open_locale zero_object

def pushout_cocone_of_bilimit {X Y : C} {b : binary_bicone X Y} (h : b.is_bilimit) :
  colimit_cocone (span b.fst b.snd) :=
{ cocone := pushout_cocone.mk (0 : X ⟶ 0) (0 : Y ⟶ 0) (by simp),
  is_colimit := pushout_cocone.is_colimit_aux _ (λ s, 0) (λ s, begin end) sorry sorry }


-- /--
-- Given a limit cone `s` over the walking pair,
-- a zero object provides a pushout of `s.fst` and `s.snd`.
-- -/
-- def pushout_cocone_of_limit_fan [has_zero_object C] [has_zero_morphisms C]
--   {X Y : C} {s : binary_fan X Y} (h : is_limit s) :
--   colimit_cocone (span s.fst s.snd) :=
-- { cocone := pushout_cocone.mk (0 : X ⟶ 0) (0 : Y ⟶ 0) (by simp),
--   is_colimit := pushout_cocone.is_colimit_aux _ (λ s, 0) begin end sorry sorry }

-- /-- The pushout of a limit cone over the walking pair is zero. -/
-- def foo [has_zero_morphisms C] {X Y : C} {s : binary_fan X Y} (h : is_limit s) [has_pushout s.fst s.snd] :
--   is_zero (pushout s.fst s.snd) :=
-- { unique_to := λ Z, begin
--     fsplit,
--     fsplit,
--     fsplit,
--     exact 0,
--     intro f,
--     have := h.uniq,
-- end,
--   unique_from := sorry, }

end category_theory.limits

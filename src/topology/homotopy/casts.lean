/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
import topology.homotopy.fundamental_groupoid


/-!
# Fundamental group casts

This file defines `hcast`, which is just an abbreviation for `eq_to_hom` for the
fundamental groupoid. In particular, it accepts an equality `x₀ = x₁` and returns
an arrow from `x₀` to `x₁`, where `x₀` and `x₁` are points in some topological space.



-/
noncomputable theory

namespace fundamental_groupoid_functor
universe u
open fundamental_groupoid

local attribute [instance] path.homotopic.setoid

section

variables {X : Top} {x₀ x₁ x₀' x₁' : X} (p : path x₀ x₁)

/-- Abbreviation for `eq_to_hom` that accepts points in a topological space -/
abbreviation hcast (hx : x₀ = x₁) : from_top x₀ ⟶ x₁ := category_theory.eq_to_hom hx

-- Shouldn't this be unnecessary, since `hcast` is an abbreviation?
@[simp] lemma hcast_eq (hx₀ : x₀ = x₁) : hcast hx₀ = category_theory.eq_to_hom hx₀ := rfl

lemma path_cast_left  (hx₀ : x₀ = x₀') :
  hcast hx₀.symm ≫ ⟦p⟧ = ⟦p.cast hx₀.symm rfl⟧ :=
begin
  subst hx₀,
  simp only [hcast_eq, category_theory.category.id_comp, category_theory.eq_to_hom_refl],
  congr, ext, simp,
end

lemma path_cast_right (hx₁ : x₁ = x₁') :
  (⟦p⟧ ≫ hcast hx₁ : from_top x₀ ⟶ x₁') = ⟦p.cast rfl hx₁.symm⟧ :=
begin
  subst hx₁,
  simp only [hcast_eq, category_theory.category.comp_id, category_theory.eq_to_hom_refl],
  congr, ext, simp,
end

end

section


open_locale fundamental_groupoid

variables {X₁ X₂ Y : Top.{u}} {f : C(X₁, Y)} {g : C(X₂, Y)}
  {x₀ x₁ : X₁} {x₂ x₃ : X₂} {p : path x₀ x₁} {q : path x₂ x₃} (hfg : ∀ t, f (p t) = g (q t))

include hfg
private lemma start_path : f x₀ = g x₂ := by { convert hfg 0; simp only [path.source], }
private lemma end_path : f x₁ = g x₃ := by { convert hfg 1; simp only [path.target], }

/- If `f(p(t) = g(q(t))` for two paths `p` and `q`, then the induced path homotopy classes
`f(p)` and `g(p)` are the same as well, up to casts. -/
lemma eq_path_of_eq_image :
  (πₘ f).map ⟦p⟧ = hcast (start_path hfg) ≫ (πₘ g).map ⟦q⟧ ≫ hcast (end_path hfg).symm :=
begin
  simp only [map_eq, ← path.homotopic.map_lift, path_cast_right],
  rw path_cast_left _ (start_path hfg).symm,
  congr, ext, simp [hfg],
end

end

end fundamental_groupoid_functor

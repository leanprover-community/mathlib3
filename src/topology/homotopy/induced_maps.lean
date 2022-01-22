/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
import topology.homotopy.product
import topology.homotopy.equiv
import topology.homotopy.casts
import category_theory.equivalence

/-!
# Homotopic maps induce naturally isomorphic functors

## Main definitions

  - `fundamental_groupoid_functor.homotopic_maps_nat_iso H` The natural isomorphism
    between the induced functors `f : π(X) ⥤ π(Y)` and `g : π(X) ⥤ π(Y)`, given a homotopy
    `H : f ∼ g`

  - `fundamental_groupoid_functor.equiv_of_homotopy_equiv hequiv` The equivalence of the categories
    `π(X)` and `π(Y)` given a homotopy equivalence `hequiv : X ≃ₕ Y` between them.

## Implementation notes
  - In order to be more universe polymorphic, we use the lower level `path.homotopic.prod`, rather
    than `fundamental_groupoid_functor.prod_to_prod_Top`. The latter would have restricted `X` to
    be of universe level `Type`, the same as `I`. Unfortunately, this does make it a little more
    annoying in terms of simplifying what otherwise might have been a one-line `simp`, since we
    have to dig and use a method directly from `path.homotopic.prod`.
-/

noncomputable theory

universe u

namespace fundamental_groupoid_functor
open fundamental_groupoid
open category_theory

private abbreviation π := fundamental_groupoid_functor

section homotopic_maps_isomorphic
open_locale unit_interval

local attribute [instance] path.homotopic.setoid


/-- We let `X` and `Y` be spaces, and `f` and `g` be homotopic maps between them -/
parameters {X : Top.{u}} {Y : Top.{u}} {f g : C(X, Y)} (H : continuous_map.homotopy f g)

variables {x₀ x₁ : X} (p : path.homotopic.quotient x₀ x₁)

/--
These definitions set up the following diagram, for each path `p`:

          f(p)
      *--------*
      | \      |
  H₀  |   \ d  |  H₁
      |     \  |
      *--------*
          g(p)

Here, `H₀ = H.to_path x₀` is the path from `f(x₀)` to `g(x₀)`,
and similarly for `H₁`. Similarly, `f(p)` denotes the
path in Y that the induced map `f` takes `p`, and similarly for `g(p)`.

Finally, `d`, the diagonal path, is H(0 ⟶ 1, p), the result of the induced `H` on
`path.homotopic.prod (0 ⟶ 1) p`, where `(0 ⟶ 1)` denotes the path from `0` to `1` in `I`.

It is clear that the diagram commutes (`H₀ ≫ g(p) = d = f(p) ≫ H₁`), but unfortunately, many of the paths do not have defeq
starting/ending points, so we end up needing some casting.
-/

/- The path 0 ⟶ 1 in I -/
private def straight_path : path (0 : I) (1 : I) := { to_fun := id, source' := rfl, target' := rfl }

/-- Just a shortened form of H.to_continuous_map (also has the right type) -/
private abbreviation H_map : C(Top.of (I × X), Y) := H.to_continuous_map

/- The diagonal path `d` -/
private def diagonal_path : from_top (H (0, x₀)) ⟶ H (1, x₁) :=
(π.map H_map).map (path.homotopic.prod ⟦straight_path⟧ p)

/- The diagonal path, but starting from `f x₀` and going to `g x₁` -/
private def diagonal_path' : from_top (f x₀) ⟶ g x₁ :=
hcast (H.apply_zero x₀).symm ≫ (diagonal_path p) ≫ hcast (H.apply_one x₁)

/- Proof that `f(p) = H(0 ⟶ 0, p)`, with the appropriate casts -/
private lemma up_is_f : (π.map f).map p = hcast (H.apply_zero x₀).symm
  ≫ (π.map H_map).map (path.homotopic.prod ⟦path.refl (0 : I)⟧ p)
  ≫ hcast (H.apply_zero x₁) :=
begin
  apply quotient.induction_on p,
  intro p',
  rw path.homotopic.prod_lift,
  apply @eq_path_of_eq_image _ (Top.of (I × X)),
  simp,
end

/- Proof that `g(p) = H(1 ⟶ 1, p)`, with the appropriate casts -/
private lemma down_is_g : (π.map g).map p = hcast (H.apply_one x₀).symm
  ≫ ((π.map H_map).map (path.homotopic.prod ⟦path.refl (1 : I)⟧ p))
  ≫ hcast (H.apply_one x₁) :=
begin
  apply quotient.induction_on p,
  intro p',
  rw path.homotopic.prod_lift,
  apply @eq_path_of_eq_image _ (Top.of (I × X)),
  simp,
end

/- Proof that `H.to_path x = H(0 ⟶ 1, x ⟶ x)`, with the appropriate casts -/
private lemma H_to_path_eq (x : X) : ⟦H.to_path x⟧ =
  hcast (H.apply_zero x).symm ≫
  (π.map H_map).map (path.homotopic.prod ⟦straight_path⟧ ⟦path.refl x⟧) ≫
  hcast (H.apply_one x) :=
by { rw path.homotopic.prod_lift, simp only [map_eq, ← path.homotopic.map_lift,
  path_cast_left, path_cast_right], refl, }

/- Finally, we show `d = f(p) ≫ H₁ = H₀ ≫ g(p)` -/
private lemma eq_diag :
  (π.map f).map p ≫ ⟦H.to_path x₁⟧ = diagonal_path' p ∧
  (⟦H.to_path x₀⟧ ≫ (π.map g).map p : from_top (f x₀) ⟶ g x₁) = diagonal_path' p :=
begin
  rw [up_is_f H, down_is_g H, H_to_path_eq, H_to_path_eq],
  split;
  simp only [hcast_eq, category.id_comp, eq_to_hom_refl, category.assoc, eq_to_hom_trans_assoc,
    ← functor.map_comp_assoc];
  simp only [comp_eq, path.homotopic.comp_prod_eq_prod_comp];
  simp [← comp_eq, ← id_eq_path_refl]; refl,
end

/-- Given a homotopy H : f ∼ g, we have an associated natural isomorphism between the induced
functors `f` and `g` -/
def homotopic_maps_nat_iso : category_theory.nat_trans (π.map f) (π.map g) :=
{ app := λ x, ⟦H.to_path x⟧,
  naturality' := by { intros x y p, rw [(eq_diag H p).1, (eq_diag H p).2], } }

/-- In order for lean to recognize that `homotopic_maps_nat_iso` can be an isomorphism, we define
this abbreviation which is an arrow in the category of functors between π(X) and π(Y)-/
abbreviation homotopic_maps_nat_iso' : (π.map f) ⟶ (π.map g) := homotopic_maps_nat_iso

instance : is_iso homotopic_maps_nat_iso' :=
by apply nat_iso.is_iso_of_is_iso_app

end homotopic_maps_isomorphic

open_locale continuous_map

/-- Homotopy equivalent topological spaces have equivalent fundamental groupoids. -/
def equiv_of_homotopy_equiv {X Y : Top.{u}} (hequiv : X ≃ₕ Y) : (π.obj X).α ≌ (π.obj Y).α :=
begin
  apply category_theory.equivalence.mk
    (π.map hequiv.to_fun : (π.obj X).α ⥤ (π.obj Y).α)
    (π.map hequiv.inv_fun : (π.obj Y).α ⥤ (π.obj X).α);
  simp only [category_theory.Groupoid.hom_to_functor, category_theory.Groupoid.id_to_functor],
  { convert (as_iso (homotopic_maps_nat_iso' hequiv.left_inv.some)).symm,
    { exact (π.map_id X).symm, }, { exact (π.map_comp _ _).symm, } },
  { convert as_iso (homotopic_maps_nat_iso' hequiv.right_inv.some),
    { exact (π.map_comp _ _).symm, }, { exact (π.map_id Y).symm, } },
end

end fundamental_groupoid_functor

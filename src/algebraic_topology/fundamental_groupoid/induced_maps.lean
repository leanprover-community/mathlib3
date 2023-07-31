/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
import topology.homotopy.equiv
import category_theory.equivalence
import algebraic_topology.fundamental_groupoid.product

/-!
# Homotopic maps induce naturally isomorphic functors

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

  - `fundamental_groupoid_functor.homotopic_maps_nat_iso H` The natural isomorphism
    between the induced functors `f : π(X) ⥤ π(Y)` and `g : π(X) ⥤ π(Y)`, given a homotopy
    `H : f ∼ g`

  - `fundamental_groupoid_functor.equiv_of_homotopy_equiv hequiv` The equivalence of the categories
    `π(X)` and `π(Y)` given a homotopy equivalence `hequiv : X ≃ₕ Y` between them.

## Implementation notes
  - In order to be more universe polymorphic, we define `continuous_map.homotopy.ulift_map`
  which lifts a homotopy from `I × X → Y` to `(Top.of ((ulift I) × X)) → Y`. This is because
  this construction uses `fundamental_groupoid_functor.prod_to_prod_Top` to convert between
  pairs of paths in I and X and the corresponding path after passing through a homotopy `H`.
  But `fundamental_groupoid_functor.prod_to_prod_Top` requires two spaces in the same universe.
-/

noncomputable theory

universe u

open fundamental_groupoid
open category_theory
open fundamental_groupoid_functor

open_locale fundamental_groupoid
open_locale unit_interval

namespace unit_interval

/-- The path 0 ⟶ 1 in I -/
def path01 : path (0 : I) 1 := { to_fun := id, source' := rfl, target' := rfl }

/-- The path 0 ⟶ 1 in ulift I -/
def upath01 : path (ulift.up 0 : ulift.{u} I) (ulift.up 1) :=
{ to_fun := ulift.up, source' := rfl, target' := rfl }

local attribute [instance] path.homotopic.setoid
/-- The homotopy path class of 0 → 1 in `ulift I` -/
def uhpath01 : @from_top (Top.of $ ulift.{u} I) (ulift.up (0 : I)) ⟶ from_top (ulift.up 1) :=
⟦upath01⟧

end unit_interval

namespace continuous_map.homotopy
open unit_interval (uhpath01)

local attribute [instance] path.homotopic.setoid

section casts

/-- Abbreviation for `eq_to_hom` that accepts points in a topological space -/
abbreviation hcast {X : Top} {x₀ x₁ : X} (hx : x₀ = x₁) : from_top x₀ ⟶ from_top x₁ := eq_to_hom hx

@[simp] lemma hcast_def {X : Top} {x₀ x₁ : X} (hx₀ : x₀ = x₁) : hcast hx₀ = eq_to_hom hx₀ := rfl

variables {X₁ X₂ Y : Top.{u}} {f : C(X₁, Y)} {g : C(X₂, Y)}
  {x₀ x₁ : X₁} {x₂ x₃ : X₂} {p : path x₀ x₁} {q : path x₂ x₃} (hfg : ∀ t, f (p t) = g (q t))

include hfg

/-- If `f(p(t) = g(q(t))` for two paths `p` and `q`, then the induced path homotopy classes
`f(p)` and `g(p)` are the same as well, despite having a priori different types -/
lemma heq_path_of_eq_image : (πₘ f).map ⟦p⟧ == (πₘ g).map ⟦q⟧ :=
by { simp only [map_eq, ← path.homotopic.map_lift], apply path.homotopic.hpath_hext, exact hfg, }

private lemma start_path : f x₀ = g x₂ := by { convert hfg 0; simp only [path.source], }
private lemma end_path : f x₁ = g x₃ := by { convert hfg 1; simp only [path.target], }

lemma eq_path_of_eq_image :
  (πₘ f).map ⟦p⟧ = hcast (start_path hfg) ≫ (πₘ g).map ⟦q⟧ ≫ hcast (end_path hfg).symm :=
by { rw functor.conj_eq_to_hom_iff_heq, exact heq_path_of_eq_image hfg }

end casts

/- We let `X` and `Y` be spaces, and `f` and `g` be homotopic maps between them -/
variables {X Y : Top.{u}} {f g : C(X, Y)} (H : continuous_map.homotopy f g)
  {x₀ x₁ : X} (p : from_top x₀ ⟶ from_top x₁)

/-!
These definitions set up the following diagram, for each path `p`:

            f(p)
        *--------*
        | \      |
    H₀  |   \ d  |  H₁
        |     \  |
        *--------*
            g(p)

Here, `H₀ = H.eval_at x₀` is the path from `f(x₀)` to `g(x₀)`,
and similarly for `H₁`. Similarly, `f(p)` denotes the
path in Y that the induced map `f` takes `p`, and similarly for `g(p)`.

Finally, `d`, the diagonal path, is H(0 ⟶ 1, p), the result of the induced `H` on
`path.homotopic.prod (0 ⟶ 1) p`, where `(0 ⟶ 1)` denotes the path from `0` to `1` in `I`.

It is clear that the diagram commutes (`H₀ ≫ g(p) = d = f(p) ≫ H₁`), but unfortunately,
many of the paths do not have defeq starting/ending points, so we end up needing some casting.
-/

/-- Interpret a homotopy `H : C(I × X, Y) as a map C(ulift I × X, Y) -/
def ulift_map : C(Top.of (ulift.{u} I × X), Y) :=
⟨λ x, H (x.1.down, x.2),
  H.continuous.comp ((continuous_induced_dom.comp continuous_fst).prod_mk continuous_snd)⟩

@[simp] lemma ulift_apply (i : ulift.{u} I) (x : X) : H.ulift_map (i, x) = H (i.down, x) := rfl

/-- An abbreviation for `prod_to_prod_Top`, with some types already in place to help the
 typechecker. In particular, the first path should be on the ulifted unit interval. -/
abbreviation prod_to_prod_Top_I {a₁ a₂ : Top.of (ulift I)} {b₁ b₂ : X}
  (p₁ : from_top a₁ ⟶ from_top a₂) (p₂ : from_top b₁ ⟶ from_top b₂) :=
@category_theory.functor.map _ _ _ _ (prod_to_prod_Top (Top.of $ ulift I) X)
  (a₁, b₁) (a₂, b₂) (p₁, p₂)

/-- The diagonal path `d` of a homotopy `H` on a path `p` -/
def diagonal_path : from_top (H (0, x₀)) ⟶ from_top (H (1, x₁)) :=
(πₘ H.ulift_map).map (prod_to_prod_Top_I uhpath01 p)

/-- The diagonal path, but starting from `f x₀` and going to `g x₁` -/
def diagonal_path' : from_top (f x₀) ⟶ from_top (g x₁) :=
hcast (H.apply_zero x₀).symm ≫ (H.diagonal_path p) ≫ hcast (H.apply_one x₁)

/-- Proof that `f(p) = H(0 ⟶ 0, p)`, with the appropriate casts -/
lemma apply_zero_path : (πₘ f).map p = hcast (H.apply_zero x₀).symm ≫
(πₘ H.ulift_map).map (prod_to_prod_Top_I (𝟙 (ulift.up 0)) p) ≫
hcast (H.apply_zero x₁) :=
begin
  apply quotient.induction_on p,
  intro p',
  apply @eq_path_of_eq_image _ _ _ _ H.ulift_map _ _ _ _ _ ((path.refl (ulift.up _)).prod p'),
  simp,
end

/-- Proof that `g(p) = H(1 ⟶ 1, p)`, with the appropriate casts -/
lemma apply_one_path : (πₘ g).map p = hcast (H.apply_one x₀).symm ≫
((πₘ H.ulift_map).map (prod_to_prod_Top_I (𝟙 (ulift.up 1)) p)) ≫
hcast (H.apply_one x₁) :=
begin
  apply quotient.induction_on p,
  intro p',
  apply @eq_path_of_eq_image _ _ _ _ H.ulift_map _ _ _ _ _ ((path.refl (ulift.up _)).prod p'),
  simp,
end

/-- Proof that `H.eval_at x = H(0 ⟶ 1, x ⟶ x)`, with the appropriate casts -/
lemma eval_at_eq (x : X) : ⟦H.eval_at x⟧ =
  hcast (H.apply_zero x).symm ≫
(πₘ H.ulift_map).map (prod_to_prod_Top_I uhpath01 (𝟙 x)) ≫
hcast (H.apply_one x).symm.symm :=
begin
  dunfold prod_to_prod_Top_I uhpath01 hcast,
  refine (@functor.conj_eq_to_hom_iff_heq (πₓ Y) _ _ _ _ _ _ _ _ _).mpr _,
  simp only [id_eq_path_refl, prod_to_prod_Top_map, path.homotopic.prod_lift, map_eq,
    ← path.homotopic.map_lift],
  apply path.homotopic.hpath_hext, intro, refl,
end

/- Finally, we show `d = f(p) ≫ H₁ = H₀ ≫ g(p)` -/
lemma eq_diag_path :
  (πₘ f).map p ≫ ⟦H.eval_at x₁⟧ = H.diagonal_path' p ∧
  (⟦H.eval_at x₀⟧ ≫ (πₘ g).map p : from_top (f x₀) ⟶ from_top (g x₁)) = H.diagonal_path' p :=
begin
  rw [H.apply_zero_path, H.apply_one_path, H.eval_at_eq, H.eval_at_eq],
  dunfold prod_to_prod_Top_I,
  split; { slice_lhs 2 5 { simp [← category_theory.functor.map_comp], }, refl, },
end

end continuous_map.homotopy

namespace fundamental_groupoid_functor
open category_theory
open_locale fundamental_groupoid
local attribute [instance] path.homotopic.setoid

variables {X Y : Top.{u}} {f g : C(X, Y)} (H : continuous_map.homotopy f g)

/-- Given a homotopy H : f ∼ g, we have an associated natural isomorphism between the induced
functors `f` and `g` -/
def homotopic_maps_nat_iso : πₘ f ⟶ πₘ g :=
{ app := λ x, ⟦H.eval_at x⟧,
  naturality' := λ x y p, by rw [(H.eq_diag_path p).1, (H.eq_diag_path p).2] }

instance : is_iso (homotopic_maps_nat_iso H) := by apply nat_iso.is_iso_of_is_iso_app

open_locale continuous_map

/-- Homotopy equivalent topological spaces have equivalent fundamental groupoids. -/
def equiv_of_homotopy_equiv (hequiv : X ≃ₕ Y) : πₓ X ≌ πₓ Y :=
begin
  apply equivalence.mk
    (πₘ hequiv.to_fun : πₓ X ⥤ πₓ Y)
    (πₘ hequiv.inv_fun : πₓ Y ⥤ πₓ X);
  simp only [Groupoid.hom_to_functor, Groupoid.id_to_functor],
  { convert (as_iso (homotopic_maps_nat_iso hequiv.left_inv.some)).symm,
    exacts [((π).map_id X).symm, ((π).map_comp _ _).symm] },
  { convert as_iso (homotopic_maps_nat_iso hequiv.right_inv.some),
    exacts [((π).map_comp _ _).symm, ((π).map_id Y).symm] },
end

end fundamental_groupoid_functor

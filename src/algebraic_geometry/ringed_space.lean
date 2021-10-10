/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
import algebraic_geometry.sheafed_space
import algebraic_geometry.stalks
import algebra.category.CommRing.limits
import algebra.category.CommRing.colimits
import algebra.category.CommRing.filtered_colimits

/-!
# Ringed spaces

We introduce the category of ringed spaces, as an alias for `SheafedSpace CommRing`.

The facts collected in this file are typically stated for locally ringed spaces, but never actually
make use of the locality of stalks. See for instance https://stacks.math.columbia.edu/tag/01HZ.

-/

universe v

open category_theory
open topological_space
open opposite
open Top
open Top.presheaf

namespace algebraic_geometry

/-- The type of Ringed spaces, as an abbreviation for `SheafedSpace CommRing`. -/
abbreviation RingedSpace : Type* := SheafedSpace CommRing

namespace RingedSpace

open SheafedSpace

variables (X : RingedSpace.{v})

/--
If the germ of a section `f` is a unit in the stalk at `x`, then `f` must be a unit on some small
neighborhood around `x`.
-/
lemma is_unit_res_of_is_unit_germ (U : opens X) (f : X.presheaf.obj (op U)) (x : U)
  (h : is_unit (X.presheaf.germ x f)) :
  ∃ (V : opens X) (i : V ⟶ U) (hxV : x.1 ∈ V), is_unit (X.presheaf.map i.op f) :=
begin
  obtain ⟨g', heq⟩ := h.exists_right_inv,
  obtain ⟨V, hxV, g, rfl⟩ := X.presheaf.germ_exist x.1 g',
  let W := U ⊓ V,
  have hxW : x.1 ∈ W := ⟨x.2, hxV⟩,
  erw [← X.presheaf.germ_res_apply (opens.inf_le_left U V) ⟨x.1, hxW⟩ f,
    ← X.presheaf.germ_res_apply (opens.inf_le_right U V) ⟨x.1, hxW⟩ g,
    ← ring_hom.map_mul, ← ring_hom.map_one (X.presheaf.germ (⟨x.1, hxW⟩ : W))] at heq,
  obtain ⟨W', hxW', i₁, i₂, heq'⟩ := X.presheaf.germ_eq x.1 hxW hxW _ _ heq,
  use [W', i₁ ≫ opens.inf_le_left U V, hxW'],
  rw [ring_hom.map_one, ring_hom.map_mul, ← comp_apply, ← X.presheaf.map_comp, ← op_comp] at heq',
  exact is_unit_of_mul_eq_one _ _ heq',
end

/-- If a section `f` is a unit in each stalk, `f` must be a unit. -/
lemma is_unit_of_is_unit_germ (U : opens X) (f : X.presheaf.obj (op U))
  (h : ∀ x : U, is_unit (X.presheaf.germ x f)) :
  is_unit f :=
begin
  -- We pick a cover of `U` by open sets `V x`, such that `f` is a unit on each `V x`.
  choose V iVU m h_unit using λ x : U, X.is_unit_res_of_is_unit_germ U f x (h x),
  have hcover : U ≤ supr V,
  { intros x hxU,
    rw [subtype.val_eq_coe, opens.mem_coe, opens.mem_supr],
    exact ⟨⟨x, hxU⟩, m ⟨x, hxU⟩⟩ },
  -- Let `g x` denote the inverse of `f` in `U x`.
  choose g hg using λ x : U, is_unit.exists_right_inv (h_unit x),
  -- We claim that these local inverses glue together to a global inverse of `f`.
  obtain ⟨gl, gl_spec, -⟩ := X.sheaf.exists_unique_gluing' V U iVU hcover g _,
  swap,
  { intros x y,
    apply section_ext X.sheaf (V x ⊓ V y),
    rintro ⟨z, hzVx, hzVy⟩,
    rw [germ_res_apply, germ_res_apply],
    apply (is_unit.mul_right_inj (h ⟨z, (iVU x).le hzVx⟩)).mp,
    erw [← X.presheaf.germ_res_apply (iVU x) ⟨z, hzVx⟩ f, ← ring_hom.map_mul,
      congr_arg (X.presheaf.germ (⟨z, hzVx⟩ : V x)) (hg x), germ_res_apply,
      ← X.presheaf.germ_res_apply (iVU y) ⟨z, hzVy⟩ f, ← ring_hom.map_mul,
      congr_arg (X.presheaf.germ (⟨z, hzVy⟩ : V y)) (hg y),
      ring_hom.map_one, ring_hom.map_one] },
  apply is_unit_of_mul_eq_one f gl,
  apply X.sheaf.eq_of_locally_eq' V U iVU hcover,
  intro i,
  rw [ring_hom.map_one, ring_hom.map_mul, gl_spec],
  exact hg i,
end

/--
The basic open of a global section `f` is the set of all points `x`, such that the germ of `f` at
`x` is a unit.
-/
def basic_open (f : Γ.obj (op X)) : opens X :=
{ val := { x : X | is_unit (X.presheaf.germ (⟨x, trivial⟩ : (⊤ : opens X)) f) },
  property := begin
    rw is_open_iff_forall_mem_open,
    intros x hx,
    obtain ⟨U, i, hxU, hf⟩ := X.is_unit_res_of_is_unit_germ ⊤ f ⟨x, trivial⟩ hx,
    use U.1,
    refine ⟨_, U.2, hxU⟩,
    intros y hy,
    rw set.mem_set_of_eq,
    convert ring_hom.is_unit_map (X.presheaf.germ ⟨y, hy⟩) hf,
    exact (X.presheaf.germ_res_apply i ⟨y, hy⟩ f).symm,
  end }

@[simp]
lemma mem_basic_open (f : Γ.obj (op X)) (x : X) :
  x ∈ X.basic_open f ↔ is_unit (X.presheaf.germ (⟨x, trivial⟩ : (⊤ : opens X)) f) := iff.rfl

/-- The restriction of a global section `f` to the basic open of `f` is a unit. -/
lemma is_unit_res_basic_open (f : Γ.obj (op X)) :
  is_unit (X.presheaf.map (opens.le_top (X.basic_open f)).op f) :=
begin
  apply is_unit_of_is_unit_germ,
  rintro ⟨x, hx⟩,
  convert hx,
  rw germ_res_apply,
  refl,
end

end RingedSpace

end algebraic_geometry

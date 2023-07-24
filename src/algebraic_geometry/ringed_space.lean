/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer, Andrew Yang
-/
import algebra.category.Ring.filtered_colimits
import algebraic_geometry.sheafed_space
import topology.sheaves.stalks
import algebra.category.Ring.colimits
import algebra.category.Ring.limits

/-!
# Ringed spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We introduce the category of ringed spaces, as an alias for `SheafedSpace CommRing`.

The facts collected in this file are typically stated for locally ringed spaces, but never actually
make use of the locality of stalks. See for instance <https://stacks.math.columbia.edu/tag/01HZ>.

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
    rw [opens.mem_supr],
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
The basic open of a section `f` is the set of all points `x`, such that the germ of `f` at
`x` is a unit.
-/
def basic_open {U : opens X} (f : X.presheaf.obj (op U)) : opens X :=
{ carrier := coe '' { x : U | is_unit (X.presheaf.germ x f) },
  is_open' := begin
    rw is_open_iff_forall_mem_open,
    rintros _ ⟨x, hx, rfl⟩,
    obtain ⟨V, i, hxV, hf⟩ := X.is_unit_res_of_is_unit_germ U f x hx,
    use V.1,
    refine ⟨_, V.2, hxV⟩,
    intros y hy,
    use (⟨y, i.le hy⟩ : U),
    rw set.mem_set_of_eq,
    split,
    { convert ring_hom.is_unit_map (X.presheaf.germ ⟨y, hy⟩) hf,
      exact (X.presheaf.germ_res_apply i ⟨y, hy⟩ f).symm },
    { refl }
  end }

@[simp]
lemma mem_basic_open {U : opens X} (f : X.presheaf.obj (op U)) (x : U) :
  ↑x ∈ X.basic_open f ↔ is_unit (X.presheaf.germ x f) :=
begin
  split,
  { rintro ⟨x, hx, a⟩, cases subtype.eq a, exact hx },
  { intro h, exact ⟨x, h, rfl⟩ },
end

@[simp]
lemma mem_top_basic_open (f : X.presheaf.obj (op ⊤)) (x : X) :
  x ∈ X.basic_open f ↔ is_unit (X.presheaf.germ ⟨x, show x ∈ (⊤ : opens X), by trivial⟩ f) :=
mem_basic_open X f ⟨x, _⟩

lemma basic_open_le {U : opens X} (f : X.presheaf.obj (op U)) : X.basic_open f ≤ U :=
by { rintros _ ⟨x, hx, rfl⟩, exact x.2 }

/-- The restriction of a section `f` to the basic open of `f` is a unit. -/
lemma is_unit_res_basic_open {U : opens X} (f : X.presheaf.obj (op U)) :
  is_unit (X.presheaf.map (@hom_of_le (opens X) _ _ _ (X.basic_open_le f)).op f) :=
begin
  apply is_unit_of_is_unit_germ,
  rintro ⟨_, ⟨x, hx, rfl⟩⟩,
  convert hx,
  rw germ_res_apply,
  refl,
end

@[simp] lemma basic_open_res {U V : (opens X)ᵒᵖ} (i : U ⟶ V) (f : X.presheaf.obj U) :
  @basic_open X (unop V) (X.presheaf.map i f) = (unop V) ⊓ @basic_open X (unop U) f :=
begin
  induction U using opposite.rec,
  induction V using opposite.rec,
  let g := i.unop, have : i = g.op := rfl, clear_value g, subst this,
  ext, split,
  { rintro ⟨x, (hx : is_unit _), rfl⟩,
    rw germ_res_apply at hx,
    exact ⟨x.2, g x, hx, rfl⟩ },
  { rintros ⟨hxV, x, hx, rfl⟩,
    refine ⟨⟨x, hxV⟩, (_ : is_unit _), rfl⟩,
    rwa germ_res_apply }
end

-- This should fire before `basic_open_res`.
@[simp, priority 1100] lemma basic_open_res_eq {U V : (opens X)ᵒᵖ} (i : U ⟶ V) [is_iso i]
  (f : X.presheaf.obj U) :
  @basic_open X (unop V) (X.presheaf.map i f) = @RingedSpace.basic_open X (unop U) f :=
begin
  apply le_antisymm,
  { rw X.basic_open_res i f, exact inf_le_right },
  { have := X.basic_open_res (inv i) (X.presheaf.map i f),
    rw [← comp_apply, ← X.presheaf.map_comp, is_iso.hom_inv_id, X.presheaf.map_id] at this,
    erw this,
    exact inf_le_right }
end

@[simp] lemma basic_open_mul {U : opens X} (f g : X.presheaf.obj (op U)) :
  X.basic_open (f * g) = X.basic_open f ⊓ X.basic_open g :=
begin
  ext1,
  dsimp [RingedSpace.basic_open],
  rw ←set.image_inter subtype.coe_injective,
  congr,
  ext,
  simp_rw map_mul,
  exact is_unit.mul_iff,
end

lemma basic_open_of_is_unit {U : opens X} {f : X.presheaf.obj (op U)} (hf : is_unit f) :
  X.basic_open f = U :=
begin
  apply le_antisymm,
  { exact X.basic_open_le f },
  intros x hx,
  erw X.mem_basic_open f (⟨x, hx⟩ : U),
  exact ring_hom.is_unit_map _ hf
end

end RingedSpace

end algebraic_geometry

/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
import algebra.category.Module.basic
import algebra.category.CommRing.filtered_colimits

/-!
# The forgetful functor from `R`-modules preserves filtered colimits.

Forgetful functors from algebraic categories usually don't preserve colimits. However, they tend
to preserve _filtered_ colimits.

In this file, we start with a ring `R`, a small filtered category `J` and a functor
`F : J ⥤ Module R`. We show that the colimit of `F ⋙ forget₂ (Module R) AddCommGroup`
(in `AddCommGroup`) carries the structure of an `R`-module, thereby showing that the forgetful
functor `forget₂ (Module R) AddCommGroup` preserves filtered colimits. In particular, this implies
that `forget (Module R)` preserves filtered colimits.

-/

universes u v

noncomputable theory
open_locale classical

open category_theory
open category_theory.limits
open category_theory.is_filtered (renaming max → max') -- avoid name collision with `_root_.max`.

open AddMon.filtered_colimits (colimit_zero_eq colimit_add_mk_eq)

namespace Module.filtered_colimits

section

-- We use parameters here, mainly so we can have the abbreviations `M` and `M.mk` below, without
-- passing around `F` all the time.
parameters {R : Type u} [ring R] {J : Type v} [small_category J] [is_filtered J]
parameters (F : J ⥤ Module.{v} R)

/--
The colimit of `F ⋙ forget₂ (Module R) AddCommGroup` in the category `AddCommGroup`.
In the following, we will show that this has the structure of an `R`-module.
-/
abbreviation M : AddCommGroup :=
AddCommGroup.filtered_colimits.colimit (F ⋙ forget₂ (Module R) AddCommGroup)

/-- The canonical projection into the colimit, as a quotient type. -/
abbreviation M.mk : (Σ j, F.obj j) → M := quot.mk (types.quot.rel (F ⋙ forget (Module R)))

lemma M.mk_eq (x y : Σ j, F.obj j)
  (h : ∃ (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k), F.map f x.2 = F.map g y.2) :
  M.mk x = M.mk y :=
quot.eqv_gen_sound (types.filtered_colimit.eqv_gen_quot_rel_of_rel (F ⋙ forget (Module R)) x y h)

/-- The "unlifted" version of scalar multiplication in the colimit. -/
def colimit_smul_aux (r : R) (x : Σ j, F.obj j) : M :=
M.mk ⟨x.1, r • x.2⟩

lemma colimit_smul_aux_eq_of_rel (r : R) (x y : Σ j, F.obj j)
  (h : types.filtered_colimit.rel (F ⋙ forget (Module R)) x y) :
  colimit_smul_aux r x = colimit_smul_aux r y :=
begin
  apply M.mk_eq,
  obtain ⟨k, f, g, hfg⟩ := h,
  use [k, f, g],
  simp only [category_theory.functor.comp_map, forget_map_eq_coe] at hfg,
  rw [linear_map.map_smul, linear_map.map_smul, hfg],
end

/-- Scalar multiplication in the colimit. See also `colimit_smul_aux`. -/
instance colimit_has_scalar : has_scalar R M :=
{ smul := λ r x, begin
    refine quot.lift (colimit_smul_aux F r) _ x,
    intros x y h,
    apply colimit_smul_aux_eq_of_rel,
    apply types.filtered_colimit.rel_of_quot_rel,
    exact h,
  end }

@[simp]
lemma colimit_smul_mk_eq (r : R) (x : Σ j, F.obj j) : r • M.mk x = M.mk ⟨x.1, r • x.2⟩ := rfl

instance colimit_module : module R M :=
{ one_smul := λ x, begin
    apply quot.induction_on x, clear x, intro x, cases x with j x,
    erw [colimit_smul_mk_eq F 1 ⟨j, x⟩, one_smul],
    refl,
  end,
  mul_smul := λ r s x, begin
    apply quot.induction_on x, clear x, intro x, cases x with j x,
    erw [colimit_smul_mk_eq F (r * s) ⟨j, x⟩, colimit_smul_mk_eq F s ⟨j, x⟩,
      colimit_smul_mk_eq F r ⟨j, _⟩, mul_smul],
  end,
  smul_add := λ r x y, begin
    apply quot.induction_on₂ x y, clear x y, intros x y, cases x with i x, cases y with j y,
    erw [colimit_add_mk_eq _ ⟨i, x⟩ ⟨j, y⟩ (max' i j) (left_to_max i j) (right_to_max i j),
      colimit_smul_mk_eq, smul_add, colimit_smul_mk_eq, colimit_smul_mk_eq,
      colimit_add_mk_eq _ ⟨i, _⟩ ⟨j, _⟩ (max' i j) (left_to_max i j) (right_to_max i j),
      linear_map.map_smul, linear_map.map_smul],
    refl,
  end,
  smul_zero := λ r, begin
    erw [colimit_zero_eq _ (is_filtered.nonempty.some : J), colimit_smul_mk_eq, smul_zero],
    refl,
  end,
  zero_smul := λ x, begin
    apply quot.induction_on x, clear x, intro x, cases x with j x,
    erw [colimit_smul_mk_eq, zero_smul, colimit_zero_eq _ j],
    refl,
  end,
  add_smul := λ r s x, begin
    apply quot.induction_on x, clear x, intro x, cases x with j x,
    erw [colimit_smul_mk_eq, add_smul, colimit_smul_mk_eq, colimit_smul_mk_eq,
      colimit_add_mk_eq _ ⟨j, _⟩ ⟨j, _⟩ j (𝟙 j) (𝟙 j), category_theory.functor.map_id,
      id_apply, id_apply],
    refl,
  end }

/-- The bundled `R`-module giving the filtered colimit of a diagram. -/
def colimit : Module R := Module.of R M

/-- The linear map from a given `R`-module in the diagram to the colimit module. -/
def cocone_morphism (j : J) : F.obj j ⟶ colimit :=
{ map_smul' := λ r x, begin erw colimit_smul_mk_eq F r ⟨j, x⟩, refl, end,
.. (AddCommGroup.filtered_colimits.colimit_cocone (F ⋙ forget₂ (Module R) AddCommGroup)).ι.app j }

/-- The cocone over the proposed colimit module. -/
def colimit_cocone : cocone F :=
{ X := colimit,
  ι :=
  { app := cocone_morphism,
    naturality' := λ j j' f,
      linear_map.coe_injective ((types.colimit_cocone (F ⋙ forget (Module R))).ι.naturality f) } }

/--
Given a cocone `t` of `F`, the induced monoid linear map from the colimit to the cocone point.
We already know that this is a morphism between additive groups. The only thing left to see is that
it is a linear map, i.e. preserves scalar multiplication.
-/
def colimit_desc (t : cocone F) : colimit ⟶ t.X :=
{ map_smul' := λ r x, begin
    apply quot.induction_on x, clear x, intro x, cases x with j x,
    erw colimit_smul_mk_eq,
    exact linear_map.map_smul (t.ι.app j) r x,
  end,
  .. (AddCommGroup.filtered_colimits.colimit_cocone_is_colimit
      (F ⋙ forget₂ (Module R) AddCommGroup)).desc
      ((forget₂ (Module R) AddCommGroup.{v}).map_cocone t) }

/-- The proposed colimit cocone is a colimit in `Module R`. -/
def colimit_cocone_is_colimit : is_colimit colimit_cocone :=
{ desc := colimit_desc,
  fac' := λ t j, linear_map.coe_injective $
    (types.colimit_cocone_is_colimit (F ⋙ forget (Module R))).fac
    ((forget (Module R)).map_cocone t) j,
  uniq' := λ t m h, linear_map.coe_injective $
    (types.colimit_cocone_is_colimit (F ⋙ forget (Module R))).uniq
    ((forget (Module R)).map_cocone t) m ((λ j, funext $ λ x, linear_map.congr_fun (h j) x)) }

instance forget₂_AddCommGroup_preserves_filtered_colimits :
  preserves_filtered_colimits (forget₂ (Module R) AddCommGroup.{v}) :=
{ preserves_filtered_colimits := λ J _ _, by exactI
  { preserves_colimit := λ F, preserves_colimit_of_preserves_colimit_cocone
      (colimit_cocone_is_colimit F)
      (AddCommGroup.filtered_colimits.colimit_cocone_is_colimit
        (F ⋙ forget₂ (Module R) AddCommGroup.{v})) } }

instance forget_preserves_filtered_colimits : preserves_filtered_colimits (forget (Module R)) :=
limits.comp_preserves_filtered_colimits (forget₂ (Module R) AddCommGroup) (forget AddCommGroup)

end

end Module.filtered_colimits

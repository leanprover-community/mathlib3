/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Scott Morrison, Floris van Doorn
-/
import category_theory.fully_faithful
import category_theory.whiskering
import tactic.slice

namespace category_theory
open category_theory.functor nat_iso category
universes v₁ v₂ v₃ u₁ u₂ u₃ -- declare the `v`'s first; see `category_theory.category` for an explanation

/-- We define an equivalence as a (half)-adjoint equivalence, a pair of functors with
  a unit and counit which are natural isomorphisms and the triangle law `Fη ≫ εF = 1`, or in other
  words the composite `F ⟶ FGF ⟶ F` is the identity.

  The triangle equation is written as a family of equalities between morphisms, it is more
  complicated if we write it as an equality of natural transformations, because then we would have
  to insert natural transformations like `F ⟶ F1`.
-/
structure equivalence (C : Type u₁) [category.{v₁} C] (D : Type u₂) [category.{v₂} D] :=
mk' ::
(functor : C ⥤ D)
(inverse : D ⥤ C)
(unit_iso   : 𝟭 C ≅ functor ⋙ inverse)
(counit_iso : inverse ⋙ functor ≅ 𝟭 D)
(functor_unit_iso_comp' : ∀(X : C), functor.map ((unit_iso.hom : 𝟭 C ⟶ functor ⋙ inverse).app X) ≫
  counit_iso.hom.app (functor.obj X) = 𝟙 (functor.obj X) . obviously)

restate_axiom equivalence.functor_unit_iso_comp'

infixr ` ≌ `:10  := equivalence

variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]

namespace equivalence

abbreviation unit (e : C ≌ D) : 𝟭 C ⟶ e.functor ⋙ e.inverse := e.unit_iso.hom
abbreviation counit (e : C ≌ D) : e.inverse ⋙ e.functor ⟶ 𝟭 D := e.counit_iso.hom
abbreviation unit_inv (e : C ≌ D) : e.functor ⋙ e.inverse ⟶ 𝟭 C := e.unit_iso.inv
abbreviation counit_inv (e : C ≌ D) : 𝟭 D ⟶ e.inverse ⋙ e.functor := e.counit_iso.inv

/- While these abbreviations are convenient, they also cause some trouble,
preventing structure projections from unfolding. -/
@[simp] lemma equivalence_mk'_unit (functor inverse unit_iso counit_iso f) :
  (⟨functor, inverse, unit_iso, counit_iso, f⟩ : C ≌ D).unit = unit_iso.hom := rfl
@[simp] lemma equivalence_mk'_counit (functor inverse unit_iso counit_iso f) :
  (⟨functor, inverse, unit_iso, counit_iso, f⟩ : C ≌ D).counit = counit_iso.hom := rfl
@[simp] lemma equivalence_mk'_unit_inv (functor inverse unit_iso counit_iso f) :
  (⟨functor, inverse, unit_iso, counit_iso, f⟩ : C ≌ D).unit_inv = unit_iso.inv := rfl
@[simp] lemma equivalence_mk'_counit_inv (functor inverse unit_iso counit_iso f) :
  (⟨functor, inverse, unit_iso, counit_iso, f⟩ : C ≌ D).counit_inv = counit_iso.inv := rfl

@[simp] lemma functor_unit_comp (e : C ≌ D) (X : C) : e.functor.map (e.unit.app X) ≫
  e.counit.app (e.functor.obj X) = 𝟙 (e.functor.obj X) :=
e.functor_unit_iso_comp X

@[simp] lemma counit_inv_functor_comp (e : C ≌ D) (X : C) :
  e.counit_inv.app (e.functor.obj X) ≫ e.functor.map (e.unit_inv.app X) = 𝟙 (e.functor.obj X) :=
begin
  erw [iso.inv_eq_inv
    (e.functor.map_iso (e.unit_iso.app X) ≪≫ e.counit_iso.app (e.functor.obj X)) (iso.refl _)],
  exact e.functor_unit_comp X
end

lemma functor_unit (e : C ≌ D) (X : C) :
  e.functor.map (e.unit.app X) = e.counit_inv.app (e.functor.obj X) :=
by { erw [←iso.comp_hom_eq_id (e.counit_iso.app _), functor_unit_comp], refl }

lemma counit_functor (e : C ≌ D) (X : C) :
  e.counit.app (e.functor.obj X) = e.functor.map (e.unit_inv.app X) :=
by { erw [←iso.hom_comp_eq_id (e.functor.map_iso (e.unit_iso.app X)), functor_unit_comp], refl }

/-- The other triangle equality. The proof follows the following proof in Globular:
  http://globular.science/1905.001 -/
@[simp] lemma unit_inverse_comp (e : C ≌ D) (Y : D) :
  e.unit.app (e.inverse.obj Y) ≫ e.inverse.map (e.counit.app Y) = 𝟙 (e.inverse.obj Y) :=
begin
  rw [←id_comp (e.inverse.map _), ←map_id e.inverse, ←counit_inv_functor_comp, map_comp,
      ←iso.hom_inv_id_assoc (e.unit_iso.app _) (e.inverse.map (e.functor.map _)),
      app_hom, app_inv],
  slice_lhs 2 3 { erw [e.unit.naturality] },
  slice_lhs 1 2 { erw [e.unit.naturality] },
  slice_lhs 4 4
  { rw [←iso.hom_inv_id_assoc (e.inverse.map_iso (e.counit_iso.app _)) (e.unit_inv.app _)] },
  slice_lhs 3 4 { erw [←map_comp e.inverse, e.counit.naturality],
    erw [(e.counit_iso.app _).hom_inv_id, map_id] }, erw [id_comp],
  slice_lhs 2 3 { erw [←map_comp e.inverse, e.counit_iso.inv.naturality, map_comp] },
  slice_lhs 3 4 { erw [e.unit_inv.naturality] },
  slice_lhs 4 5 { erw [←map_comp (e.functor ⋙ e.inverse), (e.unit_iso.app _).hom_inv_id, map_id] },
  erw [id_comp],
  slice_lhs 3 4 { erw [←e.unit_inv.naturality] },
  slice_lhs 2 3 { erw [←map_comp e.inverse, ←e.counit_iso.inv.naturality,
    (e.counit_iso.app _).hom_inv_id, map_id] }, erw [id_comp, (e.unit_iso.app _).hom_inv_id], refl
end

@[simp] lemma inverse_counit_inv_comp (e : C ≌ D) (Y : D) :
  e.inverse.map (e.counit_inv.app Y) ≫ e.unit_inv.app (e.inverse.obj Y) = 𝟙 (e.inverse.obj Y) :=
begin
  erw [iso.inv_eq_inv
    (e.unit_iso.app (e.inverse.obj Y) ≪≫ e.inverse.map_iso (e.counit_iso.app Y)) (iso.refl _)],
  exact e.unit_inverse_comp Y
end

lemma unit_inverse (e : C ≌ D) (Y : D) :
  e.unit.app (e.inverse.obj Y) = e.inverse.map (e.counit_inv.app Y) :=
by { erw [←iso.comp_hom_eq_id (e.inverse.map_iso (e.counit_iso.app Y)), unit_inverse_comp], refl }

lemma inverse_counit (e : C ≌ D) (Y : D) :
  e.inverse.map (e.counit.app Y) = e.unit_inv.app (e.inverse.obj Y) :=
by { erw [←iso.hom_comp_eq_id (e.unit_iso.app _), unit_inverse_comp], refl }

@[simp] lemma fun_inv_map (e : C ≌ D) (X Y : D) (f : X ⟶ Y) :
  e.functor.map (e.inverse.map f) = e.counit.app X ≫ f ≫ e.counit_inv.app Y :=
(nat_iso.naturality_2 (e.counit_iso) f).symm

@[simp] lemma inv_fun_map (e : C ≌ D) (X Y : C) (f : X ⟶ Y) :
  e.inverse.map (e.functor.map f) = e.unit_inv.app X ≫ f ≫ e.unit.app Y :=
(nat_iso.naturality_1 (e.unit_iso) f).symm

section
-- In this section we convert an arbitrary equivalence to a half-adjoint equivalence.
variables {F : C ⥤ D} {G : D ⥤ C} (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D)

def adjointify_η : 𝟭 C ≅ F ⋙ G :=
calc
  𝟭 C ≅ F ⋙ G               : η
  ... ≅ F ⋙ (𝟭 D ⋙ G)      : iso_whisker_left F (left_unitor G).symm
  ... ≅ F ⋙ ((G ⋙ F) ⋙ G) : iso_whisker_left F (iso_whisker_right ε.symm G)
  ... ≅ F ⋙ (G ⋙ (F ⋙ G)) : iso_whisker_left F (associator G F G)
  ... ≅ (F ⋙ G) ⋙ (F ⋙ G) : (associator F G (F ⋙ G)).symm
  ... ≅ 𝟭 C ⋙ (F ⋙ G)      : iso_whisker_right η.symm (F ⋙ G)
  ... ≅ F ⋙ G               : left_unitor (F ⋙ G)

lemma adjointify_η_ε (X : C) :
  F.map ((adjointify_η η ε).hom.app X) ≫ ε.hom.app (F.obj X) = 𝟙 (F.obj X) :=
begin
  dsimp [adjointify_η], simp,
  have := ε.hom.naturality (F.map (η.inv.app X)), dsimp at this, rw [this], clear this,
  rw [←assoc _ _ (F.map _)],
  have := ε.hom.naturality (ε.inv.app $ F.obj X), dsimp at this, rw [this], clear this,
  have := (ε.app $ F.obj X).hom_inv_id, dsimp at this, rw [this], clear this,
  rw [id_comp], have := (F.map_iso $ η.app X).hom_inv_id, dsimp at this, rw [this]
end

end

protected definition mk (F : C ⥤ D) (G : D ⥤ C)
  (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D) : C ≌ D :=
⟨F, G, adjointify_η η ε, ε, adjointify_η_ε η ε⟩

@[refl, simps] def refl : C ≌ C :=
⟨𝟭 C, 𝟭 C, iso.refl _, iso.refl _, λ X, category.id_comp _⟩

@[symm, simps] def symm (e : C ≌ D) : D ≌ C :=
⟨e.inverse, e.functor, e.counit_iso.symm, e.unit_iso.symm, e.inverse_counit_inv_comp⟩

variables {E : Type u₃} [category.{v₃} E]

@[trans, simps] def trans (e : C ≌ D) (f : D ≌ E) : C ≌ E :=
{ functor := e.functor ⋙ f.functor,
  inverse := f.inverse ⋙ e.inverse,
  unit_iso :=
  begin
    refine iso.trans e.unit_iso _,
    exact iso_whisker_left e.functor (iso_whisker_right f.unit_iso e.inverse) ,
  end,
  counit_iso :=
  begin
    refine iso.trans _ f.counit_iso,
    exact iso_whisker_left f.inverse (iso_whisker_right e.counit_iso f.functor)
  end,
  -- We wouldn't have need to give this proof if we'd used `equivalence.mk`,
  -- but we choose to avoid using that here, for the sake of good structure projection `simp` lemmas.
  functor_unit_iso_comp' := λ X,
  begin
    dsimp,
    rw [← f.functor.map_comp_assoc, e.functor.map_comp, functor_unit, fun_inv_map,
        iso.inv_hom_id_app_assoc, assoc, iso.inv_hom_id_app, counit_functor, ← functor.map_comp],
    erw [comp_id, iso.hom_inv_id_app, functor.map_id],
  end }

def fun_inv_id_assoc (e : C ≌ D) (F : C ⥤ E) : e.functor ⋙ e.inverse ⋙ F ≅ F :=
(functor.associator _ _ _).symm ≪≫ iso_whisker_right e.unit_iso.symm F ≪≫ F.left_unitor

@[simp] lemma fun_inv_id_assoc_hom_app (e : C ≌ D) (F : C ⥤ E) (X : C) :
  (fun_inv_id_assoc e F).hom.app X = F.map (e.unit_inv.app X) :=
by { dsimp [fun_inv_id_assoc], tidy }

@[simp] lemma fun_inv_id_assoc_inv_app (e : C ≌ D) (F : C ⥤ E) (X : C) :
  (fun_inv_id_assoc e F).inv.app X = F.map (e.unit.app X) :=
by { dsimp [fun_inv_id_assoc], tidy }

def inv_fun_id_assoc (e : C ≌ D) (F : D ⥤ E) : e.inverse ⋙ e.functor ⋙ F ≅ F :=
(functor.associator _ _ _).symm ≪≫ iso_whisker_right e.counit_iso F ≪≫ F.left_unitor

@[simp] lemma inv_fun_id_assoc_hom_app (e : C ≌ D) (F : D ⥤ E) (X : D) :
  (inv_fun_id_assoc e F).hom.app X = F.map (e.counit.app X) :=
by { dsimp [inv_fun_id_assoc], tidy }

@[simp] lemma inv_fun_id_assoc_inv_app (e : C ≌ D) (F : D ⥤ E) (X : D) :
  (inv_fun_id_assoc e F).inv.app X = F.map (e.counit_inv.app X) :=
by { dsimp [inv_fun_id_assoc], tidy }

section

-- There's of course a monoid structure on `C ≌ C`,
-- but let's not encourage using it.
-- The power structure is nevertheless useful.

/-- Powers of an auto-equivalence. -/
def pow (e : C ≌ C) : ℤ → (C ≌ C)
| (int.of_nat 0) := equivalence.refl
| (int.of_nat 1) := e
| (int.of_nat (n+2)) := e.trans (pow (int.of_nat (n+1)))
| (int.neg_succ_of_nat 0) := e.symm
| (int.neg_succ_of_nat (n+1)) := e.symm.trans (pow (int.neg_succ_of_nat n))

instance : has_pow (C ≌ C) ℤ := ⟨pow⟩

@[simp] lemma pow_zero (e : C ≌ C) : e^(0 : ℤ) = equivalence.refl := rfl
@[simp] lemma pow_one (e : C ≌ C) : e^(1 : ℤ) = e := rfl
@[simp] lemma pow_minus_one (e : C ≌ C) : e^(-1 : ℤ) = e.symm := rfl

-- TODO as necessary, add the natural isomorphisms `(e^a).trans e^b ≅ e^(a+b)`.
-- At this point, we haven't even defined the category of equivalences.

end

end equivalence


/-- A functor that is part of a (half) adjoint equivalence -/
class is_equivalence (F : C ⥤ D) :=
mk' ::
(inverse    : D ⥤ C)
(unit_iso   : 𝟭 C ≅ F ⋙ inverse)
(counit_iso : inverse ⋙ F ≅ 𝟭 D)
(functor_unit_iso_comp' : ∀ (X : C), F.map ((unit_iso.hom : 𝟭 C ⟶ F ⋙ inverse).app X) ≫
  counit_iso.hom.app (F.obj X) = 𝟙 (F.obj X) . obviously)

restate_axiom is_equivalence.functor_unit_iso_comp'

namespace is_equivalence

instance of_equivalence (F : C ≌ D) : is_equivalence F.functor :=
{ ..F }

instance of_equivalence_inverse (F : C ≌ D) : is_equivalence F.inverse :=
is_equivalence.of_equivalence F.symm

open equivalence
protected definition mk {F : C ⥤ D} (G : D ⥤ C)
  (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D) : is_equivalence F :=
⟨G, adjointify_η η ε, ε, adjointify_η_ε η ε⟩

end is_equivalence


namespace functor

def as_equivalence (F : C ⥤ D) [is_equivalence F] : C ≌ D :=
⟨F, is_equivalence.inverse F, is_equivalence.unit_iso, is_equivalence.counit_iso,
  is_equivalence.functor_unit_iso_comp⟩

instance is_equivalence_refl : is_equivalence (𝟭 C) :=
is_equivalence.of_equivalence equivalence.refl

def inv (F : C ⥤ D) [is_equivalence F] : D ⥤ C :=
is_equivalence.inverse F

instance is_equivalence_inv (F : C ⥤ D) [is_equivalence F] : is_equivalence F.inv :=
is_equivalence.of_equivalence F.as_equivalence.symm

@[simp] lemma as_equivalence_functor (F : C ⥤ D) [is_equivalence F] :
  F.as_equivalence.functor = F := rfl

@[simp] lemma as_equivalence_inverse (F : C ⥤ D) [is_equivalence F] :
  F.as_equivalence.inverse = inv F := rfl

@[simp] lemma inv_inv (F : C ⥤ D) [is_equivalence F] :
  inv (inv F) = F := rfl

def fun_inv_id (F : C ⥤ D) [is_equivalence F] : F ⋙ F.inv ≅ 𝟭 C :=
is_equivalence.unit_iso.symm

def inv_fun_id (F : C ⥤ D) [is_equivalence F] : F.inv ⋙ F ≅ 𝟭 D :=
is_equivalence.counit_iso

variables {E : Type u₃} [category.{v₃} E]

instance is_equivalence_trans (F : C ⥤ D) (G : D ⥤ E) [is_equivalence F] [is_equivalence G] :
  is_equivalence (F ⋙ G) :=
is_equivalence.of_equivalence (equivalence.trans (as_equivalence F) (as_equivalence G))

end functor

namespace equivalence

@[simp]
lemma functor_inv (E : C ≌ D) : E.functor.inv = E.inverse := rfl

@[simp]
lemma inverse_inv (E : C ≌ D) : E.inverse.inv = E.functor := rfl

@[simp]
lemma functor_as_equivalence (E : C ≌ D) : E.functor.as_equivalence = E :=
by { cases E, congr, }

@[simp]
lemma inverse_as_equivalence (E : C ≌ D) : E.inverse.as_equivalence = E.symm :=
by { cases E, congr, }

end equivalence

namespace is_equivalence

@[simp] lemma fun_inv_map (F : C ⥤ D) [is_equivalence F] (X Y : D) (f : X ⟶ Y) :
  F.map (F.inv.map f) = F.inv_fun_id.hom.app X ≫ f ≫ F.inv_fun_id.inv.app Y :=
begin
  erw [nat_iso.naturality_2],
  refl
end
@[simp] lemma inv_fun_map (F : C ⥤ D) [is_equivalence F] (X Y : C) (f : X ⟶ Y) :
  F.inv.map (F.map f) = F.fun_inv_id.hom.app X ≫ f ≫ F.fun_inv_id.inv.app Y :=
begin
  erw [nat_iso.naturality_2],
  refl
end

-- We should probably restate many of the lemmas about `equivalence` for `is_equivalence`,
-- but these are the only ones I need for now.
@[simp] lemma functor_unit_comp (E : C ⥤ D) [is_equivalence E] (Y) :
  E.map (is_equivalence.unit_iso.hom.app Y) ≫ is_equivalence.counit_iso.hom.app (E.obj Y) = 𝟙 _ :=
equivalence.functor_unit_comp (E.as_equivalence) Y

@[simp] lemma counit_inv_functor_comp (E : C ⥤ D) [is_equivalence E] (Y) :
  is_equivalence.counit_iso.inv.app (E.obj Y) ≫ E.map (is_equivalence.unit_iso.inv.app Y) = 𝟙 _ :=
eq_of_inv_eq_inv (functor_unit_comp _ _)

end is_equivalence

class ess_surj (F : C ⥤ D) :=
(obj_preimage (d : D) : C)
(iso' (d : D) : F.obj (obj_preimage d) ≅ d . obviously)

restate_axiom ess_surj.iso'

namespace functor
def obj_preimage (F : C ⥤ D) [ess_surj F] (d : D) : C := ess_surj.obj_preimage.{v₁ v₂} F d
def fun_obj_preimage_iso (F : C ⥤ D) [ess_surj F] (d : D) : F.obj (F.obj_preimage d) ≅ d :=
ess_surj.iso d
end functor

namespace equivalence

def ess_surj_of_equivalence (F : C ⥤ D) [is_equivalence F] : ess_surj F :=
⟨ λ Y : D, F.inv.obj Y, λ Y : D, (F.inv_fun_id.app Y) ⟩

@[priority 100] -- see Note [lower instance priority]
instance faithful_of_equivalence (F : C ⥤ D) [is_equivalence F] : faithful F :=
{ map_injective' := λ X Y f g w,
  begin
    have p := congr_arg (@category_theory.functor.map _ _ _ _ F.inv _ _) w,
    simpa only [cancel_epi, cancel_mono, is_equivalence.inv_fun_map] using p
  end }.

@[priority 100] -- see Note [lower instance priority]
instance full_of_equivalence (F : C ⥤ D) [is_equivalence F] : full F :=
{ preimage := λ X Y f, F.fun_inv_id.inv.app X ≫ F.inv.map f ≫ F.fun_inv_id.hom.app Y,
  witness' := λ X Y f, F.inv.map_injective
  (by simpa only [is_equivalence.inv_fun_map, assoc, iso.hom_inv_id_app_assoc, iso.hom_inv_id_app] using comp_id _) }

@[simp] private def equivalence_inverse (F : C ⥤ D) [full F] [faithful F] [ess_surj F] : D ⥤ C :=
{ obj  := λ X, F.obj_preimage X,
  map := λ X Y f, F.preimage ((F.fun_obj_preimage_iso X).hom ≫ f ≫ (F.fun_obj_preimage_iso Y).inv),
  map_id' := λ X, begin apply F.map_injective, tidy end,
  map_comp' := λ X Y Z f g, by apply F.map_injective; simp }

def equivalence_of_fully_faithfully_ess_surj
  (F : C ⥤ D) [full F] [faithful F] [ess_surj F] : is_equivalence F :=
is_equivalence.mk (equivalence_inverse F)
  (nat_iso.of_components
    (λ X, (preimage_iso $ F.fun_obj_preimage_iso $ F.obj X).symm)
    (λ X Y f, by { apply F.map_injective, obviously }))
  (nat_iso.of_components
    (λ Y, F.fun_obj_preimage_iso Y)
    (by obviously))

@[simp] lemma functor_map_inj_iff (e : C ≌ D) {X Y : C} (f g : X ⟶ Y) : e.functor.map f = e.functor.map g ↔ f = g :=
begin
  split,
  { intro w, apply e.functor.map_injective, exact w, },
  { rintro ⟨rfl⟩, refl, }
end

@[simp] lemma inverse_map_inj_iff (e : C ≌ D) {X Y : D} (f g : X ⟶ Y) : e.inverse.map f = e.inverse.map g ↔ f = g :=
begin
  split,
  { intro w, apply e.inverse.map_injective, exact w, },
  { rintro ⟨rfl⟩, refl, }
end

end equivalence

end category_theory

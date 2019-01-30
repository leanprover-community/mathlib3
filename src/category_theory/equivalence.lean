-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import category_theory.fully_faithful
import category_theory.functor_category
import category_theory.natural_isomorphism
import tactic.slice
import tactic.converter.interactive

namespace category_theory

universes v₁ v₂ v₃ u₁ u₂ u₃ -- declare the `v`'s first; see `category_theory.category` for an explanation

structure equivalence (C : Type u₁) [category.{v₁} C] (D : Type u₂) [category.{v₂} D] :=
(functor : C ⥤ D)
(inverse : D ⥤ C)
(fun_inv_id' : (functor ⋙ inverse) ≅ (category_theory.functor.id C) . obviously)
(inv_fun_id' : (inverse ⋙ functor) ≅ (category_theory.functor.id D) . obviously)

restate_axiom equivalence.fun_inv_id'
restate_axiom equivalence.inv_fun_id'

infixr ` ≌ `:10  := equivalence

namespace equivalence

variables {C : Type u₁} [𝒞 : category.{v₁} C]
include 𝒞

@[refl] def refl : C ≌ C :=
{ functor := functor.id C,
  inverse := functor.id C }

variables {D : Type u₂} [𝒟 : category.{v₂} D]
include 𝒟

@[symm] def symm (e : C ≌ D) : D ≌ C :=
{ functor := e.inverse,
  inverse := e.functor,
  fun_inv_id' := e.inv_fun_id,
  inv_fun_id' := e.fun_inv_id }

@[simp] lemma fun_inv_map (e : C ≌ D) (X Y : D) (f : X ⟶ Y) :
e.functor.map (e.inverse.map f) = (e.inv_fun_id.hom.app X) ≫ f ≫ (e.inv_fun_id.inv.app Y) :=
begin
  erw [nat_iso.naturality_2],
  refl
end
@[simp] lemma inv_fun_map (e : C ≌ D) (X Y : C) (f : X ⟶ Y) :
e.inverse.map (e.functor.map f) = (e.fun_inv_id.hom.app X) ≫ f ≫ (e.fun_inv_id.inv.app Y) :=
begin
  erw [nat_iso.naturality_2],
  refl
end

variables {E : Type u₃} [ℰ : category.{v₃} E]
include ℰ

@[simp] private def effe_iso_id (e : C ≌ D) (f : D ≌ E) (X : C) :
  (e.inverse).obj ((f.inverse).obj ((f.functor).obj ((e.functor).obj X))) ≅ X :=
calc
  (e.inverse).obj ((f.inverse).obj ((f.functor).obj ((e.functor).obj X)))
    ≅ (e.inverse).obj ((e.functor).obj X) : e.inverse.on_iso (nat_iso.app f.fun_inv_id _)
... ≅ X                                   : nat_iso.app e.fun_inv_id _

@[simp] private def feef_iso_id (e : C ≌ D) (f : D ≌ E) (X : E) :
  (f.functor).obj ((e.functor).obj ((e.inverse).obj ((f.inverse).obj X))) ≅ X :=
calc
  (f.functor).obj ((e.functor).obj ((e.inverse).obj ((f.inverse).obj X)))
    ≅ (f.functor).obj ((f.inverse).obj X) : f.functor.on_iso (nat_iso.app e.inv_fun_id _)
... ≅ X                                   : nat_iso.app f.inv_fun_id _

@[trans] def trans (e : C ≌ D) (f : D ≌ E) : C ≌ E :=
{ functor := e.functor ⋙ f.functor,
  inverse := f.inverse ⋙ e.inverse,
  fun_inv_id' := nat_iso.of_components (effe_iso_id e f)
  begin
    /- `tidy` says -/
    intros X Y f_1, dsimp at *, simp at *, dsimp at *,
    /- `rewrite_search` says -/
    slice_lhs 3 4 { erw [is_iso.hom_inv_id] },
    erw [category.id_comp, is_iso.hom_inv_id, category.comp_id],
  end,
  inv_fun_id' := nat_iso.of_components (feef_iso_id e f)
  begin
    /- `tidy` says -/
    intros X Y f_1, dsimp at *, simp at *, dsimp at *,
    /- `rewrite_search` says -/
    slice_lhs 3 4 { erw [is_iso.hom_inv_id] },
    erw [category.id_comp, is_iso.hom_inv_id, category.comp_id]
  end
}

end equivalence

variables {C : Type u₁} [𝒞 : category.{v₁} C]
include 𝒞

section
variables {D : Type u₂} [𝒟 : category.{v₂} D]
include 𝒟

class is_equivalence (F : C ⥤ D) :=
(inverse        : D ⥤ C)
(fun_inv_id' : (F ⋙ inverse) ≅ (functor.id C) . obviously)
(inv_fun_id' : (inverse ⋙ F) ≅ (functor.id D) . obviously)

restate_axiom is_equivalence.fun_inv_id'
restate_axiom is_equivalence.inv_fun_id'
end

namespace is_equivalence
variables {D : Type u₂} [𝒟 : category.{v₂} D]
include 𝒟

instance of_equivalence (F : C ≌ D) : is_equivalence (F.functor) :=
{ inverse := F.inverse,
  fun_inv_id' := F.fun_inv_id,
  inv_fun_id' := F.inv_fun_id }
instance of_equivalence_inverse (F : C ≌ D) : is_equivalence (F.inverse) :=
{ inverse := F.functor,
  fun_inv_id' := F.inv_fun_id,
  inv_fun_id' := F.fun_inv_id }
end is_equivalence

namespace functor
instance is_equivalence_refl : is_equivalence (functor.id C) :=
{ inverse := functor.id C }
end functor

variables {D : Type u₂} [𝒟 : category.{v₂} D]
include 𝒟

namespace functor
def inv (F : C ⥤ D) [is_equivalence F] : D ⥤ C :=
is_equivalence.inverse F

instance is_equivalence_symm (F : C ⥤ D) [is_equivalence F] : is_equivalence (F.inv) :=
{ inverse := F,
  fun_inv_id' := is_equivalence.inv_fun_id F,
  inv_fun_id' := is_equivalence.fun_inv_id F }

def fun_inv_id (F : C ⥤ D) [is_equivalence F] : (F ⋙ F.inv) ≅ functor.id C :=
is_equivalence.fun_inv_id F

def inv_fun_id (F : C ⥤ D) [is_equivalence F] : (F.inv ⋙ F) ≅ functor.id D :=
is_equivalence.inv_fun_id F

def as_equivalence (F : C ⥤ D) [is_equivalence F] : C ≌ D :=
{ functor := F,
  inverse := is_equivalence.inverse F,
  fun_inv_id' := is_equivalence.fun_inv_id F,
  inv_fun_id' := is_equivalence.inv_fun_id F }

variables {E : Type u₃} [ℰ : category.{v₃} E]
include ℰ

instance is_equivalence_trans (F : C ⥤ D) (G : D ⥤ E) [is_equivalence F] [is_equivalence G] :
  is_equivalence (F ⋙ G) :=
is_equivalence.of_equivalence (equivalence.trans (as_equivalence F) (as_equivalence G))

end functor

namespace is_equivalence
instance is_equivalence_functor (e : C ≌ D) : is_equivalence e.functor :=
{ inverse := e.inverse,
  fun_inv_id' := e.fun_inv_id,
  inv_fun_id' := e.inv_fun_id }
instance is_equivalence_inverse (e : C ≌ D) : is_equivalence e.inverse :=
{ inverse := e.functor,
  fun_inv_id' := e.inv_fun_id,
  inv_fun_id' := e.fun_inv_id }

@[simp] lemma fun_inv_map (F : C ⥤ D) [is_equivalence F] (X Y : D) (f : X ⟶ Y) :
  F.map (F.inv.map f) = (F.inv_fun_id.hom.app X) ≫ f ≫ (F.inv_fun_id.inv.app Y) :=
begin
  erw [nat_iso.naturality_2],
  refl
end
@[simp] lemma inv_fun_map (F : C ⥤ D) [is_equivalence F] (X Y : C) (f : X ⟶ Y) :
  F.inv.map (F.map f) = (F.fun_inv_id.hom.app X) ≫ f ≫ (F.fun_inv_id.inv.app Y) :=
begin
  erw [nat_iso.naturality_2],
  refl
end

end is_equivalence

class ess_surj (F : C ⥤ D) :=
(obj_preimage (d : D) : C)
(iso' (d : D) : F.obj (obj_preimage d) ≅ d . obviously)

restate_axiom ess_surj.iso'

namespace functor
def obj_preimage (F : C ⥤ D) [ess_surj F] (d : D) : C := ess_surj.obj_preimage.{v₁ v₂} F d
def fun_obj_preimage_iso (F : C ⥤ D) [ess_surj F] (d : D) : F.obj (F.obj_preimage d) ≅ d :=
ess_surj.iso F d
end functor

namespace category_theory.equivalence

def ess_surj_of_equivalence (F : C ⥤ D) [is_equivalence F] : ess_surj F :=
⟨ λ Y : D, F.inv.obj Y, λ Y : D, (nat_iso.app F.inv_fun_id Y) ⟩

instance faithful_of_equivalence (F : C ⥤ D) [is_equivalence F] : faithful F :=
{ injectivity' := λ X Y f g w,
  begin
    have p := congr_arg (@category_theory.functor.map _ _ _ _ F.inv _ _) w,
    simp at *,
    assumption
  end }.

instance full_of_equivalence (F : C ⥤ D) [is_equivalence F] : full F :=
{ preimage := λ X Y f, (nat_iso.app F.fun_inv_id X).inv ≫ (F.inv.map f) ≫ (nat_iso.app F.fun_inv_id Y).hom,
  witness' := λ X Y f,
  begin
    apply F.inv.injectivity,
    /- obviously can finish from here... -/
    dsimp, simp, dsimp,
    slice_lhs 4 6 {
      rw [←functor.map_comp, ←functor.map_comp],
      rw [←is_equivalence.fun_inv_map],
    },
    slice_lhs 1 2 { simp },
    dsimp, simp,
    slice_lhs 2 4 {
      rw [←functor.map_comp, ←functor.map_comp],
      erw [nat_iso.naturality_2],
    },
    erw [nat_iso.naturality_1],
    refl,
  end }.

section

@[simp] private def equivalence_inverse (F : C ⥤ D) [full F] [faithful F] [ess_surj F] : D ⥤ C :=
{ obj  := λ X, F.obj_preimage X,
  map := λ X Y f, F.preimage ((F.fun_obj_preimage_iso X).hom ≫ f ≫ (F.fun_obj_preimage_iso Y).inv),
  map_id' := λ X, begin apply F.injectivity, tidy, end,
  map_comp' := λ X Y Z f g, by apply F.injectivity; simp }.

def equivalence_of_fully_faithfully_ess_surj
  (F : C ⥤ D) [full F] [faithful : faithful F] [ess_surj F] : is_equivalence F :=
{ inverse := equivalence_inverse F,
  fun_inv_id' := nat_iso.of_components
    (λ X, preimage_iso (F.fun_obj_preimage_iso (F.obj X)))
    (λ X Y f, begin apply F.injectivity, obviously, end),
  inv_fun_id' := nat_iso.of_components
    (λ Y, (F.fun_obj_preimage_iso Y))
    (by obviously) }
end

end category_theory.equivalence

end category_theory

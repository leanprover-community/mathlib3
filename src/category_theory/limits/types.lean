/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Reid Barton
-/
import category_theory.limits.limits

universes v u -- declare the `v`'s first; see `category_theory.category` for an explanation

open category_theory
open category_theory.limits

namespace category_theory.limits.types

variables {J : Type u} [small_category J]

/-- (implementation) the limit cone of a functor to Type -/
def limit_ (F : J ⥤ Type u) : cone F :=
{ X := F.sections,
  π := { app := λ j u, u.val j } }

local attribute [elab_simple] congr_fun
/-- (implementation) the fact that the proposed limit cone is the limit -/
def limit_is_limit_ (F : J ⥤ Type u) : is_limit (limit_ F) :=
{ lift := λ s v, ⟨λ j, s.π.app j v, λ j j' f, congr_fun (cone.w s f) _⟩,
  uniq' :=
  begin
    intros, ext x, apply subtype.eq, ext j,
    exact congr_fun (w j) x
  end }

instance : has_limits.{u} (Type u) :=
{ has_limits_of_shape := λ J 𝒥,
  { has_limit := λ F, by exactI { cone := limit_ F, is_limit := limit_is_limit_ F } } }

@[simp] lemma types_limit (F : J ⥤ Type u) :
  limits.limit F = {u : Π j, F.obj j // ∀ {j j'} f, F.map f (u j) = u j'} := rfl
@[simp] lemma types_limit_π (F : J ⥤ Type u) (j : J) (g : limit F) :
  limit.π F j g = g.val j := rfl
@[simp] lemma types_limit_pre
  (F : J ⥤ Type u) {K : Type u} [𝒦 : small_category K] (E : K ⥤ J) (g : limit F) :
  limit.pre F E g = (⟨λ k, g.val (E.obj k), by obviously⟩ : limit (E ⋙ F)) := rfl
@[simp] lemma types_limit_map {F G : J ⥤ Type u} (α : F ⟶ G) (g : limit F) :
  (lim.map α : limit F → limit G) g =
  (⟨λ j, (α.app j) (g.val j), λ j j' f,
    by {rw ←functor_to_types.naturality, dsimp, rw ←(g.property f)}⟩ : limit G) := rfl

@[simp] lemma types_limit_lift (F : J ⥤ Type u) (c : cone F) (x : c.X) :
  limit.lift F c x = (⟨λ j, c.π.app j x, λ j j' f, congr_fun (cone.w c f) x⟩ : limit F) :=
rfl


/-- (implementation) the colimit cocone of a functor to Type -/
def colimit_ (F : J ⥤ Type u) : cocone F :=
{ X := @quot (Σ j, F.obj j) (λ p p', ∃ f : p.1 ⟶ p'.1, p'.2 = F.map f p.2),
  ι :=
  { app := λ j x, quot.mk _ ⟨j, x⟩,
    naturality' := λ j j' f, funext $ λ x, eq.symm (quot.sound ⟨f, rfl⟩) } }

local attribute [elab_with_expected_type] quot.lift

/-- (implementation) the fact that the proposed colimit cocone is the colimit -/
def colimit_is_colimit_ (F : J ⥤ Type u) : is_colimit (colimit_ F) :=
{ desc := λ s, quot.lift (λ (p : Σ j, F.obj j), s.ι.app p.1 p.2)
    (assume ⟨j, x⟩ ⟨j', x'⟩ ⟨f, hf⟩, by rw hf; exact (congr_fun (cocone.w s f) x).symm) }

instance : has_colimits.{u} (Type u) :=
{ has_colimits_of_shape := λ J 𝒥,
  { has_colimit := λ F, by exactI { cocone := colimit_ F, is_colimit := colimit_is_colimit_ F } } }

@[simp] lemma types_colimit (F : J ⥤ Type u) :
  limits.colimit F = @quot (Σ j, F.obj j) (λ p p', ∃ f : p.1 ⟶ p'.1, p'.2 = F.map f p.2) := rfl
@[simp] lemma types_colimit_ι (F : J ⥤ Type u) (j : J) :
  colimit.ι F j = λ x, quot.mk _ ⟨j, x⟩ := rfl
@[simp] lemma types_colimit_pre
  (F : J ⥤ Type u) {K : Type u} [𝒦 : small_category K] (E : K ⥤ J) :
  colimit.pre F E =
  quot.lift (λ p, quot.mk _ ⟨E.obj p.1, p.2⟩) (λ p p' ⟨f, h⟩, quot.sound ⟨E.map f, h⟩) := rfl
@[simp] lemma types_colimit_map {F G : J ⥤ Type u} (α : F ⟶ G) :
  (colim.map α : colimit F → colimit G) =
  quot.lift
    (λ p, quot.mk _ ⟨p.1, (α.app p.1) p.2⟩)
    (λ p p' ⟨f, h⟩, quot.sound ⟨f, by rw h; exact functor_to_types.naturality _ _ α f _⟩) := rfl

@[simp] lemma types_colimit_desc (F : J ⥤ Type u) (c : cocone F) :
  colimit.desc F c =
  quot.lift
    (λ p, c.ι.app p.1 p.2)
    (λ p p' ⟨f, h⟩, by rw h; exact (functor_to_types.naturality _ _ c.ι f _).symm) := rfl

end category_theory.limits.types

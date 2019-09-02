/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.bundled
import category_theory.types

/-!
# Category instances for algebraic structures that use bundled homs.

Many algebraic structures in Lean initially used unbundled homs (e.g. a bare function between types, along with
an a `is_monoid_hom` typeclass), but the general trend is towards using bundled homs.

While the helper functions in `category_theory/concrete_category.lean` are useful for categories
with unbundled homs, this file provides similar infrastructure for categories with bundled homs.
-/

universes w v u

namespace category_theory

variables (c : Type u → Type v)

-- TODO the square brackets here are useless, remove them and the resulting @s?
structure bundled_hom :=
(hom : Π {α β : Type u} (Iα : c α) (Iβ : c β), Type w)
(to_fun : Π {α β : Type u} (Iα : c α) (Iβ : c β), hom Iα Iβ → α → β)
(id : Π {α : Type u} (I : c α), hom I I)
(comp : Π {α β γ : Type u} (Iα : c α) (Iβ : c β) (Iγ : c γ),
  hom Iα Iβ → hom Iβ Iγ → hom Iα Iγ)
(hom_ext : Π {α β : Type u} (Iα : c α) (Iβ : c β) {f g : hom Iα Iβ}
  (h : to_fun Iα Iβ f = to_fun Iα Iβ g), f = g . obviously)
(id_to_fun : Π {α : Type u} (I : c α), to_fun I I (id I) = _root_.id . obviously)
(comp_to_fun : Π {α β γ : Type u} (Iα : c α) (Iβ : c β) (Iγ : c γ)
  (f : hom Iα Iβ) (g : hom Iβ Iγ),
  to_fun Iα Iγ (comp Iα Iβ Iγ f g) = (to_fun Iβ Iγ g) ∘ (to_fun Iα Iβ f) . obviously)

attribute [class] bundled_hom

attribute [extensionality] bundled_hom.hom_ext
attribute [simp] bundled_hom.id_to_fun bundled_hom.comp_to_fun

namespace bundled_hom

section
variable [S : bundled_hom c]
include S

instance : category (bundled c) :=
{ hom := λ X Y, @bundled_hom.hom c S X.α Y.α X.str Y.str,
  id := λ X, @bundled_hom.id c S X.α X.str,
  comp := λ X Y Z f g, @bundled_hom.comp c S X.α Y.α Z.α X.str Y.str Z.str f g }

def has_coe_to_fun {X Y : bundled c} : has_coe_to_fun (X ⟶ Y) :=
{ F   := λ f, X → Y,
  coe := λ f, S.to_fun X.str Y.str f }

local attribute [instance] has_coe_to_fun

@[simp] lemma coe_id {X : bundled c} : ((𝟙 X) : X → X) = _root_.id :=
S.id_to_fun X.str
@[simp] lemma coe_comp {X Y Z : bundled c} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
  (f ≫ g) x = g (f x) :=
begin
  unfold_coes,
  erw S.comp_to_fun
end
end

variables {c}

def forget [S : bundled_hom c] : bundled c ⥤ Type u :=
{ obj := λ X, X.α,
  map := λ X Y f, @bundled_hom.to_fun c S X.α Y.α X.str Y.str f }

instance [S : bundled_hom c] : faithful (@forget c _) := {}

variables (c) (d : Type u → Type v)

meta def trivial_forget_obj : tactic unit := `[exact (λ α s, by resetI; apply_instance)]
meta def trivial_forget_hom : tactic unit := `[exact (λ X Y f, f)]

-- This has pretty disgusting arguments, but it should only be used in simple cases where
-- everything can be provided by `auto_param`.
-- Example usage is:
-- `def forget_to_Mon : CommMon ⥤ Mon := bundled_hom.forget_to comm_monoid monoid`

/--
Construct a forgetful functor `bundled c ⥤ bundled d`, where the category instances were provided
via `bundled_hom`. There are arguments providing evidence that there really is a forgetful functor,
but can often be omitted, and provided via `auto_param` tactics.
-/
def forget_to [Sc : bundled_hom c] [Sd : bundled_hom d]
   (forget_obj : Π α, c α → d α . trivial_forget_obj)
   (forget_hom : Π (X Y : bundled c), @bundled_hom.hom c Sc X.α Y.α X.str Y.str → @bundled_hom.hom d Sd X.α Y.α (forget_obj X.α X.str) (forget_obj Y.α Y.str) . trivial_forget_hom)
   (map_id : Π X : bundled c, forget_hom X X (𝟙 X) = @bundled_hom.id d Sd X.α (forget_obj X.α X.str) . obviously)
   (map_comp : Π (X Y Z : bundled c) (f : @bundled_hom.hom c Sc X.α Y.α X.str Y.str) (g : @bundled_hom.hom c Sc Y.α Z.α Y.str Z.str), forget_hom X Z (@bundled_hom.comp c Sc X.α Y.α Z.α X.str Y.str Z.str f g) = @bundled_hom.comp d Sd X.α Y.α Z.α (forget_obj X.α X.str) (forget_obj Y.α Y.str) (forget_obj Z.α Z.str) (forget_hom X Y f) (forget_hom Y Z g) . obviously)
   : bundled c ⥤ bundled d :=
{ obj := λ X, ⟨X.α, forget_obj X.α X.str⟩,
  map := λ X Y f, forget_hom X Y f }

end bundled_hom

end category_theory

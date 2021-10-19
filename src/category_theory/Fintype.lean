/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Adam Topaz
-/

import data.fintype.basic
import data.fin.basic
import category_theory.concrete_category.bundled
import category_theory.concrete_category
import category_theory.full_subcategory
import category_theory.skeletal

/-!
# The category of finite types.

We define the category of finite types, denoted `Fintype` as
(bundled) types with a `fintype` instance.

We also define `Fintype.skeleton`, the standard skeleton of `Fintype` whose objects are `fin n`
for `n : ℕ`. We prove that the obvious inclusion functor `Fintype.skeleton ⥤ Fintype` is an
equivalence of categories in `Fintype.skeleton.equivalence`.
We prove that `Fintype.skeleton` is a skeleton of `Fintype` in `Fintype.is_skeleton`.
-/

open_locale classical
open category_theory

/-- The category of finite types. -/
@[derive has_coe_to_sort]
def Fintype := bundled fintype

namespace Fintype

/-- Construct a bundled `Fintype` from the underlying type and typeclass. -/
def of (X : Type*) [fintype X] : Fintype := bundled.of X
instance : inhabited Fintype := ⟨⟨pempty⟩⟩
instance {X : Fintype} : fintype X := X.2

instance : category Fintype := induced_category.category bundled.α

/-- The fully faithful embedding of `Fintype` into the category of types. -/
@[derive [full, faithful], simps]
def incl : Fintype ⥤ Type* := induced_functor _

instance : concrete_category Fintype := ⟨incl⟩

@[simp] lemma id_apply (X : Fintype) (x : X) : (𝟙 X : X → X) x = x := rfl
@[simp] lemma comp_apply {X Y Z : Fintype} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
  (f ≫ g) x = g (f x) := rfl

universe u
/--
The "standard" skeleton for `Fintype`. This is the full subcategory of `Fintype` spanned by objects
of the form `ulift (fin n)` for `n : ℕ`. We parameterize the objects of `Fintype.skeleton`
directly as `ulift ℕ`, as the type `ulift (fin m) ≃ ulift (fin n)` is
nonempty if and only if `n = m`. Specifying universes, `skeleton : Type u` is a small
skeletal category equivalent to `Fintype.{u}`.
-/
def skeleton : Type u := ulift ℕ

namespace skeleton

/-- Given any natural number `n`, this creates the associated object of `Fintype.skeleton`. -/
def mk : ℕ → skeleton := ulift.up

instance : inhabited skeleton := ⟨mk 0⟩

/-- Given any object of `Fintype.skeleton`, this returns the associated natural number. -/
def len : skeleton → ℕ := ulift.down

@[ext]
lemma ext (X Y : skeleton) : X.len = Y.len → X = Y := ulift.ext _ _

instance : small_category skeleton.{u} :=
{ hom := λ X Y, ulift.{u} (fin X.len) → ulift.{u} (fin Y.len),
  id := λ _, id,
  comp := λ _ _ _ f g, g ∘ f }

lemma is_skeletal : skeletal skeleton.{u} := λ X Y ⟨h⟩, ext _ _ $ fin.equiv_iff_eq.mp $
  nonempty.intro $
{ to_fun := λ x, (h.hom ⟨x⟩).down,
  inv_fun := λ x, (h.inv ⟨x⟩).down,
  left_inv := begin
    intro a,
    change ulift.down _ = _,
    rw ulift.up_down,
    change ((h.hom ≫ h.inv) _).down = _,
    simpa,
  end,
  right_inv := begin
    intro a,
    change ulift.down _ = _,
    rw ulift.up_down,
    change ((h.inv ≫ h.hom) _).down = _,
    simpa,
  end }

/-- The canonical fully faithful embedding of `Fintype.skeleton` into `Fintype`. -/
def incl : skeleton.{u} ⥤ Fintype.{u} :=
{ obj := λ X, Fintype.of (ulift (fin X.len)),
  map := λ _ _ f, f }

instance : full incl := { preimage := λ _ _ f, f }
instance : faithful incl := {}
instance : ess_surj incl :=
ess_surj.mk $ λ X, let F := fintype.equiv_fin X in ⟨mk (fintype.card X), nonempty.intro
  { hom := F.symm ∘ ulift.down,
    inv := ulift.up ∘ F }⟩

noncomputable instance : is_equivalence incl :=
equivalence.of_fully_faithfully_ess_surj _

/-- The equivalence between `Fintype.skeleton` and `Fintype`. -/
noncomputable def equivalence : skeleton ≌ Fintype := incl.as_equivalence

@[simp] lemma incl_mk_nat_card (n : ℕ) : fintype.card (incl.obj (mk n)) = n :=
begin
  convert finset.card_fin n,
  apply fintype.of_equiv_card,
end

end skeleton

/-- `Fintype.skeleton` is a skeleton of `Fintype`. -/
noncomputable def is_skeleton : is_skeleton_of Fintype skeleton skeleton.incl :=
{ skel := skeleton.is_skeletal,
  eqv := by apply_instance }

end Fintype

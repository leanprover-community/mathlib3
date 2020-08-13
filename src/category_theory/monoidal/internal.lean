/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.category

/-!
# The category of monoids in a monoidal category, and modules over an internal monoid.
-/

universes v u

open category_theory

variables (C : Type u) [category.{v} C] [monoidal_category.{v} C]

/--
A monoid object internal to a monoidal category.

When the monoidal category is preadditive, this is also sometimes called an "algebra object".
-/
structure Mon_ :=
(X : C)
(one : 𝟙_ C ⟶ X)
(mul : X ⊗ X ⟶ X)
(one_mul' : (one ⊗ 𝟙 X) ≫ mul = (λ_ X).hom . obviously)
(mul_one' : (𝟙 X ⊗ one) ≫ mul = (ρ_ X).hom . obviously)
-- Obviously there is some flexibility stating this axiom.
-- This one has left- and right-hand sides matching the statement of `monoid.mul_assoc`,
-- and chooses to place the associator on the right-hand side.
-- The heuristic is that unitors and associators "don't have much weight".
(mul_assoc' : (mul ⊗ 𝟙 X) ≫ mul = (α_ X X X).hom ≫ (𝟙 X ⊗ mul) ≫ mul . obviously)

restate_axiom Mon_.one_mul'
restate_axiom Mon_.mul_one'
restate_axiom Mon_.mul_assoc'
attribute [simp, reassoc] Mon_.one_mul Mon_.mul_one Mon_.mul_assoc

namespace Mon_

theorem hext (M N : Mon_ C) : M.X = N.X → M.one == N.one → M.mul == N.mul → M = N :=
begin
  intros h1 h2 h3,
  cases M, cases N,
  dsimp only [] at h1,
  subst h1,
  congr,
  repeat {apply eq_of_heq, assumption}
end

variables {C}

variables {M : Mon_ C}

lemma assoc_flip : (𝟙 M.X ⊗ M.mul) ≫ M.mul = (α_ M.X M.X M.X).inv ≫ (M.mul ⊗ 𝟙 M.X) ≫ M.mul :=
by simp

/-- A morphism of monoid objects. -/
@[ext]
structure hom (M N : Mon_ C) :=
(hom : M.X ⟶ N.X)
(one_hom' : M.one ≫ hom = N.one . obviously)
(mul_hom' : M.mul ≫ hom = (hom ⊗ hom) ≫ N.mul . obviously)

restate_axiom hom.one_hom'
restate_axiom hom.mul_hom'
attribute [simp, reassoc] hom.one_hom hom.mul_hom

/-- The identity morphism on a monoid object. -/
@[simps]
def id (M : Mon_ C) : hom M M :=
{ hom := 𝟙 M.X, }

instance hom_inhabited (M : Mon_ C) : inhabited (hom M M) := ⟨id M⟩

/-- Composition of morphisms of monoid objects. -/
@[simps]
def comp {M N O : Mon_ C} (f : hom M N) (g : hom N O) : hom M O :=
{ hom := f.hom ≫ g.hom, }

instance : category (Mon_ C) :=
{ hom := λ M N, hom M N,
  id := id,
  comp := λ M N O f g, comp f g, }

@[simp] lemma id_hom' (M : Mon_ C) : (𝟙 M : hom M M).hom = 𝟙 M.X := rfl
@[simp] lemma comp_hom' {M N K : Mon_ C} (f : M ⟶ N) (g : N ⟶ K) :
  (f ≫ g : hom M K).hom = f.hom ≫ g.hom := rfl

/-- The forgetful functor from monoid objects to the ambient category. -/
def forget : Mon_ C ⥤ C :=
{ obj := λ A, A.X,
  map := λ A B f, f.hom, }

end Mon_

-- PROJECT: lax monoidal functors `C ⥤ D` induce functors `Mon_ C ⥤ Mon_ D`.

variables {C}

/-- A module object for a monoid object, all internal to some monoidal category. -/
structure Mod (A : Mon_ C) :=
(X : C)
(act : A.X ⊗ X ⟶ X)
(one_act' : (A.one ⊗ 𝟙 X) ≫ act = (λ_ X).hom . obviously)
(assoc' : (A.mul ⊗ 𝟙 X) ≫ act = (α_ A.X A.X X).hom ≫ (𝟙 A.X ⊗ act) ≫ act . obviously)

restate_axiom Mod.one_act'
restate_axiom Mod.assoc'
attribute [simp, reassoc] Mod.one_act Mod.assoc

namespace Mod

variables {A : Mon_ C} (M : Mod A)

lemma assoc_flip : (𝟙 A.X ⊗ M.act) ≫ M.act = (α_ A.X A.X M.X).inv ≫ (A.mul ⊗ 𝟙 M.X) ≫ M.act :=
by simp

/-- A morphism of module objects. -/
@[ext]
structure hom (M N : Mod A) :=
(hom : M.X ⟶ N.X)
(act_hom' : M.act ≫ hom = (𝟙 A.X ⊗ hom) ≫ N.act . obviously)

restate_axiom hom.act_hom'
attribute [simp, reassoc] hom.act_hom

/-- The identity morphism on a module object. -/
@[simps]
def id (M : Mod A) : hom M M :=
{ hom := 𝟙 M.X, }

instance hom_inhabited (M : Mod A) : inhabited (hom M M) := ⟨id M⟩

/-- Composition of module object morphisms. -/
@[simps]
def comp {M N O : Mod A} (f : hom M N) (g : hom N O) : hom M O :=
{ hom := f.hom ≫ g.hom, }

instance : category (Mod A) :=
{ hom := λ M N, hom M N,
  id := id,
  comp := λ M N O f g, comp f g, }

theorem hom_eq_to_hom (M N : Mon_ C) (h : M = N) :
  Mon_.hom.hom (eq_to_hom h) = eq_to_hom (congr_arg _ h) := by {subst h, refl}

@[simp] lemma id_hom' (M : Mod A) : (𝟙 M : hom M M).hom = 𝟙 M.X := rfl
@[simp] lemma comp_hom' {M N K : Mod A} (f : M ⟶ N) (g : N ⟶ K) :
  (f ≫ g : hom M K).hom = f.hom ≫ g.hom := rfl

variables (A)

/-- A monoid object as a module over itself. -/
@[simps]
def regular : Mod A :=
{ X := A.X,
  act := A.mul, }

instance : inhabited (Mod A) := ⟨regular A⟩

open category_theory.monoidal_category

/--
A morphism of monoid objects induces a "restriction" or "comap" functor
between the categories of module objects.
-/
@[simps]
def comap {A B : Mon_ C} (f : A ⟶ B) : Mod B ⥤ Mod A :=
{ obj := λ M,
  { X := M.X,
    act := (f.hom ⊗ 𝟙 M.X) ≫ M.act,
    one_act' :=
    begin
      slice_lhs 1 2 { rw [←comp_tensor_id], },
      rw [f.one_hom, one_act],
    end,
    assoc' :=
    begin
      -- oh, for homotopy.io in a widget!
      slice_rhs 2 3 { rw [id_tensor_comp_tensor_id, ←tensor_id_comp_id_tensor], },
      rw id_tensor_comp,
      slice_rhs 4 5 { rw Mod.assoc_flip, },
      slice_rhs 3 4 { rw associator_inv_naturality, },
      slice_rhs 2 3 { rw [←tensor_id, associator_inv_naturality], },
      slice_rhs 1 3 { rw [iso.hom_inv_id_assoc], },
      slice_rhs 1 2 { rw [←comp_tensor_id, tensor_id_comp_id_tensor], },
      slice_rhs 1 2 { rw [←comp_tensor_id, ←f.mul_hom], },
      rw [comp_tensor_id, category.assoc],
    end, },
  map := λ M N g,
  { hom := g.hom,
    act_hom' :=
    begin
      dsimp,
      slice_rhs 1 2 { rw [id_tensor_comp_tensor_id, ←tensor_id_comp_id_tensor], },
      slice_rhs 2 3 { rw ←g.act_hom, },
      rw category.assoc,
    end }, }

-- Lots more could be said about `comap`, e.g. how it interacts with
-- identities, compositions, and equalities of monoid object morphisms.

end Mod

/-!
Projects:
* Check that `Mon_ Mon ≌ CommMon`, via the Eckmann-Hilton argument.
  (You'll have to hook up the cartesian monoidal structure on `Mon` first, available in #3463)
* Check that `Mon_ Top ≌ [bundled topological monoids]`.
* Check that `Mon_ AddCommGroup ≌ Ring`.
  (You'll have to hook up the monoidal structure on `AddCommGroup`.
  Currently we have the monoidal structure on `Module R`; perhaps one could specialize to `R = ℤ`
  and transport the monoidal structure across an equivalence? This sounds like some work!)
* Check that `Mon_ (Module R) ≌ Algebra R`.
* Show that if `C` is braided (see #3550) then `Mon_ C` is naturally monoidal.
* Can you transport this monoidal structure to `Ring` or `Algebra R`?
  How does it compare to the "native" one?
-/

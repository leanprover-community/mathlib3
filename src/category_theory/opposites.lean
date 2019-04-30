-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import category_theory.products
import category_theory.types

namespace category_theory

universes v₁ v₂ u₁ u₂ -- declare the `v`'s first; see `category_theory.category` for an explanation

/-- The type of objects of the opposite of C (which should be a category).

  In order to avoid confusion between C and its opposite category, we
  set up the type of objects `opposite C` using the following pattern,
  which will be repeated later for the morphisms.

  1. Define `opposite C := C`.
  2. Define the isomorphisms `op : C → opposite C`, `unop : opposite C → C`.
  3. Make the definition `opposite` irreducible.

  This has the following consequences.

  * `opposite C` and `C` are distinct types in the elaborator, so you
    must use `op` and `unop` explicitly to convert between them.
  * Both `unop (op X) = X` and `op (unop X) = X` are definitional
    equalities. Notably, every object of the opposite category is
    definitionally of the form `op X`, which greatly simplifies the
    definition of the structure of the opposite category, for example.

  (If Lean supported definitional eta equality for records, we could
  achieve the same goals using a structure with one field.)
-/
def opposite (C : Sort u₁) : Sort u₁ := C

-- Use a high right binding power (like that of postfix ⁻¹) so that, for example,
-- `presheaf Cᵒᵖ` parses as `presheaf (Cᵒᵖ)` and not `(presheaf C)ᵒᵖ`.
notation C `ᵒᵖ`:std.prec.max_plus := opposite C

variables {C : Sort u₁}

def op (X : C) : Cᵒᵖ := X
def unop (X : Cᵒᵖ) : C := X

attribute [irreducible] opposite

@[simp] lemma unop_op (X : C) : unop (op X) = X := rfl
@[simp] lemma op_unop (X : Cᵒᵖ) : op (unop X) = X := rfl

lemma op_inj : function.injective (@op C) :=
by { rintros _ _ ⟨ ⟩, refl }
lemma unop_inj : function.injective (@unop C) :=
by { rintros _ _ ⟨ ⟩, refl }

section has_hom

variables [𝒞 : has_hom.{v₁} C]
include 𝒞

/-- The hom types of the opposite of a category (or graph).

  As with the objects, we'll make this irreducible below.
  Use `f.op` and `f.unop` to convert between morphisms of C
  and morphisms of Cᵒᵖ.
-/
instance has_hom.opposite : has_hom Cᵒᵖ :=
{ hom := λ X Y, unop Y ⟶ unop X }

def has_hom.hom.op {X Y : C} (f : X ⟶ Y) : op Y ⟶ op X := f
def has_hom.hom.unop {X Y : Cᵒᵖ} (f : X ⟶ Y) : unop Y ⟶ unop X := f

attribute [irreducible] has_hom.opposite

lemma has_hom.hom.op_inj {X Y : C} :
  function.injective (has_hom.hom.op : (X ⟶ Y) → (op Y ⟶ op X)) :=
λ _ _ H, congr_arg has_hom.hom.unop H

lemma has_hom.hom.unop_inj {X Y : Cᵒᵖ} :
  function.injective (has_hom.hom.unop : (X ⟶ Y) → (unop Y ⟶ unop X)) :=
λ _ _ H, congr_arg has_hom.hom.op H

@[simp] lemma has_hom.hom.unop_op {X Y : C} {f : X ⟶ Y} : f.op.unop = f := rfl
@[simp] lemma has_hom.hom.op_unop {X Y : Cᵒᵖ} {f : X ⟶ Y} : f.unop.op = f := rfl

end has_hom

variables [𝒞 : category.{v₁} C]
include 𝒞

instance category.opposite : category.{v₁} Cᵒᵖ :=
{ comp := λ _ _ _ f g, (g.unop ≫ f.unop).op,
  id   := λ X, (𝟙 (unop X)).op }

@[simp] lemma op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} :
  (f ≫ g).op = g.op ≫ f.op := rfl
@[simp] lemma op_id {X : C} : (𝟙 X).op = 𝟙 (op X) := rfl

@[simp] lemma unop_comp {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z} :
  (f ≫ g).unop = g.unop ≫ f.unop := rfl
@[simp] lemma unop_id {X : Cᵒᵖ} : (𝟙 X).unop = 𝟙 (unop X) := rfl
@[simp] lemma unop_id_op {X : C} : (𝟙 (op X)).unop = 𝟙 X := rfl
@[simp] lemma op_id_unop {X : Cᵒᵖ} : (𝟙 (unop X)).op = 𝟙 X := rfl

def op_op : (Cᵒᵖ)ᵒᵖ ⥤ C :=
{ obj := λ X, unop (unop X),
  map := λ X Y f, f.unop.unop }

-- TODO this is an equivalence

namespace functor

section

variables {D : Sort u₂} [𝒟 : category.{v₂} D]
include 𝒟

variables {C D}

protected definition op (F : C ⥤ D) : Cᵒᵖ ⥤ Dᵒᵖ :=
{ obj := λ X, op (F.obj (unop X)),
  map := λ X Y f, (F.map f.unop).op }

@[simp] lemma op_obj (F : C ⥤ D) (X : Cᵒᵖ) : (F.op).obj X = op (F.obj (unop X)) := rfl
@[simp] lemma op_map (F : C ⥤ D) {X Y : Cᵒᵖ} (f : X ⟶ Y) : (F.op).map f = (F.map f.unop).op := rfl

protected definition unop (F : Cᵒᵖ ⥤ Dᵒᵖ) : C ⥤ D :=
{ obj := λ X, unop (F.obj (op X)),
  map := λ X Y f, (F.map f.op).unop }

@[simp] lemma unop_obj (F : Cᵒᵖ ⥤ Dᵒᵖ) (X : C) : (F.unop).obj X = unop (F.obj (op X)) := rfl
@[simp] lemma unop_map (F : Cᵒᵖ ⥤ Dᵒᵖ) {X Y : C} (f : X ⟶ Y) : (F.unop).map f = (F.map f.op).unop := rfl

variables (C D)

definition op_hom : (C ⥤ D)ᵒᵖ ⥤ (Cᵒᵖ ⥤ Dᵒᵖ) :=
{ obj := λ F, (unop F).op,
  map := λ F G α,
  { app := λ X, (α.unop.app (unop X)).op,
    naturality' := λ X Y f, has_hom.hom.unop_inj $ eq.symm (α.unop.naturality f.unop) } }

@[simp] lemma op_hom.obj (F : (C ⥤ D)ᵒᵖ) : (op_hom C D).obj F = (unop F).op := rfl
@[simp] lemma op_hom.map_app {F G : (C ⥤ D)ᵒᵖ} (α : F ⟶ G) (X : Cᵒᵖ) :
  ((op_hom C D).map α).app X = (α.unop.app (unop X)).op := rfl

definition op_inv : (Cᵒᵖ ⥤ Dᵒᵖ) ⥤ (C ⥤ D)ᵒᵖ :=
{ obj := λ F, op F.unop,
  map := λ F G α, has_hom.hom.op
  { app := λ X, (α.app (op X)).unop,
    naturality' := λ X Y f, has_hom.hom.op_inj $ eq.symm (α.naturality f.op) } }

@[simp] lemma op_inv.obj (F : Cᵒᵖ ⥤ Dᵒᵖ) : (op_inv C D).obj F = op F.unop := rfl
@[simp] lemma op_inv.map_app {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ⟶ G) (X : C) :
  (((op_inv C D).map α).unop).app X = (α.app (op X)).unop := rfl

-- TODO show these form an equivalence

instance {F : C ⥤ D} [full F] : full F.op :=
{ preimage := λ X Y f, (F.preimage f.unop).op }

instance {F : C ⥤ D} [faithful F] : faithful F.op :=
{ injectivity' := λ X Y f g h,
    has_hom.hom.unop_inj $ by simpa using injectivity F (has_hom.hom.op_inj h) }

end

section

omit 𝒞
variables (E : Type u₁) [ℰ : category.{v₁+1} E]
include ℰ

/-- `functor.hom` is the hom-pairing, sending (X,Y) to X → Y, contravariant in X and covariant in Y. -/
definition hom : Eᵒᵖ × E ⥤ Type v₁ :=
{ obj       := λ p, unop p.1 ⟶ p.2,
  map       := λ X Y f, λ h, f.1.unop ≫ h ≫ f.2 }

@[simp] lemma hom_obj (X : Eᵒᵖ × E) : (functor.hom E).obj X = (unop X.1 ⟶ X.2) := rfl
@[simp] lemma hom_pairing_map {X Y : Eᵒᵖ × E} (f : X ⟶ Y) :
  (functor.hom E).map f = λ h, f.1.unop ≫ h ≫ f.2 := rfl

end

end functor

-- TODO the following definitions do not belong here

omit 𝒞
variables (E : Type u₁)

instance opposite.has_one [has_one E] : has_one (Eᵒᵖ) :=
{ one := op 1 }

instance opposite.has_mul [has_mul E] : has_mul (Eᵒᵖ) :=
{ mul := λ x y, op $ unop y * unop  x }

@[simp] lemma opposite.unop_one [has_one E] : unop (1 : Eᵒᵖ) = (1 : E) := rfl

@[simp] lemma opposite.unop_mul [has_mul E] (xs ys : Eᵒᵖ) : unop (xs * ys) = (unop ys * unop xs : E) := rfl

@[simp] lemma opposite.op_one [has_one E] : op (1 : E) = 1 := rfl

@[simp] lemma opposite.op_mul [has_mul E] (xs ys : E) : op (xs * ys) = (op ys * op xs) := rfl

instance opposite.monoid [monoid E] : monoid (Eᵒᵖ) :=
{ one := op 1,
  mul := λ x y, op $ unop y * unop  x,
  mul_one := by { intros, apply unop_inj, simp },
  one_mul := by { intros, simp },
  mul_assoc := by { intros, simp [mul_assoc], } }

end category_theory

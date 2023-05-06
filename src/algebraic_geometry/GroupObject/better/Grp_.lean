
import category_theory.monoidal.Mon_
import category_theory.limits.constructions.finite_products_of_binary_products
import category_theory.monoidal.of_has_finite_products
import category_theory.limits.preserves.shapes.terminal
universes v u v₁ u₁ v₂ u₂
open category_theory
open category_theory.category
open category_theory.iso
open category_theory.limits
noncomputable theory

/-namespace monoidal_of_has_finite_products

def tensor_unit_iso : 𝟙_ C ≅ ⊤_ C := iso.refl _
def tensor_obj_iso (X Y : C) : X ⊗ Y ≅ X ⨯ Y := iso.refl _
@[simp] lemma associator_def (X Y Z : C) : α_ X Y Z = prod.associator X Y Z := rfl
@[simp] lemma left_unitor_def (X : C) : λ_ X = prod.left_unitor X := rfl
@[simp] lemma right_unitor_def (X : C) : ρ_ X = prod.right_unitor X := rfl

end monoidal_of_has_finite_products


namespace symmetric_of_has_finite_products

@[simp] lemma braiding_def (X Y : C) : β_ X Y = prod.braiding X Y := rfl

end symmetric_of_has_finite_products
-/

variables (C : Type*) [category C] [has_finite_products C]

local attribute [instance] monoidal_of_has_finite_products
local attribute [instance] symmetric_of_has_finite_products

structure Grp_ extends Mon_ C :=
(inv : X ⟶ X)
(mul_left_inv' : limits.prod.lift inv (𝟙 X) ≫ mul = terminal.from X ≫ one)
(mul_right_inv' : limits.prod.lift (𝟙 X) inv ≫ mul = terminal.from X ≫ one)

restate_axiom Grp_.mul_left_inv'
attribute [reassoc] Grp_.mul_left_inv
restate_axiom Grp_.mul_right_inv'
attribute [reassoc] Grp_.mul_right_inv

namespace Grp_

instance : category (Grp_ C) :=
show category (induced_category (Mon_ C) Grp_.to_Mon_),
by apply_instance

def to_Mon_functor : Grp_ C ⥤ Mon_ C := induced_functor Grp_.to_Mon_

-- what is coherence! it doesn't work here. but dec_trivial does.
@[simps]
def trivial : Grp_ C :=
{ X := 𝟙_ C,
  one := 𝟙 _,
  mul := (λ_ _).hom,
  mul_assoc' := dec_trivial,
  mul_one' := dec_trivial,
  inv := 𝟙 _,
  mul_left_inv' := dec_trivial,
  mul_right_inv' := dec_trivial }

instance : inhabited (Grp_ C) := ⟨trivial C⟩

variables {C} {M : Grp_ C}

open category_theory.monoidal_category

@[simp] lemma one_mul_hom {Z : C} (f : Z ⟶ M.X) :
  (limits.prod.map M.one f) ≫ M.mul = limits.prod.snd ≫ f :=
Mon_.one_mul_hom _

@[simp] lemma mul_one_hom {Z : C} (f : Z ⟶ M.X) :
  (limits.prod.map f M.one) ≫ M.mul = limits.prod.fst ≫ f :=
Mon_.mul_one_hom _

lemma assoc_flip : (limits.prod.map (𝟙 M.X) M.mul) ≫ M.mul
  = (prod.associator M.X M.X M.X).inv ≫ (limits.prod.map M.mul (𝟙 M.X)) ≫ M.mul :=
Mon_.assoc_flip

@[ext] lemma hom.ext {X Y : Grp_ C} (f g : X ⟶ Y) (H : f.hom = g.hom) : f = g :=
Mon_.hom.ext _ _ H

@[simp] lemma hom.one_hom {X Y : Grp_ C} (f : X ⟶ Y) :
  X.one ≫ f.hom = Y.one :=
Mon_.hom.one_hom _

@[simp] lemma hom.mul_hom {X Y : Grp_ C} (f : X ⟶ Y) :
  X.mul ≫ f.hom = (limits.prod.map f.hom f.hom) ≫ Y.mul := Mon_.hom.mul_hom _

-- apparently using the functor interpretation can prove hom.one_hom and hom.inv_hom.

section
variables (C)

@[simps]
def forget : Grp_ C ⥤ C :=
{ obj := λ A, A.X,
  map := λ A B f, f.hom, }

end

instance forget_faithful : faithful (@forget C _ _) := { }

instance {A B : Grp_ C} (f : A ⟶ B) [e : is_iso ((forget C).map f)] : is_iso f.hom := e

/-- The forgetful functor from monoid objects to the ambient category reflects isomorphisms. -/
instance : reflects_isomorphisms (forget C) :=
{ reflects := λ X Y f e, by exactI ⟨⟨
{ hom := category_theory.inv f.hom,
  mul_hom' := sorry }, sorry⟩⟩ }

def iso_of_iso {M N : Grp_ C}
  (f : M.X ≅ N.X)
  (one_f : M.one ≫ f.hom = N.one)
  (mul_f : M.mul ≫ f.hom = (limits.prod.map f.hom f.hom) ≫ N.mul) :
  M ≅ N :=
{ hom := { hom := f.hom, one_hom' := one_f, mul_hom' := mul_f },
  inv :=
  { hom := f.inv,
    one_hom' := by { rw ←one_f, simp },
    mul_hom' :=
    begin
      rw ←(cancel_mono f.hom),
      slice_rhs 2 3 { rw mul_f },
      simp,
    end },
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }

end Grp_

open category_theory.limits

variables {C} {D : Type u₂} [category.{v₂} D] [has_finite_products.{v₂} D]
namespace preserves_finite_products

@[simps] def to_monoidal_functor (F : C ⥤ D)
  [preserves_limits_of_shape (discrete walking_pair) F]
  [preserves_limits_of_shape (discrete.{0} pempty) F] :
  monoidal_functor C D :=
{ ε := (preserves_terminal.iso F).inv,
  μ := λ X Y, (preserves_limit_pair.iso F X Y).inv,
  μ_natural' := sorry,
  associativity' := sorry,
  left_unitality' := sorry,
  right_unitality' := sorry,
  ε_is_iso := by apply_instance,
  μ_is_iso := by apply_instance, .. F }

@[simps]
def map_Grp (F : C ⥤ D) [H1 : preserves_limits_of_shape (discrete walking_pair) F]
  [H2 : preserves_limits_of_shape (discrete.{0} pempty) F] : Grp_ C ⥤ Grp_ D :=
{ obj := λ A,
  { X := F.obj A.X,
    one := (preserves_terminal.iso F).inv ≫ F.map A.one,
    mul := (preserves_limit_pair.iso F A.X A.X).inv ≫ F.map A.mul,
    one_mul' := sorry,
    mul_one' := sorry,
    mul_assoc' := sorry,
    inv := F.map A.inv,
    mul_left_inv' := sorry,
    mul_right_inv' := sorry },
  map := λ A B f,
  { hom := F.map f.hom,
    one_hom' := sorry,
    mul_hom' := sorry },
  map_id' := sorry,
  map_comp' := sorry, }

end preserves_finite_products
namespace Grp_
open category_theory.monoidal_category
variable {C}

lemma Grp_tensor_one_mul (M N : Grp_ C) :
    ((λ_ (𝟙_ C)).inv ≫ (M.one ⊗ N.one) ⊗ 𝟙 (M.X ⊗ N.X)) ≫
    tensor_μ C (M.X, N.X) (M.X, N.X) ≫ (M.mul ⊗ N.mul)
  = (λ_ (M.X ⊗ N.X)).hom :=
Mon_.Mon_tensor_one_mul _ _

lemma Grp_tensor_mul_one (M N : Grp_ C) :
    (𝟙 (M.X ⊗ N.X) ⊗ (λ_ (𝟙_ C)).inv ≫ (M.one ⊗ N.one)) ≫
    tensor_μ C (M.X, N.X) (M.X, N.X) ≫ (M.mul ⊗ N.mul)
  = (ρ_ (M.X ⊗ N.X)).hom :=
Mon_.Mon_tensor_mul_one _ _

lemma Grp_tensor_mul_assoc (M N : Grp_ C) :
    (tensor_μ C (M.X, N.X) (M.X, N.X) ≫ (M.mul ⊗ N.mul) ⊗ 𝟙 (M.X ⊗ N.X)) ≫
    tensor_μ C (M.X, N.X) (M.X, N.X) ≫
    (M.mul ⊗ N.mul)
  = (α_ (M.X ⊗ N.X) (M.X ⊗ N.X) (M.X ⊗ N.X)).hom ≫
    (𝟙 (M.X ⊗ N.X) ⊗ tensor_μ C (M.X, N.X) (M.X, N.X) ≫ (M.mul ⊗ N.mul)) ≫
    tensor_μ C (M.X, N.X) (M.X, N.X) ≫
    (M.mul ⊗ N.mul) :=
Mon_.Mon_tensor_mul_assoc _ _

instance Grp_monoidal : monoidal_category (Grp_ C) :=
{ tensor_obj := λ M N,
  { X := M.X ⊗ N.X,
    one := (λ_ (𝟙_ C)).inv ≫ (M.one ⊗ N.one),
    mul := tensor_μ C (M.X, N.X) (M.X, N.X) ≫ (M.mul ⊗ N.mul),
    one_mul' := Mon_.Mon_tensor_one_mul M.to_Mon_ N.to_Mon_,
    mul_one' := Mon_.Mon_tensor_mul_one M.to_Mon_ N.to_Mon_,
    mul_assoc' := Mon_.Mon_tensor_mul_assoc M.to_Mon_ N.to_Mon_,
    inv := M.inv ⊗ N.inv,
    mul_left_inv' := sorry,
    mul_right_inv' := sorry },
  tensor_hom := λ M N P Q f g,
    tensor_hom (f : M.to_Mon_ ⟶ N.to_Mon_) (g : P.to_Mon_ ⟶ Q.to_Mon_),
  tensor_id' := sorry,
  tensor_comp' := sorry,
  tensor_unit := Grp_.trivial C,
  associator := λ M N P, Grp_.iso_of_iso (α_ M.X N.X P.X)
    Mon_.one_associator Mon_.mul_associator,
  associator_naturality' := sorry,
  left_unitor := λ M, Grp_.iso_of_iso (λ_ M.X) Mon_.one_left_unitor Mon_.mul_left_unitor,
  left_unitor_naturality' := sorry,
  right_unitor := λ M, Grp_.iso_of_iso (ρ_ M.X) Mon_.one_right_unitor Mon_.mul_right_unitor,
  right_unitor_naturality' := sorry,
  pentagon' := sorry,
  triangle' := sorry }

end Grp_

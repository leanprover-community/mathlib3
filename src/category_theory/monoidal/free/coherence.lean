/-
Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.monoidal.free.basic
import category_theory.discrete_category

/-!
# The monoidal coherence theorem

In this file, we prove the monoidal coherence theorem, stated in the following form: the free
monoidal category over any type `C` is thin.

We follow a proof described by Ilya Beylin and Peter Dybjer, which has been previously formalized
in the proof assistant ALF. The idea is to declare a normal form (with regard to association and
adding units) on objects of the free monoidal category and consider the discrete subcategory of
objects that are in normal form. A normalization procedure is then just a functor
`full_normalize : free_monoidal_category C ⥤ discrete (normal_monoidal_object C)`, where
functoriality says that two objects which are related by associators and unitors have the
same normal form. Another desirable property of a normalization procedure is that an object is
isomorphic (i.e., related via associators and unitors) to its normal form. In the case of the
specific normalization procedure we use we not only get these isomorphismns, but also that they
assemble into a natural isomorphism `𝟭 (free_monoidal_category C) ≅ full_normalize ⋙ inclusion`.
But this means that any two parallel morphisms in the free monoidal category factor through a
discrete category in the same way, so they must be equal, and hence the free monoidal category
is thin.

## References

* [Ilya Beylin and Peter Dybjer, Extracting a proof of coherence for monoidal categories from a
   proof of normalization for monoids][beylin1996]

-/

universe u

namespace category_theory
open monoidal_category

namespace free_monoidal_category


variables {C : Type u}

section
variables (C)

/-- We say an object in the free monoidal category is in normal form if it is of the form
    `(((𝟙_ C) ⊗ X₁) ⊗ X₂) ⊗ ⋯`. -/
@[nolint has_inhabited_instance]
inductive normal_monoidal_object : Type u
| unit : normal_monoidal_object
| tensor : normal_monoidal_object → C → normal_monoidal_object

end

local notation `F` := free_monoidal_category
local notation `N` := discrete ∘ normal_monoidal_object
local infixr ` ⟶ᵐ `:10 := hom

/-- Auxiliary definition for `inclusion`. -/
@[simp] def inclusion_obj : normal_monoidal_object C → F C
| normal_monoidal_object.unit := unit
| (normal_monoidal_object.tensor n a) := tensor (inclusion_obj n) (of a)

/-- The discrete subcategory of objects in normal form includes into the free monoidal category. -/
@[simp] def inclusion : N C ⥤ F C :=
discrete.functor inclusion_obj

/-- Auxiliary definition for `normalize`. -/
@[simp] def normalize_obj : F C → normal_monoidal_object C → normal_monoidal_object C
| unit n := n
| (of X) n := normal_monoidal_object.tensor n X
| (tensor X Y) n := normalize_obj Y (normalize_obj X n)

@[simp] lemma normalize_obj_unitor (n : N C) : normalize_obj (𝟙_ (F C)) n = n :=
rfl

@[simp] lemma normalize_obj_tensor (X Y : F C) (n : N C) :
  normalize_obj (X ⊗ Y) n = normalize_obj Y (normalize_obj X n) :=
rfl

section
open hom

/-- Auxiliary definition for `normalize`. Here we prove that objects that are related by
    associators and unitors map to the same normal form. -/
@[simp] def normalize_map_aux : Π {X Y : F C},
  (X ⟶ᵐ Y) →
    ((discrete.functor (normalize_obj X) : _ ⥤ N C) ⟶ discrete.functor (normalize_obj Y))
| _ _ (id _) := 𝟙 _
| _ _ (α_hom _ _ _) := ⟨λ X, 𝟙 _⟩
| _ _ (α_inv _ _ _) := ⟨λ X, 𝟙 _⟩
| _ _ (l_hom _) := ⟨λ X, 𝟙 _⟩
| _ _ (l_inv _) := ⟨λ X, 𝟙 _⟩
| _ _ (ρ_hom _) := ⟨λ X, 𝟙 _⟩
| _ _ (ρ_inv _) := ⟨λ X, 𝟙 _⟩
| X Y (@comp _ U V W f g) := normalize_map_aux f ≫ normalize_map_aux g
| X Y (@hom.tensor _ T U V W f g) :=
    ⟨λ X, (normalize_map_aux g).app (normalize_obj T X) ≫
      (discrete.functor (normalize_obj W) : _ ⥤ N C).map ((normalize_map_aux f).app X), by tidy⟩

end

section
variables (C)

/-- Our normalization procedure works by first defining a functor `F C ⥤ (N C ⥤ N C)` (which turns
    out to be very easy), and then obtain a functor `F C ⥤ N C` by plugging in the normal object
    `𝟙_ C`. -/
@[simp] def normalize : F C ⥤ N C ⥤ N C :=
{ obj := λ X, discrete.functor (normalize_obj X),
  map := λ X Y, quotient.lift normalize_map_aux (by tidy) }

/-- A variant of the normalization functor where we consider the result as an object in the free
    monoidal category (rather than an object of the discrete subcategory of objects in normal
    form). -/
@[simp] def normalize' : F C ⥤ N C ⥤ F C :=
normalize C ⋙ (whiskering_right _ _ _).obj inclusion

/-- The normalization functor for the free monoidal category over `C`. -/
def full_normalize : F C ⥤ N C :=
{ obj := λ X, ((normalize C).obj X).obj normal_monoidal_object.unit,
  map := λ X Y f, ((normalize C).map f).app normal_monoidal_object.unit }

/-- Given an object `X` of the free monoidal category and an object `n` in normal form, taking
    the tensor product `n ⊗ X` in the free monoidal category is functorial in both `X` and `n`. -/
@[simp] def tensor_func : F C ⥤ N C ⥤ F C :=
{ obj := λ X, discrete.functor (λ n, (inclusion.obj n) ⊗ X),
  map := λ X Y f, ⟨λ n, 𝟙 _ ⊗ f, by tidy⟩ }

lemma tensor_func_map_app {X Y : F C} (f : X ⟶ Y) (n) : ((tensor_func C).map f).app n =
  𝟙 _ ⊗ f :=
rfl

lemma tensor_func_obj_map (Z : F C) {n n' : N C} (f : n ⟶ n') :
  ((tensor_func C).obj Z).map f = inclusion.map f ⊗ 𝟙 Z :=
by tidy

/-- Auxiliary definition for `normalize_iso`. Here we construct the isomorphism between
    `n ⊗ X` and `normalize X n`. -/
@[simp] def normalize_iso_app :
  Π (X : F C) (n : N C), ((tensor_func C).obj X).obj n ≅ ((normalize' C).obj X).obj n
| (of X) n := iso.refl _
| unit n := ρ_ _
| (tensor X Y) n :=
    (α_ _ _ _).symm ≪≫ tensor_iso (normalize_iso_app X n) (iso.refl _) ≪≫ normalize_iso_app _ _

@[simp] lemma normalize_iso_app_tensor (X Y : F C) (n : N C) :
  normalize_iso_app C (X ⊗ Y) n =
  (α_ _ _ _).symm ≪≫ tensor_iso (normalize_iso_app C X n) (iso.refl _) ≪≫
    normalize_iso_app _ _ _ :=
rfl

@[simp] lemma normalize_iso_app_unitor (n : N C) : normalize_iso_app C (𝟙_ (F C)) n = ρ_ _ :=
rfl

/-- Auxiliary definition for `normalize_iso`. -/
@[simp] def normalize_iso_aux (X : F C) : (tensor_func C).obj X ≅ (normalize' C).obj X :=
nat_iso.of_components (normalize_iso_app C X) (by tidy)

/-- The isomorphism between `n ⊗ X` and `normalize X n` is natural (in both `X` and `n`, but
    naturality in `n` is trivial and was "proved" in `normalize_iso_aux`). This is the real heart
    of our proof of the coherence theorem. -/
def normalize_iso : tensor_func C ≅ normalize' C :=
nat_iso.of_components (normalize_iso_aux C)
begin
  rintros X Y f,
  apply quotient.induction_on f,
  intro f,
  ext n,
  induction f generalizing n,
  { simp only [mk_id, functor.map_id, category.id_comp, category.comp_id] },
  { dsimp,
    simp only [id_tensor_associator_inv_naturality_assoc, ←pentagon_inv_assoc,
      tensor_hom_inv_id_assoc, tensor_id, category.id_comp, discrete.functor_map_id, comp_tensor_id,
      iso.cancel_iso_inv_left, category.assoc],
    dsimp, simp only [category.comp_id] },
  { dsimp,
    simp only [discrete.functor_map_id, comp_tensor_id, category.assoc, pentagon_inv_assoc,
      ←associator_inv_naturality_assoc, tensor_id, iso.cancel_iso_inv_left],
    dsimp, simp only [category.comp_id],},
  { dsimp,
    rw triangle_assoc_comp_right_assoc,
    simp only [discrete.functor_map_id, category.assoc],
    dsimp, simp only [category.comp_id] },
  { dsimp,
    simp only [triangle_assoc_comp_left_inv_assoc, inv_hom_id_tensor_assoc, tensor_id,
      category.id_comp, discrete.functor_map_id],
    dsimp, simp only [category.comp_id] },
  { dsimp,
    rw [←(iso.inv_comp_eq _).2 (right_unitor_tensor _ _), category.assoc, ←right_unitor_naturality],
    simp only [discrete.functor_map_id, iso.cancel_iso_inv_left, category.assoc],
    dsimp, simp only [category.comp_id] },
  { dsimp,
    simp only [←(iso.eq_comp_inv _).1 (right_unitor_tensor_inv _ _), iso.hom_inv_id_assoc,
      right_unitor_conjugation, discrete.functor_map_id, category.assoc],
    dsimp, simp only [category.comp_id], },
  { dsimp at *,
    rw [id_tensor_comp, category.assoc, f_ih_g ⟦f_g⟧, ←category.assoc, f_ih_f ⟦f_f⟧, category.assoc,
      ←functor.map_comp],
    congr' 2 },
  { dsimp at *,
    rw associator_inv_naturality_assoc,
    slice_lhs 2 3 { rw [←tensor_comp, f_ih_f ⟦f_f⟧] },
    conv_lhs { rw [←@category.id_comp (F C) _ _ _ ⟦f_g⟧] },
    simp only [category.comp_id, tensor_comp, category.assoc],
    congr' 2,
    rw [←mk_tensor, quotient.lift_mk],
    dsimp,
    rw [functor.map_comp, ←category.assoc, ←f_ih_g ⟦f_g⟧, ←@category.comp_id (F C) _ _ _ ⟦f_g⟧,
      ←category.id_comp ((discrete.functor inclusion_obj).map _), tensor_comp],
    dsimp,
    simp only [category.assoc, category.comp_id],
    congr' 1,
    convert (normalize_iso_aux C f_Z).hom.naturality ((normalize_map_aux f_f).app n),
    exact (tensor_func_obj_map _ _ _).symm }
end

/-- The isomorphism between an object and its normal form is natural. -/
def full_normalize_iso : 𝟭 (F C) ≅ full_normalize C ⋙ inclusion :=
nat_iso.of_components
  (λ X, (λ_ X).symm ≪≫ ((normalize_iso C).app X).app normal_monoidal_object.unit)
  begin
    intros X Y f,
    dsimp,
    rw [left_unitor_inv_naturality_assoc, category.assoc, iso.cancel_iso_inv_left],
    exact congr_arg (λ f, nat_trans.app f normal_monoidal_object.unit)
      ((normalize_iso.{u} C).hom.naturality f),
  end

end

/-- The monoidal coherence theorem. -/
instance subsingleton_hom {X Y : F C} : subsingleton (X ⟶ Y) :=
⟨λ f g, have (full_normalize C).map f = (full_normalize C).map g, from subsingleton.elim _ _,
 begin
  rw [←functor.id_map f, ←functor.id_map g],
  simp [←nat_iso.naturality_2 (full_normalize_iso.{u} C), this]
 end⟩

section groupoid

section
open hom

/-- Auxiliary construction for showing that the free monoidal category is a groupoid. Do not use
    this, use `is_iso.inv` instead. -/
def inverse_aux : Π {X Y : F C}, (X ⟶ᵐ Y) → (Y ⟶ᵐ X)
| _ _ (id X) := id X
| _ _ (α_hom _ _ _) := α_inv _ _ _
| _ _ (α_inv _ _ _) := α_hom _ _ _
| _ _ (ρ_hom _) := ρ_inv _
| _ _ (ρ_inv _) := ρ_hom _
| _ _ (l_hom _) := l_inv _
| _ _ (l_inv _) := l_hom _
| _ _ (comp f g) := (inverse_aux g).comp (inverse_aux f)
| _ _ (hom.tensor f g) := (inverse_aux f).tensor (inverse_aux g)

end

instance : groupoid.{u} (F C) :=
{ inv := λ X Y, quotient.lift (λ f, ⟦inverse_aux f⟧) (by tidy),
  ..(infer_instance : category (F C)) }

end groupoid

end free_monoidal_category

end category_theory

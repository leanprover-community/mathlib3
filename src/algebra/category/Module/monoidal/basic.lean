/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Scott Morrison, Jakob von Raumer
-/
import algebra.category.Module.basic
import linear_algebra.tensor_product
import category_theory.linear.yoneda
import category_theory.monoidal.linear

/-!
# The monoidal category structure on R-modules

Mostly this uses existing machinery in `linear_algebra.tensor_product`.
We just need to provide a few small missing pieces to build the
`monoidal_category` instance.
The `symmetric_category` instance is in `algebra.category.Module.monoidal.symmetric`
to reduce imports.

Note the universe level of the modules must be at least the universe level of the ring,
so that we have a monoidal unit.
For now, we simplify by insisting both universe levels are the same.

We construct the monoidal closed structure on `Module R` in
`algebra.category.Module.monoidal.closed`.

If you're happy using the bundled `Module R`, it may be possible to mostly
use this as an interface and not need to interact much with the implementation details.
-/

universes v w x u

open category_theory

namespace Module

variables {R : Type u} [comm_ring R]

namespace monoidal_category
-- The definitions inside this namespace are essentially private.
-- After we build the `monoidal_category (Module R)` instance,
-- you should use that API.

open_locale tensor_product
local attribute [ext] tensor_product.ext

/-- (implementation) tensor product of R-modules -/
def tensor_obj (M N : Module R) : Module R := Module.of R (M ⊗[R] N)
/-- (implementation) tensor product of morphisms R-modules -/
def tensor_hom {M N M' N' : Module R} (f : M ⟶ N) (g : M' ⟶ N') :
  tensor_obj M M' ⟶ tensor_obj N N' :=
tensor_product.map f g

lemma tensor_id (M N : Module R) : tensor_hom (𝟙 M) (𝟙 N) = 𝟙 (Module.of R (M ⊗ N)) :=
by { ext1, refl }

lemma tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : Module R}
  (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    tensor_hom (f₁ ≫ g₁) (f₂ ≫ g₂) = tensor_hom f₁ f₂ ≫ tensor_hom g₁ g₂ :=
by { ext1, refl }

/-- (implementation) the associator for R-modules -/
def associator (M : Module.{v} R) (N : Module.{w} R) (K : Module.{x} R) :
  tensor_obj (tensor_obj M N) K ≅ tensor_obj M (tensor_obj N K) :=
(tensor_product.assoc R M N K).to_Module_iso

section

/-! The `associator_naturality` and `pentagon` lemmas below are very slow to elaborate.

We give them some help by expressing the lemmas first non-categorically, then using
`convert _aux using 1` to have the elaborator work as little as possible. -/

open tensor_product (assoc map)

private lemma associator_naturality_aux
  {X₁ X₂ X₃ : Type*}
  [add_comm_monoid X₁] [add_comm_monoid X₂] [add_comm_monoid X₃]
  [module R X₁] [module R X₂] [module R X₃]
  {Y₁ Y₂ Y₃ : Type*}
  [add_comm_monoid Y₁] [add_comm_monoid Y₂] [add_comm_monoid Y₃]
  [module R Y₁] [module R Y₂] [module R Y₃]
  (f₁ : X₁ →ₗ[R] Y₁) (f₂ : X₂ →ₗ[R] Y₂) (f₃ : X₃ →ₗ[R] Y₃) :
  (↑(assoc R Y₁ Y₂ Y₃) ∘ₗ (map (map f₁ f₂) f₃)) = ((map f₁ (map f₂ f₃)) ∘ₗ ↑(assoc R X₁ X₂ X₃)) :=
begin
  apply tensor_product.ext_threefold,
  intros x y z,
  refl
end

variables (R)

private lemma pentagon_aux
  (W X Y Z : Type*)
  [add_comm_monoid W] [add_comm_monoid X] [add_comm_monoid Y] [add_comm_monoid Z]
  [module R W] [module R X] [module R Y] [module R Z] :
  ((map (1 : W →ₗ[R] W) (assoc R X Y Z).to_linear_map).comp (assoc R W (X ⊗[R] Y) Z).to_linear_map)
    .comp (map ↑(assoc R W X Y) (1 : Z →ₗ[R] Z)) =
  (assoc R W X (Y ⊗[R] Z)).to_linear_map.comp (assoc R (W ⊗[R] X) Y Z).to_linear_map :=
begin
  apply tensor_product.ext_fourfold,
  intros w x y z,
  refl
end

end

lemma associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Module R}
  (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    tensor_hom (tensor_hom f₁ f₂) f₃ ≫ (associator Y₁ Y₂ Y₃).hom =
    (associator X₁ X₂ X₃).hom ≫ tensor_hom f₁ (tensor_hom f₂ f₃) :=
by convert associator_naturality_aux f₁ f₂ f₃ using 1

lemma pentagon (W X Y Z : Module R) :
  tensor_hom (associator W X Y).hom (𝟙 Z) ≫ (associator W (tensor_obj X Y) Z).hom
  ≫ tensor_hom (𝟙 W) (associator X Y Z).hom =
    (associator (tensor_obj W X) Y Z).hom ≫ (associator W X (tensor_obj Y Z)).hom :=
by convert pentagon_aux R W X Y Z using 1

/-- (implementation) the left unitor for R-modules -/
def left_unitor (M : Module.{u} R) : Module.of R (R ⊗[R] M) ≅ M :=
(linear_equiv.to_Module_iso (tensor_product.lid R M) : of R (R ⊗ M) ≅ of R M).trans (of_self_iso M)

lemma left_unitor_naturality {M N : Module R} (f : M ⟶ N) :
  tensor_hom (𝟙 (Module.of R R)) f ≫ (left_unitor N).hom = (left_unitor M).hom ≫ f :=
begin
  ext x y, dsimp,
  erw [tensor_product.lid_tmul, tensor_product.lid_tmul],
  rw linear_map.map_smul,
  refl,
end

/-- (implementation) the right unitor for R-modules -/
def right_unitor (M : Module.{u} R) : Module.of R (M ⊗[R] R) ≅ M :=
(linear_equiv.to_Module_iso (tensor_product.rid R M) : of R (M ⊗ R) ≅ of R M).trans (of_self_iso M)

lemma right_unitor_naturality {M N : Module R} (f : M ⟶ N) :
  tensor_hom f (𝟙 (Module.of R R)) ≫ (right_unitor N).hom = (right_unitor M).hom ≫ f :=
begin
  ext x y, dsimp,
  erw [tensor_product.rid_tmul, tensor_product.rid_tmul],
  rw linear_map.map_smul,
  refl,
end

lemma triangle (M N : Module.{u} R) :
  (associator M (Module.of R R) N).hom ≫ tensor_hom (𝟙 M) (left_unitor N).hom =
    tensor_hom (right_unitor M).hom (𝟙 N) :=
begin
  apply tensor_product.ext_threefold,
  intros x y z,
  change R at y,
  dsimp [tensor_hom, associator],
  erw [tensor_product.lid_tmul, tensor_product.rid_tmul],
  exact (tensor_product.smul_tmul _ _ _).symm
end

end monoidal_category

open monoidal_category

instance monoidal_category : monoidal_category (Module.{u} R) :=
{ -- data
  tensor_obj   := tensor_obj,
  tensor_hom   := @tensor_hom _ _,
  tensor_unit  := Module.of R R,
  associator   := associator,
  left_unitor  := left_unitor,
  right_unitor := right_unitor,
  -- properties
  tensor_id'               := λ M N, tensor_id M N,
  tensor_comp'             := λ M N K M' N' K' f g h, tensor_comp f g h,
  associator_naturality'   := λ M N K M' N' K' f g h, associator_naturality f g h,
  left_unitor_naturality'  := λ M N f, left_unitor_naturality f,
  right_unitor_naturality' := λ M N f, right_unitor_naturality f,
  pentagon'                := λ M N K L, pentagon M N K L,
  triangle'                := λ M N, triangle M N, }

/-- Remind ourselves that the monoidal unit, being just `R`, is still a commutative ring. -/
instance : comm_ring ((𝟙_ (Module.{u} R) : Module.{u} R) : Type u) :=
(by apply_instance : comm_ring R)

namespace monoidal_category

@[simp]
lemma hom_apply {K L M N : Module.{u} R} (f : K ⟶ L) (g : M ⟶ N) (k : K) (m : M) :
  (f ⊗ g) (k ⊗ₜ m) = f k ⊗ₜ g m := rfl

@[simp]
lemma left_unitor_hom_apply {M : Module.{u} R} (r : R) (m : M) :
  ((λ_ M).hom : 𝟙_ (Module R) ⊗ M ⟶ M) (r ⊗ₜ[R] m) = r • m :=
tensor_product.lid_tmul m r

@[simp]
lemma left_unitor_inv_apply {M : Module.{u} R} (m : M) :
  ((λ_ M).inv : M ⟶ 𝟙_ (Module.{u} R) ⊗ M) m = 1 ⊗ₜ[R] m :=
tensor_product.lid_symm_apply m

@[simp]
lemma right_unitor_hom_apply {M : Module.{u} R} (m : M) (r : R) :
  ((ρ_ M).hom : M ⊗ 𝟙_ (Module R) ⟶ M) (m ⊗ₜ r) = r • m :=
tensor_product.rid_tmul m r

@[simp]
lemma right_unitor_inv_apply {M : Module.{u} R} (m : M) :
  ((ρ_ M).inv : M ⟶ M ⊗ 𝟙_ (Module.{u} R)) m = m ⊗ₜ[R] 1 :=
tensor_product.rid_symm_apply m

@[simp]
lemma associator_hom_apply {M N K : Module.{u} R} (m : M) (n : N) (k : K) :
  ((α_ M N K).hom : (M ⊗ N) ⊗ K ⟶ M ⊗ (N ⊗ K)) ((m ⊗ₜ n) ⊗ₜ k) = (m ⊗ₜ (n ⊗ₜ k)) := rfl

@[simp]
lemma associator_inv_apply {M N K : Module.{u} R} (m : M) (n : N) (k : K) :
  ((α_ M N K).inv : M ⊗ (N ⊗ K) ⟶ (M ⊗ N) ⊗ K) (m ⊗ₜ (n ⊗ₜ k)) = ((m ⊗ₜ n) ⊗ₜ k) := rfl

end monoidal_category

open opposite

instance : monoidal_preadditive (Module.{u} R) :=
by refine ⟨_, _, _, _⟩; dsimp only [auto_param]; intros;
  refine tensor_product.ext (linear_map.ext $ λ x, linear_map.ext $ λ y, _);
  simp only [linear_map.compr₂_apply, tensor_product.mk_apply, monoidal_category.hom_apply,
    linear_map.zero_apply, tensor_product.tmul_zero, tensor_product.zero_tmul,
    linear_map.add_apply, tensor_product.tmul_add, tensor_product.add_tmul]

instance : monoidal_linear R (Module.{u} R) :=
by refine ⟨_, _⟩; dsimp only [auto_param]; intros;
  refine tensor_product.ext (linear_map.ext $ λ x, linear_map.ext $ λ y, _);
  simp only [linear_map.compr₂_apply, tensor_product.mk_apply, monoidal_category.hom_apply,
    linear_map.smul_apply, tensor_product.tmul_smul, tensor_product.smul_tmul]

end Module

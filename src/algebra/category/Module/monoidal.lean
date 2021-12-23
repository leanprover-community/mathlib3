/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Scott Morrison, Jakob von Raumer
-/
import category_theory.monoidal.braided
import algebra.category.Module.basic
import linear_algebra.tensor_product.left_action

/-!
# The symmetric monoidal category structure on R-modules

Mostly this uses existing machinery in `linear_algebra.tensor_product`.
We just need to provide a few small missing pieces to build the
`monoidal_category` instance and then the `symmetric_category` instance.

If you're happy using the bundled `Module R`, it may be possible to mostly
use this as an interface and not need to interact much with the implementation details.
-/

universes u

open category_theory

namespace SymmetricBiModule

variables {R : Type u} [comm_ring R]

namespace monoidal_category
-- The definitions inside this namespace are essentially private.
-- After we build the `monoidal_category (Module R)` instance,
-- you should use that API.

open_locale tensor_product
local attribute [ext] tensor_product.ext

/-- (implementation) tensor product of R-modules -/
def tensor_obj (M N : SymmetricBiModule R) : SymmetricBiModule R :=
SymmetricBiModule.of R (M ⊗[R] N)

/-- (implementation) tensor product of morphisms of symmetric R-modules -/
def tensor_hom {M N M' N' : SymmetricBiModule R} (f : M ⟶ N) (g : M' ⟶ N') :
  tensor_obj M M' ⟶ tensor_obj N N' :=
tensor_product.map f g

lemma tensor_id (M N : SymmetricBiModule R) :
  tensor_hom (𝟙 M) (𝟙 N) = 𝟙 (SymmetricBiModule.of R (↥M ⊗ ↥N)) :=
by tidy

lemma tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : SymmetricBiModule R}
  (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    tensor_hom (f₁ ≫ g₁) (f₂ ≫ g₂) = tensor_hom f₁ f₂ ≫ tensor_hom g₁ g₂ :=
by tidy

/-- (implementation) the associator for symmetric R-modules -/
def associator (M N K : SymmetricBiModule R) :
  tensor_obj (tensor_obj M N) K ≅ tensor_obj M (tensor_obj N K) :=
linear_equiv.to_SymmetricBiModule_iso (by { apply tensor_product.assoc R M N K })

section

/-! The `associator_naturality` and `pentagon` lemmas below are very slow to elaborate.

We give them some help by expressing the lemmas first non-categorically, then using
`convert _aux using 1` to have the elaborator work as little as possible. -/

open tensor_product (assoc map)

private lemma associator_naturality_aux
  {X₁ X₂ X₃ : Type*}
  [add_comm_monoid X₁] [add_comm_monoid X₂] [add_comm_monoid X₃]
  [module R X₁] [module R X₂] [module R X₃]
  [module Rᵐᵒᵖ X₁] [module Rᵐᵒᵖ X₂] [module Rᵐᵒᵖ X₃]
  [is_central_scalar R X₁] [is_central_scalar R X₂] [is_central_scalar R X₃]
  {Y₁ Y₂ Y₃ : Type*}
  [add_comm_monoid Y₁] [add_comm_monoid Y₂] [add_comm_monoid Y₃]
  [module R Y₁] [module R Y₂] [module R Y₃]
  [module Rᵐᵒᵖ Y₁] [module Rᵐᵒᵖ Y₂] [module Rᵐᵒᵖ Y₃]
  [is_central_scalar R Y₁] [is_central_scalar R Y₂] [is_central_scalar R Y₃]
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
  [module R W] [module R X] [module R Y] [module R Z]
  [module Rᵐᵒᵖ W] [module Rᵐᵒᵖ X] [module Rᵐᵒᵖ Y] [module Rᵐᵒᵖ Z]
  [is_central_scalar R W] [is_central_scalar R X] [is_central_scalar R Y] [is_central_scalar R Z] :
  ((map (1 : W →ₗ[R] W) (assoc R X Y Z).to_linear_map).comp (assoc R W (X ⊗[R] Y) Z).to_linear_map)
    .comp (map ↑(assoc R W X Y) (1 : Z →ₗ[R] Z)) =
  (assoc R W X (Y ⊗[R] Z)).to_linear_map.comp (assoc R (W ⊗[R] X) Y Z).to_linear_map :=
begin
  apply tensor_product.ext_fourfold,
  intros w x y z,
  refl
end

end

lemma associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : SymmetricBiModule R}
  (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    tensor_hom (tensor_hom f₁ f₂) f₃ ≫ (associator Y₁ Y₂ Y₃).hom =
    (associator X₁ X₂ X₃).hom ≫ tensor_hom f₁ (tensor_hom f₂ f₃) :=
by convert associator_naturality_aux f₁ f₂ f₃ using 1

lemma pentagon (W X Y Z : SymmetricBiModule R) :
  tensor_hom (associator W X Y).hom (𝟙 Z) ≫ (associator W (tensor_obj X Y) Z).hom
  ≫ tensor_hom (𝟙 W) (associator X Y Z).hom =
    (associator (tensor_obj W X) Y Z).hom ≫ (associator W X (tensor_obj Y Z)).hom :=
by convert pentagon_aux R W X Y Z using 1

/-- (implementation) the left unitor for R-modules -/
def left_unitor (M : SymmetricBiModule.{u} R) : SymmetricBiModule.of R (R ⊗[R] M) ≅ M :=
(linear_equiv.to_SymmetricBiModule_iso (tensor_product.lid R M) : of R (R ⊗ M) ≅ of R M).trans
  (of_self_iso M)

lemma left_unitor_naturality {M N : SymmetricBiModule R} (f : M ⟶ N) :
  tensor_hom (𝟙 (SymmetricBiModule.of R R)) f ≫ (left_unitor N).hom
  = (left_unitor M).hom ≫ f :=
begin
  ext x y, simp,
  erw [tensor_product.lid_tmul, tensor_product.lid_tmul],
  rw linear_map.map_smul,
  refl,
end

/-- (implementation) the right unitor for R-modules -/
def right_unitor (M : SymmetricBiModule.{u} R) : SymmetricBiModule.of R (M ⊗[R] R) ≅ M :=
(linear_equiv.to_SymmetricBiModule_iso (tensor_product.rid R M) : of R (M ⊗ R) ≅ of R M).trans
  (of_self_iso M)

lemma right_unitor_naturality {M N : SymmetricBiModule R} (f : M ⟶ N) :
  tensor_hom f (𝟙 (SymmetricBiModule.of R R)) ≫ (right_unitor N).hom
  = (right_unitor M).hom ≫ f :=
begin
  ext x y, simp,
  erw [tensor_product.rid_tmul, tensor_product.rid_tmul],
  rw linear_map.map_smul,
  refl,
end

lemma triangle (M N : SymmetricBiModule.{u} R) :
  (associator M (SymmetricBiModule.of R R) N).hom ≫ tensor_hom (𝟙 M) (left_unitor N).hom =
    tensor_hom (right_unitor M).hom (𝟙 N) :=
begin
  apply @tensor_product.ext_threefold R _,
  intros x y z,
  change R at y,
  dsimp [tensor_hom, associator],
  change x ⊗ₜ[R] _ = _ ⊗ₜ[R] z,
  erw [tensor_product.lid_tmul, tensor_product.rid_tmul],
  exact (tensor_product.smul_tmul _ _ _).symm
end

end monoidal_category

open monoidal_category

instance monoidal_category : monoidal_category (SymmetricBiModule.{u} R) :=
{ -- data
  tensor_obj   := tensor_obj,
  tensor_hom   := @tensor_hom _ _,
  tensor_unit  := SymmetricBiModule.of R R,
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
instance : comm_ring ((𝟙_ (SymmetricBiModule.{u} R) : SymmetricBiModule.{u} R) : Type u) :=
(by apply_instance : comm_ring R)

namespace monoidal_category

@[simp]
lemma hom_apply {K L M N : SymmetricBiModule.{u} R} (f : K ⟶ L) (g : M ⟶ N) (k : K) (m : M) :
  (f ⊗ g) (k ⊗ₜ m) = f k ⊗ₜ g m := rfl

@[simp]
lemma left_unitor_hom_apply {M : SymmetricBiModule.{u} R} (r : R) (m : M) :
  ((λ_ M).hom : 𝟙_ (SymmetricBiModule R) ⊗ M ⟶ M) (r ⊗ₜ[R] m) = r • m :=
tensor_product.lid_tmul m r

@[simp]
lemma left_unitor_inv_apply {M : SymmetricBiModule.{u} R} (m : M) :
  ((λ_ M).inv : M ⟶ 𝟙_ (SymmetricBiModule.{u} R) ⊗ M) m = 1 ⊗ₜ[R] m :=
tensor_product.lid_symm_apply m

@[simp]
lemma right_unitor_hom_apply {M : SymmetricBiModule.{u} R} (m : M) (r : R) :
  ((ρ_ M).hom : M ⊗ 𝟙_ (SymmetricBiModule R) ⟶ M) (m ⊗ₜ r) = r • m :=
tensor_product.rid_tmul m r

@[simp]
lemma right_unitor_inv_apply {M : SymmetricBiModule.{u} R} (m : M) :
  ((ρ_ M).inv : M ⟶ M ⊗ 𝟙_ (SymmetricBiModule.{u} R)) m = m ⊗ₜ[R] 1 :=
tensor_product.rid_symm_apply m

@[simp]
lemma associator_hom_apply {M N K : SymmetricBiModule.{u} R} (m : M) (n : N) (k : K) :
  ((α_ M N K).hom : (M ⊗ N) ⊗ K ⟶ M ⊗ (N ⊗ K)) ((m ⊗ₜ n) ⊗ₜ k) = (m ⊗ₜ (n ⊗ₜ k)) := rfl

@[simp]
lemma associator_inv_apply {M N K : SymmetricBiModule.{u} R} (m : M) (n : N) (k : K) :
  ((α_ M N K).inv : M ⊗ (N ⊗ K) ⟶ (M ⊗ N) ⊗ K) (m ⊗ₜ (n ⊗ₜ k)) = ((m ⊗ₜ n) ⊗ₜ k) := rfl

end monoidal_category

/-- (implementation) the braiding for R-modules -/
def braiding (M N : SymmetricBiModule R) : tensor_obj M N ≅ tensor_obj N M :=
linear_equiv.to_SymmetricBiModule_iso (tensor_product.comm R M N)

@[simp] lemma braiding_naturality {X₁ X₂ Y₁ Y₂ : SymmetricBiModule.{u} R}
  (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
  (f ⊗ g) ≫ (Y₁.braiding Y₂).hom =
    (X₁.braiding X₂).hom ≫ (g ⊗ f) :=
begin
  apply tensor_product.ext',
  intros x y,
  refl
end

@[simp] lemma hexagon_forward (X Y Z : SymmetricBiModule.{u} R) :
  (α_ X Y Z).hom ≫ (braiding X _).hom ≫ (α_ Y Z X).hom =
  ((braiding X Y).hom ⊗ 𝟙 Z) ≫ (α_ Y X Z).hom ≫ (𝟙 Y ⊗ (braiding X Z).hom) :=
begin
  apply @tensor_product.ext_threefold R _,
  intros x y z,
  refl,
end

@[simp] lemma hexagon_reverse (X Y Z : SymmetricBiModule.{u} R) :
  (α_ X Y Z).inv ≫ (braiding _ Z).hom ≫ (α_ Z X Y).inv =
  (𝟙 X ⊗ (Y.braiding Z).hom) ≫ (α_ X Z Y).inv ≫ ((X.braiding Z).hom ⊗ 𝟙 Y) :=
begin
  apply (cancel_epi (α_ X Y Z).hom).1,
  apply @tensor_product.ext_threefold R _,
  intros x y z,
  refl,
end

local attribute [ext] tensor_product.ext

/-- The symmetric monoidal structure on `SymmetricBiModule R`. -/
instance symmetric_category : symmetric_category (SymmetricBiModule.{u} R) :=
{ braiding := braiding,
  braiding_naturality' := λ X₁ X₂ Y₁ Y₂ f g, braiding_naturality f g,
  hexagon_forward' := hexagon_forward,
  hexagon_reverse' := hexagon_reverse, }

namespace monoidal_category

@[simp] lemma braiding_hom_apply {M N : SymmetricBiModule.{u} R} (m : M) (n : N) :
  ((β_ M N).hom : M ⊗ N ⟶ N ⊗ M) (m ⊗ₜ n) = n ⊗ₜ m := rfl

@[simp] lemma braiding_inv_apply {M N : SymmetricBiModule.{u} R} (m : M) (n : N) :
  ((β_ M N).inv : N ⊗ M ⟶ M ⊗ N) (n ⊗ₜ m) = m ⊗ₜ n := rfl

end monoidal_category

end SymmetricBiModule

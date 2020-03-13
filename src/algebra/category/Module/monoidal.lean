import category_theory.monoidal.category
import algebra.category.Module.basic
import linear_algebra.tensor_product

/-!
# The monoidal category structure on R-modules

Mostly this uses existing machinery in `linear_algebra.tensor_product`.
We just need to provide a few small missing pieces to build the
`monoidal_category` instance.

If you're happy using the bundled `Module R`, it may be possible to mostly
use this as an interface and not need to interact much with the implementation details.
-/

universe u

open category_theory

namespace Module

variables {R : Type u} [comm_ring R]

namespace monoidal_category
-- The definitions inside this namespace are essentially private.
-- After we build the `monoidal_category (Module R)` instance,
-- you should use that API.

open_locale tensor_product

/-- (implementation) tensor product of R-modules -/
def tensor_obj (M N : Module R) : Module R := Module.of R (M ⊗[R] N)
/-- (implementation) tensor product of morphisms R-modules -/
def tensor_hom {M N M' N' : Module R} (f : M ⟶ N) (g : M' ⟶ N') : tensor_obj M M' ⟶ tensor_obj N N' :=
tensor_product.map f g

lemma tensor_id (M N : Module R) : tensor_hom (𝟙 M) (𝟙 N) = 𝟙 (Module.of R (↥M ⊗ ↥N)) :=
by tidy

lemma tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : Module R}
  (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    tensor_hom (f₁ ≫ g₁) (f₂ ≫ g₂) = tensor_hom f₁ f₂ ≫ tensor_hom g₁ g₂ :=
by tidy

/-- (implementation) the associator for R-modules -/
def associator (M N K : Module R) : tensor_obj (tensor_obj M N) K ≅ tensor_obj M (tensor_obj N K) :=
linear_equiv.to_Module_iso (tensor_product.assoc R M N K)

lemma associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Module R}
  (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    tensor_hom (tensor_hom f₁ f₂) f₃ ≫ (associator Y₁ Y₂ Y₃).hom =
    (associator X₁ X₂ X₃).hom ≫ tensor_hom f₁ (tensor_hom f₂ f₃) :=
begin
  ext1,
end

#exit
lemma pentagon (W X Y Z : Module R) :
  tensor_hom (associator W X Y).hom (𝟙 Z) ≫ (associator W (tensor_obj X Y) Z).hom ≫ tensor_hom (𝟙 W) (associator X Y Z).hom =
    (associator (tensor_obj W X) Y Z).hom ≫ (associator W X (tensor_obj Y Z)).hom :=
by tidy

/-- (implementation) the left unitor for R-modules -/
-- I tried building these using `linear_equiv.to_Module_iso tensor_product.lid`,
-- but couldn't get it to work
@[simps]
def left_unitor (M : Module R) : Module.of R (R ⊗[R] M) ≅ M :=
{ hom := (tensor_product.lid R M : R ⊗[R] M ≃ₗ[R] M).to_linear_map,
  inv := (tensor_product.lid R M : R ⊗[R] M ≃ₗ[R] M).symm.to_linear_map,
  hom_inv_id' := begin ext x y, exact (tensor_product.lid R M).to_equiv.left_inv (x ⊗ₜ[R] y), end,
  inv_hom_id' := begin ext x, exact (tensor_product.lid R M).to_equiv.right_inv x, end, }

lemma left_unitor_naturality {M N : Module R} (f : M ⟶ N) :
  tensor_hom (𝟙 (Module.of R R)) f ≫ (left_unitor N).hom = (left_unitor M).hom ≫ f :=
begin
  ext x y, simp, dsimp [left_unitor],
  erw [tensor_product.lid_tmul, tensor_product.lid_tmul], -- TODO these are simp lemmas, why don't they fire?
  exact (linear_map.smul _ x y).symm, -- TODO why doesn't `rw linear_map.smul` work?
end

/-- (implementation) the right unitor for R-modules -/
@[simps]
def right_unitor (M : Module R) : Module.of R (M ⊗[R] R) ≅ M :=
{ hom := (tensor_product.rid R M : M ⊗[R] R ≃ₗ[R] M).to_linear_map,
  inv := (tensor_product.rid R M : M ⊗[R] R ≃ₗ[R] M).symm.to_linear_map,
  hom_inv_id' := begin ext x y, exact (tensor_product.rid R M).to_equiv.left_inv (x ⊗ₜ[R] y), end,
  inv_hom_id' := begin ext x, exact (tensor_product.rid R M).to_equiv.right_inv x, end, }

lemma right_unitor_naturality {M N : Module R} (f : M ⟶ N) :
  tensor_hom f (𝟙 (Module.of R R)) ≫ (right_unitor N).hom = (right_unitor M).hom ≫ f :=
begin
  ext x y, simp, dsimp [right_unitor],
  erw [tensor_product.rid_tmul, tensor_product.rid_tmul], -- TODO these are simp lemmas, why don't they fire?
  exact (linear_map.smul _ y x).symm, -- TODO why doesn't `rw linear_map.smul` work?
end

lemma triangle (M N : Module R) :
  (associator M (Module.of R R) N).hom ≫ tensor_hom (𝟙 M) (left_unitor N).hom =
    tensor_hom (right_unitor M).hom (𝟙 N) :=
begin
  ext, change R at y,
  dsimp [tensor_hom, associator],
  erw [tensor_product.lid_tmul, tensor_product.rid_tmul], -- TODO these are simp lemmas, why don't they fire?
  apply (tensor_product.smul_tmul _ _ _).symm
end

end monoidal_category

open monoidal_category

instance : monoidal_category (Module.{u} R) :=
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

end Module

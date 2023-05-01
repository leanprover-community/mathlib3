import category_theory.monoidal.internal.Module
import category_theory.monoidal.transport
import algebra.category.Module.monoidal
import ring_theory.tensor_product
import algebraic_geometry.GroupObject.CommAlg
universes v u w x
noncomputable theory
open category_theory

variables {R : Type u} [comm_ring R]

local attribute [ext] algebra.tensor_product.ext

section

variables {M N P Q : Type*} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P]
  [add_comm_monoid Q] [module R M] [module R N] [module R P] [module R Q]

end

section
open_locale tensor_product
variables {M N P Q S : Type*} [ring M] [ring N] [ring P] [ring Q] [ring S]
  [algebra R M] [algebra R N] [algebra R P] [algebra R Q] [algebra R S]

end
namespace CommAlg
namespace monoidal_category
open_locale tensor_product
/-- (implementation) tensor product of R-modules -/
def tensor_obj (M N : CommAlg R) : CommAlg R := CommAlg.of R (M ⊗[R] N)
/-- (implementation) tensor product of morphisms R-modules -/
def tensor_hom {M N M' N' : CommAlg R} (f : M ⟶ N) (g : M' ⟶ N') :
  tensor_obj M M' ⟶ tensor_obj N N' :=
algebra.tensor_product.map f g

lemma tensor_id (M N : CommAlg R) : tensor_hom (𝟙 M) (𝟙 N) = 𝟙 (CommAlg.of R (M ⊗ N)) :=
by { ext1, refl }

lemma tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : CommAlg R}
  (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    tensor_hom (f₁ ≫ g₁) (f₂ ≫ g₂) = tensor_hom f₁ f₂ ≫ tensor_hom g₁ g₂ :=
by { ext1, refl }
#exit
set_option profiler true
-- needs u and by apply
def fucksake (M : CommAlg.{u} R) (N : CommAlg.{u} R) (K : CommAlg.{u} R) :
  tensor_obj (tensor_obj M N) K ≃ₐ[R] tensor_obj M (tensor_obj N K) :=
by apply algebra.tensor_product.assoc.{u} R M N K

#exit
def associator (M : CommAlg.{u} R) (N : CommAlg.{u} R) (K : CommAlg.{u} R) :
  tensor_obj (tensor_obj M N) K ≅ tensor_obj M (tensor_obj N K) :=
alg_equiv.to_CommAlg_iso (by apply algebra.tensor_product.assoc.{u} R M N K)

section

/-! The `associator_naturality` and `pentagon` lemmas below are very slow to elaborate.

We give them some help by expressing the lemmas first non-categorically, then using
`convert _aux using 1` to have the elaborator work as little as possible. -/

open algebra.tensor_product (assoc map)

section

variables {X₁ X₂ X₃ : Type*} [ring X₁] [ring X₂] [ring X₃]
  [algebra R X₁] [algebra R X₂] [algebra R X₃] (f : X₁ ≃ₐ[R] X₂)

end

private lemma associator_naturality_aux
  {X₁ X₂ X₃ : Type*}
  [ring X₁] [ring X₂] [ring X₃]
  [algebra R X₁] [algebra R X₂] [algebra R X₃]
  {Y₁ Y₂ Y₃ : Type*}
  [ring Y₁] [ring Y₂] [ring Y₃]
  [algebra R Y₁] [algebra R Y₂] [algebra R Y₃]
  (f₁ : X₁ →ₐ[R] Y₁) (f₂ : X₂ →ₐ[R] Y₂) (f₃ : X₃ →ₐ[R] Y₃) :
  ((assoc R Y₁ Y₂ Y₃).to_alg_hom.comp (map (map f₁ f₂) f₃))
    = ((map f₁ (map f₂ f₃)).comp (assoc R X₁ X₂ X₃).to_alg_hom) :=
begin
  apply algebra.tensor_product.ext_threefold,
  intros x y z,
  refl
end

variables (R)

section
variables (W X Y Z : Type*)
  [ring W] [ring X] [ring Y] [ring Z]
  [algebra R W] [algebra R X] [algebra R Y] [algebra R Z]

end
private lemma pentagon_aux
  (W X Y Z : Type u) -- needs u
  [ring W] [ring X] [ring Y] [ring Z]
  [algebra R W] [algebra R X] [algebra R Y] [algebra R Z] :
  ((map (1 : W →ₐ[R] W) (assoc R X Y Z).to_alg_hom).comp (assoc R W (X ⊗[R] Y) Z).to_alg_hom)
    .comp (map (assoc R W X Y).to_alg_hom (1 : Z →ₐ[R] Z))
  = (assoc R W X (Y ⊗[R] Z)).to_alg_hom.comp (assoc R (W ⊗[R] X) Y Z).to_alg_hom :=
begin
  apply alg_hom.to_linear_map_injective,
  ext w x y z,
  simp only [linear_map.comp_apply, tensor_product.algebra_tensor_module.curry_apply,
    linear_map.to_fun_eq_coe, linear_map.coe_restrict_scalars, tensor_product.curry_apply],
  -- all those lemmas are definitional but refl times out otherwise
  refl,
end

end

lemma associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : CommAlg.{u} R}
  (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    tensor_hom (tensor_hom f₁ f₂) f₃ ≫ (associator Y₁ Y₂ Y₃).hom =
    (associator X₁ X₂ X₃).hom ≫ tensor_hom f₁ (tensor_hom f₂ f₃) :=
by convert associator_naturality_aux f₁ f₂ f₃ using 1

lemma pentagon (W X Y Z : CommAlg.{u} R) :
  tensor_hom (associator W X Y).hom (𝟙 Z) ≫ (associator W (tensor_obj X Y) Z).hom
  ≫ tensor_hom (𝟙 W) (associator X Y Z).hom =
    (associator.{u} (tensor_obj W X) Y Z).hom ≫ (associator W X (tensor_obj Y Z)).hom :=
by convert pentagon_aux R W X Y Z using 1

/-- (implementation) the left unitor for R-modules -/
def left_unitor (M : CommAlg.{u} R) : CommAlg.of R (R ⊗[R] M) ≅ M :=
(alg_equiv.to_CommAlg_iso (algebra.tensor_product.lid R M)
  : CommAlg.of R (R ⊗ M) ≅ CommAlg.of R M).trans (CommAlg.of_self_iso M)

lemma left_unitor_naturality {M N : CommAlg R} (f : M ⟶ N) :
  tensor_hom (𝟙 (CommAlg.of R R)) f ≫ (left_unitor N).hom = (left_unitor M).hom ≫ f :=
begin
  ext x y, dsimp,
  simp only [left_unitor, iso.trans_hom, alg_equiv.to_CommAlg_iso_hom, CommAlg.of_self_iso_hom,
    comp_apply, alg_equiv.coe_alg_hom, category_theory.id_apply, category.assoc,
    algebra.tensor_product.lid_tmul, alg_hom.map_smul, tensor_hom, algebra.tensor_product.map_tmul],
end

/-- (implementation) the right unitor for R-modules -/
def right_unitor (M : CommAlg.{u} R) : CommAlg.of R (M ⊗[R] R) ≅ M :=
(alg_equiv.to_CommAlg_iso (algebra.tensor_product.rid R M)
  : CommAlg.of R (M ⊗ R) ≅ CommAlg.of R M).trans (CommAlg.of_self_iso M)

lemma right_unitor_naturality {M N : CommAlg R} (f : M ⟶ N) :
  tensor_hom f (𝟙 (CommAlg.of R R)) ≫ (right_unitor N).hom = (right_unitor M).hom ≫ f :=
begin
  ext x y, dsimp,
  simp only [right_unitor, iso.trans_hom, alg_equiv.to_CommAlg_iso_hom, CommAlg.of_self_iso_hom,
    comp_apply, alg_equiv.coe_alg_hom, category_theory.id_apply, category.assoc,
    algebra.tensor_product.rid_tmul, alg_hom.map_smul, tensor_hom, algebra.tensor_product.map_tmul],
end

lemma triangle (M N : CommAlg.{u} R) :
  (associator M (CommAlg.of R R) N).hom ≫ tensor_hom (𝟙 M) (left_unitor N).hom
    = tensor_hom (right_unitor M).hom (𝟙 N) :=
begin
  apply alg_hom.to_linear_map_injective,
  ext x y,
  dsimp only [tensor_hom, associator, left_unitor, right_unitor,
    alg_equiv.to_CommAlg_iso_hom, iso.trans_hom, alg_hom.to_linear_map_apply,
    CommAlg.of_self_iso_hom, tensor_product.algebra_tensor_module.curry_apply,
    linear_map.to_fun_eq_coe, linear_map.coe_restrict_scalars, tensor_product.curry_apply],
  simp only [comp_apply, alg_equiv.coe_alg_hom,
    algebra.tensor_product.assoc_tmul, algebra.tensor_product.map_tmul,
    algebra.tensor_product.rid_tmul, algebra.tensor_product.lid_tmul, one_smul],
end

end monoidal_category
open monoidal_category
instance monoidal_category : monoidal_category (CommAlg.{u} R) :=
{ -- data
  tensor_obj   := tensor_obj,
  tensor_hom   := @tensor_hom _ _,
  tensor_unit  := CommAlg.of R R,
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
instance : comm_ring ((𝟙_ (CommAlg.{u} R) : CommAlg.{u} R) : Type u) :=
(by apply_instance : comm_ring R)

namespace monoidal_category
@[simp]
lemma hom_apply {K L M N : CommAlg.{u} R} (f : K ⟶ L) (g : M ⟶ N) (k : K) (m : M) :
  (f ⊗ g) (k ⊗ₜ m) = f k ⊗ₜ g m := rfl

@[simp]
lemma left_unitor_hom_apply {M : CommAlg.{u} R} (r : R) (m : M) :
  ((λ_ M).hom : 𝟙_ (CommAlg R) ⊗ M ⟶ M) (r ⊗ₜ[R] m) = r • m :=
algebra.tensor_product.lid_tmul _ _ r m

@[simp]
lemma left_unitor_inv_apply {M : CommAlg.{u} R} (m : M) :
  ((λ_ M).inv : M ⟶ 𝟙_ (CommAlg.{u} R) ⊗ M) m = 1 ⊗ₜ[R] m :=
rfl

@[simp]
lemma right_unitor_hom_apply {M : CommAlg.{u} R} (m : M) (r : R) :
  ((ρ_ M).hom : M ⊗ 𝟙_ (CommAlg R) ⟶ M) (m ⊗ₜ r) = r • m :=
tensor_product.rid_tmul m r

@[simp]
lemma right_unitor_inv_apply {M : CommAlg.{u} R} (m : M) :
  ((ρ_ M).inv : M ⟶ M ⊗ 𝟙_ (CommAlg.{u} R)) m = m ⊗ₜ[R] 1 :=
tensor_product.rid_symm_apply m

@[simp]
lemma associator_hom_apply {M N K : CommAlg.{u} R} (m : M) (n : N) (k : K) :
  ((α_ M N K).hom : (M ⊗ N) ⊗ K ⟶ M ⊗ (N ⊗ K)) ((m ⊗ₜ n) ⊗ₜ k) = (m ⊗ₜ (n ⊗ₜ k)) := rfl

@[simp]
lemma associator_inv_apply {M N K : CommAlg.{u} R} (m : M) (n : N) (k : K) :
  ((α_ M N K).inv : M ⊗ (N ⊗ K) ⟶ (M ⊗ N) ⊗ K) (m ⊗ₜ (n ⊗ₜ k)) = ((m ⊗ₜ n) ⊗ₜ k) := rfl

end monoidal_category
/-- (implementation) the braiding for R-modules -/
def braiding (M N : CommAlg.{u} R) : tensor_obj M N ≅ tensor_obj N M :=
alg_equiv.to_CommAlg_iso (algebra.tensor_product.comm R M N)

@[simp] lemma braiding_naturality {X₁ X₂ Y₁ Y₂ : CommAlg.{u} R} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
  (f ⊗ g) ≫ (Y₁.braiding Y₂).hom =
    (X₁.braiding X₂).hom ≫ (g ⊗ f) :=
begin
  ext,
  refl
end

@[simp] lemma hexagon_forward (X Y Z : CommAlg.{u} R) :
  (α_ X Y Z).hom ≫ (braiding X _).hom ≫ (α_ Y Z X).hom =
  ((braiding X Y).hom ⊗ 𝟙 Z) ≫ (α_ Y X Z).hom ≫ (𝟙 Y ⊗ (braiding X Z).hom) :=
begin
  apply alg_hom.to_linear_map_injective,
  ext,
  simp only [linear_map.comp_apply, tensor_product.algebra_tensor_module.curry_apply,
    linear_map.to_fun_eq_coe, linear_map.coe_restrict_scalars, tensor_product.curry_apply],
  refl,
end

@[simp] lemma hexagon_reverse (X Y Z : CommAlg.{u} R) :
  (α_ X Y Z).inv ≫ (braiding _ Z).hom ≫ (α_ Z X Y).inv =
  (𝟙 X ⊗ (Y.braiding Z).hom) ≫ (α_ X Z Y).inv ≫ ((X.braiding Z).hom ⊗ 𝟙 Y) :=
begin
  apply alg_hom.to_linear_map_injective,
  ext,
  simp only [linear_map.comp_apply, tensor_product.algebra_tensor_module.curry_apply,
    linear_map.to_fun_eq_coe, linear_map.coe_restrict_scalars, tensor_product.curry_apply],
  refl,
end

/-- The symmetric monoidal structure on `CommAlg R`. -/
instance symmetric_category : symmetric_category (CommAlg.{u} R) :=
{ braiding := braiding,
  braiding_naturality' := λ X₁ X₂ Y₁ Y₂ f g, braiding_naturality f g,
  hexagon_forward' := hexagon_forward,
  hexagon_reverse' := hexagon_reverse, }

namespace monoidal_category

@[simp] lemma braiding_hom_apply {M N : CommAlg.{u} R} (m : M) (n : N) :
  ((β_ M N).hom : M ⊗ N ⟶ N ⊗ M) (m ⊗ₜ n) = n ⊗ₜ m := rfl

@[simp] lemma braiding_inv_apply {M N : CommAlg.{u} R} (m : M) (n : N) :
  ((β_ M N).inv : N ⊗ M ⟶ M ⊗ N) (n ⊗ₜ m) = m ⊗ₜ n := rfl

end monoidal_category

open opposite

#exit
instance : monoidal_preadditive (CommAlg.{u} R) :=
by refine ⟨_, _, _, _⟩; dsimp only [auto_param]; intros;
  refine tensor_product.ext (alg_hom.ext $ λ x, alg_hom.ext $ λ y, _);
  simp only [alg_hom.compr₂_apply, tensor_product.mk_apply, monoidal_category.hom_apply,
    alg_hom.zero_apply, tensor_product.tmul_zero, tensor_product.zero_tmul,
    alg_hom.add_apply, tensor_product.tmul_add, tensor_product.add_tmul]

instance : monoidal_linear R (CommAlg.{u} R) :=
by refine ⟨_, _⟩; dsimp only [auto_param]; intros;
  refine tensor_product.ext (alg_hom.ext $ λ x, alg_hom.ext $ λ y, _);
  simp only [alg_hom.compr₂_apply, tensor_product.mk_apply, monoidal_category.hom_apply,
    alg_hom.smul_apply, tensor_product.tmul_smul, tensor_product.smul_tmul]

/--
Auxiliary definition for the `monoidal_closed` instance on `CommAlg R`.
(This is only a separate definition in order to speed up typechecking. )
-/
@[simps]
def monoidal_closed_hom_equiv (M N P : CommAlg.{u} R) :
  ((monoidal_category.tensor_left M).obj N ⟶ P) ≃
    (N ⟶ ((linear_coyoneda R (CommAlg R)).obj (op M)).obj P) :=
{ to_fun := λ f, alg_hom.compr₂ (tensor_product.mk R N M) ((β_ N M).hom ≫ f),
  inv_fun := λ f, (β_ M N).hom ≫ tensor_product.lift f,
  left_inv := λ f, begin ext m n,
    simp only [tensor_product.mk_apply, tensor_product.lift.tmul, alg_hom.compr₂_apply,
      function.comp_app, coe_comp, monoidal_category.braiding_hom_apply],
  end,
  right_inv := λ f, begin ext m n,
    simp only [tensor_product.mk_apply, tensor_product.lift.tmul, alg_hom.compr₂_apply,
      symmetric_category.symmetry_assoc],
  end, }

instance : monoidal_closed (CommAlg.{u} R) :=
{ closed' := λ M,
  { is_adj :=
    { right := (linear_coyoneda R (CommAlg.{u} R)).obj (op M),
      adj := adjunction.mk_of_hom_equiv
      { hom_equiv := λ N P, monoidal_closed_hom_equiv M N P, } } } }

-- I can't seem to express the function coercion here without writing `@coe_fn`.
@[simp]
lemma monoidal_closed_curry {M N P : CommAlg.{u} R} (f : M ⊗ N ⟶ P) (x : M) (y : N) :
  @coe_fn _ _ alg_hom.has_coe_to_fun ((monoidal_closed.curry f : N →ₗ[R] (M →ₗ[R] P)) y) x =
    f (x ⊗ₜ[R] y) :=
rfl

@[simp]
lemma monoidal_closed_uncurry {M N P : CommAlg.{u} R}
  (f : N ⟶ (M ⟶[CommAlg.{u} R] P)) (x : M) (y : N) :
  monoidal_closed.uncurry f (x ⊗ₜ[R] y) = (@coe_fn _ _ alg_hom.has_coe_to_fun (f y)) x :=
by { simp only [monoidal_closed.uncurry, ihom.adjunction, is_left_adjoint.adj], simp, }

end CommAlg


end CommAlg

import .monoidal
import category_theory.monoidal.rigid
import linear_algebra.dual
import linear_algebra.contraction
import linear_algebra.coevaluation

noncomputable theory

universes u

open category_theory category_theory.monoidal_category
open_locale classical

namespace Module

variables (K : Type u) [field K]
variables (V : Module.{u} K)

private def Dual : Module.{u} K := Module.of K (module.dual K V.carrier)

variables [finite_dimensional K V.carrier]

private def Coevaluation : 𝟙_ (Module.{u} K) ⟶ V ⊗ Dual K V :=
as_hom $ coevaluation K V.carrier

#check 𝟙_ (Module.{u} K) ⟶ V ⊗ Dual K V
#check as_hom $ coevaluation K V.carrier
#check monoidal_category.tensor_hom (𝟙 (Dual K V)) (Coevaluation K V)

#exit
private def Evaluation : Dual K V ⊗ V ⟶ 𝟙_ (Module.{u} K) :=
as_hom $ contract_left K V.carrier

variables {K V} [finite_dimensional K V.carrier]

private def Coevaluation_Evaluation :
  (monoidal_category.tensor_hom (𝟙 (Dual K V)) (Coevaluation K V))
  ≫ (α_ (Dual K V) V (Dual K V)).inv ≫ (Evaluation K V ⊗ 𝟙 (Dual K V))
  = (ρ_ (Dual K V)).hom ≫ (λ_ (Dual K V)).inv :=
begin
  let bK := basis.of_vector_space K K,
  let bV := basis.of_vector_space K V,
  let bV' := bV.dual_basis,
  apply tensor_product.mk_compr₂_inj,
  apply bV'.ext, intro i, apply linear_map.ext_ring,
  rw [linear_map.compr₂_apply, linear_map.compr₂_apply],
  sorry
end

instance exact_pairing (V : Module.{u} K) [finite_dimensional K V] :
  exact_pairing V (Dual K V) :=
{ coevaluation := Coevaluation K V,
  evaluation := Evaluation K V,
  coevaluation_evaluation' := Coevaluation_Evaluation,
  evaluation_coevaluation' := sorry }

#check linear_map.compr₂
#check linear_map.compr₂_apply
#check basis.ext

#exit
linear_map.compr₂_apply, tensor_product.mk_apply,  Module.coe_comp,
function.comp_app, Module.monoidal_category.hom_apply, Module.id_apply,
Module.monoidal_category.right_unitor_hom_apply, one_smul


instance has_right_dual (V : Module.{u} K) : has_right_dual V := sorry

instance right_rigid_category : right_rigid_category (Module.{u} R) := { }

end Module

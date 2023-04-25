import category_theory.monoidal.internal.Module
import category_theory.monoidal.transport
import ring_theory.tensor_product
universes v u
noncomputable theory
open category_theory
namespace Algebra
variables (R : Type u) [comm_ring R]
instance : monoidal_category (Algebra.{u} R) :=
monoidal.transport Module.Mon_Module_equivalence_Algebra
#exit
def tensor_obj (A B : Algebra.{u} R) : A ⊗ B ≅ Algebra.of R (tensor_product R A B) :=
begin
  show Module.Mon_Module_equivalence_Algebra.functor.obj _ ≅ _,
  dsimp,
  refine alg_equiv.to_Algebra_iso _,
  exact
  { map_mul' := _,
  map_add' := _,
  commutes' := _, .. equiv.refl _ },
end




end Algebra

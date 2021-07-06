import category_theory.abelian.opposite
import algebra.homology.homology

noncomputable theory

namespace category_theory

variables {A : Type*} [category A] [abelian A]
  {α : Type*} [add_right_cancel_semigroup α] [has_one α]

open opposite
open category_theory.limits

def homology_op_iso (E : chain_complex A α) (i : α) : op (E.homology i) ≅ E.op.homology i :=
{ hom := begin
    refine _ ≫ cokernel.π _,
    dsimp only [homological_complex.d_from],
  end,
  inv := _,
  hom_inv_id' := _,
  inv_hom_id' := _ }

end category_theory

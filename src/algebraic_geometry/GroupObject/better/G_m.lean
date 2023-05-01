import algebraic_geometry.GroupObject.CommAlg
import data.polynomial.laurent
import algebraic_geometry.GroupObject.better.CommAlg_equivalence
import category_theory.monoidal.transport
import category_theory.monoidal.opposite
universes v u
noncomputable theory
open category_theory
variables (R : Type u) [comm_ring R]

namespace CommAlg

instance : monoidal_category (CommAlg R) :=
monoidal.transport (CommMon_CommAlg_equivalence R)

@[priority 100000] instance : monoidal_category (CommAlg R)ᵒᵖ :=
@category_theory.monoidal_category_op  _ _ (CommAlg.category_theory.monoidal_category R)

def laurent_polynomial : CommAlg R := CommAlg.of R (laurent_polynomial R)


end CommAlg

/- CommAlg ≅ CommMon (Module R)
  want Mon (CommMon (Module R))ᵒᵖ -/
@[derive category] def BiCommAlg := @Mon_ (CommAlg R)ᵒᵖ _
  (@category_theory.monoidal_category_op  _ _ (CommAlg.category_theory.monoidal_category R))

def 𝔾_m : BiCommAlg R :=
{ X := opposite.op (CommAlg.laurent_polynomial R),
  one :=
  begin
    show opposite.op _ ⟶ _,

  end,
  mul := _,
  one_mul' := _,
  mul_one' := _,
  mul_assoc' := _ }
end G_m

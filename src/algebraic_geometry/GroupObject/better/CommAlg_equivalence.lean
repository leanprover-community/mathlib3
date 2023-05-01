import algebraic_geometry.GroupObject.CommAlg
import algebraic_geometry.GroupObject.CommMon_

universes v u
noncomputable theory
open category_theory

variables (R : Type u) [comm_ring R]

@[simps] def CommAlg_to_CommMon_ : CommAlg.{u} R ⥤ CommMon_ (Module.{u} R) :=
{ obj := λ X,
  { mul_comm' := sorry, .. Module.Mon_Module_equivalence_Algebra.inverse_obj (Algebra.of R X) },
  map := λ X Y f, Module.Mon_Module_equivalence_Algebra.inverse.map f }

@[simps] def CommMon_to_CommAlg : CommMon_ (Module.{u} R) ⥤ CommAlg.{u} R :=
{ obj := λ X,
  { carrier := Module.Mon_Module_equivalence_Algebra.functor.obj X.to_Mon_,
    is_comm_ring :=
    { mul_comm := sorry, .. Module.Mon_Module_equivalence_Algebra.Mon_.X.ring X.to_Mon_ },
    is_algebra := Module.Mon_Module_equivalence_Algebra.Mon_.X.algebra X.to_Mon_ },
  map := λ X Y f, Module.Mon_Module_equivalence_Algebra.functor.map f }

def CommMon_CommAlg_equivalence :
  CommMon_ (Module.{u} R) ≌ CommAlg.{u} R :=
{ functor := CommMon_to_CommAlg R,
  inverse := CommAlg_to_CommMon_ R,
  unit_iso := sorry,
  counit_iso := sorry,
  functor_unit_iso_comp' := sorry }

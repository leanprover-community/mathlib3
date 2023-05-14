import representation_theory.Rep
import group_theory.group_action.basic
import algebra.category.Group.Z_Module_equivalence
universes u
open category_theory

namespace Action
variables (G : Mon.{u}) (X : Type u) (A : Action (Type u) G)

instance : mul_action G A.V :=
{ smul := λ g x, A.ρ g x,
  one_smul := function.funext_iff.1 A.ρ.map_one,
  mul_smul := λ x y, function.funext_iff.1 (A.ρ.map_mul x y) }

end Action
namespace mul_action

variables (G X : Type u) [monoid G] [mul_action G X]

@[simps] def to_Action : Action (Type u) (Mon.of G) :=
{ V := X,
  ρ :=
  { to_fun := λ g x, ((•) : G → X → X) g x,
    map_one' := by ext; exact one_smul _ _,
    map_mul' := λ x y, by ext; exact mul_smul _ _ _  } }

end mul_action
namespace Rep

variables (G : Type) [group G] (A : Rep ℤ G)

instance : distrib_mul_action G A :=
{ smul := λ g x, A.ρ g x,
  one_smul := linear_map.ext_iff.1 A.ρ.map_one,
  mul_smul := λ x y, linear_map.ext_iff.1 (A.ρ.map_mul x y),
  smul_zero := λ g, (A.ρ g).map_zero,
  smul_add := λ g, (A.ρ g).map_add }

noncomputable def Rep_Z_equivalence :
  Rep ℤ G ≌ Action AddCommGroup (Mon.of G) :=
(forget₂ (Module ℤ) AddCommGroup).as_equivalence.map_Action_equivalence (Mon.of G)

end Rep
namespace distrib_mul_action

#exit
variables (G A : Type) [group G] [add_comm_group A] [distrib_mul_action G A]
#check distrib_mul_action
@[simps] def to_Rep : Action AddCommGroup (Mon.of G) :=
{ V := Module.of ℤ A,
  ρ :=
  { to_fun := _,
    map_one' := _,
    map_mul' := _ } }


end distrib_mul_action

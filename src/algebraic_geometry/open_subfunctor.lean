import algebraic_geometry.Scheme
import category_theory.limits.functor_category
import algebraic_geometry.presheafed_space.open_immersion

universes v u

open category_theory category_theory.limits algebraic_geometry algebraic_geometry.PresheafedSpace
namespace algebraic_geometry.Scheme

set_option pp.universes true

-- instance i : has_limits (Schemeᵒᵖ ⥤ Type u) :=

--   @limits.functor_category_has_limits.{u} (Type u) _

#check Top
#check Scheme
#check PresheafedSpace
#check PresheafedSpace.carrier
#check functor.category (Type u) (Type u)
#check has_limits_of_shape

variables [has_pullbacks (Scheme.{u}ᵒᵖ ⥤ Type u)]

class open_subfunctor {F G : Scheme.{u}ᵒᵖ ⥤ Type u} (f : F ⟶ G) :=
(subfunctor : mono f)
(res : ∀ {S : Scheme.{u}} (g : yoneda.obj S ⟶ G), functor.representable (pullback f g))
(res_open : ∀ {S : Scheme.{u}} (g : yoneda.obj S ⟶ G),
  is_open_immersion (yoneda.preimage (functor.repr_f (pullback f g) ≫ pullback.snd)).val)

attribute[instance] open_subfunctor.subfunctor open_subfunctor.res open_subfunctor.res_open





end algebraic_geometry.Scheme

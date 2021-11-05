import algebraic_geometry.Scheme



open category_theory category_theory.limits
namespace algebraic_geometry.Scheme

class open_subfunctor {F G : Schemeᵒᵖ ⥤ Set} (f : F ⟶ G) :=
(subfunctor : mono f)
(res : ∀ {S : Scheme} (g : yoneda.obj S ⟶ G), functor.representable (pullback f g))
(restrict_open : ∀ )


end algebraic_geometry.Scheme

import algebraic_geometry.locally_ringed_space

namespace algebraic_geometry

universe u

open category_theory category_theory.limits

namespace LocallyRingedSpace

section has_coproducts

variables {ι : Type u} (F : discrete ι ⥤ LocallyRingedSpace)

instance : has_coproducts LocallyRingedSpace.{u} :=
λ ι, ⟨λ F, ⟨⟨by { }⟩⟩⟩

end has_coproducts

end LocallyRingedSpace

end algebraic_geometry

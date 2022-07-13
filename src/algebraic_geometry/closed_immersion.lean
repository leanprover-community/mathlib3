import topology.sheaves.functors
import algebraic_geometry.Scheme

universe u

/- Formalizing the equivalence of (2) and (4) in
   https://stacks.math.columbia.edu/tag/01QN -/

noncomputable theory

namespace algebraic_geometry

variables {X Y : Scheme.{u}} (f : X ⟶ Y)



/- Our definition here is item (4) in
   https://stacks.math.columbia.edu/tag/01QO -/

structure is_closed_immersion (f : X ⟶ Y) : Prop :=
    (is_closed_embedding_base : closed_embedding f.val.base)
    (is_surjective_on_sections : surjective (f.val.c))



end algebraic_geometry

import algebraic_geometry.locally_ringed_space
import algebraic_geometry.Spec

open topological_space

namespace algebraic_geometry

structure Scheme extends X : LocallyRingedSpace :=
(local_affine : ∀ x : carrier, ∃ (U : opens carrier) (m : x ∈ U) (R : CommRing)
  (i : X.restrict _ (opens.inclusion_open_embedding U) ≅ Spec R), true)

end algebraic_geometry

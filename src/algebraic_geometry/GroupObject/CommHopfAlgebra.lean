import algebraic_geometry.GroupObject.coalgebra
import algebraic_geometry.GroupObject.over_Affine_Spec_equivalence
universes v u
open category_theory algebraic_geometry
noncomputable theory

variables (R : Type*) [comm_ring R]

abbreviation Over := over (Scheme.Spec.obj (opposite.op (CommRing.of R)))
abbreviation AffineOver := over (AffineScheme.Spec.obj (opposite.op (CommRing.of R)))

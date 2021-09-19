import algebraic_geometry.Scheme
import category_theory.essential_image

noncomputable theory

open topological_space
open category_theory
open Top
open opposite

namespace algebraic_geometry

def AffineScheme := Scheme.Spec.ess_image

instance : category AffineScheme := infer_instance

namespace AffineScheme

end AffineScheme

end algebraic_geometry

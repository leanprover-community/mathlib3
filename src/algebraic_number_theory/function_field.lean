import algebra.field
import data.rat.basic
import ring_theory.algebraic
import ring_theory.dedekind_domain
import ring_theory.integral_closure

noncomputable theory

/-- `F` is a function field if it is a finite extension of the field of rational polynomials
in one variable over a finite field.

The map `f` witnesses that `L` is isomorphic to the rational polynomials over a finite field;
`f` is uniquely determined, thus it's marked as an `out_param`.
-/
class function_field_over {K L : Type*} [field K] [fintype K] [field L]
  (f : out_param (fraction_map (polynomial K) L)) (F : Type*) [field F]
  [algebra f.codomain F] : Prop :=
(fd : finite_dimensional f.codomain F)

/-- `F` is a function field if it is a finite extension of the field of rational polynomials
in one variable over a finite field.

This is a bundled version of `function_field_over`. -/
class function_field (F : Type*) [field F] :=
(fin_field : Type*) [field_fin_field : field fin_field] [fintype_fin_field : fintype fin_field]
(rat_poly : Type*) [field_rat_poly : field rat_poly]
(rat_poly_map' : fraction_map (polynomial fin_field) rat_poly)
[alg' : algebra rat_poly_map'.codomain F]
(ff_over' : @function_field_over _ _ _ _ _ rat_poly_map' F _ alg')

namespace function_field_over

variables {K L : Type*} [field K] [fintype K] [field L]
variables (f : fraction_map (polynomial K) L)
variables (F : Type*) [field F] [algebra f.codomain F] [function_field_over f F]

include f

attribute [instance] function_field_over.fd

@[nolint dangerous_instance] -- Since `f` is an out_param
instance : algebra (polynomial K) F :=
ring_hom.to_algebra ((algebra_map f.codomain F).comp (algebra_map (polynomial K) f.codomain))

instance : is_scalar_tower (polynomial K) f.codomain F :=
is_scalar_tower.of_algebra_map_eq (λ x, rfl)

end function_field_over

namespace function_field

variables (F : Type*) [field F] [function_field F]

attribute [instance] field_fin_field fintype_fin_field field_rat_poly

/-- `rat_poly_map F` is the map witnessing that `rat_poly F` is the field of
rational polynomials over `fin_field F`. -/
def rat_poly_map : fraction_map (polynomial (fin_field F)) (rat_poly F) :=
rat_poly_map'

instance alg : algebra (rat_poly_map F).codomain F :=
alg'

instance ff_over : function_field_over (rat_poly_map F) F :=
ff_over'

end function_field

namespace function_field_over

variables {K L : Type*} [field K] [fintype K] [field L]
variables (f : fraction_map (polynomial K) L)
variables (F : Type*) [field F] [algebra f.codomain F] [function_field_over f F]

include f

/-- The function field analogue of `number_field.ring_of_integers`. -/
def ring_of_integers := integral_closure (polynomial K) F

namespace ring_of_integers

open fraction_map

/-- `ring_of_integers.fraction_map K` is the map `O_F → F`, as a `fraction_map`. -/
protected def fraction_map : fraction_map (ring_of_integers f F) F :=
integral_closure.fraction_map_of_finite_extension _ f

instance : integral_domain (ring_of_integers f F) :=
(ring_of_integers f F).integral_domain

variables [is_separable f.codomain F]

instance is_dedekind_domain_integral_closure :
  is_dedekind_domain (integral_closure (polynomial K) F) :=
is_dedekind_domain.integral_closure f (principal_ideal_ring.is_dedekind_domain _)

instance : is_dedekind_domain (ring_of_integers f F) :=
ring_of_integers.is_dedekind_domain_integral_closure f F

end ring_of_integers

end function_field_over

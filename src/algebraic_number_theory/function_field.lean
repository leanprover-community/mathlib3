import algebra.field
import algebraic_number_theory.class_number
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
class function_field_over {K : Type*} {L : Type*} [field K] [fintype K] [field L]
  (f : out_param (fraction_map (polynomial K) L)) (F : Type*) [field F] :=
[alg : algebra f.codomain F]
[fd : finite_dimensional f.codomain F]

/-- `F` is a function field if it is a finite extension of the field of rational polynomials
in one variable over a finite field.

This is a bundled version of `function_field_over`. -/
class function_field (F : Type*) [field F] :=
(fin_field : Type*) [field_fin_field : field fin_field] [fintype_fin_field : fintype fin_field]
(rat_poly : Type*) [field_rat_poly : field rat_poly]
(rat_poly_map' : fraction_map (polynomial fin_field) rat_poly)
(ff_over' : function_field_over rat_poly_map' F)

namespace function_field_over

variables {K L : Type*} [field K] [fintype K] [field L]
variables (f : fraction_map (polynomial K) L)
variables (F : Type*) [field F] [function_field_over f F]

include f

attribute [instance] function_field_over.alg function_field_over.fd

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

instance ff_over : function_field_over (rat_poly_map F) F :=
ff_over'

/-- The function field analogue of `number_field.ring_of_integers`. -/
def ring_of_integers := integral_closure (polynomial (fin_field F)) F

namespace ring_of_integers

open fraction_map

/-- `ring_of_integers.fraction_map K` is the map `O_F → F`, as a `fraction_map`. -/
def fraction_map : fraction_map (ring_of_integers F) F :=
integral_closure.fraction_map_of_finite_extension _ (rat_poly_map F)

instance : integral_domain (ring_of_integers F) :=
(ring_of_integers F).integral_domain

variables [is_separable (rat_poly_map F).codomain F]

instance is_dedekind_domain_integral_closure :
  is_dedekind_domain (integral_closure (polynomial (fin_field F)) F) :=
is_dedekind_domain.integral_closure (rat_poly_map F) (principal_ideal_ring.is_dedekind_domain _)

instance : is_dedekind_domain (ring_of_integers F) :=
ring_of_integers.is_dedekind_domain_integral_closure F

variables [decidable_eq (fin_field F)]

noncomputable instance : fintype (class_group (ring_of_integers.fraction_map F)) :=
class_group.finite_of_admissible _ _ polynomial.admissible_char_pow_degree

/-- The class number in a function field is the (finite) cardinality of the class group. -/
noncomputable def class_number : ℕ := fintype.card (class_group (ring_of_integers.fraction_map F))

end ring_of_integers

end function_field

import algebra.field
import algebraic_number_theory.class_number
import data.rat.basic
import ring_theory.algebraic
import ring_theory.dedekind_domain
import ring_theory.integral_closure

class is_number_field (K : Type*) [field K] : Prop :=
[cz : char_zero K]
[fd : finite_dimensional ℚ K]

open function
open_locale classical big_operators

namespace number_field
variables (K : Type*) [field K] [is_number_field K]

 instance is_field_of_number_field : field K := by apply_instance

 instance char_zero_of_number_field : char_zero K := is_number_field.cz

 lemma finite_dimensional_of_number_field : finite_dimensional ℚ K := is_number_field.fd

 instance algebra_of_number_field : algebra ℚ K := rat.algebra_rat

lemma is_algebraic_of_number_field : algebra.is_algebraic ℚ K :=
  @algebra.is_algebraic_of_finite ℚ K _ _ _ (finite_dimensional_of_number_field K)

 instance infinite_of_number_field : infinite K := begin
  let f : ℤ → K := (λ n, (n : ℚ) • (1 : K)),
  apply infinite.of_injective f,
  intros x y hxy,
  have hxy2 : (x : ℚ) • (1 : K) = (y : ℚ) • (1 : K) := hxy,
  have h : 0 = ((x : ℚ) - (y : ℚ)) • (1 : K), calc 0 = (x : ℚ) • (1 : K) - (y : ℚ) • (1 : K) : by rw sub_eq_zero.mpr hxy
  ... = (x : ℚ) • (1 : K) + (-((y : ℚ) • (1 : K))) : sub_eq_add_neg (↑x • 1) (↑y • 1)
  ... = (x : ℚ) • (1 : K) + ((-(y : ℚ)) • (1 : K)) : by rw neg_smul
  ... = ((x : ℚ) + (-(y : ℚ))) • (1 : K) : by rw add_smul
  ... = ((x : ℚ) - (y : ℚ)) • (1 : K) : by rw sub_eq_add_neg,
  have h2 : ((x : ℚ) - (y : ℚ)) = 0 ∨ (1 : K) = 0, {exact (@smul_eq_zero ℚ K _ _ _ ((x : ℚ) - (y : ℚ)) (1 : K)).1 (eq.symm h)},
  cases h2, {have h3 : (x : ℚ) = (y : ℚ), exact sub_eq_zero.mp h2,
    exact (rat.coe_int_inj (x : ℤ) (y : ℤ)).1 h3},
  {exfalso, revert h2, simp}
end

def ring_of_integers := @integral_closure ℤ K _

namespace ring_of_integers

open fraction_map

local attribute [class] algebra.is_algebraic

-- TODO: we should make `fraction_map` extend `algebra`, so we don't need to add these instances.
instance : algebra int.fraction_map.codomain K := rat.algebra_rat
instance is_scalar_tower_int_rat :
  @is_scalar_tower ℤ int.fraction_map.codomain K int.fraction_map.algebra.to_has_scalar _ _ :=
is_scalar_tower.of_algebra_map_eq (λ x, by simp)
instance : char_zero int.fraction_map.codomain := show char_zero ℚ, by apply_instance
instance : finite_dimensional int.fraction_map.codomain K := ‹is_number_field K›.fd
instance : algebra.is_algebraic int.fraction_map.codomain K := is_algebraic_of_number_field K
instance : is_separable int.fraction_map.codomain K := is_separable_of_char_zero ℚ K

lemma algebra_map_eq_coe : (algebra_map ℤ ℚ : ℤ → ℚ) = coe := rfl

/-- `ring_of_integers.fraction_map K` is the map `O_K → K`, as a `fraction_map`. -/
def fraction_map : fraction_map (ring_of_integers K) K :=
integral_closure.fraction_map_of_finite_extension K int.fraction_map

instance : integral_domain (ring_of_integers K) :=
(ring_of_integers K).integral_domain

example (K : Type) [field K] (x : K) (h : x ≠ 0): x * (field.inv x) = 1 := field.mul_inv_cancel h

instance integral_closure_int.is_dedekind_domain : is_dedekind_domain (integral_closure ℤ K) :=
is_dedekind_domain.integral_closure int.fraction_map (principal_ideal_ring.is_dedekind_domain _)

instance : is_dedekind_domain (ring_of_integers K) :=
integral_closure_int.is_dedekind_domain K

noncomputable instance : fintype (class_group (ring_of_integers.fraction_map K)) :=
class_group.finite_of_admissible K int.fraction_map int.admissible_abs

/-- The class number of a number ring is the (finite) cardinality of the class group. -/
noncomputable def class_number : ℕ := fintype.card (class_group (ring_of_integers.fraction_map K))

end ring_of_integers

end number_field

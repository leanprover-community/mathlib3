import algebra.field
import data.rat.basic
import ring_theory.algebraic
import ring_theory.integral_closure
import ring_theory.dedekind_domain

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

 instance algebra_of_number_field : algebra ℚ K := sorry

 lemma is_algebraic_of_number_field : algebra.is_algebraic ℚ K := sorry

/- instance infinite_of_number_field : infinite K := begin
  let f : ℤ → K := (λ n, (n : ℚ) • (1 : K)),
  apply infinite.of_injective f,
  intros x y hxy,
  have hxy2 : (x : ℚ) • (1 : K) = (y : ℚ) • (1 : K), exact hxy,
  have h : 0 = ((x : ℚ) - (y : ℚ)) • (1 : K), calc 0 = (x : ℚ) • (1 : K) - (y : ℚ) • (1 : K) : by rw sub_eq_zero.mpr hxy
  ... = (x : ℚ) • (1 : K) + (-((y : ℚ) • (1 : K))) : sub_eq_add_neg (↑x • 1) (↑y • 1)
  ... = (x : ℚ) • (1 : K) + ((-(y : ℚ)) • (1 : K)) : by rw neg_smul
  ... = ((x : ℚ) + (-(y : ℚ))) • (1 : K) : by rw add_smul
  ... = ((x : ℚ) - (y : ℚ)) • (1 : K) : by rw sub_eq_add_neg,
  have h2 : ((x : ℚ) - (y : ℚ)) = 0 ∨ (1 : K) = 0, {exact (@smul_eq_zero ℚ K _ _ _ ((x : ℚ) - (y : ℚ)) (1 : K)).1 (eq.symm h)},
  cases h2, {have h3 : (x : ℚ) = (y : ℚ), exact sub_eq_zero.mp h2,
    exact (rat.coe_int_inj (x : ℤ) (y : ℤ)).1 h3},
  {exfalso, revert h2, simp}
end -/

def number_ring := @integral_closure ℤ K _

theorem integral_domain_of_number_ring : integral_domain (number_ring K) :=
(number_ring K).integral_domain

example (K : Type) [field K] (x : K) (h : x ≠ 0): x * (field.inv x) = 1 := field.mul_inv_cancel h

/- theorem is_noetherian_ring_of_number_ring : is_noetherian_ring (number_ring K) :=
begin
  constructor,
  rintros s,
--  constructor,
  sorry,
end

theorem dimension_le_one_of_number_ring : ring.dimension_le_one (number_ring K) :=
begin
  rintros p ne_bot Hp,
  sorry,
end

lemma fraction_ring_of_number_ring_eq_number_field : fraction_ring (number_ring K) = K :=
begin
  sorry,
end

theorem is_integrally_closed_of_number_ring :
integral_closure (number_ring K) (fraction_ring (number_ring K)) = ⊥ :=
begin
  rw number_ring,
  rw dedekind_domain.
  sorry,
end -/

theorem dedekind_domain_of_number_ring : is_dedekind_domain (number_ring K) :=
begin
  refine is_dedekind_domain.integral_closure _ _,
  exact ℚ,
  apply_instance,
  refine fraction_map.int.fraction_map,
  {
    show algebra ℚ K,
    apply_instance,  },
  {
    apply is_scalar_tower.of_algebra_map_eq, simp, },
  { show finite_dimensional ℚ K,
    --unfold finite_dimensional,
    apply finite_dimensional_of_number_field K,
    sorry, },
  { show is_separable ℚ K,
    refine @is_separable_of_char_zero ℚ K _ _ _ _ (is_algebraic_of_number_field K), },
  apply_instance,
end

end number_field

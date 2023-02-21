import data.polynomial.laurent 
import data.polynomial.ring_division
import ring_theory.is_tensor_product 
import algebraic_geometry.GroupObject.GroupScheme
variables {R S : Type*} [comm_ring R] [comm_ring S]
  [is_domain R] [is_domain S]

local notation R`[T;T⁻¹]`:9000 := laurent_polynomial R
open laurent_polynomial 
#check polynomial.monomial
lemma hmmmmm (x y : polynomial R) (n : ℕ) (r : R) 
  (h : x * y = polynomial.C r * polynomial.X ^ n) :
  polynomial.support x = {x.nat_degree} :=
begin
  sorry,
end 

lemma hmmm (x : R[T;T⁻¹]) (h : is_unit x) :
  ∃ (n : ℤ) (r : R), x = C r * T n :=
begin
  rcases exists_T_pow x with ⟨n, y, hy⟩,
  rcases is_unit.exists_left_inv h with ⟨z, hz⟩,
  rcases exists_T_pow z with ⟨m, w, hw⟩,
  have H1 : polynomial.to_laurent w * T (-m : ℤ) = z :=
  by simp only [*, mul_T_assoc, add_right_neg, T_zero, mul_one] at *,
  have H2 : polynomial.to_laurent y * T (-n : ℤ) = x :=
  by simp only [*, mul_T_assoc, add_right_neg, T_zero, mul_one] at *,
  rw [←H1, ←H2] at hz,
  rw mul_left_comm at hz,
  rw mul_T_assoc at hz,
  rw ←neg_add_rev at hz,
  sorry,
end

open_locale tensor_product 

def comul (R : Type*) [comm_ring R] : R[T;T⁻¹] →+* R[T;T⁻¹] ⊗[R] R[T;T⁻¹] :=
{ to_fun := _,
  map_one' := _,
  map_mul' := _,
  map_zero' := _,
  map_add' := _ }
import algebra.algebra.basic
import ring_theory.localization.fraction_ring -- only needed for one lemma which should probably just be moved.

namespace algebra_map

instance has_lift_t (R A : Type*) [comm_semiring R] [semiring A] [algebra R A] :
  has_lift_t R A := ⟨λ r, algebra_map R A r⟩

section comm_semiring_semiring

variables {R A : Type*} [comm_semiring R] [semiring A] [algebra R A]

@[simp, norm_cast] lemma coe_zero : (↑(0 : R) : A) = 0 := map_zero (algebra_map R A)
@[simp, norm_cast] lemma coe_one : (↑(1 : R) : A) = 1 := map_one (algebra_map R A)
@[norm_cast] lemma coe_add (a b : R) : (↑(a + b : R) : A) = ↑a + ↑b :=
map_add (algebra_map R A) a b
@[norm_cast] lemma coe_mul (a b : R) : (↑(a * b : R) : A) = ↑a * ↑b :=
map_mul (algebra_map R A) a b
@[norm_cast] lemma coe_pow (a : R) (n : ℕ) : (↑(a ^ n : R) : A) = ↑a ^ n :=
map_pow (algebra_map R A) _ _

end comm_semiring_semiring

section comm_ring_ring

variables {R A : Type*} [comm_ring R] [ring A] [algebra R A]

@[norm_cast] lemma coe_neg (x : R) : (↑(-x : R) : A) = -↑x :=
map_neg (algebra_map R A) x

end comm_ring_ring

section comm_semiring_comm_semiring

variables {R A : Type*} [comm_semiring R] [comm_semiring A] [algebra R A]

open_locale big_operators

-- direct to_additive fails because of some mix-up with polynomials
@[norm_cast] lemma coe_prod {ι : Type*} {s : finset ι} (a : ι → R) :
  (↑( ∏ (i : ι) in s, a i : R) : A) = ∏ (i : ι) in s, (↑(a i) : A) :=
map_prod (algebra_map R A) a s

-- to_additive fails for some reason
@[norm_cast] lemma coe_sum {ι : Type*} {s : finset ι} (a : ι → R) :
  ↑(( ∑ (i : ι) in s, a i)) = ∑ (i : ι) in s, (↑(a i) : A) :=
map_sum (algebra_map R A) a s

attribute [to_additive] coe_prod

end comm_semiring_comm_semiring

section comm_ring_comm_ring

variables {R A : Type*} [comm_ring R] [comm_ring A] [algebra R A]

-- [is_fraction_ring] bumps the imports but I have an application, probably
-- this lemma should be elsewhere
@[norm_cast, simp] lemma coe_inj' [is_fraction_ring R A] {a b : R} : (↑a : A) = ↑b ↔ a = b :=
⟨λ h, is_fraction_ring.injective R A h, by rintro rfl; refl⟩

end comm_ring_comm_ring

section field_nontrivial

variables {R A : Type*} [field R] [comm_semiring A] [nontrivial A] [algebra R A]

@[norm_cast, simp] lemma coe_inj {a b : R} : (↑a : A) = ↑b ↔ a = b :=
⟨λ h, (algebra_map R A).injective h, by rintro rfl; refl⟩

@[norm_cast, simp] lemma lift_map_eq_zero_iff (a : R) : (↑a : A) = 0 ↔ a = 0 :=
begin
  rw (show (0 : A) = ↑(0 : R), from (map_zero (algebra_map R A)).symm),
  norm_cast,
end

end field_nontrivial

end algebra_map

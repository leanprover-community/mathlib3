namespace monoid_hom

variables {M : Type*} {G : Type*} [monoid M] [group G]

@[simp, to_additive]
theorem iterate_map_one (f : M →* M) (n : ℕ) : f^[n] 1 = 1 :=
nat.iterate₀ f.map_one

@[simp, to_additive]
theorem iterate_map_mul (f : M →* M) (n : ℕ) (x y) :
  f^[n] (x * y) = (f^[n] x) * (f^[n] y) :=
nat.iterate₂ f.map_mul

@[simp, to_additive]
theorem iterate_map_inv (f : G →* G) (n : ℕ) (x) :
  f^[n] (x⁻¹) = (f^[n] x)⁻¹ :=
nat.iterate₁ f.map_inv

@[simp]
theorem iterate_map_sub {A : Type*} [add_group A] (f : A →+ A) (n : ℕ) (x y) :
  f^[n] (x - y) = (f^[n] x) - (f^[n] y) :=
nat.iterate₂ f.map_sub

end monoid_hom

namespace ring_hom

variables {R : Type*} [semiring R] {S : Type*} [ring S]

@[simp] theorem iterate_map_one (f : R →+* R) (n : ℕ) : f^[n] 1 = 1 :=
nat.iterate₀ f.map_one

@[simp] theorem iterate_map_zero (f : R →+* R) (n : ℕ) : f^[n] 0 = 0 :=
nat.iterate₀ f.map_zero

@[simp] theorem iterate_map_mul (f : R →+* R) (n : ℕ) (x y) :
  f^[n] (x * y) = (f^[n] x) * (f^[n] y) :=
nat.iterate₂ f.map_mul

@[simp] theorem iterate_map_add (f : R →+* R) (n : ℕ) (x y) :
  f^[n] (x + y) = (f^[n] x) + (f^[n] y) :=
nat.iterate₂ f.map_add

@[simp] theorem iterate_map_neg (f : S →+* S) (n : ℕ) (x) :
  f^[n] (-x) = -(f^[n] x) :=
nat.iterate₁ f.map_neg

@[simp] theorem iterate_map_sub (f : S →+* S) (n : ℕ) (x y) :
  f^[n] (x - y) = (f^[n] x) - (f^[n] y) :=
nat.iterate₂ f.map_sub

end ring_hom

theorem monoid_hom.iterate_map_pow (f : M →* M) (a) (n m : ℕ) : f^[n] (a^m) = (f^[n] a)^m :=
show f^[n] ((λ x, x^m) a) = (λ x, x^m) (f^[n] a),
from nat.iterate₁ $ λ x, f.map_pow x m

theorem add_monoid_hom.iterate_map_smul (f : A →+ A) (a : A) (n m : ℕ) :
  f^[n] (m • a) = m • (f^[n] a) :=
f.to_multiplicative.iterate_map_pow a n m

namespace ring_hom

lemma iterate_map_pow (a) (n m : ℕ) : f^[n] (a^m) = (f^[n] a)^m :=
f.to_monoid_hom.iterate_map_pow a n m

lemma iterate_map_smul (a) (n m : ℕ) : f^[n] (m • a) = m • (f^[n] a) :=
f.to_add_monoid_hom.iterate_map_smul a n m

end ring_hom

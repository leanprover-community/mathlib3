import ring_theory.algebra
import tactic

/- IMPORTANT TODO: generalize this theory to bimodules. Important cases for mathematical
physics are left out. -/

open algebra ring_hom

variables (R : Type*) (A : Type*) [comm_semiring R] [comm_semiring A] [algebra R A]
  (M : Type*) [add_cancel_comm_monoid M] [semimodule A M]

def transitive_scalar (R : Type*) (A : Type*) (M : Type*)
  [comm_semiring R] [semiring A] [algebra R A]
  [add_comm_monoid M] [semimodule A M] : has_scalar R M :=
{ smul := λ r m, ((algebra_map R A) r) • m, }

def transitive_module (R : Type*) (A : Type*) (M : Type*)
  [comm_semiring R] [semiring A] [algebra R A] [add_comm_monoid M] [semimodule A M] :
  semimodule R M :=
{ smul_add := λ r x y, smul_add _ _ _,
  smul_zero := λ r, smul_zero _,
  zero_smul := λ x, show algebra_map R A 0 • x = 0, by rw [map_zero, zero_smul],
  one_smul := λ x, show algebra_map R A 1 • x = x, by rw [map_one, one_smul],
  mul_smul := λ r s x, show algebra_map R A (r * s) • x =
    algebra_map R A r • algebra_map R A s • x, by rw [map_mul, mul_smul],
  add_smul := λ r s x, show algebra_map R A (r + s) • x =
    algebra_map R A r • x + algebra_map R A s • x, by rw [map_add, add_smul],
  .. transitive_scalar R A M }

class compatible_semimodule (R : Type*) (A : Type*) [comm_semiring R] [semiring A]
  [algebra R A] (M : Type*) [add_comm_monoid M] [semimodule A M] [semimodule R M] :=
(compatible {r : R} {m : M} : r • m = ((algebra_map R A) r) • m)

structure derivation [semimodule A M] [semimodule R M] [compatible_semimodule R A M]
  extends A →ₗ[R] M :=
(leibniz' (a b : A) : to_fun (a * b) = a • to_fun b + b • to_fun a)

section

variables {R} {A} {M} [semimodule R M] [compatible_semimodule R A M]

namespace derivation

instance : has_coe_to_fun (derivation R A M) := ⟨_, λ D, D.to_linear_map.to_fun⟩

instance has_coe_to_linear_map : has_coe (derivation R A M) (A →ₗ[R] M) :=
  ⟨λ D, D.to_linear_map⟩

lemma one_mul_one (M : Type*) [monoid M] : 1 * 1 = 1 := one_mul 1

section
variables {R A} (D : derivation R A M) (r : R) (a b : A)
@[simp] lemma map_add : D (a + b) = D a + D b := is_add_hom.map_add D a b
@[simp] lemma map_zero : D 0 = 0 := is_add_monoid_hom.map_zero D
@[simp] lemma map_mul : D (a * b) = a • D b + b • D a := D.leibniz' _ _
@[simp] lemma leibniz : D (a * b) = b • D a + a • D b := (D.leibniz' a b).trans $ add_comm _ _
@[simp] lemma map_one_eq_zero : D 1 = 0 :=
begin
  have h : D 1 = D (1 * 1) := by rw mul_one,
  rw [leibniz D 1 1, one_smul] at h, /- better way to do this? -/
  exact zero_left_cancel h,
end
@[simp] lemma map_algebra_map : D (algebra_map R A r) = 0 :=
begin
  rw [←mul_one r, monoid_hom.map_mul R A (algebra_map R A) r 1],
  simp only [map_one_eq_zero],
  exact map_one_eq_zero,
end

variables [comm_ring R] [ring A] [algebra R A] [add_comm_group M] [module A M]

@[simp] lemma map_neg : D (-a) = -D a := add_monoid_hom.map_neg D a
@[simp] lemma map_sub : D (a - b) = D a - D b := is_add_group_hom.map_sub D a b

variables {D1 D2 : derivation R A}

lemma coe_injective (H : ⇑D1 = D2) : D1 = D2 :=
by cases D1; cases D2; congr'; exact linear_map.coe_injective H

@[ext] theorem ext (H : ∀ a, D1 a = D2 a) : D1 = D2 :=
coe_injective $ funext H

instance : add_comm_group (derivation R A) :=
by refine
{ add := λ D1 D2, ⟨λ a, D1 a + D2 a,
    λ a1 a2, by rw [D1.map_add, D2.map_add, add_comm₄],
    λ a1 a2, by rw [D1.map_mul, D2.map_mul, smul_add, smul_add, add_comm₄],
    λ r, by rw [D1.map_algebra_map, D2.map_algebra_map, add_zero]⟩,
  zero := ⟨λ a, 0,
    λ a1 a2, by rw add_zero,
    λ a1 a2, by rw [smul_zero, smul_zero, add_zero],
    λ r, rfl⟩,
  neg := λ D, ⟨λ a, -D a,
    λ a1 a2, by rw [D.map_add, neg_add],
    λ a1 a2, by rw [D.map_mul, neg_add, smul_neg, smul_neg],
    λ r, by rw [D.map_algebra_map, neg_zero]⟩,
  .. }

instance : module A (derivation R A) :=
{ smul := λ a D, ⟨λ b, a • D b,
    λ a1 a2, by rw [D.map_add, smul_add],
    λ a1 a2, by rw [D.map_mul, smul_add, smul_smul, smul_smul, mul_comm, mul_smul, mul_comm, mul_smul],
    λ s, by rw [D.map_algebra_map, smul_zero]⟩,
  mul_smul := λ a1 a2 D, ext $ λ b, mul_smul _ _ _,
  one_smul := λ D, ext $ λ b, one_smul A _,
  smul_add := λ a D1 D2, ext $ λ b, smul_add _ _ _,
  smul_zero := λ a, ext $ λ b, smul_zero _,
  add_smul := λ a1 a2 D, ext $ λ b, add_smul _ _ _,
  zero_smul := λ D, ext $ λ b, zero_smul A _ }

variables {R A M}
def comp {N : Type*} [add_comm_group N] [module A N]
  (D : derivation R A M) (f : M →ₗ[A] N) : derivation R A N :=
{ to_fun := λ a, f (D a),
  add := λ a1 a2, by rw [D.map_add, f.map_add],
  mul := λ a1 a2, by rw [D.map_mul, f.map_add, f.map_smul, f.map_smul],
  algebra := λ r, by rw [D.map_algebra_map, f.map_zero] }

end derivation

end

/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import data.matrix.basic
import linear_algebra.tensor_product
import ring_theory.subsemiring

/-!
# Algebra over Commutative Semiring (under category)

In this file we define algebra over commutative (semi)rings, algebra homomorphisms `alg_hom`,
algebra equivalences `alg_equiv`, and `subalgebra`s. We also define usual operations on `alg_hom`s
(`id`, `comp`) and subalgebras (`map`, `comap`).

If `S` is an `R`-algebra and `A` is an `S`-algebra then `algebra.comap.algebra R S A` can be used
to provide `A` with a structure of an `R`-algebra. Other than that, `algebra.comap` is now
deprecated and replcaed with `is_algebra_tower`.

## Notations

* `A →ₐ[R] B` : `R`-algebra homomorphism from `A` to `B`.
* `A ≃ₐ[R] B` : `R`-algebra equivalence from `A` to `B`.
-/
noncomputable theory

universes u v w u₁ v₁

open_locale tensor_product big_operators

section prio
-- We set this priority to 0 later in this file
set_option default_priority 200 -- see Note [default priority]
/-- The category of R-algebras where R is a commutative
ring is the under category R ↓ CRing. In the categorical
setting we have a forgetful functor R-Alg ⥤ R-Mod.
However here it extends module in order to preserve
definitional equality in certain cases. -/
@[nolint has_inhabited_instance]
class algebra (R : Type u) (A : Type v) [comm_semiring R] [semiring A]
  extends has_scalar R A, R →+* A :=
(commutes' : ∀ r x, to_fun r * x = x * to_fun r)
(smul_def' : ∀ r x, r • x = to_fun r * x)
end prio

/-- Embedding `R →+* A` given by `algebra` structure. -/
def algebra_map (R : Type u) (A : Type v) [comm_semiring R] [semiring A] [algebra R A] : R →+* A :=
algebra.to_ring_hom

/-- Creating an algebra from a morphism to the center of a semiring. -/
def ring_hom.to_algebra' {R S} [comm_semiring R] [semiring S] (i : R →+* S)
  (h : ∀ c x, i c * x = x * i c) :
  algebra R S :=
{ smul := λ c x, i c * x,
  commutes' := h,
  smul_def' := λ c x, rfl,
  .. i}

/-- Creating an algebra from a morphism to a commutative semiring. -/
def ring_hom.to_algebra {R S} [comm_semiring R] [comm_semiring S] (i : R →+* S) :
  algebra R S :=
i.to_algebra' $ λ _, mul_comm _

namespace algebra

variables {R : Type u} {S : Type v} {A : Type w}

/-- Let `R` be a commutative semiring, let `A` be a semiring with a `semimodule R` structure.
If `(r • 1) * x = x * (r • 1) = r • x` for all `r : R` and `x : A`, then `A` is an `algebra`
over `R`. -/
def of_semimodule' [comm_semiring R] [semiring A] [semimodule R A]
  (h₁ : ∀ (r : R) (x : A), (r • 1) * x = r • x)
  (h₂ : ∀ (r : R) (x : A), x * (r • 1) = r • x) : algebra R A :=
{ to_fun := λ r, r • 1,
  map_one' := one_smul _ _,
  map_mul' := λ r₁ r₂, by rw [h₁, mul_smul],
  map_zero' := zero_smul _ _,
  map_add' := λ r₁ r₂, add_smul r₁ r₂ 1,
  commutes' := λ r x, by simp only [h₁, h₂],
  smul_def' := λ r x, by simp only [h₁] }

/-- Let `R` be a commutative semiring, let `A` be a semiring with a `semimodule R` structure.
If `(r • x) * y = x * (r • y) = r • (x * y)` for all `r : R` and `x y : A`, then `A`
is an `algebra` over `R`. -/
def of_semimodule [comm_semiring R] [semiring A] [semimodule R A]
  (h₁ : ∀ (r : R) (x y : A), (r • x) * y = r • (x * y))
  (h₂ : ∀ (r : R) (x y : A), x * (r • y) = r • (x * y)) : algebra R A :=
of_semimodule' (λ r x, by rw [h₁, one_mul]) (λ r x, by rw [h₂, mul_one])

section semiring

variables [comm_semiring R] [comm_semiring S] [semiring A] [algebra R A]

lemma smul_def'' (r : R) (x : A) : r • x = algebra_map R A r * x :=
algebra.smul_def' r x

/--
To prove two algebra structures on a fixed `[comm_semiring R] [semiring A]` agree,
it suffices to check the `algebra_map`s agree.
-/
-- We'll later use this to show `algebra ℤ M` is a subsingleton.
@[ext]
lemma algebra_ext {R : Type*} [comm_semiring R] {A : Type*} [semiring A] (P Q : algebra R A)
  (w : ∀ (r : R), by { haveI := P, exact algebra_map R A r } = by { haveI := Q, exact algebra_map R A r }) :
  P = Q :=
begin
  unfreezingI { rcases P with ⟨⟨P⟩⟩, rcases Q with ⟨⟨Q⟩⟩ },
  congr,
  { funext r a,
    replace w := congr_arg (λ s, s * a) (w r),
    simp only [←algebra.smul_def''] at w,
    apply w, },
  { ext r,
    exact w r, },
  { apply proof_irrel_heq, },
  { apply proof_irrel_heq, },
end

@[priority 200] -- see Note [lower instance priority]
instance to_semimodule : semimodule R A :=
{ one_smul := by simp [smul_def''],
  mul_smul := by simp [smul_def'', mul_assoc],
  smul_add := by simp [smul_def'', mul_add],
  smul_zero := by simp [smul_def''],
  add_smul := by simp [smul_def'', add_mul],
  zero_smul := by simp [smul_def''] }

-- from now on, we don't want to use the following instance anymore
attribute [instance, priority 0] algebra.to_has_scalar

lemma smul_def (r : R) (x : A) : r • x = algebra_map R A r * x :=
algebra.smul_def' r x

lemma algebra_map_eq_smul_one (r : R) : algebra_map R A r = r • 1 :=
calc algebra_map R A r = algebra_map R A r * 1 : (mul_one _).symm
                   ... = r • 1                 : (algebra.smul_def r 1).symm

theorem commutes (r : R) (x : A) : algebra_map R A r * x = x * algebra_map R A r :=
algebra.commutes' r x

theorem left_comm (r : R) (x y : A) : x * (algebra_map R A r * y) = algebra_map R A r * (x * y) :=
by rw [← mul_assoc, ← commutes, mul_assoc]

@[simp] lemma mul_smul_comm (s : R) (x y : A) :
  x * (s • y) = s • (x * y) :=
by rw [smul_def, smul_def, left_comm]

@[simp] lemma smul_mul_assoc (r : R) (x y : A) :
  (r • x) * y = r • (x * y) :=
by rw [smul_def, smul_def, mul_assoc]

variables (R)
instance id : algebra R R := (ring_hom.id R).to_algebra
variables {R}

namespace id

@[simp] lemma map_eq_self (x : R) : algebra_map R R x = x := rfl

@[simp] lemma smul_eq_mul (x y : R) : x • y = x * y := rfl

end id

/-- Algebra over a subsemiring. -/
instance of_subsemiring (S : subsemiring R) : algebra S A :=
{ smul := λ s x, (s : R) • x,
  commutes' := λ r x, algebra.commutes r x,
  smul_def' := λ r x, algebra.smul_def r x,
  .. (algebra_map R A).comp (subsemiring.subtype S) }

/-- Algebra over a subring. -/
instance of_subring {R A : Type*} [comm_ring R] [ring A] [algebra R A]
  (S : set R) [is_subring S] : algebra S A :=
{ smul := λ s x, (s : R) • x,
  commutes' := λ r x, algebra.commutes r x,
  smul_def' := λ r x, algebra.smul_def r x,
  .. (algebra_map R A).comp (⟨coe, rfl, λ _ _, rfl, rfl, λ _ _, rfl⟩ : S →+* R) }

variables (R A)
/-- The multiplication in an algebra is a bilinear map. -/
def lmul : A →ₗ A →ₗ A :=
linear_map.mk₂ R (*)
  (λ x y z, add_mul x y z)
  (λ c x y, by rw [smul_def, smul_def, mul_assoc _ x y])
  (λ x y z, mul_add x y z)
  (λ c x y, by rw [smul_def, smul_def, left_comm])

/-- The multiplication on the left in an algebra is a linear map. -/
def lmul_left (r : A) : A →ₗ A :=
lmul R A r

/-- The multiplication on the right in an algebra is a linear map. -/
def lmul_right (r : A) : A →ₗ A :=
(lmul R A).flip r

variables {R A}

@[simp] lemma lmul_apply (p q : A) : lmul R A p q = p * q := rfl
@[simp] lemma lmul_left_apply (p q : A) : lmul_left R A p q = p * q := rfl
@[simp] lemma lmul_right_apply (p q : A) : lmul_right R A p q = q * p := rfl

end semiring

end algebra

instance module.endomorphism_algebra (R : Type u) (M : Type v)
  [comm_ring R] [add_comm_group M] [module R M] : algebra R (M →ₗ[R] M) :=
{ to_fun    := λ r, r • linear_map.id,
  map_one' := one_smul _ _,
  map_zero' := zero_smul _ _,
  map_add' := λ r₁ r₂, add_smul _ _ _,
  map_mul' := λ r₁ r₂, by { ext x, simp [mul_smul] },
  commutes' := by { intros, ext, simp },
  smul_def' := by { intros, ext, simp } }

instance matrix_algebra (n : Type u) (R : Type v)
  [fintype n] [decidable_eq n] [comm_semiring R] : algebra R (matrix n n R) :=
{ commutes' := by { intros, simp [matrix.scalar], },
  smul_def' := by { intros, simp [matrix.scalar], },
  ..(matrix.scalar n) }

set_option old_structure_cmd true
/-- Defining the homomorphism in the category R-Alg. -/
@[nolint has_inhabited_instance]
structure alg_hom (R : Type u) (A : Type v) (B : Type w)
  [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] extends ring_hom A B :=
(commutes' : ∀ r : R, to_fun (algebra_map R A r) = algebra_map R B r)

run_cmd tactic.add_doc_string `alg_hom.to_ring_hom "Reinterpret an `alg_hom` as a `ring_hom`"

infixr ` →ₐ `:25 := alg_hom _
notation A ` →ₐ[`:25 R `] ` B := alg_hom R A B

namespace alg_hom

variables {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

section semiring

variables [comm_semiring R] [semiring A] [semiring B] [semiring C] [semiring D]
variables [algebra R A] [algebra R B] [algebra R C] [algebra R D]

instance : has_coe_to_fun (A →ₐ[R] B) := ⟨_, λ f, f.to_fun⟩

instance coe_ring_hom : has_coe (A →ₐ[R] B) (A →+* B) := ⟨alg_hom.to_ring_hom⟩

instance coe_monoid_hom : has_coe (A →ₐ[R] B) (A →* B) := ⟨λ f, ↑(f : A →+* B)⟩

instance coe_add_monoid_hom : has_coe (A →ₐ[R] B) (A →+ B) := ⟨λ f, ↑(f : A →+* B)⟩

@[simp, norm_cast] lemma coe_mk {f : A → B} (h₁ h₂ h₃ h₄ h₅) :
  ⇑(⟨f, h₁, h₂, h₃, h₄, h₅⟩ : A →ₐ[R] B) = f := rfl

@[simp, norm_cast] lemma coe_to_ring_hom (f : A →ₐ[R] B) : ⇑(f : A →+* B) = f := rfl

-- as `simp` can already prove this lemma, it is not tagged with the `simp` attribute.
@[norm_cast] lemma coe_to_monoid_hom (f : A →ₐ[R] B) : ⇑(f : A →* B) = f := rfl

-- as `simp` can already prove this lemma, it is not tagged with the `simp` attribute.
@[norm_cast] lemma coe_to_add_monoid_hom (f : A →ₐ[R] B) : ⇑(f : A →+ B) = f := rfl

variables (φ : A →ₐ[R] B)

theorem coe_fn_inj ⦃φ₁ φ₂ : A →ₐ[R] B⦄ (H : ⇑φ₁ = φ₂) : φ₁ = φ₂ :=
by { cases φ₁, cases φ₂, congr, exact H }

theorem coe_ring_hom_injective : function.injective (coe : (A →ₐ[R] B) → (A →+* B)) :=
λ φ₁ φ₂ H, coe_fn_inj $ show ((φ₁ : (A →+* B)) : A → B) = ((φ₂ : (A →+* B)) : A → B),
  from congr_arg _ H

theorem coe_monoid_hom_injective : function.injective (coe : (A →ₐ[R] B)  → (A →* B)) :=
ring_hom.coe_monoid_hom_injective.comp coe_ring_hom_injective

theorem coe_add_monoid_hom_injective : function.injective (coe : (A →ₐ[R] B)  → (A →+ B)) :=
ring_hom.coe_add_monoid_hom_injective.comp coe_ring_hom_injective

@[ext]
theorem ext {φ₁ φ₂ : A →ₐ[R] B} (H : ∀ x, φ₁ x = φ₂ x) : φ₁ = φ₂ :=
coe_fn_inj $ funext H

theorem ext_iff {φ₁ φ₂ : A →ₐ[R] B} : φ₁ = φ₂ ↔ ∀ x, φ₁ x = φ₂ x :=
⟨by { rintro rfl x, refl }, ext⟩

@[simp]
theorem commutes (r : R) : φ (algebra_map R A r) = algebra_map R B r := φ.commutes' r

theorem comp_algebra_map : φ.to_ring_hom.comp (algebra_map R A) = algebra_map R B :=
ring_hom.ext $ φ.commutes

@[simp] lemma map_add (r s : A) : φ (r + s) = φ r + φ s :=
φ.to_ring_hom.map_add r s

@[simp] lemma map_zero : φ 0 = 0 :=
φ.to_ring_hom.map_zero

@[simp] lemma map_mul (x y) : φ (x * y) = φ x * φ y :=
φ.to_ring_hom.map_mul x y

@[simp] lemma map_one : φ 1 = 1 :=
φ.to_ring_hom.map_one

@[simp] lemma map_smul (r : R) (x : A) : φ (r • x) = r • φ x :=
by simp only [algebra.smul_def, map_mul, commutes]

@[simp] lemma map_pow (x : A) (n : ℕ) : φ (x ^ n) = (φ x) ^ n :=
φ.to_ring_hom.map_pow x n

lemma map_sum {ι : Type*} (f : ι → A) (s : finset ι) :
  φ (∑ x in s, f x) = ∑ x in s, φ (f x) :=
φ.to_ring_hom.map_sum f s

@[simp] lemma map_nat_cast (n : ℕ) : φ n = n :=
φ.to_ring_hom.map_nat_cast n

section

variables (R A)
/-- Identity map as an `alg_hom`. -/
protected def id : A →ₐ[R] A :=
{ commutes' := λ _, rfl,
  ..ring_hom.id A  }

end

@[simp] lemma id_apply (p : A) : alg_hom.id R A p = p := rfl

/-- Composition of algebra homeomorphisms. -/
def comp (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) : A →ₐ[R] C :=
{ commutes' := λ r : R, by rw [← φ₁.commutes, ← φ₂.commutes]; refl,
  .. φ₁.to_ring_hom.comp ↑φ₂ }

@[simp] lemma comp_apply (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) (p : A) :
  φ₁.comp φ₂ p = φ₁ (φ₂ p) := rfl

@[simp] theorem comp_id : φ.comp (alg_hom.id R A) = φ :=
ext $ λ x, rfl

@[simp] theorem id_comp : (alg_hom.id R B).comp φ = φ :=
ext $ λ x, rfl

theorem comp_assoc (φ₁ : C →ₐ[R] D) (φ₂ : B →ₐ[R] C) (φ₃ : A →ₐ[R] B) :
  (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃) :=
ext $ λ x, rfl

/-- R-Alg ⥤ R-Mod -/
def to_linear_map : A →ₗ B :=
{ to_fun := φ,
  map_add' := φ.map_add,
  map_smul' := φ.map_smul }

@[simp] lemma to_linear_map_apply (p : A) : φ.to_linear_map p = φ p := rfl

theorem to_linear_map_inj {φ₁ φ₂ : A →ₐ[R] B} (H : φ₁.to_linear_map = φ₂.to_linear_map) : φ₁ = φ₂ :=
ext $ λ x, show φ₁.to_linear_map x = φ₂.to_linear_map x, by rw H

@[simp] lemma comp_to_linear_map (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
  (g.comp f).to_linear_map = g.to_linear_map.comp f.to_linear_map := rfl

end semiring

section comm_semiring

variables [comm_semiring R] [comm_semiring A] [comm_semiring B]
variables [algebra R A] [algebra R B]

variables (φ : A →ₐ[R] B)

lemma map_prod {ι : Type*} (f : ι → A) (s : finset ι) :
  φ (∏ x in s, f x) = ∏ x in s, φ (f x) :=
φ.to_ring_hom.map_prod f s

end comm_semiring

section ring

variables [comm_ring R] [ring A] [ring B] [ring C]
variables [algebra R A] [algebra R B] [algebra R C] (φ : A →ₐ[R] B)

@[simp] lemma map_neg (x) : φ (-x) = -φ x :=
φ.to_ring_hom.map_neg x

@[simp] lemma map_sub (x y) : φ (x - y) = φ x - φ y :=
φ.to_ring_hom.map_sub x y

end ring

end alg_hom

set_option old_structure_cmd true
/-- An equivalence of algebras is an equivalence of rings commuting with the actions of scalars. -/
structure alg_equiv (R : Type u) (A : Type v) (B : Type w)
  [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B]
  extends A ≃ B, A ≃* B, A ≃+ B, A ≃+* B :=
(commutes' : ∀ r : R, to_fun (algebra_map R A r) = algebra_map R B r)

attribute [nolint doc_blame] alg_equiv.to_ring_equiv
attribute [nolint doc_blame] alg_equiv.to_equiv
attribute [nolint doc_blame] alg_equiv.to_add_equiv
attribute [nolint doc_blame] alg_equiv.to_mul_equiv

notation A ` ≃ₐ[`:50 R `] ` A' := alg_equiv R A A'

namespace alg_equiv

variables {R : Type u} {A₁ : Type v} {A₂ : Type w} {A₃ : Type u₁}
variables [comm_semiring R] [semiring A₁] [semiring A₂] [semiring A₃]
variables [algebra R A₁] [algebra R A₂] [algebra R A₃]

instance : has_coe_to_fun (A₁ ≃ₐ[R] A₂) := ⟨_, alg_equiv.to_fun⟩

@[ext]
lemma ext {f g : A₁ ≃ₐ[R] A₂} (h : ∀ a, f a = g a) : f = g :=
begin
  have h₁ : f.to_equiv = g.to_equiv := equiv.ext h,
  cases f, cases g, congr,
  { exact (funext h) },
  { exact congr_arg equiv.inv_fun h₁ }
end

lemma coe_fun_injective : @function.injective (A₁ ≃ₐ[R] A₂) (A₁ → A₂) (λ e, (e : A₁ → A₂)) :=
begin
  intros f g w,
  ext,
  exact congr_fun w a,
end

instance has_coe_to_ring_equiv : has_coe (A₁ ≃ₐ[R] A₂) (A₁ ≃+* A₂) := ⟨alg_equiv.to_ring_equiv⟩

@[simp] lemma mk_apply {to_fun inv_fun left_inv right_inv map_mul map_add commutes a} :
  (⟨to_fun, inv_fun, left_inv, right_inv, map_mul, map_add, commutes⟩ : A₁ ≃ₐ[R] A₂) a = to_fun a :=
rfl

@[simp] lemma to_fun_apply {e : A₁ ≃ₐ[R] A₂} {a : A₁} : e.to_fun a = e a := rfl

@[simp, norm_cast] lemma coe_ring_equiv (e : A₁ ≃ₐ[R] A₂) : ((e : A₁ ≃+* A₂) : A₁ → A₂) = e := rfl

lemma coe_ring_equiv_injective : function.injective (λ e : A₁ ≃ₐ[R] A₂, (e : A₁ ≃+* A₂)) :=
begin
  intros f g w,
  ext,
  replace w : ((f : A₁ ≃+* A₂) : A₁ → A₂) = ((g : A₁ ≃+* A₂) : A₁ → A₂) :=
    congr_arg (λ e : A₁ ≃+* A₂, (e : A₁ → A₂)) w,
  exact congr_fun w a,
end

@[simp] lemma map_add (e : A₁ ≃ₐ[R] A₂) : ∀ x y, e (x + y) = e x + e y := e.to_add_equiv.map_add

@[simp] lemma map_zero (e : A₁ ≃ₐ[R] A₂) : e 0 = 0 := e.to_add_equiv.map_zero

@[simp] lemma map_mul (e : A₁ ≃ₐ[R] A₂) : ∀ x y, e (x * y) = (e x) * (e y) := e.to_mul_equiv.map_mul

@[simp] lemma map_one (e : A₁ ≃ₐ[R] A₂) : e 1 = 1 := e.to_mul_equiv.map_one

@[simp] lemma commutes (e : A₁ ≃ₐ[R] A₂) : ∀ (r : R), e (algebra_map R A₁ r) = algebra_map R A₂ r :=
  e.commutes'

@[simp] lemma map_neg {A₁ : Type v} {A₂ : Type w}
  [ring A₁] [ring A₂] [algebra R A₁] [algebra R A₂] (e : A₁ ≃ₐ[R] A₂) :
  ∀ x, e (-x) = -(e x) := e.to_add_equiv.map_neg

@[simp] lemma map_sub {A₁ : Type v} {A₂ : Type w}
  [ring A₁] [ring A₂] [algebra R A₁] [algebra R A₂] (e : A₁ ≃ₐ[R] A₂) :
  ∀ x y, e (x - y) = e x - e y := e.to_add_equiv.map_sub

lemma map_sum (e : A₁ ≃ₐ[R] A₂) {ι : Type*} (f : ι → A₁) (s : finset ι) :
  e (∑ x in s, f x) = ∑ x in s, e (f x) :=
e.to_add_equiv.map_sum f s

instance has_coe_to_alg_hom : has_coe (A₁ ≃ₐ[R] A₂) (A₁ →ₐ[R] A₂) :=
  ⟨λ e, { map_one' := e.map_one, map_zero' := e.map_zero, ..e }⟩

@[simp, norm_cast] lemma coe_alg_hom (e : A₁ ≃ₐ[R] A₂) : ((e : A₁ →ₐ[R] A₂) : A₁ → A₂) = e :=
  rfl

lemma injective (e : A₁ ≃ₐ[R] A₂) : function.injective e := e.to_equiv.injective

lemma surjective (e : A₁ ≃ₐ[R] A₂) : function.surjective e := e.to_equiv.surjective

lemma bijective (e : A₁ ≃ₐ[R] A₂) : function.bijective e := e.to_equiv.bijective

instance : has_one (A₁ ≃ₐ[R] A₁) := ⟨{commutes' := λ r, rfl, ..(1 : A₁ ≃+* A₁)}⟩

instance : inhabited (A₁ ≃ₐ[R] A₁) := ⟨1⟩

/-- Algebra equivalences are reflexive. -/
@[refl]
def refl : A₁ ≃ₐ[R] A₁ := 1

@[simp] lemma coe_refl : (@refl R A₁ _ _ _ : A₁ →ₐ[R] A₁) = alg_hom.id R A₁ :=
alg_hom.ext (λ x, rfl)

/-- Algebra equivalences are symmetric. -/
@[symm]
def symm (e : A₁ ≃ₐ[R] A₂) : A₂ ≃ₐ[R] A₁ :=
{ commutes' := λ r, by { rw ←e.to_ring_equiv.symm_apply_apply (algebra_map R A₁ r), congr,
                         change _ = e _, rw e.commutes, },
  ..e.to_ring_equiv.symm, }

@[simp] lemma inv_fun_apply {e : A₁ ≃ₐ[R] A₂} {a : A₂} : e.inv_fun a = e.symm a := rfl

@[simp] lemma symm_symm {e : A₁ ≃ₐ[R] A₂} : e.symm.symm = e :=
by { ext, refl, }

/-- Algebra equivalences are transitive. -/
@[trans]
def trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) : A₁ ≃ₐ[R] A₃ :=
{ commutes' := λ r, show e₂.to_fun (e₁.to_fun _) = _, by rw [e₁.commutes', e₂.commutes'],
  ..(e₁.to_ring_equiv.trans e₂.to_ring_equiv), }

@[simp] lemma apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : ∀ x, e (e.symm x) = x :=
  e.to_equiv.apply_symm_apply

@[simp] lemma symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : ∀ x, e.symm (e x) = x :=
  e.to_equiv.symm_apply_apply

@[simp] lemma trans_apply (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) (x : A₁) :
  (e₁.trans e₂) x = e₂ (e₁ x) := rfl

@[simp] lemma comp_symm (e : A₁ ≃ₐ[R] A₂) :
  alg_hom.comp (e : A₁ →ₐ[R] A₂) ↑e.symm = alg_hom.id R A₂ :=
by { ext, simp }

@[simp] lemma symm_comp (e : A₁ ≃ₐ[R] A₂) :
  alg_hom.comp ↑e.symm (e : A₁ →ₐ[R] A₂) = alg_hom.id R A₁ :=
by { ext, simp }

/-- If an algebra morphism has an inverse, it is a algebra isomorphism. -/
def of_alg_hom (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ : f.comp g = alg_hom.id R A₂) (h₂ : g.comp f = alg_hom.id R A₁) : A₁ ≃ₐ[R] A₂ :=
{ inv_fun   := g,
  left_inv  := alg_hom.ext_iff.1 h₂,
  right_inv := alg_hom.ext_iff.1 h₁,
  ..f }

end alg_equiv

namespace algebra

variables (R : Type u) (S : Type v) (A : Type w)
include R S A

/-- `comap R S A` is a type alias for `A`, and has an R-algebra structure defined on it
  when `algebra R S` and `algebra S A`. If `S` is an `R`-algebra and `A` is an `S`-algebra then
  `algebra.comap.algebra R S A` can be used to provide `A` with a structure of an `R`-algebra.
  Other than that, `algebra.comap` is now deprecated and replcaed with `is_algebra_tower`. -/
/- This is done to avoid a type class search with meta-variables `algebra R ?m_1` and
    `algebra ?m_1 A -/
/- The `nolint` attribute is added because it has unused arguments `R` and `S`, but these are necessary for synthesizing the
     appropriate type classes -/
@[nolint unused_arguments]
def comap : Type w := A

instance comap.inhabited [h : inhabited A] : inhabited (comap R S A) := h
instance comap.semiring [h : semiring A] : semiring (comap R S A) := h
instance comap.ring [h : ring A] : ring (comap R S A) := h
instance comap.comm_semiring [h : comm_semiring A] : comm_semiring (comap R S A) := h
instance comap.comm_ring [h : comm_ring A] : comm_ring (comap R S A) := h

instance comap.algebra' [comm_semiring S] [semiring A] [h : algebra S A] :
  algebra S (comap R S A) := h

/-- Identity homomorphism `A →ₐ[S] comap R S A`. -/
def comap.to_comap [comm_semiring S] [semiring A] [algebra S A] :
  A →ₐ[S] comap R S A := alg_hom.id S A
/-- Identity homomorphism `comap R S A →ₐ[S] A`. -/
def comap.of_comap [comm_semiring S] [semiring A] [algebra S A] :
  comap R S A →ₐ[S] A := alg_hom.id S A

variables [comm_semiring R] [comm_semiring S] [semiring A] [algebra R S] [algebra S A]

/-- `R ⟶ S` induces `S-Alg ⥤ R-Alg` -/
instance comap.algebra : algebra R (comap R S A) :=
{ smul := λ r x, (algebra_map R S r • x : A),
  commutes' := λ r x, algebra.commutes _ _,
  smul_def' := λ _ _, algebra.smul_def _ _,
  .. (algebra_map S A).comp (algebra_map R S) }

/-- Embedding of `S` into `comap R S A`. -/
def to_comap : S →ₐ[R] comap R S A :=
{ commutes' := λ r, rfl,
  .. algebra_map S A }

theorem to_comap_apply (x) : to_comap R S A x = algebra_map S A x := rfl

end algebra

namespace alg_hom

variables {R : Type u} {S : Type v} {A : Type w} {B : Type u₁}
variables [comm_semiring R] [comm_semiring S] [semiring A] [semiring B]
variables [algebra R S] [algebra S A] [algebra S B] (φ : A →ₐ[S] B)
include R

/-- R ⟶ S induces S-Alg ⥤ R-Alg -/
def comap : algebra.comap R S A →ₐ[R] algebra.comap R S B :=
{ commutes' := λ r, φ.commutes (algebra_map R S r)
  ..φ }

end alg_hom

namespace rat

instance algebra_rat {α} [division_ring α] [char_zero α] : algebra ℚ α :=
(rat.cast_hom α).to_algebra' $ λ r x, r.cast_commute x

end rat

/-- A subalgebra is a subring that includes the range of `algebra_map`. -/
structure subalgebra (R : Type u) (A : Type v)
  [comm_semiring R] [semiring A] [algebra R A] : Type v :=
(carrier : subsemiring A)
(algebra_map_mem' : ∀ r, algebra_map R A r ∈ carrier)

namespace subalgebra

variables {R : Type u} {A : Type v} {B : Type w}
variables [comm_semiring R] [semiring A] [algebra R A] [semiring B] [algebra R B]
include R

instance : has_coe (subalgebra R A) (subsemiring A) :=
⟨λ S, S.carrier⟩

instance : has_mem A (subalgebra R A) :=
⟨λ x S, x ∈ (S : set A)⟩

variables {A}
theorem mem_coe {x : A} {s : subalgebra R A} : x ∈ (s : set A) ↔ x ∈ s :=
iff.rfl

@[ext] theorem ext {S T : subalgebra R A}
  (h : ∀ x : A, x ∈ S ↔ x ∈ T) : S = T :=
by cases S; cases T; congr; ext x; exact h x

theorem ext_iff {S T : subalgebra R A} : S = T ↔ ∀ x : A, x ∈ S ↔ x ∈ T :=
⟨λ h x, by rw h, ext⟩

variables (S : subalgebra R A)

theorem algebra_map_mem (r : R) : algebra_map R A r ∈ S :=
S.algebra_map_mem' r

theorem srange_le : (algebra_map R A).srange ≤ S :=
λ x ⟨r, _, hr⟩, hr ▸ S.algebra_map_mem r

theorem range_subset : set.range (algebra_map R A) ⊆ S :=
λ x ⟨r, hr⟩, hr ▸ S.algebra_map_mem r

theorem range_le : set.range (algebra_map R A) ≤ S :=
S.range_subset

theorem one_mem : (1 : A) ∈ S :=
subsemiring.one_mem S

theorem mul_mem {x y : A} (hx : x ∈ S) (hy : y ∈ S) : x * y ∈ S :=
subsemiring.mul_mem S hx hy

theorem smul_mem {x : A} (hx : x ∈ S) (r : R) : r • x ∈ S :=
(algebra.smul_def r x).symm ▸ S.mul_mem (S.algebra_map_mem r) hx

theorem pow_mem {x : A} (hx : x ∈ S) (n : ℕ) : x ^ n ∈ S :=
subsemiring.pow_mem S hx n

theorem zero_mem : (0 : A) ∈ S :=
subsemiring.zero_mem S

theorem add_mem {x y : A} (hx : x ∈ S) (hy : y ∈ S) : x + y ∈ S :=
subsemiring.add_mem S hx hy

theorem neg_mem {R : Type u} {A : Type v} [comm_ring R] [ring A]
  [algebra R A] (S : subalgebra R A) {x : A} (hx : x ∈ S) : -x ∈ S :=
neg_one_smul R x ▸ S.smul_mem hx _

theorem sub_mem {R : Type u} {A : Type v} [comm_ring R] [ring A]
  [algebra R A] (S : subalgebra R A) {x y : A} (hx : x ∈ S) (hy : y ∈ S) : x - y ∈ S :=
S.add_mem hx $ S.neg_mem hy

theorem nsmul_mem {x : A} (hx : x ∈ S) (n : ℕ) : n •ℕ x ∈ S :=
subsemiring.nsmul_mem S hx n

theorem gsmul_mem {R : Type u} {A : Type v} [comm_ring R] [ring A]
  [algebra R A] (S : subalgebra R A) {x : A} (hx : x ∈ S) (n : ℤ) : n •ℤ x ∈ S :=
int.cases_on n (λ i, S.nsmul_mem hx i) (λ i, S.neg_mem $ S.nsmul_mem hx _)

theorem coe_nat_mem (n : ℕ) : (n : A) ∈ S :=
subsemiring.coe_nat_mem S n

theorem coe_int_mem {R : Type u} {A : Type v} [comm_ring R] [ring A]
  [algebra R A] (S : subalgebra R A) (n : ℤ) : (n : A) ∈ S :=
int.cases_on n (λ i, S.coe_nat_mem i) (λ i, S.neg_mem $ S.coe_nat_mem $ i + 1)

theorem list_prod_mem {L : list A} (h : ∀ x ∈ L, x ∈ S) : L.prod ∈ S :=
subsemiring.list_prod_mem S h

theorem list_sum_mem {L : list A} (h : ∀ x ∈ L, x ∈ S) : L.sum ∈ S :=
subsemiring.list_sum_mem S h

theorem multiset_prod_mem {R : Type u} {A : Type v} [comm_semiring R] [comm_semiring A]
  [algebra R A] (S : subalgebra R A) {m : multiset A} (h : ∀ x ∈ m, x ∈ S) : m.prod ∈ S :=
subsemiring.multiset_prod_mem S m h

theorem multiset_sum_mem {m : multiset A} (h : ∀ x ∈ m, x ∈ S) : m.sum ∈ S :=
subsemiring.multiset_sum_mem S m h

theorem prod_mem {R : Type u} {A : Type v} [comm_semiring R] [comm_semiring A]
  [algebra R A] (S : subalgebra R A) {ι : Type w} {t : finset ι} {f : ι → A}
  (h : ∀ x ∈ t, f x ∈ S) : ∏ x in t, f x ∈ S :=
subsemiring.prod_mem S h

theorem sum_mem {ι : Type w} {t : finset ι} {f : ι → A}
  (h : ∀ x ∈ t, f x ∈ S) : ∑ x in t, f x ∈ S :=
subsemiring.sum_mem S h

instance {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
  (S : subalgebra R A) : is_add_submonoid (S : set A) :=
{ zero_mem := S.zero_mem,
  add_mem := λ _ _, S.add_mem }

instance {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
  (S : subalgebra R A) : is_submonoid (S : set A) :=
{ one_mem := S.one_mem,
  mul_mem := λ _ _, S.mul_mem }

instance {R : Type u} {A : Type v} [comm_ring R] [ring A] [algebra R A] (S : subalgebra R A) :
  is_subring (S : set A) :=
{ neg_mem := λ _, S.neg_mem }

instance : inhabited S := ⟨0⟩
instance (R : Type u) (A : Type v) [comm_semiring R] [semiring A]
  [algebra R A] (S : subalgebra R A) : semiring S := subsemiring.to_semiring S
instance (R : Type u) (A : Type v) [comm_semiring R] [comm_semiring A]
  [algebra R A] (S : subalgebra R A) : comm_semiring S := subsemiring.to_comm_semiring S
instance (R : Type u) (A : Type v) [comm_ring R] [ring A]
  [algebra R A] (S : subalgebra R A) : ring S := @@subtype.ring _ S.is_subring
instance (R : Type u) (A : Type v) [comm_ring R] [comm_ring A]
  [algebra R A] (S : subalgebra R A) : comm_ring S := @@subtype.comm_ring _ S.is_subring

instance algebra : algebra R S :=
{ smul := λ (c:R) x, ⟨c • x.1, S.smul_mem x.2 c⟩,
  commutes' := λ c x, subtype.eq $ algebra.commutes _ _,
  smul_def' := λ c x, subtype.eq $ algebra.smul_def _ _,
  .. (algebra_map R A).cod_srestrict S $ λ x, S.range_le ⟨x, rfl⟩ }

instance to_algebra {R : Type u} {A : Type v} [comm_semiring R] [comm_semiring A]
  [algebra R A] (S : subalgebra R A) : algebra S A :=
algebra.of_subsemiring _

-- todo: standardize on the names these morphisms
-- compare with submodule.subtype

/-- Embedding of a subalgebra into the algebra. -/
def val : S →ₐ[R] A :=
by refine_struct { to_fun := (coe : S → A) }; intros; refl

@[simp]
lemma val_apply (x : S) : S.val x = (x : A) := rfl

/-- Convert a `subalgebra` to `submodule` -/
def to_submodule : submodule R A :=
{ carrier := S,
  zero_mem' := (0:S).2,
  add_mem' := λ x y hx hy, (⟨x, hx⟩ + ⟨y, hy⟩ : S).2,
  smul_mem' := λ c x hx, (algebra.smul_def c x).symm ▸
    (⟨algebra_map R A c, S.range_le ⟨c, rfl⟩⟩ * ⟨x, hx⟩:S).2 }

instance coe_to_submodule : has_coe (subalgebra R A) (submodule R A) :=
⟨to_submodule⟩

instance to_submodule.is_subring {R : Type u} {A : Type v} [comm_ring R] [ring A] [algebra R A]
  (S : subalgebra R A) : is_subring ((S : submodule R A) : set A) := S.is_subring

@[simp] lemma mem_to_submodule {x} : x ∈ (S : submodule R A) ↔ x ∈ S := iff.rfl

theorem to_submodule_injective {S U : subalgebra R A} (h : (S : submodule R A) = U) : S = U :=
ext $ λ x, by rw [← mem_to_submodule, ← mem_to_submodule, h]

theorem to_submodule_inj {S U : subalgebra R A} : (S : submodule R A) = U ↔ S = U :=
⟨to_submodule_injective, congr_arg _⟩

instance : partial_order (subalgebra R A) :=
{ le := λ S T, (S : set A) ⊆ (T : set A),
  le_refl := λ S, set.subset.refl S,
  le_trans := λ _ _ _, set.subset.trans,
  le_antisymm := λ S T hst hts, ext $ λ x, ⟨@hst x, @hts x⟩ }

/-- Reinterpret an `S`-subalgebra as an `R`-subalgebra in `comap R S A`. -/
def comap {R : Type u} {S : Type v} {A : Type w}
  [comm_semiring R] [comm_semiring S] [semiring A] [algebra R S] [algebra S A]
  (iSB : subalgebra S A) : subalgebra R (algebra.comap R S A) :=
{ carrier := (iSB : subsemiring A),
  algebra_map_mem' := λ r, iSB.algebra_map_mem (algebra_map R S r) }

/-- If `S` is an `R`-subalgebra of `A` and `T` is an `S`-subalgebra of `A`,
then `T` is an `R`-subalgebra of `A`. -/
def under {R : Type u} {A : Type v} [comm_semiring R] [comm_semiring A]
  {i : algebra R A} (S : subalgebra R A)
  (T : subalgebra S A) : subalgebra R A :=
{ carrier := T,
  algebra_map_mem' := λ r, T.algebra_map_mem ⟨algebra_map R A r, S.algebra_map_mem r⟩ }

/-- Transport a subalgebra via an algebra homomorphism. -/
def map (S : subalgebra R A) (f : A →ₐ[R] B) : subalgebra R B :=
{ carrier := subsemiring.map (f : A →+* B) S,
  algebra_map_mem' := λ r, f.commutes r ▸ set.mem_image_of_mem _ (S.algebra_map_mem r) }

/-- Preimage of a subalgebra under an algebra homomorphism. -/
def comap' (S : subalgebra R B) (f : A →ₐ[R] B) : subalgebra R A :=
{ carrier := subsemiring.comap (f : A →+* B) S,
  algebra_map_mem' := λ r, show f (algebra_map R A r) ∈ S,
    from (f.commutes r).symm ▸ S.algebra_map_mem r }

theorem map_le {S : subalgebra R A} {f : A →ₐ[R] B} {U : subalgebra R B} :
  map S f ≤ U ↔ S ≤ comap' U f :=
set.image_subset_iff

end subalgebra

namespace alg_hom

variables {R : Type u} {A : Type v} {B : Type w}
variables [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B]
variables (φ : A →ₐ[R] B)

/-- Range of an `alg_hom` as a subalgebra. -/
protected def range (φ : A →ₐ[R] B) : subalgebra R B :=
{ carrier :=
  { carrier := set.range φ,
    one_mem' := ⟨1, φ.map_one⟩,
    mul_mem' := λ _ _ ⟨x, hx⟩ ⟨y, hy⟩, ⟨x * y, by rw [φ.map_mul, hx, hy]⟩,
    zero_mem' := ⟨0, φ.map_zero⟩,
    add_mem' := λ _ _ ⟨x, hx⟩ ⟨y, hy⟩, ⟨x + y, by rw [φ.map_add, hx, hy]⟩ },
  algebra_map_mem' := λ r, ⟨algebra_map R A r, φ.commutes r⟩ }

end alg_hom

namespace algebra

variables (R : Type u) (A : Type v)

variables [comm_semiring R] [semiring A] [algebra R A]

/-- `algebra_map` as an `alg_hom`. -/
def of_id : R →ₐ[R] A :=
{ commutes' := λ _, rfl, .. algebra_map R A }
variables {R}

theorem of_id_apply (r) : of_id R A r = algebra_map R A r := rfl

end algebra

namespace algebra

variables (R : Type u) {A : Type v} {B : Type w}
variables [comm_semiring R] [semiring A] [algebra R A] [semiring B] [algebra R B]

/-- The minimal subalgebra that includes `s`. -/
def adjoin (s : set A) : subalgebra R A :=
{ carrier := subsemiring.closure (set.range (algebra_map R A) ∪ s),
  algebra_map_mem' := λ r, subsemiring.subset_closure $ or.inl ⟨r, rfl⟩ }
variables {R}

protected lemma gc : galois_connection (adjoin R : set A → subalgebra R A) coe :=
λ s S, ⟨λ H, le_trans (le_trans (set.subset_union_right _ _) subsemiring.subset_closure) H,
λ H, subsemiring.closure_le.2 $ set.union_subset S.range_subset H⟩

/-- Galois insertion between `adjoin` and `coe`. -/
protected def gi : galois_insertion (adjoin R : set A → subalgebra R A) coe :=
{ choice := λ s hs, adjoin R s,
  gc := algebra.gc,
  le_l_u := λ S, (algebra.gc (S : set A) (adjoin R S)).1 $ le_refl _,
  choice_eq := λ _ _, rfl }

instance : complete_lattice (subalgebra R A) :=
galois_insertion.lift_complete_lattice algebra.gi

instance : inhabited (subalgebra R A) := ⟨⊥⟩

theorem mem_bot {x : A} : x ∈ (⊥ : subalgebra R A) ↔ x ∈ set.range (algebra_map R A) :=
suffices (⊥ : subalgebra R A) = (of_id R A).range, by rw this; refl,
le_antisymm bot_le $ subalgebra.range_le _

theorem mem_top {x : A} : x ∈ (⊤ : subalgebra R A) :=
subsemiring.subset_closure $ or.inr trivial

theorem eq_top_iff {S : subalgebra R A} :
  S = ⊤ ↔ ∀ x : A, x ∈ S :=
⟨λ h x, by rw h; exact mem_top, λ h, by ext x; exact ⟨λ _, mem_top, λ _, h x⟩⟩

@[simp] theorem map_top (f : A →ₐ[R] B) : subalgebra.map (⊤ : subalgebra R A) f = f.range :=
subalgebra.ext $ λ x, ⟨λ ⟨y, _, hy⟩, ⟨y, hy⟩, λ ⟨y, hy⟩, ⟨y, algebra.mem_top, hy⟩⟩

@[simp] theorem map_bot (f : A →ₐ[R] B) : subalgebra.map (⊥ : subalgebra R A) f = ⊥ :=
eq_bot_iff.2 $ λ x ⟨y, hy, hfy⟩, let ⟨r, hr⟩ := mem_bot.1 hy in subalgebra.range_le _
⟨r, by rwa [← f.commutes, hr]⟩

@[simp] theorem comap_top (f : A →ₐ[R] B) : subalgebra.comap' (⊤ : subalgebra R B) f = ⊤ :=
eq_top_iff.2 $ λ x, mem_top

/-- `alg_hom` to `⊤ : subalgebra R A`. -/
def to_top : A →ₐ[R] (⊤ : subalgebra R A) :=
by refine_struct { to_fun := λ x, (⟨x, mem_top⟩ : (⊤ : subalgebra R A)) }; intros; refl

end algebra

section nat

variables (R : Type*) [semiring R]

/-- Reinterpret a `ring_hom` as an `ℕ`-algebra homomorphism. -/
def alg_hom_nat
  {R : Type u} [semiring R] [algebra ℕ R]
  {S : Type v} [semiring S] [algebra ℕ S]
  (f : R →+* S) : R →ₐ[ℕ] S :=
{ commutes' := λ i, show f _ = _, by simp, .. f }

/-- Semiring ⥤ ℕ-Alg -/
instance algebra_nat : algebra ℕ R :=
{ commutes' := nat.cast_commute,
  smul_def' := λ _ _, nsmul_eq_mul _ _,
  .. nat.cast_ring_hom R }

variables {R}
/-- A subsemiring is a `ℕ`-subalgebra. -/
def subalgebra_of_subsemiring (S : subsemiring R) : subalgebra ℕ R :=
{ carrier := S,
  algebra_map_mem' := λ i, S.coe_nat_mem i }

@[simp] lemma mem_subalgebra_of_subsemiring {x : R} {S : subsemiring R} :
  x ∈ subalgebra_of_subsemiring S ↔ x ∈ S :=
iff.rfl

section span_nat
open submodule

lemma span_nat_eq_add_group_closure (s : set R) :
  (span ℕ s).to_add_submonoid = add_submonoid.closure s :=
eq.symm $ add_submonoid.closure_eq_of_le subset_span $ λ x hx, span_induction hx
  (λ x hx, add_submonoid.subset_closure hx) (add_submonoid.zero_mem _)
  (λ _ _, add_submonoid.add_mem _) (λ _ _ _, add_submonoid.nsmul_mem _ ‹_› _)

@[simp] lemma span_nat_eq (s : add_submonoid R) : (span ℕ (s : set R)).to_add_submonoid = s :=
by rw [span_nat_eq_add_group_closure, s.closure_eq]

end span_nat

end nat

section int

variables (R : Type*) [ring R]

/-- Reinterpret a `ring_hom` as a `ℤ`-algebra homomorphism. -/
def alg_hom_int
  {R : Type u} [comm_ring R] [algebra ℤ R]
  {S : Type v} [comm_ring S] [algebra ℤ S]
  (f : R →+* S) : R →ₐ[ℤ] S :=
{ commutes' := λ i, show f _ = _, by simp, .. f }

/-- Ring ⥤ ℤ-Alg -/
instance algebra_int : algebra ℤ R :=
{ commutes' := int.cast_commute,
  smul_def' := λ _ _, gsmul_eq_mul _ _,
  .. int.cast_ring_hom R }

/--
Promote a ring homomorphisms to a `ℤ`-algebra homomorphism.
-/
def ring_hom.to_int_alg_hom {R S : Type*} [ring R] [ring S] (f : R →+* S) : R →ₐ[ℤ] S :=
{ commutes' := λ n, by simp,
  .. f }

variables {R}
/-- A subring is a `ℤ`-subalgebra. -/
def subalgebra_of_subring (S : set R) [is_subring S] : subalgebra ℤ R :=
{ carrier :=
  { carrier := S,
    one_mem' := is_submonoid.one_mem,
    mul_mem' := λ _ _, is_submonoid.mul_mem,
    zero_mem' := is_add_submonoid.zero_mem,
    add_mem' := λ _ _, is_add_submonoid.add_mem, },
  algebra_map_mem' := λ i, int.induction_on i (show (0 : R) ∈ S, from is_add_submonoid.zero_mem)
    (λ i ih, show (i + 1 : R) ∈ S, from is_add_submonoid.add_mem ih is_submonoid.one_mem)
    (λ i ih, show ((-i - 1 : ℤ) : R) ∈ S, by { rw [int.cast_sub, int.cast_one],
      exact is_add_subgroup.sub_mem S _ _ ih is_submonoid.one_mem }) }


section
variables {S : Type*} [ring S]

instance int_algebra_subsingleton : subsingleton (algebra ℤ S) :=
⟨λ P Q, by { ext, simp, }⟩
end

section
variables {S : Type*} [semiring S]

instance nat_algebra_subsingleton : subsingleton (algebra ℕ S) :=
⟨λ P Q, by { ext, simp, }⟩
end

@[simp] lemma mem_subalgebra_of_subring {x : R} {S : set R} [is_subring S] :
  x ∈ subalgebra_of_subring S ↔ x ∈ S :=
iff.rfl

section span_int
open submodule

lemma span_int_eq_add_group_closure (s : set R) :
  (span ℤ s).to_add_subgroup = add_subgroup.closure s :=
eq.symm $ add_subgroup.closure_eq_of_le _ subset_span $ λ x hx, span_induction hx
  (λ x hx, add_subgroup.subset_closure hx) (add_subgroup.zero_mem _)
  (λ _ _, add_subgroup.add_mem _) (λ _ _ _, add_subgroup.gsmul_mem _ ‹_› _)

@[simp] lemma span_int_eq (s : add_subgroup R) : (span ℤ (s : set R)).to_add_subgroup = s :=
by rw [span_int_eq_add_group_closure, s.closure_eq]

end span_int

end int

section restrict_scalars
/- In this section, we describe restriction of scalars: if `S` is an algebra over `R`, then
`S`-modules are also `R`-modules. -/

variables (R : Type*) [comm_ring R] (S : Type*) [ring S] [algebra R S]
variables (E : Type*) [add_comm_group E] [module S E] {F : Type*} [add_comm_group F] [module S F]

/--
When `E` is a module over a ring `S`, and `S` is an algebra over `R`, then `E` inherits a
module structure over `R`, called `module.restrict_scalars' R S E`.
We do not register this as an instance as `S` can not be inferred.
-/
def module.restrict_scalars' : module R E :=
{ smul      := λ c x, (algebra_map R S c) • x,
  one_smul  := by simp,
  mul_smul  := by simp [mul_smul],
  smul_add  := by simp [smul_add],
  smul_zero := by simp [smul_zero],
  add_smul  := by simp [add_smul],
  zero_smul := by simp [zero_smul] }

/--
When `E` is a module over a ring `S`, and `S` is an algebra over `R`, then `E` inherits a
module structure over `R`, provided as a type synonym `module.restrict_scalars R S E := E`.
-/
@[nolint unused_arguments]
def module.restrict_scalars (R : Type*) (S : Type*) (E : Type*) : Type* := E

instance (R : Type*) (S : Type*) (E : Type*) [I : inhabited E] :
  inhabited (module.restrict_scalars R S E) := I

instance (R : Type*) (S : Type*) (E : Type*) [I : add_comm_group E] :
  add_comm_group (module.restrict_scalars R S E) := I

instance : module R (module.restrict_scalars R S E) :=
(module.restrict_scalars' R S E : module R E)

lemma module.restrict_scalars_smul_def (c : R) (x : module.restrict_scalars R S E) :
  c • x = ((algebra_map R S c) • x : E) := rfl

/--
`module.restrict_scalars R S S` is `R`-linearly equivalent to the original algebra `S`.

Unfortunately these structures are not generally definitionally equal:
the `R`-module structure on `S` is part of the data of `S`,
while the `R`-module structure on `module.restrict_scalars R S S`
comes from the ring homomorphism `R →+* S`, which is a separate part of the data of `S`.
The field `algebra.smul_def'` gives the equation we need here.
-/
def algebra.restrict_scalars_equiv :
  (module.restrict_scalars R S S) ≃ₗ[R] S :=
{ to_fun := λ s, s,
  inv_fun := λ s, s,
  left_inv := λ s, rfl,
  right_inv := λ s, rfl,
  map_add' := λ x y, rfl,
  map_smul' := λ c x, (algebra.smul_def' _ _).symm, }

@[simp]
lemma algebra.restrict_scalars_equiv_apply (s : S) :
  algebra.restrict_scalars_equiv R S s = s := rfl
@[simp]
lemma algebra.restrict_scalars_equiv_symm_apply (s : S) :
  (algebra.restrict_scalars_equiv R S).symm s = s := rfl

variables {S E}

open module

/--
`V.restrict_scalars R` is the `R`-submodule of the `R`-module given by restriction of scalars,
corresponding to `V`, an `S`-submodule of the original `S`-module.
-/
@[simps]
def submodule.restrict_scalars (V : submodule S E) : submodule R (restrict_scalars R S E) :=
{ carrier := V.carrier,
  zero_mem' := V.zero_mem,
  smul_mem' := λ c e h, V.smul_mem _ h,
  add_mem' := λ x y hx hy, V.add_mem hx hy, }

@[simp]
lemma submodule.restrict_scalars_mem (V : submodule S E) (e : E) :
  e ∈ V.restrict_scalars R ↔ e ∈ V :=
iff.refl _

@[simp]
lemma submodule.restrict_scalars_bot :
  submodule.restrict_scalars R (⊥ : submodule S E) = ⊥ :=
rfl

@[simp]
lemma submodule.restrict_scalars_top :
  submodule.restrict_scalars R (⊤ : submodule S E) = ⊤ :=
rfl

/-- The `R`-linear map induced by an `S`-linear map when `S` is an algebra over `R`. -/
def linear_map.restrict_scalars (f : E →ₗ[S] F) :
  (restrict_scalars R S E) →ₗ[R] (restrict_scalars R S F) :=
{ to_fun := f.to_fun,
  map_add' := λx y, f.map_add x y,
  map_smul' := λc x, f.map_smul (algebra_map R S c) x }

@[simp, norm_cast squash] lemma linear_map.coe_restrict_scalars_eq_coe (f : E →ₗ[S] F) :
  (f.restrict_scalars R : E → F) = f := rfl

@[simp]
lemma restrict_scalars_ker (f : E →ₗ[S] F) :
  (f.restrict_scalars R).ker = submodule.restrict_scalars R f.ker :=
rfl

variables (𝕜 : Type*) [field 𝕜] (𝕜' : Type*) [field 𝕜'] [algebra 𝕜 𝕜']
variables (W : Type*) [add_comm_group W] [vector_space 𝕜' W]

/--
`V.restrict_scalars 𝕜` is the `𝕜`-subspace of the `𝕜`-vector space given by restriction of scalars,
corresponding to `V`, a `𝕜'`-subspace of the original `𝕜'`-vector space.
-/
def subspace.restrict_scalars (V : subspace 𝕜' W) : subspace 𝕜 (restrict_scalars 𝕜 𝕜' W) :=
{ ..submodule.restrict_scalars 𝕜 (V : submodule 𝕜' W) }

end restrict_scalars


/-!
When `V` and `W` are `S`-modules, for some `R`-algebra `S`,
the collection of `S`-linear maps from `V` to `W` forms an `R`-module.
(But not generally an `S`-module, because `S` may be non-commutative.)
-/
section module_of_linear_maps

variables (R : Type*) [comm_ring R] (S : Type*) [ring S] [algebra R S]
  (V : Type*) [add_comm_group V] [module S V]
  (W : Type*) [add_comm_group W] [module S W]

/--
For `r : R`, and `f : V →ₗ[S] W` (where `S` is an `R`-algebra) we define
`(r • f) v = f (r • v)`.
-/
def linear_map_algebra_has_scalar : has_scalar R (V →ₗ[S] W) :=
{ smul := λ r f,
  { to_fun := λ v, f ((algebra_map R S r) • v),
    map_add' := λ x y, by simp [smul_add],
    map_smul' := λ s v, by simp [smul_smul, algebra.commutes], } }

local attribute [instance] linear_map_algebra_has_scalar

/-- The `R`-module structure on `S`-linear maps, for `S` an `R`-algebra. -/
def linear_map_algebra_module : module R (V →ₗ[S] W) :=
{ one_smul := λ f, begin ext v, dsimp [(•)], simp, end,
  mul_smul := λ r r' f,
  begin
    ext v, dsimp [(•)],
    rw [linear_map.map_smul, linear_map.map_smul, linear_map.map_smul, ring_hom.map_mul,
        smul_smul, algebra.commutes],
  end,
  smul_zero := λ r, by { ext v, dsimp [(•)], refl, },
  smul_add := λ r f g, by { ext v, dsimp [(•)], simp [linear_map.map_add], },
  zero_smul := λ f, by { ext v, dsimp [(•)], simp, },
  add_smul := λ r r' f, by { ext v, dsimp [(•)], simp [add_smul], }, }

local attribute [instance] linear_map_algebra_module

variables {R S V W}
@[simp]
lemma linear_map_algebra_module.smul_apply (c : R) (f : V →ₗ[S] W) (v : V) :
  (c • f) v = (c • (f v) : module.restrict_scalars R S W) :=
begin
  erw [linear_map.map_smul],
  refl,
end

end module_of_linear_maps

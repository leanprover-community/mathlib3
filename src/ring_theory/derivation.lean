/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Andrew Yang
-/

import ring_theory.adjoin.basic
import algebra.lie.of_associative
import ring_theory.tensor_product

/-!
# Derivations

This file defines derivation. A derivation `D` from the `R`-algebra `A` to the `A`-module `M` is an
`R`-linear map that satisfy the Leibniz rule `D (a * b) = a * D b + D a * b`.

## Notation

The notation `⁅D1, D2⁆` is used for the commutator of two derivations.

TODO: this file is just a stub to go on with some PRs in the geometry section. It only
implements the definition of derivations in commutative algebra. This will soon change: as soon
as bimodules will be there in mathlib I will change this file to take into account the
non-commutative case. Any development on the theory of derivations is discouraged until the
definitive definition of derivation will be implemented.
-/

open algebra
open_locale big_operators

/-- `D : derivation R A M` is an `R`-linear map from `A` to `M` that satisfies the `leibniz`
equality. We also require that `D 1 = 0`. See `derivation.mk'` for a constructor that deduces this
assumption from the Leibniz rule when `M` is cancellative.

TODO: update this when bimodules are defined. -/
@[protect_proj]
structure derivation (R : Type*) (A : Type*) [comm_semiring R] [comm_semiring A]
  [algebra R A] (M : Type*) [add_comm_monoid M] [module A M] [module R M]
  extends A →ₗ[R] M :=
(map_one_eq_zero' : to_linear_map 1 = 0)
(leibniz' (a b : A) : to_linear_map (a * b) = a • to_linear_map b + b • to_linear_map a)

/-- The `linear_map` underlying a `derivation`. -/
add_decl_doc derivation.to_linear_map

namespace derivation

section

variables {R : Type*} [comm_semiring R]
variables {A : Type*} [comm_semiring A] [algebra R A]
variables {M : Type*} [add_comm_monoid M] [module A M] [module R M]
variables (D : derivation R A M) {D1 D2 : derivation R A M} (r : R) (a b : A)

instance : add_monoid_hom_class (derivation R A M) A M :=
{ coe := λ D, D.to_fun,
  coe_injective' := λ D1 D2 h, by { cases D1, cases D2, congr, exact fun_like.coe_injective h },
  map_add := λ D, D.to_linear_map.map_add',
  map_zero := λ D, D.to_linear_map.map_zero }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (derivation R A M) (λ _, A → M) := ⟨λ D, D.to_linear_map.to_fun⟩

-- Not a simp lemma because it can be proved via `coe_fn_coe` + `to_linear_map_eq_coe`
lemma to_fun_eq_coe : D.to_fun = ⇑D := rfl

instance has_coe_to_linear_map : has_coe (derivation R A M) (A →ₗ[R] M) :=
⟨λ D, D.to_linear_map⟩

@[simp] lemma to_linear_map_eq_coe : D.to_linear_map = D := rfl

@[simp] lemma mk_coe (f : A →ₗ[R] M) (h₁ h₂) :
  ((⟨f, h₁, h₂⟩ : derivation R A M) : A → M) = f := rfl

@[simp, norm_cast]
lemma coe_fn_coe (f : derivation R A M) : ⇑(f : A →ₗ[R] M) = f := rfl

lemma coe_injective : @function.injective (derivation R A M) (A → M) coe_fn :=
fun_like.coe_injective

@[ext] theorem ext (H : ∀ a, D1 a = D2 a) : D1 = D2 :=
fun_like.ext _ _ H

lemma congr_fun (h : D1 = D2) (a : A) : D1 a = D2 a := fun_like.congr_fun h a

protected lemma map_add : D (a + b) = D a + D b := map_add D a b
protected lemma map_zero : D 0 = 0 := map_zero D
@[simp] lemma map_smul : D (r • a) = r • D a := D.to_linear_map.map_smul r a
@[simp] lemma leibniz : D (a * b) = a • D b + b • D a := D.leibniz' _ _

lemma map_sum {ι : Type*} (s : finset ι) (f : ι → A) : D (∑ i in s, f i) = ∑ i in s, D (f i) :=
D.to_linear_map.map_sum

@[simp, priority 900] lemma map_smul_of_tower {S : Type*} [has_smul S A] [has_smul S M]
  [linear_map.compatible_smul A M S R] (D : derivation R A M) (r : S) (a : A) :
  D (r • a) = r • D a :=
D.to_linear_map.map_smul_of_tower r a

@[simp] lemma map_one_eq_zero : D 1 = 0 := D.map_one_eq_zero'

@[simp] lemma map_algebra_map : D (algebra_map R A r) = 0 :=
by rw [←mul_one r, ring_hom.map_mul, ring_hom.map_one, ←smul_def, map_smul, map_one_eq_zero,
  smul_zero]

@[simp] lemma map_coe_nat (n : ℕ) : D (n : A) = 0 :=
by rw [← nsmul_one, D.map_smul_of_tower n, map_one_eq_zero, smul_zero]

@[simp] lemma leibniz_pow (n : ℕ) : D (a ^ n) = n • a ^ (n - 1) • D a :=
begin
  induction n with n ihn,
  { rw [pow_zero, map_one_eq_zero, zero_smul] },
  { rcases (zero_le n).eq_or_lt with (rfl|hpos),
    { rw [pow_one, one_smul, pow_zero, one_smul] },
    { have : a * a ^ (n - 1) = a ^ n, by rw [← pow_succ, nat.sub_add_cancel hpos],
      simp only [pow_succ, leibniz, ihn, smul_comm a n, smul_smul a, add_smul, this,
        nat.succ_eq_add_one, nat.add_succ_sub_one, add_zero, one_nsmul] } }
end

lemma eq_on_adjoin {s : set A} (h : set.eq_on D1 D2 s) : set.eq_on D1 D2 (adjoin R s) :=
λ x hx, algebra.adjoin_induction hx h
  (λ r, (D1.map_algebra_map r).trans (D2.map_algebra_map r).symm)
  (λ x y hx hy, by simp only [map_add, *])
  (λ x y hx hy, by simp only [leibniz, *])

/-- If adjoin of a set is the whole algebra, then any two derivations equal on this set are equal
on the whole algebra. -/
lemma ext_of_adjoin_eq_top (s : set A) (hs : adjoin R s = ⊤) (h : set.eq_on D1 D2 s) : D1 = D2 :=
ext $ λ a, eq_on_adjoin h $ hs.symm ▸ trivial

/- Data typeclasses -/

instance : has_zero (derivation R A M) :=
⟨{ to_linear_map := 0,
   map_one_eq_zero' := rfl,
   leibniz' := λ a b, by simp only [add_zero, linear_map.zero_apply, smul_zero] }⟩

@[simp] lemma coe_zero : ⇑(0 : derivation R A M) = 0 := rfl
@[simp] lemma coe_zero_linear_map : ↑(0 : derivation R A M) = (0 : A →ₗ[R] M) := rfl
lemma zero_apply (a : A) : (0 : derivation R A M) a = 0 := rfl

instance : has_add (derivation R A M) :=
⟨λ D1 D2,
  { to_linear_map := D1 + D2,
    map_one_eq_zero' := by simp,
    leibniz' := λ a b, by simp only [leibniz, linear_map.add_apply,
      coe_fn_coe, smul_add, add_add_add_comm] }⟩

@[simp] lemma coe_add (D1 D2 : derivation R A M) : ⇑(D1 + D2) = D1 + D2 := rfl
@[simp] lemma coe_add_linear_map (D1 D2 : derivation R A M) : ↑(D1 + D2) = (D1 + D2 : A →ₗ[R] M) :=
rfl
lemma add_apply : (D1 + D2) a = D1 a + D2 a := rfl

instance : inhabited (derivation R A M) := ⟨0⟩

section scalar

variables {S : Type*} [monoid S] [distrib_mul_action S M] [smul_comm_class R S M]
  [smul_comm_class S A M]

@[priority 100]
instance : has_smul S (derivation R A M) :=
⟨λ r D,
  { to_linear_map := r • D,
    map_one_eq_zero' := by rw [linear_map.smul_apply, coe_fn_coe, D.map_one_eq_zero, smul_zero],
    leibniz' := λ a b, by simp only [linear_map.smul_apply, coe_fn_coe, leibniz, smul_add,
      smul_comm r] }⟩

@[simp] lemma coe_smul (r : S) (D : derivation R A M) : ⇑(r • D) = r • D := rfl
@[simp] lemma coe_smul_linear_map (r : S) (D : derivation R A M) :
  ↑(r • D) = (r • D : A →ₗ[R] M) := rfl
lemma smul_apply (r : S) (D : derivation R A M) : (r • D) a = r • D a := rfl

instance : add_comm_monoid (derivation R A M) :=
coe_injective.add_comm_monoid _ coe_zero coe_add (λ _ _, rfl)

/-- `coe_fn` as an `add_monoid_hom`. -/
def coe_fn_add_monoid_hom : derivation R A M →+ (A → M) :=
{ to_fun := coe_fn, map_zero' := coe_zero, map_add' := coe_add }

@[priority 100]
instance : distrib_mul_action S (derivation R A M) :=
function.injective.distrib_mul_action coe_fn_add_monoid_hom coe_injective coe_smul

instance [distrib_mul_action Sᵐᵒᵖ M] [is_central_scalar S M] :
  is_central_scalar S (derivation R A M) :=
{ op_smul_eq_smul := λ _ _, ext $ λ _, op_smul_eq_smul _ _}

end scalar

@[priority 100]
instance {S : Type*} [semiring S] [module S M] [smul_comm_class R S M] [smul_comm_class S A M] :
  module S (derivation R A M) :=
function.injective.module S coe_fn_add_monoid_hom coe_injective coe_smul

instance [is_scalar_tower R A M] : is_scalar_tower R A (derivation R A M) :=
⟨λ x y z, ext (λ a, smul_assoc _ _ _)⟩

section push_forward

variables {N : Type*} [add_comm_monoid N] [module A N] [module R N] [is_scalar_tower R A M]
  [is_scalar_tower R A N]
variables (f : M →ₗ[A] N)

/-- We can push forward derivations using linear maps, i.e., the composition of a derivation with a
linear map is a derivation. Furthermore, this operation is linear on the spaces of derivations. -/
def _root_.linear_map.comp_der : derivation R A M →ₗ[R] derivation R A N :=
{ to_fun    := λ D,
  { to_linear_map := (f : M →ₗ[R] N).comp (D : A →ₗ[R] M),
    map_one_eq_zero' := by simp only [linear_map.comp_apply, coe_fn_coe, map_one_eq_zero, map_zero],
    leibniz'  := λ a b, by simp only [coe_fn_coe, linear_map.comp_apply, linear_map.map_add,
      leibniz, linear_map.coe_coe_is_scalar_tower, linear_map.map_smul] },
  map_add'  := λ D₁ D₂, by { ext, exact linear_map.map_add _ _ _, },
  map_smul' := λ r D, by { ext, exact linear_map.map_smul _ _ _, }, }

@[simp] lemma coe_to_linear_map_comp :
  (f.comp_der D : A →ₗ[R] N) = (f : M →ₗ[R] N).comp (D : A →ₗ[R] M) :=
rfl

@[simp] lemma coe_comp :
  (f.comp_der D : A → N) = (f : M →ₗ[R] N).comp (D : A →ₗ[R] M) :=
rfl

/-- The composition of a derivation with a linear map as a bilinear map -/
def llcomp : (M →ₗ[A] N) →ₗ[A] derivation R A M →ₗ[R] derivation R A N :=
{ to_fun := λ f, f.comp_der,
  map_add' := λ f₁ f₂, by { ext, refl },
  map_smul' := λ r D, by { ext, refl } }

end push_forward

end

section cancel

variables {R : Type*} [comm_semiring R] {A : Type*} [comm_semiring A] [algebra R A]
  {M : Type*} [add_cancel_comm_monoid M] [module R M] [module A M]

/-- Define `derivation R A M` from a linear map when `M` is cancellative by verifying the Leibniz
rule. -/
def mk' (D : A →ₗ[R] M) (h : ∀ a b, D (a * b) = a • D b + b • D a) : derivation R A M :=
{ to_linear_map := D,
  map_one_eq_zero' := add_right_eq_self.1 $ by simpa only [one_smul, one_mul] using (h 1 1).symm,
  leibniz' := h }

@[simp] lemma coe_mk' (D : A →ₗ[R] M) (h) : ⇑(mk' D h) = D := rfl
@[simp] lemma coe_mk'_linear_map (D : A →ₗ[R] M) (h) : (mk' D h : A →ₗ[R] M) = D := rfl

end cancel

section

variables {R : Type*} [comm_ring R]
variables {A : Type*} [comm_ring A] [algebra R A]

section

variables {M : Type*} [add_comm_group M] [module A M] [module R M]
variables (D : derivation R A M) {D1 D2 : derivation R A M} (r : R) (a b : A)

protected lemma map_neg : D (-a) = -D a := map_neg D a
protected lemma map_sub : D (a - b) = D a - D b := map_sub D a b

@[simp] lemma map_coe_int (n : ℤ) : D (n : A) = 0 :=
by rw [← zsmul_one, D.map_smul_of_tower n, map_one_eq_zero, smul_zero]

lemma leibniz_of_mul_eq_one {a b : A} (h : a * b = 1) : D a = -a^2 • D b :=
begin
  rw neg_smul,
  refine eq_neg_of_add_eq_zero_left _,
  calc D a + a ^ 2 • D b = a • b • D a + a • a • D b : by simp only [smul_smul, h, one_smul, sq]
                     ... = a • D (a * b)             : by rw [leibniz, smul_add, add_comm]
                     ... = 0                         : by rw [h, map_one_eq_zero, smul_zero]
end

lemma leibniz_inv_of [invertible a] : D (⅟a) = -⅟a^2 • D a :=
D.leibniz_of_mul_eq_one $ inv_of_mul_self a

lemma leibniz_inv {K : Type*} [field K] [module K M] [algebra R K] (D : derivation R K M) (a : K) :
  D (a⁻¹) = -a⁻¹ ^ 2 • D a :=
begin
  rcases eq_or_ne a 0 with (rfl|ha),
  { simp },
  { exact D.leibniz_of_mul_eq_one (inv_mul_cancel ha) }
end

instance : has_neg (derivation R A M) :=
⟨λ D, mk' (-D) $  λ a b,
  by simp only [linear_map.neg_apply, smul_neg, neg_add_rev, leibniz, coe_fn_coe, add_comm]⟩

@[simp] lemma coe_neg (D : derivation R A M) : ⇑(-D) = -D := rfl
@[simp] lemma coe_neg_linear_map (D : derivation R A M) : ↑(-D) = (-D : A →ₗ[R] M) :=
rfl
lemma neg_apply : (-D) a = -D a := rfl

instance : has_sub (derivation R A M) :=
⟨λ D1 D2, mk' (D1 - D2 : A →ₗ[R] M) $ λ a b,
  by simp only [linear_map.sub_apply, leibniz, coe_fn_coe, smul_sub, add_sub_add_comm]⟩

@[simp] lemma coe_sub (D1 D2 : derivation R A M) : ⇑(D1 - D2) = D1 - D2 := rfl
@[simp] lemma coe_sub_linear_map (D1 D2 : derivation R A M) : ↑(D1 - D2) = (D1 - D2 : A →ₗ[R] M) :=
rfl
lemma sub_apply : (D1 - D2) a = D1 a - D2 a := rfl

instance : add_comm_group (derivation R A M) :=
coe_injective.add_comm_group _ coe_zero coe_add coe_neg coe_sub (λ _ _, rfl) (λ _ _, rfl)

end

section lie_structures

/-! # Lie structures -/

variables (D : derivation R A A) {D1 D2 : derivation R A A} (r : R) (a b : A)

/-- The commutator of derivations is again a derivation. -/
instance : has_bracket (derivation R A A) (derivation R A A) :=
⟨λ D1 D2, mk' (⁅(D1 : module.End R A), (D2 : module.End R A)⁆) $ λ a b,
  by { simp only [ring.lie_def, map_add, id.smul_eq_mul, linear_map.mul_apply, leibniz, coe_fn_coe,
    linear_map.sub_apply], ring, }⟩

@[simp] lemma commutator_coe_linear_map :
  ↑⁅D1, D2⁆ = ⁅(D1 : module.End R A), (D2 : module.End R A)⁆ := rfl

lemma commutator_apply : ⁅D1, D2⁆ a = D1 (D2 a) - D2 (D1 a) := rfl

instance : lie_ring (derivation R A A) :=
{ add_lie     := λ d e f, by { ext a, simp only [commutator_apply, add_apply, map_add], ring, },
  lie_add     := λ d e f, by { ext a, simp only [commutator_apply, add_apply, map_add], ring, },
  lie_self    := λ d, by { ext a, simp only [commutator_apply, add_apply, map_add], ring_nf, },
  leibniz_lie := λ d e f,
    by { ext a, simp only [commutator_apply, add_apply, sub_apply, map_sub], ring, } }

instance : lie_algebra R (derivation R A A) :=
{ lie_smul := λ r d e, by { ext a, simp only [commutator_apply, map_smul, smul_sub, smul_apply]},
  ..derivation.module }

end lie_structures

end

end derivation

section to_square_zero

universes u v w

variables {R : Type u} {A : Type u} {B : Type w} [comm_semiring R] [comm_semiring A] [comm_ring B]
variables [algebra R A] [algebra R B] (I : ideal B) (hI : I ^ 2 = ⊥)

/-- If `f₁ f₂ : A →ₐ[R] B` are two lifts of the same `A →ₐ[R] B ⧸ I`,
  we may define a map `f₁ - f₂ : A →ₗ[R] I`. -/
def diff_to_ideal_of_quotient_comp_eq (f₁ f₂ : A →ₐ[R] B)
  (e : (ideal.quotient.mkₐ R I).comp f₁ = (ideal.quotient.mkₐ R I).comp f₂) :
  A →ₗ[R] I :=
linear_map.cod_restrict (I.restrict_scalars _) (f₁.to_linear_map - f₂.to_linear_map)
begin
  intro x,
  change f₁ x - f₂ x ∈ I,
  rw [← ideal.quotient.eq, ← ideal.quotient.mkₐ_eq_mk R, ← alg_hom.comp_apply, e],
  refl,
end

@[simp]
lemma diff_to_ideal_of_quotient_comp_eq_apply (f₁ f₂ : A →ₐ[R] B)
  (e : (ideal.quotient.mkₐ R I).comp f₁ = (ideal.quotient.mkₐ R I).comp f₂) (x : A) :
  ((diff_to_ideal_of_quotient_comp_eq I f₁ f₂ e) x : B) = f₁ x - f₂ x :=
rfl

variables [algebra A B] [is_scalar_tower R A B]

include hI

/-- Given a tower of algebras `R → A → B`, and a square-zero `I : ideal B`, each lift `A →ₐ[R] B`
of the canonical map `A →ₐ[R] B ⧸ I` corresponds to a `R`-derivation from `A` to `I`. -/
def derivation_to_square_zero_of_lift
  (f : A →ₐ[R] B) (e : (ideal.quotient.mkₐ R I).comp f = is_scalar_tower.to_alg_hom R A (B ⧸ I)) :
  derivation R A I :=
begin
  refine
  { map_one_eq_zero' := _,
    leibniz' := _,
    ..(diff_to_ideal_of_quotient_comp_eq I f (is_scalar_tower.to_alg_hom R A B) _) },
  { rw e, ext, refl },
  { ext, change f 1 - algebra_map A B 1 = 0, rw [map_one, map_one, sub_self] },
  { intros x y,
    let F := diff_to_ideal_of_quotient_comp_eq I f (is_scalar_tower.to_alg_hom R A B)
      (by { rw e, ext, refl }),
    have : (f x - algebra_map A B x) * (f y - algebra_map A B y) = 0,
    { rw [← ideal.mem_bot, ← hI, pow_two],
      convert (ideal.mul_mem_mul (F x).2 (F y).2) using 1 },
    ext,
    dsimp only [submodule.coe_add, submodule.coe_mk, linear_map.coe_mk,
      diff_to_ideal_of_quotient_comp_eq_apply, submodule.coe_smul_of_tower,
      is_scalar_tower.coe_to_alg_hom', linear_map.to_fun_eq_coe],
    simp only [map_mul, sub_mul, mul_sub, algebra.smul_def] at ⊢ this,
    rw [sub_eq_iff_eq_add, sub_eq_iff_eq_add] at this,
    rw this,
    ring }
end

lemma derivation_to_square_zero_of_lift_apply (f : A →ₐ[R] B)
  (e : (ideal.quotient.mkₐ R I).comp f = is_scalar_tower.to_alg_hom R A (B ⧸ I))
  (x : A) : (derivation_to_square_zero_of_lift I hI f e x : B) = f x - algebra_map A B x := rfl

/-- Given a tower of algebras `R → A → B`, and a square-zero `I : ideal B`, each `R`-derivation
from `A` to `I` corresponds to a lift `A →ₐ[R] B` of the canonical map `A →ₐ[R] B ⧸ I`. -/
def lift_of_derivation_to_square_zero (f : derivation R A I) :
  A →ₐ[R] B :=
{ map_one' := show (f 1 : B) + algebra_map A B 1 = 1,
   by rw [map_one, f.map_one_eq_zero, submodule.coe_zero, zero_add],
  map_mul' := λ x y, begin
    have : (f x : B) * (f y) = 0,
    { rw [← ideal.mem_bot, ← hI, pow_two], convert (ideal.mul_mem_mul (f x).2 (f y).2) using 1 },
    dsimp,
    simp only [map_mul, f.leibniz, add_mul, mul_add, submodule.coe_add,
      submodule.coe_smul_of_tower, algebra.smul_def, this],
    ring
  end,
  commutes' := λ r, by { dsimp, simp [← is_scalar_tower.algebra_map_apply R A B r] },
  map_zero' := ((I.restrict_scalars R).subtype.comp f.to_linear_map +
    (is_scalar_tower.to_alg_hom R A B).to_linear_map).map_zero,
  ..((I.restrict_scalars R).subtype.comp f.to_linear_map +
    (is_scalar_tower.to_alg_hom R A B).to_linear_map) }

lemma lift_of_derivation_to_square_zero_apply (f : derivation R A I) (x : A) :
  lift_of_derivation_to_square_zero I hI f x = f x + algebra_map A B x := rfl

@[simp] lemma lift_of_derivation_to_square_zero_mk_apply (d : derivation R A I) (x : A) :
    ideal.quotient.mk I (lift_of_derivation_to_square_zero I hI d x) = algebra_map A (B ⧸ I) x :=
by { rw [lift_of_derivation_to_square_zero_apply, map_add,
  ideal.quotient.eq_zero_iff_mem.mpr (d x).prop, zero_add], refl }

/-- Given a tower of algebras `R → A → B`, and a square-zero `I : ideal B`,
there is a 1-1 correspondance between `R`-derivations from `A` to `I` and
lifts `A →ₐ[R] B` of the canonical map `A →ₐ[R] B ⧸ I`. -/
@[simps]
def derivation_to_square_zero_equiv_lift :
  derivation R A I ≃
    { f : A →ₐ[R] B // (ideal.quotient.mkₐ R I).comp f = is_scalar_tower.to_alg_hom R A (B ⧸ I) } :=
begin
  refine ⟨λ d, ⟨lift_of_derivation_to_square_zero I hI d, _⟩, λ f,
    (derivation_to_square_zero_of_lift I hI f.1 f.2 : _), _, _⟩,
  { ext x, exact lift_of_derivation_to_square_zero_mk_apply I hI d x },
  { intro d, ext x, exact add_sub_cancel (d x : B) (algebra_map A B x) },
  { rintro ⟨f, hf⟩, ext x,  exact sub_add_cancel (f x) (algebra_map A B x) }
end

end to_square_zero

section derivation_module

open_locale tensor_product

variables (R S : Type*) [comm_ring R] [comm_ring S] [algebra R S]

/-- The kernel of the map `(𝟙, 𝟙) : S ⊗[R] S →ₐ[R] S`. -/
abbreviation derivation_module.ideal : ideal (S ⊗[R] S) :=
ring_hom.ker (tensor_product.lmul' R : S ⊗[R] S →ₐ[R] S)

variable {S}

lemma derivation_module.one_smul_sub_smul_one_mem_ideal (a : S) :
  (1 : S) ⊗ₜ[R] a - a ⊗ₜ[R] (1 : S) ∈ derivation_module.ideal R S :=
by simp [ring_hom.mem_ker]

variables {R}

variables {M : Type*} [add_comm_group M] [module R M] [module S M] [is_scalar_tower R S M]

/-- For a `R`-derivation `S → M`, this is the map `S ⊗[R] S →ₗ[S] M` sending `s ⊗ₜ t ↦ s • D t`. -/
def derivation.tensor_product_to (d : derivation R S M) : S ⊗[R] S →ₗ[S] M :=
tensor_product.algebra_tensor_module.lift ((linear_map.lsmul S (S →ₗ[R] M)).flip d.to_linear_map)

lemma derivation.tensor_product_to_tmul (d : derivation R S M) (s t : S) :
  d.tensor_product_to (s ⊗ₜ t) = s • d t :=
tensor_product.lift.tmul s t

lemma derivation.tensor_product_to_mul (d : derivation R S M) (x y : S ⊗[R] S) :
  d.tensor_product_to (x * y) = tensor_product.lmul' R x • d.tensor_product_to y +
    tensor_product.lmul' R y • d.tensor_product_to x :=
begin
  apply tensor_product.induction_on x,
  { rw [zero_mul, map_zero, map_zero, zero_smul, smul_zero, add_zero] },
  swap, { rintros, simp only [add_mul, map_add, add_smul, *, smul_add], rw add_add_add_comm },
  intros x₁ x₂,
  apply tensor_product.induction_on y,
  { rw [mul_zero, map_zero, map_zero, zero_smul, smul_zero, add_zero] },
  swap, { rintros, simp only [mul_add, map_add, add_smul, *, smul_add], rw add_add_add_comm },
  intros x y,
  simp only [tensor_product.tmul_mul_tmul, derivation.tensor_product_to,
    tensor_product.algebra_tensor_module.lift_apply, tensor_product.lift.tmul',
    tensor_product.lmul'_apply_tmul],
  dsimp,
  rw d.leibniz,
  simp only [smul_smul, smul_add, mul_comm (x * y) x₁, mul_right_comm x₁ x₂, ← mul_assoc],
end

variables (R S)

/-- The kernel of `S ⊗[R] S →ₐ[R] S` is generated by `1 ⊗ s - s ⊗ 1` as a `S`-module. -/
lemma derivation_module.submodule_span_range_eq_ideal :
  submodule.span S (set.range $ λ s : S, (1 : S) ⊗ₜ[R] s - s ⊗ₜ[R] (1 : S)) =
    (derivation_module.ideal R S).restrict_scalars S :=
begin
  apply le_antisymm,
  { rw submodule.span_le,
    rintros _ ⟨s, rfl⟩,
    exact derivation_module.one_smul_sub_smul_one_mem_ideal _ _ },
  { rintros x (hx : _ = _),
    have : x - (tensor_product.lmul' R x) ⊗ₜ[R] (1 : S)   = x,
    { rw [hx, tensor_product.zero_tmul, sub_zero] },
    rw ← this,
    clear this hx,
    apply tensor_product.induction_on x; clear x,
    { rw [map_zero, tensor_product.zero_tmul, sub_zero], exact zero_mem _ },
    { intros x y,
      convert_to x • (1 ⊗ₜ y - y ⊗ₜ 1) ∈ _,
      { rw [tensor_product.lmul'_apply_tmul, smul_sub, tensor_product.smul_tmul',
          tensor_product.smul_tmul', smul_eq_mul, smul_eq_mul, mul_one] },
      { refine submodule.smul_mem _ x _,
        apply submodule.subset_span,
        exact set.mem_range_self y } },
    { intros x y hx hy,
      rw [map_add, tensor_product.add_tmul, ← sub_add_sub_comm],
      exact add_mem hx hy } }
end

lemma derivation_module.span_range_eq_ideal :
  ideal.span (set.range $ λ s : S, (1 : S) ⊗ₜ[R] s - s ⊗ₜ[R] (1 : S)) =
    derivation_module.ideal R S :=
begin
  apply le_antisymm,
  { rw ideal.span_le,
    rintros _ ⟨s, rfl⟩,
    exact derivation_module.one_smul_sub_smul_one_mem_ideal _ _ },
  { change (derivation_module.ideal R S).restrict_scalars S ≤ (ideal.span _).restrict_scalars S,
    rw [← derivation_module.submodule_span_range_eq_ideal, ideal.span],
    conv_rhs { rw ← submodule.span_span_of_tower S },
    exact submodule.subset_span }
end

end derivation_module

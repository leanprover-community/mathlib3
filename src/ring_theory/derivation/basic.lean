/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Andrew Yang
-/

import ring_theory.adjoin.basic

/-!
# Derivations

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines derivation. A derivation `D` from the `R`-algebra `A` to the `A`-module `M` is an
`R`-linear map that satisfy the Leibniz rule `D (a * b) = a * D b + D a * b`.

## Main results

- `derivation`: The type of `R`-derivations from `A` to `M`. This has an `A`-module structure.
- `derivation.llcomp`: We may compose linear maps and derivations to obtain a derivation,
  and the composition is bilinear.

See `ring_theory.derivation.lie` for
- `derivation.lie_algebra`: The `R`-derivations from `A` to `A` form an lie algebra over `R`.

and `ring_theory.derivation.to_square_zero` for
- `derivation_to_square_zero_equiv_lift`: The `R`-derivations from `A` into a square-zero ideal `I`
  of `B` corresponds to the lifts `A →ₐ[R] B` of the map `A →ₐ[R] B ⧸ I`.

## Future project

- Generalize derivations into bimodules.

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

variables {S T : Type*}
variables [monoid S] [distrib_mul_action S M] [smul_comm_class R S M] [smul_comm_class S A M]
variables [monoid T] [distrib_mul_action T M] [smul_comm_class R T M] [smul_comm_class T A M]

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

instance [has_smul S T] [is_scalar_tower S T M] : is_scalar_tower S T (derivation R A M) :=
⟨λ x y z, ext $ λ a, smul_assoc _ _ _⟩

instance [smul_comm_class S T M] : smul_comm_class S T (derivation R A M) :=
⟨λ x y z, ext $ λ a, smul_comm _ _ _⟩

end scalar

@[priority 100]
instance {S : Type*} [semiring S] [module S M] [smul_comm_class R S M] [smul_comm_class S A M] :
  module S (derivation R A M) :=
function.injective.module S coe_fn_add_monoid_hom coe_injective coe_smul

section push_forward

variables {N : Type*} [add_comm_monoid N] [module A N] [module R N] [is_scalar_tower R A M]
  [is_scalar_tower R A N]
variables (f : M →ₗ[A] N) (e : M ≃ₗ[A] N)

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
@[simps]
def llcomp : (M →ₗ[A] N) →ₗ[A] derivation R A M →ₗ[R] derivation R A N :=
{ to_fun := λ f, f.comp_der,
  map_add' := λ f₁ f₂, by { ext, refl },
  map_smul' := λ r D, by { ext, refl } }

/-- Pushing a derivation foward through a linear equivalence is an equivalence. -/
def _root_.linear_equiv.comp_der : derivation R A M ≃ₗ[R] derivation R A N :=
{ inv_fun := e.symm.to_linear_map.comp_der,
  left_inv := λ D, by { ext a, exact e.symm_apply_apply (D a) },
  right_inv := λ D, by { ext a, exact e.apply_symm_apply (D a) },
  ..e.to_linear_map.comp_der }


end push_forward

section restrict_scalars

variables {S : Type*} [comm_semiring S]
variables [algebra S A] [module S M] [linear_map.compatible_smul A M R S]

variables (R)

/-- If `A` is both an `R`-algebra and an `S`-algebra; `M` is both an `R`-module and an `S`-module,
then an `S`-derivation `A → M` is also an `R`-derivation if it is also `R`-linear. -/
protected
def restrict_scalars (d : derivation S A M) : derivation R A M :=
{ map_one_eq_zero' := d.map_one_eq_zero,
  leibniz' := d.leibniz,
  to_linear_map := d.to_linear_map.restrict_scalars R }

end restrict_scalars

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

end

end derivation

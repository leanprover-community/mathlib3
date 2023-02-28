/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import algebra.algebra.pi
import ring_theory.adjoin.basic
import data.polynomial.eval

/-!
# Theory of univariate polynomials

We show that `A[X]` is an R-algebra when `A` is an R-algebra.
We promote `eval₂` to an algebra hom in `aeval`.
-/

noncomputable theory
open finset
open_locale big_operators polynomial

namespace polynomial
universes u v w z
variables {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B' : Type*} {a b : R} {n : ℕ}
variables [comm_semiring A'] [semiring B']

section comm_semiring
variables [comm_semiring R] {p q r : R[X]}

variables [semiring A] [algebra R A]

/-- Note that this instance also provides `algebra R R[X]`. -/
instance algebra_of_algebra : algebra R A[X] :=
{ smul_def' := λ r p, to_finsupp_injective $ begin
    dsimp only [ring_hom.to_fun_eq_coe, ring_hom.comp_apply],
    rw [to_finsupp_smul, to_finsupp_mul, to_finsupp_C],
    exact algebra.smul_def' _ _,
  end,
  commutes' := λ r p, to_finsupp_injective $ begin
    dsimp only [ring_hom.to_fun_eq_coe, ring_hom.comp_apply],
    simp_rw [to_finsupp_mul, to_finsupp_C],
    convert algebra.commutes' r p.to_finsupp,
  end,
  to_ring_hom := C.comp (algebra_map R A) }

lemma algebra_map_apply (r : R) :
  algebra_map R A[X] r = C (algebra_map R A r) :=
rfl

@[simp] lemma to_finsupp_algebra_map (r : R) :
  (algebra_map R A[X] r).to_finsupp = algebra_map R _ r :=
show to_finsupp (C (algebra_map _ _ r)) = _, by { rw to_finsupp_C, refl }

lemma of_finsupp_algebra_map (r : R) :
  (⟨algebra_map R _ r⟩ : A[X]) = algebra_map R A[X] r :=
to_finsupp_injective (to_finsupp_algebra_map _).symm

/--
When we have `[comm_semiring R]`, the function `C` is the same as `algebra_map R R[X]`.

(But note that `C` is defined when `R` is not necessarily commutative, in which case
`algebra_map` is not available.)
-/
lemma C_eq_algebra_map (r : R) :
  C r = algebra_map R R[X] r :=
rfl

variables {R}

/--
  Extensionality lemma for algebra maps out of `A'[X]` over a smaller base ring than `A'`
-/
@[ext] lemma alg_hom_ext' [algebra R A'] [algebra R B']
  {f g : A'[X] →ₐ[R] B'}
  (h₁ : f.comp (is_scalar_tower.to_alg_hom R A' A'[X]) =
        g.comp (is_scalar_tower.to_alg_hom R A' A'[X]))
  (h₂ : f X = g X) : f = g :=
alg_hom.coe_ring_hom_injective (polynomial.ring_hom_ext'
  (congr_arg alg_hom.to_ring_hom h₁) h₂)

variable (R)

/-- Algebra isomorphism between `R[X]` and `add_monoid_algebra R ℕ`. This is just an
implementation detail, but it can be useful to transfer results from `finsupp` to polynomials. -/
@[simps]
def to_finsupp_iso_alg : R[X] ≃ₐ[R] add_monoid_algebra R ℕ :=
{ commutes' := λ r,
  begin
    dsimp,
    exact to_finsupp_algebra_map _,
  end,
  ..to_finsupp_iso R }

variable {R}

instance [nontrivial A] : nontrivial (subalgebra R A[X]) :=
⟨⟨⊥, ⊤, begin
  rw [ne.def, set_like.ext_iff, not_forall],
  refine ⟨X, _⟩,
  simp only [algebra.mem_bot, not_exists, set.mem_range, iff_true, algebra.mem_top,
    algebra_map_apply, not_forall],
  intro x,
  rw [ext_iff, not_forall],
  refine ⟨1, _⟩,
  simp [coeff_C],
end⟩⟩

@[simp]
lemma alg_hom_eval₂_algebra_map
  {R A B : Type*} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B]
  (p : R[X]) (f : A →ₐ[R] B) (a : A) :
  f (eval₂ (algebra_map R A) a p) = eval₂ (algebra_map R B) (f a) p :=
begin
  dsimp [eval₂, sum],
  simp only [f.map_sum, f.map_mul, f.map_pow, eq_int_cast, map_int_cast,
    alg_hom.commutes],
end

@[simp]
lemma eval₂_algebra_map_X {R A : Type*} [comm_semiring R] [semiring A] [algebra R A]
  (p : R[X]) (f : R[X] →ₐ[R] A) :
  eval₂ (algebra_map R A) (f X) p = f p :=
begin
  conv_rhs { rw [←polynomial.sum_C_mul_X_pow_eq p], },
  dsimp [eval₂, sum],
  simp only [f.map_sum, f.map_mul, f.map_pow, eq_int_cast, map_int_cast],
  simp [polynomial.C_eq_algebra_map],
end

-- these used to be about `algebra_map ℤ R`, but now the simp-normal form is `int.cast_ring_hom R`.
@[simp]
lemma ring_hom_eval₂_cast_int_ring_hom {R S : Type*} [ring R] [ring S]
  (p : ℤ[X]) (f : R →+* S) (r : R) :
  f (eval₂ (int.cast_ring_hom R) r p) = eval₂ (int.cast_ring_hom S) (f r) p :=
alg_hom_eval₂_algebra_map p f.to_int_alg_hom r

@[simp]
lemma eval₂_int_cast_ring_hom_X {R : Type*} [ring R] (p : ℤ[X]) (f : ℤ[X] →+* R) :
  eval₂ (int.cast_ring_hom R) (f X) p = f p :=
eval₂_algebra_map_X p f.to_int_alg_hom

end comm_semiring

section aeval
variables [comm_semiring R] {p q : R[X]}

variables [semiring A] [algebra R A]
variables {B : Type*} [semiring B] [algebra R B]
variables (x : A)

/-- Given a valuation `x` of the variable in an `R`-algebra `A`, `aeval R A x` is
the unique `R`-algebra homomorphism from `R[X]` to `A` sending `X` to `x`.

This is a stronger variant of the linear map `polynomial.leval`. -/
def aeval : R[X] →ₐ[R] A :=
{ commutes' := λ r, eval₂_C _ _,
  ..eval₂_ring_hom' (algebra_map R A) x (λ a, algebra.commutes _ _) }

variables {R A}

@[simp] lemma adjoin_X : algebra.adjoin R ({X} : set R[X]) = ⊤ :=
begin
  refine top_unique (λ p hp, _),
  set S := algebra.adjoin R ({X} : set R[X]),
  rw [← sum_monomial_eq p], simp only [← smul_X_eq_monomial, sum],
  exact S.sum_mem (λ n hn, S.smul_mem (S.pow_mem (algebra.subset_adjoin rfl) _) _)
end

@[ext] lemma alg_hom_ext {f g : R[X] →ₐ[R] A} (h : f X = g X) : f = g :=
alg_hom.ext_of_adjoin_eq_top adjoin_X $ λ p hp, (set.mem_singleton_iff.1 hp).symm ▸ h

theorem aeval_def (p : R[X]) : aeval x p = eval₂ (algebra_map R A) x p := rfl

@[simp] lemma aeval_zero : aeval x (0 : R[X]) = 0 :=
alg_hom.map_zero (aeval x)

@[simp] lemma aeval_X : aeval x (X : R[X]) = x := eval₂_X _ x

@[simp] lemma aeval_C (r : R) : aeval x (C r) = algebra_map R A r := eval₂_C _ x

@[simp] lemma aeval_monomial {n : ℕ} {r : R} : aeval x (monomial n r) = (algebra_map _ _ r) * x^n :=
eval₂_monomial _ _

@[simp] lemma aeval_X_pow {n : ℕ} : aeval x ((X : R[X])^n) = x^n :=
eval₂_X_pow _ _

@[simp] lemma aeval_add : aeval x (p + q) = aeval x p + aeval x q :=
alg_hom.map_add _ _ _

@[simp] lemma aeval_one : aeval x (1 : R[X]) = 1 :=
alg_hom.map_one _

@[simp] lemma aeval_bit0 : aeval x (bit0 p) = bit0 (aeval x p) :=
alg_hom.map_bit0 _ _

@[simp] lemma aeval_bit1 : aeval x (bit1 p) = bit1 (aeval x p) :=
alg_hom.map_bit1 _ _

@[simp] lemma aeval_nat_cast (n : ℕ) : aeval x (n : R[X]) = n :=
map_nat_cast _ _

lemma aeval_mul : aeval x (p * q) = aeval x p * aeval x q :=
alg_hom.map_mul _ _ _

lemma aeval_comp {A : Type*} [comm_semiring A] [algebra R A] (x : A) :
  aeval x (p.comp q) = (aeval (aeval x q) p) :=
eval₂_comp (algebra_map R A)

theorem aeval_alg_hom (f : A →ₐ[R] B) (x : A) : aeval (f x) = f.comp (aeval x) :=
alg_hom_ext $ by simp only [aeval_X, alg_hom.comp_apply]

@[simp] theorem aeval_X_left : aeval (X : R[X]) = alg_hom.id R R[X] :=
alg_hom_ext $ aeval_X X

theorem aeval_X_left_apply (p : R[X]) : aeval X p = p :=
alg_hom.congr_fun (@aeval_X_left R _) p

theorem eval_unique (φ : R[X] →ₐ[R] A) (p) :
  φ p = eval₂ (algebra_map R A) (φ X) p :=
by rw [← aeval_def, aeval_alg_hom, aeval_X_left, alg_hom.comp_id]

theorem aeval_alg_hom_apply {F : Type*} [alg_hom_class F R A B] (f : F) (x : A) (p : R[X]) :
  aeval (f x) p = f (aeval x p) :=
begin
  refine polynomial.induction_on p (by simp) (λ p q hp hq, _) (by simp),
  rw [map_add, hp, hq, ← map_add, ← map_add]
end

theorem aeval_alg_equiv (f : A ≃ₐ[R] B) (x : A) : aeval (f x) = (f : A →ₐ[R] B).comp (aeval x) :=
aeval_alg_hom (f : A →ₐ[R] B) x

lemma aeval_algebra_map_apply_eq_algebra_map_eval (x : R) (p : R[X]) :
  aeval (algebra_map R A x) p = algebra_map R A (p.eval x) :=
aeval_alg_hom_apply (algebra.of_id R A) x p

@[simp] lemma coe_aeval_eq_eval (r : R) : (aeval r : R[X] → R) = eval r := rfl

@[simp] lemma coe_aeval_eq_eval_ring_hom (x : R) :
  ((aeval x : R[X] →ₐ[R] R) : R[X] →+* R) = eval_ring_hom x :=
rfl

@[simp] lemma aeval_fn_apply {X : Type*} (g : R[X]) (f : X → R) (x : X) :
  ((aeval f) g) x = aeval (f x) g :=
(aeval_alg_hom_apply (pi.eval_alg_hom R (λ _, R) x) f g).symm

@[norm_cast] lemma aeval_subalgebra_coe
  (g : R[X]) {A : Type*} [semiring A] [algebra R A] (s : subalgebra R A) (f : s) :
  (aeval f g : A) = aeval (f : A) g :=
(aeval_alg_hom_apply s.val f g).symm

lemma coeff_zero_eq_aeval_zero (p : R[X]) : p.coeff 0 = aeval 0 p :=
by simp [coeff_zero_eq_eval_zero]

lemma coeff_zero_eq_aeval_zero' (p : R[X]) :
  algebra_map R A (p.coeff 0) = aeval (0 : A) p :=
by simp [aeval_def]

lemma map_aeval_eq_aeval_map {S T U : Type*} [comm_semiring S] [comm_semiring T] [semiring U]
  [algebra R S] [algebra T U] {φ : R →+* T} {ψ : S →+* U}
  (h : (algebra_map T U).comp φ = ψ.comp (algebra_map R S)) (p : R[X]) (a : S) :
  ψ (aeval a p) = aeval (ψ a) (p.map φ) :=
begin
  conv_rhs {rw [aeval_def, ← eval_map]},
  rw [map_map, h, ← map_map, eval_map, eval₂_at_apply, aeval_def, eval_map],
end

lemma aeval_eq_zero_of_dvd_aeval_eq_zero [comm_semiring S] [comm_semiring T] [algebra S T]
  {p q : S[X]} (h₁ : p ∣ q) {a : T} (h₂ : aeval a p = 0) : aeval a q = 0 :=
begin
  rw [aeval_def, ← eval_map] at h₂ ⊢,
  exact eval_eq_zero_of_dvd_of_eval_eq_zero (polynomial.map_dvd (algebra_map S T) h₁) h₂,
end

variable (R)

theorem _root_.algebra.adjoin_singleton_eq_range_aeval (x : A) :
  algebra.adjoin R {x} = (polynomial.aeval x).range :=
by rw [← algebra.map_top, ← adjoin_X, alg_hom.map_adjoin, set.image_singleton, aeval_X]

variable {R}

section semiring

variables [semiring S] {f : R →+* S}

lemma aeval_eq_sum_range [algebra R S] {p : R[X]} (x : S) :
  aeval x p = ∑ i in finset.range (p.nat_degree + 1), p.coeff i • x ^ i :=
by { simp_rw algebra.smul_def, exact eval₂_eq_sum_range (algebra_map R S) x }

lemma aeval_eq_sum_range' [algebra R S] {p : R[X]} {n : ℕ} (hn : p.nat_degree < n) (x : S) :
  aeval x p = ∑ i in finset.range n, p.coeff i • x ^ i :=
by { simp_rw algebra.smul_def, exact eval₂_eq_sum_range' (algebra_map R S) hn x }

lemma is_root_of_eval₂_map_eq_zero
  (hf : function.injective f) {r : R} : eval₂ f (f r) p = 0 → p.is_root r :=
begin
  intro h,
  apply hf,
  rw [←eval₂_hom, h, f.map_zero],
end

lemma is_root_of_aeval_algebra_map_eq_zero [algebra R S] {p : R[X]}
  (inj : function.injective (algebra_map R S))
  {r : R} (hr : aeval (algebra_map R S r) p = 0) : p.is_root r :=
is_root_of_eval₂_map_eq_zero inj hr

end semiring

section comm_semiring

section aeval_tower

variables [comm_semiring S] [algebra S R] [algebra S A'] [algebra S B']

/-- Version of `aeval` for defining algebra homs out of `R[X]` over a smaller base ring
  than `R`. -/
def aeval_tower (f : R →ₐ[S] A') (x : A') : R[X] →ₐ[S] A' :=
{ commutes' := λ r, by simp [algebra_map_apply],
  ..eval₂_ring_hom ↑f x }

variables (g : R →ₐ[S] A') (y : A')

@[simp] lemma aeval_tower_X : aeval_tower g y X = y := eval₂_X _ _

@[simp] lemma aeval_tower_C (x : R) : aeval_tower g y (C x) = g x := eval₂_C _ _

@[simp] lemma aeval_tower_comp_C : ((aeval_tower g y : R[X] →+* A').comp C) = g :=
ring_hom.ext $ aeval_tower_C _ _

@[simp] lemma aeval_tower_algebra_map (x : R) :
  aeval_tower g y (algebra_map R R[X] x) = g x := eval₂_C _ _

@[simp] lemma aeval_tower_comp_algebra_map :
  (aeval_tower g y : R[X] →+* A').comp (algebra_map R R[X]) = g :=
aeval_tower_comp_C _ _

lemma aeval_tower_to_alg_hom (x : R) :
  aeval_tower g y (is_scalar_tower.to_alg_hom S R R[X] x) = g x :=
aeval_tower_algebra_map _ _ _

@[simp] lemma aeval_tower_comp_to_alg_hom :
  (aeval_tower g y).comp (is_scalar_tower.to_alg_hom S R R[X]) = g :=
alg_hom.coe_ring_hom_injective $ aeval_tower_comp_algebra_map _ _

@[simp] lemma aeval_tower_id : aeval_tower (alg_hom.id S S) = aeval :=
by { ext, simp only [eval_X, aeval_tower_X, coe_aeval_eq_eval], }

@[simp] lemma aeval_tower_of_id : aeval_tower (algebra.of_id S A') = aeval :=
by { ext, simp only [aeval_X, aeval_tower_X], }

end aeval_tower

end comm_semiring

section comm_ring

variables [comm_ring S] {f : R →+* S}

lemma dvd_term_of_dvd_eval_of_dvd_terms {z p : S} {f : S[X]} (i : ℕ)
  (dvd_eval : p ∣ f.eval z) (dvd_terms : ∀ (j ≠ i), p ∣ f.coeff j * z ^ j) :
  p ∣ f.coeff i * z ^ i :=
begin
  by_cases hi : i ∈ f.support,
  { rw [eval, eval₂, sum] at dvd_eval,
    rw [←finset.insert_erase hi, finset.sum_insert (finset.not_mem_erase _ _)] at dvd_eval,
    refine (dvd_add_left _).mp dvd_eval,
    apply finset.dvd_sum,
    intros j hj,
    exact dvd_terms j (finset.ne_of_mem_erase hj) },
  { convert dvd_zero p,
    rw not_mem_support_iff at hi,
    simp [hi] }
end

lemma dvd_term_of_is_root_of_dvd_terms {r p : S} {f : S[X]} (i : ℕ)
  (hr : f.is_root r) (h : ∀ (j ≠ i), p ∣ f.coeff j * r ^ j) : p ∣ f.coeff i * r ^ i :=
dvd_term_of_dvd_eval_of_dvd_terms i (eq.symm hr ▸ dvd_zero p) h

end comm_ring

end aeval

section ring
variables [ring R]

/--
The evaluation map is not generally multiplicative when the coefficient ring is noncommutative,
but nevertheless any polynomial of the form `p * (X - monomial 0 r)` is sent to zero
when evaluated at `r`.

This is the key step in our proof of the Cayley-Hamilton theorem.
-/
lemma eval_mul_X_sub_C {p : R[X]} (r : R) :
  (p * (X - C r)).eval r = 0 :=
begin
  simp only [eval, eval₂, ring_hom.id_apply],
  have bound := calc
    (p * (X - C r)).nat_degree
         ≤ p.nat_degree + (X - C r).nat_degree : nat_degree_mul_le
     ... ≤ p.nat_degree + 1 : add_le_add_left (nat_degree_X_sub_C_le _) _
     ... < p.nat_degree + 2 : lt_add_one _,
  rw sum_over_range' _ _ (p.nat_degree + 2) bound,
  swap,
  { simp, },
  rw sum_range_succ',
  conv_lhs
  { congr, apply_congr, skip,
    rw [coeff_mul_X_sub_C, sub_mul, mul_assoc, ←pow_succ], },
  simp [sum_range_sub', coeff_monomial],
end

theorem not_is_unit_X_sub_C [nontrivial R] (r : R) : ¬ is_unit (X - C r) :=
λ ⟨⟨_, g, hfg, hgf⟩, rfl⟩, zero_ne_one' R $ by erw [← eval_mul_X_sub_C, hgf, eval_one]

end ring

lemma aeval_endomorphism {M : Type*}
  [comm_ring R] [add_comm_group M] [module R M]
  (f : M →ₗ[R] M) (v : M) (p : R[X]) :
  aeval f p v = p.sum (λ n b, b • (f ^ n) v) :=
begin
  rw [aeval_def, eval₂],
  exact (linear_map.applyₗ v).map_sum,
end

end polynomial

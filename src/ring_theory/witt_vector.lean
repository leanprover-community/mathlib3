/-
2020. No rights reserved. https://unlicense.org/
Authors: Johan Commelin
-/

-- import algebra.inj_surj
import data.nat.choose
import data.int.gcd
import data.mv_polynomial
import data.zmod.basic
import data.fintype.card
import ring_theory.multiplicity
import algebra.invertible
import number_theory.quadratic_reciprocity
import ring_theory.witt_vector_preps
import tactic
import tactic.nth_rewrite

/-!
# Witt vectors

## Main definitions
TODO

## Notation
TODO

## Implementation details
TODO
-/

/-- `witt_vectors p R` is the ring of `p`-typical Witt vectors over the commutative ring `R`,
where `p` is a prime number.

If `p` is invertible in `R`, this ring is isomorphic to `ℕ → R` (the product of `ℕ` copies of `R`).
If `R` is a ring of characteristic `p`, then `witt_vectors p R` is a ring of characteristic `0`.
The canonical example is `witt_vectors p (zmod p)`,
which is isomorphic to the `p`-adic integers `ℤ_[p]`. -/
def witt_vectors (p : ℕ) (R : Type*) := ℕ → R

universes u v w u₁
open mv_polynomial (hiding aeval) -- this hiding is a hack, because we setup notation below
open set
open finset (range)

open_locale big_operators

-- TODO: This should be fixed in mathlib
local notation `aeval` := mv_polynomial.aeval _ _

local attribute [-simp] coe_eval₂_hom

variables (p : ℕ)
variables (R : Type u) [comm_ring R]

/-!
## Witt polynomials

To endow `witt_vectors p R` with a ring structure,
we need to study the so-called Witt polynomials.
-/

/-- `witt_polynomial p R n` is the `n`-th Witt polynomial
with respect to a prime `p` with coefficients in a commutative ring `R`.
It is defined as:

`∑_{i ≤ n} p^i X_i^{p^{n-i}} ∈ R[X_0, X_1, X_2, …]`. -/
noncomputable def witt_polynomial (n : ℕ) : mv_polynomial ℕ R :=
∑ i in range (n+1), C (p^i : R) * X i ^ (p^(n-i))

/-! We set up notation locally to this file, to keep statements short and comprehensible.
This allows us to simply write `W n` or `W_ ℤ n`. -/

-- Notation with ring of coefficients explicit
localized "notation `W_` := witt_polynomial p"   in witt
-- Notation with ring of coefficients implicit
localized "notation `W`  := witt_polynomial p _" in witt

open_locale witt

/- The first observation is that the Witt polynomial doesn't really depend on the coefficient ring.
If we map the coefficients through a ring homomorphism, we obtain the corresponding Witt polynomial
over the target ring. -/
section
variables {R} {S : Type*} [comm_ring S]

@[simp] lemma map_hom_witt_polynomial (f : R →+* S) (n : ℕ) :
  map_hom f (W n) = W n :=
begin
  rw [witt_polynomial, ring_hom.map_sum],
  apply finset.sum_congr rfl,
  intros i hi,
  rw [ring_hom.map_mul, map_hom_C f, ring_hom.map_pow,
      ring_hom.map_nat_cast, ring_hom.map_pow, ring_hom.map_pow, map_hom_X],
end

-- no longer used...
lemma map_witt_polynomial (f : R →+* S) (n : ℕ) :
  map f (W n) = W n :=
map_hom_witt_polynomial p f n

variables (R)

lemma aeval_witt_polynomial {A : Type*} [comm_ring A] [algebra R A] (f : ℕ → A) (n : ℕ) :
  aeval f (W_ R n) = ∑ i in range (n+1), p^i * (f i) ^ (p ^ (n-i)) :=
by { -- clean this up
  simp only [witt_polynomial, alg_hom.map_sum, aeval_C, ring_hom.map_nat_cast, alg_hom.map_pow,
    C_pow, aeval_X, alg_hom.map_mul,
 ring_hom.map_nat_cast, alg_hom.map_pow, C_pow, aeval_X, alg_hom.map_mul],
 simp only [alg_hom.map_nat_cast], }

end

/-- View a polynomial written in terms of the basis of Witt polynomials
as a polynomial written in terms of the standard basis.

In particular, this sends `X n` to `witt_polynomial p n`.
This fact is recorded in `from_W_to_X_basis_X`. -/
noncomputable def from_W_to_X_basis : mv_polynomial ℕ R →ₐ[R] mv_polynomial ℕ R :=
aeval W

@[simp] lemma from_W_to_X_basis_X (n) : from_W_to_X_basis p R (X n) = W n :=
by simp [from_W_to_X_basis]

-- We need p to be invertible for the following definitions

/-- The `X_in_terms_of_W p R n` is the polynomial on the basis of Witt polynomials
that corresponds to the ordinary `X n`.
This means that `from_W_to_X_basis` sends `X_in_terms_of_W p R n` to `X n`.
This fact is recorded in `from_W_to_X_basis_X_in_terms_of_W`. -/
noncomputable def X_in_terms_of_W [invertible (p : R)] :
  ℕ → mv_polynomial ℕ R
| n := (X n - (∑ i : fin n,
  have _ := i.2, (C (p^(i : ℕ) : R) * (X_in_terms_of_W i)^(p^(n-i))))) * C (⅟p ^ n : R)

lemma X_in_terms_of_W_eq [invertible (p : R)] {n : ℕ} :
  X_in_terms_of_W p R n =
  (X n - (∑ i in range n, C (p^i : R) * X_in_terms_of_W p R i ^ p ^ (n - i))) * C (⅟p ^ n : R) :=
by { rw [X_in_terms_of_W, ← fin.sum_univ_eq_sum_range], refl }

/-- View a polynomial written in terms of the standard basis
as a polynomial written in terms of the Witt basis.

This sends `W n` to `X n`, and `X n` to `X_in_terms_of_W p R n`. -/
noncomputable def from_X_to_W_basis [invertible (p : R)] :
  mv_polynomial ℕ R →ₐ[R] mv_polynomial ℕ R :=
aeval (X_in_terms_of_W p R)

@[simp] lemma from_X_to_W_basis_X [invertible (p : R)] (n : ℕ) :
  (from_X_to_W_basis p R) (X n) = X_in_terms_of_W p R n :=
by rw [from_X_to_W_basis, aeval_X]

@[simp] lemma from_W_to_X_basis_X_in_terms_of_W [invertible (p : R)] (n : ℕ) :
  from_W_to_X_basis p R (X_in_terms_of_W p R n) = X n :=
begin
  apply nat.strong_induction_on n,
  clear n, intros n H,
  rw [X_in_terms_of_W_eq],
  simp only [alg_hom.map_mul, alg_hom.map_sub, alg_hom_C, from_W_to_X_basis_X p R n, alg_hom.map_sum],
  rw [finset.sum_congr rfl, (_ : W_ R n - ∑ i in range n, C (p^i : R) * (X i)^p^(n-i) = C (p^n : R) * X n)],
  { rw [mul_right_comm, ← C_mul, ← mul_pow, mul_inv_of_self, one_pow, C_1, one_mul] },
  { simp [witt_polynomial, nat.sub_self, finset.sum_range_succ] },
  { intros i h,
    rw finset.mem_range at h,
    simp only [alg_hom.map_mul, alg_hom.map_pow, alg_hom_C, function.comp_app, H i h] },
end

lemma from_W_to_X_basis_comp_from_X_to_W_basis [invertible (p : R)] :
  (from_W_to_X_basis p R).comp (from_X_to_W_basis p _) = alg_hom.id _ _ :=
begin
  apply mv_polynomial.alg_hom_ext R (mv_polynomial ℕ R),
  intro n,
  rw [from_X_to_W_basis, alg_hom.comp_apply, aeval_X],
  exact from_W_to_X_basis_X_in_terms_of_W p R n
end

lemma X_in_terms_of_W_aux [invertible (p : R)] (n : ℕ) :
  X_in_terms_of_W p R n * C (p^n : R) =
  X n - ∑ i in range n, C (p^i : R) * (X_in_terms_of_W p R i)^p^(n-i) :=
by rw [X_in_terms_of_W_eq, mul_assoc, ← C_mul, ← mul_pow, inv_of_mul_self, one_pow, C_1, mul_one]

lemma from_X_to_W_basis_witt_polynomial [invertible (p : R)] (n : ℕ) :
  (from_X_to_W_basis p R) (W n) = X n :=
begin
  rw [witt_polynomial],
  rw [alg_hom.map_sum],
  simp only [alg_hom.map_pow, C_pow, alg_hom.map_mul],
  simp only [from_X_to_W_basis_X, alg_hom_C],
  rw [finset.sum_range_succ, nat.sub_self, nat.pow_zero, pow_one],
  rw [mul_comm, ← C_pow],
  rw X_in_terms_of_W_aux,
  simp only [C_pow, sub_add_cancel],
end

lemma from_X_to_W_basis_comp_from_W_to_X_basis [invertible (p : R)] :
  (from_X_to_W_basis p R).comp (from_W_to_X_basis p _) = alg_hom.id _ _ :=
begin
  apply mv_polynomial.alg_hom_ext R (mv_polynomial ℕ R),
  intro n,
  rw [alg_hom.comp_apply, from_W_to_X_basis_X],
  exact from_X_to_W_basis_witt_polynomial p R n,
end

@[simp] lemma from_X_to_W_basis_comp_from_W_to_X_basis_apply [invertible (p : R)] (φ : mv_polynomial ℕ R) :
  (from_X_to_W_basis p R) (from_W_to_X_basis p R φ) = φ :=
begin
  rw [← alg_hom.comp_apply, from_X_to_W_basis_comp_from_W_to_X_basis, alg_hom.id_apply],
end

@[simp] lemma from_W_to_X_basis_comp_from_X_to_W_basis_apply [invertible (p : R)] (φ : mv_polynomial ℕ R) :
  (from_W_to_X_basis p R) (from_X_to_W_basis p R φ) = φ :=
begin
  rw [← alg_hom.comp_apply, from_W_to_X_basis_comp_from_X_to_W_basis, alg_hom.id_apply],
end

@[simp] lemma X_in_terms_of_W_prop₂ [invertible (p : R)] (k : ℕ) :
  aeval (X_in_terms_of_W p R) (W_ R k) = X k :=
begin
  rw ← from_X_to_W_basis_comp_from_W_to_X_basis_apply p R (X k),
  rw from_W_to_X_basis_X,
  refl,
end

@[simp] lemma X_in_terms_of_W_prop [invertible (p : R)] (n : ℕ) :
  aeval (W_ R) (X_in_terms_of_W p R n) = X n :=
begin
  rw ← from_W_to_X_basis_comp_from_X_to_W_basis_apply p R (X n),
  rw from_X_to_W_basis_X,
  refl,
end

noncomputable def witt.alg_equiv [invertible (p : R)] : mv_polynomial ℕ R ≃ₐ[R] mv_polynomial ℕ R :=
equiv_of_family (W_ R) (X_in_terms_of_W p R)
(X_in_terms_of_W_prop₂ p R)
(X_in_terms_of_W_prop p R)

variables {idx : Type*} [fact p.prime]

noncomputable def witt_structure_rat (Φ : mv_polynomial idx ℚ) (n : ℕ) :
  mv_polynomial (idx × ℕ) ℚ :=
aeval (λ k : ℕ, (aeval (λ b, (rename_hom (λ i, (b,i)) (W_ ℚ k)))) Φ) (X_in_terms_of_W p ℚ n)

theorem witt_structure_rat_prop (Φ : mv_polynomial idx ℚ) (n : ℕ) :
  aeval (witt_structure_rat p Φ) (W_ ℚ n) = aeval (λ b, (rename_hom (λ i, (b,i)) (W_ ℚ n))) Φ :=
calc aeval (witt_structure_rat p Φ) (W_ ℚ n) =
      aeval (λ k, aeval (λ b, (rename_hom (prod.mk b)) (W_ ℚ k)) Φ)
        (aeval (X_in_terms_of_W p ℚ) (W_ ℚ n)) :
      by { conv_rhs { rw [aeval_eq_eval₂_hom', map_aeval] },
           apply eval₂_hom_congr (ring_hom.ext_rat _ _) rfl rfl }
... = aeval (λ b, (rename_hom (λ i, (b,i)) (W_ ℚ n))) Φ :
      by rw [X_in_terms_of_W_prop₂ p _ n, aeval_X]

theorem witt_structure_prop_exists_unique (Φ : mv_polynomial idx ℚ) :
  ∃! (φ : ℕ → mv_polynomial (idx × ℕ) ℚ),
    ∀ (n : ℕ), aeval φ (W_ ℚ n) = aeval (λ b, (rename_hom (λ i, (b,i)) (W_ ℚ n))) Φ :=
begin
  refine ⟨witt_structure_rat p Φ, _, _⟩,
  { intro n, apply witt_structure_rat_prop },
  { intros φ H,
    funext n,
    rw show φ n = aeval φ (aeval (W_ ℚ) (X_in_terms_of_W p ℚ n)),
    { rw [X_in_terms_of_W_prop p, aeval_X] },
    rw [aeval_eq_eval₂_hom', map_aeval],
    apply eval₂_hom_congr (ring_hom.ext_rat _ _) _ rfl,
    funext k, exact H k },
end

lemma witt_structure_rat_rec_aux (Φ : mv_polynomial idx ℚ) (n) :
  (witt_structure_rat p Φ n) * C (p^n : ℚ) =
  ((aeval (λ b, (rename_hom (λ i, (b,i)) (W_ ℚ n))) Φ)) -
  ∑ i in range n, C (p^i : ℚ) * (witt_structure_rat p Φ i)^p^(n-i) :=
begin
  have := X_in_terms_of_W_aux p ℚ n,
  replace := congr_arg (aeval (λ k : ℕ, (aeval (λ b, (rename_hom (λ i, (b,i)) (W_ ℚ k)))) Φ)) this,
  rw [alg_hom.map_mul, aeval_C] at this,
  convert this, clear this,
  conv_rhs { simp only [alg_hom.map_sub, aeval_X] },
  rw sub_right_inj,
  rw [alg_hom.map_sum, finset.sum_congr rfl],
  intros i hi,
  rw [alg_hom.map_mul, aeval_C, alg_hom.map_pow],
  refl
end

lemma witt_structure_rat_rec (Φ : mv_polynomial idx ℚ) (n) :
  (witt_structure_rat p Φ n) = C (1/p^n : ℚ) *
  (aeval (λ b, (rename_hom (λ i, (b,i)) (W_ ℚ n))) Φ -
  ∑ i in range n, C (p^i : ℚ) * (witt_structure_rat p Φ i)^p^(n-i)) :=
begin
  rw [← witt_structure_rat_rec_aux p Φ n, mul_comm, mul_assoc,
      ← C_mul, mul_one_div_cancel, C_1, mul_one],
  exact pow_ne_zero _ (nat.cast_ne_zero.2 $ ne_of_gt (nat.prime.pos ‹_›)),
end

noncomputable def witt_structure_int (Φ : mv_polynomial idx ℤ) (n : ℕ) : mv_polynomial (idx × ℕ) ℤ :=
finsupp.map_range rat.num (rat.coe_int_num 0)
  (witt_structure_rat p (map_hom (int.cast_ring_hom ℚ) Φ) n)
.

lemma mv_polynomial.coe_int_rat_map_injective (I : Type*) :
  function.injective (map_hom (int.cast_ring_hom ℚ) : mv_polynomial I ℤ → mv_polynomial I ℚ) :=
begin
  apply map_injective,
  intros m n,
  exact int.cast_inj.mp
end
.

lemma sub_congr (a b c d : R) (h1 : a = c) (h2 : b = d) : a - b = c - d :=
by rw [h1, h2]
.

variables {ι : Type*} {σ : Type*}
variables {S : Type*} [comm_ring S]
variables {T : Type*} [comm_ring T]

lemma foo' (Φ : mv_polynomial idx ℤ) (n : ℕ)
  (IH : ∀ m : ℕ, m < n →
    map_hom (int.cast_ring_hom ℚ) (witt_structure_int p Φ m) =
    witt_structure_rat p (map_hom (int.cast_ring_hom ℚ) Φ) m) :
  map_hom (int.cast_ring_hom ℚ)
    (((aeval (λ b, (rename_hom (λ i, (b,i)) (W_ ℤ n)))) Φ) -
      (∑ i in range n, C (p^i : ℤ) * (witt_structure_int p Φ i)^p^(n-i))) =
  aeval (λ b, (rename_hom (λ i, (b,i)) (W_ ℚ n)))
   (map_hom (int.cast_ring_hom ℚ) Φ) -
  (∑ i in range n, C (p^i : ℚ) * (witt_structure_rat p (map_hom (int.cast_ring_hom ℚ) Φ) i)^p^(n-i)) :=
begin
  rw [ring_hom.map_sub, ring_hom.map_sum],
  apply sub_congr,
  { clear IH,
    rw [map_aeval, aeval_eq_eval₂_hom', eval₂_hom_map_hom],
    apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
    funext k, rw [map_hom_rename_hom, map_hom_witt_polynomial] },
  { apply finset.sum_congr rfl,
    intros i hi,
    rw finset.mem_range at hi,
    specialize IH i hi,
    simp only [IH, int.cast_coe_nat, ring_hom.eq_int_cast, C_pow,
      ring_hom.map_pow, map_hom_C, ring_hom.map_mul],
    simp only [ring_hom.map_nat_cast], }
end

@[simp] lemma witt_polynomial_zmod_self (n : ℕ) :
  W_ (zmod (p^(n+1))) (n + 1) = aeval (λ i, ((X i)^p)) (W_ (zmod (p^(n+1))) n) :=
begin
  delta witt_polynomial,
  rw [finset.sum_range_succ, ← nat.cast_pow,
      char_p.cast_eq_zero (zmod (p^(n+1))) (p^(n+1)),
      C_0, zero_mul, zero_add],
  rw [alg_hom.map_sum, finset.sum_congr rfl],
  intros k hk,
  rw [alg_hom.map_mul, alg_hom.map_pow, aeval_X, alg_hom_C],
  rw [← pow_mul, mul_comm p, ← nat.pow_succ, nat.succ_eq_add_one],
  congr,
  rw finset.mem_range at hk,
  omega
end

@[simp] lemma frobenius_zmod (p : ℕ) [hp : fact p.prime] (a : zmod p) :
  frobenius _ p a = a :=
begin
  have ppos : p > 0 := nat.prime.pos ‹_›,
  by_cases h : a = 0,
  { subst a, apply zero_pow ppos },
  { have := zmod.fermat_little p h,
    replace := congr_arg (λ x, a * x) this,
    simp at this,
    convert this,
    rw [← pow_succ, frobenius_def], congr, clear this h a hp,
    revert ppos p, omega manual nat }
end

lemma fermat_little' (p : ℕ) [hp : fact p.prime] (a : zmod p) : a^p = a :=
frobenius_zmod p a

lemma mv_polynomial.frobenius_zmod (φ : mv_polynomial σ (zmod p)) :
  frobenius _ p φ = aeval (λ i, X i ^ p) φ :=
begin
  apply induction_on φ,
  { intro a, rw [aeval_C, frobenius_def, ← C_pow, fermat_little'], refl },
  { simp only [alg_hom.map_add, ring_hom.map_add], intros _ _ hf hg, rw [hf, hg] },
  { simp only [aeval_X, ring_hom.map_mul, alg_hom.map_mul],
    intros _ _ hf, rw [hf, frobenius_def], },
end

lemma mv_polynomial.zmod_pow_char (φ : mv_polynomial ι (zmod p)) :
  (aeval (λ i, (X i)^p)) φ = φ^p :=
begin
  symmetry,
  apply mv_polynomial.frobenius_zmod
end

lemma rat_mv_poly_is_integral_iff (p : mv_polynomial ι ℚ) :
  map (int.cast_ring_hom ℚ) (finsupp.map_range rat.num (rat.coe_int_num 0) p) = p ↔
  ∀ m, (coeff m p).denom = 1 :=
begin
  rw mv_polynomial.ext_iff,
  apply forall_congr, intro m,
  rw coeff_map,
  split; intro h,
  { rw [← h], apply rat.coe_int_denom },
  { show (rat.num (coeff m p) : ℚ) = coeff m p,
    lift (coeff m p) to ℤ using h with n hn,
    rw rat.coe_int_num n }
end

lemma mv_polynomial.algebra_map_eq_C (r : R) :
  algebra_map R (mv_polynomial σ R) r = C r :=
rfl

lemma blur' (Φ : mv_polynomial idx ℤ) (n : ℕ)
  (IH : ∀ m : ℕ, m < (n + 1) →
    map_hom (int.cast_ring_hom ℚ) (witt_structure_int p Φ m) =
      witt_structure_rat p (map_hom (int.cast_ring_hom ℚ) Φ) m) :
  aeval (λ b, rename_hom (λ i, (b, i)) (aeval (λ i, ((X i ^ p : mv_polynomial ℕ ℤ))) (W_ ℤ n))) Φ =
  aeval (λ i, aeval (λ bi, (X bi)^p) (witt_structure_int p Φ i)) (W_ ℤ n) :=
begin
  have aux := λ x, aeval_X ℤ _ (witt_structure_int p Φ) x,
  have aux₂ : ∀ n : ℕ, (algebra_map ℚ (mv_polynomial (idx × ℕ) ℚ)) (p ^ n) =
    map_hom (int.cast_ring_hom ℚ) (aeval (witt_structure_int p Φ) (C (p ^ n : ℤ))),
  { intro n, rw [map_aeval, eval₂_hom_C, ring_hom.eq_int_cast, mv_polynomial.algebra_map_eq_C],
    rw [C_pow, C_eq_coe_nat], norm_cast, },
  have key := (witt_structure_rat_prop p (map_hom (int.cast_ring_hom ℚ) Φ) n).symm,
  conv_rhs at key
  { rw [witt_polynomial, alg_hom.map_sum],
    conv {
      apply_congr, skip,
      rw [alg_hom.map_mul, alg_hom.map_pow, aeval_C, aeval_X],
      rw [← IH x (finset.mem_range.mp H)],
      rw [← aux, aux₂],
      rw [← ring_hom.map_pow, ← alg_hom.map_pow, ← ring_hom.map_mul, ← alg_hom.map_mul], },
    rw [← ring_hom.map_sum, ← alg_hom.map_sum], },
  replace key := congr_arg (aeval (λ bi, (X bi ^ p : mv_polynomial (idx × ℕ) ℚ))) key,

  apply mv_polynomial.coe_int_rat_map_injective,

  calc _ = _ : _
     ... = _ : key
     ... = _ : _,

  { clear IH aux aux₂ key,
    simp only [map_aeval, map_eval₂_hom, aeval_eq_eval₂_hom', ring_hom.map_pow, eval₂_hom_map_hom,
      eval₂_hom_rename_hom, ← map_hom_witt_polynomial p (int.cast_ring_hom ℚ)],
    apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
    funext i,
    apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
    funext k,
    rw [map_hom_rename_hom, map_hom_X, rename_hom_X] },
  { simp only [map_aeval, map_eval₂_hom, aeval_eq_eval₂_hom', ring_hom.map_pow,
      eval₂_hom_map_hom, witt_polynomial, int.nat_cast_eq_coe_nat],
    apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
    funext i,
    apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
    funext bi, rw map_hom_X }
end
.

lemma map_hom_witt_structure_int (Φ : mv_polynomial idx ℤ) (n : ℕ) :
  map_hom (int.cast_ring_hom ℚ) (witt_structure_int p Φ n) =
    witt_structure_rat p (map_hom (int.cast_ring_hom ℚ) Φ) n :=
begin
  apply nat.strong_induction_on n, clear n,
  intros n IH,
  erw rat_mv_poly_is_integral_iff,
  intro c,
  rw witt_structure_rat_rec p _ n,
  rw coeff_C_mul,
  rw [mul_comm, mul_div_assoc', mul_one],
  rw ← foo' p Φ n IH,
  erw coeff_map,
  rw show (p : ℚ)^n = ((p^n : ℕ) : ℤ), by norm_cast,
  erw rat.denom_div_cast_eq_one_iff,
  swap,
  { rw int.coe_nat_pow, apply pow_ne_zero, exact_mod_cast ne_of_gt (nat.prime.pos ‹_›) },
  induction n with n ih, {simp}, clear ih, revert c,
  rw [← C_dvd_iff_dvd_coeff, nat.succ_eq_add_one],
  rw C_dvd_iff_zmod,
  -- rw ← eq_mod_iff_dvd_sub',
  rw [ring_hom.map_sub, sub_eq_zero, map_aeval],
  simp only [witt_polynomial_zmod_self, map_aeval, map_hom_witt_polynomial,
    map_hom_rename_hom, ring_hom.map_pow, rename_hom_X],

  have key := congr_arg (map_hom (int.cast_ring_hom (zmod (p^(n+1))))) (blur' p Φ n IH),

  calc _ = _ : _
     ... = _ : key
     ... = _ : _,

  { clear key IH,
    rw map_aeval,
    apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
    funext i,
    rw ← map_hom_witt_polynomial p (int.cast_ring_hom (zmod _)) n,
    simp only [map_hom_X, map_aeval, map_eval₂_hom, ring_hom.map_pow,
      rename_hom_X, eval₂_hom_map_hom],
    apply eval₂_hom_congr (ring_hom.ext_int _ _) rfl rfl, },

  { clear key IH,
    rw [aeval_witt_polynomial, ring_hom.map_sum, ring_hom.map_sum],
    apply finset.sum_congr rfl,
    intros k hk, rw finset.mem_range at hk,
    rw [← sub_eq_zero, ← ring_hom.map_sub, ← C_dvd_iff_zmod],
    rw [← int.nat_cast_eq_coe_nat, C_eq_coe_nat],
    rw [← int.nat_cast_eq_coe_nat, C_eq_coe_nat, ← mul_sub],
    rw show p^(n+1) = p^k * p^(n-k+1),
    { rw ← nat.pow_add, congr' 1, omega },
    rw [nat.cast_mul, nat.cast_pow, nat.cast_pow],
    apply mul_dvd_mul_left,
    rw show p^(n+1-k) = p * p^(n-k),
    { rw [mul_comm, ← nat.pow_succ], congr' 1, omega },
    rw [pow_mul],
    -- the machine!
    apply dvd_sub_pow_of_dvd_sub,

    rw [← C_eq_coe_nat, int.nat_cast_eq_coe_nat, C_dvd_iff_zmod],
    rw [ring_hom.map_sub, sub_eq_zero, ring_hom.map_pow, ← mv_polynomial.zmod_pow_char],
    rw [map_aeval, aeval_eq_eval₂_hom', eval₂_hom_map_hom],
    apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
    { funext i, rw [ring_hom.map_pow, map_hom_X] } }
end
.

theorem witt_structure_int_prop (Φ : mv_polynomial idx ℤ) (n) :
  aeval (witt_structure_int p Φ) (W_ ℤ n) = aeval (λ b, (rename_hom (λ i, (b,i)) (W_ ℤ n))) Φ :=
begin
  apply mv_polynomial.coe_int_rat_map_injective,
  convert witt_structure_rat_prop p (map_hom (int.cast_ring_hom ℚ) Φ) n,
  { rw [map_aeval, aeval_eq_eval₂_hom',
        ← map_hom_witt_polynomial p (int.cast_ring_hom ℚ), eval₂_hom_map_hom],
    apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
    funext i, apply map_hom_witt_structure_int },
  { rw [map_aeval, aeval_eq_eval₂_hom', eval₂_hom_map_hom],
    apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
    funext b, rw [map_hom_rename_hom, map_hom_witt_polynomial] }
end

theorem witt_structure_int_exists_unique (Φ : mv_polynomial idx ℤ) :
  ∃! (φ : ℕ → mv_polynomial (idx × ℕ) ℤ),
  ∀ (n : ℕ), aeval φ (W_ ℤ n) = aeval (λ b : idx, (rename_hom (λ i, (b,i)) (W_ ℤ n))) Φ :=
begin
  refine ⟨witt_structure_int p Φ, _, _⟩,
  { apply witt_structure_int_prop },
  { intros φ H,
    funext k,
    apply mv_polynomial.coe_int_rat_map_injective,
    rw map_hom_witt_structure_int,
    refine congr_fun _ k,
    have := (witt_structure_prop_exists_unique p (map_hom (int.cast_ring_hom ℚ) Φ)),
    apply unique_of_exists_unique this,
    { clear this, intro n,
      specialize H n,
      convert congr_arg (map_hom (int.cast_ring_hom ℚ)) H using 1,
      { rw [map_aeval, ← map_hom_witt_polynomial p (int.cast_ring_hom ℚ),
        aeval_eq_eval₂_hom', eval₂_hom_map_hom],
        exact eval₂_hom_congr (ring_hom.ext_int _ _) rfl rfl },
      { rw [map_aeval, aeval_eq_eval₂_hom', eval₂_hom_map_hom],
        apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
        funext i, rw [map_hom_rename_hom, map_hom_witt_polynomial] } },
    { intro n, apply witt_structure_rat_prop } },
end
.

theorem witt_structure_prop (Φ : mv_polynomial idx ℤ) (n) :
  aeval (λ i, map_hom (int.cast_ring_hom R) (witt_structure_int p Φ i)) (W_ ℤ n) =
  aeval (λ b, (rename_hom (λ i, (b,i)) (W n))) Φ :=
begin
  convert congr_arg (map_hom (int.cast_ring_hom R)) (witt_structure_int_prop p Φ n),
  { rw [aeval_eq_eval₂_hom', map_aeval],
    exact eval₂_hom_congr (ring_hom.ext_int _ _) rfl rfl },
  { rw [aeval_eq_eval₂_hom', map_aeval],
    apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
    simp only [map_hom_rename_hom, map_hom_witt_polynomial] }
end

namespace witt_vectors

local notation `𝕎` := witt_vectors -- type as `\bbW`

instance : functor (𝕎 p) :=
{ map := λ α β f v, f ∘ v,
  map_const := λ α β a v, λ _, a }

instance : is_lawful_functor (𝕎 p) :=
{ map_const_eq := λ α β, rfl,
  id_map := λ α v, rfl,
  comp_map := λ α β γ f g v, rfl }

variable (R)

instance : has_zero (𝕎 p R) :=
⟨λ _, 0⟩

variable {R}

def Teichmuller (r : R) : 𝕎 p R
| 0 := r
| (n+1) := 0

@[simp] lemma Teichmuller_zero : Teichmuller p (0:R) = 0 :=
funext $ λ n, match n with | 0 := rfl | (n+1) := rfl end

variable (R)

instance : has_one (𝕎 p R) :=
⟨Teichmuller p 1⟩

noncomputable def witt_add : ℕ → mv_polynomial (bool × ℕ) ℤ :=
witt_structure_int p (X tt + X ff)

noncomputable def witt_mul : ℕ → mv_polynomial (bool × ℕ) ℤ :=
witt_structure_int p (X tt * X ff)

noncomputable def witt_neg : ℕ → mv_polynomial (unit × ℕ) ℤ :=
witt_structure_int p (-X unit.star)

noncomputable instance : has_add (𝕎 p R) :=
⟨λ x y n, aeval (λ bn : bool × ℕ, cond bn.1 (x bn.2) (y bn.2)) (witt_add p n)⟩

noncomputable instance : has_mul (𝕎 p R) :=
⟨λ x y n, aeval (λ bn : bool × ℕ, cond bn.1 (x bn.2) (y bn.2)) (witt_mul p n)⟩

noncomputable instance : has_neg (𝕎 p R) :=
⟨λ x n, aeval (λ n : unit × ℕ, x n.2) (witt_neg p n)⟩

variable {R}

@[simp] lemma Teichmuller_one : Teichmuller p (1:R) = 1 := rfl

variable {p}

noncomputable def ghost_component (n : ℕ) (w : 𝕎 p R) : R :=
aeval w (W_ R n)

section map
open function
variables {α : Type*} {β : Type*}

def map (f : α → β) : 𝕎 p α → 𝕎 p β := λ w, f ∘ w

lemma map_injective (f : α → β) (hf : injective f) :
  injective (map f : 𝕎 p α → 𝕎 p β) :=
λ x y h, funext $ λ n, hf $ by exact congr_fun h n

lemma map_surjective (f : α → β) (hf : surjective f) :
  surjective (map f : 𝕎 p α → 𝕎 p β) :=
λ x, ⟨λ n, classical.some $ hf $ x n,
by { funext n, dsimp [map], rw classical.some_spec (hf (x n)) }⟩

variables (f : R →+* S)

@[simp] lemma map_zero : map f (0 : 𝕎 p R) = 0 :=
funext $ λ n, f.map_zero

@[simp] lemma map_one : map f (1 : 𝕎 p R) = 1 :=
funext $ λ n,
match n with
| 0     := f.map_one
| (n+1) := f.map_zero
end

@[simp] lemma map_add (x y : 𝕎 p R) :
  map f (x + y) = map f x + map f y :=
begin
  funext n,
  show f (aeval _ _) = aeval _ _,
  rw map_aeval,
  apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
  { funext bn, rcases bn with ⟨⟨⟩, i⟩; refl, }
end

@[simp] lemma map_mul (x y : 𝕎 p R) :
  map f (x * y) = map f x * map f y :=
begin
  funext n,
  show f (aeval _ _) = aeval _ _,
  rw map_aeval,
  apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
  { funext bn, rcases bn with ⟨⟨⟩, i⟩; refl, }
end

@[simp] lemma map_neg (x : 𝕎 p R) :
  map f (-x) = -map f x :=
begin
  funext n,
  show f (aeval _ _) = aeval _ _,
  rw map_aeval,
  apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
  { funext bn, rcases bn with ⟨⟨⟩, i⟩; refl, }
end

end map

noncomputable def ghost_map : 𝕎 p R → (ℕ → R) := λ w n, ghost_component n w

@[simp] lemma ghost_map.zero : ghost_map (0 : 𝕎 p R) = 0 :=
funext $ λ n,
begin
  delta ghost_map ghost_component,
  rw [aeval_witt_polynomial, finset.sum_eq_zero],
  { refl },
  intros i hi,
  convert mul_zero _,
  apply zero_pow _,
  apply nat.pow_pos,
  apply nat.prime.pos, assumption,
end

@[simp] lemma ghost_map.one : ghost_map (1 : 𝕎 p R) = 1 :=
funext $ λ n,
begin
  delta ghost_map ghost_component,
  rw [aeval_witt_polynomial],
  have : 0 ∈ range (n+1),
  { rw finset.mem_range, exact nat.succ_pos n },
  rw ← finset.insert_erase this,
  rw finset.sum_insert (finset.not_mem_erase 0 (range (n + 1))),
  convert add_zero _,
  { apply finset.sum_eq_zero, intros i hi,
    rw finset.mem_erase at hi,
    suffices H : (1 : 𝕎 p R) i = 0,
    { rw [H, zero_pow, mul_zero], apply nat.pow_pos, exact nat.prime.pos ‹_› },
    rw ← Teichmuller_one, cases hi with hi bla, revert hi,
    exact match i with
    | 0 := λ H, false.elim (H rfl)
    | (n+1) := λ H, rfl
    end },
  { dsimp, rw one_mul, symmetry,
    apply one_pow }
end

variable {R}

@[simp] lemma ghost_map.add (x y : 𝕎 p R) :
  ghost_map (x + y) = ghost_map x + ghost_map y :=
funext $ λ n,
begin
  delta ghost_map ghost_component,
  have := congr_arg (λ (ψ : mv_polynomial (bool × ℕ) R), aeval (λ (bn : bool × ℕ), cond bn.1 (x bn.2) (y bn.2)) ψ) (witt_structure_prop p _ (X tt + X ff) n),
  convert this using 1; clear this,
  { delta witt_vectors.has_add witt_add,
    rw ← map_hom_witt_polynomial p (int.cast_ring_hom R),
    simp only [aeval_eq_eval₂_hom', eval₂_hom_map_hom, map_eval₂_hom],
    apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
    funext k,
    exact eval₂_hom_congr (ring_hom.ext_int _ _) rfl rfl },
  { simp only [aeval_eq_eval₂_hom', ring_hom.map_add, eval₂_hom_X', eval₂_hom_rename_hom],
    refl }
end

@[simp] lemma ghost_map.mul (x y : 𝕎 p R) :
  ghost_map (x * y) = ghost_map x * ghost_map y :=
funext $ λ n,
begin
  delta ghost_map ghost_component,
  have := congr_arg (λ (ψ : mv_polynomial (bool × ℕ) R), aeval (λ (bn : bool × ℕ), cond bn.1 (x bn.2) (y bn.2)) ψ) (witt_structure_prop p _ (X tt * X ff) n),
  convert this using 1; clear this,
  { delta witt_vectors.has_mul witt_mul,
    rw ← map_hom_witt_polynomial p (int.cast_ring_hom R),
    simp only [aeval_eq_eval₂_hom', eval₂_hom_map_hom, map_eval₂_hom],
    apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
    funext k,
    exact eval₂_hom_congr (ring_hom.ext_int _ _) rfl rfl },
  { simp only [aeval_eq_eval₂_hom', ring_hom.map_mul, eval₂_hom_X', eval₂_hom_rename_hom],
    refl },
end

@[simp] lemma ghost_map.neg (x : 𝕎 p R) :
  ghost_map (-x) = - ghost_map x :=
funext $ λ n,
begin
  delta ghost_map ghost_component,
  have := congr_arg (λ (ψ : mv_polynomial (unit × ℕ) R), aeval (λ (n : unit × ℕ), (x n.2)) ψ) (witt_structure_prop p _ (-X unit.star) n),
  convert this using 1; clear this,
  { delta witt_vectors.has_neg witt_neg,
    rw ← map_hom_witt_polynomial p (int.cast_ring_hom R),
    simp only [aeval_eq_eval₂_hom', eval₂_hom_map_hom, map_eval₂_hom],
    apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
    funext k,
    exact eval₂_hom_congr (ring_hom.ext_int _ _) rfl rfl },
  { simp only [aeval_eq_eval₂_hom', ring_hom.map_neg, eval₂_hom_X', eval₂_hom_rename_hom],
    refl },
end
.

variables (p) (R)

noncomputable def ghost_map.equiv_of_invertible [invertible (p : R)] :
  𝕎 p R ≃ (ℕ → R) :=
mv_polynomial.comap_equiv (witt.alg_equiv p R)

lemma ghost_map_eq [invertible (p : R)] :
  (ghost_map : 𝕎 p R → ℕ → R) = ghost_map.equiv_of_invertible p R :=
begin
  ext w n,
  dsimp [ghost_map.equiv_of_invertible, witt.alg_equiv],
  rw [aeval_X], refl,
end

lemma ghost_map.bijective_of_invertible [invertible (p : R)] :
  function.bijective (ghost_map : 𝕎 p R → ℕ → R) :=
by { rw ghost_map_eq, exact (ghost_map.equiv_of_invertible p R).bijective }

section
open function

variable (R)

noncomputable def mv_polynomial.counit : mv_polynomial R ℤ →+* R :=
eval₂_hom (int.cast_ring_hom R) id

lemma counit_surjective : surjective (mv_polynomial.counit R) :=
λ r, ⟨X r, eval₂_hom_X' _ _ _⟩

end

local attribute [instance] mv_polynomial.invertible_rat_coe_nat

variable (R)

noncomputable def aux₁ : comm_ring (𝕎 p (mv_polynomial R ℚ)) :=
function.injective.comm_ring (ghost_map)
  (ghost_map.bijective_of_invertible p (mv_polynomial R ℚ)).1
  (ghost_map.zero) (ghost_map.one) (ghost_map.add) (ghost_map.mul) (ghost_map.neg)

local attribute [instance] aux₁

noncomputable def aux₂ : comm_ring (𝕎 p (mv_polynomial R ℤ)) :=
function.injective.comm_ring (map $ mv_polynomial.map_hom (int.cast_ring_hom ℚ))
  (map_injective _ $ mv_polynomial.coe_int_rat_map_injective _)
  (map_zero _) (map_one _) (map_add _) (map_mul _) (map_neg _)

local attribute [instance] aux₂

noncomputable instance : comm_ring (𝕎 p R) :=
function.surjective.comm_ring
  (map $ mv_polynomial.counit _) (map_surjective _ $ counit_surjective _)
  (map_zero _) (map_one _) (map_add _) (map_mul _) (map_neg _)

/-- Teichmuller is a natural transformation -/
@[simp] lemma map_Teichmuller (f : R →+* S) (r : R) :
  map f (Teichmuller p r) = Teichmuller p (f r) :=
by { ext n, cases n, { refl }, { exact f.map_zero } }

@[simp] lemma aeval_Teichmuller_witt_polynomial (r : R) (n : ℕ) :
  aeval (Teichmuller p r) (W_ R n) = r ^ p ^ n :=
begin
  rw aeval_witt_polynomial,
  rw [finset.sum_eq_single 0, pow_zero, one_mul, nat.sub_zero],
  { refl },
  { intros i hi h0,
    convert mul_zero _, convert zero_pow _,
    { cases i, { contradiction }, { refl } },
    { apply nat.pow_pos, apply nat.prime.pos, assumption } },
  { contrapose!, intro, rw finset.mem_range, exact nat.succ_pos n }
end

lemma Teichmuller_mul_aux₁ (x y : mv_polynomial R ℚ) :
  Teichmuller p (x * y) = Teichmuller p x * Teichmuller p y :=
begin
  apply (ghost_map.bijective_of_invertible p (mv_polynomial R ℚ)).1,
  rw ghost_map.mul,
  ext1 n,
  dsimp [ghost_map, ghost_component],
  simp [mul_pow],
end

lemma Teichmuller_mul_aux₂ (x y : mv_polynomial R ℤ) :
  Teichmuller p (x * y) = Teichmuller p x * Teichmuller p y :=
begin
  apply map_injective (map_hom (int.cast_ring_hom ℚ)) (mv_polynomial.coe_int_rat_map_injective _),
  { simp [Teichmuller_mul_aux₁], },
  { assumption } -- map_injective shouldn't have the p.prime assumption
end

@[simp] lemma Teichmuller_mul (x y : R) :
  Teichmuller p (x * y) = Teichmuller p x * Teichmuller p y :=
begin
  rcases counit_surjective R x with ⟨x, rfl⟩,
  rcases counit_surjective R y with ⟨y, rfl⟩,
  simp only [← map_Teichmuller, ← ring_hom.map_mul, Teichmuller_mul_aux₂, map_mul],
end

end witt_vectors

attribute [irreducible] witt_vectors

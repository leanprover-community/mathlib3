/-
2020. No rights reserved. https://unlicense.org/
Authors: Johan Commelin
-/

-- import algebra.inj_surj
import data.nat.choose
import data.int.gcd
import field_theory.mv_polynomial
import data.zmod.basic
import data.fintype.card
import ring_theory.multiplicity
import algebra.invertible
import number_theory.quadratic_reciprocity
import ring_theory.witt_vector.witt_vector_preps
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
open mv_polynomial
open set
open finset (range)
open finsupp (single)

open_locale big_operators

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
∑ i in range (n+1), monomial (single i (p ^ (n - i))) (p ^ i)

lemma witt_polynomial_eq_sum_C_mul_X_pow (n : ℕ) :
  witt_polynomial p R n = ∑ i in range (n+1), C (p ^ i : R) * X i ^ (p ^ (n - i)) :=
begin
  apply finset.sum_congr rfl,
  rintro i -,
  rw [monomial_eq, finsupp.prod_single_index],
  rw pow_zero,
end

/-! We set up notation locally to this file, to keep statements short and comprehensible.
This allows us to simply write `W n` or `W_ ℤ n`. -/

-- Notation with ring of coefficients explicit
localized "notation `W_` := witt_polynomial p"   in witt
-- Notation with ring of coefficients implicit
localized "notation `W`  := witt_polynomial p _" in witt

open_locale witt
open mv_polynomial
/- The first observation is that the Witt polynomial doesn't really depend on the coefficient ring.
If we map the coefficients through a ring homomorphism, we obtain the corresponding Witt polynomial
over the target ring. -/
section
variables {R} {S : Type*} [comm_ring S]

@[simp] lemma map_witt_polynomial (f : R →+* S) (n : ℕ) :
  map f (W n) = W n :=
begin
  rw [witt_polynomial, ring_hom.map_sum],
  apply finset.sum_congr rfl,
  intros i hi,
  rw [map_monomial, ring_hom.map_pow, ring_hom.map_nat_cast],
end

variables (R)

lemma aeval_witt_polynomial {A : Type*} [comm_ring A] [algebra R A] (f : ℕ → A) (n : ℕ) :
  aeval f (W_ R n) = ∑ i in range (n+1), p^i * (f i) ^ (p ^ (n-i)) :=
by simp [witt_polynomial, alg_hom.map_sum, aeval_monomial, finsupp.prod_single_index]

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
  rw [alg_hom.map_mul, alg_hom.map_sub, alg_hom_C, alg_hom.map_sum, from_W_to_X_basis_X],
  -- simp only [from_W_to_X_basis_X p R n, alg_hom.map_sum],
  have : W_ R n - ∑ i in range n, C (p ^ i : R) * (X i) ^ p ^ (n - i) = C (p ^ n : R) * X n,
  by simp only [witt_polynomial_eq_sum_C_mul_X_pow, nat.sub_self, finset.sum_range_succ,
    pow_one, add_sub_cancel, nat.pow_zero],
  rw [finset.sum_congr rfl, this],
  { -- this is really slow for some reason
    rw [mul_right_comm, ← C_mul, ← mul_pow, mul_inv_of_self, one_pow, C_1, one_mul], },
  { intros i h,
    rw finset.mem_range at h,
    simp only [alg_hom.map_mul, alg_hom.map_pow, alg_hom_C, function.comp_app, H i h] },
end

lemma from_W_to_X_basis_comp_from_X_to_W_basis [invertible (p : R)] :
  (from_W_to_X_basis p R).comp (from_X_to_W_basis p _) = alg_hom.id _ _ :=
begin
  apply mv_polynomial.alg_hom_ext,
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
  rw [witt_polynomial_eq_sum_C_mul_X_pow, alg_hom.map_sum],
  simp only [alg_hom.map_pow, C_pow, alg_hom.map_mul, from_X_to_W_basis_X, alg_hom_C],
  rw [finset.sum_range_succ, nat.sub_self, nat.pow_zero, pow_one,
      mul_comm, ← C_pow, X_in_terms_of_W_aux],
  simp only [C_pow, sub_add_cancel],
end

lemma from_X_to_W_basis_comp_from_W_to_X_basis [invertible (p : R)] :
  (from_X_to_W_basis p R).comp (from_W_to_X_basis p _) = alg_hom.id _ _ :=
begin
  apply mv_polynomial.alg_hom_ext,
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

section p_prime

variables {idx : Type*} [fact p.prime]

noncomputable def witt_structure_rat (Φ : mv_polynomial idx ℚ) (n : ℕ) :
  mv_polynomial (idx × ℕ) ℚ :=
bind₁ (λ k : ℕ, (bind₁ (λ b, (rename (λ i, (b,i)) (W_ ℚ k)))) Φ) (X_in_terms_of_W p ℚ n)

theorem witt_structure_rat_prop (Φ : mv_polynomial idx ℚ) (n : ℕ) :
  bind₁ (witt_structure_rat p Φ) (W_ ℚ n) = bind₁ (λ b, (rename (λ i, (b,i)) (W_ ℚ n))) Φ :=
calc aeval (witt_structure_rat p Φ) (W_ ℚ n) =
      aeval (λ k, aeval (λ b, (rename (prod.mk b)) (W_ ℚ k)) Φ)
        (aeval (X_in_terms_of_W p ℚ) (W_ ℚ n)) :
      by { conv_rhs { rw [aeval_eq_eval₂_hom, map_aeval] },
           apply eval₂_hom_congr (ring_hom.ext_rat _ _) rfl rfl }
... = aeval (λ b, (rename (λ i, (b,i)) (W_ ℚ n))) Φ :
      by rw [X_in_terms_of_W_prop₂ p _ n, aeval_X]

theorem witt_structure_prop_exists_unique (Φ : mv_polynomial idx ℚ) :
  ∃! (φ : ℕ → mv_polynomial (idx × ℕ) ℚ),
    ∀ (n : ℕ), bind₁ φ (W_ ℚ n) = bind₁ (λ b, (rename (λ i, (b,i)) (W_ ℚ n))) Φ :=
begin
  refine ⟨witt_structure_rat p Φ, _, _⟩,
  { intro n, apply witt_structure_rat_prop },
  { intros φ H,
    funext n,
    rw show φ n = aeval φ (aeval (W_ ℚ) (X_in_terms_of_W p ℚ n)),
    { rw [X_in_terms_of_W_prop p, aeval_X] },
    rw [aeval_eq_eval₂_hom, map_aeval],
    apply eval₂_hom_congr (ring_hom.ext_rat _ _) _ rfl,
    funext k, exact H k },
end

lemma witt_structure_rat_rec_aux (Φ : mv_polynomial idx ℚ) (n) :
  (witt_structure_rat p Φ n) * C (p^n : ℚ) =
  ((bind₁ (λ b, (rename (λ i, (b,i)) (W_ ℚ n))) Φ)) -
  ∑ i in range n, C (p^i : ℚ) * (witt_structure_rat p Φ i)^p^(n-i) :=
begin
  have := X_in_terms_of_W_aux p ℚ n,
  replace := congr_arg (bind₁ (λ k : ℕ, (bind₁ (λ b, (rename (λ i, (b,i)) (W_ ℚ k)))) Φ)) this,
  rw [alg_hom.map_mul, bind₁_C_right] at this,
  convert this, clear this,
  conv_rhs { simp only [alg_hom.map_sub, bind₁_X_right] },
  rw sub_right_inj,
  simp only [alg_hom.map_sum, alg_hom.map_mul, bind₁_C_right, alg_hom.map_pow],
  refl
end

lemma witt_structure_rat_rec (Φ : mv_polynomial idx ℚ) (n) :
  (witt_structure_rat p Φ n) = C (1/p^n : ℚ) *
  (bind₁ (λ b, (rename (λ i, (b,i)) (W_ ℚ n))) Φ -
  ∑ i in range n, C (p^i : ℚ) * (witt_structure_rat p Φ i)^p^(n-i)) :=
begin
  rw [← witt_structure_rat_rec_aux p Φ n, mul_comm, mul_assoc,
      ← C_mul, mul_one_div_cancel, C_1, mul_one],
  exact pow_ne_zero _ (nat.cast_ne_zero.2 $ ne_of_gt (nat.prime.pos ‹_›)),
end

noncomputable def witt_structure_int (Φ : mv_polynomial idx ℤ) (n : ℕ) : mv_polynomial (idx × ℕ) ℤ :=
finsupp.map_range rat.num (rat.coe_int_num 0)
  (witt_structure_rat p (map (int.cast_ring_hom ℚ) Φ) n)
.

lemma mv_polynomial.coe_int_rat_map_injective (I : Type*) :
  function.injective (map (int.cast_ring_hom ℚ) : mv_polynomial I ℤ → mv_polynomial I ℚ) :=
begin
  apply map_injective,
  intros m n,
  exact int.cast_inj.mp
end
.

end p_prime

lemma sub_congr (a b c d : R) (h1 : a = c) (h2 : b = d) : a - b = c - d :=
by rw [h1, h2]
.

variables {idx : Type*}

variables {ι : Type*} {σ : Type*}
variables {S : Type*} [comm_ring S]
variables {T : Type*} [comm_ring T]

lemma foo [fact p.prime] (Φ : mv_polynomial idx ℤ) (n : ℕ)
  (IH : ∀ m : ℕ, m < n →
    map (int.cast_ring_hom ℚ) (witt_structure_int p Φ m) =
    witt_structure_rat p (map (int.cast_ring_hom ℚ) Φ) m) :
  map (int.cast_ring_hom ℚ)
    (((bind₁ (λ b, (rename (λ i, (b,i)) (W_ ℤ n)))) Φ) -
      (∑ i in range n, C (p^i : ℤ) * (witt_structure_int p Φ i)^p^(n-i))) =
  bind₁ (λ b, (rename (λ i, (b,i)) (W_ ℚ n)))
   (map (int.cast_ring_hom ℚ) Φ) -
  (∑ i in range n, C (p^i : ℚ) * (witt_structure_rat p (map (int.cast_ring_hom ℚ) Φ) i)^p^(n-i)) :=
begin
  rw [ring_hom.map_sub, ring_hom.map_sum],
  apply sub_congr,
  { simp only [map_bind₁, map_rename, map_witt_polynomial], },
  { apply finset.sum_congr rfl,
    intros i hi,
    rw finset.mem_range at hi,
    specialize IH i hi,
    simp only [IH, int.cast_coe_nat, ring_hom.eq_int_cast, ring_hom.map_pow, map_C, ring_hom.map_mul, ring_hom.map_nat_cast], }
end

@[simp] lemma witt_polynomial_zmod_self (n : ℕ) :
  W_ (zmod (p^(n+1))) (n + 1) = expand p (W_ (zmod (p^(n+1))) n) :=
begin
  simp only [witt_polynomial_eq_sum_C_mul_X_pow],
  rw [finset.sum_range_succ, ← nat.cast_pow, char_p.cast_eq_zero (zmod (p^(n+1))) (p^(n+1)),
      C_0, zero_mul, zero_add],
  rw [alg_hom.map_sum, finset.sum_congr rfl],
  intros k hk,
  rw [alg_hom.map_mul, alg_hom.map_pow, expand_X, alg_hom_C, ← pow_mul,
      mul_comm p, ← nat.pow_succ, nat.succ_eq_add_one],
  congr,
  rw finset.mem_range at hk,
  omega
end

@[simp] lemma frobenius_zmod (p : ℕ) [hp : fact p.prime] (a : zmod p) :
  frobenius _ p a = a :=
by rw [frobenius_def, zmod.pow_card]

lemma mv_polynomial.frobenius_zmod [fact p.prime] (φ : mv_polynomial σ (zmod p)) :
  frobenius _ p φ = expand p φ :=
begin
  apply induction_on φ,
  { intro a, rw [expand_C, frobenius_def, ← C_pow, zmod.pow_card], },
  { simp only [alg_hom.map_add, ring_hom.map_add], intros _ _ hf hg, rw [hf, hg] },
  { simp only [expand_X, ring_hom.map_mul, alg_hom.map_mul],
    intros _ _ hf, rw [hf, frobenius_def], },
end

lemma mv_polynomial.expand_zmod [fact p.prime] (φ : mv_polynomial ι (zmod p)) :
  expand p φ = φ^p :=
(mv_polynomial.frobenius_zmod _ _).symm

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

section p_prime

variable [fact p.prime]

lemma xyzzy (n : ℕ) (i : idx) :
  (map (int.cast_ring_hom ℚ))
    ((eval₂_hom ((rename (prod.mk i)).comp (algebra_map.{0 0} ℤ (mv_polynomial ℕ ℤ)))
      (λ (k : ℕ), (rename (prod.mk i)) (X k ^ p)))
        (witt_polynomial p ℤ n)) =
  (eval₂_hom (algebra_map ℚ (mv_polynomial (idx × ℕ) ℚ))
    (λ (bi : idx × ℕ), X bi ^ p))
    ((rename (prod.mk i)) (witt_polynomial p ℚ n)) :=
begin
  rw [map_eval₂_hom, eval₂_hom_rename,
    ← map_witt_polynomial p (int.cast_ring_hom ℚ), eval₂_hom_map_hom],
  apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
  funext k,
  simp only [rename_X, map_X, ring_hom.map_pow],
end

lemma blur (Φ : mv_polynomial idx ℤ) (n : ℕ)
  (IH : ∀ m : ℕ, m < (n + 1) →
    map (int.cast_ring_hom ℚ) (witt_structure_int p Φ m) =
      witt_structure_rat p (map (int.cast_ring_hom ℚ) Φ) m) :
  bind₁ (λ b, rename (λ i, (b, i)) (expand p (W_ ℤ n))) Φ =
  bind₁ (λ i, expand p (witt_structure_int p Φ i)) (W_ ℤ n) :=
begin
  have aux := λ x, @bind₁_X_right _ _ ℤ _ (witt_structure_int p Φ) x,
  have aux₂ : ∀ n : ℕ, C (↑p ^ n) =
    map (int.cast_ring_hom ℚ) (bind₁ (witt_structure_int p Φ) (C (p ^ n : ℤ))),
  { intro n, rw [map_bind₁, map_C, bind₁_C_right, ring_hom.eq_int_cast], norm_cast, },
  have key := (witt_structure_rat_prop p (map (int.cast_ring_hom ℚ) Φ) n).symm,
  conv_rhs at key
  { rw [witt_polynomial_eq_sum_C_mul_X_pow, alg_hom.map_sum],
    conv {
      apply_congr, skip,
      rw [alg_hom.map_mul, alg_hom.map_pow, bind₁_C_right, bind₁_X_right],
      rw [← IH x (finset.mem_range.mp H)],
      rw [← aux, aux₂],
      rw [← ring_hom.map_pow, ← alg_hom.map_pow, ← ring_hom.map_mul, ← alg_hom.map_mul], },
    rw [← ring_hom.map_sum, ← alg_hom.map_sum], },
  apply_fun expand p at key,

  apply mv_polynomial.coe_int_rat_map_injective,

  calc _ = _ : _
     ... = _ : key
     ... = _ : _,

  { clear IH aux aux₂ key,
    simp only [map_bind₁, expand_bind₁, map_rename, map_expand, rename_expand, map_witt_polynomial] },
  { simp only [map_bind₁, expand_bind₁, map_expand, witt_polynomial_eq_sum_C_mul_X_pow, int.nat_cast_eq_coe_nat], }
end

@[simp] lemma map_witt_structure_int (Φ : mv_polynomial idx ℤ) (n : ℕ) :
  map (int.cast_ring_hom ℚ) (witt_structure_int p Φ n) =
    witt_structure_rat p (map (int.cast_ring_hom ℚ) Φ) n :=
begin
  apply nat.strong_induction_on n, clear n,
  intros n IH,
  erw rat_mv_poly_is_integral_iff,
  intro c,
  rw [witt_structure_rat_rec p _ n, coeff_C_mul, mul_comm, mul_div_assoc', mul_one],
  rw ← foo p Φ n IH,
  rw coeff_map,
  rw show (p : ℚ)^n = ((p^n : ℕ) : ℤ), by norm_cast,
  rw [ring_hom.eq_int_cast, rat.denom_div_cast_eq_one_iff],
  swap,
  { rw int.coe_nat_pow, apply pow_ne_zero, exact_mod_cast ne_of_gt (nat.prime.pos ‹_›) },
  induction n with n ih, {simp}, clear ih, revert c,
  rw [← C_dvd_iff_dvd_coeff, nat.succ_eq_add_one],
  rw C_dvd_iff_zmod,
  rw [ring_hom.map_sub, sub_eq_zero, map_bind₁],
  simp only [map_rename, map_witt_polynomial, witt_polynomial_zmod_self],

  have key := congr_arg (map (int.cast_ring_hom (zmod (p^(n+1))))) (blur p Φ n IH),

  calc _ = _ : _
     ... = _ : key
     ... = _ : _,

  { simp only [map_bind₁, map_rename, map_expand, map_witt_polynomial], },

  { clear key IH,
    rw [bind₁, aeval_witt_polynomial, ring_hom.map_sum, ring_hom.map_sum],
    apply finset.sum_congr rfl,
    intros k hk, rw finset.mem_range at hk,
    rw [← sub_eq_zero, ← ring_hom.map_sub, ← C_dvd_iff_zmod],
    rw [← int.nat_cast_eq_coe_nat, C_eq_coe_nat],
    rw [← int.nat_cast_eq_coe_nat, ← nat.cast_pow, ← nat.cast_pow, C_eq_coe_nat, ← mul_sub],
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
    rw [ring_hom.map_sub, sub_eq_zero, ring_hom.map_pow, ← mv_polynomial.expand_zmod],
    rw [map_expand],
   }
end

theorem witt_structure_int_prop (Φ : mv_polynomial idx ℤ) (n) :
  bind₁ (witt_structure_int p Φ) (W_ ℤ n) = bind₁ (λ b, (rename (λ i, (b,i)) (W_ ℤ n))) Φ :=
begin
  apply mv_polynomial.coe_int_rat_map_injective,
  have := witt_structure_rat_prop p (map (int.cast_ring_hom ℚ) Φ) n,
  simpa only [map_bind₁, ← eval₂_hom_map_hom, eval₂_hom_C_left, map_rename,
        map_witt_polynomial, alg_hom.coe_to_ring_hom, map_witt_structure_int],
end

theorem witt_structure_int_exists_unique (Φ : mv_polynomial idx ℤ) :
  ∃! (φ : ℕ → mv_polynomial (idx × ℕ) ℤ),
  ∀ (n : ℕ), bind₁ φ (W_ ℤ n) = bind₁ (λ b : idx, (rename (λ i, (b,i)) (W_ ℤ n))) Φ :=
begin
  refine ⟨witt_structure_int p Φ, _, _⟩,
  { apply witt_structure_int_prop },
  { intros φ H,
    funext k,
    apply mv_polynomial.coe_int_rat_map_injective,
    rw map_witt_structure_int,
    refine congr_fun _ k,
    have := (witt_structure_prop_exists_unique p (map (int.cast_ring_hom ℚ) Φ)),
    apply unique_of_exists_unique this,
    { clear this, intro n,
      specialize H n,
      apply_fun map (int.cast_ring_hom ℚ) at H,
      simpa only [map_bind₁, ← eval₂_hom_map_hom, eval₂_hom_C_left, map_rename,
        map_witt_polynomial, alg_hom.coe_to_ring_hom] using H, },
    { intro n, apply witt_structure_rat_prop } },
end
.
theorem witt_structure_prop (Φ : mv_polynomial idx ℤ) (n) :
  aeval (λ i, map (int.cast_ring_hom R) (witt_structure_int p Φ i)) (W_ ℤ n) =
  aeval (λ b, (rename (λ i, (b,i)) (W n))) Φ :=
begin
  convert congr_arg (map (int.cast_ring_hom R)) (witt_structure_int_prop p Φ n),
  { rw [hom_bind₁],
    exact eval₂_hom_congr (ring_hom.ext_int _ _) rfl rfl, },
  { rw [hom_bind₁],
    apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
    simp only [map_rename, map_witt_polynomial] }
end

end p_prime

namespace witt_vectors

local notation `𝕎` := witt_vectors -- type as `\bbW`

-- do we want to keep these two?
instance : functor (𝕎 p) :=
{ map := λ α β f v, f ∘ v,
  map_const := λ α β a v, λ _, a }

instance : is_lawful_functor (𝕎 p) :=
{ map_const_eq := λ α β, rfl,
  id_map := λ α v, rfl,
  comp_map := λ α β γ f g v, rfl }

section p_prime

variable (R)

variable [fact p.prime]

/-- The polynomial used for defining the element `0` of the ring of Witt vectors. -/
noncomputable def witt_zero : ℕ → mv_polynomial (empty × ℕ) ℤ :=
witt_structure_int p 0

/-- The polynomial used for defining the element `1` of the ring of Witt vectors. -/
noncomputable def witt_one : ℕ → mv_polynomial (empty × ℕ) ℤ :=
witt_structure_int p 1

-- Do we want to use bool, or a custom inductive type with terms l(eft) and r(ight)?
noncomputable def witt_add : ℕ → mv_polynomial (bool × ℕ) ℤ :=
witt_structure_int p (X tt + X ff)

noncomputable def witt_mul : ℕ → mv_polynomial (bool × ℕ) ℤ :=
witt_structure_int p (X tt * X ff)

noncomputable def witt_neg : ℕ → mv_polynomial (unit × ℕ) ℤ :=
witt_structure_int p (-X unit.star)

noncomputable instance : has_zero (𝕎 p R) :=
⟨λ n, aeval (λ p : empty × ℕ, p.1.elim) (witt_zero p n)⟩

noncomputable instance : has_one (𝕎 p R) :=
⟨λ n, aeval (λ p : empty × ℕ, p.1.elim) (witt_one p n)⟩

noncomputable instance : has_add (𝕎 p R) :=
⟨λ x y n, aeval (λ bn : bool × ℕ, cond bn.1 (x bn.2) (y bn.2)) (witt_add p n)⟩

noncomputable instance : has_mul (𝕎 p R) :=
⟨λ x y n, aeval (λ bn : bool × ℕ, cond bn.1 (x bn.2) (y bn.2)) (witt_mul p n)⟩

noncomputable instance : has_neg (𝕎 p R) :=
⟨λ x n, aeval (λ n : unit × ℕ, x n.2) (witt_neg p n)⟩

end p_prime

variables {p} {R}

section map
open function
variables {α : Type*} {β : Type*}

def map_fun (f : α → β) : 𝕎 p α → 𝕎 p β := λ x, f ∘ x

lemma map_fun_injective (f : α → β) (hf : injective f) :
  injective (map_fun f : 𝕎 p α → 𝕎 p β) :=
λ x y h, funext $ λ n, hf $ by exact congr_fun h n

lemma map_fun_surjective (f : α → β) (hf : surjective f) :
  surjective (map_fun f : 𝕎 p α → 𝕎 p β) :=
λ x, ⟨λ n, classical.some $ hf $ x n,
by { funext n, dsimp [map_fun], rw classical.some_spec (hf (x n)) }⟩

variables (f : R →+* S)

/-- Auxiliary tactic for showing that `witt_package.map` respects ring data. -/
meta def witt_map : tactic unit :=
`[funext n,
  show f (aeval _ _) = aeval _ _,
  rw map_aeval,
  apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
  funext p,
  rcases p with ⟨⟨⟩, i⟩; refl]

variable [fact p.prime]

@[simp] lemma map_fun_zero : map_fun f (0 : 𝕎 p R) = 0 :=
by witt_map

@[simp] lemma map_fun_one : map_fun f (1 : 𝕎 p R) = 1 :=
by witt_map

@[simp] lemma map_fun_add (x y : 𝕎 p R) :
  map_fun f (x + y) = map_fun f x + map_fun f y :=
by witt_map

@[simp] lemma map_fun_mul (x y : 𝕎 p R) :
  map_fun f (x * y) = map_fun f x * map_fun f y :=
by witt_map

@[simp] lemma map_fun_neg (x : 𝕎 p R) :
  map_fun f (-x) = -map_fun f x :=
by witt_map

end map

noncomputable def ghost_component (n : ℕ) (x : 𝕎 p R) : R :=
aeval x (W_ ℤ n)

lemma ghost_component_apply (n : ℕ) (x : 𝕎 p R) :
  ghost_component n x = aeval x (W_ ℤ n) := rfl

lemma ghost_component_apply' (n : ℕ) (x : 𝕎 p R) :
  ghost_component n x = aeval x (W_ R n) :=
begin
  simp only [ghost_component_apply, aeval_eq_eval₂_hom,
    ← map_witt_polynomial p (int.cast_ring_hom R), eval₂_hom_map_hom],
  exact eval₂_hom_congr (ring_hom.ext_int _ _) rfl rfl,
end

noncomputable def ghost_map_fun : 𝕎 p R → (ℕ → R) := λ w n, ghost_component n w

end witt_vectors

section tactic
setup_tactic_parser
open tactic
meta def tactic.interactive.ghost_boo (poly fn: parse parser.pexpr) : tactic unit :=
do to_expr ```(witt_structure_int_prop p (%%poly) n) >>= note `aux none >>=
     apply_fun_to_hyp ```(aeval %%fn) none,
`[convert aux using 1; clear aux,
  simp only [aeval_eq_eval₂_hom, eval₂_hom_map_hom, map_eval₂_hom, bind₁];
  apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl;
  funext k;
  exact eval₂_hom_congr (ring_hom.ext_int _ _) rfl rfl,
  all_goals { simp only [aeval_eq_eval₂_hom, ring_hom.map_add, ring_hom.map_one, ring_hom.map_neg,
                         ring_hom.map_mul, eval₂_hom_X', bind₁];
              simp only [coe_eval₂_hom, eval₂_rename];
              refl }]
end tactic

namespace witt_vectors
local notation `𝕎` := witt_vectors -- type as `\bbW`


section p_prime
open finset mv_polynomial function set

variable {p}
variables [comm_ring R] [comm_ring S] [comm_ring T]

@[simp] lemma ghost_map_fun_apply (x : 𝕎 p R) (n : ℕ) :
  ghost_map_fun x n = ghost_component n x := rfl

variable [hp : fact p.prime]
include hp

@[simp] lemma ghost_component_zero (n : ℕ) :
  ghost_component n (0 : 𝕎 p R) = 0 :=
by ghost_boo (0 : mv_polynomial empty ℤ) (λ (p : empty × ℕ), (p.1.elim : R))

@[simp] lemma ghost_component_one (n : ℕ) :
  ghost_component n (1 : 𝕎 p R) = 1 :=
by ghost_boo (1 : mv_polynomial empty ℤ) (λ (p : empty × ℕ), (p.1.elim : R))

variable {R}

@[simp] lemma ghost_component_add (n : ℕ) (x y : 𝕎 p R) :
  ghost_component n (x + y) = ghost_component n x + ghost_component n y :=
by ghost_boo (X tt + X ff) (λ (bn : bool × ℕ), cond bn.1 (x bn.2) (y bn.2))

@[simp] lemma ghost_component_mul (n : ℕ) (x y : 𝕎 p R) :
  ghost_component n (x * y) = ghost_component n x * ghost_component n y :=
by ghost_boo (X tt * X ff) (λ (bn : bool × ℕ), cond bn.1 (x bn.2) (y bn.2))

@[simp] lemma ghost_component_neg (n : ℕ) (x : 𝕎 p R) :
  ghost_component n (-x) = - ghost_component n x :=
by ghost_boo (-X unit.star) (λ (n : unit × ℕ), (x n.2))

variables (R)

@[simp] lemma ghost_map_fun.zero : ghost_map_fun (0 : 𝕎 p R) = 0 :=
by { ext n, simp only [pi.zero_apply, ghost_map_fun_apply, ghost_component_zero], }

@[simp] lemma ghost_map_fun.one : ghost_map_fun (1 : 𝕎 p R) = 1 :=
by { ext n, simp only [pi.one_apply, ghost_map_fun_apply, ghost_component_one], }

variable {R}

@[simp] lemma ghost_map_fun.add (x y : 𝕎 p R) :
  ghost_map_fun (x + y) = ghost_map_fun x + ghost_map_fun y :=
by { ext n, simp only [ghost_component_add, pi.add_apply, ghost_map_fun_apply], }

@[simp] lemma ghost_map_fun.mul (x y : 𝕎 p R) :
  ghost_map_fun (x * y) = ghost_map_fun x * ghost_map_fun y :=
by { ext n, simp only [ghost_component_mul, pi.mul_apply, ghost_map_fun_apply], }

@[simp] lemma ghost_map_fun.neg (x : 𝕎 p R) :
  ghost_map_fun (-x) = - ghost_map_fun x :=
by { ext n, simp only [ghost_component_neg, pi.neg_apply, ghost_map_fun_apply], }

end p_prime

variables (p) (R)

noncomputable def ghost_map_fun.equiv_of_invertible [invertible (p : R)] :
  𝕎 p R ≃ (ℕ → R) :=
mv_polynomial.comap_equiv (witt.alg_equiv p R)

lemma ghost_map_fun_eq [invertible (p : R)] :
  (ghost_map_fun : 𝕎 p R → ℕ → R) = ghost_map_fun.equiv_of_invertible p R :=
begin
  ext w n,
  rw [ghost_map_fun_apply, ghost_component_apply'],
  dsimp [ghost_map_fun.equiv_of_invertible, witt.alg_equiv],
  rw [aeval_X],
end

lemma ghost_map_fun.bijective_of_invertible [invertible (p : R)] :
  function.bijective (ghost_map_fun : 𝕎 p R → ℕ → R) :=
by { rw ghost_map_fun_eq, exact (ghost_map_fun.equiv_of_invertible p R).bijective }

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

variable [hp : fact p.prime]
include hp

private noncomputable def comm_ring_aux₁ : comm_ring (𝕎 p (mv_polynomial R ℚ)) :=
function.injective.comm_ring (ghost_map_fun)
  (ghost_map_fun.bijective_of_invertible p (mv_polynomial R ℚ)).1
  (ghost_map_fun.zero _) (ghost_map_fun.one _) (ghost_map_fun.add) (ghost_map_fun.mul) (ghost_map_fun.neg)

local attribute [instance] comm_ring_aux₁

private noncomputable def comm_ring_aux₂ : comm_ring (𝕎 p (mv_polynomial R ℤ)) :=
function.injective.comm_ring (map_fun $ mv_polynomial.map (int.cast_ring_hom ℚ))
  (map_fun_injective _ $ mv_polynomial.coe_int_rat_map_injective _)
  (map_fun_zero _) (map_fun_one _) (map_fun_add _) (map_fun_mul _) (map_fun_neg _)

local attribute [instance] comm_ring_aux₂

noncomputable instance : comm_ring (𝕎 p R) :=
function.surjective.comm_ring
  (map_fun $ mv_polynomial.counit _) (map_fun_surjective _ $ counit_surjective _)
  (map_fun_zero _) (map_fun_one _) (map_fun_add _) (map_fun_mul _) (map_fun_neg _)

variables {p R}

section map
open function

noncomputable def map (f : R →+* S) : 𝕎 p R →+* 𝕎 p S :=
{ to_fun := map_fun f,
  map_zero' := map_fun_zero f,
  map_one' := map_fun_one f,
  map_add' := map_fun_add f,
  map_mul' := map_fun_mul f }

lemma map_injective (f : R →+* S) (hf : injective f) :
  injective (map f : 𝕎 p R → 𝕎 p S) :=
map_fun_injective f hf

lemma map_surjective (f : R →+* S) (hf : surjective f) :
  surjective (map f : 𝕎 p R → 𝕎 p S) :=
map_fun_surjective f hf

end map

noncomputable def ghost_map : 𝕎 p R →+* ℕ → R :=
{ to_fun := ghost_map_fun,
  map_zero' := ghost_map_fun.zero R,
  map_one' := ghost_map_fun.one R,
  map_add' := ghost_map_fun.add,
  map_mul' := ghost_map_fun.mul }

@[simp] lemma ghost_map_apply (x : 𝕎 p R) (n : ℕ) :
  ghost_map x n = ghost_component n x := rfl

variables (p R)

lemma ghost_map.bijective_of_invertible [invertible (p : R)] :
  function.bijective (ghost_map : 𝕎 p R → ℕ → R) :=
ghost_map_fun.bijective_of_invertible p R


section witt_constant_coeff
-- move this up

@[simp] lemma constant_coeff_X_in_terms_of_W [invertible (p : R)] (n : ℕ) :
  constant_coeff (X_in_terms_of_W p R n) = 0 :=
begin
  apply nat.strong_induction_on n; clear n,
  intros n IH,
  rw [X_in_terms_of_W_eq, mul_comm, ring_hom.map_mul, ring_hom.map_sub, ring_hom.map_sum,
    constant_coeff_C, finset.sum_eq_zero],
  { simp only [constant_coeff_X, sub_zero, mul_zero] },
  { intros m H,
    rw finset.mem_range at H,
    simp only [ring_hom.map_mul, ring_hom.map_pow, constant_coeff_C, IH m H],
    rw [zero_pow, mul_zero],
    apply nat.pow_pos hp.pos, }
end

@[simp] lemma constant_coeff_witt_polynomial (n : ℕ) :
  constant_coeff (witt_polynomial p R n) = 0 :=
begin
  simp only [witt_polynomial, ring_hom.map_sum, constant_coeff_monomial],
  rw [finset.sum_eq_zero],
  rintro i hi,
  rw [if_neg],
  rw [finsupp.single_eq_zero, ← nat.pow_eq_pow],
  apply ne_of_gt,
  apply pow_pos hp.pos
end

-- move this up
@[simp] lemma X_in_terms_of_W_zero [invertible (p : R)] :
  X_in_terms_of_W p R 0 = X 0 :=
by rw [X_in_terms_of_W_eq, finset.range_zero, finset.sum_empty, pow_zero, C_1, mul_one, sub_zero]

section move_this
omit hp

-- move this
variable (σ)
@[simp] lemma constant_coeff_comp_C :
  constant_coeff.comp (C : R →+* mv_polynomial σ R) = ring_hom.id R :=
by { ext, apply constant_coeff_C }

@[simp] lemma constant_coeff_comp_algebra_map :
  constant_coeff.comp (algebra_map R (mv_polynomial σ R)) = ring_hom.id R :=
constant_coeff_comp_C _ _

variable {σ}

@[simp] lemma constant_coeff_rename {τ : Type*} (f : σ → τ) (φ : mv_polynomial σ R) :
  constant_coeff (rename f φ) = constant_coeff φ :=
begin
  apply φ.induction_on,
  { intro a, simp only [constant_coeff_C, rename_C]},
  { intros p q hp hq, simp only [hp, hq, ring_hom.map_add] },
  { intros p n hp, simp only [hp, rename_X, constant_coeff_X, ring_hom.map_mul]}
end

@[simp] lemma constant_coeff_comp_rename {τ : Type*} (f : σ → τ) :
  (constant_coeff : mv_polynomial τ R →+* R).comp (rename f) = constant_coeff :=
by { ext, apply constant_coeff_rename }

end move_this

@[simp]
lemma constant_coeff_witt_structure_rat_zero (Φ : mv_polynomial idx ℚ) :
  constant_coeff (witt_structure_rat p Φ 0) = constant_coeff Φ :=
begin
  rw witt_structure_rat,
  simp only [bind₁, map_aeval, X_in_terms_of_W_zero, aeval_X, constant_coeff_witt_polynomial,
    constant_coeff_rename, constant_coeff_comp_algebra_map],
  exact @aeval_zero' _ _ ℚ _ _ (algebra.id _) Φ,
end

lemma constant_coeff_witt_structure_rat (Φ : mv_polynomial idx ℚ) (h : constant_coeff Φ = 0) (n : ℕ) :
  constant_coeff (witt_structure_rat p Φ n) = 0 :=
begin
  rw witt_structure_rat,
  -- we need `eval₂_hom_zero` but it doesn't exist
  have : (eval₂_hom (ring_hom.id ℚ) (λ (_x : idx), 0)) Φ = constant_coeff Φ :=
    @aeval_zero' _ _ ℚ _ _ (algebra.id _) Φ,
  simp only [this, h, bind₁, map_aeval, constant_coeff_witt_polynomial, constant_coeff_rename,
    constant_coeff_comp_algebra_map],
  conv_rhs { rw ← constant_coeff_X_in_terms_of_W p ℚ n },
  exact @aeval_zero' _ _ ℚ _ _ (algebra.id _) _,
end

section move_this
-- move this
omit hp

lemma constant_coeff_map (f : R →+* S) (φ : mv_polynomial σ R) :
  constant_coeff (mv_polynomial.map f φ) = f (constant_coeff φ) :=
coeff_map f φ 0

lemma constant_coeff_comp_map (f : R →+* S) :
  (constant_coeff : mv_polynomial σ S →+* S).comp (mv_polynomial.map f) = f.comp (constant_coeff) :=
by { ext, apply constant_coeff_map }

end move_this

@[simp]
lemma constant_coeff_witt_structure_int_zero (Φ : mv_polynomial idx ℤ) :
  constant_coeff (witt_structure_int p Φ 0) = constant_coeff Φ :=
begin
  have inj : function.injective (int.cast_ring_hom ℚ),
  { intros m n, exact int.cast_inj.mp, },
  apply inj,
  rw [← constant_coeff_map, map_witt_structure_int,
      constant_coeff_witt_structure_rat_zero, constant_coeff_map],
end

lemma constant_coeff_witt_structure_int (Φ : mv_polynomial idx ℤ) (h : constant_coeff Φ = 0) (n : ℕ) :
  constant_coeff (witt_structure_int p Φ n) = 0 :=
begin
  have inj : function.injective (int.cast_ring_hom ℚ),
  { intros m n, exact int.cast_inj.mp, },
  apply inj,
  rw [← constant_coeff_map, map_witt_structure_int,
      constant_coeff_witt_structure_rat, ring_hom.map_zero],
  rw [constant_coeff_map, h, ring_hom.map_zero],
end

end witt_constant_coeff

section witt_structure_simplifications

@[simp] lemma witt_zero_eq_zero (n : ℕ) : witt_zero p n = 0 :=
begin
  apply mv_polynomial.coe_int_rat_map_injective,
  simp only [witt_zero, witt_structure_rat, bind₁, aeval_zero',
    constant_coeff_X_in_terms_of_W, ring_hom.map_zero,
    alg_hom.map_zero, map_witt_structure_int],
end

@[simp] lemma witt_one_zero_eq_one : witt_one p 0 = 1 :=
begin
  apply mv_polynomial.coe_int_rat_map_injective,
  simp only [witt_one, witt_structure_rat, X_in_terms_of_W_zero, alg_hom.map_one,
    ring_hom.map_one, bind₁_X_right, map_witt_structure_int]
end

@[simp] lemma witt_one_pos_eq_zero (n : ℕ) (hn : 0 < n) : witt_one p n = 0 :=
begin
  apply mv_polynomial.coe_int_rat_map_injective,
  simp only [witt_one, witt_structure_rat, ring_hom.map_zero, alg_hom.map_one,
    ring_hom.map_one, map_witt_structure_int],
  revert hn, apply nat.strong_induction_on n, clear n,
  intros n IH hn,
  rw X_in_terms_of_W_eq,
  simp only [alg_hom.map_mul, alg_hom.map_sub, alg_hom.map_sum, alg_hom.map_pow, bind₁_X_right, bind₁_C_right],
  rw [sub_mul, one_mul],
  rw [finset.sum_eq_single 0],
  { simp only [inv_of_eq_inv, one_mul, inv_pow', nat.sub_zero, ring_hom.map_one, pow_zero],
    simp only [one_pow, one_mul, X_in_terms_of_W_zero, sub_self, bind₁_X_right] },
  { intros i hin hi0,
    rw [finset.mem_range] at hin,
    rw [IH _ hin (nat.pos_of_ne_zero hi0), zero_pow (nat.pow_pos hp.pos _), mul_zero], },
  { rw finset.mem_range, intro, contradiction }
end

-- move this up
@[simp] lemma witt_polynomial_zero : witt_polynomial p R 0 = X 0 :=
by simp only [witt_polynomial, X, finset.sum_singleton, finset.range_one, nat.pow_zero, pow_zero]

@[simp] lemma witt_add_zero : witt_add p 0 = X (tt,0) + X (ff,0) :=
begin
  apply mv_polynomial.coe_int_rat_map_injective,
  simp only [witt_add, witt_structure_rat, alg_hom.map_add, ring_hom.map_add,
    rename_X, X_in_terms_of_W_zero, map_X,
     witt_polynomial_zero, bind₁_X_right, map_witt_structure_int],
end

@[simp] lemma witt_mul_zero : witt_mul p 0 = X (tt,0) * X (ff,0) :=
begin
  apply mv_polynomial.coe_int_rat_map_injective,
  simp only [witt_mul, witt_structure_rat, rename_X, X_in_terms_of_W_zero, map_X,
    witt_polynomial_zero, ring_hom.map_mul,
    bind₁_X_right, alg_hom.map_mul, map_witt_structure_int]

end

@[simp] lemma witt_neg_zero : witt_neg p 0 = - X ((),0) :=
begin
  apply mv_polynomial.coe_int_rat_map_injective,
  simp only [witt_neg, witt_structure_rat, rename_X, X_in_terms_of_W_zero, map_X,
    witt_polynomial_zero, ring_hom.map_neg,
   alg_hom.map_neg, bind₁_X_right, map_witt_structure_int]
end

@[simp] lemma constant_coeff_witt_add (n : ℕ) :
  constant_coeff (witt_add p n) = 0 :=
begin
  apply constant_coeff_witt_structure_int p _ _ n,
  simp only [add_zero, ring_hom.map_add, constant_coeff_X],
end

@[simp] lemma constant_coeff_witt_mul (n : ℕ) :
  constant_coeff (witt_mul p n) = 0 :=
begin
  apply constant_coeff_witt_structure_int p _ _ n,
  simp only [mul_zero, ring_hom.map_mul, constant_coeff_X],
end

@[simp] lemma constant_coeff_witt_neg (n : ℕ) :
  constant_coeff (witt_neg p n) = 0 :=
begin
  apply constant_coeff_witt_structure_int p _ _ n,
  simp only [neg_zero, ring_hom.map_neg, constant_coeff_X],
end

-- not sure if this one is useful
lemma coeff_witt_mul (n : ℕ) (d : bool × ℕ →₀ ℕ) (hd : coeff d (witt_mul p n) ≠ 0)
  (b : bool) (k : ℕ) (hbk : d ⟨b, k⟩ ≠ 0) (b' : bool) :
  d ⟨b', k⟩ ≠ 0 :=
begin
  sorry
end

end witt_structure_simplifications

section witt_vars

-- move this up?
lemma witt_polynomial_vars [char_zero R] (n : ℕ) :
  (witt_polynomial p R n).vars = finset.range (n + 1) :=
begin
  have : ∀ i, (monomial (single i (p ^ (n - i))) (p ^ i : R)).vars = {i},
  { intro i,
    rw vars_monomial_single,
    { rw ← nat.pos_iff_ne_zero,
      apply nat.pow_pos hp.pos },
    { rw [← nat.cast_pow, nat.cast_ne_zero, ← nat.pow_eq_pow],
      apply ne_of_gt,
      apply pow_pos hp.pos i } },
  rw [witt_polynomial, vars_sum_of_disjoint],
  { simp only [this, int.nat_cast_eq_coe_nat, finset.bind_singleton_eq_self], },
  { simp only [this, int.nat_cast_eq_coe_nat],
    intros a b h,
    apply finset.singleton_disjoint.mpr,
    rwa finset.mem_singleton, },
end

lemma witt_polynomial_vars_subset (n : ℕ) :
  (witt_polynomial p R n).vars ⊆ finset.range (n + 1) :=
begin
  rw [← map_witt_polynomial p (int.cast_ring_hom R), ← witt_polynomial_vars p ℤ],
  apply vars_map,
end

-- move this up?
lemma X_in_terms_of_W_vars (n : ℕ) :
  (X_in_terms_of_W p ℚ n).vars = finset.range (n + 1) :=
begin
  have : ∀ i, (monomial (single i (p ^ (n - i))) (p ^ i : ℤ)).vars = {i},
  { intro i,
    rw vars_monomial_single,
    { rw ← nat.pos_iff_ne_zero,
      apply nat.pow_pos hp.pos },
    { apply pow_ne_zero, exact_mod_cast hp.ne_zero } },
  -- rw [vars_sub_of_disjoint], -- unknown id -- added in #4018
  -- also need vars_mul_eq (over integral domains)
  sorry
  -- rw [X_in_terms_of_W_eq, vars_sum_of_disjoint],
  -- { simp only [this, int.nat_cast_eq_coe_nat, finset.bind_singleton_eq_self], },
  -- { simp only [this, int.nat_cast_eq_coe_nat],
  --   intros a b h,
  --   apply finset.singleton_disjoint.mpr,
  --   rwa finset.mem_singleton, },
end

section
omit hp
open_locale classical

variables {R}

lemma vars_rename {τ} (f : σ → τ) (φ : mv_polynomial σ R) :
  (rename f φ).vars ⊆ (φ.vars.image f) :=
begin
  -- I guess a higher level proof might be shorter
  -- should we prove `degrees_rename` first?
  intros i,
  rw [mem_vars, finset.mem_image],
  rintro ⟨d, hd, hi⟩,
  simp only [exists_prop, mem_vars],
  contrapose! hd,
  rw [rename_eq],
  rw [finsupp.not_mem_support_iff],
  simp only [finsupp.map_domain, finsupp.sum_apply, finsupp.single_apply],
  rw [finsupp.sum, finset.sum_eq_zero],
  intros d' hd',
  split_ifs with H, swap, refl,
  subst H,
  rw [finsupp.mem_support_iff, finsupp.sum_apply] at hi,
  contrapose! hi,
  rw [finsupp.sum, finset.sum_eq_zero],
  intros j hj,
  rw [finsupp.single_apply, if_neg],
  apply hd,
  exact ⟨d', hd', hj⟩
end

end

-- we could relax the fintype on `idx`, but then we need to cast from finset to set.
-- for our applications `idx` is always finite.
lemma witt_structure_rat_vars [fintype idx] (Φ : mv_polynomial idx ℚ) (n : ℕ) :
  (witt_structure_rat p Φ n).vars ⊆ finset.univ.product (finset.range (n + 1)) :=
begin
  rw witt_structure_rat,
  intros x hx,
  simp only [finset.mem_product, true_and, finset.mem_univ, finset.mem_range],
  have hx' := bind₁_vars _ _ hx,
  simp only [X_in_terms_of_W_vars] at hx',
  simp only [exists_prop, finset.mem_bind, finset.mem_range] at hx',
  rcases hx' with ⟨k, hk, hx''⟩,
  have hx''' := bind₁_vars _ _ hx'',
  simp only [exists_prop, finset.mem_bind, finset.mem_range] at hx''',
  rcases hx''' with ⟨i, -, H⟩,
  have H' := vars_rename _ _ H,
  rw [finset.mem_image] at H',
  rcases H' with ⟨j, hj, rfl⟩,
  rw [witt_polynomial_vars, finset.mem_range] at hj,
  exact lt_of_lt_of_le hj hk,
end

-- we could relax the fintype on `idx`, but then we need to cast from finset to set.
-- for our applications `idx` is always finite.
lemma witt_structure_int_vars [fintype idx] (Φ : mv_polynomial idx ℤ) (n : ℕ) :
  (witt_structure_int p Φ n).vars ⊆ finset.univ.product (finset.range (n + 1)) :=
begin
  rw [← @vars_map_of_injective _ _ _ _ _ _ (int.cast_ring_hom ℚ) (λ m n, (rat.coe_int_inj m n).mp),
      map_witt_structure_int],
  apply witt_structure_rat_vars,
end

lemma witt_add_vars (n : ℕ) :
  (witt_add p n).vars ⊆ finset.univ.product (finset.range (n + 1)) :=
witt_structure_int_vars _ _ _

lemma witt_mul_vars (n : ℕ) :
  (witt_mul p n).vars ⊆ finset.univ.product (finset.range (n + 1)) :=
witt_structure_int_vars _ _ _

lemma witt_neg_vars (n : ℕ) :
  (witt_neg p n).vars ⊆ finset.univ.product (finset.range (n + 1)) :=
witt_structure_int_vars _ _ _

end witt_vars

section coeff
/-! ## Witt coefficients

I don't know a name for this map in the literature. But coefficient seems ok.
-/

omit hp
variables {p R}

def coeff (n : ℕ) (x : 𝕎 p R) : R := x n

@[ext]
lemma ext {x y : 𝕎 p R} (h : ∀ n, x.coeff n = y.coeff n) : x = y :=
funext $ λ n, h n

lemma ext_iff {x y : 𝕎 p R} : x = y ↔ ∀ n, x.coeff n = y.coeff n :=
⟨λ h n, by rw h, ext⟩

include hp
variables (p R)

@[simp] lemma zero_coeff (n : ℕ) : (0 : 𝕎 p R).coeff n = 0 :=
show (aeval _ (witt_zero p n) : R) = 0,
by simp only [witt_zero_eq_zero, alg_hom.map_zero]

@[simp] lemma one_coeff_zero : (1 : 𝕎 p R).coeff 0 = 1 :=
show (aeval _ (witt_one p 0) : R) = 1,
by simp only [witt_one_zero_eq_one, alg_hom.map_one]

@[simp] lemma one_coeff_pos (n : ℕ) (hn : 0 < n) : coeff n (1 : 𝕎 p R) = 0 :=
show (aeval _ (witt_one p n) : R) = 0,
by simp only [hn, witt_one_pos_eq_zero, alg_hom.map_zero]

lemma add_coeff (x y : 𝕎 p R) (n : ℕ) :
  (x + y).coeff n =
  aeval (λ bn : bool × ℕ, cond bn.1 (x.coeff bn.2) (y.coeff bn.2)) (witt_add p n) :=
rfl

lemma mul_coeff (x y : 𝕎 p R) (n : ℕ) :
  (x * y).coeff n =
  aeval (λ bn : bool × ℕ, cond bn.1 (x.coeff bn.2) (y.coeff bn.2)) (witt_mul p n) :=
rfl

lemma neg_coeff (x : 𝕎 p R) (n : ℕ) :
  (-x).coeff n = aeval (λ bn : unit × ℕ, (x.coeff bn.2)) (witt_neg p n) := rfl

end coeff

section ideal

lemma mul_coeff_eq_zero (n : ℕ) (x : 𝕎 p R) {y : 𝕎 p R}
  (hy : y ∈ {x : 𝕎 p R | ∀ (i : ℕ), i ≤ n → coeff i x = 0}) :
  (x * y).coeff n = 0 :=
begin
  sorry,
end

noncomputable def ideal (n : ℕ) : ideal (𝕎 p R) :=
{ carrier := {x | ∀ i < n, x.coeff i = 0},
  zero_mem' := by { intros i hi, rw zero_coeff },
  add_mem' :=
  begin
    intros x y hx hy i hi,
    rw [add_coeff, aeval_eq_constant_coeff_of_vars, constant_coeff_witt_add, ring_hom.map_zero],
    rintro ⟨⟨⟩, k⟩ hk,
    all_goals
    { replace hk := witt_add_vars p i hk,
      simp only [true_and, and_true, false_or, or_false, eq_self_iff_true, fintype.univ_bool,
        finset.mem_insert, finset.mem_singleton, finset.mem_range, finset.mem_product] at hk,
      apply_assumption,
      exact lt_of_lt_of_le hk hi }
  end,
  smul_mem' :=
  begin
    intros x y hy i hi,
    rw [smul_eq_mul],
    apply mul_coeff_eq_zero,
    intros j hj,
    apply hy _ (lt_of_le_of_lt hj hi),
  end }

end ideal

section teichmuller
/-! ## Teichmüller lifts -/

variable {R}

omit hp

def teichmuller_fun (r : R) : 𝕎 p R
| 0 := r
| (n+1) := 0

include hp

private lemma ghost_component_teichmuller_fun (r : R) (n : ℕ) :
  ghost_component n (teichmuller_fun p r) = r ^ p ^ n :=
begin
  rw [ghost_component, aeval_witt_polynomial, finset.sum_eq_single 0, pow_zero, one_mul, nat.sub_zero],
  { refl },
  { intros i hi h0,
    convert mul_zero _, convert zero_pow _,
    { cases i, { contradiction }, { refl } },
    { apply nat.pow_pos, apply nat.prime.pos, assumption } },
  { rw finset.mem_range, intro h, exact (h (nat.succ_pos n)).elim }
end

/-- teichmuller is a natural transformation -/
private lemma map_teichmuller_fun (f : R →+* S) (r : R) :
  map f (teichmuller_fun p r) = teichmuller_fun p (f r) :=
by { ext n, cases n, { refl }, { exact f.map_zero } }

private lemma teichmuller_mul_aux₁ (x y : mv_polynomial R ℚ) :
  teichmuller_fun p (x * y) = teichmuller_fun p x * teichmuller_fun p y :=
begin
  apply (ghost_map.bijective_of_invertible p (mv_polynomial R ℚ)).1,
  rw ring_hom.map_mul,
  ext1 n,
  simp only [pi.mul_apply, ghost_map_apply, ghost_component_teichmuller_fun, mul_pow],
end

private lemma teichmuller_mul_aux₂ (x y : mv_polynomial R ℤ) :
  teichmuller_fun p (x * y) = teichmuller_fun p x * teichmuller_fun p y :=
begin
  refine map_injective (mv_polynomial.map (int.cast_ring_hom ℚ))
    (mv_polynomial.coe_int_rat_map_injective _) _,
  simp only [teichmuller_mul_aux₁, map_teichmuller_fun, ring_hom.map_mul]
end

noncomputable def teichmuller : R →* 𝕎 p R :=
{ to_fun := teichmuller_fun p,
  map_one' :=
  begin
    ext ⟨⟩,
    { rw one_coeff_zero, refl },
    { rw one_coeff_pos _ _ _ (nat.succ_pos n), refl }
  end,
  map_mul' :=
  begin
    intros x y,
    rcases counit_surjective R x with ⟨x, rfl⟩,
    rcases counit_surjective R y with ⟨y, rfl⟩,
    simp only [← map_teichmuller_fun, ← ring_hom.map_mul, teichmuller_mul_aux₂],
  end }

@[simp] lemma teichmuller_coeff_zero (r : R) :
  (teichmuller p r).coeff 0 = r := rfl

@[simp] lemma teichmuller_coeff_pos (r : R) :
  ∀ (n : ℕ) (hn : 0 < n), (teichmuller p r).coeff n = 0
| (n+1) _ := rfl.

@[simp] lemma teichmuller_zero : teichmuller p (0:R) = 0 :=
by ext ⟨⟩; { rw zero_coeff, refl }

/-- teichmuller is a natural transformation -/
@[simp] lemma map_teichmuller (f : R →+* S) (r : R) :
  map f (teichmuller p r) = teichmuller p (f r) :=
map_teichmuller_fun _ _ _

@[simp] lemma ghost_component_teichmuller (r : R) (n : ℕ) :
  ghost_component n (teichmuller p r) = r ^ p ^ n :=
ghost_component_teichmuller_fun _ _ _

end teichmuller

section verschiebung
/-! ## The Verschiebung operator -/

def verschiebung_fun : 𝕎 p R → 𝕎 p R
| x 0     := 0
| x (n+1) := x n

/-- verschiebung is a natural transformation -/
@[simp] lemma map_verschiebung_fun (f : R →+* S) (x : 𝕎 p R) :
  map f (verschiebung_fun p R x) = verschiebung_fun p S (map f x) :=
by { ext ⟨-, -⟩, exact f.map_zero, refl }

@[simp] lemma ghost_component_zero_verschiebung_fun (x : 𝕎 p R) :
  ghost_component 0 (verschiebung_fun p R x) = 0 :=
by simp only [ghost_component, aeval_witt_polynomial, verschiebung_fun,
    pow_one, finset.sum_singleton, finset.range_one, nat.pow_zero, mul_zero]

@[simp] lemma ghost_component_verschiebung_fun (x : 𝕎 p R) (n : ℕ) :
  ghost_component (n + 1) (verschiebung_fun p R x) = p * ghost_component n x :=
begin
  simp only [ghost_component, aeval_witt_polynomial],
  rw [finset.sum_range_succ', verschiebung_fun, zero_pow (nat.pow_pos hp.pos _), mul_zero, add_zero,
      finset.mul_sum, finset.sum_congr rfl],
  rintro i -,
  rw [pow_succ, mul_assoc, verschiebung_fun, nat.succ_sub_succ],
end

lemma verschiebung_add_aux₁ (x y : 𝕎 p (mv_polynomial R ℚ)) :
  verschiebung_fun p _ (x + y) = verschiebung_fun p _ x + verschiebung_fun p _ y :=
begin
  apply (ghost_map.bijective_of_invertible p (mv_polynomial R ℚ)).1,
  ext1 n,
  rw ring_hom.map_add,
  simp only [pi.add_apply],
  cases n,
  { simp only [add_zero, ghost_component_zero_verschiebung_fun, ghost_map_apply], },
  { simp only [ghost_map_apply, ghost_component_verschiebung_fun, ghost_component_add, mul_add], }
end

lemma vershiebung_add_aux₂ (x y : 𝕎 p (mv_polynomial R ℤ)) :
  verschiebung_fun p _ (x + y) = verschiebung_fun p _ x + verschiebung_fun p _ y :=
begin
  refine map_injective (mv_polynomial.map (int.cast_ring_hom ℚ))
    (mv_polynomial.coe_int_rat_map_injective _) _,
  simp only [verschiebung_add_aux₁, ring_hom.map_add, map_verschiebung_fun],
end

variables {R}

noncomputable
def verschiebung : 𝕎 p R →+ 𝕎 p R :=
{ to_fun := verschiebung_fun p R,
  map_zero' :=
  begin
    ext ⟨⟩,
    { rw zero_coeff, refl },
    { calc coeff n (0 : 𝕎 p R) = 0             : by rw zero_coeff
                            ... = coeff (n+1) 0 : by rw zero_coeff, }
  end,
  map_add' :=
  begin
    intros x y,
    rcases map_surjective _ (counit_surjective R) x with ⟨x, rfl⟩,
    rcases map_surjective _ (counit_surjective R) y with ⟨y, rfl⟩,
    rw [← ring_hom.map_add],
    iterate 3 { rw [← map_verschiebung_fun] },
    rw [vershiebung_add_aux₂, ring_hom.map_add],
  end }

@[simp] lemma verschiebung_coeff_zero (x : 𝕎 p R) :
  (verschiebung p x).coeff 0 = 0 := rfl

@[simp] lemma verschiebung_coeff_add_one (x : 𝕎 p R) (n : ℕ) :
  (verschiebung p x).coeff (n + 1) = x.coeff n := rfl

@[simp] lemma verschiebung_coeff_succ (x : 𝕎 p R) (n : ℕ) :
  (verschiebung p x).coeff n.succ = x.coeff n := rfl

/-- Verschiebung is a natural transformation. -/
@[simp] lemma map_verschiebung (f : R →+* S) (x : 𝕎 p R) :
  map f (verschiebung p x) = verschiebung p (map f x) :=
map_verschiebung_fun _ _ _ _

@[simp] lemma ghost_component_zero_verschiebung (x : 𝕎 p R) :
  ghost_component 0 (verschiebung p x) = 0 :=
ghost_component_zero_verschiebung_fun _ _ _

@[simp] lemma ghost_component_verschiebung (x : 𝕎 p R) (n : ℕ) :
  ghost_component (n + 1) (verschiebung p x) = p * ghost_component n x :=
ghost_component_verschiebung_fun _ _ _ _

end verschiebung

-- section frobenius



-- noncomputable def frobenius_fun (x : 𝕎 p R) : 𝕎 p R :=
-- λ n, aeval x (frobenius_poly p n)

-- end frobenius

variable {R}
def mk (x : ℕ → R) : 𝕎 p R := x

end witt_vectors

attribute [irreducible] witt_vectors

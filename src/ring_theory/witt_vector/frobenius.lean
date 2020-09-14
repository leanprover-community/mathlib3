/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import data.nat.multiplicity
import ring_theory.witt_vector.basic
import ring_theory.witt_vector.is_poly


/-! ## The Verschiebung operator -/

namespace witt_vector

variables {p : ℕ} {R S : Type*} [hp : fact p.prime] [comm_ring R] [comm_ring S]
local notation `𝕎` := witt_vector p -- type as `\bbW`

local attribute [semireducible] witt_vector
local attribute [instance] mv_polynomial.invertible_rat_coe_nat

noncomputable theory
open mv_polynomial finset
open_locale big_operators

variables (p)
include hp

def frobenius_poly_rat (n : ℕ) : mv_polynomial ℕ ℚ :=
bind₁ (witt_polynomial p ℚ ∘ λ n, n + 1) (X_in_terms_of_W p ℚ n)

lemma bind₁_frobenius_poly_rat_witt_polynomial (n : ℕ) :
  bind₁ (frobenius_poly_rat p) (witt_polynomial p ℚ n) = (witt_polynomial p ℚ (n+1)) :=
begin
  delta frobenius_poly_rat,
  rw [← bind₁_bind₁, X_in_terms_of_W_prop₂, bind₁_X_right],
end

-- move this?
def pnat_multiplicity (n : ℕ+) : ℕ :=
(multiplicity p n).get $ multiplicity.finite_nat_iff.mpr $ ⟨ne_of_gt hp.one_lt, n.2⟩

local notation `vp` k := pnat_multiplicity p k

lemma blahrg (n i j : ℕ)
  (hi : i < n)
  (hj : j < p ^ (n - i)) :
  j - pnat_multiplicity p ⟨j + 1, j.succ_pos⟩ + n =
    i + j + (n - i - pnat_multiplicity p ⟨j + 1, j.succ_pos⟩) :=
begin
  generalize h : pnat_multiplicity p ⟨j + 1, j.succ_pos⟩ = m,
  suffices : m ≤ n - i ∧ m ≤ j,
  { cases this, unfreezingI { clear_dependent p }, omega },
  split,
  { rw ← h,
    rw [← enat.coe_le_coe, pnat_multiplicity, enat.coe_get],
    rw [← (nat.prime.multiplicity_choose_prime_pow hp hj j.succ_pos)],
    apply le_add_left, refl },
  { obtain ⟨c, hc⟩ : p ^ m ∣ j + 1,
    { rw [← h],
      exact multiplicity.pow_multiplicity_dvd _, },
    have cpos : c ≠ 0,
    { rintro rfl, simpa only using hc, },
    apply nat.le_of_lt_succ,
    calc m < p ^ m : nat.lt_pow_self hp.one_lt m
       ... ≤ j + 1 : _,
    obtain ⟨c, rfl⟩ := nat.exists_eq_succ_of_ne_zero cpos,
    rw [nat.succ_eq_add_one, mul_add, mul_one] at hc,
    have := nat.sub_eq_of_eq_add hc,
    rw ← this,
    apply nat.sub_le }
end

section omit hp
lemma rat.coe_nat_div (a b : ℕ) (h : b ∣ a) : ((a / b : ℕ) : ℚ) = (a / b : ℚ) :=
begin
  rcases h with ⟨c, rfl⟩,
  simp only [dvd_mul_right, nat.cast_dvd_char_zero],
end
end

lemma final_bit (n i j : ℕ) (hi : i < n) (hj : j < p ^ (n - i)) :
  @C _ ℕ _ (↑p * (int.cast_ring_hom ℚ)
           ↑((p ^ (n - i)).choose (j + 1) / p ^ (n - i - vp ⟨j + 1, nat.succ_pos j⟩)) *
            ↑p ^ (j - vp ⟨j + 1, nat.succ_pos j⟩)) =
    C (⅟ ↑p ^ n * ↑p ^ i * ↑((p ^ (n - i)).choose (j + 1)) *
         ↑p ^ (j + 1)) :=
begin
  rw C_inj,
  simp only [inv_of_eq_inv, ring_hom.eq_int_cast, inv_pow', int.cast_coe_nat],
  rw [rat.coe_nat_div],
  swap,
  { apply multiplicity.pow_dvd_of_le_multiplicity,
    have aux : multiplicity.finite p ((p ^ (n - i)).choose (j + 1)),
    { rw multiplicity.finite_nat_iff,
      exact ⟨ne_of_gt hp.one_lt, nat.choose_pos hj⟩, },
    rw multiplicity.finite_iff_dom at aux,
    rw [← enat.coe_get aux, enat.coe_le_coe, nat.sub_le_left_iff_le_add],
    rw [← enat.coe_le_coe, enat.coe_add, pnat_multiplicity, enat.coe_get, enat.coe_get, add_comm],
    apply le_of_eq,
    apply (nat.prime.multiplicity_choose_prime_pow hp hj j.succ_pos).symm, },
  { have aux : ∀ k : ℕ, (p ^ k : ℚ) ≠ 0,
    { intro, apply pow_ne_zero, exact_mod_cast hp.ne_zero },
    simp only [nat.cast_pow, pow_add, pow_one],
    field_simp [aux],
    ring_exp,
    congr' 1,
    simp only [← mul_assoc],
    congr' 1,
    simp only [← pow_add],
    congr' 1,
    apply blahrg p n i j hi hj, }
end
.


noncomputable
def frobenius_poly_aux : ℕ → mv_polynomial ℕ ℤ
| n := X (n + 1) - ∑ i : fin n, have _ := i.is_lt,
  ∑ j in range (p ^ (n - i)), (X i ^ p) ^ (p ^ (n - i) - (j + 1)) *
                              (frobenius_poly_aux i) ^ (j + 1) *
                              C ↑((p ^ (n - i)).choose (j + 1) / (p ^ (n - i - vp ⟨j + 1, nat.succ_pos j⟩)) *
                                ↑p ^ (j - vp ⟨j + 1, nat.succ_pos j⟩) : ℕ)

lemma frobenius_poly_aux_eq (n : ℕ) :
  frobenius_poly_aux p n =
  X (n + 1) - ∑ i in range n, ∑ j in range (p ^ (n - i)),
    (X i ^ p) ^ (p ^ (n - i) - (j + 1)) *
    (frobenius_poly_aux p i) ^ (j + 1) *
    C ↑((p ^ (n - i)).choose (j + 1) / (p ^ (n - i - vp ⟨j + 1, nat.succ_pos j⟩)) *
      ↑p ^ (j - vp ⟨j + 1, nat.succ_pos j⟩) : ℕ) :=
by { rw [frobenius_poly_aux, ← fin.sum_univ_eq_sum_range], refl }

def frobenius_poly (n : ℕ) : mv_polynomial ℕ ℤ :=
X n ^ p + C ↑p * (frobenius_poly_aux p n)

lemma map_frobenius_poly (n : ℕ) :
  mv_polynomial.map (int.cast_ring_hom ℚ) (frobenius_poly p n) = frobenius_poly_rat p n :=
begin
  calc mv_polynomial.map (int.cast_ring_hom ℚ) (frobenius_poly p n)
      = X n ^ p + (C ↑p) * mv_polynomial.map (int.cast_ring_hom ℚ) (frobenius_poly_aux p n) : _ -- step 1
  ... = bind₁ (witt_polynomial p ℚ ∘ λ n, n + 1) (X_in_terms_of_W p ℚ n)                    : _ -- step 2
  ... = frobenius_poly_rat p n : rfl,
  { -- step 1
    rw [frobenius_poly, ring_hom.map_add, ring_hom.map_mul, ring_hom.map_pow,
        map_C, map_X, ring_hom.eq_int_cast, int.cast_coe_nat] },
  -- step 2
  apply nat.strong_induction_on n, clear n,
  intros n IH,
  rw [X_in_terms_of_W_eq],

  -- we move the `bind₁` into the sum, so that we can isolate `X n ^ p` in the right hand side
  suffices : X n ^ p + C ↑p * (mv_polynomial.map (int.cast_ring_hom ℚ)) (frobenius_poly_aux p n)
   = X n ^ p + (C ↑p * X (n + 1) + C (⅟ ↑p ^ n) * ∑ (x : ℕ) in range n, (C (↑p ^ x) * X x ^ p ^ (n + 1 - x) - C (↑p ^ x) * (bind₁ (witt_polynomial p ℚ ∘ λ (n : ℕ), n + 1)) (X_in_terms_of_W p ℚ x) ^ p ^ (n - x))),
  { convert this,
  simp only [alg_hom.map_mul, alg_hom.map_sub, alg_hom.map_pow, alg_hom.map_sum,
    bind₁_C_right, bind₁_X_right, function.comp_app, witt_polynomial_eq_sum_C_mul_X_pow],
  rw [sum_range_succ, sum_range_succ, nat.sub_self, nat.pow_zero,
      mul_comm _ (C (⅟ ↑p ^ n)), mul_sub, mul_add, ← mul_assoc, ← C_mul, mul_add, ← mul_assoc, ← C_mul,
      pow_add, ← mul_assoc, pow_one, pow_one,
      ← mul_pow, inv_of_mul_self, one_pow, one_mul, C_1, one_mul,
      add_comm n, nat.add_sub_cancel, nat.pow_one, add_comm _ n,
      add_left_comm, ← add_sub, ← add_sub, ← mul_sub, ← sum_sub_distrib], },

  -- now that we have managed to isolate `X n ^ p`, we gladly cancel it
  rw [add_right_inj],


  -- the next step is to isolate `C p * X (n + 1)`
  -- to do that, it is time to take a better look at the left hand side
  suffices : C ↑p * X (n + 1) +
    -(C ↑p *
         ∑ (x : ℕ) in
           range n,
           (mv_polynomial.map (int.cast_ring_hom ℚ))
             (∑ (j : ℕ) in
                range (p ^ (n - x)),
                (X x ^ p) ^ (p ^ (n - x) - (j + 1)) * frobenius_poly_aux p x ^ (j + 1) *
                  C
                    ↑((p ^ (n - x)).choose (j + 1) / p ^ (n - x - pnat_multiplicity p ⟨j + 1, _⟩) *
                         ↑p ^ (j - pnat_multiplicity p ⟨j + 1, _⟩)))) =
  C ↑p * X (n + 1) +
    C (⅟ ↑p ^ n) *
      ∑ (x : ℕ) in
        range n,
        (C (↑p ^ x) * X x ^ p ^ (n + 1 - x) -
           C (↑p ^ x) *
             (bind₁ (witt_polynomial p ℚ ∘ λ (n : ℕ), n + 1)) (X_in_terms_of_W p ℚ x) ^ p ^ (n - x)),
  { convert this,
    rw [frobenius_poly_aux_eq, ring_hom.map_sub, map_X, ring_hom.map_sum, mul_sub, sub_eq_add_neg], },

  -- now we can cancel `X (n + 1)`
  rw [add_right_inj],

  -- we push the everything into the sums,
  -- and compare the remaining sums term by term
  rw [mul_sum, mul_sum, ← sum_neg_distrib],
  apply sum_congr rfl,
  intros i hi,
  rw mem_range at hi,

  -- use the induction hypothesis, but in a smart way
  suffices : -(C ↑p *
       (mv_polynomial.map (int.cast_ring_hom ℚ))
         (∑ (j : ℕ) in
            range (p ^ (n - i)),
            (X i ^ p) ^ (p ^ (n - i) - (j + 1)) * frobenius_poly_aux p i ^ (j + 1) *
              C
                ↑((p ^ (n - i)).choose (j + 1) / p ^ (n - i - pnat_multiplicity p ⟨j + 1, _⟩) *
                     ↑p ^ (j - pnat_multiplicity p ⟨j + 1, _⟩)))) =
  C (⅟ ↑p ^ n * ↑p ^ i) *
    (X i ^ p ^ (n + 1 - i) -
       (C ↑p * (mv_polynomial.map (int.cast_ring_hom ℚ)) (frobenius_poly_aux p i) + X i ^ p) ^ p ^ (n - i)),
  { convert this using 1,
    specialize IH i hi,
    rw [add_comm] at IH,
    rw [← IH, ← mul_sub, ← mul_assoc, ← C_mul], },
  clear IH,

  -- we now apply the binomium of Newton on the right hand side,
  -- and split off the first term of the resulting sum
  suffices : ∑ (x : ℕ) in
    range (p ^ (n - i)),
    C ↑p *
      (mv_polynomial.map (int.cast_ring_hom ℚ))
        ((X i ^ p) ^ (p ^ (n - i) - (x + 1)) * frobenius_poly_aux p i ^ (x + 1) *
           C
             ↑((p ^ (n - i)).choose (x + 1) / p ^ (n - i - pnat_multiplicity p ⟨x + 1, _⟩) *
                  ↑p ^ (x - pnat_multiplicity p ⟨x + 1, _⟩))) =
  ∑ (x : ℕ) in
    range (p ^ (n - i)),
    C (⅟ ↑p ^ n * ↑p ^ i) *
      ((C ↑p * (mv_polynomial.map (int.cast_ring_hom ℚ)) (frobenius_poly_aux p i)) ^ (x + 1) *
           (X i ^ p) ^ (p ^ (n - i) - (x + 1)) *
         ↑((p ^ (n - i)).choose (x + 1))),
  { rw [add_pow, sum_range_succ'],
    -- now we can clean up the term that we split off
    rw [nat.sub_zero, pow_zero, nat.choose_zero_right, nat.cast_one, one_mul, mul_one,
        sub_add_eq_sub_sub_swap],
    rw show (X i ^ p ^ (n + 1 - i) - (X i ^ p) ^ p ^ (n - i) : mv_polynomial ℕ ℚ) = 0,
    { rw [← pow_mul, mul_comm, nat.sub_add_comm, nat.pow_succ, sub_self],
      exact le_of_lt hi },
    rw [zero_sub, mul_neg_eq_neg_mul_symm, neg_inj, mul_sum, ring_hom.map_sum, mul_sum],
    exact this },

  -- and then we compare the remaining sums term by term
  apply sum_congr rfl,
  intros j hj,
  rw mem_range at hj,

  -- reorganise, in order to isolate more common factors
  suffices : C
        (↑p *
           (int.cast_ring_hom ℚ)
             ↑((p ^ (n - i)).choose (j + 1) / p ^ (n - i - pnat_multiplicity p ⟨j + 1, _⟩) *
                  ↑p ^ (j - pnat_multiplicity p ⟨j + 1, _⟩))) *
      (X i ^ p) ^ (p ^ (n - i) - (j + 1)) *
    (mv_polynomial.map (int.cast_ring_hom ℚ)) (frobenius_poly_aux p i) ^ (j + 1) =
  C (⅟ ↑p ^ n * ↑p ^ i * ↑p ^ (j + 1) * ↑((p ^ (n - i)).choose (j + 1))) *
      (X i ^ p) ^ (p ^ (n - i) - (j + 1)) *
    (mv_polynomial.map (int.cast_ring_hom ℚ)) (frobenius_poly_aux p i) ^ (j + 1),
  { simp only [ring_hom.map_mul, ring_hom.map_pow, map_X, map_C, mul_pow, mul_assoc],
    simp only [← mul_assoc, ← C_mul, ← C_pow, ← C_eq_coe_nat, mul_right_comm],
    rw [mul_right_comm, mul_right_comm (C ↑p : mv_polynomial ℕ ℚ), ← C_mul],
    exact this },

  congr' 2,
  convert final_bit p n i j hi hj,
  { simp [C_mul, mul_assoc] },
  { simp only [C_mul, mul_assoc], conv_lhs { congr, skip, congr, skip, rw mul_comm } }
end
.

variables {p}

def frobenius_fun (x : 𝕎 R) : 𝕎 R :=
mk p $ λ n, (mv_polynomial.aeval (λ (k : ℕ), coeff k x)) (frobenius_poly p n)

lemma coeff_frobenius_fun (x : 𝕎 R) (n : ℕ) :
  coeff n (frobenius_fun x) = (mv_polynomial.aeval (λ (k : ℕ), coeff k x)) (frobenius_poly p n) :=
coeff_mk _ _ _

variables (p)

@[simps { fully_applied := ff }]
lemma frobenius_is_poly : is_poly p (λ R _Rcr, @frobenius_fun p R _ _Rcr) :=
{ poly := frobenius_poly p,
  coeff := by { introsI, apply coeff_frobenius_fun } }

lemma bind₁_frobenius_poly_witt_polynomial (n : ℕ) :
  bind₁ (frobenius_poly p) (witt_polynomial p ℤ n) = (witt_polynomial p ℤ (n+1)) :=
begin
  apply mv_polynomial.map_injective (int.cast_ring_hom ℚ) int.cast_injective,
  simp only [map_bind₁, map_frobenius_poly, bind₁_frobenius_poly_rat_witt_polynomial,
    map_witt_polynomial],
end

lemma frobenius_poly_zmod (n : ℕ) :
  mv_polynomial.map (int.cast_ring_hom (zmod p)) (frobenius_poly p n) = X n ^ p :=
begin
  rw [frobenius_poly, ring_hom.map_add, ring_hom.map_pow, ring_hom.map_mul, map_X, map_C],
  simp only [int.cast_coe_nat, add_zero, ring_hom.eq_int_cast, zmod.cast_self, zero_mul, C_0],
end

section char_p
variables [char_p R p]

-- move this
instance qwerty : algebra (zmod p) R :=
ring_hom.to_algebra (zmod.cast_hom (dvd_refl p) R)

@[simp]
lemma coeff_frobenius_fun_char_p (x : 𝕎 R) (n : ℕ) :
  coeff n (frobenius_fun x) = (x.coeff n) ^ p :=
begin
  rw [coeff_frobenius_fun],
  -- outline of the calculation, proofs follow below
  calc aeval (λ k, x.coeff k) (frobenius_poly p n)
      = aeval (λ k, x.coeff k) (mv_polynomial.map (int.cast_ring_hom (zmod p)) (frobenius_poly p n)) : _
  ... = aeval (λ k, x.coeff k) (X n ^ p : mv_polynomial ℕ (zmod p)) : _
  ... = (x.coeff n) ^ p : _,
  { conv_rhs { rw [aeval_eq_eval₂_hom, eval₂_hom_map_hom] },
    apply eval₂_hom_congr (ring_hom.ext_int _ _) rfl rfl },
  { rw frobenius_poly_zmod },
  { rw [alg_hom.map_pow, aeval_X] }
end

@[simp]
lemma frobenius_fun_zmodp (x : 𝕎 (zmod p)) :
  (frobenius_fun x) = x :=
by simp only [ext_iff, coeff_frobenius_fun_char_p, zmod.pow_card, eq_self_iff_true, forall_const]

end char_p

end witt_vector

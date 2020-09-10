/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/

import ring_theory.witt_vector.witt_polynomial
import field_theory.mv_polynomial
import field_theory.finite

open mv_polynomial
open set
open finset (range)
open finsupp (single)

open_locale big_operators

local attribute [-simp] coe_eval₂_hom

variables {p : ℕ} {R : Type*} {idx : Type*} [comm_ring R]

open_locale witt

section p_prime

variables (p) [hp : fact p.prime]
include hp

noncomputable def witt_structure_rat (Φ : mv_polynomial idx ℚ) (n : ℕ) :
  mv_polynomial (idx × ℕ) ℚ :=
bind₁ (λ k : ℕ, (bind₁ (λ b, (rename (λ i, (b,i)) (W_ ℚ k)))) Φ) (X_in_terms_of_W p ℚ n)

theorem witt_structure_rat_prop (Φ : mv_polynomial idx ℚ) (n : ℕ) :
  bind₁ (witt_structure_rat p Φ) (W_ ℚ n) =
  bind₁ (λ b, (rename (λ i, (b,i)) (W_ ℚ n))) Φ :=
calc bind₁ (witt_structure_rat p Φ) (W_ ℚ n) =
      bind₁ (λ k, bind₁ (λ b, (rename (prod.mk b)) (W_ ℚ k)) Φ)
        (bind₁ (X_in_terms_of_W p ℚ) (W_ ℚ n)) :
      by { rw [bind₁_bind₁], apply eval₂_hom_congr (ring_hom.ext_rat _ _) rfl rfl }
... = bind₁ (λ b, (rename (λ i, (b,i)) (W_ ℚ n))) Φ :
      by rw [X_in_terms_of_W_prop₂ p _ n, bind₁_X_right]

theorem witt_structure_prop_exists_unique (Φ : mv_polynomial idx ℚ) :
  ∃! (φ : ℕ → mv_polynomial (idx × ℕ) ℚ),
    ∀ (n : ℕ), bind₁ φ (W_ ℚ n) = bind₁ (λ b, (rename (λ i, (b,i)) (W_ ℚ n))) Φ :=
begin
  refine ⟨witt_structure_rat p Φ, _, _⟩,
  { intro n, apply witt_structure_rat_prop },
  { intros φ H,
    funext n,
    rw show φ n = bind₁ φ (bind₁ (W_ ℚ) (X_in_terms_of_W p ℚ n)),
    { rw [X_in_terms_of_W_prop p, bind₁_X_right] },
    rw [bind₁_bind₁],
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

end p_prime

variables {ι : Type*} {σ : Type*}
variables {S : Type*} [comm_ring S]
variables {T : Type*} [comm_ring T]

variables (p)

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
  apply congr₂,
  { simp only [map_bind₁, map_rename, map_witt_polynomial], },
  { apply finset.sum_congr rfl,
    intros i hi,
    rw finset.mem_range at hi,
    specialize IH i hi,
    simp only [IH, int.cast_coe_nat, ring_hom.eq_int_cast, ring_hom.map_pow, map_C, ring_hom.map_mul, ring_hom.map_nat_cast], }
end

variable {p}

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
(mv_polynomial.frobenius_zmod _).symm

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

variables (p)

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

  apply mv_polynomial.map_injective (int.cast_ring_hom ℚ) int.cast_injective,

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

variables (p)

theorem witt_structure_int_prop (Φ : mv_polynomial idx ℤ) (n) :
  bind₁ (witt_structure_int p Φ) (witt_polynomial p ℤ n) =
  bind₁ (λ b, (rename (λ i, (b,i)) (W_ ℤ n))) Φ :=
begin
  apply mv_polynomial.map_injective (int.cast_ring_hom ℚ) int.cast_injective,
  have := witt_structure_rat_prop p (map (int.cast_ring_hom ℚ) Φ) n,
  simpa only [map_bind₁, ← eval₂_hom_map_hom, eval₂_hom_C_left, map_rename,
        map_witt_polynomial, alg_hom.coe_to_ring_hom, map_witt_structure_int],
end

lemma eq_witt_structure_int (Φ : mv_polynomial idx ℤ) (φ : ℕ → mv_polynomial (idx × ℕ) ℤ)
  (h : ∀ n, bind₁ φ (witt_polynomial p ℤ n) = bind₁ (λ b, (rename (λ i, (b,i)) (W_ ℤ n))) Φ) :
  φ = witt_structure_int p Φ :=
begin
  funext k,
    apply mv_polynomial.map_injective (int.cast_ring_hom ℚ) int.cast_injective,
    rw map_witt_structure_int,
    refine congr_fun _ k,
    have := (witt_structure_prop_exists_unique p (map (int.cast_ring_hom ℚ) Φ)),
    apply unique_of_exists_unique this,
    { clear this, intro n,
      specialize h n,
      apply_fun map (int.cast_ring_hom ℚ) at h,
      simpa only [map_bind₁, ← eval₂_hom_map_hom, eval₂_hom_C_left, map_rename,
        map_witt_polynomial, alg_hom.coe_to_ring_hom] using h, },
    { intro n, apply witt_structure_rat_prop }
end

theorem witt_structure_int_exists_unique (Φ : mv_polynomial idx ℤ) :
  ∃! (φ : ℕ → mv_polynomial (idx × ℕ) ℤ),
  ∀ (n : ℕ), bind₁ φ (witt_polynomial p ℤ n) = bind₁ (λ b : idx, (rename (λ i, (b,i)) (W_ ℤ n))) Φ :=
⟨witt_structure_int p Φ, witt_structure_int_prop _ _, eq_witt_structure_int _ _⟩

theorem witt_structure_prop (Φ : mv_polynomial idx ℤ) (n) :
  aeval (λ i, map (int.cast_ring_hom R) (witt_structure_int p Φ i)) (witt_polynomial p ℤ n) =
  aeval (λ b, (rename (λ i, (b,i)) (W n))) Φ :=
begin
  convert congr_arg (map (int.cast_ring_hom R)) (witt_structure_int_prop p Φ n),
  { rw [hom_bind₁],
    exact eval₂_hom_congr (ring_hom.ext_int _ _) rfl rfl, },
  { rw [hom_bind₁],
    apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
    simp only [map_rename, map_witt_polynomial] }
end

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

end p_prime

namespace witt_vector
variables (p) [hp : fact p.prime]
include hp

/-- The polynomial used for defining the element `0` of the ring of Witt vectors. -/
noncomputable def witt_zero : ℕ → mv_polynomial (empty × ℕ) ℤ :=
witt_structure_int p 0

/-- The polynomial used for defining the element `1` of the ring of Witt vectors. -/
noncomputable def witt_one : ℕ → mv_polynomial (empty × ℕ) ℤ :=
witt_structure_int p 1

-- Do we want to use bool, or a custom inductive type with terms l(eft) and r(ight)?
noncomputable def witt_add : ℕ → mv_polynomial (bool × ℕ) ℤ :=
witt_structure_int p (X tt + X ff)

noncomputable def witt_sub : ℕ → mv_polynomial (bool × ℕ) ℤ :=
witt_structure_int p (X tt - X ff)

noncomputable def witt_mul : ℕ → mv_polynomial (bool × ℕ) ℤ :=
witt_structure_int p (X tt * X ff)

noncomputable def witt_neg : ℕ → mv_polynomial (unit × ℕ) ℤ :=
witt_structure_int p (-X unit.star)

section witt_structure_simplifications

@[simp] lemma witt_zero_eq_zero (n : ℕ) : witt_zero p n = 0 :=
begin
  apply mv_polynomial.map_injective (int.cast_ring_hom ℚ) int.cast_injective,
  simp only [witt_zero, witt_structure_rat, bind₁, aeval_zero',
    constant_coeff_X_in_terms_of_W, ring_hom.map_zero,
    alg_hom.map_zero, map_witt_structure_int],
end

@[simp] lemma witt_one_zero_eq_one : witt_one p 0 = 1 :=
begin
  apply mv_polynomial.map_injective (int.cast_ring_hom ℚ) int.cast_injective,
  simp only [witt_one, witt_structure_rat, X_in_terms_of_W_zero, alg_hom.map_one,
    ring_hom.map_one, bind₁_X_right, map_witt_structure_int]
end

@[simp] lemma witt_one_pos_eq_zero (n : ℕ) (hn : 0 < n) : witt_one p n = 0 :=
begin
  apply mv_polynomial.map_injective (int.cast_ring_hom ℚ) int.cast_injective,
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

@[simp] lemma witt_add_zero : witt_add p 0 = X (tt,0) + X (ff,0) :=
begin
  apply mv_polynomial.map_injective (int.cast_ring_hom ℚ) int.cast_injective,
  simp only [witt_add, witt_structure_rat, alg_hom.map_add, ring_hom.map_add,
    rename_X, X_in_terms_of_W_zero, map_X,
     witt_polynomial_zero, bind₁_X_right, map_witt_structure_int],
end

@[simp] lemma witt_sub_zero : witt_sub p 0 = X (tt,0) - X (ff,0) :=
begin
  apply mv_polynomial.map_injective (int.cast_ring_hom ℚ) int.cast_injective,
  simp only [witt_sub, witt_structure_rat, alg_hom.map_sub, ring_hom.map_sub,
    rename_X, X_in_terms_of_W_zero, map_X,
     witt_polynomial_zero, bind₁_X_right, map_witt_structure_int],
end

@[simp] lemma witt_mul_zero : witt_mul p 0 = X (tt,0) * X (ff,0) :=
begin
  apply mv_polynomial.map_injective (int.cast_ring_hom ℚ) int.cast_injective,
  simp only [witt_mul, witt_structure_rat, rename_X, X_in_terms_of_W_zero, map_X,
    witt_polynomial_zero, ring_hom.map_mul,
    bind₁_X_right, alg_hom.map_mul, map_witt_structure_int]

end

@[simp] lemma witt_neg_zero : witt_neg p 0 = - X ((),0) :=
begin
  apply mv_polynomial.map_injective (int.cast_ring_hom ℚ) int.cast_injective,
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

@[simp] lemma constant_coeff_witt_sub (n : ℕ) :
  constant_coeff (witt_sub p n) = 0 :=
begin
  apply constant_coeff_witt_structure_int p _ _ n,
  simp only [sub_zero, ring_hom.map_sub, constant_coeff_X],
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

end witt_structure_simplifications


section witt_vars
variable (R)

-- we could relax the fintype on `idx`, but then we need to cast from finset to set.
-- for our applications `idx` is always finite.
lemma witt_structure_rat_vars [fintype idx] (Φ : mv_polynomial idx ℚ) (n : ℕ) :
  (witt_structure_rat p Φ n).vars ⊆ finset.univ.product (finset.range (n + 1)) :=
begin
  rw witt_structure_rat,
  intros x hx,
  simp only [finset.mem_product, true_and, finset.mem_univ, finset.mem_range],
  replace hx := bind₁_vars _ _ hx,
  simp only [exists_prop, finset.mem_bind, finset.mem_range] at hx,
  rcases hx with ⟨k, hk, hx⟩,
  replace hk := X_in_terms_of_W_vars_subset p _ hk,
  rw finset.mem_range at hk,
  replace hx := bind₁_vars _ _ hx,
  simp only [exists_prop, finset.mem_bind, finset.mem_range] at hx,
  rcases hx with ⟨i, -, hx⟩,
  replace hx := vars_rename _ _ hx,
  rw [finset.mem_image] at hx,
  rcases hx with ⟨j, hj, rfl⟩,
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


end witt_vector

/-
2020. No rights reserved. https://unlicense.org/
Authors: Johan Commelin
-/

import algebra.inj_surj
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
open mv_polynomial (hiding aeval)
open set
open finset (range)

open_locale big_operators

-- TODO: This should be fixed in mathlib
local notation `aeval` := mv_polynomial.aeval _ _

variables (p : ℕ) [fact p.prime]
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
∑ i in range (n+1), C (p^i) * X i ^ (p^(n-i))

/-! We set up notation locally to this file, to keep statements short and comprehensible.
This allows us to simply write `W n` or `W_ ℤ n`. -/

local notation `W_`  := witt_polynomial p   -- Notation with ring of coefficients explicit
local notation `W`   := witt_polynomial p _ -- Notation with ring of coefficients implicit

/- The first observation is that the Witt polynomial doesn't really depend on the coefficient ring.
If we map the coefficients through a ring homomorphism, we obtain the corresponding Witt polynomial
over the target ring. -/
section
variables {R} {S : Type*} [comm_ring S]

lemma map_witt_polynomial (f : R →+* S) (n : ℕ) :
  map f (W n) = W n :=
begin
  delta witt_polynomial,
  rw [← finset.sum_hom _ (map f)],
  { apply finset.sum_congr rfl,
    intros i hi,
    rw [map_mul f, map_C f, f.map_pow, f.map_nat_cast, map_pow f, map_X f], },
  { apply_instance }
end

@[simp] lemma map_hom_witt_polynomial (f : R →+* S) (n : ℕ) :
  map_hom f (W n) = W n :=
map_witt_polynomial p f n

variables (R)

lemma aeval_witt_polynomial {A : Type*} [comm_ring A] [algebra R A] (f : ℕ → A) (n : ℕ) :
  aeval f (W_ R n) = ∑ i in range (n+1), p^i * (f i) ^ (p ^ (n-i)) :=
by simp only [witt_polynomial, alg_hom.map_sum, aeval_C,
    ring_hom.map_nat_cast, alg_hom.map_pow, C_pow, aeval_X, alg_hom.map_mul]

end

/-- View a polynomial written in terms of the basis of Witt polynomials
as a polynomial written in terms of the standard basis.

In particular, this sends `X n` to `witt_polynomial p n`.
This fact is recorded in `from_W_to_X_basis_X`. -/
noncomputable def from_W_to_X_basis : mv_polynomial ℕ R →ₐ[R] mv_polynomial ℕ R :=
aeval W

-- instance from_W_to_X_basis.is_ring_hom : is_ring_hom (from_W_to_X_basis p R) :=
-- by delta from_W_to_X_basis; apply_instance

lemma witt_polynomial_zero : (W 0 : mv_polynomial ℕ R) = X 0 :=
begin
  delta witt_polynomial,
  simp [finset.sum_range_succ, finset.range_zero, finset.sum_empty],
end

@[simp] lemma from_W_to_X_basis_X (n) : from_W_to_X_basis p R (X n) = W n :=
by simp [from_W_to_X_basis]

-- variables {R} -- (pu : units R) (hp : (pu : R) = p)

-- We need p to be invertible for the following definitions

/-- The `X_in_terms_of_W p R n` is the polynomial on the basis of Witt polynomials
that corresponds to the ordinary `X n`.
This means that `from_W_to_X_basis` sends `X_in_terms_of_W p R n` to `X n`.
This fact is recorded in `from_W_to_X_basis_X_in_terms_of_W`. -/
noncomputable def X_in_terms_of_W [invertible (p : R)] :
  ℕ → mv_polynomial ℕ R
| n := (X n - (∑ i : fin n,
  have _ := i.2, (C (p^(i : ℕ)) * (X_in_terms_of_W i)^(p^(n-i))))) * C (⅟p ^ n)

lemma X_in_terms_of_W_eq [invertible (p : R)] {n : ℕ} : X_in_terms_of_W p R n =
    (X n - (∑ i in finset.range n, C (p^i) * X_in_terms_of_W p R i ^ p ^ (n - i))) *
      C (⅟p ^ n) :=
by { rw [X_in_terms_of_W, ← fin.sum_univ_eq_sum_range], refl }

/-- View a polynomial written in terms of the standard basis
as a polynomial written in terms of the Witt basis.

This sends `W n` to `X n`,
and `X n` to `X_in_terms_of_W p R n`. -/
noncomputable def from_X_to_W_basis [invertible (p : R)] :
  mv_polynomial ℕ R →ₐ[R] mv_polynomial ℕ R :=
aeval (X_in_terms_of_W p R)

-- instance from_X_to_W_basis.is_ring_hom : is_ring_hom (from_X_to_W_basis p pu hp) :=
-- by delta from_X_to_W_basis; apply_instance

@[simp] lemma from_X_to_W_basis_X [invertible (p : R)] (n : ℕ) :
  (from_X_to_W_basis p R) (X n) = X_in_terms_of_W p R n :=
by rw [from_X_to_W_basis, aeval_X]

-- move this
@[simp] lemma alg_hom_C {σ : Type*} (f : mv_polynomial σ R →ₐ[R] mv_polynomial σ R) (r : R) :
  f (C r) = C r :=
f.commutes r

-- lemma X_in_terms_of_W_zero [invertible (p : R)] :
--   X_in_terms_of_W p R 0 = W 0 :=
-- begin
--   rw X_in_terms_of_W_eq,
--   rw finset.range_zero,
--   rw finset.sum_empty,
--   rw witt_polynomial_zero,
--   simp
-- end

lemma X_in_terms_of_W_aux [invertible (p : R)] {n} : X_in_terms_of_W p R n * C (p^n) =
  X n - ∑ i in finset.range n, C (p^i) * (X_in_terms_of_W p R i)^p^(n-i) :=
by rw [X_in_terms_of_W_eq, mul_assoc, ← C_mul, ← mul_pow, inv_of_mul_self, one_pow, C_1, mul_one]

section -- Kudos to Mario

theorem rat.ring_hom_unique {α} [ring α]
  (f g : ℚ → α) [is_ring_hom f] [is_ring_hom g] (r : ℚ) : f r = g r :=
rat.num_denom_cases_on' r $ λ a b b0, begin
  let φ : ℤ →+* α := (ring_hom.of f).comp (int.cast_ring_hom ℚ),
  let ψ : ℤ →+* α := (ring_hom.of g).comp (int.cast_ring_hom ℚ),
  rw [rat.mk_eq_div, int.cast_coe_nat],
  have b0' : (b:ℚ) ≠ 0 := nat.cast_ne_zero.2 b0,
  have : ∀ n : ℤ, f n = g n := λ n,
    (ring_hom.eq_int_cast φ n).trans
    (ring_hom.eq_int_cast ψ n).symm,
  calc f (a * b⁻¹)
      = f a * f b⁻¹ * (g (b:ℤ) * g b⁻¹) : by rw [
    int.cast_coe_nat, ← is_ring_hom.map_mul g,
    mul_inv_cancel b0', is_ring_hom.map_one g, mul_one,
    is_ring_hom.map_mul f]
  ... = g a * f b⁻¹ * (f (b:ℤ) * g b⁻¹) : by rw [this a, ← this b]
  ... = g (a * b⁻¹) : by rw [
    int.cast_coe_nat, mul_assoc, ← mul_assoc (f b⁻¹),
    ← is_ring_hom.map_mul f, inv_mul_cancel b0',
    is_ring_hom.map_one f, one_mul,
    is_ring_hom.map_mul g]
end

end

-- Important: gonna need this
-- have fC : ∀ (a : ℚ), f (C a) = C a,
-- { intro a, show (f ∘ C) a = _, apply rat.ring_hom_unique (f ∘ C) C a },

lemma X_in_terms_of_W_prop' [invertible (p : R)]
  (f : mv_polynomial ℕ R →ₐ[R] mv_polynomial ℕ R)
  (fX : ∀ (n : ℕ), f (X n) = W n)
  (n : ℕ) : f (X_in_terms_of_W p R n) = X n :=
begin
  have fC : ∀ r, f (C r) = C r := f.commutes,
  apply nat.strong_induction_on n,
  clear n, intros n H,
  rw [X_in_terms_of_W_eq],
  simp only [f.map_mul, alg_hom.map_sub f, fC, fX, alg_hom.map_sum],
  rw [finset.sum_congr rfl, (_ : W_ R n -
    (finset.range n).sum (λ i, C (p^i) * (X i)^p^(n-i)) = C (p^n) * X n)],
  { rw [mul_right_comm, ← C_mul, ← mul_pow, mul_inv_of_self, one_pow, C_1, one_mul] },
  { simp [witt_polynomial, nat.sub_self],
    rw finset.sum_range_succ,
    simp },
  { intros i h,
    rw finset.mem_range at h,
    simp only [alg_hom.map_mul f, alg_hom.map_pow f, fC, function.comp_app],
    rw H _ h }
end

@[simp] lemma from_W_to_X_basis_X_in_terms_of_W [invertible (p : R)] (n : ℕ) :
  from_W_to_X_basis p R (X_in_terms_of_W p R n) = X n :=
begin
  apply X_in_terms_of_W_prop' p R _ _ n,
  intro n,
  exact from_W_to_X_basis_X p R n,
end



lemma from_W_to_X_basis_comp_from_X_to_W_basis [invertible (p : R)] :
  (from_W_to_X_basis p R).comp (from_X_to_W_basis p _) = alg_hom.id _ _ :=
begin
  apply mv_polynomial.alg_hom_ext R (mv_polynomial ℕ R),
  intro n,
  rw [from_X_to_W_basis, alg_hom.comp_apply, aeval_X],
  exact from_W_to_X_basis_X_in_terms_of_W p R n
end

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
  (W k).eval₂ C (X_in_terms_of_W p R) = X k :=
begin
  rw ← from_X_to_W_basis_comp_from_W_to_X_basis_apply p R (X k),
  rw from_W_to_X_basis_X,
  refl,
end

@[simp] lemma X_in_terms_of_W_prop [invertible (p : R)] (n : ℕ) :
  (X_in_terms_of_W p R n).eval₂ C (W) = X n :=
begin
  rw ← from_W_to_X_basis_comp_from_X_to_W_basis_apply p R (X n),
  rw from_X_to_W_basis_X,
  refl,
end

variables {idx : Type*}

noncomputable def witt_structure_rat (Φ : mv_polynomial idx ℚ) : ℕ → mv_polynomial (idx × ℕ) ℚ :=
λ n, aeval (λ k : ℕ, (aeval (λ b, (rename_hom (λ i, (b,i)) (W_ ℚ k)))) Φ) (X_in_terms_of_W p ℚ n)

noncomputable def witt_structure_rat' (Φ : mv_polynomial idx ℚ) : ℕ → mv_polynomial (idx × ℕ) ℚ :=
λ n, eval₂ C (λ k : ℕ,
   Φ.eval₂ C (λ b, (rename_hom (λ i, (b,i)) (W_ ℚ k))))
     (X_in_terms_of_W p ℚ n)

theorem witt_structure_rat_prop (Φ : mv_polynomial idx ℚ) (n : ℕ) :
  aeval (witt_structure_rat p Φ) (W_ ℚ n) = aeval (λ b, (rename_hom (λ i, (b,i)) (W_ ℚ n))) Φ :=
begin
  simp only [witt_structure_rat, aeval_def],
  rw [← function.comp, eval₂_assoc, X_in_terms_of_W_prop₂ p _ n, eval₂_X],
end

theorem witt_structure_prop_exists_unique (Φ : mv_polynomial idx ℚ) :
  ∃! (φ : ℕ → mv_polynomial (idx × ℕ) ℚ),
    ∀ (n : ℕ), aeval φ (W_ ℚ n) = aeval (λ b, (rename_hom (λ i, (b,i)) (W_ ℚ n))) Φ :=
begin
  refine ⟨witt_structure_rat p Φ, _, _⟩,
  { intro n, apply witt_structure_rat_prop },
  { intros φ H,
    unfold witt_structure_rat,
    funext n,
    rw show φ n = ((X_in_terms_of_W p ℚ n).eval₂ C (W_ ℚ)).eval₂ C φ,
    { rw [X_in_terms_of_W_prop p, eval₂_X] },
    rw ← eval₂_assoc,
    congr,
    funext k,
    exact H k },
end

lemma witt_structure_rat_rec_aux' (Φ : mv_polynomial idx ℚ) (n) :
  (witt_structure_rat p Φ n) * C (p^n) =
  ((aeval (λ b, (rename_hom (λ i, (b,i)) (W_ ℚ n))) Φ)) -
  ∑ i in range n, C (p^i) * (witt_structure_rat p Φ i)^p^(n-i) :=
begin
  have := @X_in_terms_of_W_aux p _ ℚ _ _ n,
  replace := congr_arg (eval₂ C (λ k : ℕ, (aeval (λ b, (rename_hom (λ i, (b,i)) (W_ ℚ k)))) Φ)) this,
  rw [eval₂_mul, eval₂_C] at this,
  convert this, clear this,
  conv_rhs { simp only [eval₂_sub, eval₂_X] },
  rw sub_right_inj,
  simp only [eval₂_sum],
  apply finset.sum_congr rfl,
  intros i hi,
  rw [eval₂_mul, eval₂_C, eval₂_pow],
  refl
end

lemma witt_structure_rat_rec_aux (Φ : mv_polynomial idx ℚ) (n) :
  (witt_structure_rat p Φ n) * C (p^n) =
  Φ.eval₂ C (λ b, (rename_hom (λ i, (b,i)) (W_ ℚ n))) -
  ∑ i in range n, C (p^i) * (witt_structure_rat p Φ i)^p^(n-i) :=
begin
  have := @X_in_terms_of_W_aux p _ ℚ _ _ n,
  replace := congr_arg (eval₂ C (λ k : ℕ,
  Φ.eval₂ C (λ b, (rename_hom (λ i, (b,i)) (W_ ℚ k))))) this,
  rw [eval₂_mul, eval₂_C] at this,
  convert this, clear this,
  conv_rhs { simp only [eval₂_sub, eval₂_X] },
  rw sub_right_inj,
  simp only [eval₂_sum],
  apply finset.sum_congr rfl,
  intros i hi,
  rw [eval₂_mul, eval₂_C, eval₂_pow],
  refl
end

lemma witt_structure_rat_rec (Φ : mv_polynomial idx ℚ) (n) :
  (witt_structure_rat p Φ n) = C (1/p^n) *
  (Φ.eval₂ C (λ b, (rename_hom (λ i, (b,i)) (W_ ℚ n))) -
  ∑ i in range n, C (p^i) * (witt_structure_rat p Φ i)^p^(n-i)) :=
begin
  rw [← witt_structure_rat_rec_aux p Φ n, mul_comm, mul_assoc,
      ← C_mul, mul_one_div_cancel, C_1, mul_one],
  exact pow_ne_zero _ (nat.cast_ne_zero.2 $ ne_of_gt (nat.prime.pos ‹_›))
end

lemma witt_structure_rat_rec' (Φ : mv_polynomial idx ℚ) (n) :
  (witt_structure_rat p Φ n) = C (1/p^n) *
  (aeval (λ b, (rename_hom (λ i, (b,i)) (W_ ℚ n))) Φ -
  ∑ i in range n, C (p^i) * (witt_structure_rat p Φ i)^p^(n-i)) :=
begin
  apply witt_structure_rat_rec
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
  (IH : ∀ m : ℕ, m < n → map_hom (int.cast_ring_hom ℚ) (witt_structure_int p Φ m) =
    witt_structure_rat p (map_hom (int.cast_ring_hom ℚ) Φ) m) :
  map_hom (int.cast_ring_hom ℚ)
    (((aeval (λ b, (rename_hom (λ i, (b,i)) (W_ ℤ n)))) Φ) -
      (∑ i in range n, C (p^i) * (witt_structure_int p Φ i)^p^(n-i))) =
  aeval (λ b, (rename_hom (λ i, (b,i)) (W_ ℚ n)))
   (map_hom (int.cast_ring_hom ℚ) Φ) -
  (∑ i in range n, C (p^i) * (witt_structure_rat p (map_hom (int.cast_ring_hom ℚ) Φ) i)^p^(n-i)) :=
begin
  rw [ring_hom.map_sub, ring_hom.map_sum],
  apply sub_congr,
  { clear IH,
    simp only [← alg_hom.coe_to_ring_hom, aeval_eq_eval₂_hom, map_eval₂_hom, eval₂_hom_map_hom],
    rw ring_hom.eq_int_cast' ((map_hom (int.cast_ring_hom ℚ)).comp (algebra_map ℤ (mv_polynomial (idx × ℕ) ℤ))),
    simp only [coe_eval₂_hom],
    congr' 1,
    { congr' 1, symmetry, convert ring_hom.eq_int_cast' _ }, -- what's going on here?
    funext b,
    rw [map_hom_rename_hom, map_hom_witt_polynomial], },
  { apply finset.sum_congr rfl,
    intros i hi,
    rw finset.mem_range at hi,
    specialize IH i hi,
    rw [C_pow, ring_hom.map_mul, ring_hom.map_pow, ring_hom.map_pow, IH], -- needs map_hom_C
    -- what follows should be a one-liner
    congr' 1,
    simp only [map_hom, C_pow, ring_hom.coe_of],
    rw map_C, refl, }
end

-- lemma foo (Φ : mv_polynomial idx ℤ) (n : ℕ)
--   (IH : ∀ m : ℕ, m < n → map_hom (int.cast_ring_hom ℚ) (witt_structure_int p Φ m) =
--     witt_structure_rat p (map_hom (int.cast_ring_hom ℚ) Φ) m) :
--   map_hom (int.cast_ring_hom ℚ) (Φ.eval₂ C (λ b, (rename_hom (λ i, (b,i)) (W_ ℤ n))) -
--   (∑ i in range n, C (p^i) * (witt_structure_int p Φ i)^p^(n-i))) =
--   ((map_hom (int.cast_ring_hom ℚ) Φ).eval₂ C (λ b, (rename_hom (λ i, (b,i)) (W_ ℚ n))) -
--   (∑ i in range n, C (p^i) * (witt_structure_rat p (map_hom (int.cast_ring_hom ℚ) Φ) i)^p^(n-i))) :=
-- begin
--   rw [ring_hom.map_sub, ring_hom.map_sum],
--   apply sub_congr,
--   { rw map_eval₂', congr' 1, funext b,
--     show map_hom (int.cast_ring_hom ℚ) (rename (prod.mk b) (witt_polynomial p n)) =
--       rename (prod.mk b) (witt_polynomial p n),
--     rw [map_rename, map_witt_polynomial], },
--   apply finset.sum_congr rfl,
--   intros i hi,
--   rw finset.mem_range at hi,
--   specialize IH i hi,
--   rw [map_mul, map_C, map_pow, IH],
--   norm_cast
-- end
.

def doh {α : Type*} [comm_ring α] : add_comm_monoid α := by apply_instance
def dah {α : Type*} [comm_ring α] : add_monoid α := by apply_instance

-- def bah {α : Type*} [comm_ring α] (n : ℕ) :
--   is_add_monoid_hom (ideal.quotient.mk (ideal.span ({((p^(n+1) : ℕ) : α)} : set α))) :=
-- (ideal.quotient.mk_hom (ideal.span ({((p^(n+1) : ℕ) : α)} : set α))).is_semiring_hom.is_add_monoid_hom
.

def boh {α : Type*} {β : Type*} [comm_semiring α] [comm_semiring β] (f : α → β) [is_semiring_hom f] :
  is_add_monoid_hom f := by apply_instance
-- set_option class.instance_max_depth 50

-- def aahrg (k : ℕ) (φ) : ((C (p : ℤ) ^ k * φ : mv_polynomial ι ℤ) modₑ ↑p) =
--   (0 : ideal.quotient (ideal.span {(p : mv_polynomial ι ℤ)})) := _

-- set_option pp.all true

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

-- lemma quux (n : ℕ) :
--   ((W_ ℤ (n + 1)) modₑ (↑(p^(n+1)) : mv_polynomial ℕ ℤ)) =
--   ((eval₂ C (λ i, ((X i)^p)) (W_ ℤ n)) modₑ (↑(p^(n+1)) : mv_polynomial ℕ ℤ)) :=
-- begin
--   delta witt_polynomial,
--   rw [← finset.sum_hom _ (ideal.quotient.mk _),
--       ← finset.sum_hom _ (eval₂ C (λ (i : ℕ), X i ^ p)),
--       ← finset.sum_hom _ (ideal.quotient.mk _),
--       finset.sum_range_succ],
--   all_goals {try { apply doh }},
--   work_on_goal 0 {
--     convert zero_add _ using 1,
--     work_on_goal 1 { apply dah },
--     congr' 1,
--     work_on_goal 0 {
--       apply ideal.quotient.eq_zero_iff_mem.mpr,
--       apply ideal.mul_mem_right _ _,
--       apply ideal.subset_span,
--       rw [mem_singleton_iff, ← C_eq_coe_nat],
--       norm_cast },
--     apply finset.sum_congr rfl,
--     intros i hi,
--     rw [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, ← pow_mul],
--     congr,
--     rw [mul_comm, ← nat.pow_succ],
--     rw finset.mem_range at hi,
--     congr,
--     replace hi := nat.le_of_lt_succ hi,
--     exact nat.succ_sub hi },
--   all_goals { try {apply bah} },
--   { refine @boh _ _ _ _ _ _, },
-- end
.

lemma eq_mod_iff_dvd_sub' (a b c : R) :
  (@ideal.quotient.mk_hom R _ (ideal.span {c}) a) = (@ideal.quotient.mk_hom R _ (ideal.span {c}) b) ↔
  c ∣ a - b :=
by rw [← sub_eq_zero, ← ring_hom.map_sub,
  ← ideal.mem_span_singleton, ← ideal.quotient.eq_zero_iff_mem]; refl

lemma eq_mod_iff_dvd_sub (a b c : R) :
  (a modₑ c) = (b modₑ c) ↔ c ∣ a - b :=
by rw [← sub_eq_zero, ← ideal.quotient.mk_sub,
  ideal.quotient.eq_zero_iff_mem, ideal.mem_span_singleton]

lemma fermat_little' (p : ℕ) [hp : fact p.prime] (a : zmod p) : a^p = a :=
begin
  have ppos : p > 0 := nat.prime.pos ‹_›,
  by_cases h : a = 0,
  { subst a, apply zero_pow ppos },
  { have := zmod.fermat_little p h,
    replace := congr_arg (λ x, a * x) this,
    simp at this,
    convert this,
    rw ← pow_succ, congr, clear this h a hp,
    revert ppos p, omega manual nat }
end

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

lemma int_pol_mod_p (φ : mv_polynomial ι ℤ) :
  ((φ.eval₂ C (λ i, (X i)^p)) modₑ ↑p) = (φ^p modₑ ↑p) :=
begin
  apply mv_polynomial.induction_on φ,
  { intro n, rw [eval₂_C, eq_mod_iff_dvd_sub, ← C_eq_coe_nat, ← C_pow, ← C_sub],
    suffices : (p : ℤ) ∣ n - n^p,
    { rcases this with ⟨d, h⟩, refine ⟨C d, _⟩, rw [h, C_mul, int.nat_cast_eq_coe_nat] },
      rw ← (char_p.int_cast_eq_zero_iff (zmod p) p),
      rw [int.cast_sub, int.cast_pow, sub_eq_zero],
      symmetry, apply fermat_little' },
  { intros f g hf hg, rw [eval₂_add, ideal.quotient.mk_add, hf, hg, modp.add_pow], assumption },
  { intros f i hf, rw [eval₂_mul, ideal.quotient.mk_mul, hf, eval₂_X, mul_pow, ideal.quotient.mk_mul] }
end

lemma zrum (a b : R) (h : (a modₑ (p : R)) = (b modₑ (p : R))) (k : ℕ) :
  (a^(p^k) modₑ (p^(k+1) : R)) = (b^(p^k) modₑ (p^(k+1) : R)) :=
begin
  rw eq_mod_iff_dvd_sub at h ⊢,
  apply dvd_sub_pow_of_dvd_sub,
  exact h
end

lemma rat_mv_poly_is_integral_iff (p : mv_polynomial ι ℚ) :
  map (int.cast_ring_hom ℚ) (finsupp.map_range rat.num (rat.coe_int_num 0) p) = p ↔
  ∀ m, (coeff m p).denom = 1 :=
begin
  split; intro h,
  { rw ← mv_polynomial.ext_iff at h, intro m,
    rw [← h m, coeff_map],
    apply rat.coe_int_denom },
  { apply mv_polynomial.ext, intro m,
    rw coeff_map,
    apply integral_of_denom_eq_one,
    exact h m }
end

lemma baz (φ : mv_polynomial ι ℤ) (c) (n : ℤ) (hn : n ≠ 0) :
  (coeff c (C (1 / (n : ℚ)) * map (int.cast_ring_hom ℚ) φ)).denom = 1 ↔ n ∣ coeff c φ :=
begin
  split,
  { intro h,
    rw [coeff_C_mul, coeff_map] at h,
    refine ⟨((1 : ℚ) / n * ↑(coeff c φ)).num, _⟩,
    suffices : (↑(coeff c φ) : ℚ) = (_ : ℤ),
    { rwa int.cast_inj at this },
    replace h := integral_of_denom_eq_one _ h,
    dsimp at h,
    rw [int.cast_mul, h, ← mul_assoc, mul_one_div_cancel, one_mul],
    exact_mod_cast hn },
  { rintros ⟨d, h⟩,
    rw [coeff_C_mul, coeff_map, h],
    dsimp,
    rw [int.cast_mul, ← mul_assoc, one_div_mul_cancel, one_mul],
    { apply rat.coe_int_denom },
    { exact_mod_cast hn } }
end

lemma baz_nat (φ : mv_polynomial ι ℤ) (c) (n : ℕ) (hn : n ≠ 0) :
  (coeff c (C (1 / (n : ℚ)) * map (int.cast_ring_hom ℚ) φ)).denom = 1 ↔ (n : ℤ) ∣ coeff c φ :=
begin
  have := baz φ c n (by exact_mod_cast hn),
  rwa [show ((n : ℤ) : ℚ) = n, by simp] at this,
end
.

lemma droj (φ : mv_polynomial ι ℤ) (n : ℕ) (hn : n ≠ 0) :
  (n : mv_polynomial ι ℤ) ∣ φ ↔ ∀ c, (n : ℤ) ∣ coeff c φ :=
begin
  split,
  { rintros ⟨d, rfl⟩ c, rw [← C_eq_coe_nat, coeff_C_mul, int.nat_cast_eq_coe_nat], apply dvd_mul_right },
  { intro h, refine ⟨finsupp.map_range (λ k, k/n) (by simp) φ, _⟩,
    apply mv_polynomial.ext,
    intro c,
    rw [← C_eq_coe_nat, coeff_C_mul],
    dsimp [coeff] at h ⊢,
    rcases h c with ⟨d, h⟩,
    rw [h, int.mul_div_cancel_left, int.nat_cast_eq_coe_nat],
    exact_mod_cast hn }
end

-- lemma eval₂_mod (φ : mv_polynomial ι R) (f : R → S) [is_semiring_hom f] (g₁ : ι → S) (g₂ : ι → S) (s : S)
--   (h : ∀ i, (g₁ i modₑ s) = (g₂ i modₑ s)) :
--   ((φ.eval₂ f g₁) modₑ s) = (φ.eval₂ f g₂ modₑ s) :=
-- begin
--   rw [eval₂_comp_right (ideal.quotient.mk _) f g₁, eval₂_comp_right (ideal.quotient.mk _) f g₂,
--     function.comp, function.comp],
--   all_goals {try {apply_instance}},
--   congr, funext i, rw h i,
-- end

lemma rename_mod (φ₁ φ₂ : mv_polynomial ι R) (g : ι → σ) (r : mv_polynomial ι R)
  (h : (φ₁ modₑ r) = (φ₂ modₑ r)) :
  ((φ₁.rename g) modₑ (r.rename g)) = (φ₂.rename g modₑ (r.rename g)) :=
begin
  rw eq_mod_iff_dvd_sub at h ⊢,
  rcases h with ⟨d, h⟩,
  refine ⟨d.rename g, _⟩,
  rw [← rename_sub, ← rename_mul],
  congr, exact h,
end

lemma rename_mod_C (φ₁ φ₂ : mv_polynomial ι R) (g : ι → σ) (r : R)
  (h : (φ₁ modₑ (C r)) = (φ₂ modₑ (C r))) :
  ((φ₁.rename g) modₑ (C r)) = (φ₂.rename g modₑ (C r)) :=
begin
  rwa [← rename_C g, rename_mod],
end

lemma blur' (Φ : mv_polynomial idx ℤ) (n : ℕ)
  (IH : ∀ m : ℕ, m < (n + 1) →
    map_hom (int.cast_ring_hom ℚ) (witt_structure_int p Φ m) =
      witt_structure_rat p (map_hom (int.cast_ring_hom ℚ) Φ) m) :
  aeval (λ b, rename_hom (λ i, (b, i)) (aeval (λ i, ((X i ^ p : mv_polynomial ℕ ℤ))) (W_ ℤ n))) Φ =
  aeval (λ i, aeval (λ bi, (X bi)^p) (witt_structure_int p Φ i)) (W_ ℤ n) :=
begin
  -- have aux : ∀ x, (aeval (λ m, (map_hom (int.cast_ring_hom ℚ)) (witt_structure_int p Φ m))) (X x) =
  --   (map_hom (int.cast_ring_hom ℚ)) (witt_structure_int p Φ x) :=
  -- λ x, aeval_X ℚ (mv_polynomial (idx × ℕ) ℚ)
  --   (λ m, (map_hom (int.cast_ring_hom ℚ)) (witt_structure_int p Φ m)) x,
  have aux := λ x, aeval_X ℤ _ (witt_structure_int p Φ) x,
  have aux₂ : ∀ n : ℕ, (algebra_map ℚ (mv_polynomial (idx × ℕ) ℚ)) (p ^ n) =
    map_hom (int.cast_ring_hom ℚ) (aeval (witt_structure_int p Φ) (C (p ^ n : ℤ))),
  { intro n, rw [map_aeval, eval₂_hom_C, ring_hom.eq_int_cast],
    show C (p ^ n : ℚ) = (p ^ n : ℤ),
    rw [C_pow, C_eq_coe_nat], norm_cast },
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
    apply eval₂_hom_congr _ _ rfl,
    { convert ring_hom.ext_int _ _ },
    { funext i, apply eval₂_hom_congr _ _ rfl,
      { convert ring_hom.ext_int _ _ },
      { funext k,
        rw [map_hom_rename_hom, map_hom_X, rename_hom_X] } } },
  { simp only [map_aeval, map_eval₂_hom, aeval_eq_eval₂_hom', ring_hom.map_pow,
      eval₂_hom_map_hom, witt_polynomial, int.nat_cast_eq_coe_nat],
    apply eval₂_hom_congr _ _ rfl,
    { convert ring_hom.ext_int _ _ },
    { funext i, apply eval₂_hom_congr _ _ rfl,
      { convert ring_hom.ext_int _ _ },
      { funext bi, rw map_hom_X } } }
end
.
-- lemma blur (Φ : mv_polynomial idx ℤ) (n : ℕ)
--   (IH : ∀ m : ℕ, m < (n + 1) →
--     map (int.cast_ring_hom ℚ) (witt_structure_int p Φ m) =
--       witt_structure_rat p (map (int.cast_ring_hom ℚ) Φ) m) :
--   Φ.eval₂ C (λ b, rename (λ i, (b, i)) (eval₂ C (λ i, ((X i)^p)) (W_ ℤ n))) =
--   (W_ ℤ n).eval₂ C (λ i, (witt_structure_int p Φ i).eval₂ C $ λ bi, (X bi)^p) :=
-- begin
--   apply mv_polynomial.coe_int_rat_map_injective,
--   have := witt_structure_rat_prop p (map (int.cast_ring_hom ℚ) Φ) n,
--   replace := congr_arg (λ ψ, eval₂ C (λ bi, (X bi)^p) ψ) this,
--   simp only [map_eval₂, function.comp, map_rename, map_witt_polynomial, map_pow, map_X] at this ⊢,
--   rw [← eval₂_assoc, ← eval₂_assoc] at this,
--   simp only [function.comp, eval₂_rename] at this,
--   simp only [rename_prodmk_eval₂, rename_pow, rename_X],
--   rw ← this, clear this,
--   apply eval₂_congr,
--   intros i c hi hc,
--   rw IH,
--   delta witt_polynomial at hc,
--   rw ← finset.sum_hom _ (coeff c) at hc,
--   work_on_goal 0 {
--     rcases finset.exists_ne_zero_of_sum_ne_zero hc with ⟨j, hj, hcj⟩,
--     dsimp only at hcj,
--     rw [X_pow_eq_single, C_mul_monomial, coeff_monomial] at hcj,
--     split_ifs at hcj,
--     { subst c,
--       rw finsupp.mem_support_single at hi,
--       cases hi, subst i, rwa finset.mem_range at hj, },
--     { contradiction }
--   },
--   exact coeff.is_add_monoid_hom c
-- end
.

-- lemma eval₂_sum (f : R → S) [is_semiring_hom f] (g : ι → S) (X : finset σ) (φ : σ → mv_polynomial ι R) :
--   eval₂ f g (X.sum φ) = X.sum (λ s, eval₂ f g (φ s)) :=
-- eval₂_sum _ _ _ _
-- begin
--   apply finset.induction_on X, {simp},
--   intros s Y hs, simp [*, finset.sum_insert],
-- end

local attribute [-simp] coe_eval₂_hom

-- lemma foobar (k : ℕ) (a b : zmod (p^k)) :

-- lemma xyzzy (n k : ℕ) (Φ : mv_polynomial idx ℤ) (hk : k ∈ range (n + 1)) :
--   C (↑p ^ k) * (eval₂_hom ((map_hom (int.cast_ring_hom (zmod (p ^ (n + 1))))).comp
--     (algebra_map ℤ (mv_polynomial (idx) ℤ)))
--            (λ (i : idx), X i ^ p)) Φ ^ p ^ (n - k) =
--     C (p ^ k) * (map_hom (int.cast_ring_hom (zmod (p ^ (n + 1))))) Φ ^ p ^ (n + 1 - k) :=
-- begin
--   rw finset.mem_range at hk,
--   rw show p ^ (n + 1 - k) = p * p ^ (n - k),
--   { rw [mul_comm p, ← nat.pow_succ, nat.succ_eq_add_one], congr, omega },
--   rw pow_mul,
--   calc _ = map_hom (int.cast_ring_hom (zmod (p^(n+1)))) (C (p ^ k) * (aeval (λ (i : idx), X i ^ p) Φ) ^ p ^ (n - k)) : _
--      ... = _ : _,
--   { rw [ring_hom.map_mul, map_hom_C, ring_hom.map_pow, ring_hom.map_pow, map_aeval],
--     congr' 1, { refl },
--     rw [eval₂_hom_congr _ _ rfl],
--     { convert ring_hom.ext_int _ _ },
--     { funext i, rw [ring_hom.map_pow, map_hom_X] } },
--   rw [← sub_eq_zero, ← ring_hom.map_pow, ← ring_hom.map_pow, ← ring_hom.map_pow,
--       ← mul_sub, ← ring_hom.map_sub],

--   rw [← C_dvd_iff_zmod, ← int.nat_cast_eq_coe_nat],
--   rw [C_eq_coe_nat],
--   rw show p^(n+1) = p^k * p^(n+1-k),
--   { rw ← nat.pow_add, congr' 1, omega },
--   rw nat.cast_mul,
--   apply mul_dvd_mul_left,

--   -- rw ← mv_polynomial.zmod_pow_char,
-- end

lemma map_hom_witt_structure_int (Φ : mv_polynomial idx ℤ) (n : ℕ) :
  map_hom (int.cast_ring_hom ℚ) (witt_structure_int p Φ n) =
    witt_structure_rat p (map_hom (int.cast_ring_hom ℚ) Φ) n :=
begin
  apply nat.strong_induction_on n, clear n,
  intros n IH,
  erw rat_mv_poly_is_integral_iff,
  intro c,
  rw witt_structure_rat_rec' p _ n,
  rw coeff_C_mul,
  rw [mul_comm, mul_div_assoc', mul_one],
  rw ← foo' p Φ n IH,
  erw coeff_map,
  rw show (p : ℚ)^n = ((p^n : ℕ) : ℤ), by norm_cast,
  erw rat.denom_div_cast_eq_one_iff,
  work_on_goal 1 { rw int.coe_nat_pow, apply pow_ne_zero, exact_mod_cast ne_of_gt (nat.prime.pos ‹_›) },
  induction n with n ih, {simp}, clear ih, revert c,
  rw [← C_dvd_iff_dvd_coeff, nat.succ_eq_add_one],
  rw C_dvd_iff_zmod,
  -- rw ← eq_mod_iff_dvd_sub',
  rw [ring_hom.map_sub, sub_eq_zero, map_aeval],
  simp only [witt_polynomial_zmod_self, map_aeval, map_hom_witt_polynomial,
    map_hom_rename_hom, ring_hom.map_pow, rename_hom_X],

  -- simp only [ring_hom.map_sum, ring_hom.map_mul, ring_hom.map_pow, map_hom_C],

  have key := congr_arg (map_hom (int.cast_ring_hom (zmod (p^(n+1))))) (blur' p Φ n IH),

  calc _ = _ : _
     ... = _ : key
     ... = _ : _,

  { clear key IH,
    rw map_aeval,
    apply eval₂_hom_congr _ _ rfl,
    { convert ring_hom.ext_int _ _ },
    { funext i,
      rw ← map_hom_witt_polynomial p (int.cast_ring_hom (zmod _)) n,
      simp only [map_hom_X, map_aeval, map_eval₂_hom, ring_hom.map_pow,
        rename_hom_X, eval₂_hom_map_hom],
      apply eval₂_hom_congr _ rfl rfl,
      { convert ring_hom.ext_int _ _ } } },

  { clear key IH,
    rw [aeval_witt_polynomial, ring_hom.map_sum, ring_hom.map_sum],
    apply finset.sum_congr rfl,
    intros k hk, rw finset.mem_range at hk,
    rw [← sub_eq_zero, ← ring_hom.map_sub, ← C_dvd_iff_zmod],
    rw [← int.nat_cast_eq_coe_nat, C_eq_coe_nat],
    rw [← int.nat_cast_eq_coe_nat, C_pow, C_eq_coe_nat, ← mul_sub],
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
    apply eval₂_hom_congr _ _ rfl,
    { convert ring_hom.ext_int _ _ },
    { funext i, rw [ring_hom.map_pow, map_hom_X] } }

    -- calc _ =
    -- (eval₂_hom
    --        ((algebra_map (zmod (p^(n+1))) (mv_polynomial (idx × ℕ) (zmod (p^(n+1)))))
    --          .comp
    --         (int.cast_ring_hom (zmod (p ^ (n + 1)))))
    --         )
    --        (λ (i : idx × ℕ), X i ^ p)
    --     (witt_structure_int p Φ k) ^
    --   p ^ (n - k) : _
    --   ... = _ : _,
    -- rw ← eval₂_hom_map_hom,

  -- calc _ = (Φ.eval₂ C (λ (b : idx), rename (λ (i : ℕ), (b, i)) (witt_polynomial p _ (nat.succ n))) modₑ ↑(p^(n+1))) : rfl
  --    ... = (Φ.eval₂ C (λ (b : idx), rename (λ (i : ℕ), (b, i)) (eval₂ C (λ i, ((X i)^p)) (witt_polynomial p _ n))) modₑ ↑(p^(n+1))) :
  --    begin
  --     apply eval₂_mod, intro b,
  --     rw [← C_eq_coe_nat], apply rename_mod_C, rw C_eq_coe_nat,
  --     rw [nat.succ_eq_add_one],
  --     exact quux p n,
  --    end
  --    ... = _ : by rw blur p Φ n IH
  --    ... = _ :
  --    begin
  --     delta witt_polynomial,
  --     conv_lhs { congr, simp [eval₂_sum] },
  --     rw [← finset.sum_hom _ (ideal.quotient.mk _), ← finset.sum_hom _ (ideal.quotient.mk _)],
  --     { apply finset.sum_congr rfl,
  --       intros i hi,
  --       rw finset.mem_range at hi, replace hi := nat.le_of_lt_succ hi,
  --       dsimp,
  --       rw [eval₂_mul, ← C_pow, eval₂_C, eval₂_pow, eval₂_X],
  --       rw [show (p:ℤ)^i = (p^i : ℕ), by simp, ← int.nat_cast_eq_coe_nat, C_eq_coe_nat],
  --       rw [eq_mod_iff_dvd_sub, ← mul_sub],
  --       rw show p^(n+1) = p^i * p^(n+1-i),
  --       { rw ← nat.pow_add, congr' 1, clear IH, revert hi i n, omega manual nat },
  --       rw nat.cast_mul,
  --       apply mul_dvd_mul_left,
  --       rw show n + 1 - i = n - i + 1,
  --       { exact nat.succ_sub hi },
  --       rw nat.cast_pow,
  --       rw [nat.pow_succ, mul_comm, pow_mul],
  --       apply dvd_sub_pow_of_dvd_sub,
  --       rw ← eq_mod_iff_dvd_sub,
  --       apply int_pol_mod_p },
  --       apply doh, all_goals {apply bah}
  --    end,
end
.

-- lemma witt_structure_int_prop.aux (Φ : mv_polynomial idx ℤ) (n : ℕ) :
--   map (int.cast_ring_hom ℚ) ((witt_polynomial p n).eval₂ C (witt_structure_int p Φ)) =
--   (witt_polynomial p n).eval₂ C (witt_structure_rat p (map (int.cast_ring_hom ℚ) Φ)) :=
-- begin
--   rw [map_eval₂, map_witt_polynomial],
--   congr' 1,
--   funext i,
--   apply map_hom_witt_structure_int
-- end

theorem witt_structure_int_prop (Φ : mv_polynomial idx ℤ) (n) :
  aeval (witt_structure_int p Φ) (W_ ℤ n) = aeval (λ b, (rename_hom (λ i, (b,i)) (W_ ℤ n))) Φ :=
begin
  apply mv_polynomial.coe_int_rat_map_injective,
  convert witt_structure_rat_prop p (map_hom (int.cast_ring_hom ℚ) Φ) n,
  { simp only [← alg_hom.coe_to_ring_hom, aeval_eq_eval₂_hom, map_eval₂_hom],
    rw [← map_hom_witt_polynomial p (int.cast_ring_hom ℚ), eval₂_hom_map_hom],
    simp only [coe_eval₂_hom],
    congr' 2,
    { convert ring_hom.ext_int _ _, },
    { funext i, apply map_hom_witt_structure_int } },
  { simp only [← alg_hom.coe_to_ring_hom, aeval_eq_eval₂_hom, map_eval₂_hom, eval₂_hom_map_hom],
    simp only [coe_eval₂_hom],
    congr' 2,
    { convert ring_hom.ext_int _ _, },
    { funext b,
      simp only [map_hom_rename_hom, map_hom_witt_polynomial] } }
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
        apply eval₂_hom_congr _ rfl rfl, convert ring_hom.ext_int _ _ },
      { rw [map_aeval, aeval_eq_eval₂_hom', eval₂_hom_map_hom],
        apply eval₂_hom_congr _ _ rfl,
        { convert ring_hom.ext_int _ _ },
        { funext i, rw [map_hom_rename_hom, map_hom_witt_polynomial] } } },
    { intro n, apply witt_structure_rat_prop } },
end
.

-- lemma eval₂_rename_prodmk (f : R → S) [is_semiring_hom f] (g : σ × ι → S) (s : σ) (φ : mv_polynomial ι R) :
--   (rename (prod.mk s) φ).eval₂ f g = eval₂ f (λ i, g (s, i)) φ :=
-- eval₂_rename_prodmk f φ g s
-- begin
--   apply mv_polynomial.induction_on φ,
--   { intro r, rw [rename_C, eval₂_C, eval₂_C] },
--   { intros p q hp hq, rw [rename_add, eval₂_add, eval₂_add, hp, hq] },
--   { intros p i hp, rw [rename_mul, rename_X, eval₂_mul, eval₂_mul, eval₂_X, eval₂_X, hp] }
-- end

-- lemma eval_rename_prodmk (g : σ × ι → R) (s : σ) (φ : mv_polynomial ι R) :
--   (rename (prod.mk s) φ).eval g = eval (λ i, g (s, i)) φ :=
-- eval₂_rename_prodmk id _ _ _

theorem witt_structure_prop (Φ : mv_polynomial idx ℤ) (n) :
  aeval (λ i, map_hom (int.cast_ring_hom R) (witt_structure_int p Φ i)) (W_ ℤ n) =
  aeval (λ b, (rename_hom (λ i, (b,i)) (W n))) (map_hom (int.cast_ring_hom R) Φ) :=
begin
  convert congr_arg (map_hom (int.cast_ring_hom R)) (witt_structure_int_prop p Φ n),
  { rw [aeval_eq_eval₂_hom', map_aeval],
    simp only [eval₂_hom, ring_hom.coe_of],
    apply eval₂_hom_congr _ rfl rfl,
    convert ring_hom.ext_int _ _ },
  { rw [aeval_eq_eval₂_hom', eval₂_hom_map_hom, map_aeval],
    simp only [eval₂_hom, ring_hom.coe_of],
    apply eval₂_hom_congr _ _ rfl,
    { convert ring_hom.ext_int _ _ },
    { simp only [map_hom_rename_hom, map_hom_witt_polynomial] } }
end

noncomputable def witt_add : ℕ → mv_polynomial (bool × ℕ) ℤ :=
witt_structure_int p (X tt + X ff)

noncomputable def witt_mul : ℕ → mv_polynomial (bool × ℕ) ℤ :=
witt_structure_int p (X tt * X ff)

noncomputable def witt_neg : ℕ → mv_polynomial (unit × ℕ) ℤ :=
witt_structure_int p (-X unit.star)

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

noncomputable instance : has_add (𝕎 p R) :=
⟨λ x y n, aeval (λ bn : bool × ℕ, cond bn.1 (x bn.2) (y bn.2)) (witt_add p n)⟩

noncomputable instance : has_mul (𝕎 p R) :=
⟨λ x y n, (witt_mul p n).eval₂ (int.cast_ring_hom R) $ λ bn, cond bn.1 (x bn.2) (y bn.2)⟩

noncomputable instance : has_neg (𝕎 p R) :=
⟨λ x n, (witt_neg p n).eval₂ (int.cast_ring_hom R) $ λ bn, x bn.2⟩

variable {R}

@[simp] lemma Teichmuller_one : Teichmuller p (1:R) = 1 := rfl

-- TODO(jmc): Prove this
-- lemma Teichmuller_mul (x y : R) :
--   Teichmuller p (x * y) = Teichmuller p x * Teichmuller p y := sorry

variable {p}

noncomputable def ghost_component (n : ℕ) (w : 𝕎 p R) : R :=
(W n).eval w

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
funext $ λ n, is_ring_hom.map_zero f

@[simp] lemma map_one : map f (1 : 𝕎 p R) = 1 :=
funext $ λ n,
match n with
| 0     := is_ring_hom.map_one f
| (n+1) := is_ring_hom.map_zero f
end

@[simp] lemma map_add (x y : 𝕎 p R) :
  map f (x + y) = map f x + map f y :=
funext $ λ n,
begin
  show f (eval₂ (int.cast_ring_hom R) _ _) = eval₂ (int.cast_ring_hom S) _ _,
  rw eval₂_comp_left f,
  congr' 1,
  { funext n, exact (f.comp (int.cast_ring_hom R)).eq_int_cast n, },
  { funext bn, cases bn with b i,
    exact match b with | tt := rfl | ff := rfl end },
  recover, all_goals {apply_instance},
end

@[simp] lemma map_mul (x y : 𝕎 p R) :
  map f (x * y) = map f x * map f y :=
funext $ λ n,
begin
  show f (eval₂ (int.cast_ring_hom R) _ _) = eval₂ (int.cast_ring_hom S) _ _,
  rw eval₂_comp_left f,
  congr' 1,
  { funext n, exact (f.comp (int.cast_ring_hom R)).eq_int_cast n, },
  { funext bn, cases bn with b i,
    exact match b with | tt := rfl | ff := rfl end },
  recover, all_goals {apply_instance},
end

@[simp] lemma map_neg (x : 𝕎 p R) :
  map f (-x) = -map f x :=
funext $ λ n,
begin
  show f (eval₂ (int.cast_ring_hom R) _ _) = eval₂ (int.cast_ring_hom S) _ _,
  rw eval₂_comp_left f,
  congr' 1,
  { funext n, exact (f.comp (int.cast_ring_hom R)).eq_int_cast n, },
  recover, all_goals {apply_instance},
end

end map

noncomputable def ghost_map : 𝕎 p R → (ℕ → R) := λ w n, ghost_component n w

@[simp] lemma ghost_map.zero : ghost_map (0 : 𝕎 p R) = 0 :=
funext $ λ n,
begin
  delta ghost_map ghost_component witt_polynomial eval,
  rw eval₂_sum,
  apply finset.sum_eq_zero,
  intros i hi,
  rw [eval₂_mul, eval₂_pow, eval₂_X],
  convert mul_zero _,
  apply zero_pow _,
  apply nat.pow_pos,
  apply nat.prime.pos, assumption,
end

@[simp] lemma ghost_map.one : ghost_map (1 : 𝕎 p R) = 1 :=
funext $ λ n,
begin
  delta ghost_map ghost_component witt_polynomial eval,
  rw eval₂_sum,
  have : 0 ∈ finset.range (n+1),
  { rw finset.mem_range, exact nat.succ_pos n },
  rw ← finset.insert_erase this,
  rw finset.sum_insert (finset.not_mem_erase 0 (finset.range (n + 1))),
  convert add_zero _,
  { apply finset.sum_eq_zero, intros i hi,
    rw [eval₂_mul, eval₂_pow, eval₂_X],
    rw finset.mem_erase at hi,
    suffices H : (1 : 𝕎 p R) i = 0,
    { rw [H, zero_pow, mul_zero], apply nat.pow_pos, exact nat.prime.pos ‹_› },
    rw ← Teichmuller_one, cases hi with hi bla, revert hi,
    exact match i with
    | 0 := λ H, false.elim (H rfl)
    | (n+1) := λ H, rfl
    end },
  { rw [eval₂_mul, eval₂_pow, eval₂_X, eval₂_C],
    dsimp, rw one_mul, symmetry,
    apply one_pow }
end

variable {R}

-- Unfortunately the following lemma doesn't typecheck,
-- because we don't know that (𝕎 p R) is a comm_semiring

-- @[simp] lemma ghost_map.compat (x : idx → 𝕎 p R) (φ : mv_polynomial (idx × ℕ) ℤ) :
--   ghost_map (φ.eval₂ coe (λ bn, x bn.1)) = φ.eval₂ coe (λ bn, ghost_map (x bn.1)) :=
-- funext $ λ n,
-- begin
--   delta ghost_map ghost_component,
--   have := congr_arg (λ (ψ : mv_polynomial (bool × ℕ) R), ψ.eval $ λ (bn : bool × ℕ), cond bn.1 (x bn.2) (y bn.2)) (witt_structure_prop p (X tt + X ff) n),
--   convert this using 1; clear this,
--   { delta witt_vectors.has_add witt_add, dsimp [eval],
--     rw ← eval₂_assoc' _ _ _ _,
--     work_on_goal 0 { congr' 1, funext i, apply eval₂_eq_eval_map },
--     all_goals {try {assumption}, try {apply_instance}} },
--   { dsimp,
--     rw [mv_polynomial.map_add, eval₂_add, eval_add],
--     congr' 1,
--     all_goals {
--       erw [mv_polynomial.map_X (int.cast_ring_hom R), eval₂_X, eval_rename_prodmk],
--       congr } }
-- end

@[simp] lemma ghost_map.add (x y : 𝕎 p R) :
  ghost_map (x + y) = ghost_map x + ghost_map y :=
funext $ λ n,
begin
  delta ghost_map ghost_component,
  have := congr_arg (λ (ψ : mv_polynomial (bool × ℕ) R), ψ.eval $ λ (bn : bool × ℕ), cond bn.1 (x bn.2) (y bn.2)) (witt_structure_prop p _ (X tt + X ff) n),
  convert this using 1; clear this,
  { delta witt_vectors.has_add witt_add, dsimp only [eval],
    rw ← eval₂_assoc' _ _ _ _,
    work_on_goal 0 { congr' 1, funext i, apply eval₂_eq_eval_map },
    all_goals {try {assumption}, try {apply_instance}} },
  { dsimp only,
    rw [mv_polynomial.map_add, eval₂_add, eval_add],
    dsimp,
    congr' 1,
    all_goals {
      erw [mv_polynomial.map_X (int.cast_ring_hom R), eval₂_X, eval_rename_prodmk],
      congr } }
end

@[simp] lemma ghost_map.mul (x y : 𝕎 p R) :
  ghost_map (x * y) = ghost_map x * ghost_map y :=
funext $ λ n,
begin
  delta ghost_map ghost_component,
  have := congr_arg (λ (ψ : mv_polynomial (bool × ℕ) R), ψ.eval $ λ (bn : bool × ℕ), cond bn.1 (x bn.2) (y bn.2)) (witt_structure_prop p _ (X tt * X ff) n),
  convert this using 1; clear this,
  { delta witt_vectors.has_mul witt_mul, dsimp only [eval],
    rw ← eval₂_assoc' _ _ _ _,
    work_on_goal 0 { congr' 1, funext i, apply eval₂_eq_eval_map },
    all_goals {try {assumption}, try {apply_instance}} },
  { dsimp only,
    rw [mv_polynomial.map_mul, eval₂_mul, eval_mul],
    dsimp,
    congr' 1,
    all_goals {
      erw [mv_polynomial.map_X (int.cast_ring_hom R), eval₂_X, eval_rename_prodmk],
      congr } }
end

@[simp] lemma ghost_map.neg (x : 𝕎 p R) :
  ghost_map (-x) = - ghost_map x :=
funext $ λ n,
begin
  delta ghost_map ghost_component,
  have := congr_arg (λ (ψ : mv_polynomial (unit × ℕ) R), ψ.eval $ λ (bn : unit × ℕ), (x bn.2)) (witt_structure_prop p _ (-X unit.star) n),
  convert this using 1; clear this,
  { delta witt_vectors.has_neg witt_neg, dsimp only [eval],
    rw ← eval₂_assoc' _ _ _ _,
    work_on_goal 0 { congr' 1, funext i, apply eval₂_eq_eval_map },
    all_goals {try {assumption}, try {apply_instance}} },
  { dsimp only,
    rw [mv_polynomial.map_neg, map_X],
    have := eval_rename_prodmk (W n) (λ i : unit × ℕ, x i.2) (),
    dsimp only at this,
    dsimp,
    rw ← this, clear this,
    rw ← eval_neg,
    congr' 1,
    have := eval₂_neg (X ()) C (λ (b : unit), rename (prod.mk b) (W n)),
    rw eval₂_X at this,
    exact this.symm }
end
.

variables (p) (R)

noncomputable def ghost_map.equiv_of_invertible [invertible (p : R)] :
  𝕎 p R ≃ (ℕ → R) :=
{ to_fun := ghost_map,
  inv_fun := λ x n, (X_in_terms_of_W p R n).eval x,
  left_inv :=
  begin
    intro x, funext n,
    dsimp [ghost_map, ghost_component, eval],
    rw eval₂_assoc' (id : R → R),
    { convert eval_X _, exact X_in_terms_of_W_prop p R n },
    all_goals { assumption <|> apply_instance }
  end,
  right_inv :=
  begin
    intro x, funext n,
    dsimp [ghost_map, ghost_component, eval],
    rw eval₂_assoc' (id : R → R) x (X_in_terms_of_W p R),
    simp only [eval₂_X, X_in_terms_of_W_prop₂]
  end }

lemma ghost_map.bijective_of_invertible [invertible (p : R)] :
  function.bijective (ghost_map : 𝕎 p R → ℕ → R) :=
(ghost_map.equiv_of_invertible p R).bijective

section
open function

variable (R)

noncomputable def mv_polynomial.counit : mv_polynomial R ℤ →+*  R :=
eval₂_hom (int.cast_ring_hom R) id

-- instance mv_polynomial.counit.is_ring_hom : is_ring_hom (mv_polynomial.counit R) :=
-- by delta mv_polynomial.counit; apply_instance

lemma counit_surjective : surjective (mv_polynomial.counit R) :=
λ r, ⟨X r, eval₂_X _ _ _⟩

end

-- instance map_invertible (A : Type*) [comm_ring A] [algebra R A] (n : ℕ) [invertible (n : R)] :
--   invertible (n : A) :=
-- _

noncomputable def helper : invertible (p : mv_polynomial R ℚ) :=
{ inv_of := C (⅟p),
  inv_of_mul_self := by { rw [← C_eq_coe_nat, ← C_mul, inv_of_mul_self, C_1] },
  mul_inv_of_self := by { rw [← C_eq_coe_nat, ← C_mul, mul_inv_of_self, C_1] } }

local attribute [instance] helper

variable (R)

noncomputable def aux₁ : comm_ring (𝕎 p (mv_polynomial R ℚ)) :=
comm_ring_of_injective (ghost_map)
  (ghost_map.bijective_of_invertible p _).1
  (@ghost_map.zero p _ (mv_polynomial R ℚ) _)
  (ghost_map.one) (ghost_map.add) (ghost_map.mul) (ghost_map.neg)

local attribute [instance] aux₁
.

-- experiment... this isn't defeq
-- example : mv_polynomial.map (int.cast_ring_hom R) = aeval ℤ (mv_polynomial σ R) X :=
-- begin
--   delta mv_polynomial.map,
--   dsimp [aeval, eval₂_hom],
-- end

noncomputable def aux₂ : comm_ring (𝕎 p (mv_polynomial R ℤ)) :=
-- have hom : is_ring_hom (mv_polynomial.map coe : mv_polynomial R ℤ → mv_polynomial R ℚ), by apply_instance,
comm_ring_of_injective (map $ mv_polynomial.map (int.cast_ring_hom ℚ))
  (map_injective _ $ mv_polynomial.coe_int_rat_map_injective _)
  (map_zero _) _ _ _ _
  -- (@map_zero _ _ _ _ _ _ _ _ _ hom)
  -- (@map_one _ _ _ _ _ _ _ _ _ hom)
  -- (@map_add _ _ _ _ _ _ _ _ _ hom)
  -- (@map_mul _ _ _ _ _ _ _ _ _ hom)
  -- (@map_neg _ _ _ _ _ _ _ _ _ hom)

local attribute [instance] aux₂
.

noncomputable instance : comm_ring (𝕎 p R) :=
comm_ring_of_surjective
(map $ mv_polynomial.counit _) (map_surjective _ $ counit_surjective _)
  (@map_zero _ _ _ _ _ _ _ _ _ (mv_polynomial.counit.is_ring_hom R))
  (@map_one _ _ _ _ _ _ _ _ _ (mv_polynomial.counit.is_ring_hom R))
  (@map_add _ _ _ _ _ _ _ _ _ (mv_polynomial.counit.is_ring_hom R))
  (@map_mul _ _ _ _ _ _ _ _ _ (mv_polynomial.counit.is_ring_hom R))
  (@map_neg _ _ _ _ _ _ _ _ _ (mv_polynomial.counit.is_ring_hom R))

end witt_vectors

attribute [irreducible] witt_vectors

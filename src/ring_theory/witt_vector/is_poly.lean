import ring_theory.witt_vector.basic
import ring_theory.witt_vector.witt_vector_preps

namespace witt_vector

variables {p : ℕ} {R S σ idx : Type*} [hp : fact p.prime] [comm_ring R] [comm_ring S]

local notation `𝕎` := witt_vector p -- type as `\bbW`

local attribute [semireducible] witt_vector
local attribute [instance] mv_polynomial.invertible_rat_coe_nat

open mv_polynomial
local attribute [-simp] coe_eval₂_hom

include hp
variables (p)

section ghost_equation
noncomputable theory

lemma poly_eq_of_witt_polynomial_bind_eq (f g : ℕ → mv_polynomial ℕ ℤ)
  (h : ∀ n, bind₁ f (witt_polynomial p _ n) = bind₁ g (witt_polynomial p _ n)) :
  f = g :=
begin
  ext1 n,
  apply mv_polynomial.map_injective (int.cast_ring_hom ℚ) int.cast_injective,
  rw ← function.funext_iff at h,
  replace h := congr_arg
    (λ fam, bind₁ (mv_polynomial.map (int.cast_ring_hom ℚ) ∘ fam)
    (X_in_terms_of_W p ℚ n)) h,
  simpa only [function.comp, map_bind₁, map_witt_polynomial,
    ← bind₁_bind₁, X_in_terms_of_W_prop, bind₁_X_right] using h
end

-- Ideally, we would generalise this to n-ary functions
-- But we don't have a good theory of n-ary compositions in mathlib
omit hp

structure is_poly (f : Π ⦃R : Type*⦄ [comm_ring R], witt_vector p R → 𝕎 R) :=
(poly : ℕ → mv_polynomial ℕ ℤ)
(coeff : ∀ (n : ℕ) ⦃R : Type*⦄ [comm_ring R] (x : 𝕎 R),
  (f x).coeff n = aeval (λ k, x.coeff k) (poly n))

lemma id_is_poly : is_poly p (λ _ _, id) :=
{ poly := X,
  coeff := by { introsI, rw [aeval_X, id] } }

variables {p}

@[simps { fully_applied := ff }]
def is_poly.comp {g f} (hg : is_poly p g) (hf : is_poly p f) :
  is_poly p (λ R _Rcr, @g R _Rcr ∘ @f R _Rcr) :=
{ poly := λ n, bind₁ (hf.poly) (hg.poly n),
  coeff := by intros; simp only [aeval_bind₁, function.comp, hg.coeff, hf.coeff] }

lemma is_poly.ext {f g} (hf : is_poly p f) (hg : is_poly p g)
  (h : hf.poly = hg.poly) :
  f = g :=
by { ext R _Rcr x n, rw [hf.coeff, hg.coeff, h] }

include hp

lemma is_poly.ext' {f g} (hf : is_poly p f) (hg : is_poly p g)
  (h : ∀ n, bind₁ hf.poly (witt_polynomial p _ n) = bind₁ hg.poly (witt_polynomial p _ n)) :
  f = g :=
is_poly.ext hf hg $ poly_eq_of_witt_polynomial_bind_eq p _ _ h

end ghost_equation

end witt_vector

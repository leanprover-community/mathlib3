-- this should all be moved

import algebra.inj_surj
import data.nat.choose
import data.int.gcd
import data.mv_polynomial
import data.zmod.basic
import data.fintype.card
import ring_theory.multiplicity
import algebra.invertible
import number_theory.basic

universes u v w u₁

-- ### FOR_MATHLIB
-- everything in this file should move to other files

namespace ring_hom

lemma ext_nat {R : Type*} [semiring R] (f g : ℕ →+* R) : f = g :=
begin
  ext n,
  calc f n = nat.cast_ring_hom R n : ring_hom.eq_nat_cast f n
       ... = g n                   : (ring_hom.eq_nat_cast g n).symm,
end

lemma ext_int {R : Type*} [semiring R] (f g : ℤ →+* R) : f = g :=
begin
  ext n,
  let φ : ℕ →+* R := f.comp (nat.cast_ring_hom ℤ),
  let ψ : ℕ →+* R := g.comp (nat.cast_ring_hom ℤ),
  have h : ∀ n : ℕ, f n = g n, by { intro n, simp [← int.nat_cast_eq_coe_nat] },
  cases n, { apply h },
  calc  f (-(n+1))
      = f (-(n+1)) + (g (n+1) + g (-(n+1))) : by rw [← g.map_add, add_neg_self, g.map_zero, add_zero]
  ... = f (-(n+1)) + f (n+1) + g (-(n+1))   : by simp only [add_assoc, h, map_add, map_one]
  ... = g (-(n+1))                          : by rw [← f.map_add, neg_add_self, f.map_zero, zero_add]
end

lemma ext_zmod {n : ℕ} {R : Type*} [semiring R] (f g : (zmod n) →+* R) : f = g :=
begin
  ext a,
  obtain ⟨k, rfl⟩ := zmod.int_cast_surjective a,
  let φ : ℤ →+* R := f.comp (int.cast_ring_hom (zmod n)),
  let ψ : ℤ →+* R := g.comp (int.cast_ring_hom (zmod n)),
  show φ k = ψ k,
  rw φ.ext_int ψ,
end

lemma ext_rat {R : Type*} [semiring R]
  (f g : ℚ →+* R) : f = g :=
begin
  ext r,
  refine rat.num_denom_cases_on' r _,
  intros a b b0,
  let φ : ℤ →+* R := f.comp (int.cast_ring_hom ℚ),
  let ψ : ℤ →+* R := g.comp (int.cast_ring_hom ℚ),
  rw [rat.mk_eq_div, int.cast_coe_nat],
  have b0' : (b:ℚ) ≠ 0 := nat.cast_ne_zero.2 b0,
  have : ∀ n : ℤ, f n = g n := λ n, show φ n = ψ n, by rw [φ.ext_int ψ],
  calc f (a * b⁻¹)
      = f a * f b⁻¹ * (g (b:ℤ) * g b⁻¹) :
        by rw [int.cast_coe_nat, ← g.map_mul, mul_inv_cancel b0', g.map_one, mul_one, f.map_mul]
  ... = g a * f b⁻¹ * (f (b:ℤ) * g b⁻¹) : by rw [this a, ← this b]
  ... = g (a * b⁻¹) :
        by rw [int.cast_coe_nat, mul_assoc, ← mul_assoc (f b⁻¹),
              ← f.map_mul, inv_mul_cancel b0', f.map_one, one_mul, g.map_mul]
end

end ring_hom

namespace mv_polynomial

variables {σ : Type*} {R : Type*} [comm_semiring R]

noncomputable def C_ (σ : Type*) {R : Type*} [comm_semiring R] : R →+* mv_polynomial σ R :=
ring_hom.of C

example (x y : R) : C_ σ (x * y) = C_ σ x * C_ σ y := C_mul

lemma ring_hom_ext {σ : Type*} {R : Type*} {A : Type*} [comm_ring R] [comm_ring A]
  (f g : mv_polynomial σ R →+* A)
  (hC : ∀ r, f (C r) = g (C r)) (hX : ∀ i, f (X i) = g (X i)) :
  f = g :=
begin
  ext p : 1,
  apply mv_polynomial.induction_on' p,
  { intros m r, rw [monomial_eq, finsupp.prod],
    simp only [monomial_eq, ring_hom.map_mul, ring_hom.map_prod, ring_hom.map_pow, hC, hX], },
  { intros p q hp hq, simp only [ring_hom.map_add, hp, hq] }
end

lemma alg_hom_ext {σ : Type*} (R : Type*) [comm_ring R]
  (A : Type*) [comm_ring A] [algebra R A]
  (f g : mv_polynomial σ R →ₐ[R] A)
  (hf : ∀ i : σ, f (X i) = g (X i)) : f = g :=
begin
  apply alg_hom.coe_ring_hom_inj,
  apply ring_hom_ext,
  { intro r,
    calc f (C r) = algebra_map R A r : f.commutes r
             ... = g (C r)           : (g.commutes r).symm },
  { simpa only [hf] },
end

lemma C_injective (σ : Type*) (R : Type*) [comm_ring R] :
  function.injective (C : R → mv_polynomial σ R) :=
finsupp.injective_single _

@[simp] lemma C_inj {σ : Type*} (R : Type*) [comm_ring R] (r s : R) :
  (C r : mv_polynomial σ R) = C s ↔ r = s :=
(C_injective σ R).eq_iff

end mv_polynomial

namespace mv_polynomial

section char_p
variables (σ : Type*) (R : Type*) [comm_ring R] (p : ℕ)

instance [char_p R p] : char_p (mv_polynomial σ R) p :=
{ cast_eq_zero_iff := λ n,
  by rw [← C_eq_coe_nat, ← C_0, C_inj, char_p.cast_eq_zero_iff R p] }

end char_p

end mv_polynomial

namespace alg_hom
open mv_polynomial

lemma comp_aeval {σ : Type*}
  {R : Type*} {A : Type*} {B : Type*}
   [comm_ring R] [comm_ring A] [algebra R A] [comm_ring B] [algebra R B]
  (f : σ → A) (φ : A →ₐ[R] B) :
  φ.comp (aeval R A f) = (aeval R B (λ i, φ (f i))) :=
begin
  apply mv_polynomial.alg_hom_ext,
  intros i,
  rw [comp_apply, aeval_X, aeval_X],
end

end alg_hom

namespace mv_polynomial

open mv_polynomial finsupp

lemma eval₂_assoc'
  {S : Type*} [comm_semiring S]
  {T : Type*} [comm_semiring T]
  {σ : Type*}
  {τ : Type*}
  (f : S → T) [is_semiring_hom f]
  (φ : σ → T) (q : τ → mv_polynomial σ S)
  (p : mv_polynomial τ S) :
  eval₂ f (λ t, eval₂ f φ (q t)) p = eval₂ f φ (eval₂ C q p) :=
by { rw eval₂_comp_left (eval₂ f φ), congr, funext, simp }

noncomputable def rename_hom {σ : Type*} {τ : Type*} {R : Type*} [comm_semiring R] (f : σ → τ) :
  mv_polynomial σ R →+* mv_polynomial τ R :=
ring_hom.of (rename f)

section
variables {σ : Type*} {τ : Type*} {R : Type*} [comm_semiring R] (f : σ → τ)

@[simp] lemma rename_hom_X (i : σ) :
  rename_hom f (X i : mv_polynomial σ R) = X (f i) :=
rename_X _ _

end

noncomputable def map_hom
  {S : Type*} [comm_semiring S]
  {T : Type*} [comm_semiring T]
  {σ : Type*}
  (f : S →+* T) :
  mv_polynomial σ S →+* mv_polynomial σ T :=
ring_hom.of (mv_polynomial.map f)

section
variables {σ : Type*} {R : Type*} {S : Type*} {T : Type*}
variables [comm_semiring R] [comm_semiring S] [comm_semiring T] (f : R →+* S)

@[simp] lemma map_hom_C (r : R) : map_hom f (C r : mv_polynomial σ R) = C (f r) :=
map_C f r

@[simp] lemma map_hom_X (i : σ) : map_hom f (X i : mv_polynomial σ R) = X i :=
map_X f i

@[simp] lemma map_hom_rename_hom {τ : Type*} (g : σ → τ) (p : mv_polynomial σ R) :
  map_hom f (rename_hom g p) = rename_hom g (map_hom f p) :=
map_rename f g p

@[simp] lemma eval₂_hom_rename_hom {τ : Type*} (g : τ → S) (h : σ → τ) (p : mv_polynomial σ R) :
  eval₂_hom f g (rename_hom h p) = eval₂_hom f (g ∘ h) p :=
eval₂_rename f h g p -- Achtung die Reihenfolge!

end

lemma eval₂_hom_congr {σ : Type*} {R : Type*} {S : Type*} [comm_semiring R] [comm_semiring S]
  {f₁ f₂ : R →+* S} {g₁ g₂ : σ → S} {p₁ p₂ : mv_polynomial σ R} :
  f₁ = f₂ → g₁ = g₂ → p₁ = p₂ →  eval₂_hom f₁ g₁ p₁ = eval₂_hom f₂ g₂ p₂ :=
by rintros rfl rfl rfl; refl

lemma map_eval₂'
  {R : Type*} [comm_semiring R]
  {S : Type*} [comm_semiring S]
  {T : Type*} [comm_semiring T]
  {σ : Type*}
  (φ : S →+* T)
  (f : R →+* S)
  (g : σ → S)
  (p : mv_polynomial σ R) :
  φ (eval₂ f g p) = eval₂ (φ.comp f) (λ i, φ (g i)) p :=
begin
  apply p.induction_on,
  { intros, rw [eval₂_C, eval₂_C, ring_hom.coe_comp] },
  { intros p₁ p₂ hp₁ hp₂, rw [eval₂_add, eval₂_add, ring_hom.map_add, hp₁, hp₂] },
  { intros q n h, rw [eval₂_mul, eval₂_mul, ring_hom.map_mul, eval₂_X, eval₂_X, h] }
end

lemma aeval_eq_eval₂_hom {σ : Type*} {R : Type*} {A : Type*}
   [comm_ring R] [comm_ring A] [algebra R A] (f : σ → A) :
  (aeval R A f : mv_polynomial σ R →+* A) = eval₂_hom (algebra_map R A) f :=
rfl

lemma aeval_eq_eval₂_hom' {σ : Type*} {R : Type*} {A : Type*}
   [comm_ring R] [comm_ring A] [algebra R A] (f : σ → A) (p : mv_polynomial σ R) :
  aeval R A f p = eval₂_hom (algebra_map R A) f p :=
rfl

@[simp] lemma eval₂_hom_C {σ : Type*} {R : Type*} {A : Type*} [comm_ring R] [comm_ring A]
  (f : R →+* A) (g : σ → A) (r : R) :
  eval₂_hom f g (C r) = f r := eval₂_C f g r

@[simp] lemma eval₂_hom_X' {σ : Type*} {R : Type*} {A : Type*} [comm_ring R] [comm_ring A]
  (f : R →+* A) (g : σ → A) (i : σ) :
  eval₂_hom f g (X i) = g i := eval₂_X f g i

@[simp] lemma comp_eval₂_hom {σ : Type*} {R : Type*} {A : Type*} {B : Type*}
  [comm_ring R] [comm_ring A] [comm_ring B]
  (f : R →+* A) (g : σ → A) (φ : A →+* B) :
  φ.comp (eval₂_hom f g) = (eval₂_hom (φ.comp f) (λ i, φ (g i))) :=
begin
  apply mv_polynomial.ring_hom_ext,
  { intro r, rw [ring_hom.comp_apply, eval₂_hom_C, eval₂_hom_C, ring_hom.comp_apply] },
  { intro i, rw [ring_hom.comp_apply, eval₂_hom_X', eval₂_hom_X'] }
end

@[simp] lemma map_eval₂_hom {σ : Type*} {R : Type*} {A : Type*} {B : Type*}
  [comm_ring R] [comm_ring A] [comm_ring B]
  (f : R →+* A) (g : σ → A) (φ : A →+* B) (p : mv_polynomial σ R) :
  φ (eval₂_hom f g p) = (eval₂_hom (φ.comp f) (λ i, φ (g i)) p) :=
by { rw ← comp_eval₂_hom, refl }

@[simp] lemma map_aeval {σ : Type*} {R : Type*} {A : Type*} {B : Type*}
  [comm_ring R] [comm_ring A] [algebra R A] [comm_ring B]
  (g : σ → A) (φ : A →+* B) (p : mv_polynomial σ R) :
  φ (aeval R A g p) = (eval₂_hom (φ.comp (algebra_map R A)) (λ i, φ (g i)) p) :=
by { rw ← comp_eval₂_hom, refl }

@[simp] lemma eval_map {σ : Type*} {R : Type*} {A : Type*} [comm_ring R] [comm_ring A]
  (f : R →+* A) (g : σ → A) (p : mv_polynomial σ R) :
  eval g (map f p) = eval₂ f g p :=
by { apply mv_polynomial.induction_on p; { simp { contextual := tt } } }

@[simp] lemma eval₂_map {σ : Type*} {R : Type*} {A : Type*} {B : Type*}
  [comm_ring R] [comm_ring A] [comm_ring B]
  (f : R →+* A) (g : σ → B) (φ : A →+* B) (p : mv_polynomial σ R) :
  eval₂ φ g (map f p) = eval₂ (φ.comp f) g p :=
by { rw [← eval_map, ← eval_map, map_map], refl }

@[simp] lemma eval₂_hom_map_hom {σ : Type*} {R : Type*} {A : Type*} {B : Type*}
  [comm_ring R] [comm_ring A] [comm_ring B]
  (f : R →+* A) (g : σ → B) (φ : A →+* B) (p : mv_polynomial σ R) :
  eval₂_hom φ g (map_hom f p) = eval₂_hom (φ.comp f) g p :=
eval₂_map f g φ p

open_locale big_operators

lemma C_dvd_iff_dvd_coeff {σ : Type*} {R : Type*} [comm_ring R]
  (r : R) (φ : mv_polynomial σ R) :
  C r ∣ φ ↔ ∀ i, r ∣ (φ.coeff i) :=
begin
  split,
  { rintros ⟨φ, rfl⟩ c, rw coeff_C_mul, apply dvd_mul_right },
  { intro h,
    choose c hc using h,
    classical,
    let c' : (σ →₀ ℕ) → R := λ i, if i ∈ φ.support then c i else 0,
    let ψ : mv_polynomial σ R := ∑ i in φ.support, monomial i (c' i),
    use ψ,
    apply mv_polynomial.ext, intro i,
    simp only [coeff_C_mul, coeff_sum, coeff_monomial],
    rw [finset.sum_eq_single i, if_pos rfl],
    { dsimp [c'], split_ifs with hi hi,
      { rw hc },
      { rw finsupp.not_mem_support_iff at hi, rwa [mul_zero] } },
    { intros j hj hji, convert if_neg hji },
    { intro hi, rw [if_pos rfl], exact if_neg hi } }
end

-- why the hack does ring_hom.ker not exist!!!

lemma C_dvd_iff_map_hom_eq_zero {σ : Type*} {R : Type*} {S : Type*} [comm_ring R] [comm_ring S]
  (q : R →+* S) (hq : function.surjective q) (r : R) (hr : ∀ r' : R, q r' = 0 ↔ r ∣ r')
  (φ : mv_polynomial σ R) :
  C r ∣ φ ↔ map_hom q φ = 0 :=
begin
  rw C_dvd_iff_dvd_coeff,
  split,
  { intro h, apply mv_polynomial.ext, intro i,
    simp only [map_hom, coeff_map, *, ring_hom.coe_of, coeff_zero], },
  { rw mv_polynomial.ext_iff,
    simp only [map_hom, coeff_map, *, ring_hom.coe_of, coeff_zero, imp_self] }
end

lemma C_dvd_iff_zmod {σ : Type*} (n : ℕ) (φ : mv_polynomial σ ℤ) :
  C (n:ℤ) ∣ φ ↔ map_hom (int.cast_ring_hom (zmod n)) φ = 0 :=
begin
  apply C_dvd_iff_map_hom_eq_zero,
  { exact zmod.int_cast_surjective },
  { exact char_p.int_cast_eq_zero_iff (zmod n) n, }
end

end mv_polynomial

section
open multiplicity

lemma coe_nat_dvd {R : Type*} [comm_semiring R] (m n : ℕ) (h : m ∣ n) :
  (m : R) ∣ n :=
ring_hom.map_dvd (nat.cast_ring_hom R) h

lemma coe_int_dvd {R : Type*} [comm_ring R] (m n : ℤ) (h : m ∣ n) :
  (m : R) ∣ n :=
ring_hom.map_dvd (int.cast_ring_hom R) h

-- by { rcases h with ⟨k, rfl⟩, refine ⟨k, by norm_cast⟩ }

lemma rat.denom_div_cast_eq_one_iff (m n : ℤ) (hn : n ≠ 0) :
  ((m : ℚ) / n).denom = 1 ↔ n ∣ m :=
begin
  replace hn : (n:ℚ) ≠ 0, by rwa [ne.def, int.cast_eq_zero],
  split,
  { intro h,
    lift ((m : ℚ) / n) to ℤ using h with k hk,
    use k,
    rwa [eq_div_iff_mul_eq _ _ hn, ← int.cast_mul, mul_comm, eq_comm, int.cast_inj] at hk },
  { rintros ⟨d, rfl⟩,
    rw [int.cast_mul, mul_comm, mul_div_cancel _ hn, rat.coe_int_denom] }
end

end

-- move this (and generalize to char_zero fields)
instance rat.invertible_of_prime (n : ℕ) [h : fact (0 < n)] : invertible (n : ℚ) :=
{ inv_of := 1/n,
  inv_of_mul_self := one_div_mul_cancel $ by { rw nat.pos_iff_ne_zero at h, exact_mod_cast h },
  mul_inv_of_self := mul_one_div_cancel $ by { rw nat.pos_iff_ne_zero at h, exact_mod_cast h } }

namespace invertible
variables {R : Type*} {S : Type*} [monoid R] [monoid S]

def map (f : R →* S) (r : R) [invertible r] : invertible (f r) :=
{ inv_of := f (⅟r),
  inv_of_mul_self := by rw [← f.map_mul, inv_of_mul_self, f.map_one],
  mul_inv_of_self := by rw [← f.map_mul, mul_inv_of_self, f.map_one] }

def copy {r : R} (hr : invertible r) (s : R) (hs : s = r) : invertible s :=
{ inv_of := ⅟r,
  inv_of_mul_self := by rw [hs, inv_of_mul_self],
  mul_inv_of_self := by rw [hs, mul_inv_of_self] }

end invertible

namespace mv_polynomial
noncomputable instance invertible_C
  (σ : Type*) {R : Type*} [comm_semiring R] (r : R) [invertible r] :
  invertible (C r : mv_polynomial σ R) :=
invertible.map ⟨C, C_1, λ x y, C_mul⟩ _

-- name??
noncomputable def invertible_rat_coe_nat (σ : Type*) (p : ℕ) [invertible (p : ℚ)] :
  invertible (p : mv_polynomial σ ℚ) :=
(mv_polynomial.invertible_C σ (p:ℚ)).copy p $ (C_eq_coe_nat p).symm

end mv_polynomial

-- ### end FOR_MATHLIB

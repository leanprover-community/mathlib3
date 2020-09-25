/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import data.polynomial.degree.basic
import data.polynomial.algebra_map
import ring_theory.polynomial.basic
import ring_theory.localization
import data.zmod.basic
import analysis.special_functions.trigonometric
import data.real.cardinality

/-!
# Chebyshev polynomials
-/

-- move this
lemma set.infinite_of_subset {α : Type*} (s t : set α) (h : s ⊆ t) (hs : s.infinite) : t.infinite :=
mt (λ ht, set.finite.subset ht h) hs

lemma char_p.char_field_eq_char_field {K L : Type*} [field K] [field L] (f : K →+* L) (p : ℕ) :
  char_p K p ↔ char_p L p :=
begin
  split;
  { introI _c, constructor, intro n,
    rw [← @char_p.cast_eq_zero_iff _ _ p _c n, ← f.injective.eq_iff, f.map_nat_cast, f.map_zero] }
end

noncomputable theory

namespace polynomial

variables (R S : Type*) [ring R] [ring S]

/-- The Chebyshev polynomials of the first kind. -/
noncomputable def chebyshev₁ : ℕ → polynomial R
| 0       := 1
| 1       := X
| (n + 2) := 2 * X * chebyshev₁ (n + 1) - chebyshev₁ n

@[simp] lemma chebyshev₁_zero : chebyshev₁ R 0 = 1 := rfl
@[simp] lemma chebyshev₁_one : chebyshev₁ R 1 = X := rfl
@[simp] lemma chebyshev₁_two : chebyshev₁ R 2 = 2 * X ^ 2 - 1 :=
by simp only [chebyshev₁, sub_left_inj, pow_two, mul_assoc]
@[simp] lemma chebyshev₁_add_two (n : ℕ) :
  chebyshev₁ R (n + 2) = 2 * X * chebyshev₁ R (n + 1) - chebyshev₁ R n :=
by rw chebyshev₁

lemma chebyshev₁_two_le (n : ℕ) (h : 2 ≤ n) :
  chebyshev₁ R n = 2 * X * chebyshev₁ R (n - 1) - chebyshev₁ R (n - 2) :=
begin
  obtain ⟨n, rfl⟩ := nat.exists_eq_add_of_le h,
  rw add_comm,
  exact chebyshev₁_add_two R n
end

section
variables {R}

-- this shouldn't need `comm_ring S` !
lemma map_chebyshev₁ {S : Type*} [comm_ring S] (f : R →+* S) :
  ∀ (n : ℕ), map f (chebyshev₁ R n) = chebyshev₁ S n
| 0       := by simp only [chebyshev₁_zero, map_one]
| 1       := by simp only [chebyshev₁_one, map_X]
| (n + 2) :=
begin
  simp only [chebyshev₁_add_two, map_mul, map_sub, map_X, bit0, map_add, map_one],
  rw [map_chebyshev₁ (n + 1), map_chebyshev₁ n],
end

end

-- move this
instance char_zero.nontrivial [char_zero R] : nontrivial R :=
char_p.nontrivial_of_char_ne_one zero_ne_one

section complex
open complex

@[simp] lemma chebyshev₁_complex_cos (θ : ℂ) :
  ∀ n, (chebyshev₁ ℂ n).eval (cos θ) = cos (n * θ)
| 0       := by simp only [chebyshev₁_zero, eval_one, nat.cast_zero, zero_mul, cos_zero]
| 1       := by simp only [eval_X, one_mul, chebyshev₁_one, nat.cast_one]
| (n + 2) :=
begin
  simp only [eval_X, eval_one, chebyshev₁_add_two, eval_sub, eval_bit0, nat.cast_succ, eval_mul],
  rw [chebyshev₁_complex_cos (n + 1), chebyshev₁_complex_cos n],
  have aux : sin θ * sin θ = 1 - cos θ * cos θ,
  { rw ← sin_sq_add_cos_sq θ, ring, },
  simp only [nat.cast_add, nat.cast_one, add_mul, cos_add, one_mul, sin_add, mul_assoc, aux],
  ring,
end


end complex

-- move this
lemma eq_zero_of_infinite_is_root {R : Type*} [integral_domain R]
  (p : polynomial R) (h : set.infinite {x | is_root p x}) : p = 0 :=
begin
  classical,
  by_contradiction hp,
  apply h,
  convert p.roots.to_finset.finite_to_set using 1,
  ext1 r,
  simp only [mem_roots hp, multiset.mem_to_finset, set.mem_set_of_eq, finset.mem_coe]
end

-- move this
lemma eq_of_infinite_eval_eq {R : Type*} [integral_domain R]
  (p q : polynomial R) (h : set.infinite {x | eval x p = eval x q}) : p = q :=
begin
  rw [← sub_eq_zero],
  apply eq_zero_of_infinite_is_root,
  simpa only [is_root, eval_sub, sub_eq_zero]
end

-- move this
instance complex.infinite : infinite ℂ :=
infinite.of_injective coe nat.cast_injective

-- move this
instance real.infinite : infinite ℝ :=
infinite.of_injective coe nat.cast_injective

-- move this
lemma complex.range_cos_infinite : (set.range complex.cos).infinite :=
begin
  have : (set.range real.cos).infinite,
  { rw [real.range_cos, ← set.infinite_coe_iff, cardinal.infinite_iff,
        cardinal.mk_Icc_real (show (-1 : ℝ) < 1, by norm_num),
        ← cardinal.mk_real, ← cardinal.infinite_iff],
    apply_instance },
  rw ← set.infinite_coe_iff at this ⊢,
  delta real.cos at this,
  apply @infinite.of_injective _ _ this,
  swap,
  { rintro ⟨x, hx⟩,
    refine ⟨x, _⟩,
    rcases hx with ⟨θ, rfl⟩,
    simp only [complex.of_real_cos_of_real_re, set.mem_range_self] },
  { rintro ⟨x, hx⟩ ⟨y, hy⟩ h,
    simpa only [complex.of_real_inj, subtype.mk_eq_mk] using h }
end

-- this shouldn't need `[comm_ring R]` !
lemma chebyshev₁_mul (R : Type*) [comm_ring R] (m n : ℕ) :
  chebyshev₁ R (m * n) = (chebyshev₁ R m).comp (chebyshev₁ R n) :=
begin
  simp only [← map_comp, ← map_chebyshev₁ (int.cast_ring_hom R)],
  congr' 1,
  apply map_injective (int.cast_ring_hom ℂ) int.cast_injective,
  simp only [map_comp, map_chebyshev₁],
  apply eq_of_infinite_eval_eq,
  apply set.infinite_of_subset _ _ _ complex.range_cos_infinite,
  rintro _ ⟨θ, rfl⟩,
  simp only [chebyshev₁_complex_cos, nat.cast_mul, set.mem_set_of_eq, eval_comp, mul_assoc]
end

section lambdashev
/-!

### A Lambda structure on `polynomial ℤ`

-/

/-- `lambdashev R n` is equal to `2 * (chebyshev₁ R n).comp (X / 2)`.
It is a family of polynomials that satisfies
`lambdashev (zmod p) p = X ^ p`, and therefore defines a Lambda structure on `polynomial ℤ`. -/
noncomputable def lambdashev : ℕ → polynomial R
| 0       := 2
| 1       := X
| (n + 2) := X * lambdashev (n + 1) - lambdashev n

@[simp] lemma lambdashev_zero : lambdashev R 0 = 2 := rfl
@[simp] lemma lambdashev_one : lambdashev R 1 = X := rfl
@[simp] lemma lambdashev_two : lambdashev R 2 = X ^ 2 - 2 :=
by simp only [lambdashev, sub_left_inj, pow_two, mul_assoc]
@[simp] lemma lambdashev_add_two (n : ℕ) :
  lambdashev R (n + 2) = X * lambdashev R (n + 1) - lambdashev R n :=
by rw lambdashev

lemma lambdashev_two_le (n : ℕ) (h : 2 ≤ n) :
  lambdashev R n = X * lambdashev R (n - 1) - lambdashev R (n - 2) :=
begin
  obtain ⟨n, rfl⟩ := nat.exists_eq_add_of_le h,
  rw add_comm,
  exact lambdashev_add_two R n
end

section
variables {R}

-- this shouldn't need `comm_ring S` !
lemma map_lambdashev {S : Type*} [comm_ring S] (f : R →+* S) :
  ∀ (n : ℕ), map f (lambdashev R n) = lambdashev S n
| 0       := by simp only [lambdashev_zero, bit0, map_add, map_one]
| 1       := by simp only [lambdashev_one, map_X]
| (n + 2) :=
begin
  simp only [lambdashev_add_two, map_mul, map_sub, map_X, bit0, map_add, map_one],
  rw [map_lambdashev (n + 1), map_lambdashev n],
end

end

lemma lambdashev_eval_add_inv {R : Type*} [comm_ring R] (x y : R) (h : x * y = 1) :
  ∀ n, (lambdashev R n).eval (x + y) = x ^ n + y ^ n
| 0       := by simp only [bit0, eval_one, eval_add, pow_zero, lambdashev_zero]
| 1       := by simp only [eval_X, lambdashev_one, pow_one]
| (n + 2) :=
begin
  simp only [eval_sub, eval_mul, lambdashev_eval_add_inv, eval_X, lambdashev_add_two],
  conv_lhs { simp only [pow_succ, add_mul, mul_add, h, ← mul_assoc, mul_comm y x, one_mul] },
  ring_exp
end

-- move this
lemma comp_assoc {R : Type*} [comm_semiring R] (φ ψ χ : polynomial R) :
  (φ.comp ψ).comp χ = φ.comp (ψ.comp χ) :=
begin
  apply polynomial.induction_on φ;
  { intros, simp only [add_comp, mul_comp, C_comp, X_comp, pow_succ', ← mul_assoc, *] at * }
end

-- move this
lemma eval₂_congr {R S : Type*} [semiring R] [semiring S]
  {f g : R →+* S} {s t : S} {φ ψ : polynomial R} :
  f = g → s = t → φ = ψ → eval₂ f s φ = eval₂ g t ψ :=
by rintro rfl rfl rfl; refl

-- generalize to `[invertible (2 : R)]`
lemma lambdashev_eq_chebyshev₁ :
  ∀ n, lambdashev ℚ n = 2 * (chebyshev₁ ℚ n).comp (C (1/2) * X)
| 0       := by simp only [chebyshev₁_zero, mul_one, one_comp, lambdashev_zero]
| 1       :=
begin
  simp only [one_div, X_comp, lambdashev_one, chebyshev₁_one, ← C_bit0, ← C_1, ← C_mul, ← mul_assoc],
  rw [mul_inv_cancel, C_1, one_mul],
  norm_num
end
| (n + 2) :=
begin
  simp only [lambdashev_add_two, chebyshev₁_add_two],
  rw [lambdashev_eq_chebyshev₁ (n + 1), lambdashev_eq_chebyshev₁ n],
  simp only [comp, eval₂_sub, mul_sub],
  simp only [eval₂_one, eval₂_bit0, sub_left_inj, eval₂_mul, eval₂_X],
  simp only [← mul_assoc],
  suffices : (2 * 2 * C (1/2) : polynomial ℚ) = 2,
  { rw [this, mul_comm X] },
  simp only [← C_bit0, ← C_1, ← C_mul, C_inj],
  norm_num
end

-- generalize to `[invertible (2 : R)]`
lemma chebyshev₁_eq_lambdashev (n : ℕ) :
  chebyshev₁ ℚ n = C (1/2) * (lambdashev ℚ n).comp (2 * X) :=
begin
  rw lambdashev_eq_chebyshev₁,
  simp only [comp_assoc, mul_comp, C_comp, X_comp, ← mul_assoc, ← C_1, ← C_bit0, ← C_mul],
  rw [div_mul_cancel, C_1, one_mul, one_mul, comp_X],
  norm_num
end

lemma lambdashev_mul (R : Type*) [comm_ring R] (m n : ℕ) :
  lambdashev R (m * n) = (lambdashev R m).comp (lambdashev R n) :=
begin
  simp only [← map_lambdashev (int.cast_ring_hom R), ← map_comp],
  congr' 1,
  apply map_injective (int.cast_ring_hom ℚ) int.cast_injective,
  simp only [map_lambdashev, map_comp, lambdashev_eq_chebyshev₁, chebyshev₁_mul],
  simp only [two_mul, ← add_comp],
  simp only [← two_mul, ← comp_assoc],
  apply eval₂_congr rfl rfl,
  rw [comp_assoc],
  apply eval₂_congr rfl _ rfl,
  rw [mul_comp, C_comp, X_comp, ← mul_assoc, ← C_1, ← C_bit0, ← C_mul, div_mul_cancel, C_1, one_mul],
  norm_num
end

-- move this
instance [nontrivial R] : infinite (polynomial R) :=
infinite.of_injective (λ i, monomial i 1)
begin
  intros m n h,
  have := (finsupp.single_eq_single_iff _ _ _ _).mp h,
  simpa only [and_true, eq_self_iff_true, or_false, one_ne_zero, and_self],
end

lemma lambdashev_zmod_p (p : ℕ) [fact p.prime] :
  lambdashev (zmod p) p = X ^ p :=
begin
  suffices : ∃ (K : Type) [field K], by exactI ∃ [char_p K p], infinite K,
  { obtain ⟨K, _, _, H⟩ := this,
    resetI,
    apply map_injective (zmod.cast_hom (dvd_refl p) K) (ring_hom.injective _),
    rw [map_lambdashev, map_pow, map_X],
    apply eq_of_infinite_eval_eq,
    apply set.infinite_of_subset {x : K | ∃ y, x = y + y⁻¹ ∧ y ≠ 0},
    { rintro _ ⟨x, rfl, hx⟩,
      -- TODO: make `p` explicit in `add_pow_char`
      simp only [eval_X, eval_pow, set.mem_set_of_eq, @add_pow_char K _ p,
        lambdashev_eval_add_inv _ _ (mul_inv_cancel hx)] },
    { intro h,
      rw ← set.infinite_univ_iff at H,
      apply H,
      suffices : (set.univ : set K) =
        {x : K | ∃ (y : K), x = y + y⁻¹ ∧ y ≠ 0} >>= (λ x, {y | x = y + y⁻¹ ∨ y = 0}),
      { rw this, clear this,
        apply set.finite_bind h,
        rintro x hx,
        let φ : polynomial K := X ^ 2 - C x * X + 1,
        have hφ : φ ≠ 0,
        { intro H,
          have : φ.eval 0 = 0, by rw [H, eval_zero],
          simpa [eval_X, eval_one, eval_pow, eval_sub, sub_zero, eval_add,
            eval_mul, mul_zero, pow_two, zero_add, one_ne_zero] },
        classical,
        convert (φ.roots ∪ {0}).to_finset.finite_to_set using 1,
        ext1 y,
        simp only [multiset.mem_to_finset, set.mem_set_of_eq, finset.mem_coe, multiset.mem_union,
          mem_roots hφ, is_root, eval_add, eval_sub, eval_pow, eval_mul, eval_X, eval_C, eval_one,
          multiset.mem_singleton, multiset.singleton_eq_singleton],
        by_cases hy : y = 0,
        { simp only [hy, eq_self_iff_true, or_true] },
        apply or_congr _ iff.rfl,
        rw [← mul_left_inj' hy, eq_comm, ← sub_eq_zero, add_mul, inv_mul_cancel hy],
        apply eq_iff_eq_cancel_right.mpr,
        ring },
    { apply (set.eq_univ_of_forall _).symm,
      intro x,
      simp only [exists_prop, set.mem_Union, set.bind_def, ne.def, set.mem_set_of_eq],
      by_cases hx : x = 0,
      { simp only [hx, and_true, eq_self_iff_true, inv_zero, or_true],
        exact ⟨_, 1, rfl, one_ne_zero⟩ },
      { simp only [hx, or_false, exists_eq_right],
        exact ⟨_, rfl, hx⟩ } } } },
  { let K := fraction_ring (polynomial (zmod p)),
    let f : zmod p →+* K := (fraction_ring.of _).to_map.comp C,
    refine ⟨K, infer_instance, _, _⟩,
    { rw ← char_p.char_field_eq_char_field f, apply_instance },
    { apply infinite.of_injective _ (fraction_ring.of _).injective, apply_instance } }
end

lemma lambdashev_char_p (p : ℕ) (R : Type*) [fact p.prime] [comm_ring R] [char_p R p] :
  lambdashev R p = X ^ p :=
by rw [← map_lambdashev (zmod.cast_hom (dvd_refl p) R), lambdashev_zmod_p, map_pow, map_X]

end lambdashev

end polynomial

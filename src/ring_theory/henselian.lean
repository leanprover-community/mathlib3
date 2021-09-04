/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import data.finset.nat_antidiagonal
import ring_theory.polynomial.content
import ring_theory.ideal.local_ring
import linear_algebra.adic_completion
import number_theory.padics.padic_integers
import tactic.field_simp

/-!
# Henselian local rings


## References

https://stacks.math.columbia.edu/tag/04GE
-/

noncomputable theory

universe variables u v

open_locale big_operators

open local_ring (maximal_ideal residue_field residue)
open polynomial (X C aeval)
open function

class henselian (R : Type*) [comm_ring R] extends local_ring R : Prop :=
(is_henselian : ∀ (f : polynomial R) (hf : f.monic) (a₀ : R) (h₁ : f.eval a₀ ∈ maximal_ideal R)
  (h₂ : is_unit (f.derivative.eval a₀)),
  ∃ a : R, f.is_root a ∧ (a - a₀ ∈ maximal_ideal R))

instance field.henselian (K : Type*) [field K] : henselian K :=
{ is_henselian := λ f hf a₀ h₁ h₂,
  begin
    refine ⟨a₀, _, _⟩;
    rwa [(maximal_ideal K).eq_bot_of_prime, ideal.mem_bot] at *,
    rw sub_self,
  end }

-- move this
instance local_ring.residue_field.algebra (R : Type*) [comm_ring R] [local_ring R] :
  algebra R (residue_field R) := (residue R).to_algebra

-- move this
/-- The kernel of a homomorphism to a field is a maximal ideal. -/
lemma ring_hom.ker_is_maximal_of_surjective {R K : Type*} [ring R] [field K]
  (f : R →+* K) (hf : surjective f) :
  f.ker.is_maximal :=
begin
  refine ideal.is_maximal_iff.mpr
    ⟨λ h1, @one_ne_zero K _ _ $ f.map_one ▸ f.mem_ker.mp h1,
    λ J x hJ hxf hxJ, _⟩,
  obtain ⟨y, hy⟩ := hf (f x)⁻¹,
  have H : 1 = y * x - (y * x - 1) := (sub_sub_cancel _ _).symm,
  rw H,
  refine J.sub_mem (J.mul_mem_left _ hxJ) (hJ _),
  rw f.mem_ker,
  simp only [hy, ring_hom.map_sub, ring_hom.map_one, ring_hom.map_mul,
    inv_mul_cancel (mt f.mem_ker.mpr hxf), sub_self],
end

-- move this
lemma local_ring.ker_eq_maximal_ideal {R K : Type*} [comm_ring R] [local_ring R] [field K]
  (φ : R →+* K) (hφ : surjective φ) : φ.ker = maximal_ideal R :=
local_ring.eq_maximal_ideal $ φ.ker_is_maximal_of_surjective hφ

-- move this
section
open polynomial finset.nat

lemma polynomial.X_add_one_pow_coeff (R : Type*) [semiring R] (n k : ℕ) :
  ((X + 1) ^ n).coeff k = (n.choose k : R) :=
begin
  rw [(commute_X (1 : polynomial R)).add_pow, ← lcoeff_apply, linear_map.map_sum],
  simp only [one_pow, mul_one, lcoeff_apply, ← C_eq_nat_cast, coeff_mul_C, nat.cast_id],
  rw [finset.sum_eq_single k, coeff_X_pow_self, one_mul],
  { intros _ _,
    simp only [coeff_X_pow, boole_mul, ite_eq_right_iff, ne.def] {contextual := tt},
    rintro h rfl, contradiction },
  { simp only [coeff_X_pow_self, one_mul, not_lt, finset.mem_range],
    intro h, rw [nat.choose_eq_zero_of_lt h, nat.cast_zero], }
end

open polynomial

/-- Vandermonde's identity -/
lemma nat.add_choose_eq (m n k : ℕ) :
  (m + n).choose k = ∑ (ij : ℕ × ℕ) in antidiagonal k, m.choose ij.1 * n.choose ij.2 :=
begin
  calc (m + n).choose k
      = ((X + 1) ^ (m + n)).coeff k : _
  ... = ((X + 1) ^ m * (X + 1) ^ n).coeff k : by rw pow_add
  ... = ∑ (ij : ℕ × ℕ) in antidiagonal k, m.choose ij.1 * n.choose ij.2 : _,
  { rw [X_add_one_pow_coeff, nat.cast_id], },
  { rw [coeff_mul, finset.sum_congr rfl],
    simp only [X_add_one_pow_coeff, nat.cast_id, eq_self_iff_true, imp_true_iff], }
end

end

-- move this
namespace smodeq

variables {R : Type*} [ring R]
variables {M : Type*} [add_comm_group M] [module R M] (U U₁ U₂ : submodule R M)
variables {x x₁ x₂ y y₁ y₂ z z₁ z₂ : M}
variables {N : Type*} [add_comm_group N] [module R N] (V V₁ V₂ : submodule R N)

lemma sub_mem : x ≡ y [SMOD U] ↔ x - y ∈ U :=
by rw [smodeq.def, submodule.quotient.eq]

lemma eval {R : Type*} [comm_ring R] {I : ideal R} {x y : R} (h : x ≡ y [SMOD I])
  (f : polynomial R) : f.eval x ≡ f.eval y [SMOD I] :=
begin
  rw [smodeq.def] at h ⊢,
  show ideal.quotient.mk I (f.eval x) = ideal.quotient.mk I (f.eval y),
  change ideal.quotient.mk I x = ideal.quotient.mk I y at h,
  rw [← polynomial.eval₂_at_apply, ← polynomial.eval₂_at_apply, h],
end

end smodeq

lemma enat.coe_eq_coe (n : ℕ) :
  @eq enat
    (@coe nat enat (@coe_to_lift nat enat (@nat.cast_coe enat (@add_zero_class.to_has_zero enat
      (@add_monoid.to_add_zero_class enat (@add_comm_monoid.to_add_monoid enat enat.add_comm_monoid)))
        enat.has_one (@add_zero_class.to_has_add enat (@add_monoid.to_add_zero_class enat
          (@add_comm_monoid.to_add_monoid enat enat.add_comm_monoid))))) n)
    (@coe nat enat (@coe_to_lift nat enat (@coe_base nat enat enat.has_coe)) n) :=
begin
  induction n with n ih, { refl },
  simp only [nat.succ_eq_add_one, enat.coe_one, enat.coe_add, nat.cast_add, nat.cast_one, ih],
end

namespace discrete_valuation_ring

variables {R : Type*} [integral_domain R] [discrete_valuation_ring R]

instance : is_Hausdorff (maximal_ideal R) R :=
{ haus' := λ x hx,
  begin
    simp only [← ideal.one_eq_top, smul_eq_mul, mul_one, smodeq.zero] at hx,
    rw [← add_val_eq_top_iff, enat.eq_top_iff_forall_le],
    intro n,
    obtain ⟨ϖ, hϖ⟩ := exists_irreducible R,
    have : add_val R (ϖ ^ n) = n,
    { rw [add_val_pow, add_val_uniformizer hϖ, nsmul_one, enat.coe_eq_coe], },
    rw irreducible_iff_uniformizer at hϖ,
    rw [← this, add_val_le_iff_dvd, ← ideal.mem_span_singleton, ← ideal.span_singleton_pow, ← hϖ],
    exact hx n,
  end }

end discrete_valuation_ring

namespace padic_int

open cau_seq

instance (p : ℕ) [hp : fact p.prime] : is_adic_complete (maximal_ideal ℤ_[p]) ℤ_[p] :=
{ prec' := λ x hx,
  begin
    simp only [← ideal.one_eq_top, smul_eq_mul, mul_one, smodeq.sub_mem, maximal_ideal_eq_span_p,
      ideal.span_singleton_pow, ← norm_le_pow_iff_mem_span_pow] at hx ⊢,
    let x' : cau_seq ℤ_[p] norm := ⟨x, _⟩, swap,
    { intros ε hε, obtain ⟨m, hm⟩ := exists_pow_neg_lt p hε,
      refine ⟨m, λ n hn, lt_of_le_of_lt _ hm⟩, rw [← neg_sub, norm_neg], exact hx hn },
    { refine ⟨x'.lim, λ n, _⟩,
      have : (0:ℝ) < p ^ (-n : ℤ), { apply fpow_pos_of_pos, exact_mod_cast hp.1.pos },
      obtain ⟨i, hi⟩ := equiv_def₃ (equiv_lim x') this,
      by_cases hin : i ≤ n,
      { exact (hi i le_rfl n hin).le, },
      { push_neg at hin, specialize hi i le_rfl i le_rfl, specialize hx hin.le,
        have := nonarchimedean (x n - x i) (x i - x'.lim),
        rw [sub_add_sub_cancel] at this,
        refine this.trans (max_le_iff.mpr ⟨hx, hi.le⟩), } },
  end }

end padic_int

namespace ideal

variables {R : Type*} [comm_ring R] (I : ideal R)

lemma pow_mem_pow {x : R} (hx : x ∈ I) (n : ℕ) : x ^ n ∈ I ^ n :=
begin
  induction n with n ih, { simp only [pow_zero, ideal.one_eq_top], },
  simpa only [pow_succ] using mul_mem_mul hx ih,
end

end ideal

namespace nat

open_locale nat

lemma cast_choose_eq (K : Type*) [division_ring K] [char_zero K] (a b : ℕ) (h : b ≤ a) :
  (a.choose b : K) = a! / b! / (a-b)! :=
begin
  have : ∀ {n : ℕ}, (n! : K) ≠ 0, { exact_mod_cast factorial_ne_zero },
  simp only [eq_div_iff_mul_eq this],
  norm_cast,
  rwa [mul_right_comm, nat.choose_mul_factorial_mul_factorial],
end

end nat

namespace polynomial

open_locale nat

section hasse_derivative

/-!
Reference: https://math.fontein.de/2009/08/12/the-hasse-derivative/
-/

variables {R : Type*} [semiring R] (k : ℕ) (f : polynomial R)

/-- The `k`th Hasse derivative of a polynomials `∑ a_i X^i` is `∑ (i.choose k) a_i X^(i-k)`.
It satisfies `k! * (hasse_derivative k f) = derivative^[k] f`. -/
def hasse_derivative (k : ℕ) : polynomial R →ₗ[R] polynomial R :=
{ to_fun := λ f, f.sum $ λ i r, monomial (i - k) (↑(i.choose k) * r),
  map_add' := λ f g,
  begin
    rw [sum_eq_of_subset _ _ _ _ support_add,
        sum_eq_of_subset _ _ _ _ (f.support.subset_union_left g.support),
        sum_eq_of_subset _ _ _ _ (f.support.subset_union_right g.support),
        ← finset.sum_add_distrib, finset.sum_congr rfl],
    { intros i hi, simp only [coeff_add, mul_add, linear_map.map_add], },
    all_goals { simp only [forall_const, monomial_zero_right, mul_zero], },
  end,
  map_smul' := λ c f,
  begin
    rw [sum_eq_of_subset _ _ _ _ (support_smul c f), sum_def, finset.smul_sum,
      finset.sum_congr rfl],
    { intros i hi,
      have := nat.cast_commute (i.choose k) c,
      simp only [coeff_smul, smul_monomial, smul_eq_mul, ← mul_assoc, this.eq], },
    { simp only [forall_const, monomial_zero_right, mul_zero], }
  end }
.

lemma hasse_derivative_apply :
  hasse_derivative k f = f.sum (λ i r, monomial (i - k) (↑(i.choose k) * r)) := rfl

lemma hasse_derivative_coeff (n : ℕ) :
  (hasse_derivative k f).coeff n = (n + k).choose k * f.coeff (n + k) :=
begin
  rw [hasse_derivative_apply, coeff_sum, sum_def, finset.sum_eq_single (n + k), coeff_monomial],
  { simp only [if_true, nat.add_sub_cancel, eq_self_iff_true], },
  { intros i hi hink,
    rw [coeff_monomial],
    by_cases hik : i < k,
    { simp only [nat.choose_eq_zero_of_lt hik, if_t_t, nat.cast_zero, zero_mul], },
    { push_neg at hik, rw if_neg, contrapose! hink, exact (nat.sub_eq_iff_eq_add hik).mp hink, } },
  { intro h, simp only [not_mem_support_iff.mp h, monomial_zero_right, mul_zero, coeff_zero] }
end

lemma hasse_derivative_zero' : hasse_derivative 0 f = f :=
by simp only [hasse_derivative_apply, nat.sub_zero, nat.choose_zero_right,
  nat.cast_one, one_mul, sum_monomial_eq]

@[simp] lemma hasse_derivative_zero : @hasse_derivative R _ 0 = linear_map.id :=
linear_map.ext $ hasse_derivative_zero'

lemma hasse_derivative_one' : hasse_derivative 1 f = derivative f :=
by simp only [hasse_derivative_apply, derivative_apply, monomial_eq_C_mul_X, nat.choose_one_right,
    (nat.cast_commute _ _).eq]

@[simp] lemma hasse_derivative_one : @hasse_derivative R _ 1 = derivative :=
linear_map.ext $ hasse_derivative_one'

@[simp] lemma hasse_derivative_monomial (n : ℕ) (r : R) :
  hasse_derivative k (monomial n r) = monomial (n - k) (↑(n.choose k) * r) :=
begin
  ext i,
  simp only [hasse_derivative_coeff, coeff_monomial],
  by_cases hnik : n = i + k,
  { rw [if_pos hnik, if_pos, ← hnik], apply nat.sub_eq_of_eq_add, rwa add_comm },
  { rw [if_neg hnik, mul_zero],
    by_cases hkn : k ≤ n,
    { rw [← nat.sub_eq_iff_eq_add hkn] at hnik, rw [if_neg hnik] },
    { push_neg at hkn, rw [nat.choose_eq_zero_of_lt hkn, nat.cast_zero, zero_mul, if_t_t] } }
end

lemma hasse_derivative_C (r : R) (hk : 0 < k) : hasse_derivative k (C r) = 0 :=
by rw [← monomial_zero_left, hasse_derivative_monomial, nat.choose_eq_zero_of_lt hk,
    nat.cast_zero, zero_mul, monomial_zero_right]

lemma hasse_derivative_apply_one (hk : 0 < k) : hasse_derivative k (1 : polynomial R) = 0 :=
by rw [← C_1, hasse_derivative_C k _ hk]

lemma hasse_derivative_X (hk : 1 < k) : hasse_derivative k (X : polynomial R) = 0 :=
by rw [← monomial_one_one_eq_X, hasse_derivative_monomial, nat.choose_eq_zero_of_lt hk,
    nat.cast_zero, zero_mul, monomial_zero_right]

open nat (hiding nsmul_eq_mul)

lemma factorial_smul_hasse_derivative :
  ⇑(k! • @hasse_derivative R _ k) = ((@derivative R _)^[k]) :=
begin
  induction k with k ih,
  { rw [hasse_derivative_zero, factorial_zero, iterate_zero, one_smul, linear_map.id_coe], },
  ext f n : 2,
  rw [iterate_succ_apply', ← ih],
  simp only [linear_map.smul_apply, coeff_smul, linear_map.map_smul_of_tower, coeff_derivative,
    hasse_derivative_coeff, ← @choose_symm_add _ k],
  simp only [nsmul_eq_mul, factorial_succ, mul_assoc, succ_eq_add_one, ← add_assoc,
    add_right_comm n 1 k, ← cast_succ],
  rw ← (cast_commute (n+1) (f.coeff (n + k + 1))).eq,
  simp only [← mul_assoc], norm_cast, congr' 2,
  apply @cast_injective ℚ,
  have h1 : n + 1 ≤ n + k + 1 := succ_le_succ le_self_add,
  have h2 : k + 1 ≤ n + k + 1 := succ_le_succ le_add_self,
  have H : ∀ (n : ℕ), (n! : ℚ) ≠ 0, { exact_mod_cast factorial_ne_zero },
  -- why can't `field_simp` help me here?
  simp only [cast_mul, cast_choose_eq ℚ, h1, h2, -one_div, -mul_eq_zero,
    succ_sub_succ_eq_sub, nat.add_sub_cancel, add_sub_cancel_left] with field_simps,
  rw [eq_div_iff_mul_eq (mul_ne_zero (H _) (H _)), eq_comm, div_mul_eq_mul_div,
    eq_div_iff_mul_eq (mul_ne_zero (H _) (H _))],
  norm_cast,
  simp only [factorial_succ, succ_eq_add_one], ring,
end
.

lemma hasse_derivative_comp (k l : ℕ) :
  (@hasse_derivative R _ k).comp (hasse_derivative l) = (k+l).choose k • hasse_derivative (k+l) :=
begin
  ext i : 2,
  simp only [linear_map.smul_apply, comp_app, linear_map.coe_comp, smul_monomial,
    hasse_derivative_apply, mul_one, monomial_eq_zero_iff, sum_monomial_index, mul_zero,
    nat.sub_sub, add_comm l k],
  rw_mod_cast nsmul_eq_mul,
  congr' 2,
  by_cases hikl : i < k + l,
  { rw [choose_eq_zero_of_lt hikl, mul_zero],
    by_cases hil : i < l,
    { rw [choose_eq_zero_of_lt hil, mul_zero] },
    { push_neg at hil, rw [← nat.sub_lt_right_iff_lt_add hil] at hikl,
      rw [choose_eq_zero_of_lt hikl , zero_mul], }, },
  push_neg at hikl, apply @cast_injective ℚ,
  have h1 : l ≤ i     := nat.le_of_add_le_right hikl,
  have h2 : k ≤ i - l := nat.le_sub_right_of_add_le hikl,
  have h3 : k ≤ k + l := le_self_add,
  have H : ∀ (n : ℕ), (n! : ℚ) ≠ 0, { exact_mod_cast factorial_ne_zero },
  -- why can't `field_simp` help me here?
  simp only [cast_mul, cast_choose_eq ℚ, h1, h2, h3, hikl, -one_div, -mul_eq_zero,
    succ_sub_succ_eq_sub, nat.add_sub_cancel, add_sub_cancel_left] with field_simps,
  rw [eq_div_iff_mul_eq, eq_comm, div_mul_eq_mul_div, eq_div_iff_mul_eq, nat.sub_sub, add_comm l k],
  { ring, },
  all_goals { apply_rules [mul_ne_zero, H] }
end
.

section
open add_monoid_hom

lemma hasse_derivative_mul (f g : polynomial R) :
  hasse_derivative k (f * g) =
    ∑ ij in finset.nat.antidiagonal k, hasse_derivative ij.1 f * hasse_derivative ij.2 g :=
begin
  let D := λ k, (@hasse_derivative R _ k).to_add_monoid_hom,
  let Φ := @add_monoid_hom.mul (polynomial R) _,
  show (comp_hom (D k)).comp Φ f g =
    ∑ (ij : ℕ × ℕ) in finset.nat.antidiagonal k,
      ((comp_hom.comp ((comp_hom Φ) (D ij.1))).flip (D ij.2) f) g,
  simp only [← finset_sum_apply],
  congr' 2, clear f g,
  ext m r n s : 4,
  simp only [finset_sum_apply, coe_mul_left, coe_comp, flip_apply, comp_app,
    hasse_derivative_monomial, linear_map.to_add_monoid_hom_coe, comp_hom_apply_apply, coe_mul,
    monomial_mul_monomial],
  have aux : ∀ (x : ℕ × ℕ), x ∈ finset.nat.antidiagonal k →
    monomial (m - x.1 + (n - x.2)) (↑(m.choose x.1) * r * (↑(n.choose x.2) * s)) =
    monomial (m + n - k) (↑(m.choose x.1) * ↑(n.choose x.2) * (r * s)),
  { intros x hx, rw [finset.nat.mem_antidiagonal] at hx, subst hx,
    by_cases hm : m < x.1,
    { simp only [nat.choose_eq_zero_of_lt hm, nat.cast_zero, zero_mul, monomial_zero_right], },
    by_cases hn : n < x.2,
    { simp only [nat.choose_eq_zero_of_lt hn, nat.cast_zero,
        zero_mul, mul_zero, monomial_zero_right], },
    push_neg at hm hn,
    rw [← nat.sub_add_comm hm, ← nat.add_sub_assoc hn, nat.sub_sub, add_comm x.2 x.1, mul_assoc,
      ← mul_assoc r, ← (nat.cast_commute _ r).eq, mul_assoc, mul_assoc], },
  conv_rhs { apply_congr, skip, rw aux _ H, },
  rw_mod_cast [← linear_map.map_sum, ← finset.sum_mul, ← nat.add_choose_eq],
end

end

end hasse_derivative

-- move this
/-- Evaluation of polynomials as linear map. -/
@[simps] def leval {R : Type*} [semiring R] (r : R) : polynomial R →ₗ[R] R :=
{ to_fun := λ f, f.eval r,
  map_add' := λ f g, eval_add,
  map_smul' := λ c f, by simp only [smul_eq_C_mul, eval_C_mul, smul_eq_mul] }

section taylor

variables {R : Type*} [semiring R] (r : R) (f : polynomial R)

/-- The Taylor expansion of a polynomial `f` at `r`. -/
def taylor (r : R) : polynomial R →ₗ[R] polynomial R :=
{ to_fun := λ f, f.comp (X + C r),
  map_add' := λ f g, add_comp,
  map_smul' := λ c f, by simp only [smul_eq_C_mul, C_mul_comp] }

lemma taylor_apply : taylor r f = f.comp (X + C r) := rfl

@[simp] lemma taylor_X : taylor r X = X + C r :=
by simp only [taylor_apply, X_comp]

@[simp] lemma taylor_C (x : R) : taylor r (C x) = C x :=
by simp only [taylor_apply, C_comp]

@[simp] lemma taylor_one : taylor r (1 : polynomial R) = C 1 :=
by rw [← C_1, taylor_C]

lemma taylor_coeff (n : ℕ) : (taylor r f).coeff n = (hasse_derivative n f).eval r :=
show (lcoeff R n).comp (taylor r) f = (leval r).comp (hasse_derivative n) f,
begin
  congr' 1, clear f, ext i,
  simp only [leval_apply, mul_one, one_mul, eval_monomial, linear_map.comp_apply, coeff_C_mul,
    hasse_derivative_monomial, taylor_apply, monomial_comp, C_1,
    (commute_X (C r)).add_pow i, linear_map.map_sum],
  simp only [lcoeff_apply, ← C_eq_nat_cast, mul_assoc, ← C_pow, ← C_mul, coeff_mul_C,
    (nat.cast_commute _ _).eq, coeff_X_pow, boole_mul, finset.sum_ite_eq, finset.mem_range],
  split_ifs with h, { refl },
  push_neg at h, rw [nat.choose_eq_zero_of_lt h, nat.cast_zero, mul_zero],
end

@[simp] lemma taylor_coeff_zero : (taylor r f).coeff 0 = f.eval r :=
by rw [taylor_coeff, hasse_derivative_zero, linear_map.id_apply]

@[simp] lemma taylor_coeff_one : (taylor r f).coeff 1 = f.derivative.eval r :=
by rw [taylor_coeff, hasse_derivative_one]

lemma taylor_eval {R} [comm_semiring R] (r : R) (f : polynomial R) (s : R) :
  (taylor r f).eval s = f.eval (s + r) :=
by simp only [taylor_apply, eval_comp, eval_C, eval_X, eval_add]

lemma taylor_eval_sub {R} [comm_ring R] (r : R) (f : polynomial R) (s : R) :
  (taylor r f).eval (s - r) = f.eval s :=
by rw [taylor_eval, sub_add_cancel]

lemma taylor_injective {R} [comm_ring R] (r : R) : function.injective (taylor r) :=
begin
  intros f g h,
  apply_fun taylor (-r) at h,
  simpa only [taylor_apply, comp_assoc, add_comp, X_comp, C_comp, C_neg,
    neg_add_cancel_right, comp_X] using h,
end

end taylor

lemma eq_zero_of_hasse_derivative_eq_zero {R} [comm_ring R] (f : polynomial R) (r : R)
  (h : ∀ k, (hasse_derivative k f).eval r = 0) :
  f = 0 :=
begin
  apply taylor_injective r,
  rw linear_map.map_zero,
  ext k,
  simp only [taylor_coeff, h, coeff_zero],
end

end polynomial

section
open polynomial

lemma henselian.tfae (R : Type u) [comm_ring R] [local_ring R] :
  tfae [
  henselian R,
  ∀ (f : polynomial R) (hf : f.monic) (a₀ : residue_field R) (h₁ : aeval a₀ f = 0)
    (h₂ : aeval a₀ f.derivative ≠ 0),
    ∃ a : R, f.is_root a ∧ (residue R a = a₀),
  ∀ {K : Type u} [field K], by exactI ∀ (φ : R →+* K) (hφ : surjective φ)
    (f : polynomial R) (hf : f.monic) (a₀ : K) (h₁ : f.eval₂ φ a₀ = 0)
    (h₂ : f.derivative.eval₂ φ a₀ ≠ 0),
    ∃ a : R, f.is_root a ∧ (φ a = a₀)] :=
begin
  tfae_have _3_2 : 3 → 2, { intro H, exact H (residue R) ideal.quotient.mk_surjective, },
  tfae_have _2_1 : 2 → 1,
  { intros H, constructor, intros f hf a₀ h₁ h₂,
    specialize H f hf (residue R a₀),
    have aux := flip mem_nonunits_iff.mp h₂,
    simp only [aeval_def, ring_hom.algebra_map_to_algebra, eval₂_at_apply,
      ← ideal.quotient.eq_zero_iff_mem, ← local_ring.mem_maximal_ideal] at H h₁ aux,
    obtain ⟨a, ha₁, ha₂⟩ := H h₁ aux,
    refine ⟨a, ha₁, _⟩,
    rw ← ideal.quotient.eq_zero_iff_mem,
    rwa [← sub_eq_zero, ← ring_hom.map_sub] at ha₂, },
  tfae_have _1_3 : 1 → 3,
  { introsI hR K _K φ hφ f hf a₀ h₁ h₂,
    obtain ⟨a₀, rfl⟩ := hφ a₀,
    have H := henselian.is_henselian f hf a₀,
    simp only [← local_ring.ker_eq_maximal_ideal φ hφ, eval₂_at_apply, φ.mem_ker] at H h₁ h₂,
    obtain ⟨a, ha₁, ha₂⟩ := H h₁ _,
    { refine ⟨a, ha₁, _⟩, rwa [φ.map_sub, sub_eq_zero] at ha₂, },
    { contrapose! h₂,
      rwa [← mem_nonunits_iff, ← local_ring.mem_maximal_ideal,
        ← local_ring.ker_eq_maximal_ideal φ hφ, φ.mem_ker] at h₂, } },
  tfae_finish,
end
.


instance is_adic_complete.henselian (R : Type*)
  [comm_ring R] [local_ring R] [is_adic_complete (maximal_ideal R) R] :
  henselian R :=
begin
  constructor,
  intros f hf a₀ h₁ h₂,
  classical,
  let I := maximal_ideal R,
  -- a temporary multiplicative inverse for units in `R`
  let inv : R → R := λ x, if hx : is_unit x then ↑hx.some⁻¹ else 0,
  have hinv : ∀ x, is_unit x → x * inv x = 1,
  { intros x hx, simp only [hx, inv, dif_pos], convert units.mul_inv hx.some, rw hx.some_spec },
  -- in the following line, `f.derivative.eval b` is a unit,
  -- because `b` has the same residue class as `a₀`
  let c : ℕ → R := λ n, nat.rec_on n a₀ (λ k b, b - f.eval b * inv (f.derivative.eval b)),
  have hc : ∀ n, c (n+1) = c n - f.eval (c n) * inv (f.derivative.eval (c n)),
  { intro n, dsimp only [c, nat.rec_add_one], refl, },
  have hc' : ∀ n, c n ≡ a₀ [SMOD I],
  { intro n, induction n with n ih, { refl },
    rw [nat.succ_eq_add_one, hc, sub_eq_add_neg, ← add_zero a₀],
    refine ih.add _,
    rw [smodeq.zero, ideal.neg_mem_iff],
    refine I.mul_mem_right _ _,
    rw [← smodeq.zero] at h₁ ⊢,
    exact (ih.eval f).trans h₁, },
  have hfc : ∀ n, is_unit (f.derivative.eval (c n)),
  { intro n, contrapose! h₂,
    rw [← mem_nonunits_iff, ← local_ring.mem_maximal_ideal, ← smodeq.zero] at h₂ ⊢,
    exact ((hc' n).symm.eval _).trans h₂, },
  have Hc : ∀ n, f.eval (c n) ∈ I ^ (n+1),
  { intro n,
    induction n with n ih, { simpa only [pow_one] },
    simp only [nat.succ_eq_add_one],
    rw [← taylor_eval_sub (c n), hc],
    simp only [sub_eq_add_neg, add_neg_cancel_comm],
    rw [eval_eq_sum, sum_over_range' _ _ _ (lt_add_of_pos_right _ zero_lt_two),
      ← finset.sum_range_add_sum_Ico _ (nat.le_add_left _ _)],
    swap, { intro i, rw zero_mul },
    refine ideal.add_mem _ _ _,
    { simp only [finset.sum_range_succ, taylor_coeff_one, mul_one, pow_one, mul_neg_eq_neg_mul_symm,
        taylor_coeff_zero, finset.sum_singleton, finset.range_one, pow_zero],
      rw [mul_left_comm, hinv _ (hfc n), mul_one, add_neg_self],
      exact ideal.zero_mem _ },
    { refine submodule.sum_mem _ _, simp only [finset.Ico.mem],
      rintro i ⟨h2i, hi⟩,
      have aux : n + 2 ≤ i * (n + 1), { transitivity 2 * (n + 1); nlinarith only [h2i], },
      refine ideal.mul_mem_left _ _ (ideal.pow_le_pow aux _),
      rw [pow_mul'],
      refine ideal.pow_mem_pow _ ((ideal.neg_mem_iff _).2 $ ideal.mul_mem_right _ _ ih) _, } },
  -- the sequence `c : ℕ → R` is a Cauchy sequence
  have aux : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : ideal R)],
  { intros m n hmn,
    rw [← ideal.one_eq_top, algebra.id.smul_eq_mul, mul_one],
    obtain ⟨k, rfl⟩ := nat.exists_eq_add_of_le hmn, clear hmn,
    induction k with k ih, { rw add_zero, },
    rw [nat.succ_eq_add_one, ← add_assoc, hc, ← add_zero (c m), sub_eq_add_neg],
    refine ih.add _, symmetry,
    rw [smodeq.zero, ideal.neg_mem_iff],
    refine ideal.mul_mem_right _ _ (ideal.pow_le_pow _ (Hc _)),
    rw [add_assoc], exact le_self_add },
  -- hence the sequence converges to some limit point `a`, which is the `a` we are looking for
  obtain ⟨a, ha⟩ := is_precomplete.prec' c aux,
  refine ⟨a, _, _⟩,
  { show f.is_root a,
    suffices : ∀ n, f.eval a ≡ 0 [SMOD (I ^ n • ⊤ : ideal R)], { from is_Hausdorff.haus' _ this },
    intro n, specialize ha n,
    rw [← ideal.one_eq_top, algebra.id.smul_eq_mul, mul_one] at ha ⊢,
    refine (ha.symm.eval f).trans _,
    rw [smodeq.zero],
    exact ideal.pow_le_pow le_self_add (Hc _), },
  { show a - a₀ ∈ maximal_ideal R,
    specialize ha 1,
    rw [hc, pow_one, ← ideal.one_eq_top, algebra.id.smul_eq_mul, mul_one, sub_eq_add_neg] at ha,
    rw [← smodeq.sub_mem, ← add_zero a₀],
    refine ha.symm.trans (smodeq.refl.add _),
    rw [smodeq.zero, ideal.neg_mem_iff],
    exact ideal.mul_mem_right _ _ h₁, }
end

/-
TODO: it's not clear to me (jmc) whether the following items can be easily included,
      maybe they depend on theory of etale algebras, just like the items further below

  ∀ (f : polynomial R) (a₀ : R) (h₁ : f.eval a₀ ∈ maximal_ideal R)
    (h₂ : f.derivative.eval a₀ ∉ maximal_ideal R),
    ∃ a : R, f.is_root a ∧ (a - a₀ ∈ maximal_ideal R),
  ∀ (f : polynomial R) (a₀ : residue_field R) (h₁ : aeval a₀ f = 0)
    (h₂ : aeval a₀ f.derivative ≠ 0),
    ∃ a : R, f.is_root a ∧ (residue R a = a₀),
  ∀ {K : Type u} [field K], by exactI ∀ (φ : R →+* K) (hφ : surjective φ)
    (f : polynomial R) (a₀ : K) (h₁ : f.eval₂ φ a₀ = 0)
    (h₂ : f.derivative.eval₂ φ a₀ ≠ 0),
    ∃ a : R, f.is_root a ∧ (φ a = a₀),

TODO: develop enough theory of etale algebras to include the following items in the `tfae`.

  ∀ (f : polynomial R) (hf : f.monic) (g₀ h₀ : polynomial (residue_field R))
    (h₁ : f.map (residue R) = g₀ * h₀) (h₂ : is_coprime g₀ h₀),
    ∃ g h : polynomial R, f = g * h ∧ g.map (residue R) = g₀ ∧ h.map (residue R) = h₀,
  ∀ (f : polynomial R) (g₀ h₀ : polynomial (residue_field R))
    (h₁ : f.map (residue R) = g₀ * h₀) (h₂ : is_coprime g₀ h₀),
    ∃ g h : polynomial R, f = g * h ∧ g.map (residue R) = g₀ ∧ h.map (residue R) = h₀ ∧
      g.degree = g₀.degree,
  ∀ {K : Type u} [field K], by exactI ∀ (φ : R →+* K) (hφ : surjective φ)
    (f : polynomial R) (hf : f.monic) (g₀ h₀ : polynomial K)
    (h₁ : f.map φ = g₀ * h₀) (h₂ : is_coprime g₀ h₀),
    ∃ g h : polynomial R, f = g * h ∧ g.map φ = g₀ ∧ h.map φ = h₀,
  ∀ {K : Type u} [field K], by exactI ∀ (φ : R →+* K) (hφ : surjective φ)
    (f : polynomial R) (g₀ h₀ : polynomial K)
    (h₁ : f.map φ = g₀ * h₀) (h₂ : is_coprime g₀ h₀),
    ∃ g h : polynomial R, f = g * h ∧ g.map φ = g₀ ∧ h.map φ = h₀ ∧
      g.degree = g₀.degree,

-- Here's a proof showing that the last item implies the 2nd but last item.

  -- tfae_have _10_8 : 10 → 8,
  -- { introsI H K _K φ hφ f a₀ h₁ h₂,
  --   let g₀ : polynomial K := X - C a₀,
  --   let h₀ := (f.map φ).div_by_monic g₀,
  --   have hg₀ : g₀.degree = 1 := degree_X_sub_C _,
  --   have hg₀h₀ : f.map φ = g₀ * h₀,
  --   { rw [← eval_map] at h₁, exact (mul_div_by_monic_eq_iff_is_root.mpr h₁).symm },
  --   have hcop : is_coprime g₀ h₀,
  --   { apply is_coprime_of_is_root_of_eval_derivative_ne_zero,
  --     rwa [derivative_map, eval_map] },
  --   obtain ⟨g, h, rfl, Hg, Hh, H2⟩ := H φ hφ f g₀ h₀ hg₀h₀ hcop,
  --   rw hg₀ at H2,
  --   obtain ⟨u, hu⟩ : is_unit (g.coeff 1),
  --   { apply local_ring.is_unit_of_mem_nonunits_one_sub_self,
  --     rw [← local_ring.mem_maximal_ideal, ← local_ring.ker_eq_maximal_ideal φ hφ, φ.mem_ker],
  --     have : (C a₀).nat_degree < 1, { simp only [nat_degree_C, nat.lt_one_iff], },
  --     simp only [ring_hom.map_sub, ring_hom.map_one, sub_eq_zero, ← polynomial.coeff_map, Hg,
  --       coeff_X_one, coeff_sub, coeff_eq_zero_of_nat_degree_lt this, sub_zero], },
  --   let a := ↑u⁻¹ * -g.coeff 0,
  --   refine ⟨a, _, _⟩,
  --   { apply root_mul_right_of_is_root,
  --     rw [is_root.def, eq_X_add_C_of_degree_le_one H2.le],
  --     simp only [eval_C, eval_X, eval_add, eval_mul, ← hu, a,
  --       units.mul_inv_cancel_left, add_left_neg], },
  --   { calc φ (↑u⁻¹ * -g.coeff 0) = (g₀.coeff 1)⁻¹ * - (g₀.coeff 0) :
  --           by simp only [φ.map_mul, φ.map_neg, ring_hom.map_units_inv, hu, ←Hg, coeff_map]
  --     ... = (g₀.leading_coeff)⁻¹ * - (g₀.coeff 0) : _
  --     ... = a₀ : _,
  --     { suffices : g₀.nat_degree = 1, { rw ← this, refl },
  --       rw degree_eq_nat_degree (monic_X_sub_C a₀).ne_zero at hg₀,
  --       exact_mod_cast hg₀ },
  --     { simp only [(monic_X_sub_C a₀).leading_coeff, inv_one, one_mul,
  --         coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, neg_neg], } } },
-/

end

instance (p : ℕ) [fact p.prime] : henselian ℤ_[p] := infer_instance

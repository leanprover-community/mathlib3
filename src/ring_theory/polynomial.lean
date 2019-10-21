/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Ring-theoretic supplement of data.polynomial.

Main result: Hilbert basis theorem, that if a ring is noetherian then so is its polynomial ring.
-/

import data.polynomial data.mv_polynomial
import ring_theory.subring
import ring_theory.ideals ring_theory.noetherian

noncomputable theory
local attribute [instance, priority 100] classical.prop_decidable

universes u v w

namespace polynomial

variables (R : Type u) [comm_ring R] [decidable_eq R]

/-- The `R`-submodule of `R[X]` consisting of polynomials of degree ≤ `n`. -/
def degree_le (n : with_bot ℕ) : submodule R (polynomial R) :=
⨅ k : ℕ, ⨅ h : ↑k > n, (lcoeff R k).ker

variable {R}

theorem mem_degree_le {n : with_bot ℕ} {f : polynomial R} :
  f ∈ degree_le R n ↔ degree f ≤ n :=
by simp only [degree_le, submodule.mem_infi, degree_le_iff_coeff_zero, linear_map.mem_ker]; refl

theorem degree_le_mono {m n : with_bot ℕ} (H : m ≤ n) :
  degree_le R m ≤ degree_le R n :=
λ f hf, mem_degree_le.2 (le_trans (mem_degree_le.1 hf) H)

theorem degree_le_eq_span_X_pow {n : ℕ} :
  degree_le R n = submodule.span R ↑((finset.range (n+1)).image (λ n, X^n) : finset (polynomial R)) :=
begin
  apply le_antisymm,
  { intros p hp, replace hp := mem_degree_le.1 hp,
    rw [← finsupp.sum_single p, finsupp.sum, submodule.mem_coe],
    refine submodule.sum_mem _ (λ k hk, _),
    have := with_bot.coe_le_coe.1 (finset.sup_le_iff.1 hp k hk),
    rw [single_eq_C_mul_X, C_mul'],
    refine submodule.smul_mem _ _ (submodule.subset_span $ finset.mem_coe.2 $
      finset.mem_image.2 ⟨_, finset.mem_range.2 (nat.lt_succ_of_le this), rfl⟩) },
  rw [submodule.span_le, finset.coe_image, set.image_subset_iff],
  intros k hk, apply mem_degree_le.2,
  apply le_trans (degree_X_pow_le _) (with_bot.coe_le_coe.2 $ nat.le_of_lt_succ $ finset.mem_range.1 hk)
end

/-- Given a polynomial, return the polynomial whose coefficients are in
the ring closure of the original coefficients. -/
def restriction (p : polynomial R) : polynomial (ring.closure (↑p.frange : set R)) :=
⟨p.support, λ i, ⟨p.to_fun i,
  if H : p.to_fun i = 0 then H.symm ▸ is_add_submonoid.zero_mem _
  else ring.subset_closure $ finsupp.mem_frange.2 ⟨H, i, rfl⟩⟩,
λ i, finsupp.mem_support_iff.trans (not_iff_not_of_iff ⟨λ H, subtype.eq H, subtype.mk.inj⟩)⟩

@[simp] theorem coeff_restriction {p : polynomial R} {n : ℕ} : ↑(coeff (restriction p) n) = coeff p n := rfl

@[simp] theorem coeff_restriction' {p : polynomial R} {n : ℕ} : (coeff (restriction p) n).1 = coeff p n := rfl

@[simp] theorem degree_restriction {p : polynomial R} : (restriction p).degree = p.degree := rfl

@[simp] theorem nat_degree_restriction {p : polynomial R} : (restriction p).nat_degree = p.nat_degree := rfl

@[simp] theorem monic_restriction {p : polynomial R} : monic (restriction p) ↔ monic p :=
⟨λ H, congr_arg subtype.val H, λ H, subtype.eq H⟩

@[simp] theorem restriction_zero : restriction (0 : polynomial R) = 0 := rfl

@[simp] theorem restriction_one : restriction (1 : polynomial R) = 1 :=
ext $ λ i, subtype.eq $ by rw [coeff_restriction', coeff_one, coeff_one]; split_ifs; refl

variables {S : Type v} [comm_ring S] {f : R → S} {x : S}

theorem eval₂_restriction {p : polynomial R} :
  eval₂ f x p = eval₂ (f ∘ subtype.val) x p.restriction :=
rfl

section to_subring
variables (p : polynomial R) (T : set R) [is_subring T]

/-- Given a polynomial `p` and a subring `T` that contains the coefficients of `p`,
return the corresponding polynomial whose coefficients are in `T. -/
def to_subring (hp : ↑p.frange ⊆ T) : polynomial T :=
⟨p.support, λ i, ⟨p.to_fun i,
  if H : p.to_fun i = 0 then H.symm ▸ is_add_submonoid.zero_mem _
  else hp $ finsupp.mem_frange.2 ⟨H, i, rfl⟩⟩,
λ i, finsupp.mem_support_iff.trans (not_iff_not_of_iff ⟨λ H, subtype.eq H, subtype.mk.inj⟩)⟩

variables (hp : ↑p.frange ⊆ T)
include hp

@[simp] theorem coeff_to_subring {n : ℕ} : ↑(coeff (to_subring p T hp) n) = coeff p n := rfl

@[simp] theorem coeff_to_subring' {n : ℕ} : (coeff (to_subring p T hp) n).1 = coeff p n := rfl

@[simp] theorem degree_to_subring : (to_subring p T hp).degree = p.degree := rfl

@[simp] theorem nat_degree_to_subring : (to_subring p T hp).nat_degree = p.nat_degree := rfl

@[simp] theorem monic_to_subring : monic (to_subring p T hp) ↔ monic p :=
⟨λ H, congr_arg subtype.val H, λ H, subtype.eq H⟩

omit hp

@[simp] theorem to_subring_zero : to_subring (0 : polynomial R) T (set.empty_subset _) = 0 := rfl

@[simp] theorem to_subring_one : to_subring (1 : polynomial R) T
  (set.subset.trans (finset.coe_subset.2 finsupp.frange_single)
    (set.singleton_subset_iff.2 (is_submonoid.one_mem _))) = 1 :=
ext $ λ i, subtype.eq $ by rw [coeff_to_subring', coeff_one, coeff_one]; split_ifs; refl

theorem to_subring_eval₂ {S : Type*} [semiring S] (f : R → S) (x : S) :
  eval₂ (f ∘ subtype.val) x (to_subring p T hp) = eval₂ f x p := rfl

end to_subring

variables (T : set R) [is_subring T]

/-- Given a polynomial whose coefficients are in some subring, return
the corresponding polynomial whose coefificents are in the ambient ring. -/
def of_subring (p : polynomial T) : polynomial R :=
⟨p.support, subtype.val ∘ p.to_fun,
λ n, finsupp.mem_support_iff.trans (not_iff_not_of_iff
  ⟨λ h, congr_arg subtype.val h, λ h, subtype.eq h⟩)⟩

@[simp] theorem frange_of_subring {p : polynomial T} :
  ↑(p.of_subring T).frange ⊆ T :=
λ y H, let ⟨hy, x, hx⟩ := finsupp.mem_frange.1 H in hx ▸ (p.to_fun x).2

end polynomial

variables {R : Type u} [comm_ring R] [decidable_eq R]

namespace ideal
open polynomial

/-- Transport an ideal of `R[X]` to an `R`-submodule of `R[X]`. -/
def of_polynomial (I : ideal (polynomial R)) : submodule R (polynomial R) :=
{ carrier := I.carrier,
  zero := I.zero_mem,
  add := λ _ _, I.add_mem,
  smul := λ c x H, by rw [← C_mul']; exact submodule.smul_mem _ _ H }

variables {I : ideal (polynomial R)}
theorem mem_of_polynomial (x) : x ∈ I.of_polynomial ↔ x ∈ I := iff.rfl
variables (I)

/-- Given an ideal `I` of `R[X]`, make the `R`-submodule of `I`
consisting of polynomials of degree ≤ `n`. -/
def degree_le (n : with_bot ℕ) : submodule R (polynomial R) :=
degree_le R n ⊓ I.of_polynomial

/-- Given an ideal `I` of `R[X]`, make the ideal in `R` of
leading coefficients of polynomials in `I` with degree ≤ `n`. -/
def leading_coeff_nth (n : ℕ) : ideal R :=
(I.degree_le n).map $ lcoeff R n

theorem mem_leading_coeff_nth (n : ℕ) (x) :
  x ∈ I.leading_coeff_nth n ↔ ∃ p ∈ I, degree p ≤ n ∧ leading_coeff p = x :=
begin
  simp only [leading_coeff_nth, degree_le, submodule.mem_map, lcoeff_apply, submodule.mem_inf, mem_degree_le],
  split,
  { rintro ⟨p, ⟨hpdeg, hpI⟩, rfl⟩,
    cases lt_or_eq_of_le hpdeg with hpdeg hpdeg,
    { refine ⟨0, I.zero_mem, lattice.bot_le, _⟩,
      rw [leading_coeff_zero, eq_comm],
      exact coeff_eq_zero_of_degree_lt hpdeg },
    { refine ⟨p, hpI, le_of_eq hpdeg, _⟩,
      rw [leading_coeff, nat_degree, hpdeg], refl } },
  { rintro ⟨p, hpI, hpdeg, rfl⟩,
    have : nat_degree p + (n - nat_degree p) = n,
    { exact nat.add_sub_cancel' (nat_degree_le_of_degree_le hpdeg) },
    refine ⟨p * X ^ (n - nat_degree p), ⟨_, I.mul_mem_right hpI⟩, _⟩,
    { apply le_trans (degree_mul_le _ _) _,
      apply le_trans (add_le_add' (degree_le_nat_degree) (degree_X_pow_le _)) _,
      rw [← with_bot.coe_add, this],
      exact le_refl _ },
    { rw [leading_coeff, ← coeff_mul_X_pow p (n - nat_degree p), this] } }
end

theorem mem_leading_coeff_nth_zero (x) :
  x ∈ I.leading_coeff_nth 0 ↔ C x ∈ I :=
(mem_leading_coeff_nth _ _ _).trans
⟨λ ⟨p, hpI, hpdeg, hpx⟩, by rwa [← hpx, leading_coeff,
  nat.eq_zero_of_le_zero (nat_degree_le_of_degree_le hpdeg),
  ← eq_C_of_degree_le_zero hpdeg],
λ hx, ⟨C x, hx, degree_C_le, leading_coeff_C x⟩⟩

theorem leading_coeff_nth_mono {m n : ℕ} (H : m ≤ n) :
  I.leading_coeff_nth m ≤ I.leading_coeff_nth n :=
begin
  intros r hr,
  simp only [submodule.mem_coe, mem_leading_coeff_nth] at hr ⊢,
  rcases hr with ⟨p, hpI, hpdeg, rfl⟩,
  refine ⟨p * X ^ (n - m), I.mul_mem_right hpI, _, leading_coeff_mul_X_pow⟩,
  refine le_trans (degree_mul_le _ _) _,
  refine le_trans (add_le_add' hpdeg (degree_X_pow_le _)) _,
  rw [← with_bot.coe_add, nat.add_sub_cancel' H],
  exact le_refl _
end

/-- Given an ideal `I` in `R[X]`, make the ideal in `R` of the
leading coefficients in `I`. -/
def leading_coeff : ideal R :=
⨆ n : ℕ, I.leading_coeff_nth n

theorem mem_leading_coeff (x) :
  x ∈ I.leading_coeff ↔ ∃ p ∈ I, polynomial.leading_coeff p = x :=
begin
  rw [leading_coeff, submodule.mem_supr_of_directed],
  simp only [mem_leading_coeff_nth],
  { split, { rintro ⟨i, p, hpI, hpdeg, rfl⟩, exact ⟨p, hpI, rfl⟩ },
    rintro ⟨p, hpI, rfl⟩, exact ⟨nat_degree p, p, hpI, degree_le_nat_degree, rfl⟩ },
  { exact ⟨0⟩ },
  intros i j, exact ⟨i + j, I.leading_coeff_nth_mono (nat.le_add_right _ _),
    I.leading_coeff_nth_mono (nat.le_add_left _ _)⟩
end

theorem is_fg_degree_le [is_noetherian_ring R] (n : ℕ) :
  submodule.fg (I.degree_le n) :=
is_noetherian_submodule_left.1 (is_noetherian_of_fg_of_noetherian _
  ⟨_, degree_le_eq_span_X_pow.symm⟩) _

end ideal

/-- Hilbert basis theorem. -/
theorem is_noetherian_ring_polynomial [is_noetherian_ring R] : is_noetherian_ring (polynomial R) :=
⟨assume I : ideal (polynomial R),
let L := I.leading_coeff in
let M := well_founded.min (is_noetherian_iff_well_founded.1 (by apply_instance))
  (set.range I.leading_coeff_nth) (set.ne_empty_of_mem ⟨0, rfl⟩) in
have hm : M ∈ set.range I.leading_coeff_nth := well_founded.min_mem _ _ _,
let ⟨N, HN⟩ := hm, ⟨s, hs⟩ := I.is_fg_degree_le N in
have hm2 : ∀ k, I.leading_coeff_nth k ≤ M := λ k, or.cases_on (le_or_lt k N)
  (λ h, HN ▸ I.leading_coeff_nth_mono h)
  (λ h x hx, classical.by_contradiction $ λ hxm,
    have ¬M < I.leading_coeff_nth k, by refine well_founded.not_lt_min
      (well_founded_submodule_gt _ _) _ _ _; exact ⟨k, rfl⟩,
    this ⟨HN ▸ I.leading_coeff_nth_mono (le_of_lt h), λ H, hxm (H hx)⟩),
have hs2 : ∀ {x}, x ∈ I.degree_le N → x ∈ ideal.span (↑s : set (polynomial R)),
from hs ▸ λ x hx, submodule.span_induction hx (λ _ hx, ideal.subset_span hx) (ideal.zero_mem _)
  (λ _ _, ideal.add_mem _) (λ c f hf, f.C_mul' c ▸ ideal.mul_mem_left _ hf),
⟨s, le_antisymm (ideal.span_le.2 $ λ x hx, have x ∈ I.degree_le N, from hs ▸ submodule.subset_span hx, this.2) $ begin
  change I ≤ ideal.span ↑s,
  intros p hp, generalize hn : p.nat_degree = k,
  induction k using nat.strong_induction_on with k ih generalizing p,
  cases le_or_lt k N,
  { subst k, refine hs2 ⟨polynomial.mem_degree_le.2
      (le_trans polynomial.degree_le_nat_degree $ with_bot.coe_le_coe.2 h), hp⟩ },
  { have hp0 : p ≠ 0,
    { rintro rfl, cases hn, exact nat.not_lt_zero _ h },
    have : (0 : R) ≠ 1,
    { intro h, apply hp0, ext i, refine (mul_one _).symm.trans _,
      rw [← h, mul_zero], refl },
    letI : nonzero_comm_ring R := { zero_ne_one := this,
      ..(infer_instance : comm_ring R) },
    have : p.leading_coeff ∈ I.leading_coeff_nth N,
    { rw HN, exact hm2 k ((I.mem_leading_coeff_nth _ _).2
        ⟨_, hp, hn ▸ polynomial.degree_le_nat_degree, rfl⟩) },
    rw I.mem_leading_coeff_nth at this,
    rcases this with ⟨q, hq, hdq, hlqp⟩,
    have hq0 : q ≠ 0,
    { intro H, rw [← polynomial.leading_coeff_eq_zero] at H,
      rw [hlqp, polynomial.leading_coeff_eq_zero] at H, exact hp0 H },
    have h1 : p.degree = (q * polynomial.X ^ (k - q.nat_degree)).degree,
    { rw [polynomial.degree_mul_eq', polynomial.degree_X_pow],
      rw [polynomial.degree_eq_nat_degree hp0, polynomial.degree_eq_nat_degree hq0],
      rw [← with_bot.coe_add, nat.add_sub_cancel', hn],
      { refine le_trans (polynomial.nat_degree_le_of_degree_le hdq) (le_of_lt h) },
      rw [polynomial.leading_coeff_X_pow, mul_one],
      exact mt polynomial.leading_coeff_eq_zero.1 hq0 },
    have h2 : p.leading_coeff = (q * polynomial.X ^ (k - q.nat_degree)).leading_coeff,
    { rw [← hlqp, polynomial.leading_coeff_mul_X_pow] },
    have := polynomial.degree_sub_lt h1 hp0 h2,
    rw [polynomial.degree_eq_nat_degree hp0] at this,
    rw ← sub_add_cancel p (q * polynomial.X ^ (k - q.nat_degree)),
    refine (ideal.span ↑s).add_mem _ ((ideal.span ↑s).mul_mem_right _),
    { by_cases hpq : p - q * polynomial.X ^ (k - q.nat_degree) = 0,
      { rw hpq, exact ideal.zero_mem _ },
      refine ih _ _ (I.sub_mem hp (I.mul_mem_right hq)) rfl,
      rwa [polynomial.degree_eq_nat_degree hpq, with_bot.coe_lt_coe, hn] at this },
    exact hs2 ⟨polynomial.mem_degree_le.2 hdq, hq⟩ }
end⟩⟩

theorem is_noetherian_ring_mv_polynomial_fin {n : ℕ} [is_noetherian_ring R] :
  is_noetherian_ring (mv_polynomial (fin n) R) :=
begin
  induction n with n ih,
  { exact is_noetherian_ring_of_ring_equiv R
      ((mv_polynomial.pempty_ring_equiv R).symm.trans $ mv_polynomial.ring_equiv_of_equiv _
        ⟨pempty.elim, fin.elim0, λ x, pempty.elim x, λ x, fin.elim0 x⟩) },
  exact @is_noetherian_ring_of_ring_equiv (polynomial (mv_polynomial (fin n) R)) _
    (mv_polynomial (fin (n+1)) R) _
    ((mv_polynomial.option_equiv_left _ _).symm.trans (mv_polynomial.ring_equiv_of_equiv _
      ⟨λ x, option.rec_on x 0 fin.succ, λ x, fin.cases none some x,
      by rintro ⟨none | x⟩; [refl, exact fin.cases_succ _],
      λ x, fin.cases rfl (λ i, show (option.rec_on (fin.cases none some (fin.succ i) : option (fin n))
        0 fin.succ : fin n.succ) = _, by rw fin.cases_succ) x⟩))
    (@@is_noetherian_ring_polynomial _ _ ih)
end

theorem is_noetherian_ring_mv_polynomial_of_fintype {σ : Type v} [fintype σ] [decidable_eq σ]
  [is_noetherian_ring R] : is_noetherian_ring (mv_polynomial σ R) :=
trunc.induction_on (fintype.equiv_fin σ) $ λ e,
@is_noetherian_ring_of_ring_equiv (mv_polynomial (fin (fintype.card σ)) R) _ _ _
  (mv_polynomial.ring_equiv_of_equiv _ e.symm) is_noetherian_ring_mv_polynomial_fin

/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Ring-theoretic supplement of data.polynomial.

Main result: Hilbert basis theorem, that if a ring is noetherian then so is its polynomial ring.
-/
import algebra.char_p
import data.mv_polynomial
import ring_theory.noetherian

noncomputable theory
local attribute [instance, priority 100] classical.prop_decidable

universes u v w

namespace polynomial

instance {R : Type u} [comm_semiring R] (p : ℕ) [h : char_p R p] : char_p (polynomial R) p :=
let ⟨h⟩ := h in ⟨λ n, by rw [← C.map_nat_cast, ← C_0, C_inj, h]⟩

variables (R : Type u) [comm_ring R]

/-- The `R`-submodule of `R[X]` consisting of polynomials of degree ≤ `n`. -/
def degree_le (n : with_bot ℕ) : submodule R (polynomial R) :=
⨅ k : ℕ, ⨅ h : ↑k > n, (lcoeff R k).ker

/-- The `R`-submodule of `R[X]` consisting of polynomials of degree < `n`. -/
def degree_lt (n : ℕ) : submodule R (polynomial R) :=
⨅ k : ℕ, ⨅ h : k ≥ n, (lcoeff R k).ker

variable {R}

theorem mem_degree_le {n : with_bot ℕ} {f : polynomial R} :
  f ∈ degree_le R n ↔ degree f ≤ n :=
by simp only [degree_le, submodule.mem_infi, degree_le_iff_coeff_zero, linear_map.mem_ker]; refl

@[mono] theorem degree_le_mono {m n : with_bot ℕ} (H : m ≤ n) :
  degree_le R m ≤ degree_le R n :=
λ f hf, mem_degree_le.2 (le_trans (mem_degree_le.1 hf) H)

theorem degree_le_eq_span_X_pow {n : ℕ} :
  degree_le R n = submodule.span R ↑((finset.range (n+1)).image (λ n, X^n) : finset (polynomial R)) :=
begin
  apply le_antisymm,
  { intros p hp, replace hp := mem_degree_le.1 hp,
    rw [← finsupp.sum_single p, finsupp.sum],
    refine submodule.sum_mem _ (λ k hk, _),
    show monomial _ _ ∈ _,
    have := with_bot.coe_le_coe.1 (finset.sup_le_iff.1 hp k hk),
    rw [single_eq_C_mul_X, C_mul'],
    refine submodule.smul_mem _ _ (submodule.subset_span $ finset.mem_coe.2 $
      finset.mem_image.2 ⟨_, finset.mem_range.2 (nat.lt_succ_of_le this), rfl⟩) },
  rw [submodule.span_le, finset.coe_image, set.image_subset_iff],
  intros k hk, apply mem_degree_le.2,
  apply le_trans (degree_X_pow_le _) (with_bot.coe_le_coe.2 $ nat.le_of_lt_succ $ finset.mem_range.1 hk)
end

theorem mem_degree_lt {n : ℕ} {f : polynomial R} :
  f ∈ degree_lt R n ↔ degree f < n :=
by { simp_rw [degree_lt, submodule.mem_infi, linear_map.mem_ker, degree,
    finset.sup_lt_iff (with_bot.bot_lt_coe n), finsupp.mem_support_iff, with_bot.some_eq_coe,
    with_bot.coe_lt_coe, lt_iff_not_ge', ne, not_imp_not], refl }

@[mono] theorem degree_lt_mono {m n : ℕ} (H : m ≤ n) :
  degree_lt R m ≤ degree_lt R n :=
λ f hf, mem_degree_lt.2 (lt_of_lt_of_le (mem_degree_lt.1 hf) $ with_bot.coe_le_coe.2 H)

theorem degree_lt_eq_span_X_pow {n : ℕ} :
  degree_lt R n = submodule.span R ↑((finset.range n).image (λ n, X^n) : finset (polynomial R)) :=
begin
  apply le_antisymm,
  { intros p hp, replace hp := mem_degree_lt.1 hp,
    rw [← finsupp.sum_single p, finsupp.sum],
    refine submodule.sum_mem _ (λ k hk, _),
    show monomial _ _ ∈ _,
    have := with_bot.coe_lt_coe.1 ((finset.sup_lt_iff $ with_bot.bot_lt_coe n).1 hp k hk),
    rw [single_eq_C_mul_X, C_mul'],
    refine submodule.smul_mem _ _ (submodule.subset_span $ finset.mem_coe.2 $
      finset.mem_image.2 ⟨_, finset.mem_range.2 this, rfl⟩) },
  rw [submodule.span_le, finset.coe_image, set.image_subset_iff],
  intros k hk, apply mem_degree_lt.2,
  exact lt_of_le_of_lt (degree_X_pow_le _) (with_bot.coe_lt_coe.2 $ finset.mem_range.1 hk)
end

/-- Given a polynomial, return the polynomial whose coefficients are in
the ring closure of the original coefficients. -/
def restriction (p : polynomial R) : polynomial (ring.closure (↑p.frange : set R)) :=
⟨p.support, λ i, ⟨p.to_fun i,
  if H : p.to_fun i = 0 then H.symm ▸ is_add_submonoid.zero_mem
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

variables {S : Type v} [comm_ring S] {f : R →+* S} {x : S}

theorem eval₂_restriction {p : polynomial R} :
  eval₂ f x p = eval₂ (f.comp (is_subring.subtype _)) x p.restriction :=
rfl

section to_subring
variables (p : polynomial R) (T : set R) [is_subring T]

/-- Given a polynomial `p` and a subring `T` that contains the coefficients of `p`,
return the corresponding polynomial whose coefficients are in `T. -/
def to_subring (hp : ↑p.frange ⊆ T) : polynomial T :=
⟨p.support, λ i, ⟨p.to_fun i,
  if H : p.to_fun i = 0 then H.symm ▸ is_add_submonoid.zero_mem
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
    (finset.singleton_subset_set_iff.2 is_submonoid.one_mem)) = 1 :=
ext $ λ i, subtype.eq $ by rw [coeff_to_subring', coeff_one, coeff_one]; split_ifs; refl

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

variables {R : Type u} {σ : Type v} [comm_ring R]

namespace ideal
open polynomial

/-- Transport an ideal of `R[X]` to an `R`-submodule of `R[X]`. -/
def of_polynomial (I : ideal (polynomial R)) : submodule R (polynomial R) :=
{ carrier := I.carrier,
  zero_mem' := I.zero_mem,
  add_mem' := λ _ _, I.add_mem,
  smul_mem' := λ c x H, by rw [← C_mul']; exact submodule.smul_mem _ _ H }

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
    { refine ⟨0, I.zero_mem, bot_le, _⟩,
      rw [leading_coeff_zero, eq_comm],
      exact coeff_eq_zero_of_degree_lt hpdeg },
    { refine ⟨p, hpI, le_of_eq hpdeg, _⟩,
      rw [leading_coeff, nat_degree, hpdeg], refl } },
  { rintro ⟨p, hpI, hpdeg, rfl⟩,
    have : nat_degree p + (n - nat_degree p) = n,
    { exact nat.add_sub_cancel' (nat_degree_le_of_degree_le hpdeg) },
    refine ⟨p * X ^ (n - nat_degree p), ⟨_, I.mul_mem_right hpI⟩, _⟩,
    { apply le_trans (degree_mul_le _ _) _,
      apply le_trans (add_le_add (degree_le_nat_degree) (degree_X_pow_le _)) _,
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
  refine le_trans (add_le_add hpdeg (degree_X_pow_le _)) _,
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
  intros i j, exact ⟨i + j, I.leading_coeff_nth_mono (nat.le_add_right _ _),
    I.leading_coeff_nth_mono (nat.le_add_left _ _)⟩
end

theorem is_fg_degree_le [is_noetherian_ring R] (n : ℕ) :
  submodule.fg (I.degree_le n) :=
is_noetherian_submodule_left.1 (is_noetherian_of_fg_of_noetherian _
  ⟨_, degree_le_eq_span_X_pow.symm⟩) _

end ideal

/-- Hilbert basis theorem: a polynomial ring over a noetherian ring is a noetherian ring. -/
protected theorem polynomial.is_noetherian_ring [is_noetherian_ring R] : is_noetherian_ring (polynomial R) :=
⟨assume I : ideal (polynomial R),
let L := I.leading_coeff in
let M := well_founded.min (is_noetherian_iff_well_founded.1 (by apply_instance))
  (set.range I.leading_coeff_nth) ⟨_, ⟨0, rfl⟩⟩ in
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
    haveI : nonzero R := ⟨this⟩,
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

attribute [instance] polynomial.is_noetherian_ring

namespace mv_polynomial

lemma is_noetherian_ring_fin_0 [is_noetherian_ring R] :
  is_noetherian_ring (mv_polynomial (fin 0) R) :=
is_noetherian_ring_of_ring_equiv R
  ((mv_polynomial.pempty_ring_equiv R).symm.trans
   (mv_polynomial.ring_equiv_of_equiv _ fin_zero_equiv'.symm))

theorem is_noetherian_ring_fin [is_noetherian_ring R] :
  ∀ {n : ℕ}, is_noetherian_ring (mv_polynomial (fin n) R)
| 0 := is_noetherian_ring_fin_0
| (n+1) :=
  @is_noetherian_ring_of_ring_equiv (polynomial (mv_polynomial (fin n) R)) _ _ _
    (mv_polynomial.fin_succ_equiv _ n).symm
    (@polynomial.is_noetherian_ring (mv_polynomial (fin n) R) _ (is_noetherian_ring_fin))

/-- The multivariate polynomial ring in finitely many variables over a noetherian ring
is itself a noetherian ring. -/
instance is_noetherian_ring [fintype σ] [is_noetherian_ring R] :
  is_noetherian_ring (mv_polynomial σ R) :=
trunc.induction_on (fintype.equiv_fin σ) $ λ e,
@is_noetherian_ring_of_ring_equiv (mv_polynomial (fin (fintype.card σ)) R) _ _ _
  (mv_polynomial.ring_equiv_of_equiv _ e.symm) is_noetherian_ring_fin

lemma is_integral_domain_fin_zero (R : Type u) [comm_ring R] (hR : is_integral_domain R) :
  is_integral_domain (mv_polynomial (fin 0) R) :=
ring_equiv.is_integral_domain R hR
  ((ring_equiv_of_equiv R fin_zero_equiv').trans (mv_polynomial.pempty_ring_equiv R))

/-- Auxilliary lemma:
Multivariate polynomials over an integral domain
with variables indexed by `fin n` form an integral domain.
This fact is proven inductively,
and then used to prove the general case without any finiteness hypotheses.
See `mv_polynomial.integral_domain` for the general case. -/
lemma is_integral_domain_fin (R : Type u) [comm_ring R] (hR : is_integral_domain R) :
  ∀ (n : ℕ), is_integral_domain (mv_polynomial (fin n) R)
| 0 := is_integral_domain_fin_zero R hR
| (n+1) :=
  ring_equiv.is_integral_domain
    (polynomial (mv_polynomial (fin n) R))
    (is_integral_domain_fin n).polynomial
    (mv_polynomial.fin_succ_equiv _ n)

lemma is_integral_domain_fintype (R : Type u) (σ : Type v) [comm_ring R] [fintype σ]
  (hR : is_integral_domain R) : is_integral_domain (mv_polynomial σ R) :=
trunc.induction_on (fintype.equiv_fin σ) $ λ e,
@ring_equiv.is_integral_domain _ (mv_polynomial (fin $ fintype.card σ) R) _ _
  (mv_polynomial.is_integral_domain_fin _ hR _)
  (ring_equiv_of_equiv R e)

/-- Auxilliary definition:
Multivariate polynomials in finitely many variables over an integral domain form an integral domain.
This fact is proven by transport of structure from the `mv_polynomial.integral_domain_fin`,
and then used to prove the general case without finiteness hypotheses.
See `mv_polynomial.integral_domain` for the general case. -/
def integral_domain_fintype (R : Type u) (σ : Type v) [integral_domain R] [fintype σ] :
  integral_domain (mv_polynomial σ R) :=
@is_integral_domain.to_integral_domain _ _ $ mv_polynomial.is_integral_domain_fintype R σ $
integral_domain.to_is_integral_domain R

protected theorem eq_zero_or_eq_zero_of_mul_eq_zero {R : Type u} [integral_domain R] {σ : Type v}
  (p q : mv_polynomial σ R) (h : p * q = 0) : p = 0 ∨ q = 0 :=
begin
  obtain ⟨s, p, rfl⟩ := exists_finset_rename p,
  obtain ⟨t, q, rfl⟩ := exists_finset_rename q,
  have : p.rename (subtype.map id (finset.subset_union_left s t) : {x // x ∈ s} → {x // x ∈ s ∪ t}) *
    q.rename (subtype.map id (finset.subset_union_right s t)) = 0,
  { apply rename_injective _ subtype.val_injective, simpa using h },
  letI := mv_polynomial.integral_domain_fintype R {x // x ∈ (s ∪ t)},
  rw mul_eq_zero at this,
  cases this; [left, right],
  all_goals { simpa using congr_arg (rename subtype.val) this }
end

/-- The multivariate polynomial ring over an integral domain is an integral domain. -/
instance {R : Type u} {σ : Type v} [integral_domain R] :
  integral_domain (mv_polynomial σ R) :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := mv_polynomial.eq_zero_or_eq_zero_of_mul_eq_zero,
  zero_ne_one :=
  begin
    intro H,
    have : eval₂ id (λ s, (0:R)) (0 : mv_polynomial σ R) =
      eval₂ id (λ s, (0:R)) (1 : mv_polynomial σ R),
    { congr, exact H },
    simpa,
  end,
  .. (by apply_instance : comm_ring (mv_polynomial σ R)) }

end mv_polynomial

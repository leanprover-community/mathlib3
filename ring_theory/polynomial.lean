/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Hilbert basis theorem: if a ring is noetherian then so is its polynomial ring.
-/

import linear_algebra.multivariate_polynomial
import data.polynomial
import ring_theory.principal_ideal_domain
import ring_theory.subring

universes u v w

namespace polynomial

section
variables {R : Type u} [comm_semiring R] [decidable_eq R]

theorem degree_le_iff_coeff_zero (f : polynomial R) (n : with_bot ℕ) :
  degree f ≤ n ↔ ∀ m : ℕ, n < m → coeff f m = 0 :=
⟨λ (H : finset.sup (f.support) some ≤ n) m (Hm : n < (m : with_bot ℕ)), decidable.of_not_not $ λ H4,
  have H1 : m ∉ f.support,
    from λ H2, not_lt_of_ge ((finset.sup_le_iff.1 H) m H2 : ((m : with_bot ℕ) ≤ n)) Hm,
  H1 $ (finsupp.mem_support_to_fun f m).2 H4,
λ H, finset.sup_le $ λ b Hb, decidable.of_not_not $ λ Hn,
  (finsupp.mem_support_to_fun f b).1 Hb $ H b $ lt_of_not_ge Hn⟩

theorem degree_C_mul_X_pow_le (r : R) (n : ℕ) : degree (C r * X^n : polynomial R) ≤ n :=
by rw [← single_eq_C_mul_X]; exact finset.sup_le (λ b hb,
by rw list.eq_of_mem_singleton (finsupp.support_single_subset hb); exact le_refl _)

theorem degree_X_pow_le (n : ℕ) : degree (X^n : polynomial R) ≤ n :=
by simpa only [C_1, one_mul] using degree_C_mul_X_pow_le (1:R) n

theorem degree_X_le (n : ℕ) : degree (X : polynomial R) ≤ 1 :=
by simpa only [C_1, one_mul, pow_one] using degree_C_mul_X_pow_le (1:R) 1

theorem nat_degree_le_of_degree_le {p : polynomial R} {n : ℕ}
  (H : degree p ≤ n) : nat_degree p ≤ n :=
show option.get_or_else (degree p) 0 ≤ n, from match degree p, H with
| none,     H := zero_le _
| (some d), H := with_bot.coe_le_coe.1 H
end

theorem leading_coeff_mul_X_pow {p : polynomial R} {n : ℕ} :
  leading_coeff (p * X ^ n) = leading_coeff p :=
decidable.by_cases
  (assume H : leading_coeff p = 0, by rw [H, leading_coeff_eq_zero.1 H, zero_mul, leading_coeff_zero])
  (assume H : leading_coeff p ≠ 0,
    by rw [leading_coeff_mul', leading_coeff_X_pow, mul_one];
       rwa [leading_coeff_X_pow, mul_one])

end

variables (R : Type u) [comm_ring R] [decidable_eq R]

/-- The `R`-submodule of `R[X]` consisting of polynomials of degree ≤ `n`. -/
def degree_le (n : with_bot ℕ) :
  submodule R (polynomial R) :=
⨅ k : ℕ, ⨅ h : ↑k > n, (lcoeff R k).ker

variable {R}

theorem mem_degree_le {n : with_bot ℕ} {f : polynomial R} :
  f ∈ degree_le R n ↔ degree f ≤ n :=
by simp only [degree_le, submodule.mem_infi, degree_le_iff_coeff_zero, linear_map.mem_ker]; refl

theorem degree_le_eq_span_X_pow {n : ℕ} :
  degree_le R n = submodule.span ↑((finset.range (n+1)).image (λ n, X^n) : finset (polynomial R)) :=
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

end polynomial

variables {R : Type u} [comm_ring R] [decidable_eq R]

namespace ideal
open polynomial

variable (I : ideal (polynomial R))

/-- Transport an ideal of `R[X]` to an `R`-submodule of `R[X]`. -/
def of_polynomial : submodule R (polynomial R) :=
{ carrier := (@submodule.carrier (polynomial R) (polynomial R) _ _ ring.to_module I : set (polynomial R)),
  zero := I.zero_mem,
  add := λ _ _, I.add_mem,
  smul := λ c x H, by rw [← C_mul'];
    exact @submodule.smul_mem (polynomial R) (polynomial R) _ _ ring.to_module _ _ _ H }

theorem mem_of_polynomial (x) : x ∈ I.of_polynomial ↔ x ∈ I := iff.rfl

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

theorem is_fg_degree_le (hnr : is_noetherian_ring R) (n : ℕ) :
  submodule.fg (I.degree_le n) :=
is_noetherian_submodule_left.1 (is_noetherian_of_fg_of_noetherian _ hnr
  ⟨_, degree_le_eq_span_X_pow.symm⟩) _

end ideal

/-- Hilbert basis theorem. -/
theorem is_noetherian_ring_polynomial (hnr : is_noetherian_ring R) : is_noetherian_ring (polynomial R) :=
assume I : ideal (polynomial R),
let L := I.leading_coeff in
let M := well_founded.min (is_noetherian_iff_well_founded.1 hnr)
  (set.range I.leading_coeff_nth) (set.ne_empty_of_mem ⟨0, rfl⟩) in
have hm : M ∈ set.range I.leading_coeff_nth := well_founded.min_mem _ _ _,
let ⟨N, HN⟩ := hm, ⟨s, hs⟩ := I.is_fg_degree_le hnr N in
have hm2 : ∀ k, I.leading_coeff_nth k ≤ M := λ k, or.cases_on (le_or_lt k N)
  (λ h, HN ▸ I.leading_coeff_nth_mono h)
  (λ h x hx, classical.by_contradiction $ λ hxm,
    have ¬M < I.leading_coeff_nth k, by refine well_founded.not_lt_min
      (is_noetherian_iff_well_founded.1 hnr) _ _ _; exact ⟨k, rfl⟩,
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
end⟩

namespace mv_polynomial

section semiring

variables {σ : Type u} {τ : Type v} {α : Type w} [comm_semiring α]
variables [decidable_eq σ] [decidable_eq τ] [decidable_eq α]

def equiv_of_equiv (e : σ ≃ τ) : mv_polynomial σ α ≃ mv_polynomial τ α :=
{ to_fun := eval₂ C (X ∘ e),
  inv_fun := eval₂ C (X ∘ e.symm),
  left_inv := λ f, induction_on f
    (λ r, by rw [eval₂_C, eval₂_C])
    (λ p q hp hq, by rw [eval₂_add, eval₂_add, hp, hq])
    (λ p s hp, by simp only [eval₂_mul, eval₂_X, hp, (∘), equiv.inverse_apply_apply]),
  right_inv := λ f, induction_on f
    (λ r, by rw [eval₂_C, eval₂_C])
    (λ p q hp hq, by rw [eval₂_add, eval₂_add, hp, hq])
    (λ p s hp, by simp only [eval₂_mul, eval₂_X, hp, (∘), equiv.apply_inverse_apply]) }

def option_equiv : mv_polynomial (option σ) α ≃ polynomial (mv_polynomial σ α) :=
{ to_fun := eval₂ (polynomial.C ∘ C) (λ x, option.rec_on x polynomial.X (polynomial.C ∘ X)),
  inv_fun := polynomial.eval₂ (eval₂ C (X ∘ some)) (X none),
  left_inv := λ f, induction_on f
    (λ r, by simp only [eval₂_C, polynomial.eval₂_C])
    (λ p q hp hq, by rw [eval₂_add, polynomial.eval₂_add, hp, hq])
    (λ p n h, by simp only [eval₂_mul, eval₂_X, polynomial.eval₂_mul, h];
      cases n; simp only [polynomial.eval₂_X, polynomial.eval₂_C, eval₂_X]),
  right_inv := λ f, polynomial.induction_on f
    (λ g, induction_on g
      (λ r, by rw [polynomial.eval₂_C, eval₂_C, eval₂_C])
      (λ p q hp hq, by rw [polynomial.C_add, polynomial.eval₂_add, eval₂_add, hp, hq])
      (λ p n h, by simp only [polynomial.C_mul, polynomial.eval₂_mul, eval₂_mul, h];
        rw [polynomial.eval₂_C, eval₂_X, eval₂_X]))
    (λ p q hp hq, by rw [polynomial.eval₂_add, eval₂_add, hp, hq])
    (λ n g h, by rw [pow_add, ← mul_assoc]; simp only [polynomial.eval₂_mul];
      rw [eval₂_mul, ← h]; simp only [polynomial.eval₂_mul, polynomial.eval₂_C, polynomial.eval₂_X,
        eval₂_mul, eval₂_C, eval₂_X, pow_one]) }

def pempty_equiv : mv_polynomial pempty α ≃ α :=
{ to_fun := eval₂ id pempty.elim,
  inv_fun := C,
  left_inv := λ f, induction_on f (λ r, by rw [eval₂_C, id])
    (λ p q hp hq, by rw [eval₂_add, C_add, hp, hq]) (λ g n, pempty.elim n),
  right_inv := λ r, eval₂_C _ _ _ }

end semiring

section ring

variables {σ : Type u} {τ : Type v} {α : Type w} [comm_ring α]
variables [decidable_eq σ] [decidable_eq τ] [decidable_eq α]

def ring_equiv_of_equiv (e : σ ≃ τ) : mv_polynomial σ α ≃r mv_polynomial τ α :=
/-{ hom := eval₂.is_ring_hom _ _, .. equiv_of_equiv e }-/
/-ring_equiv.mk (equiv_of_equiv e) (eval₂.is_ring_hom _ _)-/
@ring_equiv.mk (@mv_polynomial σ α (@comm_ring.to_comm_semiring α _inst_3))
    (@mv_polynomial τ α (@comm_ring.to_comm_semiring α _inst_3))
    (@mv_polynomial.ring α σ _inst_4 _inst_6 _inst_3)
    (@mv_polynomial.ring α τ _inst_5 _inst_6 _inst_3)
    (@mv_polynomial.equiv_of_equiv σ τ α (@comm_ring.to_comm_semiring α _inst_3) _inst_4 _inst_5 _inst_6 e)
    (@mv_polynomial.eval₂.is_ring_hom α (@mv_polynomial τ α (@comm_ring.to_comm_semiring α _inst_3)) σ
      _inst_4
      _inst_6
      _inst_3
      (λ (a b : @mv_polynomial τ α (@comm_ring.to_comm_semiring α _inst_3)),
        @mv_polynomial.decidable_eq α τ _inst_5 _inst_6
          (@comm_ring.to_comm_semiring α _inst_3)
          a
          b)
      (@mv_polynomial.comm_ring α τ _inst_5 _inst_6 _inst_3)
      (λ (a : α),
        @mv_polynomial.C α τ _inst_5
          _inst_6
          (@comm_ring.to_comm_semiring α _inst_3)
          a)
      (@mv_polynomial.C.is_ring_hom α τ _inst_5
        _inst_6
        _inst_3)
      (λ (n : σ),
        @function.comp σ τ (@mv_polynomial τ α (@comm_ring.to_comm_semiring α _inst_3))
          (@mv_polynomial.X α τ _inst_5
              _inst_6
              (@comm_ring.to_comm_semiring α _inst_3))
          (@coe_fn (equiv σ τ) (@equiv.has_coe_to_fun σ τ) e)
          n))

-- It still takes 16 seconds to elaborate
def option_ring_equiv : mv_polynomial (option σ) α ≃r polynomial (mv_polynomial σ α) :=
/-{ hom := eval₂.is_ring_hom _ _, .. option_equiv }-/
  @ring_equiv.mk
    (@mv_polynomial (option σ) α (@comm_ring.to_comm_semiring α _inst_3))
    (@polynomial (@mv_polynomial σ α (@comm_ring.to_comm_semiring α _inst_3))
       (@comm_ring.to_comm_semiring (@mv_polynomial σ α (@comm_ring.to_comm_semiring α _inst_3)) (@mv_polynomial.comm_ring α σ _inst_4 _inst_6 _inst_3)))
    (@mv_polynomial.ring α (option σ) (@option.decidable_eq σ _inst_4) _inst_6 _inst_3)
    (@comm_ring.to_ring
       (@polynomial (@mv_polynomial σ α (@comm_ring.to_comm_semiring α _inst_3))
          (@comm_ring.to_comm_semiring (@mv_polynomial σ α (@comm_ring.to_comm_semiring α _inst_3)) (@mv_polynomial.comm_ring α σ _inst_4 _inst_6 _inst_3)))
       (@polynomial.comm_ring (@mv_polynomial σ α (@comm_ring.to_comm_semiring α _inst_3))
          (@mv_polynomial.decidable_eq α σ _inst_4 _inst_6
            (@comm_ring.to_comm_semiring α _inst_3))
          (@mv_polynomial.comm_ring α σ _inst_4 _inst_6 _inst_3)))
    (@mv_polynomial.option_equiv σ α (@comm_ring.to_comm_semiring α _inst_3) _inst_4
       _inst_6)
(  @mv_polynomial.eval₂.is_ring_hom α
    (@polynomial (@mv_polynomial σ α (@comm_ring.to_comm_semiring α _inst_3))
       (@comm_ring.to_comm_semiring (@mv_polynomial σ α (@comm_ring.to_comm_semiring α _inst_3)) (@mv_polynomial.comm_ring α σ _inst_4 _inst_6 _inst_3)))
    (option σ)
    (@option.decidable_eq σ _inst_4)
    _inst_6
    _inst_3
    (@polynomial.decidable_eq (@mv_polynomial σ α (@comm_ring.to_comm_semiring α _inst_3))
      (@mv_polynomial.decidable_eq α σ _inst_4 _inst_6
        (@comm_ring.to_comm_semiring α _inst_3))
      (@comm_ring.to_comm_semiring (@mv_polynomial σ α (@comm_ring.to_comm_semiring α _inst_3)) (@mv_polynomial.comm_ring α σ _inst_4 _inst_6 _inst_3)))
    (@polynomial.comm_ring (@mv_polynomial σ α (@comm_ring.to_comm_semiring α _inst_3))
       (@mv_polynomial.decidable_eq α σ _inst_4 _inst_6
          (@comm_ring.to_comm_semiring α _inst_3))
       (@mv_polynomial.comm_ring α σ _inst_4 _inst_6 _inst_3))
    (@function.comp α (@mv_polynomial σ α (@comm_ring.to_comm_semiring α _inst_3))
       (@polynomial (@mv_polynomial σ α (@comm_ring.to_comm_semiring α _inst_3))
          (@comm_ring.to_comm_semiring (@mv_polynomial σ α (@comm_ring.to_comm_semiring α _inst_3)) (@mv_polynomial.comm_ring α σ _inst_4 _inst_6 _inst_3)))
       (@polynomial.C (@mv_polynomial σ α (@comm_ring.to_comm_semiring α _inst_3))
          (@mv_polynomial.decidable_eq α σ _inst_4
             _inst_6
             (@comm_ring.to_comm_semiring α _inst_3))
          (@comm_ring.to_comm_semiring (@mv_polynomial σ α (@comm_ring.to_comm_semiring α _inst_3)) (@mv_polynomial.comm_ring α σ _inst_4 _inst_6 _inst_3)))
       (@mv_polynomial.C α σ _inst_4
          _inst_6
          (@comm_ring.to_comm_semiring α _inst_3)))
    (@is_ring_hom.comp α (@mv_polynomial σ α (@comm_ring.to_comm_semiring α _inst_3))
       (@comm_ring.to_ring α _inst_3)
       (@mv_polynomial.ring α σ _inst_4 _inst_6 _inst_3)
       (@mv_polynomial.C α σ _inst_4
          _inst_6
          (@comm_ring.to_comm_semiring α _inst_3))
       (@mv_polynomial.C.is_ring_hom α σ _inst_4
          _inst_6
          _inst_3)
       (@polynomial (@mv_polynomial σ α (@comm_ring.to_comm_semiring α _inst_3))
          (@comm_ring.to_comm_semiring (@mv_polynomial σ α (@comm_ring.to_comm_semiring α _inst_3)) (@mv_polynomial.comm_ring α σ _inst_4 _inst_6 _inst_3)))
       (@comm_ring.to_ring
          (@polynomial (@mv_polynomial σ α (@comm_ring.to_comm_semiring α _inst_3))
             (@comm_ring.to_comm_semiring (@mv_polynomial σ α (@comm_ring.to_comm_semiring α _inst_3)) (@mv_polynomial.comm_ring α σ _inst_4 _inst_6 _inst_3)))
          (@polynomial.comm_ring (@mv_polynomial σ α (@comm_ring.to_comm_semiring α _inst_3))
             (@mv_polynomial.decidable_eq α σ _inst_4 _inst_6
                (@comm_ring.to_comm_semiring α _inst_3))
             (@mv_polynomial.comm_ring α σ _inst_4 _inst_6 _inst_3)))
       (@polynomial.C (@mv_polynomial σ α (@comm_ring.to_comm_semiring α _inst_3))
          (@mv_polynomial.decidable_eq α σ _inst_4
             _inst_6
             (@comm_ring.to_comm_semiring α _inst_3))
          (@comm_ring.to_comm_semiring (@mv_polynomial σ α (@comm_ring.to_comm_semiring α _inst_3)) (@mv_polynomial.comm_ring α σ _inst_4 _inst_6 _inst_3)))
       (@polynomial.C.is_ring_hom (@mv_polynomial σ α (@comm_ring.to_comm_semiring α _inst_3))
          (@mv_polynomial.decidable_eq α σ _inst_4
             _inst_6
             (@comm_ring.to_comm_semiring α _inst_3))
          (@mv_polynomial.comm_ring α σ _inst_4 _inst_6 _inst_3)))
    (λ (n : option σ),
       (λ (x : option σ),
          @option.rec_on σ
            (λ (_x : option σ),
               @polynomial (@mv_polynomial σ α (@comm_ring.to_comm_semiring α _inst_3))
                 (@comm_ring.to_comm_semiring (@mv_polynomial σ α (@comm_ring.to_comm_semiring α _inst_3)) (@mv_polynomial.comm_ring α σ _inst_4 _inst_6 _inst_3)))
            x
            (@polynomial.X (@mv_polynomial σ α (@comm_ring.to_comm_semiring α _inst_3))
               (@mv_polynomial.decidable_eq α σ _inst_4
                  _inst_6
                  (@comm_ring.to_comm_semiring α _inst_3))
               (@comm_ring.to_comm_semiring (@mv_polynomial σ α (@comm_ring.to_comm_semiring α _inst_3)) (@mv_polynomial.comm_ring α σ _inst_4 _inst_6 _inst_3)))
            (@function.comp σ (@mv_polynomial σ α (@comm_ring.to_comm_semiring α _inst_3))
               (@polynomial (@mv_polynomial σ α (@comm_ring.to_comm_semiring α _inst_3))
                  (@comm_ring.to_comm_semiring (@mv_polynomial σ α (@comm_ring.to_comm_semiring α _inst_3)) (@mv_polynomial.comm_ring α σ _inst_4 _inst_6 _inst_3)))
               (@polynomial.C (@mv_polynomial σ α (@comm_ring.to_comm_semiring α _inst_3))
                  (@mv_polynomial.decidable_eq α σ _inst_4
                     _inst_6
                     (@comm_ring.to_comm_semiring α _inst_3))
                  (@comm_ring.to_comm_semiring (@mv_polynomial σ α (@comm_ring.to_comm_semiring α _inst_3)) (@mv_polynomial.comm_ring α σ _inst_4 _inst_6 _inst_3)))
               (@mv_polynomial.X α σ _inst_4
                  _inst_6
                  (@comm_ring.to_comm_semiring α _inst_3))))
         n))

def pempty_ring_equiv : mv_polynomial pempty α ≃r α :=
{ hom := eval₂.is_ring_hom _ _, .. pempty_equiv }

end ring

end mv_polynomial

theorem is_noetherian_ring_mv_polynomial_fin {n : ℕ}
  (hnr : is_noetherian_ring R) : is_noetherian_ring (mv_polynomial (fin n) R) :=
begin
  induction n with n ih,
  { exact is_noetherian_ring_of_ring_equiv R
      (mv_polynomial.pempty_ring_equiv.symm.trans $ mv_polynomial.ring_equiv_of_equiv
        ⟨pempty.elim, fin.elim0, λ x, pempty.elim x, λ x, fin.elim0 x⟩) hnr },
  exact is_noetherian_ring_of_ring_equiv (polynomial (mv_polynomial (fin n) R))
    (mv_polynomial.option_ring_equiv.symm.trans (mv_polynomial.ring_equiv_of_equiv
      ⟨λ x, option.rec_on x 0 fin.succ, λ x, fin.cases none some x,
      by rintro ⟨none | x⟩; [refl, exact fin.cases_succ _],
      λ x, fin.cases rfl (λ i, show (option.rec_on (fin.cases none some (fin.succ i) : option (fin n))
        0 fin.succ : fin n.succ) = _, by rw fin.cases_succ) x⟩))
    (is_noetherian_ring_polynomial ih)
end

theorem is_noetherian_ring_mv_polynomial_of_fintype {σ : Type v} [fintype σ] [decidable_eq σ]
  (hnr : is_noetherian_ring R) : is_noetherian_ring (mv_polynomial σ R) :=
trunc.induction_on (fintype.equiv_fin σ) $ λ e,
is_noetherian_ring_of_ring_equiv (mv_polynomial (fin (fintype.card σ)) R)
  (mv_polynomial.ring_equiv_of_equiv e.symm)
  (is_noetherian_ring_mv_polynomial_fin hnr)

theorem is_noetherian_ring_of_fg_of_is_noetherian_ring
  (S : set R) [is_subring S] (σ : set R) (hfσ : set.finite σ)
  (hσ : ring.closure (S ∪ σ) = set.univ)
  (hs : @is_noetherian_ring S (comm_ring.to_ring S)) : is_noetherian_ring R :=
begin
  haveI := set.finite.fintype hfσ, haveI := classical.dec_eq σ,
  haveI := classical.dec_eq S,
  refine is_noetherian_ring_of_surjective (mv_polynomial σ S) R
    (mv_polynomial.eval₂ subtype.val subtype.val) _ _
    (is_noetherian_ring_mv_polynomial_of_fintype hs),
  { exact @mv_polynomial.eval₂.is_ring_hom S R σ _inst_4 _inst_5
      subset.comm_ring _inst_2 _inst_1 subtype.val
      is_ring_hom.is_ring_hom subtype.val },
  { intro r, have hr := set.eq_univ_iff_forall.1 hσ r,
    rcases ring.exists_list_of_mem_closure hr with ⟨L, hl1, hl2⟩,
    induction L with hd tl ih generalizing r,
    { rw [list.map, list.sum_nil] at hl2,
      refine ⟨0, hl2 ▸ mv_polynomial.eval₂_zero _ _⟩ },
    rw list.forall_mem_cons at hl1,
    cases ih hl1.2 _ (set.eq_univ_iff_forall.1 hσ _) rfl with f hf,
    subst hl2, rw [list.map_cons, list.sum_cons, ← hf],
    replace hl1 := hl1.1, clear hr hf ih tl,
    suffices : ∃ (a : mv_polynomial ↥σ S),
      mv_polynomial.eval₂ subtype.val subtype.val a = list.prod hd,
    { cases this with g hg, refine ⟨g + f, _⟩,
      rw @mv_polynomial.eval₂_add S R σ _inst_4 _inst_5 comm_ring.to_comm_semiring
        g f comm_ring.to_comm_semiring subtype.val subtype.val
        (@@is_ring_hom.is_semiring_hom _ _ _ is_ring_hom.is_ring_hom),
      rw hg },
    induction hd with hd tl ih,
    { refine ⟨1, _⟩,
      rw @mv_polynomial.eval₂_one S R σ _inst_4 _inst_5 comm_ring.to_comm_semiring
        comm_ring.to_comm_semiring subtype.val subtype.val
        (@@is_ring_hom.is_semiring_hom _ _ _ is_ring_hom.is_ring_hom),
      rw list.prod_nil },
    rw list.forall_mem_cons at hl1,
    cases ih hl1.2 with g hg,
    rw [list.prod_cons, ← hg],
    rcases hl1.1 with h | h | h,
    { cases h with h h,
      { refine ⟨mv_polynomial.C ⟨hd, h⟩ * g, _⟩,
        rw @mv_polynomial.eval₂_mul S R σ _inst_4 _inst_5 comm_ring.to_comm_semiring
          g comm_ring.to_comm_semiring subtype.val subtype.val
          (@@is_ring_hom.is_semiring_hom _ _ _ is_ring_hom.is_ring_hom),
        rw @mv_polynomial.eval₂_C S R σ _inst_4 _inst_5 comm_ring.to_comm_semiring
          comm_ring.to_comm_semiring subtype.val subtype.val
          (@@is_ring_hom.is_semiring_hom _ _ _ is_ring_hom.is_ring_hom) },
      refine ⟨mv_polynomial.X ⟨hd, h⟩ * g, _⟩,
      rw @mv_polynomial.eval₂_mul S R σ _inst_4 _inst_5 comm_ring.to_comm_semiring
        g comm_ring.to_comm_semiring subtype.val subtype.val
        (@@is_ring_hom.is_semiring_hom _ _ _ is_ring_hom.is_ring_hom),
      rw @mv_polynomial.eval₂_X S R σ _inst_4 _inst_5 comm_ring.to_comm_semiring
        comm_ring.to_comm_semiring subtype.val subtype.val
        (@@is_ring_hom.is_semiring_hom _ _ _ is_ring_hom.is_ring_hom) },
    { cases h with h h,
      { refine ⟨-mv_polynomial.C ⟨-hd, h⟩ * g, _⟩,
        rw @mv_polynomial.eval₂_mul S R σ _inst_4 _inst_5 comm_ring.to_comm_semiring
          g comm_ring.to_comm_semiring subtype.val subtype.val
          (@@is_ring_hom.is_semiring_hom _ _ _ is_ring_hom.is_ring_hom),
        rw @mv_polynomial.eval₂_neg S R σ _inst_4 _inst_5 subset.comm_ring
          _ _inst_2 _inst_1 subtype.val
          is_ring_hom.is_ring_hom subtype.val,
        rw @mv_polynomial.eval₂_C S R σ _inst_4 _inst_5 comm_ring.to_comm_semiring
          comm_ring.to_comm_semiring subtype.val subtype.val
          (@@is_ring_hom.is_semiring_hom _ _ _ is_ring_hom.is_ring_hom),
        rw neg_neg },
      refine ⟨-mv_polynomial.X ⟨-hd, h⟩ * g, _⟩,
      rw @mv_polynomial.eval₂_mul S R σ _inst_4 _inst_5 comm_ring.to_comm_semiring
        g comm_ring.to_comm_semiring subtype.val subtype.val
        (@@is_ring_hom.is_semiring_hom _ _ _ is_ring_hom.is_ring_hom),
      rw @mv_polynomial.eval₂_neg S R σ _inst_4 _inst_5 subset.comm_ring
        _ _inst_2 _inst_1 subtype.val
        is_ring_hom.is_ring_hom subtype.val,
      rw @mv_polynomial.eval₂_X S R σ _inst_4 _inst_5 comm_ring.to_comm_semiring
        comm_ring.to_comm_semiring subtype.val subtype.val
        (@@is_ring_hom.is_semiring_hom _ _ _ is_ring_hom.is_ring_hom),
      rw neg_neg },
    { refine ⟨-g, _⟩,
      rw @mv_polynomial.eval₂_neg S R σ _inst_4 _inst_5 subset.comm_ring
        _ _inst_2 _inst_1 subtype.val
        is_ring_hom.is_ring_hom subtype.val,
      rw [h, neg_one_mul] } }
end

instance int.cast.is_ring_hom {R : Type u} [ring R] :
  is_ring_hom (int.cast : ℤ → R) :=
⟨int.cast_one, int.cast_mul, int.cast_add⟩

instance set.range.is_subring {R : Type u} {S : Type v} [ring R] [ring S]
  (f : R → S) [is_ring_hom f] : is_subring (set.range f) :=
{ zero_mem := ⟨0, is_ring_hom.map_zero f⟩,
  one_mem := ⟨1, is_ring_hom.map_one f⟩,
  neg_mem := λ x ⟨p, hp⟩, ⟨-p, hp ▸ is_ring_hom.map_neg f⟩,
  add_mem := λ x y ⟨p, hp⟩ ⟨q, hq⟩, ⟨p + q, hp ▸ hq ▸ is_ring_hom.map_add f⟩,
  mul_mem := λ x y ⟨p, hp⟩ ⟨q, hq⟩, ⟨p * q, hp ▸ hq ▸ is_ring_hom.map_mul f⟩, }

theorem is_noetherian_ring_of_fg (σ : set R) (hfσ : set.finite σ)
  (hσ : ring.closure σ = set.univ) : is_noetherian_ring R :=
@is_noetherian_ring_of_fg_of_is_noetherian_ring R _ _ (set.range int.cast)
  (set.range.is_subring _) σ hfσ
  (set.eq_univ_of_univ_subset $ hσ ▸ (ring.closure_subset $
    set.subset.trans (set.subset_union_right _ _) ring.subset_closure))
  (is_noetherian_ring_of_surjective ℤ (set.range (int.cast : ℤ → R))
    (λ i, ⟨i, i, rfl⟩) ⟨subtype.eq int.cast_one, λ _ _, subtype.eq (int.cast_mul _ _),
      λ _ _, subtype.eq (int.cast_add _ _)⟩
    (λ ⟨r, i, rfl⟩, ⟨i, subtype.eq rfl⟩)
    principal_ideal_domain.is_noetherian_ring)

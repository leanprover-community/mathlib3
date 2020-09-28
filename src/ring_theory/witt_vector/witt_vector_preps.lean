-- this should all be moved

-- import algebra.inj_surj
import data.nat.choose
import data.int.gcd
import data.mv_polynomial.comap
import data.mv_polynomial.monad
import data.zmod.basic
import data.fintype.card
import data.finset.lattice
import data.set.disjointed
import ring_theory.multiplicity
import algebra.invertible
import number_theory.basic
import group_theory.order_of_element
import field_theory.finite.basic
import field_theory.mv_polynomial
import data.mv_polynomial.expand
import data.mv_polynomial.counit

universes u v w u₁

-- ### FOR_MATHLIB

open_locale big_operators

namespace mv_polynomial
open finsupp

variables (σ R A : Type*) [comm_semiring R] [comm_semiring A]

open_locale big_operators

end mv_polynomial

namespace mv_polynomial
variables {σ : Type*} {τ : Type*} {υ : Type*} {R : Type*} [comm_semiring R]

section monadic_stuff

open_locale classical
variables (φ : mv_polynomial σ R) (f : σ → mv_polynomial τ R)

lemma bind₁_vars : (bind₁ f φ).vars ⊆ φ.vars.bind (λ i, (f i).vars) :=
begin
  -- can we prove this using the `mono` tactic?
  -- are the lemmas above good `mono` lemmas?
  -- is `bind_mono` a good `mono` lemma?
  -- Rob: I've never used mono, so I'm not really sure...
  calc (bind₁ f φ).vars
      = (φ.support.sum (λ (x : σ →₀ ℕ), (bind₁ f) (monomial x (coeff x φ)))).vars : by { rw [← alg_hom.map_sum, ← φ.as_sum], }
  ... ≤ φ.support.bind (λ (i : σ →₀ ℕ), ((bind₁ f) (monomial i (coeff i φ))).vars) : vars_sum_subset _ _
  ... = φ.support.bind (λ (d : σ →₀ ℕ), (C (coeff d φ) * ∏ i in d.support, f i ^ d i).vars) : by simp only [bind₁_monomial]
  ... ≤ φ.support.bind (λ (d : σ →₀ ℕ), d.support.bind (λ i, (f i).vars)) : _ -- proof below
  ... ≤ φ.vars.bind (λ (i : σ), (f i).vars) : _, -- proof below
  { apply finset.bind_mono,
    intros d hd,
    calc (C (coeff d φ) * ∏ (i : σ) in d.support, f i ^ d i).vars
        ≤ (C (coeff d φ)).vars ∪ (∏ (i : σ) in d.support, f i ^ d i).vars : vars_mul _ _
    ... ≤ (∏ (i : σ) in d.support, f i ^ d i).vars : by { simp only [finset.empty_union, vars_C, finset.le_iff_subset, finset.subset.refl], }
    ... ≤ d.support.bind (λ (i : σ), (f i ^ d i).vars) : vars_prod _
    ... ≤ d.support.bind (λ (i : σ), (f i).vars) : _,
    apply finset.bind_mono,
    intros i hi,
    apply vars_pow, },
  { -- can this be golfed into a point-free proof?
    intro j,
    rw [finset.mem_bind],
    rintro ⟨d, hd, hj⟩,
    rw [finset.mem_bind] at hj,
    rcases hj with ⟨i, hi, hj⟩,
    rw [finset.mem_bind],
    refine ⟨i, _, hj⟩,
    rw [mem_vars],
    exact ⟨d, hd, hi⟩, }
end


end monadic_stuff



section rename
open function


end rename

section move_this

-- move this
variables (σ) (R)

end move_this

end mv_polynomial


namespace finset

variables {α : Type*} [fintype α]

end finset

namespace function
variables {α β : Type*}
open set

lemma injective_of_inj_on (f : α → β) (hf : inj_on f univ) : injective f :=
λ x y h, hf (mem_univ x) (mem_univ y) h

lemma surjective_of_surj_on (f : α → β) (hf : surj_on f univ univ) : surjective f :=
begin
  intro b,
  rcases hf (mem_univ b) with ⟨a, -, ha⟩,
  exact ⟨a, ha⟩
end

end function

namespace fintype
variables {α β : Type*} [fintype α] [fintype β]
open function finset



end fintype

section isos_to_zmod
variables (R : Type*) (n : ℕ) [comm_ring R]

lemma zmod.cast_hom_inj [char_p R n] :
  function.injective (zmod.cast_hom (show n ∣ n, by refl) R) :=
begin
  rw ring_hom.injective_iff,
  intro x,
  obtain ⟨k, rfl⟩ := zmod.int_cast_surjective x,
  rw [ring_hom.map_int_cast,
      char_p.int_cast_eq_zero_iff R n, char_p.int_cast_eq_zero_iff (zmod n) n],
  exact id,
end

lemma zmod.cast_hom_bij [fintype R] [char_p R n] (hn : fintype.card R = n) :
  function.bijective (zmod.cast_hom (show n ∣ n, by refl) R) :=
begin
  haveI : fact (0 < n) :=
  begin
    classical, by_contra H,
    erw [nat.pos_iff_ne_zero, not_not] at H,
    unfreezingI { subst H, },
    rw fintype.card_eq_zero_iff at hn,
    exact hn 0
  end,
  rw [fintype.bijective_iff_injective_and_card, zmod.card, hn, eq_self_iff_true, and_true],
  apply zmod.cast_hom_inj,
end

lemma ring_equiv.coe_ring_hom_inj {R S : Type*} [semiring R] [semiring S] (f g : R ≃+* S) :
  f = g ↔ (f : R →+* S) = g :=
begin
  refine ⟨congr_arg _, _⟩,
  rw ring_hom.ext_iff,
  intro h, ext, apply h,
end

instance zmod.ring_equiv_subsingleton : subsingleton (zmod n ≃+* R) :=
⟨λ f g, by { rw ring_equiv.coe_ring_hom_inj, apply ring_hom.ext_zmod _ _ }⟩

lemma cast_card_eq_zero [fintype R] : (fintype.card R : R) = 0 :=
begin
  have : fintype.card R •ℕ (1 : R) = 0 :=
    @pow_card_eq_one (multiplicative R) _ _ (multiplicative.of_add 1),
  simpa only [mul_one, nsmul_eq_mul]
end


lemma char_p_of_prime_pow_ne_zero [fintype R] (p : ℕ) [hp : fact p.prime] (n : ℕ) (hn : fintype.card R = p ^ n)
  (hR : ∀ i ≤ n, (p ^ i : R) = 0 → i = n) :
  char_p R (p ^ n) :=
begin
  obtain ⟨c, hc⟩ := char_p.exists R, resetI,
  have hcpn : c ∣ p ^ n,
  { rw [← char_p.cast_eq_zero_iff R c, ← hn, cast_card_eq_zero], },
  obtain ⟨i, hi, hc⟩ : ∃ i ≤ n, c = p ^ i, by rwa nat.dvd_prime_pow hp at hcpn,
  obtain rfl : i = n,
  { apply hR i hi, rw [← nat.cast_pow, ← hc, char_p.cast_eq_zero] },
  rwa ← hc,
end

end isos_to_zmod

section
-- move this
lemma prod_mk_injective {α β : Type*} (a : α) :
  function.injective (prod.mk a : β → α × β) :=
by { intros b₁ b₂ h, simpa only [true_and, prod.mk.inj_iff, eq_self_iff_true] using h }
end

-- TODO: making this a global instance causes timeouts in the comm_ring instance for Witt vectors
-- :scream: :scream: :scream:
/-- A natural number that is invertible when coerced to `ℚ` is also invertible
when coerced to any `ℚ`-algebra. -/
def invertible_rat_algebra_coe_nat (R : Type*) (p : ℕ)
  [semiring R] [algebra ℚ R] [invertible (p : ℚ)] :
  invertible (p : R) :=
invertible.copy (invertible.map (algebra_map ℚ R : ℚ →* R) p) p
  (by simp only [ring_hom.map_nat_cast, coe_monoid_hom])

namespace mv_polynomial
noncomputable instance invertible_C
  (σ : Type*) {R : Type*} [comm_semiring R] (r : R) [invertible r] :
  invertible (C r : mv_polynomial σ R) :=
invertible.map ⟨C, C_1, λ x y, C_mul⟩ _

/-- A natural number that is invertible when coerced to `ℚ` is also invertible
when coerced to any polynomial ring with rational coefficients.

Short-cut for typeclass resolution. -/
noncomputable instance invertible_rat_coe_nat (σ : Type*) (p : ℕ) [invertible (p : ℚ)] :
  invertible (p : mv_polynomial σ ℚ) :=
invertible_rat_algebra_coe_nat _ _

section
open function

variables (A B R : Type*) [comm_semiring A] [comm_semiring B] [comm_ring R] [algebra A B]

end
end mv_polynomial

lemma nontrivial_of_char_ne_one {v : ℕ} (hv : v ≠ 1) {R : Type*} [semiring R] [hr : char_p R v] :
  nontrivial R :=
⟨⟨(1 : ℕ), 0, λ h, hv $ by rwa [char_p.cast_eq_zero_iff _ v, nat.dvd_one] at h; assumption ⟩⟩

section zmod
open mv_polynomial
variables {p : ℕ} {σ : Type*}


end zmod
-- ### end FOR_MATHLIB

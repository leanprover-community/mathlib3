import linear_algebra.finite_dimensional
import order.zorn
import ring_theory.algebraic
import ring_theory.fractional_ideal
import ring_theory.coprime
import ring_theory.integral_closure
import ring_theory.localization
import ring_theory.noetherian
import set_theory.cardinal
import tactic

/-- A ring `R` is (at most) one-dimensional if all nonzero prime ideals are maximal. -/
def ring.is_one_dimensional (R : Type*) [comm_ring R] :=
∀ p ≠ (⊥ : ideal R), p.is_prime → p.is_maximal

open ring

lemma principal_ideal_ring.is_one_dimensional (R : Type*) [integral_domain R]
  [is_principal_ideal_ring R] :
  ring.is_one_dimensional R :=
λ p nonzero prime, by { haveI := prime, exact ideal.is_prime.to_maximal_ideal nonzero }

variables {R K : Type*}

-- TODO: `class is_dedekind_domain`?
structure is_dedekind_domain [comm_ring R] [comm_ring K] (f : fraction_map R K) :=
(is_one_dimensional : is_one_dimensional R)
(is_noetherian_ring : is_noetherian_ring R)
(is_integrally_closed : integral_closure R f.codomain = ⊥)

lemma integrally_closed_iff_integral_implies_integer
  [comm_ring R] [comm_ring K] {f : fraction_map R K} :
  integral_closure R f.codomain = ⊥ ↔ ∀ x : f.codomain, is_integral R x → f.is_integer x :=
subalgebra.ext_iff.trans
  ⟨ λ h x hx, algebra.mem_bot.mp ((h x).mp hx),
    λ h x, iff.trans
      ⟨λ hx, h x hx, λ ⟨y, hy⟩, hy ▸ is_integral_algebra_map⟩
      (@algebra.mem_bot R f.codomain _ _ _ _).symm⟩

namespace unique_factorization_domain

variables [integral_domain R] [unique_factorization_domain R] [field K] {f : fraction_map R K}

-- TODO: might need nonzero or similar assumptions
lemma exists_reduced_factors (a b : R) :
  ∃ a' b' c', (∀ {p}, p ∣ a' → p ∣ b' → is_unit p) ∧ a' * c' = a ∧ b' * c' = b :=
sorry

lemma mul_mem_non_zero_divisors {a b : R} : a * b ∈ non_zero_divisors R ↔ a ∈ non_zero_divisors R ∧ b ∈ non_zero_divisors R :=
begin
split,
intro h, split,
      intros x ha,
      have hab : x*(a*b)=0,
        calc x*(a*b) = (x*a)*b : by ring
         ... = 0*b : by rw ha
        ...  = 0 : by ring,
apply h, exact hab,
      intros x hb,
      have hab : x*(a*b)=0,
        calc x*(a*b) = (x*b)*a : by ring
         ... = 0*a : by rw hb
        ...  = 0 : by ring,
apply h, exact hab,
intro h,cases h with ha hb, intros x hx,
have hab: a*b*x=0, rw [mul_comm], exact hx,
apply ha,
have hba: b*x*a=0, rw [mul_comm,← mul_assoc], exact hab,
apply hb, rw [mul_assoc,hx],
end

lemma integrally_closed : integral_closure R f.codomain = ⊥ :=
begin
  apply integrally_closed_iff_integral_implies_integer.mpr,
  rintros x ⟨p, hp, px⟩,
  obtain ⟨⟨b, b_nonzero⟩, a, hab⟩ := f.exists_integer_multiple x,
  rw subtype.coe_mk at hab,
  obtain ⟨a', b', c', coprime, rfl, rfl⟩ := exists_reduced_factors a b,
  obtain ⟨b'_nonzero, c'_nonzero⟩ := mul_mem_non_zero_divisors.mp b_nonzero,
  suffices : b' ∣ a',
  { obtain ⟨⟨b', d', hbd, hdb⟩, rfl⟩ := coprime this (dvd_refl b'),
    rw units.coe_mk at *,
    use d' * a',
    apply eq_of_mul_eq_mul_right_of_ne_zero
      (mt f.to_map_eq_zero_iff.mpr (mem_non_zero_divisors_iff_ne_zero.mp c'_nonzero))_,
    calc f.to_map (d' * a') * f.to_map c'
          = f.to_map d' * f.to_map (a' * c') : by simp [mul_assoc]
      ... = f.to_map d' * (f.to_map (b' * c') * x) :
        by rw hab
      ... = f.to_map (d' * b') * x * f.to_map c' :
        by simp [mul_assoc, mul_comm, mul_left_comm]
      ... = x * f.to_map c' : by rw [hdb, ring_hom.map_one, one_mul] },
  sorry
end

end unique_factorization_domain

-- TODO: instance instead of def?
def principal_ideal_ring.to_dedekind_domain [integral_domain R] [is_principal_ideal_ring R]
  [field K] (f : fraction_map R K) :
  is_dedekind_domain f :=
{ is_one_dimensional := principal_ideal_ring.is_one_dimensional R,
  is_noetherian_ring := principal_ideal_ring.is_noetherian_ring,
  is_integrally_closed := @unique_factorization_domain.integrally_closed R _ _
    (principal_ideal_ring.to_unique_factorization_domain) _ _}

namespace dedekind_domain

variables {S : Type*} [integral_domain R] [integral_domain S] [algebra R S]
variables {L : Type*} [field K] [field L] {f : fraction_map R K}

open finsupp polynomial

instance : integral_domain (integral_closure R S) :=
{ zero_ne_one := mt subtype.ext.mp zero_ne_one,
  eq_zero_or_eq_zero_of_mul_eq_zero := λ ⟨a, ha⟩ ⟨b, hb⟩ h,
    or.imp subtype.ext.mpr subtype.ext.mpr (eq_zero_or_eq_zero_of_mul_eq_zero (subtype.ext.mp h)),
  ..(integral_closure R S).comm_ring R S }

lemma maximal_ideal_invertible_of_dedekind (h : is_dedekind_domain f) {M : ideal R}
(hM : ideal.is_maximal M) : is_unit (M : fractional_ideal f) :=
sorry

lemma fractional_ideal_invertible_of_dedekind (h : is_dedekind_domain f) (I : fractional_ideal f) :
I * I⁻¹ = 1 :=
begin
sorry
end

/-- If `f : polynomial R` is a polynomial with root `z`, `to_monic f` is
a monic polynomial with root `leading_coeff f * z` -/
noncomputable def to_monic {f : polynomial R} (hf : f ≠ 0) : polynomial R :=
on_finset f.support
  (λ i, if i = f.nat_degree then 1 else coeff f i * f.leading_coeff ^ (f.nat_degree - 1 - i))
  begin
    intros i h,
    apply mem_support_iff.mpr,
    split_ifs at h with hi,
    { rw hi,
      exact mt polynomial.leading_coeff_eq_zero.mp hf },
    { exact ne_zero_of_mul_ne_zero_right h },
  end

@[simp] lemma to_monic_coeff_degree {f : polynomial R} (hf : f ≠ 0) :
  (to_monic hf).coeff f.nat_degree = 1 :=
if_pos rfl

@[simp] lemma to_monic_coeff_ne_degree {f : polynomial R} (hf : f ≠ 0)
  {i : ℕ} (hi : i ≠ f.nat_degree) :
  coeff (to_monic hf) i = coeff f i * f.leading_coeff ^ (f.nat_degree - 1 - i) :=
if_neg hi

lemma monic_to_monic {f : polynomial R} (hf : f ≠ 0) : monic (to_monic hf) :=
begin
  apply monic_of_degree_le f.nat_degree,
  { refine finset.sup_le (λ i h, _),
    rw [to_monic, mem_support_iff, on_finset_apply] at h,
    split_ifs at h with hi,
    { rw hi,
      exact le_refl _ },
    { erw [with_bot.some_le_some],
      apply le_nat_degree_of_ne_zero,
      exact ne_zero_of_mul_ne_zero_right h } },
  { exact to_monic_coeff_degree hf }
end

@[simp] lemma support_to_monic {f : polynomial R} (hf : f ≠ 0) : (to_monic hf).support = f.support :=
begin
  ext i,
  simp only [to_monic, on_finset_apply, mem_support_iff],
  split_ifs with hi,
  { simp only [ne.def, not_false_iff, true_iff, one_ne_zero, hi],
    exact λ h, hf (leading_coeff_eq_zero.mp h) },
  split,
  { intro h,
    exact ne_zero_of_mul_ne_zero_right h },
  { intro h,
    refine mul_ne_zero h (pow_ne_zero _ _),
    exact λ h, hf (leading_coeff_eq_zero.mp h) }
end

lemma eq_C_of_nat_degree_le_zero {p : polynomial R} (h : nat_degree p ≤ 0) : p = C (coeff p 0) :=
begin
  refine polynomial.ext (λ n, _),
  cases n,
  { simp },
  { have : nat_degree p < nat.succ n := lt_of_le_of_lt h (nat.succ_pos _),
    rw [coeff_C, if_neg (nat.succ_ne_zero _), coeff_eq_zero_of_nat_degree_lt this] }
end

lemma nat_degree_pos_of_aeval_root {f : polynomial R} (hf : f ≠ 0)
  {z : S} (hz : aeval R S z f = 0) (inj : ∀ (x : R), algebra_map R S x = 0 → x = 0) :
  0 < f.nat_degree :=
lt_of_not_ge $ λ hlt, begin
  have := eq_C_of_nat_degree_le_zero hlt,
  rw [this, aeval_C] at hz,
  have : ∀ n, coeff f n = 0 := λ n, nat.cases_on n (inj _ hz)
    (λ _, coeff_eq_zero_of_nat_degree_lt (lt_of_le_of_lt hlt (nat.succ_pos _))),
  exact hf (finsupp.ext this),
end

lemma to_monic_aeval_eq_zero {f : polynomial R} (hf : f ≠ 0)
  {z : S} (hz : aeval R S z f = 0) (inj : ∀ (x : R), algebra_map R S x = 0 → x = 0) :
  aeval R S (z * algebra_map R S f.leading_coeff) (to_monic hf) = 0 :=
calc aeval R S (z * algebra_map R S f.leading_coeff) (to_monic hf)
    = f.support.attach.sum
        (λ i, algebra_map R S (coeff (to_monic hf) i.1 * f.leading_coeff ^ i.1) * z ^ i.1) :
      by { rw [aeval_def, eval₂, finsupp.sum, support_to_monic],
           simp only [mul_comm z, mul_pow, mul_assoc, ring_hom.map_pow, ring_hom.map_mul],
           exact finset.sum_attach.symm }
... = f.support.attach.sum
        (λ i, algebra_map R S (coeff f i.1 * f.leading_coeff ^ (f.nat_degree - 1)) * z ^ i.1) :
      begin
        have one_le_deg : 1 ≤ f.nat_degree :=
          nat.succ_le_of_lt (nat_degree_pos_of_aeval_root hf hz inj),
        congr,
        ext i,
        congr' 2,
        by_cases hi : i.1 = f.nat_degree,
        { rw [hi, to_monic_coeff_degree, one_mul, leading_coeff, ←pow_succ,
              nat.sub_add_cancel one_le_deg] },
        { have : i.1 ≤ f.nat_degree - 1 := nat.le_pred_of_lt (lt_of_le_of_ne
            (le_nat_degree_of_ne_zero (finsupp.mem_support_iff.mp i.2)) hi),
          rw [to_monic_coeff_ne_degree hf hi, mul_assoc, ←pow_add, nat.sub_add_cancel this] }
      end
... = algebra_map R S f.leading_coeff ^ (f.nat_degree - 1) * aeval R S z f :
      by { simp_rw [aeval_def, eval₂, finsupp.sum, λ i, mul_comm (coeff f i), ring_hom.map_mul,
                    ring_hom.map_pow, mul_assoc, ←finset.mul_sum],
           congr' 1,
           exact @finset.sum_attach _ _ f.support _ (λ i, algebra_map R S (f.coeff i) * z ^ i) }
... = 0 : by rw [hz, _root_.mul_zero]

lemma exists_integral_multiple (S_alg : algebra.is_algebraic R S) (z : S)
  (inj : ∀ x, algebra_map R S x = 0 → x = 0) :
  ∃ x : integral_closure R S × non_zero_divisors (integral_closure R S),
    z * x.2 = x.1 :=
begin
  obtain ⟨p, p_nonzero, px⟩ := S_alg z,
  set n := p.nat_degree with n_def,
  set a := p.leading_coeff with a_def,
  have a_nonzero : a ≠ 0 := mt polynomial.leading_coeff_eq_zero.mp p_nonzero,
  have y_integral : is_integral R (algebra_map R S a) := is_integral_algebra_map,
  have x_integral : is_integral R (z * algebra_map R S a) :=
  ⟨ to_monic p_nonzero, monic_to_monic p_nonzero, to_monic_aeval_eq_zero p_nonzero px inj ⟩,
  refine ⟨⟨⟨_, x_integral⟩, ⟨⟨_, y_integral⟩, _⟩⟩, rfl⟩,
  exact mem_non_zero_divisors_iff_ne_zero.mpr (λ h, a_nonzero (inj _ (subtype.ext.mp h)))
end

/-- If the field `L` is an algebraic extension of `R`,
  the integral closure of `R` in `L` has fraction field `L`. -/
def integral_closure.fraction_map [algebra R L] (L_alg : algebra.is_algebraic R L)
  (inj : ∀ x, algebra_map R L x = 0 → x = 0) :
  fraction_map (integral_closure R L) L :=
(algebra_map (integral_closure R L) L).to_localization_map
  (λ ⟨⟨y, integral⟩, nonzero⟩,
    have y ≠ 0 := λ h, mem_non_zero_divisors_iff_ne_zero.mp nonzero (subtype.ext.mpr h),
    show is_unit y, from ⟨⟨y, y⁻¹, mul_inv_cancel this, inv_mul_cancel this⟩, rfl⟩)
  (λ z, exists_integral_multiple L_alg _ inj)
  (λ x y, ⟨ λ (h : x.1 = y.1), ⟨1, by simpa using subtype.ext.mpr h⟩,
  λ ⟨c, hc⟩, congr_arg (algebra_map _ L)
    (eq_of_mul_eq_mul_right_of_ne_zero (mem_non_zero_divisors_iff_ne_zero.mp c.2) hc) ⟩)

lemma extension_is_algebraic_of_finite [algebra K L] (finite : finite_dimensional K L) :
  algebra.is_algebraic K L :=
λ x, (is_algebraic_iff_is_integral _).mpr (is_integral_of_noetherian ⊤
  (is_noetherian_of_submodule_of_noetherian _ _ _ finite) x algebra.mem_top)

open_locale classical

/-- `coeff_to_base_ring p` gives the coefficients of the polynomial `to_base_ring p` -/
noncomputable def coeff_to_base_ring (p : polynomial f.codomain) (i : ℕ) : R :=
if hi : i ∈ p.support
then classical.some (classical.some_spec
      (f.exist_integer_multiples_of_finset (p.support.image p.coeff))
      (p.coeff i)
      (finset.mem_image.mpr ⟨i, hi, rfl⟩))
else 0

lemma coeff_to_base_ring_mem_support (p : polynomial f.codomain) (i : ℕ)
  (h : coeff_to_base_ring p i ≠ 0) : i ∈ p.support :=
begin
  contrapose h,
  rw [ne.def, not_not, coeff_to_base_ring, dif_neg h]
end

/-- `to_base_ring g` clears the denominators of the given polynomial -/
noncomputable def to_base_ring : polynomial f.codomain → polynomial R :=
λ p, on_finset p.support (coeff_to_base_ring p) (coeff_to_base_ring_mem_support p)

@[simp]
lemma to_base_ring_coeff (p : polynomial f.codomain) (i : ℕ) :
  (to_base_ring p).coeff i = coeff_to_base_ring p i := rfl

lemma to_base_ring_spec (p : polynomial f.codomain) :
  ∃ (b : non_zero_divisors R), ∀ i, f.to_map ((to_base_ring p).coeff i) = f.to_map b * p.coeff i :=
begin
  use classical.some (f.exist_integer_multiples_of_finset (p.support.image p.coeff)),
  intro i,
  rw [to_base_ring_coeff, coeff_to_base_ring],
  split_ifs with hi,
  { exact classical.some_spec (classical.some_spec
      (f.exist_integer_multiples_of_finset (p.support.image p.coeff))
      (p.coeff i)
      (finset.mem_image.mpr ⟨i, hi, rfl⟩)) },
  { convert (_root_.mul_zero (f.to_map _)).symm,
    { exact f.to_ring_hom.map_zero },
    { exact finsupp.not_mem_support_iff.mp hi } }
end

lemma to_base_ring_map_to_map (p : polynomial f.codomain) : ∃ (b : non_zero_divisors R),
  (to_base_ring p).map f.to_map = f.to_map b • p :=
let ⟨b, hb⟩ := to_base_ring_spec p in ⟨b, polynomial.ext (λ i, by { rw coeff_map, exact hb i })⟩

lemma to_base_ring_eq_zero_iff {p : polynomial f.codomain} : to_base_ring p = 0 ↔ p = 0 :=
begin
  refine (polynomial.ext_iff.trans (polynomial.ext_iff.trans _).symm),
  obtain ⟨⟨b, nonzero⟩, hb⟩ := to_base_ring_spec p,
  split; intros h i,
  { apply f.to_map_eq_zero_iff.mpr,
    rw [hb i, h i],
    exact _root_.mul_zero _ },
  { have hi := h i,
    rw [coeff_zero, f.to_map_eq_zero_iff, hb i] at hi,
    apply or.resolve_left (eq_zero_or_eq_zero_of_mul_eq_zero hi),
    intro h,
    apply mem_non_zero_divisors_iff_ne_zero.mp nonzero,
    exact f.to_map_eq_zero_iff.mpr h }
end

lemma eval₂_smul {S : Type*} [comm_ring S] (g : R →+* S) (p : polynomial R) (x : S) {s : R} :
  eval₂ g x (s • p) = g s * eval₂ g x p :=
begin
  by_cases s = 0,
  { simp [h] },
  simp_rw [eval₂, finsupp.sum, finset.mul_sum],
  apply finset.sum_congr,
  { ext i,
    simp [mem_support_iff, h] },
  intros i hi,
  simp [mul_assoc]
end

lemma to_base_ring_eval₂_eq_zero {S : Type*} [comm_ring S] (g : f.codomain →+* S) (p : polynomial f.codomain) {x : S}
  (hx : eval₂ g x p = 0) : eval₂ (g ∘ f.to_map) x (to_base_ring p) = 0 :=
let ⟨b, hb⟩ := to_base_ring_map_to_map p in
trans (eval₂_map _ _ _).symm (by rw [hb, eval₂_smul, hx, _root_.mul_zero])

lemma to_base_ring_aeval_root {S : Type*} [comm_ring S] [algebra f.codomain S] (p : polynomial f.codomain) {x : S}
  (hx : aeval _ _ x p = 0) : aeval _ (algebra.comap R f.codomain S) x (to_base_ring p) = 0 :=
to_base_ring_eval₂_eq_zero (algebra_map f.codomain S) p hx

lemma comap_is_algebraic_iff [algebra f.codomain L] :
  algebra.is_algebraic R (algebra.comap R f.codomain L) ↔ algebra.is_algebraic f.codomain L :=
begin
  split; intros h x; obtain ⟨p, hp, px⟩ := h x,
  { refine ⟨p.map f.to_map, λ h, hp (polynomial.ext (λ i, _)), _⟩,
    { have : f.to_map (p.coeff i) = 0 := by { rw [←coeff_map], simp [h] },
      exact f.to_map_eq_zero_iff.mpr this },
    { exact trans (eval₂_map _ _ _) px } },
  { use [to_base_ring p, mt to_base_ring_eq_zero_iff.mp hp],
    convert to_base_ring_aeval_root p px },
end

lemma fraction_map.extension_is_algebraic_of_finite [algebra f.codomain L]
  (finite : finite_dimensional f.codomain L) : algebra.is_algebraic R (algebra.comap R f.codomain L) :=
comap_is_algebraic_iff.mpr (extension_is_algebraic_of_finite finite)

/-- The fraction field of the integral closure in a finite extension is that extension. -/
def integral_closure.fraction_map_of_finite_extension [algebra f.codomain L]
  (finite : finite_dimensional f.codomain L) :
  fraction_map (integral_closure R (algebra.comap R f.codomain L)) (algebra.comap R f.codomain L) :=
integral_closure.fraction_map
  (fraction_map.extension_is_algebraic_of_finite finite)
  (λ x hx, f.to_map_eq_zero_iff.mpr ((algebra_map f.codomain L).map_eq_zero.mp hx))

/- If L is a finite extension of K, the integral closure of R in L is a Dedekind domain. -/
def closure_in_field_extension [algebra f.codomain L] (finite : finite_dimensional f.codomain L)
  (h : is_dedekind_domain f) : is_dedekind_domain (integral_closure.fraction_map_of_finite_extension finite) :=
{ is_noetherian_ring := sorry,
  is_one_dimensional := sorry,
  is_integrally_closed := sorry }

end dedekind_domain

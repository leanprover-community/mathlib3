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

lemma mul_mem_non_zero_divisors {R} [comm_ring R] {a b : R} :
  a * b ∈ non_zero_divisors R ↔ a ∈ non_zero_divisors R ∧ b ∈ non_zero_divisors R :=
begin
  split,
  { intro h,
    split; intros x h'; apply h,
    { rw [←mul_assoc, h', zero_mul] },
    { rw [mul_comm a b, ←mul_assoc, h', zero_mul] } },
  { rintros ⟨ha, hb⟩ x hx,
    apply ha,
    apply hb,
    rw [mul_assoc, hx] },
end

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

section scale_roots

open finsupp polynomial

variables [comm_ring R]

lemma coeff_nat_degree_eq_zero_iff {f : polynomial R} : f.coeff f.nat_degree = 0 ↔ f = 0 :=
begin
  split; intro hf,
  { refine polynomial.degree_eq_bot.mp _,
    rw [polynomial.nat_degree] at hf,
    cases i_def : f.degree with i,
    { exact rfl },
    rw [polynomial.degree, ←finset.max_eq_sup_with_bot] at i_def hf,
    have := finsupp.mem_support_iff.mp (finset.mem_of_max i_def),
    rw [i_def, option.get_or_else_some] at hf,
    contradiction },
  { rw [hf, polynomial.coeff_zero] }
end

lemma nat_degree_mem_support {f : polynomial R} (hf : f ≠ 0) : f.nat_degree ∈ f.support :=
finsupp.mem_support_iff.mpr (mt coeff_nat_degree_eq_zero_iff.mp hf)

/-- If `f : polynomial R` has a root `r`, then `scale_roots f s` is a polynomial with root `r * s`. -/
noncomputable def scale_roots (p : polynomial R) (s : R) : polynomial R :=
on_finset p.support
  (λ i, coeff p i * s ^ (p.nat_degree - i))
  (λ i h, mem_support_iff.mpr (ne_zero_of_mul_ne_zero_right h))

@[simp] lemma coeff_scale_roots (p : polynomial R) (s : R) (i : ℕ) :
  (scale_roots p s).coeff i = coeff p i * s ^ (p.nat_degree - i) :=
rfl

lemma coeff_scale_roots_nat_degree (p : polynomial R) (s : R) :
  (scale_roots p s).coeff p.nat_degree = p.leading_coeff :=
by rw [leading_coeff, coeff_scale_roots, nat.sub_self, pow_zero, mul_one]

@[simp] lemma zero_scale_roots (s : R) : scale_roots 0 s = 0 := by { ext, simp }

lemma scale_roots_ne_zero {p : polynomial R} (hp : p ≠ 0) (s : R) :
  scale_roots p s ≠ 0 :=
begin
  intro h,
  have : p.coeff p.nat_degree ≠ 0 := mt coeff_nat_degree_eq_zero_iff.mp hp,
  have : (scale_roots p s).coeff p.nat_degree = 0 :=
    congr_fun (congr_arg (coeff : polynomial R → ℕ → R) h) p.nat_degree,
  rw [coeff_scale_roots_nat_degree] at this,
  contradiction
end

lemma support_scale_roots_le (p : polynomial R) (s : R) :
(scale_roots p s).support ≤ p.support :=
begin
  intros i,
  simp only [mem_support_iff, scale_roots, on_finset_apply],
  exact ne_zero_of_mul_ne_zero_right
end

lemma support_scale_roots_eq (p : polynomial R) {s : R} (hs : s ∈ non_zero_divisors R) :
  (scale_roots p s).support = p.support :=
le_antisymm (support_scale_roots_le p s)
  begin
    intro i,
    simp only [mem_support_iff, scale_roots, on_finset_apply],
    intros p_ne_zero ps_zero,
    have := ((non_zero_divisors R).pow_mem hs (p.nat_degree - i)) _ ps_zero,
    contradiction
  end

@[simp] lemma degree_scale_roots (p : polynomial R) {s : R} :
  degree (scale_roots p s) = degree p :=
begin
  haveI := classical.prop_decidable,
  by_cases hp : p = 0,
  { rw [hp, zero_scale_roots] },
  have := scale_roots_ne_zero hp s,
  refine le_antisymm (finset.sup_mono (support_scale_roots_le p s)) (degree_le_degree _),
  rw coeff_scale_roots_nat_degree,
  intro h,
  have := leading_coeff_eq_zero.mp h,
  contradiction,
end

@[simp] lemma nat_degree_scale_roots (p : polynomial R) {s : R} :
  nat_degree (scale_roots p s) = nat_degree p :=
by simp only [nat_degree, degree_scale_roots]

lemma monic_scale_roots_iff {p : polynomial R} {s : R} :
  monic (scale_roots p s) ↔ monic p :=
by simp [monic, leading_coeff]

variables {S : Type*} [comm_ring S]

lemma scale_roots_eval₂_eq_zero {p : polynomial S} (f : S →+* R)
  {r : R} {s : S} (hr : eval₂ f r p = 0) (hs : s ∈ non_zero_divisors S) :
  eval₂ f (f s * r) (scale_roots p s) = 0 :=
calc (scale_roots p s).support.sum (λ i, f (coeff p i * s ^ (p.nat_degree - i)) * (f s * r) ^ i)
    = p.support.sum (λ (i : ℕ), f (p.coeff i) * f s ^ (p.nat_degree - i + i) * r ^ i) :
  finset.sum_congr (support_scale_roots_eq p hs)
    (λ i hi, by simp_rw [f.map_mul, f.map_pow, pow_add, mul_pow, mul_assoc])
... = p.support.sum (λ (i : ℕ), f s ^ p.nat_degree * (f (p.coeff i) * r ^ i)) :
  finset.sum_congr rfl
  (λ i hi, by { rw [mul_assoc, mul_left_comm, nat.sub_add_cancel],
                exact le_nat_degree_of_ne_zero (mem_support_iff.mp hi) })
... = f s ^ p.nat_degree * eval₂ f r p : finset.mul_sum.symm
... = 0 : by rw [hr, _root_.mul_zero]

lemma scale_roots_aeval_eq_zero [algebra S R] {p : polynomial S}
  {r : R} {s : S} (hr : aeval S R r p = 0) (hs : s ∈ non_zero_divisors S) :
  aeval S R (algebra_map S R s * r) (scale_roots p s) = 0 :=
scale_roots_eval₂_eq_zero (algebra_map S R) hr hs

lemma scale_roots_eval₂_eq_zero_of_eval₂_div_eq_zero {R} [integral_domain R] [field K]
  {p : polynomial R} {f : R →+* K} (hf : function.injective f)
  {r s : R} (hr : eval₂ f (f r / f s) p = 0) (hs : s ∈ non_zero_divisors R) :
  eval₂ f (f r) (scale_roots p s) = 0 :=
begin
  convert scale_roots_eval₂_eq_zero f hr hs,
  rw [←mul_div_assoc, mul_comm, mul_div_cancel],
  exact @map_ne_zero_of_mem_non_zero_divisors _ _ _ _ _ hf ⟨s, hs⟩
end

lemma scale_roots_aeval_eq_zero_of_aeval_div_eq_zero {R} [integral_domain R] [field K] [algebra R K]
  (inj : function.injective (algebra_map R K)) {p : polynomial R} {r s : R}
  (hr : aeval R K (algebra_map R K r / algebra_map R K s) p = 0) (hs : s ∈ non_zero_divisors R) :
  aeval R K (algebra_map R K r) (scale_roots p s) = 0 :=
scale_roots_eval₂_eq_zero_of_eval₂_div_eq_zero inj hr hs

lemma is_root_of_eval₂_map_eq_zero [comm_ring S] {p : polynomial R} {f : R →+* S}
  (hf : function.injective f) {r : R} : eval₂ f (f r) p = 0 → p.is_root r :=
show eval₂ (f ∘ ring_hom.id R) (f r) p = 0 → eval₂ id r p = 0, begin
  intro h,
  rw [←hom_eval₂, ←f.map_zero] at h,
  exact hf h
end

lemma is_root_of_aeval_algebra_map_eq_zero [algebra R S] {p : polynomial R}
  (inj : function.injective (algebra_map R S))
  {r : R} (hr : polynomial.aeval R S (algebra_map R S r) p = 0) : p.is_root r :=
is_root_of_eval₂_map_eq_zero inj hr

end scale_roots

lemma prime.dvd_of_dvd_pow {a p : R} [comm_semiring R] (hp : prime p) {n : ℕ} (h : p ∣ a^n) : p ∣ a :=
begin
  induction n with n ih,
  { rw pow_zero at h,
    have := is_unit_of_dvd_one _ h,
    have := hp.not_unit,
    contradiction },
  { rw pow_succ at h,
    cases hp.div_or_div h,
    { assumption },
    { apply ih,
      assumption } }
end

namespace unique_factorization_domain

variables [integral_domain R] [unique_factorization_domain R] [field K] {f : fraction_map R K}

lemma is_unit.mul_right_dvd_of_dvd {a b c : R} (hb : is_unit b) (h : a ∣ c) : a * b ∣ c :=
begin
  rcases hb with ⟨b, rfl⟩,
  rcases h with ⟨c', rfl⟩,
  use (b⁻¹ : units R) * c',
  rw [mul_assoc, units.mul_inv_cancel_left]
end

lemma is_unit.mul_left_dvd_of_dvd {a b c : R} (hb : is_unit b) (h : a ∣ c) : b * a ∣ c :=
begin
  rcases hb with ⟨b, rfl⟩,
  rcases h with ⟨c', rfl⟩,
  use (b⁻¹ : units R) * c',
  rw [mul_comm (b : R) a, mul_assoc, units.mul_inv_cancel_left]
end

/-- If `p` and `q` are irreducible, then `p ∣ q` implies `q ∣ p`. -/
lemma irreducible.dvd_symm {p q : R} (hp : irreducible p) (hq : irreducible q) :
  p ∣ q → q ∣ p :=
begin
  tactic.unfreeze_local_instances,
  rintros ⟨q', rfl⟩,
  cases of_irreducible_mul hq with h h,
  { have := hp.not_unit,
    contradiction },
  { exact is_unit.mul_right_dvd_of_dvd h (dvd_refl p) }
end

lemma left_dvd_or_dvd_right_of_dvd_prime_mul {a : R} :
  ∀ {b p : R}, prime p → (a ∣ p * b) → p ∣ a ∨ a ∣ b :=
begin
  refine induction_on_prime a _ _ _,
  { intros b p _ ha,
    refine (eq_zero_or_eq_zero_of_mul_eq_zero (zero_dvd_iff.mp ha)).imp _ _;
      rintro ⟨rfl⟩; refl },
  { intros x x_is_unit b _ _ _,
    exact or.inr (is_unit_iff_forall_dvd.mp x_is_unit b) },
  { intros a q a_ne_zero hq ih b p hp qa_dvd,
    cases (hq.div_or_div (dvd_of_mul_right_dvd qa_dvd)) with q_dvd_p q_dvd_b,
    { left,
      apply dvd_mul_of_dvd_left,
      refine irreducible.dvd_symm (irreducible_of_prime _) (irreducible_of_prime _) _;
        assumption },
    { rcases q_dvd_b with ⟨b', rfl⟩,
      rw mul_left_comm at qa_dvd,
      refine (ih hp ((mul_dvd_mul_iff_left hq.ne_zero).mp qa_dvd)).imp _ _,
      { exact λ h, dvd_mul_of_dvd_right h _ },
      { exact mul_dvd_mul_left q } } }
end

/-- If `a ≠ 0, b` are elements of a unique factorization domain, then dividing
out their common factor `c'` gives `a'` and `b'` with no factors in common. -/
lemma exists_reduced_factors : ∀ (a ≠ (0 : R)) b,
  ∃ a' b' c', (∀ {p}, p ∣ a' → p ∣ b' → is_unit p) ∧ c' * a' = a ∧ c' * b' = b :=
begin
  haveI := classical.prop_decidable,
  intros a,
  refine induction_on_prime a _ _ _,
  { intros, contradiction },
  { intros a a_unit a_ne_zero b,
    use [a, b, 1],
    split,
    { intros p p_dvd_a _,
      exact is_unit_of_dvd_unit p_dvd_a a_unit },
    { simp } },
  { intros a p a_ne_zero p_prime ih_a pa_ne_zero b,
    by_cases p ∣ b,
    { rcases h with ⟨b, rfl⟩,
      obtain ⟨a', b', c', no_factor, ha', hb'⟩ := ih_a a_ne_zero b,
      refine ⟨a', b', p * c', @no_factor, _, _⟩,
      { rw [mul_assoc, ha'] },
      { rw [mul_assoc, hb'] } },
    { obtain ⟨a', b', c', coprime, rfl, rfl⟩ := ih_a a_ne_zero b,
      refine ⟨p * a', b', c', _, mul_left_comm _ _ _, rfl⟩,
      intros q q_dvd_pa' q_dvd_b',
      cases left_dvd_or_dvd_right_of_dvd_prime_mul p_prime q_dvd_pa' with p_dvd_q q_dvd_a',
      { have : p ∣ c' * b' := dvd_mul_of_dvd_right (dvd_trans p_dvd_q q_dvd_b') _,
        contradiction },
      exact coprime q_dvd_a' q_dvd_b'  } }
end

lemma exists_reduced_factors' (a b : R) (hb : b ≠ 0) :
  ∃ a' b' c', (∀ {p}, p ∣ a' → p ∣ b' → is_unit p) ∧ c' * a' = a ∧ c' * b' = b :=
let ⟨b', a', c', no_factor, hb, ha⟩ := exists_reduced_factors b hb a
in ⟨a', b', c', λ _ hpb hpa, no_factor hpa hpb, ha, hb⟩

lemma mul_mem_non_zero_divisors {a b : R} :
  a * b ∈ non_zero_divisors R ↔ a ∈ non_zero_divisors R ∧ b ∈ non_zero_divisors R :=
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

lemma exists_reduced_fraction (x : f.codomain) :
  ∃ (a : R) (b : non_zero_divisors R),
  (∀ {p}, p ∣ a → p ∣ b → is_unit p) ∧
  f.to_map a / f.to_map b = x :=
begin
  obtain ⟨⟨b, b_nonzero⟩, a, hab⟩ := f.exists_integer_multiple x,
  obtain ⟨a', b', c', no_factor, rfl, rfl⟩ := exists_reduced_factors' a b
    (mem_non_zero_divisors_iff_ne_zero.mp b_nonzero),
  obtain ⟨c'_nonzero, b'_nonzero⟩ := mul_mem_non_zero_divisors.mp b_nonzero,
  refine ⟨a', ⟨b', b'_nonzero⟩, @no_factor, eq.symm ((eq_div_iff _).mpr _)⟩,
  { exact f.map_ne_zero_of_mem_non_zero_divisors ⟨b', b'_nonzero⟩ },
  { rw mul_comm x,
    apply mul_left_cancel' (f.map_ne_zero_of_mem_non_zero_divisors ⟨c', c'_nonzero⟩),
    simp only [subtype.coe_mk, f.to_map.map_mul] at *,
    rw [←mul_assoc, hab] },
end

lemma dvd_term_of_is_root_of_dvd_coeff {r p : R} {f : polynomial R} (i : ℕ)
  (hf : f ≠ 0) (hr : f.is_root r) (h : ∀ (j ≠ i), p ∣ f.coeff j) : p ∣ f.coeff i * r ^ i :=
begin
  by_cases hi : i ∈ f.support,
  { unfold polynomial.is_root at hr,
    have : p ∣ f.eval r := hr.symm ▸ dvd_zero p,
    unfold polynomial.eval polynomial.eval₂ finsupp.sum id at this,
    rw [←finset.insert_erase hi, finset.sum_insert (finset.not_mem_erase _ _)] at this,
    refine (dvd_add_left (finset.dvd_sum _)).mp this,
    intros j hj,
    exact dvd_mul_of_dvd_left (h j (finset.ne_of_mem_erase hj)) _ },
  { convert dvd_zero p,
    convert _root_.zero_mul _,
    exact finsupp.not_mem_support_iff.mp hi }
end

lemma prime_dvd_root_of_monic_of_dvd_coeff {r p : R} (hp : prime p) {f : polynomial R}
  (hf : f.monic) (hr : f.is_root r) (h : ∀ i ≠ f.nat_degree, p ∣ f.coeff i) : p ∣ r :=
begin
  have := dvd_term_of_is_root_of_dvd_coeff f.nat_degree hf.ne_zero hr h,
  rw [←polynomial.leading_coeff, hf.leading_coeff, one_mul] at this,
  exact hp.dvd_of_dvd_pow this
end

lemma integrally_closed : integral_closure R f.codomain = ⊥ :=
begin
  apply integrally_closed_iff_integral_implies_integer.mpr,
  rintros x ⟨p, hp, px⟩,
  obtain ⟨a, ⟨b, b_nonzero⟩, no_factors, rfl⟩ := exists_reduced_fraction x,
  simp only [subtype.coe_mk] at *,
  suffices : is_unit b,
  { obtain ⟨⟨b, c, hbc, hcb⟩, rfl⟩ := this,
    simp only [units.coe_mk] at *,
    use c * a,
    refine (eq_div_iff _).mpr _,
    { exact f.map_ne_zero_of_mem_non_zero_divisors ⟨b, b_nonzero⟩ },
    rw [←f.to_map.map_mul, mul_assoc, mul_left_comm, hcb, mul_one] },
  apply is_unit_of_no_prime_factor,
  { exact mem_non_zero_divisors_iff_ne_zero.mp b_nonzero },
  intros q q_prime q_dvd_b,
  refine q_prime.not_unit (no_factors _ q_dvd_b),
  have alg_inj : function.injective (algebra_map R f.codomain) := f.injective,
  apply prime_dvd_root_of_monic_of_dvd_coeff q_prime (monic_scale_roots_iff.mpr hp),
  { apply is_root_of_aeval_algebra_map_eq_zero alg_inj,
    apply scale_roots_aeval_eq_zero_of_aeval_div_eq_zero; assumption },
  { intros i hi,
    rw nat_degree_scale_roots at hi,
    rw coeff_scale_roots,
    by_cases h : p.nat_degree < i,
    { rw [polynomial.coeff_eq_zero_of_nat_degree_lt h, _root_.zero_mul],
      exact dvd_zero q },
    { refine dvd_mul_of_dvd_right (dvd_trans q_dvd_b _) _,
      convert pow_dvd_pow b _,
      { exact (pow_one b).symm },
      { refine nat.succ_le_of_lt (nat.lt_sub_left_of_add_lt _),
        rw add_zero,
        exact lt_of_le_of_ne (le_of_not_gt h) hi } } },
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

lemma maximal_ideal_invertible_of_dedekind (h : is_dedekind_domain f) {M : ideal R}
(hM : ideal.is_maximal M) : is_unit (M : fractional_ideal f) :=
begin
have M1 := {x : K | ∀ y ∈ M, f.is_integer (x * f.to_map y)},
-- have hM1 : is_fractional f (M1), --sorry,
have M1 : fractional_ideal f, --sorry,
{use M1,
  sorry,
  intros a b ha hb,
  sorry,
  sorry,
  sorry,},
-- rcases M1 with ⟨I, aI, haI, hI⟩,
-- have N := fractional_ideal.mk_fractional(M),
have hprod : ↑M*M1=1, --sorry,
  apply le_antisymm,
    apply fractional_ideal.mul_le.mpr,
      intros x hx y hy,
      rw [mul_comm], sorry, sorry,
      -- sto copiando la prova dal teorema right_inverse_eq di fractional_ideal.lean
      -- exact (mem_div_iff_of_nonzero hI).mp hy x hx,},
    --   {rw [←h],
    --   apply mul_left_mono I,
    --   apply (le_div_iff_of_nonzero hI).mpr _,
    --   intros y hy x hx,
    --   rw [mul_comm],
    --   exact mul_mem_mul hx hy},
apply is_unit_of_mul_eq_one ↑M M1 hprod,
end


lemma fractional_ideal_invertible_of_dedekind (h : is_dedekind_domain f) (I : fractional_ideal f) :
I * I⁻¹ = 1 :=
begin
sorry
end

/- If L is a finite extension of K, the integral closure of R in L is a Dedekind domain. -/
def closure_in_field_extension [algebra f.codomain L] [finite_dimensional f.codomain L]
  (h : is_dedekind_domain f) :
  is_dedekind_domain (integral_closure.fraction_map_of_finite_extension L f) :=
{ is_noetherian_ring := sorry,
  is_one_dimensional := sorry,
  is_integrally_closed := sorry }

end dedekind_domain

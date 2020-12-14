import linear_algebra.determinant
import linear_algebra.free_module
import ring_theory.dedekind_domain
import ring_theory.fractional_ideal

open ring

open_locale big_operators

section dedekind_domain

variables {R K : Type*} [integral_domain R] [is_dedekind_domain R] [field K] {f : fraction_map R K}

lemma ideal.mul_right_mono (I J : ideal R) :
  I * J ≤ I :=
ideal.mul_le.mpr (λ i hi j hj, I.mul_mem_right hi)

noncomputable instance : comm_group_with_zero (fractional_ideal f) :=
{ exists_pair_ne := ⟨0, 1, zero_ne_one⟩,
  inv_zero := fractional_ideal.inv_zero,
  mul_inv_cancel := sorry,
  .. fractional_ideal.has_inv,
  .. fractional_ideal.comm_semiring }

@[simp]
lemma fractional_ideal.coe_ideal_le_coe_ideal {I J : ideal R} :
  (I : fractional_ideal f) ≤ (J : fractional_ideal f) ↔ I ≤ J :=
by library_search

@[simp]
lemma fractional_ideal.coe_to_fractional_ideal_mul {I J : ideal R} :
  (↑(I * J) : fractional_ideal f) = I * J :=
by library_search


open ring.fractional_ideal fractional_ideal

-- 3.1: "To contain is to divide"
lemma ideal.dvd_iff_le {I J : ideal R} :
  (I ∣ J) ↔ J ≤ I :=
⟨λ ⟨H, hH⟩, le_trans (le_of_eq hH) (ideal.mul_right_mono I H),
 λ h, begin
    by_cases hI : I = ⊥,
    { have hJ : J = ⊥,
      { rw hI at h,
        exact eq_bot_iff.mpr h },
      rw [hI, hJ] },
    set f := fraction_ring.of R,
    have hI' : (I : fractional_ideal f) ≠ 0 :=
      (fractional_ideal.coe_to_fractional_ideal_ne_zero (le_refl (non_zero_divisors R))).mpr hI,
    have : (I : fractional_ideal f)⁻¹ * J ≤ 1 := le_trans
      (fractional_ideal.mul_left_mono _ (coe_ideal_le_coe_ideal.mpr h))
      (le_of_eq (inv_mul_cancel hI')),
    obtain ⟨H, hH⟩ := fractional_ideal.le_one_iff_exists_coe_ideal.mp this,
    use H,
    refine coe_to_fractional_ideal_injective (le_refl (non_zero_divisors R))
      (show (J : fractional_ideal f) = _, from _),
    rw [coe_to_fractional_ideal_mul, hH, ← mul_assoc, mul_inv_cancel hI', one_mul]
  end⟩

lemma ideal.mul_left_cancel' {H I J : ideal R} (hH : H ≠ 0) (hIJ : H * I = H * J) :
  I = J :=
coe_to_fractional_ideal_injective
  (le_refl (non_zero_divisors R))
  (show (I : fractional_ideal (fraction_ring.of R)) = J,
   from mul_left_cancel'
     ((coe_to_fractional_ideal_ne_zero (le_refl (non_zero_divisors R))).mpr hH)
     (by simpa only [← coe_to_fractional_ideal_mul] using congr_arg coe hIJ))

instance : comm_cancel_monoid_with_zero (ideal R) :=
{ mul_left_cancel_of_ne_zero := λ H I J hH hIJ, ideal.mul_left_cancel' hH hIJ,
  mul_right_cancel_of_ne_zero := λ H I J hI hHJ, ideal.mul_left_cancel' hI (by rwa [mul_comm I H, mul_comm I J]),
  .. ideal.comm_semiring }

lemma ideal.is_unit_iff {I : ideal R} :
  is_unit I ↔ I = ⊤ :=
by rw [is_unit_iff_dvd_one, ideal.one_eq_top, ideal.dvd_iff_le, eq_top_iff]

lemma ideal.dvd_not_unit_iff_lt {I J : ideal R} :
  dvd_not_unit I J ↔ J < I :=
⟨λ ⟨hI, H, hunit, hmul⟩, lt_of_le_of_ne (ideal.dvd_iff_le.mp ⟨H, hmul⟩)
  (mt (λ h, have H = 1, from mul_left_cancel' hI (by rw [← hmul, h, mul_one]),
            show is_unit H, from this.symm ▸ is_unit_one) hunit),
 λ h, dvd_not_unit_of_dvd_of_not_dvd (ideal.dvd_iff_le.mpr (le_of_lt h))
   (mt ideal.dvd_iff_le.mp (not_le_of_lt h))⟩

lemma ideal.dvd_not_unit_eq_gt : (dvd_not_unit : ideal R → ideal R → Prop) = (>) :=
by { ext, exact ideal.dvd_not_unit_iff_lt }

instance : wf_dvd_monoid (ideal R) :=
{ well_founded_dvd_not_unit :=
  have well_founded ((>) : ideal R → ideal R → Prop) :=
  is_noetherian_iff_well_founded.mp (is_dedekind_domain.is_noetherian_ring),
  by rwa ideal.dvd_not_unit_eq_gt }

#print ideal.is_prime

instance ideal.unique_factorization_monoid :
  unique_factorization_monoid (ideal R) :=
{ irreducible_iff_prime := λ P,
    ⟨λ hirr, ⟨hirr.ne_zero, hirr.not_unit, λ I J, begin
      have : P.is_maximal,
      { use mt ideal.is_unit_iff.mpr hirr.not_unit,
        intros J hJ,
        obtain ⟨J_ne, H, hunit, P_eq⟩ := ideal.dvd_not_unit_iff_lt.mpr hJ,
        exact ideal.is_unit_iff.mp ((hirr.is_unit_or_is_unit P_eq).resolve_right hunit) },
      simp only [ideal.dvd_iff_le, has_le.le, preorder.le, partial_order.le],
      contrapose!,
      rintros ⟨⟨x, x_mem, x_not_mem⟩, ⟨y, y_mem, y_not_mem⟩⟩,
      exact ⟨x * y, ideal.mul_mem_mul x_mem y_mem, mt this.is_prime.mem_or_mem (not_or x_not_mem y_not_mem)⟩,
    end⟩,
     λ h, irreducible_of_prime h⟩,
  .. ideal.wf_dvd_monoid }

-- 3.2: "Only finitely many divisors"
lemma unique_factorization_monoid.finite_divisors
  {R : Type*} [comm_cancel_monoid_with_zero R] [unique_factorization_monoid R]
  (x : R) : set.finite {y | y ∣ x} :=
begin
  sorry
end

lemma ideal.finite_divisors (I : ideal R) : set.finite {J | J ∣ I} :=
unique_factorization_monoid.finite_divisors I

end dedekind_domain

-- TODO: unify this with `is_absolute_value` in `data.real.cau_seq`?
structure absolute_value (R S : Type*) [semiring R] [ordered_semiring S] extends mul_hom R S :=
(zero_le_map' : ∀ x, 0 ≤ to_fun x)
(map_eq_zero_iff' : ∀ x, to_fun x = 0 ↔ x = 0)
(map_add_le' : ∀ x y, to_fun (x + y) ≤ to_fun x + to_fun y)

namespace absolute_value

variables {R S : Type*} [semiring R] [ordered_semiring S]

instance : has_coe_to_fun (absolute_value R S) := ⟨λ f, R → S, λ f, f.to_fun⟩

lemma nonneg (f : absolute_value R S) (x : R) : 0 ≤ f x := f.zero_le_map' x

@[simp]
lemma eq_zero_iff {f : absolute_value R S} {x : R} : f x = 0 ↔ x = 0 := f.map_eq_zero_iff' x

@[simp]
lemma map_zero (f : absolute_value R S) : f 0 = 0 := eq_zero_iff.mpr rfl

@[simp]
lemma map_mul (f : absolute_value R S) (x y : R) : f (x * y) = f x * f y := f.map_mul' x y

lemma le_add (f : absolute_value R S) (x y : R) : f (x + y) ≤ f x + f y := f.map_add_le' x y

@[simp]
lemma map_one (f : absolute_value R S) : f 1 = 1 :=
_

def to_monoid_hom (f : absolute_value R S) : R →* S :=
{ map_one' := f.map_one,
  .. f}

@[simp]
lemma map_neg {R : Type*} [ring R] (f : absolute_value R S) (x : R) :
  f (-x) = f x :=
_

@[simp]
lemma map_units {R : Type*} [ring R] (f : absolute_value R S) (x : units ℤ) :
  f ((x : ℤ) : R) = 1 :=
by rcases int.units_eq_one_or x with (rfl | rfl); simp

/-
-- TODO: weaken assumption on S?
noncomputable def to_fraction_ring {R S K L : Type*} [comm_ring R] {P : submonoid R}
  [linear_ordered_comm_ring S] [field K] [field L]
  (f : absolute_value R S) (g : fraction_map R K) (h : fraction_map S L) :
  absolute_value g.codomain h.codomain :=
{ to_fun := λ x, h.to_ring_hom (f (g.to_localization_map.sec x).1) /
    h.to_ring_hom (f (g.to_localization_map.sec x).2),
  map_mul' := sorry,
  zero_le_map' := sorry,
  map_add_le' := sorry,
  map_eq_zero_iff' := sorry }
  -/

-- TODO: this could be generalized to extending the codomain from any S to S's fraction field
noncomputable def int_to_fraction_ring {R S K L : Type*} [comm_ring R] {P : submonoid R}
  [linear_ordered_comm_ring S] [field K] [field L]
  (f : absolute_value R ℤ) (g : fraction_map R K) :
  absolute_value g.codomain ℚ :=
{ zero_le_map' := λ x,
    by { simp only [← div_eq_mul_inv], exact div_nonneg (by exact_mod_cast f.nonneg _) (by exact_mod_cast f.nonneg _) },
  map_add_le' := λ x y, _,
  map_eq_zero_iff' := sorry,
  .. @submonoid.localization_map.lift _ _ _ _ _ _ _ g.to_localization_map f.to_monoid_hom _ }

def absolute_value.abs {R : Type*} [linear_ordered_ring R] : absolute_value R R :=
{ to_fun := λ x, abs x,
  map_add_le' := λ x y, abs_add x y,
  map_eq_zero_iff' := λ x, abs_eq_zero,
  map_mul' := λ x y, abs_mul x y,
  zero_le_map' := λ x, abs_nonneg x }

open polynomial

lemma nat_degree_add_le (p q : polynomial R) :
  nat_degree (p + q) ≤ max (nat_degree p) (nat_degree q) :=
sorry


noncomputable def absolute_value.pow_degree {R : Type*} [integral_domain R] [decidable_eq R]
  {c : ℤ} (hc : 1 < c) :
  absolute_value (polynomial R) ℤ :=
{ to_fun := λ p, if p = 0 then 0 else c ^ p.nat_degree,
  map_add_le' := λ p q, begin
    simp only,
    by_cases hp : p = 0,
    { simp only [hp, zero_add, eq_self_iff_true, if_true, nat_degree_zero],
      convert le_rfl },
    by_cases hq : q = 0,
    { simp only [hq, add_zero, eq_self_iff_true, if_true, nat_degree_zero],
      convert le_rfl },
    simp only [hp, hq, if_false, pow_add],
    split_ifs with hpq;
      try { refine add_nonneg (pow_nonneg _ _) (pow_nonneg _ _); linarith },
    { refine le_trans (pow_le_pow _ (nat_degree_add_le _ _)) _,
      { linarith },
      refine le_trans (le_max_iff.mpr _) (max_le_add_of_nonneg (pow_nonneg _ _) (pow_nonneg _ _));
      sorry }
  end,
  map_eq_zero_iff' := λ p, by { simp only, split_ifs with h; simp [h], sorry },
  map_mul' := λ p q, begin
    by_cases hp : p = 0,
    { simp only [hp, zero_mul, eq_self_iff_true, if_true, polynomial.nat_degree_zero] },
    by_cases hq : q = 0,
    { simp only [hq, mul_zero, eq_self_iff_true, if_true, polynomial.nat_degree_zero] },
    simp only [hp, hq, mul_eq_zero, false_or, if_false, polynomial.nat_degree_mul hp hq, pow_add]
    end,
  zero_le_map' := λ p, begin
    simp only,
    split_ifs with hp,
    { refl },
    apply pow_nonneg,
    linarith
  end }

lemma le_sum {ι : Type*} (s : finset ι) (f : absolute_value R S) (g : ι → R) :
  f (∑ i in s, g i) ≤ ∑ i in s, f (g i) :=
begin
  haveI := classical.dec_eq ι,
  refine finset.induction_on s _ _,
  { simp },
  intros a s ha ih,
  simp only [finset.sum_insert ha],
  exact le_trans (f.le_add _ _) (add_le_add_left ih _),
end

@[simp]
lemma map_prod {R S : Type*} [comm_semiring R] [linear_ordered_comm_ring S]
  {ι : Type*} (f : absolute_value R S) (s : finset ι) (g : ι → R) :
  f (∏ i in s, g i) = ∏ i in s, f (g i) :=
begin
  haveI := classical.dec_eq ι,
  refine finset.induction_on s _ _,
  { simp },
  intros a s ha ih,
  simp only [finset.prod_insert ha, f.map_mul, ih],
end

end absolute_value

section det

open equiv finset matrix

variables {R S : Type*} [comm_ring R] [linear_ordered_comm_ring S] {n : Type*} [fintype n] [decidable_eq n]

-- 3.4: a bound on the determinant
lemma det_le {A : matrix n n R} {f : absolute_value R S}
  {x : S} (hx : ∀ i j, f (A i j) ≤ x) :
  f A.det ≤ nat.factorial (fintype.card n) • x ^ (fintype.card n) :=
calc f A.det ≤ ∑ σ : perm n, f ((σ.sign : ℤ) * ∏ i, A (σ i) i) : f.le_sum _ _
         ... = ∑ σ : perm n, (∏ i, f (A (σ i) i)) : sum_congr rfl (λ σ hσ,
           by rw [f.map_mul, f.map_units, one_mul, f.map_prod])
         ... ≤ ∑ σ : perm n, (∏ (i : n), x) :
           sum_le_sum (λ _ _, prod_le_prod (λ _ _, f.nonneg _) (λ _ _, hx _ _))
         ... = ∑ σ : perm n, x ^ (fintype.card n) : sum_congr rfl (λ _ _,
           by rw [prod_const, finset.card_univ])
         ... = nat.factorial (fintype.card n) •ℕ x ^ (fintype.card n) :
           by rw [sum_const, finset.card_univ, fintype.card_perm]

lemma det_sum_le {ι : Type*} (s : finset ι) {c : ι → R} {A : ι → matrix n n R}
  {f : absolute_value R S}
  {x : S} (hx : ∀ k i j, f (A k i j) ≤ x) {y : S} (hy : ∀ k, f (c k) ≤ y) :
  f (det (∑ k in s, c k • A k)) ≤ nat.factorial (fintype.card n) • (finset.card s • (x * y)) ^ (fintype.card n) :=
begin
  have : ∀ i j, f ((∑ k in s, (c k • A k)) i j) ≤ finset.card s • (x * y),
  { intros i j,
    calc f ((∑ k in s, (c k • A k)) i j)
        = f (∑ k in s, (c k • A k) i j) : by simp only [sum_apply]
    ... ≤ ∑ k in s, f ((c k • A k) i j) : f.le_sum _ _
    ... = ∑ k in s, f (A k i j) * f (c k) : sum_congr rfl (λ k _,
      by rw [matrix.smul_apply, mul_comm, f.map_mul])
    ... ≤ ∑ k in s, x * y : sum_le_sum (λ k _, mul_le_mul (hx _ _ _) (hy _)
      (f.nonneg _) (le_trans (f.nonneg _) (hx k i j)))
    ... = s.card •ℕ (x * y) : sum_const _, },
  exact det_le this
end

end det


section div_with_rem

variables {R K L : Type*} [integral_domain R] [field K] [field L]
variables (f : fraction_map R K)
variables [algebra f.codomain L] [finite_dimensional f.codomain L]
variables [algebra R L] [is_scalar_tower R f.codomain L]

lemma subalgebra.smul_mk {R A : Type*} [comm_semiring R] [semiring A] [algebra R A]
  {S : subalgebra R A} (a : R) (x : A) (hx : x ∈ S) :
  a • (⟨x, hx⟩ : S) = ⟨a • x, S.smul_mem hx a⟩ :=
by { ext, refl }

@[simp]
lemma subalgebra.mk_eq_zero_iff {R A : Type*} [comm_semiring R] [semiring A] [algebra R A]
  {S : subalgebra R A} (x : A) (hx : x ∈ S) :
  (⟨x, hx⟩ : S) = 0 ↔ x = 0 :=
subtype.ext_iff

#check exists_integral_multiple

lemma fraction_map.map_ne_zero {x : R} (hx : x ≠ 0) : f.to_map x ≠ 0 :=
mt (f.to_map.injective_iff.mp (fraction_map.injective f) _) hx

lemma is_basis_coe {ι : Type*} {b : ι → integral_closure R L}
  (hb : is_basis R b) : is_basis f.codomain ((coe : integral_closure R L → L) ∘ b) :=
begin
  haveI := classical.dec_eq ι,
  haveI := classical.dec_eq K,
  split,
  { rw linear_independent_iff'',
    intros s g hg h i,
    obtain ⟨⟨a, a_ne⟩, ha⟩ := f.exist_integer_multiples_of_finset (s.image g),
    set g' : ι → R := λ i,
        if h : i ∈ s
        then classical.some (ha (g i) (finset.mem_image.mpr ⟨i, h, rfl⟩))
        else 0
      with g'_eq,
    have hg' : ∀ i, f.to_map (g' i) = (a • g i : f.codomain),
    { intros i,
      simp only [g'_eq],
      split_ifs with hi,
      { exact (classical.some_spec (ha (g i) _)) },
      { rw [hg _ hi, smul_zero, ring_hom.map_zero] } },
    suffices : g' i = 0,
    { have := congr_arg f.to_map this,
      rw [hg' i, ring_hom.map_zero, algebra.smul_def, f.algebra_map_eq, mul_eq_zero] at this,
      exact this.resolve_left (f.to_map_ne_zero_of_mem_non_zero_divisors ⟨a, a_ne⟩) },
    apply linear_independent_iff''.mp hb.1 s (λ i, g' i),
    { intros i hi, exact dif_neg hi },
    { rw [← submodule.coe_eq_zero, ← subalgebra.coe_val, alg_hom.map_sum, ← smul_zero a, ← h,
          finset.smul_sum, finset.sum_congr rfl],
      intros i hi,
      simp only [subalgebra.coe_val, submodule.coe_smul, function.comp_app],
      rw [← is_scalar_tower.algebra_map_smul f.codomain (g' i) (b i : L), f.algebra_map_eq,
          hg', smul_assoc] } },
  { rw eq_top_iff,
    intros x _,
    set g : fraction_map (integral_closure R L) L :=
      integral_closure.fraction_map_of_finite_extension L f,
    have : algebra.is_algebraic R L := f.comap_is_algebraic_iff.mpr algebra.is_algebraic_of_finite,
    obtain ⟨y, z, z_ne, ha⟩ := exists_integral_multiple (this x)
      (λ x hx, f.to_map_eq_zero_iff.mp ((algebra_map f.codomain L).map_eq_zero.mp $
        (is_scalar_tower.algebra_map_apply _ _ _ _).symm.trans hx)),
    have := hb.mem_span y,
    refine (submodule.smul_mem_iff _ (f.map_ne_zero z_ne)).mp _,
    rw [← f.algebra_map_eq, is_scalar_tower.algebra_map_smul f.codomain z x, ha],
    obtain ⟨t, c, rfl⟩ := mem_span_range_iff_exists_sum.mp this,
    show (integral_closure R L).val (∑ (i : ι) in t, c i • b i) ∈
      submodule.span (localization_map.codomain f) (set.range ((integral_closure R L).val ∘ b)),
    simp only [alg_hom.map_sum, alg_hom.map_smul],
    apply submodule.sum_mem _ _,
    intros i hi,
    rw ← is_scalar_tower.algebra_map_smul f.codomain (c i) ((integral_closure R L).val (b i)),
    exact submodule.smul_mem _ _ (submodule.subset_span ⟨i, rfl⟩) }
end

end div_with_rem

end

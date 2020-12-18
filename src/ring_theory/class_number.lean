import algebra.floor
import group_theory.quotient_group
import linear_algebra.determinant
import linear_algebra.free_module
import linear_algebra.matrix
import ring_theory.dedekind_domain
import ring_theory.fractional_ideal

open ring

open_locale big_operators

section move_me

lemma ne_zero_of_mem_non_zero_divisors {R : Type*} [monoid_with_zero R] [nontrivial R]
  {y : R} (hy : y ∈ non_zero_divisors R) :
  y ≠ 0 :=
λ h, one_ne_zero (show (1 : R) = 0, from hy _ (by rw [h, one_mul]))

lemma ideal.mul_right_le {R : Type*} [comm_ring R] (I J : ideal R) :
  I * J ≤ I :=
ideal.mul_le.mpr (λ i hi j hj, I.mul_mem_right hi)

lemma ideal.mul_left_mono {R : Type*} [comm_ring R]
  {I J K : ideal R} (h : I ≤ J) :
  K * I ≤ K * J :=
ideal.mul_le.mpr (λ a ha b hb, ideal.mul_mem_mul ha (h hb))

section

variables {R K : Type*} [integral_domain R] [field K] {f : fraction_map R K}

@[simp]
lemma fractional_ideal.coe_to_fractional_ideal_mul (I J : ideal R) :
  (↑(I * J) : fractional_ideal f) = I * J :=
sorry

@[simp]
lemma fractional_ideal.coe_ideal_le_coe_ideal {I J : ideal R} :
  (I : fractional_ideal f) ≤ (J : fractional_ideal f) ↔ I ≤ J :=
sorry

end

end move_me

section dedekind_domain

variables {R K : Type*} [integral_domain R] [is_dedekind_domain R] [field K] {f : fraction_map R K}

noncomputable instance : comm_group_with_zero (fractional_ideal f) :=
{ exists_pair_ne := ⟨0, 1, zero_ne_one⟩,
  inv_zero := fractional_ideal.inv_zero,
  mul_inv_cancel := sorry,
  .. fractional_ideal.has_inv,
  .. fractional_ideal.comm_semiring }

open ring.fractional_ideal fractional_ideal

-- 3.1: "To contain is to divide"
lemma ideal.dvd_iff_le {I J : ideal R} :
  (I ∣ J) ↔ J ≤ I :=
⟨λ ⟨H, hH⟩, le_trans (le_of_eq hH) (ideal.mul_right_le I H),
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

#check associates.mk

namespace unique_factorization_monoid

-- 3.2: "Only finitely many divisors"
lemma finite_divisors
  {R : Type*} [comm_cancel_monoid_with_zero R] [unique_factorization_monoid R]
  {x : R} (hx : x ≠ 0) : set.finite {(y : associates R) | y ∣ associates.mk x} :=
begin
  haveI : nontrivial R := ⟨⟨x, 0, hx⟩⟩,
  haveI := @unique_factorization_monoid.normalization_monoid R _ _ _,
  haveI := classical.dec_eq R,
  haveI := classical.dec_eq (associates R),
  set divisors := ((factors x).powerset.map (λ (s : multiset R), associates.mk s.prod)).to_finset,
  convert set.finite_mem_finset divisors,
  ext y,
  obtain ⟨y, rfl⟩ := associates.mk_surjective y,
  simp only [exists_prop, multiset.mem_to_finset, multiset.mem_powerset, exists_eq_right,
    multiset.mem_map, associates.mk_dvd_mk],
  split,
  { intro h,
    have hy : y ≠ 0, { refine mt (λ hy, _) hx, rwa [hy, zero_dvd_iff] at h },
    refine ⟨factors y, _, quot.sound (factors_prod hy)⟩,
    exact (dvd_iff_factors_le_factors hy hx).mp h },
  { rintros ⟨s, hs, hy⟩,
    refine (dvd_iff_factors_le_factors _ hx).mpr (le_trans (le_of_eq _) hs),
    apply factors_unique }
end

end unique_factorization_monoid

lemma ideal.finite_divisors (I : ideal R) (hI : I ≠ ⊥) : set.finite {J | J ∣ I} :=
begin
  have := unique_factorization_monoid.finite_divisors hI,
end

end dedekind_domain

-- TODO: unify this with `is_absolute_value` in `data.real.cau_seq`?
structure absolute_value (R S : Type*) [semiring R] [ordered_semiring S] extends mul_hom R S :=
(zero_le_map' : ∀ x, 0 ≤ to_fun x)
(map_eq_zero_iff' : ∀ x, to_fun x = 0 ↔ x = 0)
(map_add_le' : ∀ x y, to_fun (x + y) ≤ to_fun x + to_fun y)

namespace absolute_value

section semiring

variables {R : Type*} [semiring R]

section ordered_semiring

variables {S : Type*} [ordered_semiring S]

instance : has_coe_to_fun (absolute_value R S) := ⟨λ f, R → S, λ f, f.to_fun⟩

@[simp] lemma coe_to_mul_hom (f : absolute_value R S) : ⇑f.to_mul_hom = f := rfl

lemma nonneg (f : absolute_value R S) (x : R) : 0 ≤ f x := f.zero_le_map' x

@[simp]
lemma eq_zero_iff (f : absolute_value R S) {x : R} : f x = 0 ↔ x = 0 := f.map_eq_zero_iff' x

@[simp]
lemma map_zero (f : absolute_value R S) : f 0 = 0 := f.eq_zero_iff.mpr rfl

lemma map_ne_zero (f : absolute_value R S) {x : R} : f x ≠ 0 ↔ x ≠ 0 :=
not_iff_not.mpr f.eq_zero_iff

/-- `simp`-normal form version of `f.map_ne_zero` -/
@[simp]
lemma map_ne_zero' (f : absolute_value R S) {x : R} : ¬ (f x = 0) ↔ ¬ (x = 0) :=
f.map_ne_zero

lemma pos (f : absolute_value R S) {x : R} (hx : x ≠ 0) : 0 < f x :=
lt_of_le_of_ne (f.nonneg x) (f.map_ne_zero.mpr hx).symm

@[simp]
lemma map_mul (f : absolute_value R S) (x y : R) : f (x * y) = f x * f y := f.map_mul' x y

lemma le_add (f : absolute_value R S) (x y : R) : f (x + y) ≤ f x + f y := f.map_add_le' x y

end ordered_semiring

section linear_ordered_ring

variables {S : Type*} [linear_ordered_ring S]

@[simp]
lemma map_one [nontrivial R] (f : absolute_value R S) : f 1 = 1 :=
(mul_right_inj' $ show f 1 ≠ 0, from f.map_ne_zero.mpr one_ne_zero).mp $
show f 1 * f 1 = f 1 * 1, by rw [← f.map_mul, mul_one, mul_one]

def to_monoid_hom [nontrivial R] (f : absolute_value R S) : R →* S :=
{ map_one' := f.map_one,
  .. f }

@[simp] lemma coe_fn_to_monoid_hom [nontrivial R] (f : absolute_value R S) :
  ⇑f.to_monoid_hom = f := rfl

end linear_ordered_ring

end semiring

section ring

variables {R : Type*} [ring R]

section linear_ordered_comm_ring

variables {S : Type*} [linear_ordered_comm_ring S]

@[simp]
lemma map_neg (f : absolute_value R S) (x : R) :
  f (-x) = f x :=
begin
  by_cases hx : x = 0, { simp [hx] },
  refine (mul_self_eq_mul_self_iff.mp
    (by rw [← f.map_mul, neg_mul_neg, f.map_mul])).resolve_right _,
  have : 0 < f x := f.pos hx,
  have : 0 < f (-x) := f.pos (neg_ne_zero.mpr hx),
  linarith
end

@[simp]
lemma map_sub_eq_zero_iff (f : absolute_value R S) (a b : R) :
  f (a - b) = 0 ↔ a = b :=
f.eq_zero_iff.trans sub_eq_zero

@[simp]
lemma map_units [nontrivial R] (f : absolute_value R S) (x : units ℤ) :
  f ((x : ℤ) : R) = 1 :=
by rcases int.units_eq_one_or x with (rfl | rfl); simp

-- TODO: this could be generalized to extending the codomain from any S to S's fraction field
noncomputable def to_frac {R K : Type*} [nontrivial R] [comm_ring R] [field K]
  (f : absolute_value R ℤ) (g : fraction_map R K) :
  absolute_value g.codomain ℚ :=
{ zero_le_map' := λ x, begin
    obtain ⟨x_n, ⟨x_d, hx_d⟩, rfl⟩ := g.to_localization_map.mk'_surjective x,
    simp only [ring_hom.to_monoid_hom_eq_coe, monoid_hom.to_fun_eq_coe, g.to_localization_map.lift_mk',
      ring_hom.eq_int_cast, ring_hom.coe_monoid_hom, units.coe_inv', function.comp_app, coe_fn_to_monoid_hom,
      monoid_hom.coe_comp, is_unit.coe_lift_right, monoid_hom.mrestrict_apply, subtype.coe_mk],
    refine mul_nonneg _ (inv_nonneg.mpr _),
    { exact_mod_cast f.nonneg x_n },
    { exact_mod_cast f.nonneg x_d }
  end,
  map_add_le' := λ x y, begin
    obtain ⟨x_n, ⟨x_d, hx_d⟩, rfl⟩ := g.mk'_surjective x,
    obtain ⟨y_n, ⟨y_d, hy_d⟩, rfl⟩ := g.mk'_surjective y,
    rw ← g.mk'_add,
    simp only [ring_hom.to_monoid_hom_eq_coe, monoid_hom.to_fun_eq_coe, localization_map.mk',
      g.to_localization_map.lift_mk', ring_hom.eq_int_cast, ring_hom.coe_monoid_hom, units.coe_inv',
      function.comp_app, coe_fn_to_monoid_hom, monoid_hom.coe_comp, monoid_hom.mrestrict_apply,
      ring_hom.eq_int_cast, ring_hom.coe_monoid_hom, is_unit.coe_lift_right, function.comp_app,
      coe_fn_to_monoid_hom, monoid_hom.coe_comp, subtype.coe_mk, int.cast_mul, submonoid.coe_mul,
      map_mul, subtype.coe_mk],
    sorry
  end,
  map_eq_zero_iff' := λ x, begin
    obtain ⟨x_n, ⟨x_d, hx_d⟩, rfl⟩ := g.to_localization_map.mk'_surjective x,
    squeeze_simp [g.to_localization_map.lift_mk', ne_zero_of_mem_non_zero_divisors hx_d],
    refine iff.trans _ g.mk'_eq_iff_eq_mul.symm,
    sorry
  end,
  .. @submonoid.localization_map.lift _ _ _ _ _ _ _ g.to_localization_map
    ((algebra_map ℤ ℚ).to_monoid_hom.comp f.to_monoid_hom)
    (λ ⟨y, hy⟩, is_unit.mk0 _ (by simpa only [int.cast_eq_zero, eq_zero_iff, ring_hom.eq_int_cast, ring_hom.coe_monoid_hom, ring_hom.to_monoid_hom_eq_coe, function.comp_app, ne.def, coe_fn_to_monoid_hom, monoid_hom.coe_comp] using ne_zero_of_mem_non_zero_divisors hy)) }

.

@[simp]
lemma to_frac_mk' {R K : Type*} [nontrivial R] [comm_ring R] [field K]
  (f : absolute_value R ℤ) (g : fraction_map R K) (a : R) (b : non_zero_divisors R) :
  f.to_frac g (g.mk' a b) = f a / f b :=
(submonoid.localization_map.lift_mk' _ _ _ _).trans
  (by simp [is_unit.coe_lift_right, div_eq_mul_inv])

@[simp]
lemma to_frac_to_map {R K : Type*} [nontrivial R] [comm_ring R] [field K]
  (f : absolute_value R ℤ) (g : fraction_map R K) (a : R) :
  f.to_frac g (g.to_map a) = f a :=
by { rw ← g.mk'_one, simp }

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
lemma map_prod {R S : Type*} [comm_semiring R] [nontrivial R]
  [linear_ordered_comm_ring S]
  {ι : Type*} (f : absolute_value R S) (s : finset ι) (g : ι → R) :
  f (∏ i in s, g i) = ∏ i in s, f (g i) :=
begin
  haveI := classical.dec_eq ι,
  refine finset.induction_on s _ _,
  { simp },
  intros a s ha ih,
  simp only [finset.prod_insert ha, f.map_mul, ih],
end

end linear_ordered_comm_ring

end ring

end absolute_value

local infix ` ≺ `:50 := euclidean_domain.r

/-- A `euclidean_absolute_value` is an absolute value from R to S,
that agrees with the `euclidean_domain` structure on `R` -/
structure euclidean_absolute_value (R S : Type*) [euclidean_domain R] [ordered_semiring S]
  extends absolute_value R S :=
(map_lt_map_iff' : ∀ x y, to_fun x < to_fun y ↔ x ≺ y)

namespace euclidean_absolute_value

section euclidean_domain

variables {R S : Type*} [euclidean_domain R] [ordered_semiring S]
variables (f : euclidean_absolute_value R S)

instance : has_coe_to_fun (euclidean_absolute_value R S) :=
{ F := λ _, R → S,
  coe := λ f, f.to_fun }

instance : has_coe (euclidean_absolute_value R S) (absolute_value R S) :=
⟨euclidean_absolute_value.to_absolute_value⟩

lemma nonneg (x : R) : 0 ≤ f x := f.zero_le_map' x

@[simp]
lemma eq_zero_iff {x : R} : f x = 0 ↔ x = 0 := f.map_eq_zero_iff' x

@[simp]
lemma map_zero : f 0 = 0 := f.eq_zero_iff.mpr rfl

lemma map_ne_zero {x : R} : f x ≠ 0 ↔ x ≠ 0 :=
not_iff_not.mpr f.eq_zero_iff

/-- `simp`-normal form version of `f.map_ne_zero` -/
@[simp]
lemma map_ne_zero' {x : R} : ¬ (f x = 0) ↔ ¬ (x = 0) :=
f.map_ne_zero

lemma pos {x : R} (hx : x ≠ 0) : 0 < f x :=
lt_of_le_of_ne (f.nonneg x) (f.map_ne_zero.mpr hx).symm

@[simp]
lemma map_mul (x y : R) : f (x * y) = f x * f y := f.map_mul' x y

lemma le_add (x y : R) : f (x + y) ≤ f x + f y := f.map_add_le' x y

@[simp]
lemma map_lt_map_iff {x y : R} : f x < f y ↔ x ≺ y := f.map_lt_map_iff' x y

lemma sub_mod_lt (a : R) {b : R} (hb : b ≠ 0) :
  f (a % b) < f b :=
f.map_lt_map_iff.mpr (euclidean_domain.mod_lt a hb)

@[simp]
lemma map_sub_eq_zero_iff (a b : R) :
  f (a - b) = 0 ↔ a = b :=
f.eq_zero_iff.trans sub_eq_zero

variables {K : Type*} [field K]

/-- Lift a euclidean absolute value to an absolute value on the fraction field,
by sending `f (a / b)` to `f a / f b`. -/
noncomputable def to_frac (f : euclidean_absolute_value R ℤ) (g : fraction_map R K) :
  absolute_value g.codomain ℚ :=
f.to_absolute_value.to_frac g

@[simp] lemma to_frac_mk' (f : euclidean_absolute_value R ℤ) (g : fraction_map R K)
  (x : R) (y : non_zero_divisors R) :
  f.to_frac g (g.mk' x y) = f x / f y :=
f.to_absolute_value.to_frac_mk' g x y

@[simp] lemma to_frac_to_map (f : euclidean_absolute_value R ℤ) (g : fraction_map R K)
  (x : R) : f.to_frac g (g.to_map x) = f x :=
f.to_absolute_value.to_frac_to_map g x

end euclidean_domain

end euclidean_absolute_value

namespace fraction_map

variables {R S K : Type*} [euclidean_domain R] [ordered_semiring S] [field K]
variables (f : fraction_map R K) (abs : euclidean_absolute_value R ℤ) -- TODO: generalize to any S

/-- The integral part of `x : f.codomain` according to an euclidean absolute value `abs : R → S`,
is a `q ∶ R` such that `abs (x - q) < 1`. -/
noncomputable def integral_part (x : f.codomain) : R :=
f.num x / f.denom x

#print euclidean_domain

lemma integral_part_mk' (a : R) (b : non_zero_divisors R) :
  f.integral_part (f.mk' a b) = a / b :=
sorry

lemma to_frac_lt_one {x : f.codomain}
  (h : ∀ (a : R) (b : non_zero_divisors R), f.mk' a b = x → abs a < abs b) :
  abs.to_frac f x < 1 :=
begin
  obtain ⟨a, b, eq_x⟩ := f.mk'_surjective x,
  specialize h a b eq_x,
  have hb' : 0 < abs.to_frac f (f.to_map b),
  { exact (abs.to_frac f).pos (f.to_map_ne_zero_of_mem_non_zero_divisors b) },
  rwa [← mul_lt_mul_right hb', one_mul, ← (abs.to_frac f).map_mul, ← eq_x,
      f.mk'_spec, abs.to_frac_to_map, abs.to_frac_to_map, int.cast_lt],
end

/-- The integral part of `x : f.codomain` according to an euclidean absolute value `abs : R → S`,
is a `q ∶ R` such that `abs (x - q) < 1`. -/
lemma sub_integral_part_le (x : f.codomain) :
  abs.to_frac f (x - f.to_map (f.integral_part x)) < 1 :=
begin
  obtain ⟨a, b, rfl⟩ := f.mk'_surjective x,
  have hb' : 0 < abs.to_frac f (f.to_map b),
  { apply (abs.to_frac f).pos,
    exact f.to_map_ne_zero_of_mem_non_zero_divisors b },
  rw [integral_part_mk', ← mul_lt_mul_right hb', one_mul, ← (abs.to_frac f).map_mul, sub_mul,
      f.mk'_spec, ← ring_hom.map_mul, ← ring_hom.map_sub, abs.to_frac_to_map, abs.to_frac_to_map,
      int.cast_lt, abs.map_lt_map_iff, mul_comm (a / b) b, ← euclidean_domain.mod_eq_sub_mul_div],
  exact euclidean_domain.mod_lt a (ne_zero_of_mem_non_zero_divisors b.2)
end

end fraction_map

section det

open equiv finset matrix

variables {R S : Type*} [comm_ring R] [nontrivial R] [linear_ordered_comm_ring S]
variables {n : Type*} [fintype n] [decidable_eq n]

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

section
variables (L) (f)
include f
def integral_closure.basis : finset (integral_closure R L) := sorry

lemma integral_closure.is_basis :
  is_basis R (coe : (↑(integral_closure.basis L f) : set (integral_closure R L)) → integral_closure R L) :=
sorry
end

end div_with_rem

section norm

section comm_ring

variables {R A : Type*} [comm_ring R] [ring A] [algebra R A]
variables {ι : Type*} [fintype ι] [decidable_eq ι] {b : ι → A} (hb : is_basis R b)

noncomputable def algebra.norm : A →* R :=
{ to_fun := λ x, matrix.det (linear_map.to_matrix hb hb (algebra.lmul R A x)),
  map_one' := by rw [alg_hom.map_one, show (1 : A →ₗ[R] A) = linear_map.id, from rfl,
                     linear_map.to_matrix_id, matrix.det_one],
  map_mul' := λ x y, by rw [alg_hom.map_mul, linear_map.to_matrix_mul, matrix.det_mul]}

end comm_ring

section integral_domain

variables {R A : Type*} [integral_domain R] [integral_domain A] [algebra R A]
variables {ι : Type*} [fintype ι] [decidable_eq ι] {b : ι → A} (hb : is_basis R b)

lemma matrix.det_eq_zero_iff_exists_mul_vec_eq_zero {M : matrix ι ι R} :
  M.det = 0 ↔ ∃ (v ≠ 0), M.mul_vec v = 0 :=
sorry

lemma linear_map.to_matrix_mul_vec {l : A →ₗ[R] A} (v : ι → R) :
  (linear_map.to_matrix hb hb l).mul_vec v = hb.repr (l (∑ i, v i • b i)) :=
begin
  show matrix.to_lin' (linear_map.to_matrix' (hb.equiv_fun.arrow_congr hb.equiv_fun l)) v = _,
  ext i,
  rw [matrix.to_lin'_to_matrix', linear_equiv.arrow_congr_apply, hb.equiv_fun_apply,
      hb.equiv_fun_symm_apply]
end

lemma algebra.norm_eq_zero_iff {x : A} : algebra.norm hb x = 0 ↔ x = 0 :=
begin
  split,
  { intro h,
    obtain ⟨v, hv, mul_eq⟩ := matrix.det_eq_zero_iff_exists_mul_vec_eq_zero.mp h,
    have : x * ∑ i, (v i • b i) = 0,
    { simp only [linear_map.to_matrix_mul_vec, linear_map.map_sum, algebra.lmul_apply] at mul_eq,
      have : hb.repr (x * ∑ i, v i • b i) = 0,
      { ext j, exact congr_fun mul_eq j },
      rwa hb.repr_eq_zero at this },
    refine (eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_right (mt _ hv),
    intro h,
    ext i,
    apply linear_independent_iff'.mp hb.1 _ _ h _ (finset.mem_univ i) },
  { rintro rfl,
    have : nonempty ι := sorry,
    simp [algebra.norm, matrix.det_zero this] }
end

lemma algebra.norm_ne_zero {x : A} : algebra.norm hb x ≠ 0 ↔ x ≠ 0 :=
not_iff_not.mpr (algebra.norm_eq_zero_iff hb)

end integral_domain

end norm

section euclidean_domain

variables {R K L : Type*} [euclidean_domain R] [field K] [field L]
variables (f : fraction_map R K)
variables [algebra f.codomain L] [finite_dimensional f.codomain L]
variables [algebra R L] [is_scalar_tower R f.codomain L]
variables (abs : euclidean_absolute_value R ℤ)

noncomputable def abs_norm [decidable_eq L] (x : integral_closure R L) : ℤ :=
abs (@algebra.norm R (integral_closure R L) _ _ _ _ _ _ _ (integral_closure.is_basis L f) x)

noncomputable def abs_frac_norm [decidable_eq L] (x : L) : ℚ :=
abs.to_frac f (algebra.norm (is_basis_coe f (integral_closure.is_basis L f)) x)

lemma abs_frac_norm_coe [decidable_eq L] (x : integral_closure R L) :
  abs_frac_norm f abs (x : L) = abs_norm f abs x :=
begin
  unfold abs_frac_norm abs_norm,
  sorry
end

/-- If `L` is a finite dimensional extension of the field of fractions of a Euclidean domain `R`,
there is a function mapping each `x : L` to the "closest" value that is integral over `R`. -/
noncomputable def integral_part (x : L) : integral_closure R L :=
∑ i, f.integral_part ((is_basis_coe f (integral_closure.is_basis L f)).repr x i) • i

variables [decidable_eq L]

section

variables (L)

include L f abs

def finset_approx : finset R := sorry

end

-- Theorem 4.1
lemma finset_approx.zero_not_mem : (0 : R) ∉ finset_approx L f abs := sorry

theorem exists_mem_finset_approx (g : L) :
  ∃ (q : integral_closure R L) (r ∈ finset_approx L f abs),
    abs_frac_norm f abs (r • g - q) < 1 :=
sorry

-- Corollary 4.2
theorem exists_mem_finset_approx' (a : integral_closure R L) {b}
  (hb : b ≠ (0 : integral_closure R L)) :
  ∃ (q : integral_closure R L) (r ∈ finset_approx L f abs),
    abs_norm f abs (r • a - q * b) < abs_norm f abs b :=
begin
  obtain ⟨q, r, hr, hrgq⟩ := exists_mem_finset_approx f abs (a / b : L),
  use [q, r, hr],
  unfold abs_frac_norm abs_norm at hrgq,
  have h_coe_b : (b : L) ≠ 0,
  { rwa [ne.def, submodule.coe_eq_zero] },
  have hb' : 0 < abs_frac_norm f abs (b : L),
  { exact (abs.to_frac f).pos ((algebra.norm_ne_zero _).mpr h_coe_b) },
  rw [← mul_lt_mul_right hb', one_mul] at hrgq,
  unfold abs_frac_norm at hrgq,
  rw [← (abs.to_frac f).map_mul, ← (algebra.norm _).map_mul, sub_mul, mul_comm, ← smul_eq_mul,
      smul_comm, smul_eq_mul, ← mul_div_assoc, mul_div_cancel_left _ h_coe_b] at hrgq,
  rw [← @int.cast_lt ℚ, ← abs_frac_norm_coe, ← abs_frac_norm_coe],
  unfold abs_frac_norm,
  exact_mod_cast hrgq
end

end euclidean_domain


section class_group

section integral_domain

variables {R K L : Type*} [integral_domain R]
variables [field K] [field L] [decidable_eq L]
variables (f : fraction_map R K)
variables [algebra f.codomain L] [finite_dimensional f.codomain L]
variables [algebra R L] [is_scalar_tower R f.codomain L]

open ring.fractional_ideal units

section
/-- `to_principal_ideal x` sends `x ≠ 0 : K` to the fractional ideal generated by `x` -/
@[irreducible]
def to_principal_ideal : units f.codomain →* units (fractional_ideal f) :=
{ to_fun := λ x,
  ⟨ span_singleton x,
    span_singleton x⁻¹,
    by simp only [span_singleton_one, units.mul_inv', span_singleton_mul_span_singleton],
    by simp only [span_singleton_one, units.inv_mul', span_singleton_mul_span_singleton]⟩,
  map_mul' := λ x y, ext (by simp only [units.coe_mk, units.coe_mul, span_singleton_mul_span_singleton]),
  map_one' := ext (by simp only [span_singleton_one, units.coe_mk, units.coe_one]) }

local attribute [semireducible] to_principal_ideal

variables {f}

@[simp] lemma coe_to_principal_ideal (x : units f.codomain) :
  (to_principal_ideal f x : fractional_ideal f) = span_singleton x :=
rfl

@[simp] lemma to_principal_ideal_eq_iff {I : units (fractional_ideal f)} {x : units f.codomain} :
  to_principal_ideal f x = I ↔ span_singleton (x : f.codomain) = I :=
units.ext_iff

end

instance principal_ideals.normal : (to_principal_ideal f).range.normal :=
subgroup.normal_of_comm _

section
/-- The class group with respect to `f : fraction_map R K`
is the group of invertible fractional ideals modulo the principal ideals. -/
@[derive(comm_group)]
def class_group := quotient_group.quotient (to_principal_ideal f).range

@[simp] lemma fractional_ideal.coe_to_fractional_ideal_top :
  ((⊤ : ideal R) : fractional_ideal f) = 1 :=
by { rw [← ideal.one_eq_top], refl }

@[simp] lemma units.mk0_one {M : Type*} [group_with_zero M] (h) :
  units.mk0 (1 : M) h = 1 :=
by { ext, refl }

@[simp] lemma units.mk0_map {M : Type*} [group_with_zero M] (x y : M) (hxy) :
  mk0 (x * y) hxy = mk0 x (mul_ne_zero_iff.mp hxy).1 * mk0 y (mul_ne_zero_iff.mp hxy).2 :=
by { ext, refl }

/-- The monoid of nonzero ideals. -/
def nonzero_ideal (R : Type*) [integral_domain R] : submonoid (ideal R) :=
{ carrier := {I | I ≠ ⊥},
  one_mem' := show (1 : ideal R) ≠ ⊥, by { rw ideal.one_eq_top, exact submodule.bot_ne_top.symm },
  mul_mem' := λ I J (hI : I ≠ ⊥) (hJ : J ≠ ⊥), show I * J ≠ ⊥,
    by { obtain ⟨x, x_mem, x_ne⟩ := I.ne_bot_iff.mp hI,
         obtain ⟨y, y_mem, y_ne⟩ := J.ne_bot_iff.mp hJ,
         exact (submodule.ne_bot_iff _).mpr
           ⟨x * y, ideal.mul_mem_mul x_mem y_mem, mul_ne_zero x_ne y_ne⟩ } }

/-- Send a nonzero ideal to the corresponding class in the class group. -/
noncomputable def class_group.mk [is_dedekind_domain R] :
  nonzero_ideal R →* class_group f :=
(quotient_group.mk' _).comp
  { to_fun := λ I, units.mk0 I
      ((fractional_ideal.coe_to_fractional_ideal_ne_zero (le_refl (non_zero_divisors R))).mpr I.2),
    map_one' := by simp,
    map_mul' := λ x y, by simp }

lemma quotient_group.mk'_eq_mk' {G : Type*} [group G] {N : subgroup G} [hN : N.normal] {x y : G} :
  quotient_group.mk' N x = quotient_group.mk' N y ↔ ∃ z ∈ N, x * z = y :=
(@quotient.eq _ (quotient_group.left_rel _) _ _).trans
  ⟨λ (h : x⁻¹ * y ∈ N), ⟨_, h, by rw [← mul_assoc, mul_right_inv, one_mul]⟩,
   λ ⟨z, z_mem, eq_y⟩,
     by { rw ← eq_y, show x⁻¹ * (x * z) ∈ N, rwa [← mul_assoc, mul_left_inv, one_mul] }⟩

lemma class_group.mk_eq_mk_iff [is_dedekind_domain R]
  (I J : nonzero_ideal R) :
  class_group.mk f I = class_group.mk f J ↔
    ∃ (x y : R) (hx : x ≠ 0) (hy : y ≠ 0), ideal.span {x} * (I : ideal R) = ideal.span {y} * J :=
begin
  simp only [class_group.mk, monoid_hom.comp_apply, monoid_hom.coe_mk, quotient_group.mk'_eq_mk',
             exists_prop, monoid_hom.mem_range],
  split,
  { rintros ⟨z, ⟨xy, hxy, rfl⟩, eq_J⟩,
    have hx : (f.to_localization_map.sec (xy : f.codomain)).1 ≠ 0,
    { suffices : f.to_map (f.to_localization_map.sec (xy : f.codomain)).1 ≠ 0,
      { refine mt (λ h, _) this,
        rw [h, ring_hom.map_zero] },
      rw [ne.def, ← localization_map.sec_spec (xy : f.codomain), mul_eq_zero],
      push_neg,
      use xy.ne_zero,
      exact f.to_map_ne_zero_of_mem_non_zero_divisors _ },
    use [(f.to_localization_map.sec (xy : f.codomain)).1,
         (f.to_localization_map.sec (xy : f.codomain)).2,
         hx,
         ne_zero_of_mem_non_zero_divisors (f.to_localization_map.sec (xy : f.codomain)).2.2],
    apply fractional_ideal.coe_to_fractional_ideal_injective (le_refl (non_zero_divisors R)),
    rw [fractional_ideal.coe_to_fractional_ideal_mul (ideal.span _),
        fractional_ideal.coe_to_fractional_ideal_mul (ideal.span _)],
    all_goals { sorry } },
  { rintros ⟨x, y, hx, hy, h⟩,
    refine ⟨_, ⟨units.mk0 (f.mk' x ⟨y, mem_non_zero_divisors_iff_ne_zero.mpr hy⟩) _, rfl⟩, _⟩,
    { rw [ne.def, f.mk'_eq_iff_eq_mul, zero_mul],
      exact mt (f.to_map.injective_iff.mp f.injective _) hx },
    { ext, sorry } },
end

lemma class_group.mk_surjective [is_dedekind_domain R] : function.surjective (class_group.mk f) :=
begin
  rintros ⟨I⟩,
  obtain ⟨a, a_ne_zero, ha⟩ := I.1.2,
  refine ⟨⟨{ carrier := { x | f.to_map (a * x) ∈ I.1 }, .. }, _⟩, _⟩,
  { simp only [ring_hom.map_zero, set.mem_set_of_eq, mul_zero, ring_hom.map_mul],
    exact submodule.zero_mem I },
  { simp only [ring_hom.map_add, set.mem_set_of_eq, mul_zero, ring_hom.map_mul, mul_add],
    exact λ _ _ ha hb, submodule.add_mem I ha hb },
  { simp only [smul_eq_mul, set.mem_set_of_eq, mul_zero, ring_hom.map_mul, mul_add,
               mul_left_comm (f.to_map a)],
    exact λ c _ hb, submodule.smul_mem I c hb },
  { apply (submodule.ne_bot_iff _).mpr,
    obtain ⟨x, x_ne, x_mem⟩ := exists_ne_zero_mem_is_integer I.ne_zero,
    refine ⟨x, show f.to_map (a * x) ∈ I.1, from _, x_ne⟩,
    rw [ring_hom.map_mul, ← f.algebra_map_eq, ← algebra.smul_def a (algebra_map _ f.codomain x)],
    exact submodule.smul_mem _ _ x_mem },
  { symmetry,
    apply quotient.sound,
    refine ⟨units.mk0 (f.to_map a) (f.to_map_ne_zero_of_mem_non_zero_divisors ⟨a, a_ne_zero⟩), _⟩,
    apply @mul_left_cancel _ _ I,
    rw [← mul_assoc, mul_right_inv, one_mul],
    ext x,
    simp [localization_map.coe_submodule],
    sorry }
end

variables {K' : Type*} [field K'] (f) (f' : fraction_map R K')

lemma monoid_hom.range_eq_top {G H : Type*} [group G] [group H] (f : G →* H) :
  f.range = ⊤ ↔ function.surjective f :=
⟨ λ h y, show y ∈ f.range, from h.symm ▸ subgroup.mem_top y,
  λ h, subgroup.ext (λ x, by simp [h x]) ⟩
end

end integral_domain

section euclidean_domain

variables {R K L : Type*} [euclidean_domain R] [is_dedekind_domain R]
variables [field K] [field L] [decidable_eq L]
variables (f : fraction_map R K)
variables [algebra f.codomain L] [finite_dimensional f.codomain L]
variables [algebra R L] [is_scalar_tower R f.codomain L]
variables (abs : euclidean_absolute_value R ℤ)

-- Lemma 5.1
lemma exists_min (I : nonzero_ideal (integral_closure R L)) :
  ∃ b ∈ I.1, b ≠ 0 ∧ ∀ c ∈ I.1, abs_norm f abs c < abs_norm f abs b → c = 0 :=
begin
  obtain ⟨_, ⟨b, b_mem, b_ne_zero, rfl⟩, min⟩ :=
    @int.exists_least_of_bdd (λ a, ∃ b ∈ I.1, b ≠ 0 ∧ abs_norm f abs b = a) _ _,
  { use [b, b_mem, b_ne_zero],
    intros c hc lt,
    by_contra c_ne_zero,
    exact not_le_of_gt lt (min _ ⟨c, hc, c_ne_zero, rfl⟩) },
  { use 0,
    rintros _ ⟨b, b_mem, b_ne_zero, rfl⟩,
    apply abs.nonneg },
  { obtain ⟨b, b_mem, b_ne_zero⟩ := I.1.ne_bot_iff.mp I.2,
    exact ⟨_, ⟨b, b_mem, b_ne_zero, rfl⟩⟩ }
end

instance : is_dedekind_domain (integral_closure R L) := sorry

lemma is_scalar_tower.algebra_map_injective {R S T : Type*}
  [comm_semiring R] [comm_semiring S] [comm_semiring T]
  [algebra R S] [algebra S T] [algebra R T]
  [is_scalar_tower R S T]
  (hRS : function.injective (algebra_map R S)) (hST : function.injective (algebra_map S T)) :
  function.injective (algebra_map R T) :=
by { rw is_scalar_tower.algebra_map_eq R S T, exact hST.comp hRS }

lemma subalgebra.algebra_map_injective {R S : Type*} [comm_semiring R] [comm_semiring S]
  [algebra R S] (A : subalgebra R S) (h : function.injective (algebra_map R S)) :
  function.injective (algebra_map R A) :=
begin
  intros x y hxy,
  apply h,
  simp only [is_scalar_tower.algebra_map_apply R A S],
  exact congr_arg (coe : A → S) hxy
end

lemma integral_closure.algebra_map_injective :
  function.injective (algebra_map R (integral_closure R L)) :=
(subalgebra.algebra_map_injective _
  (is_scalar_tower.algebra_map_injective
    (show function.injective (algebra_map R f.codomain), from f.injective)
    (algebra_map f.codomain L).injective))

lemma cancel_monoid_with_zero.dvd_of_mul_dvd_mul_left {G₀ : Type*} [cancel_monoid_with_zero G₀]
  {a b c : G₀} (ha : a ≠ 0) (h : a * b ∣ a * c) :
  b ∣ c :=
begin
  obtain ⟨d, hd⟩ := h,
  refine ⟨d, mul_left_cancel' ha _⟩,
  rwa mul_assoc at hd
end

lemma ideal.dvd_of_mul_dvd_mul_left {R : Type*} [integral_domain R] [is_dedekind_domain R]
  {I J K : ideal R} (hI : I ≠ ⊥)
  (h : I * J ∣ I * K) :
  J ∣ K :=
cancel_monoid_with_zero.dvd_of_mul_dvd_mul_left hI h

lemma ideal.span_singleton_ne_bot {R : Type*} [comm_ring R] {a : R} (ha : a ≠ 0) :
  ideal.span ({a} : set R) ≠ ⊥ :=
begin
  rw [ne.def, ideal.span_eq_bot],
  push_neg,
  exact ⟨a, set.mem_singleton a, ha⟩
end

lemma finset.dvd_prod {ι M : Type*} [comm_monoid M] {x : ι} {s : finset ι}
  (hx : x ∈ s) (f : ι → M) :
  f x ∣ ∏ i in s, f i :=
multiset.dvd_prod (multiset.mem_map.mpr ⟨x, hx, rfl⟩)

-- Theorem 5.2
theorem exists_mul_eq_mul (I : nonzero_ideal (integral_closure R L)) :
  ∃ (J : nonzero_ideal (integral_closure R L)),
  class_group.mk (integral_closure.fraction_map_of_finite_extension L f) I =
    class_group.mk (integral_closure.fraction_map_of_finite_extension L f) J ∧
    J.1 ∣ ideal.span {algebra_map _ _ (∏ m in finset_approx L f abs, m)} :=
begin
  set m := ∏ m in finset_approx L f abs, m with m_eq,
  obtain ⟨b, b_mem, b_ne_zero, b_min⟩ := exists_min f abs I,
  suffices : ideal.span {b} ∣ ideal.span {algebra_map _ _ m} * I.1,
  { obtain ⟨J, hJ⟩ := this,
    refine ⟨⟨J, _⟩, _, _⟩,
    { sorry },
    { rw class_group.mk_eq_mk_iff,
      refine ⟨algebra_map _ _ m, b, _, b_ne_zero, hJ⟩,
      refine mt ((algebra_map R _).injective_iff.mp (integral_closure.algebra_map_injective f) _) _,
      rw finset.prod_eq_zero_iff,
      push_neg,
      intros a ha a_eq,
      rw a_eq at ha,
      exact finset_approx.zero_not_mem f abs ha },
    apply ideal.dvd_of_mul_dvd_mul_left (ideal.span_singleton_ne_bot b_ne_zero),
    rw [ideal.dvd_iff_le, ← hJ, mul_comm, m_eq],
    apply ideal.mul_left_mono,
    rw [ideal.span_le, set.singleton_subset_iff],
    exact b_mem },
  rw [ideal.dvd_iff_le, ideal.mul_le],
  intros r' hr' a ha,
  rw ideal.mem_span_singleton at ⊢ hr',
  obtain ⟨q, r, r_mem, lt⟩ := exists_mem_finset_approx' f abs a b_ne_zero,
  apply @dvd_of_mul_left_dvd _ _ q,
  rw algebra.smul_def at lt,
  rw ← sub_eq_zero.mp (b_min _ (I.1.sub_mem (I.1.mul_mem_left ha) (I.1.mul_mem_left b_mem)) lt),
  refine mul_dvd_mul_right (dvd_trans (ring_hom.map_dvd _ _) hr') _,
  exact finset.dvd_prod r_mem (λ x, x)
end

-- Theorem 5.3
instance : fintype (class_group f) :=
_

end euclidean_domain

end class_group

#lint

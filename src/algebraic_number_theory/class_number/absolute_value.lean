import ring_theory.localization

open_locale big_operators

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

@[simp]
lemma map_pow [nontrivial R] (f : absolute_value R S) (x : R) (n : ℕ) : f (x ^ n) = f x ^ n :=
f.to_monoid_hom.map_pow x n

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

noncomputable def to_frac_aux {R K : Type*} [nontrivial R] [comm_ring R] [field K]
  (f : absolute_value R ℤ) (g : fraction_map R K) :=
@submonoid.localization_map.lift _ _ _ _ _ _ _ g.to_localization_map
  ((algebra_map ℤ ℚ).to_monoid_hom.comp f.to_monoid_hom)
  (λ ⟨y, hy⟩, is_unit.mk0 _
    (by simpa only [int.cast_eq_zero, eq_zero_iff, ring_hom.eq_int_cast, ring_hom.coe_monoid_hom,
                    ring_hom.to_monoid_hom_eq_coe, function.comp_app, ne.def, coe_fn_to_monoid_hom,
                    monoid_hom.coe_comp]
          using non_zero_divisors.ne_zero_of_mem hy))

@[simp]
lemma to_frac_aux_mk' {R K : Type*} [nontrivial R] [comm_ring R] [field K]
  (f : absolute_value R ℤ) (g : fraction_map R K) (a : R) (b : non_zero_divisors R) :
  f.to_frac_aux g (g.mk' a b) = f a / f b :=
(submonoid.localization_map.lift_mk' _ _ _ _).trans
  (by simp [is_unit.coe_lift_right, div_eq_mul_inv])
.

@[simp]
lemma fraction_map.mk'_eq_zero_iff {R K : Type*} [nontrivial R] [comm_ring R] [field K]
  (g : fraction_map R K) {n d : R} {hd : d ∈ non_zero_divisors R} :
  g.mk' n ⟨d, hd⟩ = 0 ↔ n = 0 :=
by rw [g.mk'_eq_iff_eq_mul, zero_mul, g.to_map_eq_zero_iff]

-- TODO: this could be generalized to extending the codomain from any S to S's fraction field
noncomputable def to_frac {R K : Type*} [nontrivial R] [comm_ring R] [field K]
  (f : absolute_value R ℤ) (g : fraction_map R K) :
  absolute_value g.codomain ℚ :=
{ zero_le_map' := λ x, begin
    obtain ⟨x_n, ⟨x_d, hx_d⟩, rfl⟩ := g.to_localization_map.mk'_surjective x,
    show 0 ≤ f.to_frac_aux g (g.mk' x_n ⟨x_d, hx_d⟩),
    rw [to_frac_aux_mk', div_eq_mul_inv],
    refine mul_nonneg _ (inv_nonneg.mpr _),
    { exact_mod_cast f.nonneg x_n },
    { exact_mod_cast f.nonneg x_d }
  end,
  map_add_le' := λ x y, begin
    obtain ⟨x_n, ⟨x_d, hx_d⟩, rfl⟩ := g.mk'_surjective x,
    obtain ⟨y_n, ⟨y_d, hy_d⟩, rfl⟩ := g.mk'_surjective y,
    rw ← g.mk'_add,
    show f.to_frac_aux g (localization_map.mk' g (x_n * y_d + y_n * x_d) (⟨x_d, hx_d⟩ * ⟨y_d, hy_d⟩)) ≤
      f.to_frac_aux g (localization_map.mk' g x_n ⟨x_d, hx_d⟩) +
      f.to_frac_aux g (localization_map.mk' g y_n ⟨y_d, hy_d⟩),
    have cast_fx_ne : ∀ {x} (hx : x ∈ non_zero_divisors R), (f x : ℚ) ≠ 0 :=
      λ x hx, int.cast_ne_zero.mpr (f.map_ne_zero.mpr (non_zero_divisors.ne_zero_of_mem hx)),
    have : x_d * y_d ≠ 0 := non_zero_divisors.ne_zero_of_mem (submonoid.mul_mem _ hx_d hy_d),
    rw ← mul_le_mul_right ((@int.cast_pos ℚ _ _ _).mpr (f.pos this)),
    simp only [f.to_frac_aux_mk', subtype.coe_mk, submonoid.coe_mul, int.cast_mul, f.map_mul, add_mul],
    convert (@int.cast_le ℚ _ _ _ _).mpr (f.le_add (x_n * y_d) (y_n * x_d)),
    { apply div_mul_cancel,
      rwa [← int.cast_mul, int.cast_ne_zero, ← f.map_mul, f.map_ne_zero] },
    { simp only [f.map_mul, int.cast_mul, int.cast_add],
      congr' 1,
      { rw [← mul_assoc, div_mul_cancel _ (cast_fx_ne hx_d)] },
      { rw [mul_comm (f x_d : ℚ), ← mul_assoc, div_mul_cancel _ (cast_fx_ne hy_d)] } },
  end,
  map_eq_zero_iff' := λ x, begin
    obtain ⟨x_n, ⟨x_d, hx_d⟩, rfl⟩ := g.mk'_surjective x,
    show f.to_frac_aux g (g.mk' x_n ⟨x_d, hx_d⟩) = 0 ↔ g.mk' x_n ⟨x_d, hx_d⟩ = 0,
    simp only [f.to_frac_aux_mk', div_eq_zero_iff, fraction_map.mk'_eq_zero_iff, int.cast_eq_zero,
               f.eq_zero_iff, subtype.coe_mk, non_zero_divisors.ne_zero_of_mem hx_d, or_false],
  end,
  .. to_frac_aux f g }

@[simp]
lemma to_frac_mk' {R K : Type*} [nontrivial R] [comm_ring R] [field K]
  (f : absolute_value R ℤ) (g : fraction_map R K) (a : R) (b : non_zero_divisors R) :
  f.to_frac g (g.mk' a b) = f a / f b :=
f.to_frac_aux_mk' g a b

@[simp]
lemma to_frac_to_map {R K : Type*} [nontrivial R] [comm_ring R] [field K]
  (f : absolute_value R ℤ) (g : fraction_map R K) (a : R) :
  f.to_frac g (g.to_map a) = f a :=
by { rw ← g.mk'_one, simp }

def abs {R : Type*} [linear_ordered_ring R] : absolute_value R R :=
{ to_fun := λ x, abs x,
  map_add_le' := λ x y, abs_add x y,
  map_eq_zero_iff' := λ x, abs_eq_zero,
  map_mul' := λ x y, abs_mul x y,
  zero_le_map' := λ x, abs_nonneg x }

open polynomial

lemma nat_degree_add_le (p q : polynomial R) :
  nat_degree (p + q) ≤ max (nat_degree p) (nat_degree q) :=
le_max_iff.mpr
  ((le_max_iff.mp (polynomial.degree_add_le p q)).imp
    nat_degree_le_nat_degree nat_degree_le_nat_degree)

noncomputable def pow_degree {R : Type*} [integral_domain R] [decidable_eq R]
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
    { refine le_trans (pow_le_pow (le_of_lt hc) (nat_degree_add_le _ _)) _,
      have c_nonneg : 0 ≤ c, { linarith },
      refine le_trans (le_max_iff.mpr _)
        (max_le_add_of_nonneg (pow_nonneg c_nonneg _) (pow_nonneg c_nonneg _)),
      exact (max_choice p.nat_degree q.nat_degree).imp (λ h, by rw [h]) (λ h, by rw [h]) }
  end,
  map_eq_zero_iff' := λ p, begin
    simp only,
    split_ifs with h,
    { simp [h] },
    simp only [h, iff_false],
    apply pow_ne_zero _ (show c ≠ 0, from ne_of_gt _),
    linarith,
  end,
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

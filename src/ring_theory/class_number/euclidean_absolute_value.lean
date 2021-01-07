import ring_theory.class_number.absolute_value

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

@[simp]
lemma mul_denom (x : f.codomain) :
  x * f.to_map (f.denom x) = f.to_map (f.num x) :=
f.num_mul_denom_eq_num_iff_eq.mpr rfl

/-- The integral part of `x : f.codomain` according to an euclidean absolute value `abs : R → S`,
is a `q ∶ R` such that `abs (x - q) < 1`. -/
lemma sub_integral_part_le (x : f.codomain) :
  abs.to_frac f (x - f.to_map (f.integral_part x)) < 1 :=
begin
  set a := f.num x,
  set b := f.denom x,
  have hb' : 0 < abs.to_frac f (f.to_map b),
  { apply (abs.to_frac f).pos,
    exact f.to_map_ne_zero_of_mem_non_zero_divisors b },
  rw [integral_part, ← mul_lt_mul_right hb', one_mul, ← (abs.to_frac f).map_mul, sub_mul,
      mul_denom, ← ring_hom.map_mul, ← ring_hom.map_sub, abs.to_frac_to_map, abs.to_frac_to_map,
      int.cast_lt, abs.map_lt_map_iff, mul_comm (a / b) b, ← euclidean_domain.mod_eq_sub_mul_div],
  exact euclidean_domain.mod_lt a (non_zero_divisors.ne_zero b)
end

end fraction_map

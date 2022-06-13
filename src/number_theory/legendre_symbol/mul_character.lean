/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import ring_theory.integral_domain

/-!
# Multiplicative characters of finite rings and fields

Let `R` be a finite commutative ring.
A *multiplicative character* of `R` with values in `R'` is a morphism of
monoids with zero from the multiplicative monoid of `R` into that of `R'`.

We use the namespace `mul_char` for the definitions and results.

## Tags

multiplicative character
-/

section multiplicative

namespace mul_char

/-!
### Definitions related to and results on multiplicative characters
-/

universes u v w

-- The domain of our multiplicative characters
variables {R : Type u} [comm_ring R]
-- The target
variables {R' : Type v} [comm_ring R']

/-- The trivial multiplicative character. It takes the value `0` on non-units and
the value `1` on units. -/
@[simps]
def trivial [nontrivial R] [decidable_pred (λ x : R, is_unit x)] : R →*₀ R' :=
{ to_fun := λ x, if is_unit x then 1 else 0,
  map_zero' := by simp only [not_is_unit_zero, if_false],
  map_one' := by simp only [is_unit_one, if_true],
  map_mul' := by { intros x y,
                   simp only [is_unit.mul_iff, boole_mul],
                   split_ifs; tauto, } }
attribute [protected] trivial

/-- A multiplicative character is *nontrivial* if it takes a value `≠ 1` on a unit. -/
def is_nontrivial (χ : R →*₀ R') : Prop := ∃ (a : R), is_unit a ∧ χ a ≠ 1

/-- A multiplicative character is *quadratic* if it takes only the values `0`, `1`, `-1`. -/
def is_quadratic (χ : R →*₀ R') : Prop := ∀ a, χ a = 0 ∨ χ a = 1 ∨ χ a = -1

/-- Composition with an injective ring homomorphism preserves nontriviality. -/
lemma is_nontrivial.comp {χ : R →*₀ R'} (hχ : is_nontrivial χ) {R'' : Type w} [comm_ring R'']
  {f : R' →+* R''} (hf : function.injective f) :
   is_nontrivial (f.to_monoid_with_zero_hom.comp χ) :=
begin
  obtain ⟨a, ha₁, ha₂⟩ := hχ,
  refine ⟨a, ha₁, λ ha, ha₂ (hf _)⟩,
  erw [ha, map_one],
end

/-- Composition with a ring homomorphism preserves the property of being a quadratic character. -/
lemma is_quadratic.comp {χ : R →*₀ R'} (hχ : is_quadratic χ) {R'' : Type w} [comm_ring R'']
  (f : R' →+* R'') : is_quadratic (f.to_monoid_with_zero_hom.comp χ) :=
begin
  intro a,
  simp only [monoid_with_zero_hom.coe_comp, ring_hom.to_monoid_with_zero_hom_eq_coe,
             function.comp_app],
  rcases hχ a with (ha | ha | ha); rw [ha],
  { left,
    rw [map_zero], },
  { right, left,
    rw [map_one], },
  { right, right,
    rw [map_neg, map_one], },
end

/-- If `χ` is a quadratic character and `a : R` is a unit, then `(χ a) * (χ a) = 1`. -/
lemma quad_char_sq_eq_one {χ : R →*₀ R'} [nontrivial R'] (hχ : is_quadratic χ)
 {a : R} (ha : is_unit a) : χ a ^ 2 = 1 :=
begin
  rcases hχ a with (h | h | h),
  { have hu := is_unit.map χ ha,
    rw h at hu ⊢,
    exact false.rec _ (is_unit.ne_zero hu rfl), },
  { rw [h, one_pow], },
  { rw [h, neg_one_sq], },
end

/-- For positive `n : ℕ`, define `χ ^ n` as `χ` composed with the `n`the power homomorphism. -/
def pow_pos (χ : R →*₀ R') {n : ℕ} (hn : 0 < n) : R →*₀ R' :=
χ.comp (pow_monoid_with_zero_hom hn)

@[simp]
lemma pow_pos_spec (χ : R →*₀ R') {n : ℕ} (hn : 0 < n) (x : R) :
  pow_pos χ hn x = (χ x) ^ n :=
by simp only [pow_pos, pow_monoid_with_zero_hom_apply, monoid_with_zero_hom.coe_comp,
              monoid_with_zero_hom.coe_mk, function.comp_app, map_pow]

/-- The `p`th power of a quadratic character is itself, when `p` is the (prime) characteristic
of the target ring. -/
lemma quad_char_pow_char {χ : R →*₀ R'} (hχ : is_quadratic χ)
 (p : ℕ) [hp : fact p.prime] [char_p R' p] :
  pow_pos χ hp.1.pos = χ :=
begin
  ext,
  rw [pow_pos_spec],
  rcases hχ x with (hx | hx | hx); rw hx,
  { rw [zero_pow (fact.out p.prime).pos], },
  { rw [one_pow], },
  { exact char_p.neg_one_pow_char R' p, },
end

/-- The `n`th power of a quadratic character is itself, when `n` is odd. -/
lemma quad_char_pow_odd {χ : R →*₀ R'} (hχ : is_quadratic χ) {n : ℕ} (hn : n % 2 = 1) :
  pow_pos χ (nat.odd_gt_zero (nat.odd_iff.mpr hn)) = χ :=
begin
  ext,
  rw [pow_pos_spec],
  rcases hχ x with (hx | hx | hx); rw hx,
  { rw [zero_pow (nat.odd_gt_zero (nat.odd_iff.mpr hn))], },
  { rw [one_pow], },
  { exact odd.neg_one_pow (nat.odd_iff.mpr hn), },
end

/-- The inverse of a multiplicative character. -/
noncomputable
def inv' (χ : R →*₀ R') : R →*₀ R' := χ.comp monoid_with_zero.inverse
attribute [protected] inv'

@[simp]
lemma inv'_spec (χ : R →*₀ R') (a : R) : (inv' χ) a = χ (ring.inverse a) := rfl

/-- When `R` is a field `F`, we can use the standard inverse map. -/
def inv {F : Type u} [field F] (χ : F →*₀ R') : F →*₀ R' := χ.comp (@inv_monoid_with_zero_hom F _)
attribute [protected] inv

@[simp]
lemma inv_spec {F : Type u} [field F] (χ : F →*₀ R') (a : F) : (inv χ) a = χ a⁻¹ := rfl

lemma inv_eq_inv' {F : Type u} [field F] (χ : F →*₀ R') : inv χ = inv' χ :=
begin
  ext x,
  simp only [inv_spec, inv'_spec, ring.inverse_eq_inv'],
end

/-- The product of a character with its inverse is the trivial character. -/
@[simp]
lemma mul_inv [nontrivial R] [decidable_pred (λ (x : R), is_unit x)] (χ : R →*₀ R') :
  χ * (inv' χ) = mul_char.trivial :=
begin
  ext x,
  have h₁ : (χ * (inv' χ)) x = (χ x) * (inv' χ x) := rfl,
  rw [h₁, inv'_spec, ← map_mul, trivial_apply],
  split_ifs,
  { haveI := is_unit.invertible h,
    rw [ring.inverse_invertible, mul_inv_of_self, map_one], },
  { rw [ring.inverse_non_unit x h, mul_zero, map_zero], },
end

/-- The inverse of a quadratic character is itself. -/
lemma quadratic_char_inv {χ : R →*₀ R'} (hχ : is_quadratic χ) (hχ' : ∀ a, χ a ≠ 0 → is_unit a) :
  inv' χ = χ :=
begin
  ext x,
  rw [inv'_spec],
  by_cases hx : is_unit x,
  { haveI := is_unit.invertible hx,
    apply_fun (λ a, a * χ x) using (is_unit.is_regular (is_unit.map χ hx)).right,
    change χ _ * χ x = χ x * χ x,
    rw [← map_mul, ring.inverse_invertible, inv_of_mul_self, map_one],
    rcases hχ x with h₀ | h₁ | h₂,
    { rw [h₀, mul_zero],
      exact (is_unit_zero_iff.mp (cast (congr_arg is_unit h₀) (is_unit.map χ hx))).symm, },
    { rw [h₁, mul_one], },
    { rw [h₂, neg_one_mul, neg_neg], }, },
  { rw [ring.inverse_non_unit x hx, map_zero],
    exact (of_not_not (mt (hχ' x) hx)).symm, },
end

/-- When `R` is a field `F`, then a multiplicative character takes nonzero values
only on units. -/
lemma is_unit_of_ne_zero {F : Type u} [field F] (χ : F →*₀ R') {a : F} (ha : χ a ≠ 0) :
  is_unit a :=
begin
  by_cases h₀ : a = 0,
  { simp only [h₀, map_zero, ne.def, eq_self_iff_true, not_true] at ha,
    exact false.rec (is_unit a) ha, },
  { exact is_unit_iff_ne_zero.mpr h₀, },
end

open_locale big_operators

/-- The sum over all values of a nontrivial multiplicative character is zero. -/
lemma sum_eq_zero_of_is_nontrivial [fintype R] [is_domain R'] {χ : R →*₀ R'}
 (hχ : is_nontrivial χ) : ∑ a, χ a = 0 :=
begin
  rcases hχ with ⟨b, hb₀, hb⟩,
  have h₁ : ∑ a, χ (b * a) = ∑ a, χ a :=
    fintype.sum_bijective _ (units.mul_left_bijective hb₀.unit) _ _ (λ x, rfl),
  simp only [map_mul] at h₁,
  rw [← finset.mul_sum] at h₁,
  exact eq_zero_of_mul_eq_self_left hb h₁,
end

end mul_char

end multiplicative

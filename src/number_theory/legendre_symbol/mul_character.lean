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
monoids with zero from the multiplicative monoid of `R` into that of `R'`
that sends non-units to zero.

We use the namespace `mul_char` for the definitions and results.

## Tags

multiplicative character
-/

section multiplicative

/-!
### Definitions related to and results on multiplicative characters
-/

universes u v w

-- The domain of our multiplicative characters
variables {R : Type u} [comm_ring R]
-- The target
variables {R' : Type v} [comm_ring R']

/-- Define a structure for multiplicative characters.
A multiplicative character from a commutative ring `R` to a commutative ring `R'`
is a homomorphism of (multiplicative) monoids that sends non-units to zero. -/
structure mul_char (R : Type u) [comm_ring R] (R' : Type v) [comm_ring R']
 extends monoid_hom R R' :=
(map_nonunit' : ∀ a : R, ¬ is_unit a → to_fun a = 0)

/-- This is the corresponding extension of `monoid_hom_class`. -/
class mul_char_class (F : Type*) (R R' : out_param $ Type*) [comm_ring R] [comm_ring R']
  extends monoid_hom_class F R R' :=
(map_nonunit : ∀ (χ : mul_char R R') {a : R} (ha : ¬ is_unit a), χ.to_monoid_hom a = 0)

namespace mul_char

instance coe_to_fun : has_coe_to_fun (mul_char R R') (λ _, R → R') :=
⟨λ χ, χ.to_fun⟩

@[simp]
lemma coe_coe (χ : mul_char R R') : (χ.to_monoid_hom : R → R') = χ := rfl

lemma ext' {χ χ' : mul_char R R'} : (∀ a, χ a = χ' a) → χ = χ' :=
begin
  intro h,
  cases χ,
  cases χ',
  congr,
  ext a,
  exact h a,
end

instance mul_char_class : mul_char_class (mul_char R R') R R' :=
{ coe := λ χ, χ.to_monoid_hom.to_fun,
  coe_injective' := λ f g h, ext' (λ a, congr_fun h a),
  map_mul := λ χ, χ.map_mul',
  map_one := λ χ, χ.map_one',
  map_nonunit := λ χ a ha, χ.map_nonunit' a ha, }

lemma map_nonunit (χ : mul_char R R') {a : R} (ha : ¬ is_unit a) : χ a = 0 :=
χ.map_nonunit' a ha

/-!
### Equivalence of multiplicative characters with homomorphisms on units
-/

/-- Since `mul_char`s always take the value zero on non-units, it is sufficient
to compare the values on units. -/
@[ext]
lemma ext {χ χ' : mul_char R R'} : (∀ a, is_unit a → χ a = χ' a) → χ = χ' :=
begin
  intro h,
  apply ext',
  intro a,
  by_cases ha : is_unit a,
  { exact h a ha, },
  { rw [map_nonunit χ ha, map_nonunit χ' ha], },
end

/-- A multiplicative character is the extension by zero of a group homomorphism
between the unit groups of `R` and `R'`. This is the conversion from `mul_char`s. -/
def to_unit_hom (χ : mul_char R R') : Rˣ →* R'ˣ := units.map χ.to_monoid_hom

lemma to_unit_hom_eval (χ : mul_char R R') {a : R} (ha : is_unit a) :
  χ.to_unit_hom ha.unit = (is_unit.map χ ha).unit :=
begin
  simp only [to_unit_hom],
  apply_fun (coe : R'ˣ → R') using units.ext,
  refl,
end

lemma to_unit_hom_eval' (χ : mul_char R R') (a : Rˣ) :
  χ.to_unit_hom a = (is_unit.map χ (units.is_unit a)).unit :=
begin
  simp only [to_unit_hom],
  apply_fun (coe : R'ˣ → R') using units.ext,
  refl,
end

/-- This is the conversion to `mul_char`s. -/
noncomputable
def of_unit_hom [decidable_pred (λ a : R, is_unit a)] (f : Rˣ →* R'ˣ) : mul_char R R' :=
{ to_fun := λ x, if hx : is_unit x then f (is_unit.unit hx) else 0,
  map_one' := by { have h1 : (is_unit.unit is_unit_one : Rˣ) = 1 := units.eq_iff.mp rfl,
                   simp  [h1, dif_pos, units.coe_eq_one, map_one, is_unit_one], },
  map_mul' :=
  begin
    intros x y,
    by_cases hx : is_unit x,
    { simp only [hx, is_unit.mul_iff, true_and, dif_pos],
      by_cases hy : is_unit y,
      { simp only [hy, dif_pos],
        have hm : (is_unit.mul_iff.mpr ⟨hx, hy⟩).unit = hx.unit * hy.unit := units.eq_iff.mp rfl,
        rw [hm, map_mul],
        norm_cast, },
      { simp only [hy, not_false_iff, dif_neg, mul_zero], }, },
    { simp only [hx, is_unit.mul_iff, false_and, not_false_iff, dif_neg, zero_mul], },
  end ,
  map_nonunit' := by { intros a ha, simp only [ha, not_false_iff, dif_neg], }, }

lemma of_unit_hom_eval [decidable_pred (λ a : R, is_unit a)] (f : Rˣ →* R'ˣ)
 {a : R} (ha : is_unit a) :
  of_unit_hom f a = f ha.unit :=
begin
  change (of_unit_hom f).to_fun _ = _,
  simp only [ha, of_unit_hom, units.is_unit, dif_pos, is_unit.unit_of_coe_units],
end

lemma of_unit_hom_eval' [decidable_pred (λ a : R, is_unit a)] (f : Rˣ →* R'ˣ) (a : Rˣ) :
  of_unit_hom f a = f a :=
begin
  change (of_unit_hom f).to_fun _ = _,
  simp only [of_unit_hom, units.is_unit, dif_pos, is_unit.unit_of_coe_units],
end

/-- Set up the equivalence. -/
noncomputable
def equiv_to_unit_hom [decidable_pred (λ a : R, is_unit a)] : mul_char R R' ≃ (Rˣ →* R'ˣ) :=
{ to_fun := to_unit_hom,
  inv_fun := of_unit_hom,
  left_inv :=
  by { intro χ, ext x hx, rw [of_unit_hom_eval _ hx, to_unit_hom_eval, is_unit.unit_spec] },
  right_inv :=
  by { intro f, ext x, rw [to_unit_hom_eval', ← of_unit_hom_eval' f x, is_unit.unit_spec], } }

/-!
### Commutative group structure on multiplicative characters
-/

lemma map_one (χ : mul_char R R') : χ (1 : R) = 1 :=
χ.map_one'

lemma map_zero [nontrivial R] (χ : mul_char R R') : χ (0 : R) = 0 :=
by rw [map_nonunit χ not_is_unit_zero]

/-- The trivial multiplicative character. It takes the value `0` on non-units and
the value `1` on units. -/
@[simps]
def trivial (R : Type u) [comm_ring R] [decidable_pred (λ a : R, is_unit a)]
 (R' : Type v) [comm_ring R'] : mul_char R R' :=
{ to_fun := λ x, if is_unit x then 1 else 0,
  map_nonunit' := by { intros a ha, simp only [ha, if_false], },
  map_one' := by simp only [is_unit_one, if_true],
  map_mul' := by { intros x y,
                   simp only [is_unit.mul_iff, boole_mul],
                   split_ifs; tauto, } }

instance inhabited [decidable_pred (λ a : R, is_unit a)] : inhabited (mul_char R R') :=
  ⟨trivial R R'⟩

instance has_one [decidable_pred (λ a : R, is_unit a)] : has_one (mul_char R R') := ⟨trivial R R'⟩

lemma trivial_unit [decidable_pred (λ a : R, is_unit a)] {a : R} (ha : is_unit a) :
  (1 : mul_char R R') a = 1 :=
begin
  change (mul_char.trivial R R').to_fun a = _,
  simp only [ha, mul_char.trivial, ite_eq_left_iff, not_true, forall_false_left],
end

lemma trivial_nonunit [decidable_pred (λ a : R, is_unit a)] {a : R} (ha : ¬ is_unit a) :
  (1 : mul_char R R') a = 0 :=
begin
  change (mul_char.trivial R R').to_fun a = _,
  simp only [ha, mul_char.trivial, ite_eq_right_iff, forall_false_left],
end

/-- Multiplication of multiplicative characters -/
def mul (χ χ' : mul_char R R') : mul_char R R' :=
{ map_nonunit' :=
  begin
    intros a ha,
    simp only,
    have h : (χ.to_monoid_hom : R → R') = χ := rfl,
    rw [monoid_hom.to_fun_eq_coe, monoid_hom.mul_apply, h, map_nonunit χ ha, zero_mul],
  end,
  ..χ.to_monoid_hom * χ'.to_monoid_hom }

instance has_mul : has_mul (mul_char R R') := ⟨mul⟩

lemma coe_to_fun_mul (χ χ' : mul_char R R') : ⇑(χ * χ') = χ * χ' :=
begin
  ext a,
  change (χ.mul χ').to_fun a = χ.to_fun a * χ'.to_fun a,
  simp only [mul, monoid_hom.to_fun_eq_coe, monoid_hom.mul_apply],
end

lemma one_mul [decidable_pred (λ a : R, is_unit a)] (χ : mul_char R R') :
  (1 : mul_char R R') * χ = χ :=
begin
  ext a ha,
  rw [coe_to_fun_mul, pi.mul_apply, trivial_unit ha, one_mul],
end

lemma mul_one [decidable_pred (λ a : R, is_unit a)] (χ : mul_char R R') : χ * 1 = χ :=
begin
  ext a ha,
  rw [coe_to_fun_mul, pi.mul_apply, trivial_unit ha, mul_one],
end

instance mul_one_class [decidable_pred (λ a : R, is_unit a)] : mul_one_class (mul_char R R') :=
{ one_mul := one_mul,
  mul_one := mul_one,
  ..has_one,
  ..has_mul }

instance semigroup : semigroup (mul_char R R') :=
{ mul_assoc := by { intros χ₁ χ₂ χ₃, ext a, repeat {rw [coe_to_fun_mul]}, rw [mul_assoc], },
  ..has_mul }

instance monoid [decidable_pred (λ a : R, is_unit a)] : monoid (mul_char R R') :=
{ ..mul_one_class,
  ..semigroup }

instance comm_semigroup : comm_semigroup (mul_char R R') :=
{ mul_comm := by { intros χ₁ χ₂, ext a, repeat {rw [coe_to_fun_mul]}, rw [mul_comm], },
  ..semigroup }

instance comm_monoid [decidable_pred (λ a : R, is_unit a)] : comm_monoid (mul_char R R') :=
{ ..monoid,
  ..comm_semigroup }

/-- The inverse of a multiplicative character. -/
noncomputable -- noncomputable forced by `ring.inverse` even with `[decidable_pred is_unit]`
def inv (χ : mul_char R R') : mul_char R R' :=
{ map_nonunit' :=
  begin
    intros a,
    simp only [monoid_hom.to_fun_eq_coe, monoid_hom.coe_comp, function.comp_app,
               monoid_with_zero_hom.to_monoid_hom_coe, monoid_with_zero.coe_inverse, coe_coe],
    nontriviality R,
    intro ha,
    rw [ring.inverse_non_unit a ha, map_nonunit χ not_is_unit_zero],
  end,
  ..χ.to_monoid_hom.comp monoid_with_zero.inverse.to_monoid_hom }

@[simp]
lemma inv_spec (χ : mul_char R R') (a : R) : (inv χ) a = χ (ring.inverse a) := rfl

noncomputable
instance has_inv : has_inv (mul_char R R') := ⟨inv⟩

noncomputable
instance div_inv_monoid [decidable_pred (λ a : R, is_unit a)] : div_inv_monoid (mul_char R R') :=
{ ..monoid,
  ..has_inv }

/-- The product of a character with its inverse is the trivial character. -/
@[simp]
lemma inv_mul [decidable_pred (λ a : R, is_unit a)] (χ : mul_char R R') : (inv χ) * χ = 1 :=
begin
  ext x hx,
  simp only [coe_to_fun_mul, pi.mul_apply, inv_spec],
  have h : χ (ring.inverse x) * χ x = χ (ring.inverse x * x) :=
  by { change χ.to_monoid_hom.to_fun (ring.inverse x) * χ.to_monoid_hom.to_fun x
               = χ.to_monoid_hom.to_fun (ring.inverse x * x),
       rw [χ.map_mul'], },
  haveI := is_unit.invertible hx,
  rw [h, ring.inverse_invertible, inv_of_mul_self, map_one, trivial_unit hx],
end

noncomputable
instance group [decidable_pred (λ a : R, is_unit a)] : group (mul_char R R') :=
{ mul_left_inv := inv_mul,
  ..div_inv_monoid }

noncomputable
instance comm_group [decidable_pred (λ a : R, is_unit a)] : comm_group (mul_char R R') :=
{ ..group,
  ..comm_monoid }

lemma mul_apply (χ χ' : mul_char R R') (a : R) : (χ * χ') a = χ a * χ' a := rfl

/-- If `a` is a unit, then `(χ ^ n) a = (χ a) ^ n`. -/
lemma pow_apply [decidable_pred (λ a : R, is_unit a)] (χ : mul_char R R') (n : ℕ)
 {a : R} (ha : is_unit a) :
  (χ ^ n) a = (χ a) ^ n :=
begin
  induction n with n ih,
  { rw [pow_zero, pow_zero, trivial_unit ha], },
  { rw [pow_succ, pow_succ, mul_apply, ih], },
end

/-!
### Properties of multiplicative characters
-/

/-- A multiplicative character is *nontrivial* if it takes a value `≠ 1` on a unit. -/
def is_nontrivial (χ : mul_char R R') : Prop := ∃ (a : R), is_unit a ∧ χ a ≠ 1

/-- A multiplicative character is nontrivial iff it is not the trivial character. -/
lemma is_nontrivial_iff [decidable_pred (λ a : R, is_unit a)] (χ : mul_char R R') :
  χ.is_nontrivial ↔ χ ≠ 1 :=
begin
  split,
  { intros h₁ h₂,
    obtain ⟨a, ha₁, ha₂⟩ := h₁,
    rw [h₂, trivial_unit ha₁] at ha₂,
    exact ha₂ rfl, },
  { contrapose!,
    intro h,
    change ¬ ∃ a, is_unit a ∧ χ a ≠ 1 at h,
    push_neg at h,
    ext a ha,
    rw [trivial_unit ha, h a ha], },
end

/-- A multiplicative character is *quadratic* if it takes only the values `0`, `1`, `-1`. -/
def is_quadratic (χ : mul_char R R') : Prop := ∀ a, χ a = 0 ∨ χ a = 1 ∨ χ a = -1

/-- We can post-compose a multiplicative character with a ring homomorphism. -/
-- I can't let `R'` have universe `w` here -- why?
def ring_hom_comp (χ : mul_char R R') {R'' : Type v} [comm_ring R''] (f : R' →+* R'') :
  mul_char R R'' :=
{ map_nonunit' :=
  begin
    intros a ha,
    simp only [ring_hom.to_monoid_hom_eq_coe, monoid_hom.to_fun_eq_coe, monoid_hom.coe_comp,
               ring_hom.coe_monoid_hom, coe_coe, function.comp_app],
    rw [map_nonunit χ ha, ring_hom.map_zero],
  end,
  ..f.to_monoid_hom.comp χ.to_monoid_hom}

@[simp]
lemma ring_hom_comp_apply (χ : mul_char R R') {R'' : Type v} [comm_ring R''] (f : R' →+* R'')
 (a : R) :
  χ.ring_hom_comp f a = f (χ a) := rfl

/-- Composition with an injective ring homomorphism preserves nontriviality. -/
lemma is_nontrivial.comp {χ : mul_char R R'} (hχ : is_nontrivial χ) {R'' : Type v} [comm_ring R'']
  {f : R' →+* R''} (hf : function.injective f) :
   is_nontrivial (χ.ring_hom_comp f) :=
begin
  obtain ⟨a, ha₁, ha₂⟩ := hχ,
  refine ⟨a, ha₁, λ ha, ha₂ (hf _)⟩,
  rw [ring_hom_comp_apply] at ha,
  rw [ha, ring_hom.map_one],
end

/-- Composition with a ring homomorphism preserves the property of being a quadratic character. -/
lemma is_quadratic.comp {χ : mul_char R R'} (hχ : is_quadratic χ) {R'' : Type v} [comm_ring R'']
 (f : R' →+* R'') :
  is_quadratic (χ.ring_hom_comp f) :=
begin
  intro a,
  simp only [ring_hom_comp_apply],
  rcases hχ a with (ha | ha | ha); rw [ha],
  { left,
    rw [ring_hom.map_zero], },
  { right, left,
    rw [ring_hom.map_one], },
  { right, right,
    rw [ring_hom.map_neg, ring_hom.map_one], },
end

/-- The square of a quadratic character is the trivial character. -/
lemma quad_char_sq_eq_one [decidable_pred (λ a : R, is_unit a)] {χ : mul_char R R'} [nontrivial R']
 (hχ : is_quadratic χ) :
  χ ^ 2 = 1 :=
begin
  ext a ha,
  rw [pow_apply χ 2 ha],
  rcases hχ a with (h | h | h); rw [trivial_unit ha],
  { have hu := is_unit.map χ ha,
    rw h at hu ⊢,
    exact false.rec _ (is_unit.ne_zero hu rfl), },
  { rw [h, one_pow], },
  { rw [h, neg_one_sq], },
end

/-- The `p`th power of a quadratic character is itself, when `p` is the (prime) charactersitic
of the target ring. -/
lemma quad_char_pow_char [decidable_pred (λ a : R, is_unit a)] {χ : mul_char R R'}
 (hχ : is_quadratic χ) (p : ℕ) [hp : fact p.prime] [char_p R' p] :
  χ ^ p = χ :=
begin
  ext x h,
  rw [pow_apply _ _ h],
  rcases hχ x with (hx | hx | hx); rw hx,
  { rw [zero_pow (fact.out p.prime).pos], },
  { rw [one_pow], },
  { exact char_p.neg_one_pow_char R' p, },
end

/-- The `n`th power of a quadratic character is itself, when `n` is odd. -/
lemma quad_char_pow_odd [decidable_pred (λ a : R, is_unit a)] {χ : mul_char R R'}
 (hχ : is_quadratic χ) {n : ℕ} (hn : n % 2 = 1) :
  χ ^ n = χ :=
begin
  ext x h,
  rw [pow_apply _ _ h],
  rcases hχ x with (hx | hx | hx); rw hx,
  { rw [zero_pow (nat.odd_gt_zero (nat.odd_iff.mpr hn))], },
  { rw [one_pow], },
  { exact odd.neg_one_pow (nat.odd_iff.mpr hn), },
end

/-- The inverse of a quadratic character is itself. -/
lemma quadratic_char_inv {χ : mul_char R R'} (hχ : is_quadratic χ) : χ⁻¹ = χ :=
begin
  ext x hx,
  change (inv χ) x = _,
  rw [inv_spec],
  haveI := is_unit.invertible hx,
  apply_fun (λ a, a * χ x) using (is_unit.is_regular (is_unit.map χ hx)).right,
  change χ _ * χ x = χ x * χ x,
  rw [← map_mul, ring.inverse_invertible, inv_of_mul_self, map_one],
  rcases hχ x with h₀ | h₁ | h₂,
  { rw [h₀, mul_zero],
    exact (is_unit_zero_iff.mp (cast (congr_arg is_unit h₀) (is_unit.map χ hx))).symm, },
  { rw [h₁, ring.mul_one], },
  { rw [h₂, neg_one_mul, neg_neg], },
end

open_locale big_operators

/-- The sum over all values of a nontrivial multiplicative character is zero. -/
lemma sum_eq_zero_of_is_nontrivial [fintype R] [is_domain R'] {χ : mul_char R R'}
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

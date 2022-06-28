/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import ring_theory.integral_domain

/-!
# Multiplicative characters of finite rings and fields

Let `R` and `R'` be a commutative rings.
A *multiplicative character* of `R` with values in `R'` is a morphism of
monoids from the multiplicative monoid of `R` into that of `R'`
that sends non-units to zero.

We use the namespace `mul_char` for the definitions and results.

## Tags

multiplicative character
-/

section definition_and_group

/-!
### Definitions related to multiplicative characters

Even though the intended use is when domain and target of the characters
are commutative rings, we define them in the more general setting when
the domain is a commutative monoid and the target is a commutative monoid
with zero. (We need a zero in the target, since non-units are supposed
to map to zero.)

In this setting, there is an equivalence between multiplicative characters
`R → R'` and group homomorphisms `Rˣ → R'ˣ`, and the multiplicative characters
have a natural structure as a commutative group.
-/

universes u v

section defi

-- The domain of our multiplicative characters
variables (R : Type u) [comm_monoid R]
-- The target
variables (R' : Type v) [comm_monoid_with_zero R']

/-- Define a structure for multiplicative characters.
A multiplicative character from a commutative monoid `R` to a commutative monoid with zero `R'`
is a homomorphism of (multiplicative) monoids that sends non-units to zero. -/
structure mul_char extends monoid_hom R R' :=
(map_nonunit' : ∀ a : R, ¬ is_unit a → to_fun a = 0)

/-- This is the corresponding extension of `monoid_hom_class`. -/
class mul_char_class (F : Type*) (R R' : out_param $ Type*) [comm_monoid R]
 [comm_monoid_with_zero R']
  extends monoid_hom_class F R R' :=
(map_nonunit : ∀ (χ : F) {a : R} (ha : ¬ is_unit a), χ a = 0)

attribute [simp] mul_char_class.map_nonunit

end defi

section group

namespace mul_char

-- The domain of our multiplicative characters
variables {R : Type u} [comm_monoid R]
-- The target
variables {R' : Type v} [comm_monoid_with_zero R']

instance coe_to_fun : has_coe_to_fun (mul_char R R') (λ _, R → R') :=
⟨λ χ, χ.to_fun⟩

/-- See note [custom simps projection] -/
protected def simps.apply (χ : mul_char R R') : R → R' := χ
initialize_simps_projections mul_char (to_monoid_hom_to_fun → apply, -to_monoid_hom)

section trivial

variables (R R')

/-- The trivial multiplicative character. It takes the value `0` on non-units and
the value `1` on units. -/
@[simps]
noncomputable
def trivial : mul_char R R' :=
{ to_fun := by { classical, exact λ x, if is_unit x then 1 else 0 },
  map_nonunit' := by { intros a ha, simp only [ha, if_false], },
  map_one' := by simp only [is_unit_one, if_true],
  map_mul' := by { intros x y,
                   simp only [is_unit.mul_iff, boole_mul],
                   split_ifs; tauto, } }

end trivial


@[simp]
lemma coe_coe (χ : mul_char R R') : (χ.to_monoid_hom : R → R') = χ := rfl

@[simp]
lemma to_fun_eq_coe (χ : mul_char R R') : χ.to_fun = χ := rfl

@[simp]
lemma coe_mk (f : R →* R') (hf) : (mul_char.mk f hf : R → R') = f := rfl

/-- Extensionality. See `ext` below for the version that will actually be used. -/
lemma ext' {χ χ' : mul_char R R'} (h : ∀ a, χ a = χ' a) : χ = χ' :=
begin
  cases χ,
  cases χ',
  congr,
  exact monoid_hom.ext h,
end

instance : mul_char_class (mul_char R R') R R' :=
{ coe := λ χ, χ.to_monoid_hom.to_fun,
  coe_injective' := λ f g h, ext' (λ a, congr_fun h a),
  map_mul := λ χ, χ.map_mul',
  map_one := λ χ, χ.map_one',
  map_nonunit := λ χ, χ.map_nonunit', }

lemma map_nonunit (χ : mul_char R R') {a : R} (ha : ¬ is_unit a) : χ a = 0 :=
χ.map_nonunit' a ha

/-- Extensionality. Since `mul_char`s always take the value zero on non-units, it is sufficient
to compare the values on units. -/
@[ext]
lemma ext {χ χ' : mul_char R R'} (h : ∀ a : Rˣ, χ a = χ' a) : χ = χ' :=
begin
  apply ext',
  intro a,
  by_cases ha : is_unit a,
  { exact h ha.unit, },
  { rw [map_nonunit χ ha, map_nonunit χ' ha], },
end

/-!
### Equivalence of multiplicative characters with homomorphisms on units

We show that restriction / extension by zero gives an equivalence
between `mul_char R R'` and `Rˣ →* R'ˣ`.
-/

/-- Turn a `mul_char` into a homomorphism between the unit groups. -/
def to_unit_hom (χ : mul_char R R') : Rˣ →* R'ˣ := units.map χ

lemma coe_to_unit_hom (χ : mul_char R R') (a : Rˣ) :
  ↑(χ.to_unit_hom a) = χ a :=
rfl

/-- Turn a homomorphism between unit groups into a `mul_char`. -/
noncomputable
def of_unit_hom (f : Rˣ →* R'ˣ) : mul_char R R' :=
{ to_fun := by { classical, exact λ x, if hx : is_unit x then f hx.unit else 0 },
  map_one' := by { have h1 : (is_unit_one.unit : Rˣ) = 1 := units.eq_iff.mp rfl,
                   simp only [h1, dif_pos, units.coe_eq_one, map_one, is_unit_one], },
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

lemma of_unit_hom_coe (f : Rˣ →* R'ˣ) (a : Rˣ) :
  of_unit_hom f ↑a = f a :=
by simp [of_unit_hom]

/-- The equivalence between multiplicative characters and homomorphisms of unit groups. -/
noncomputable
def equiv_to_unit_hom : mul_char R R' ≃ (Rˣ →* R'ˣ) :=
{ to_fun := to_unit_hom,
  inv_fun := of_unit_hom,
  left_inv :=
  by { intro χ, ext x, rw [of_unit_hom_coe, coe_to_unit_hom] },
  right_inv :=
  by { intro f, ext x, rw [coe_to_unit_hom, of_unit_hom_coe], } }

@[simp]
lemma to_unit_hom_eq (χ : mul_char R R') : to_unit_hom χ = equiv_to_unit_hom χ := rfl

@[simp]
lemma of_unit_hom_eq (χ : Rˣ →* R'ˣ) : of_unit_hom χ = equiv_to_unit_hom.symm χ := rfl

@[simp]
lemma coe_equiv_to_unit_hom (χ : mul_char R R') (a : Rˣ) :
  ↑(equiv_to_unit_hom χ a) = χ a :=
coe_to_unit_hom χ a

@[simp]
lemma equiv_unit_hom_symm_coe (f : Rˣ →* R'ˣ) (a : Rˣ) :
  equiv_to_unit_hom.symm f ↑a = f a :=
of_unit_hom_coe f a


/-!
### Commutative group structure on multiplicative characters

The multiplicative characters `R → R'` form a commutative group.
-/

protected
lemma map_one (χ : mul_char R R') : χ (1 : R) = 1 :=
χ.map_one'

/-- If the domain has a zero (and is nontrivial), then `χ 0 = 0`. -/
protected
lemma map_zero {R : Type u} [comm_monoid_with_zero R] [nontrivial R] (χ : mul_char R R') :
  χ (0 : R) = 0 :=
by rw [map_nonunit χ not_is_unit_zero]

noncomputable
instance has_one : has_one (mul_char R R') := ⟨trivial R R'⟩

noncomputable
instance inhabited : inhabited (mul_char R R') := ⟨1⟩

/-- Evaluation of the trivial character -/
@[simp]
lemma one_apply_coe (a : Rˣ) : (1 : mul_char R R') a = 1 :=
dif_pos a.is_unit

/-- Multiplication of multiplicative characters. (This needs the target to be commutative.) -/
def mul (χ χ' : mul_char R R') : mul_char R R' :=
{ to_fun := χ * χ',
  map_nonunit' := λ a ha, by simp [map_nonunit χ ha],
  ..χ.to_monoid_hom * χ'.to_monoid_hom }

instance has_mul : has_mul (mul_char R R') := ⟨mul⟩

lemma mul_apply (χ χ' : mul_char R R') (a : R) : (χ * χ') a = χ a * χ' a := rfl

@[simp]
lemma coe_to_fun_mul (χ χ' : mul_char R R') : ⇑(χ * χ') = χ * χ' := rfl

protected
lemma one_mul (χ : mul_char R R') : (1 : mul_char R R') * χ = χ := by { ext, simp }

protected
lemma mul_one (χ : mul_char R R') : χ * 1 = χ := by { ext, simp }

/-- The inverse of a multiplicative character. We define it as `inverse ∘ χ`. -/
noncomputable
def inv (χ : mul_char R R') : mul_char R R' :=
{ to_fun := λ a, monoid_with_zero.inverse (χ a),
  map_nonunit' := λ a ha, by simp [map_nonunit _ ha],
  ..monoid_with_zero.inverse.to_monoid_hom.comp χ.to_monoid_hom }

noncomputable
instance has_inv : has_inv (mul_char R R') := ⟨inv⟩

/-- The inverse of a multiplicative character `χ`, applied to `a`, is the inverse of `χ a`. -/
lemma inv_apply_eq_inv (χ : mul_char R R') (a : R) :
  χ⁻¹ a = ring.inverse (χ a) :=
eq.refl $ inv χ a

/-- Variant when the target is a field -/
lemma inv_apply_eq_inv' {R' : Type v} [field R'] (χ : mul_char R R') (a : R) :
  χ⁻¹ a = (χ a)⁻¹ :=
(inv_apply_eq_inv χ a).trans $ ring.inverse_eq_inv (χ a)

/-- When the domain has a zero, we can as well take the inverse first. -/
lemma inv_apply {R : Type u} [comm_monoid_with_zero R] (χ : mul_char R R') (a : R) :
  χ⁻¹ a = χ (ring.inverse a) :=
begin
  by_cases ha : is_unit a,
  { rw [inv_apply_eq_inv],
    have h := is_unit.map χ ha,
    apply_fun ((*) (χ a)) using is_unit.mul_right_injective h,
    rw [ring.mul_inverse_cancel _ h, ← map_mul, ring.mul_inverse_cancel _ ha, mul_char.map_one], },
  { revert ha, nontriviality R, intro ha, -- `nontriviality R` by itself doesn't do it
    rw [map_nonunit _ ha, ring.inverse_non_unit a ha, mul_char.map_zero χ], },
end

/-- When the domain is a field, we can use the field inverse instead. -/
lemma inv_apply' {R : Type u} [field R] (χ : mul_char R R') (a : R) : χ⁻¹ a = χ a⁻¹ :=
(inv_apply χ a).trans $ congr_arg _ (ring.inverse_eq_inv a)

/-- The product of a character with its inverse is the trivial character. -/
@[simp]
lemma inv_mul (χ : mul_char R R') : χ⁻¹ * χ = 1 :=
begin
  ext x,
  rw [coe_to_fun_mul, pi.mul_apply, inv_apply_eq_inv,
      ring.inverse_mul_cancel _ (is_unit.map _ x.is_unit), one_apply_coe],
end

/-- Finally, the commutative group structure on `mul_char R R'`. -/
noncomputable
instance comm_group : comm_group (mul_char R R') :=
{ one := 1,
  mul := (*),
  inv := has_inv.inv,
  mul_left_inv := inv_mul,
  mul_assoc := by { intros χ₁ χ₂ χ₃, ext a, simp [mul_assoc], },
  mul_comm := by { intros χ₁ χ₂, ext a, simp [mul_comm], },
  one_mul := one_mul,
  mul_one := mul_one, }

/-- If `a` is a unit and `n : ℕ`, then `(χ ^ n) a = (χ a) ^ n`. -/
lemma pow_apply_coe (χ : mul_char R R') (n : ℕ) (a : Rˣ) :
  (χ ^ n) a = (χ a) ^ n :=
begin
  induction n with n ih,
  { rw [pow_zero, pow_zero, one_apply_coe], },
  { rw [pow_succ, pow_succ, mul_apply, ih], },
end

/-- If `n` is positive, then `(χ ^ n) a = (χ a) ^ n`. -/
lemma pow_apply' (χ : mul_char R R') {n : ℕ} (hn : 0 < n) (a : R) :
  (χ ^ n) a = (χ a) ^ n :=
begin
  by_cases ha : is_unit a,
  { exact pow_apply_coe χ n ha.unit, },
  { rw [map_nonunit (χ ^ n) ha, map_nonunit χ ha, zero_pow hn], },
end

end mul_char

end group

end definition_and_group

/-!
### Properties of multiplicative characters

We introduce the properties of being nontrivial or quadratic and prove
some basic facts about them.

We now assume that domain and target are commutative rings.
-/

section properties

namespace mul_char

universes u v w

variables {R : Type u} [comm_ring R] {R' : Type v} [comm_ring R'] {R'' : Type w} [comm_ring R'']

/-- A multiplicative character is *nontrivial* if it takes a value `≠ 1` on a unit. -/
def is_nontrivial (χ : mul_char R R') : Prop := ∃ a : Rˣ, χ a ≠ 1

/-- A multiplicative character is nontrivial iff it is not the trivial character. -/
lemma is_nontrivial_iff (χ : mul_char R R') : χ.is_nontrivial ↔ χ ≠ 1 :=
begin
  split,
  { intros h₁ h₂,
    obtain ⟨a, ha⟩ := h₁,
    rw [h₂, one_apply_coe] at ha,
    exact ha rfl, },
  { contrapose!,
    intro h,
    change ¬ ∃ a : Rˣ, χ a ≠ 1 at h,
    push_neg at h,
    ext a,
    rw [one_apply_coe a, h a], },
end

/-- A multiplicative character is *quadratic* if it takes only the values `0`, `1`, `-1`. -/
def is_quadratic (χ : mul_char R R') : Prop := ∀ a, χ a = 0 ∨ χ a = 1 ∨ χ a = -1

/-- We can post-compose a multiplicative character with a ring homomorphism. -/
def ring_hom_comp (χ : mul_char R R') (f : R' →+* R'') : mul_char R R'' :=
{ map_nonunit' :=
  begin
    intros a ha,
    simp only [ring_hom.to_monoid_hom_eq_coe, monoid_hom.to_fun_eq_coe, monoid_hom.coe_comp,
               ring_hom.coe_monoid_hom, coe_coe, function.comp_app, map_nonunit χ ha,
               ring_hom.map_zero],
  end,
  ..f.to_monoid_hom.comp χ.to_monoid_hom}

@[simp]
lemma ring_hom_comp_apply (χ : mul_char R R') (f : R' →+* R'') (a : R) :
  χ.ring_hom_comp f a = f (χ a) := rfl

/-- Composition with an injective ring homomorphism preserves nontriviality. -/
lemma is_nontrivial.comp {χ : mul_char R R'} (hχ : χ.is_nontrivial)
  {f : R' →+* R''} (hf : function.injective f) :
   (χ.ring_hom_comp f).is_nontrivial :=
begin
  obtain ⟨a, ha⟩ := hχ,
  use a,
  rw [ring_hom_comp_apply, ← ring_hom.map_one f],
  exact λ h, ha (hf h),
end

/-- Composition with a ring homomorphism preserves the property of being a quadratic character. -/
lemma is_quadratic.comp {χ : mul_char R R'} (hχ : χ.is_quadratic) (f : R' →+* R'') :
  (χ.ring_hom_comp f).is_quadratic :=
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

/-- The inverse of a quadratic character is itself. →  -/
lemma quadratic_char_inv {χ : mul_char R R'} (hχ : χ.is_quadratic) : χ⁻¹ = χ :=
begin
  ext x,
  rw [inv_apply_eq_inv],
  rcases hχ x with h₀ | h₁ | h₂,
  { rw [h₀, ring.inverse_zero], },
  { rw [h₁, ring.inverse_one], },
  { rw [h₂, (by norm_num : (-1 : R') = (-1 : R'ˣ)), ring.inverse_unit (-1 : R'ˣ)],
    refl, },
end

/-- The square of a quadratic character is the trivial character. -/
lemma quad_char_sq_eq_one {χ : mul_char R R'} (hχ : χ.is_quadratic) : χ ^ 2 = 1 :=
begin
  rw [pow_two],
  nth_rewrite 0 ← quadratic_char_inv hχ,
  rw [mul_left_inv],
end

/-- The `p`th power of a quadratic character is itself, when `p` is the (prime) characteristic
of the target ring. -/
lemma quad_char_pow_char {χ : mul_char R R'} (hχ : χ.is_quadratic)
 (p : ℕ) [hp : fact p.prime] [char_p R' p] :
  χ ^ p = χ :=
begin
  ext x,
  rw [pow_apply_coe],
  rcases hχ x with (hx | hx | hx); rw hx,
  { rw [zero_pow (fact.out p.prime).pos], },
  { rw [one_pow], },
  { exact char_p.neg_one_pow_char R' p, },
end

/-- The `n`th power of a quadratic character is itself, when `n` is odd. -/
lemma quad_char_pow_odd {χ : mul_char R R'} (hχ : χ.is_quadratic) {n : ℕ} (hn : n % 2 = 1) :
  χ ^ n = χ :=
by rw [← nat.div_add_mod n 2, hn,
       pow_add, pow_mul, quad_char_sq_eq_one hχ, one_pow, pow_one, mul_char.one_mul]

open_locale big_operators

/-- The sum over all values of a nontrivial multiplicative character on a finite ring is zero
(when the target is a domain). -/
lemma sum_eq_zero_of_is_nontrivial [fintype R] [is_domain R'] {χ : mul_char R R'}
 (hχ : χ.is_nontrivial) :
  ∑ a, χ a = 0 :=
begin
  rcases hχ with ⟨b, hb⟩,
  have h₁ : ∑ a, χ (b * a) = ∑ a, χ a :=
    fintype.sum_bijective _ (units.mul_left_bijective b) _ _ (λ x, rfl),
  simp only [map_mul] at h₁,
  rw [← finset.mul_sum] at h₁,
  exact eq_zero_of_mul_eq_self_left hb h₁,
end

/-- The sum over all values of the trivial multiplicative character on a finite ring is
the cardinality of its unit group. -/
lemma sum_eq_card_units_of_is_trivial [fintype R] [decidable_eq R] :
  ∑ a, (1 : mul_char R R') a = fintype.card Rˣ :=
begin
  have h₁ : ∀ a : R, (1 : mul_char R R') a = ite (is_unit a) 1 0 :=
  by { intro a, split_ifs, { exact one_apply_coe h.unit }, { exact map_nonunit _ h } },
  simp_rw [h₁],
  have h₂ := @finset.sum_filter R' R finset.univ _ is_unit _ 1,
  simp only [pi.one_apply] at h₂,
  have h₃ := map_sum (algebra_map ℕ R') 1 (finset.filter (is_unit : R → Prop) finset.univ),
  simp only [pi.one_apply] at h₃,
  rw [← finset.card_eq_sum_ones, eq_nat_cast, eq_nat_cast, nat.cast_one] at h₃,
  have h₄ : finset.filter (is_unit : R → Prop) finset.univ
             = finset.map ⟨(coe : Rˣ → R), units.ext⟩ finset.univ :=
  begin
    ext a,
    simp only [finset.mem_filter, finset.mem_univ, true_and, finset.mem_map,
               function.embedding.coe_fn_mk, exists_true_left],
    refl,
  end,
  rw [← h₂, ← h₃, h₄, finset.card_map, fintype.card],
end

end mul_char

end properties

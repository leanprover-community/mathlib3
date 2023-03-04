/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import algebra.char_p.basic
import algebra.euclidean_domain.instances
import algebra.group.conj_finite

/-!
# Multiplicative characters of finite rings and fields

Let `R` and `R'` be a commutative rings.
A *multiplicative character* of `R` with values in `R'` is a morphism of
monoids from the multiplicative monoid of `R` into that of `R'`
that sends non-units to zero.

We use the namespace `mul_char` for the definitions and results.

## Main results

We show that the multiplicative characters form a group (if `R'` is commutative);
see `mul_char.comm_group`. We also provide an equivalence with the
homomorphisms `Rˣ →* R'ˣ`; see `mul_char.equiv_to_unit_hom`.

We define a multiplicative character to be *quadratic* if its values
are among `0`, `1` and `-1`, and we prove some properties of quadratic characters.

Finally, we show that the sum of all values of a nontrivial multiplicative
character vanishes; see `mul_char.is_nontrivial.sum_eq_zero`.

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
                   classical,
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

lemma ext_iff {χ χ' : mul_char R R'} : χ = χ' ↔ ∀ a : Rˣ, χ a = χ' a :=
⟨by { rintro rfl a, refl }, ext⟩

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
    classical,
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

/-- If the domain is a ring `R`, then `χ (ring_char R) = 0`. -/
lemma map_ring_char {R : Type u} [comm_ring R] [nontrivial R] (χ : mul_char R R') :
  χ (ring_char R) = 0 :=
by rw [ring_char.nat.cast_ring_char, χ.map_zero]

noncomputable
instance has_one : has_one (mul_char R R') := ⟨trivial R R'⟩

noncomputable
instance inhabited : inhabited (mul_char R R') := ⟨1⟩

/-- Evaluation of the trivial character -/
@[simp]
lemma one_apply_coe (a : Rˣ) : (1 : mul_char R R') a = 1 :=
by { classical, exact dif_pos a.is_unit }

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

/-- The inverse of a multiplicative character `χ`, applied to `a`, is the inverse of `χ a`.
Variant when the target is a field -/
lemma inv_apply_eq_inv' {R' : Type v} [field R'] (χ : mul_char R R') (a : R) :
  χ⁻¹ a = (χ a)⁻¹ :=
(inv_apply_eq_inv χ a).trans $ ring.inverse_eq_inv (χ a)

/-- When the domain has a zero, then the inverse of a multiplicative character `χ`,
applied to `a`, is `χ` applied to the inverse of `a`. -/
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

/-- When the domain has a zero, then the inverse of a multiplicative character `χ`,
applied to `a`, is `χ` applied to the inverse of `a`. -/
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

/-- The commutative group structure on `mul_char R R'`. -/
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
by simp only [is_nontrivial, ne.def, ext_iff, not_forall, one_apply_coe]

/-- A multiplicative character is *quadratic* if it takes only the values `0`, `1`, `-1`. -/
def is_quadratic (χ : mul_char R R') : Prop := ∀ a, χ a = 0 ∨ χ a = 1 ∨ χ a = -1

/-- If two values of quadratic characters with target `ℤ` agree after coercion into a ring
of characteristic not `2`, then they agree in `ℤ`. -/
lemma is_quadratic.eq_of_eq_coe {χ : mul_char R ℤ} (hχ : is_quadratic χ)
  {χ' : mul_char R' ℤ} (hχ' : is_quadratic χ') [nontrivial R''] (hR'' : ring_char R'' ≠ 2)
  {a : R} {a' : R'} (h : (χ a : R'') = χ' a') :
  χ a = χ' a' :=
int.cast_inj_on_of_ring_char_ne_two hR'' (hχ a) (hχ' a') h

/-- We can post-compose a multiplicative character with a ring homomorphism. -/
@[simps]
def ring_hom_comp (χ : mul_char R R') (f : R' →+* R'') : mul_char R R'' :=
{ to_fun := λ a, f (χ a),
  map_nonunit' := λ a ha, by simp only [map_nonunit χ ha, map_zero],
  ..f.to_monoid_hom.comp χ.to_monoid_hom }

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
  rcases hχ a with (ha | ha | ha);
    simp [ha],
end

/-- The inverse of a quadratic character is itself. →  -/
lemma is_quadratic.inv {χ : mul_char R R'} (hχ : χ.is_quadratic) : χ⁻¹ = χ :=
begin
  ext x,
  rw [inv_apply_eq_inv],
  rcases hχ x with h₀ | h₁ | h₂,
  { rw [h₀, ring.inverse_zero], },
  { rw [h₁, ring.inverse_one], },
  { rw [h₂, (by norm_cast : (-1 : R') = (-1 : R'ˣ)), ring.inverse_unit (-1 : R'ˣ)],
    refl, },
end

/-- The square of a quadratic character is the trivial character. -/
lemma is_quadratic.sq_eq_one {χ : mul_char R R'} (hχ : χ.is_quadratic) : χ ^ 2 = 1 :=
begin
  convert mul_left_inv _,
  rw [pow_two, hχ.inv],
end

/-- The `p`th power of a quadratic character is itself, when `p` is the (prime) characteristic
of the target ring. -/
lemma is_quadratic.pow_char {χ : mul_char R R'} (hχ : χ.is_quadratic)
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

/-- The `n`th power of a quadratic character is the trivial character, when `n` is even. -/
lemma is_quadratic.pow_even {χ : mul_char R R'} (hχ : χ.is_quadratic) {n : ℕ} (hn : even n) :
  χ ^ n = 1 :=
begin
  obtain ⟨n, rfl⟩ := even_iff_two_dvd.mp hn,
  rw [pow_mul, hχ.sq_eq_one, one_pow]
end

/-- The `n`th power of a quadratic character is itself, when `n` is odd. -/
lemma is_quadratic.pow_odd {χ : mul_char R R'} (hχ : χ.is_quadratic) {n : ℕ} (hn : odd n) :
  χ ^ n = χ :=
begin
  obtain ⟨n, rfl⟩ := hn,
  rw [pow_add, pow_one, hχ.pow_even (even_two_mul _), one_mul]
end

open_locale big_operators

/-- The sum over all values of a nontrivial multiplicative character on a finite ring is zero
(when the target is a domain). -/
lemma is_nontrivial.sum_eq_zero [fintype R] [is_domain R'] {χ : mul_char R R'}
 (hχ : χ.is_nontrivial) :
  ∑ a, χ a = 0 :=
begin
  rcases hχ with ⟨b, hb⟩,
  refine eq_zero_of_mul_eq_self_left hb _,
  simp only [finset.mul_sum, ← map_mul],
  exact fintype.sum_bijective _ (units.mul_left_bijective b) _ _ (λ x, rfl)
end

/-- The sum over all values of the trivial multiplicative character on a finite ring is
the cardinality of its unit group. -/
lemma sum_one_eq_card_units [fintype R] [decidable_eq R] :
  ∑ a, (1 : mul_char R R') a = fintype.card Rˣ :=
begin
  calc ∑ a, (1 : mul_char R R') a
      = ∑ a : R, if is_unit a then 1 else 0 : finset.sum_congr rfl (λ a _, _)
  ... = ((finset.univ : finset R).filter is_unit).card : finset.sum_boole
  ... = (finset.univ.map (⟨(coe : Rˣ → R), units.ext⟩)).card : _
  ... = fintype.card Rˣ : congr_arg _ (finset.card_map _),
  { split_ifs with h h,
    { exact one_apply_coe h.unit },
    { exact map_nonunit _ h } },
  { congr,
    ext a,
    simp only [finset.mem_filter, finset.mem_univ, true_and, finset.mem_map,
               function.embedding.coe_fn_mk, exists_true_left, is_unit], },
end

end mul_char

end properties

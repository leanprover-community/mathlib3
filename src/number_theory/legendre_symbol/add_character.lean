/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import number_theory.cyclotomic.primitive_roots
import field_theory.finite.trace

/-!
# Additive characters of finite rings and fields

Let `R` be a finite commutative ring. An *additive character* of `R` with values
in another commutative ring `R'` is simply a morphism from the additive group
of `R` into the multiplicative monoid of `R'`.

The additive characters on `R` with values in `R'` form a commutative group.

We use the namespace `add_char`.

## Main definitions and results

We define `mul_shift ψ a`, where `ψ : add_char R R'` and `a : R`, to be the
character defined by `x ↦ ψ (a * x)`. An additive character `ψ` is *primitive*
if `mul_shift ψ a` is trivial only when `a = 0`.

We show that when `ψ` is primitive, then the map `a ↦ mul_shift ψ a` is injective
(`add_char.to_mul_shift_inj_of_is_primitive`) and that `ψ` is primitive when `R` is a field
and `ψ` is nontrivial (`add_char.is_nontrivial.is_primitive`).

We also show that there are primitive additive characters on `R` (with suitable
target `R'`) when `R` is a field or `R = zmod n` (`add_char.primitive_char_finite_field`
and `add_char.primitive_zmod_char`).

Finally, we show that the sum of all character values is zero when the character
is nontrivial (and the target is a domain); see `add_char.sum_eq_zero_of_is_nontrivial`.

## Tags

additive character
-/

universes u v

/-!
### Definitions related to and results on additive characters
-/

section add_char_def

-- The domain of our additive characters
variables (R : Type u) [add_monoid R]
-- The target
variables (R' : Type v) [comm_monoid R']

/-- Define `add_char R R'` as `(multiplicative R) →* R'`.
The definition works for an additive monoid `R` and a monoid `R'`,
but we will restrict to the case that both are commutative rings below.
We assume right away that `R'` is commutative, so that `add_char R R'` carries
a structure of commutative monoid.
The trivial additive character (sending everything to `1`) is `(1 : add_char R R').` -/
@[derive [comm_monoid, inhabited]]
def add_char : Type (max u v) := (multiplicative R) →* R'

end add_char_def

namespace add_char

section coe_to_fun

variables {R : Type u} [add_monoid R] {R' : Type v} [comm_monoid R']

/-- Interpret an additive character as a monoid homomorphism. -/
def to_monoid_hom : (add_char R R') → (multiplicative R →* R') := id

open multiplicative

/-- Define coercion to a function so that it includes the move from `R` to `multiplicative R`.
After we have proved the API lemmas below, we don't need to worry about writing `of_add a`
when we want to apply an additive character. -/
instance has_coe_to_fun : has_coe_to_fun (add_char R R') (λ x, R → R') :=
{ coe := λ ψ x, ψ.to_monoid_hom (of_add x) }

lemma coe_to_fun_apply (ψ : add_char R R') (a : R) : ψ a = ψ.to_monoid_hom (of_add a) := rfl

instance monoid_hom_class : monoid_hom_class (add_char R R') (multiplicative R) R' :=
monoid_hom.monoid_hom_class

/-- An additive character maps `0` to `1`. -/
@[simp]
lemma map_zero_one (ψ : add_char R R') : ψ 0 = 1 :=
by rw [coe_to_fun_apply, of_add_zero, map_one]

/-- An additive character maps sums to products. -/
@[simp]
lemma map_add_mul (ψ : add_char R R') (x y : R) : ψ (x + y) = ψ x * ψ y :=
by rw [coe_to_fun_apply, coe_to_fun_apply _ x, coe_to_fun_apply _ y, of_add_add, map_mul]

/-- An additive character maps multiples by natural numbers to powers. -/
@[simp]
lemma map_nsmul_pow (ψ : add_char R R') (n : ℕ) (x : R) : ψ (n • x) = (ψ x) ^ n :=
by rw [coe_to_fun_apply, coe_to_fun_apply _ x, of_add_nsmul, map_pow]

end coe_to_fun

section group_structure

open multiplicative

variables {R : Type u} [add_comm_group R] {R' : Type v} [comm_monoid R']

/-- An additive character on a commutative additive group has an inverse.

Note that this is a different inverse to the one provided by `monoid_hom.has_inv`,
as it acts on the domain instead of the codomain. -/
instance has_inv : has_inv (add_char R R') := ⟨λ ψ, ψ.comp inv_monoid_hom⟩

lemma inv_apply (ψ : add_char R R') (x : R) : ψ⁻¹ x = ψ (-x) := rfl

/-- An additive character maps multiples by integers to powers. -/
@[simp]
lemma map_zsmul_zpow {R' : Type v} [comm_group R'] (ψ : add_char R R') (n : ℤ) (x : R) :
  ψ (n • x) = (ψ x) ^ n :=
by rw [coe_to_fun_apply, coe_to_fun_apply _ x, of_add_zsmul, map_zpow]

/-- The additive characters on a commutative additive group form a commutative group. -/
instance comm_group : comm_group (add_char R R') :=
{ inv := has_inv.inv,
  mul_left_inv :=
  λ ψ, by { ext, rw [monoid_hom.mul_apply, monoid_hom.one_apply, inv_apply, ← map_add_mul,
                     add_left_neg, map_zero_one], },
  ..monoid_hom.comm_monoid }

end group_structure

section additive

-- The domain and target of our additive characters. Now we restrict to rings on both sides.
variables {R : Type u} [comm_ring R] {R' : Type v} [comm_ring R']

/-- An additive character is *nontrivial* if it takes a value `≠ 1`. -/
def is_nontrivial (ψ : add_char R R') : Prop := ∃ (a : R), ψ a ≠ 1

/-- An additive character is nontrivial iff it is not the trivial character. -/
lemma is_nontrivial_iff_ne_trivial (ψ : add_char R R') : is_nontrivial ψ ↔ ψ ≠ 1 :=
begin
  refine not_forall.symm.trans (iff.not _),
  rw fun_like.ext_iff,
  refl,
end

/-- Define the multiplicative shift of an additive character.
This satisfies `mul_shift ψ a x = ψ (a * x)`. -/
def mul_shift (ψ : add_char R R') (a : R) : add_char R R' :=
ψ.comp (add_monoid_hom.mul_left a).to_multiplicative

@[simp] lemma mul_shift_apply {ψ : add_char R R'} {a : R} {x : R} : mul_shift ψ a x = ψ (a * x) :=
rfl

/-- `ψ⁻¹ = mul_shift ψ (-1))`. -/
lemma inv_mul_shift (ψ : add_char R R') : ψ⁻¹ = mul_shift ψ (-1) :=
begin
  ext,
  rw [inv_apply, mul_shift_apply, neg_mul, one_mul],
end

/-- If `n` is a natural number, then `mul_shift ψ n x = (ψ x) ^ n`. -/
lemma mul_shift_spec' (ψ : add_char R R') (n : ℕ) (x : R) : mul_shift ψ n x = (ψ x) ^ n :=
by rw [mul_shift_apply, ← nsmul_eq_mul, map_nsmul_pow]

/-- If `n` is a natural number, then `ψ ^ n = mul_shift ψ n`. -/
lemma pow_mul_shift (ψ : add_char R R') (n : ℕ) : ψ ^ n = mul_shift ψ n :=
begin
  ext x,
  rw [show (ψ ^ n) x = (ψ x) ^ n, from rfl, ← mul_shift_spec'],
end

/-- The product of `mul_shift ψ a` and `mul_shift ψ b` is `mul_shift ψ (a + b)`. -/
lemma mul_shift_mul (ψ : add_char R R') (a b : R) :
  mul_shift ψ a * mul_shift ψ b = mul_shift ψ (a + b) :=
begin
  ext,
  simp only [right_distrib, monoid_hom.mul_apply, mul_shift_apply, map_add_mul],
end

/-- `mul_shift ψ 0` is the trivial character. -/
@[simp]
lemma mul_shift_zero (ψ : add_char R R') : mul_shift ψ 0 = 1 :=
begin
  ext,
  simp only [mul_shift_apply, zero_mul, map_zero_one, monoid_hom.one_apply],
end

/-- An additive character is *primitive* iff all its multiplicative shifts by nonzero
elements are nontrivial. -/
def is_primitive (ψ : add_char R R') : Prop :=
∀ (a : R), a ≠ 0 → is_nontrivial (mul_shift ψ a)

/-- The map associating to `a : R` the multiplicative shift of `ψ` by `a`
is injective when `ψ` is primitive. -/
lemma to_mul_shift_inj_of_is_primitive {ψ : add_char R R'} (hψ : is_primitive ψ) :
  function.injective ψ.mul_shift :=
begin
  intros a b h,
  apply_fun (λ x, x * mul_shift ψ (-b)) at h,
  simp only [mul_shift_mul, mul_shift_zero, add_right_neg] at h,
  have h₂ := hψ (a + (-b)),
  rw [h, is_nontrivial_iff_ne_trivial, ← sub_eq_add_neg, sub_ne_zero] at h₂,
  exact not_not.mp (λ h, h₂ h rfl),
end

-- `add_comm_group.equiv_direct_sum_zmod_of_fintype`
-- gives the structure theorem for finite abelian groups.
-- This could be used to show that the map above is a bijection.
-- We leave this for a later occasion.

/-- When `R` is a field `F`, then a nontrivial additive character is primitive -/
lemma is_nontrivial.is_primitive {F : Type u} [field F] {ψ : add_char F R'}
  (hψ : is_nontrivial ψ) :
  is_primitive ψ :=
begin
  intros a ha,
  cases hψ with x h,
  use (a⁻¹ * x),
  rwa [mul_shift_apply, mul_inv_cancel_left₀ ha],
end

/-- Structure for a primitive additive character on a finite ring `R` into a cyclotomic extension
of a field `R'`. It records which cyclotomic extension it is, the character, and the
fact that the character is primitive. -/
@[nolint has_nonempty_instance] -- can't prove that they always exist
structure primitive_add_char (R : Type u) [comm_ring R] [fintype R] (R' : Type v) [field R'] :=
(n : ℕ+)
(char : add_char R (cyclotomic_field n R'))
(prim : is_primitive char)

/-!
### Additive characters on `zmod n`
-/

variables {C : Type v} [comm_ring C]

section zmod_char_def

open multiplicative -- so we can write simply `to_add`, which we need here again

/-- We can define an additive character on `zmod n` when we have an `n`th root of unity `ζ : C`. -/
def zmod_char (n : ℕ+) {ζ : C} (hζ : ζ ^ ↑n = 1) : add_char (zmod n) C :=
{ to_fun := λ (a : multiplicative (zmod n)), ζ ^ a.to_add.val,
  map_one' := by simp only [to_add_one, zmod.val_zero, pow_zero],
  map_mul' := λ x y, by rw [to_add_mul, ← pow_add, zmod.val_add (to_add x) (to_add y),
                            ← pow_eq_pow_mod _ hζ] }

/-- The additive character on `zmod n` defined using `ζ` sends `a` to `ζ^a`. -/
lemma zmod_char_apply {n : ℕ+} {ζ : C} (hζ : ζ ^ ↑n = 1) (a : zmod n) :
  zmod_char n hζ a = ζ ^ a.val := rfl

lemma zmod_char_apply' {n : ℕ+} {ζ : C} (hζ : ζ ^ ↑n = 1) (a : ℕ) : zmod_char n hζ a = ζ ^ a :=
by rw [pow_eq_pow_mod a hζ, zmod_char_apply, zmod.val_nat_cast a]

end zmod_char_def

/-- An additive character on `zmod n` is nontrivial iff it takes a value `≠ 1` on `1`. -/
lemma zmod_char_is_nontrivial_iff (n : ℕ+) (ψ : add_char (zmod n) C) : is_nontrivial ψ ↔ ψ 1 ≠ 1 :=
begin
  refine ⟨_, λ h, ⟨1, h⟩⟩,
  contrapose!,
  rintros h₁ ⟨a, ha⟩,
  have ha₁ : a = a.val • 1,
  { rw [nsmul_eq_mul, mul_one], exact (zmod.nat_cast_zmod_val a).symm },
  rw [ha₁, map_nsmul_pow, h₁, one_pow] at ha,
  exact ha rfl,
end

/-- A primitive additive character on `zmod n` takes the value `1` only at `0`. -/
lemma is_primitive.zmod_char_eq_one_iff (n : ℕ+) {ψ : add_char (zmod n) C} (hψ : is_primitive ψ)
  (a : zmod n) :
  ψ a = 1 ↔ a = 0 :=
begin
  refine ⟨λ h, not_imp_comm.mp (hψ a) _, λ ha, (by rw [ha, map_zero_one])⟩,
  rw [zmod_char_is_nontrivial_iff n (mul_shift ψ a), mul_shift_apply, mul_one, h, not_not],
end

/-- The converse: if the additive character takes the value `1` only at `0`,
then it is primitive. -/
lemma zmod_char_primitive_of_eq_one_only_at_zero (n : ℕ) (ψ : add_char (zmod n) C)
  (hψ : ∀ a, ψ a = 1 → a = 0) :
  is_primitive ψ :=
begin
  refine λ a ha, (is_nontrivial_iff_ne_trivial _).mpr (λ hf, _),
  have h : mul_shift ψ a 1 = (1 : add_char (zmod n) C) (1 : zmod n) :=
    congr_fun (congr_arg coe_fn hf) 1,
  rw [mul_shift_apply, mul_one, monoid_hom.one_apply] at h,
  exact ha (hψ a h),
end

/-- The additive character on `zmod n` associated to a primitive `n`th root of unity
is primitive -/
lemma zmod_char_primitive_of_primitive_root (n : ℕ+) {ζ : C} (h : is_primitive_root ζ n) :
  is_primitive (zmod_char n ((is_primitive_root.iff_def ζ n).mp h).left) :=
begin
  apply zmod_char_primitive_of_eq_one_only_at_zero,
  intros a ha,
  rw [zmod_char_apply, ← pow_zero ζ] at ha,
  exact (zmod.val_eq_zero a).mp (is_primitive_root.pow_inj h (zmod.val_lt a) n.pos ha),
end

/-- There is a primitive additive character on `zmod n` if the characteristic of the target
does not divide `n` -/
noncomputable
def primitive_zmod_char (n : ℕ+) (F' : Type v) [field F'] (h : (n : F') ≠ 0) :
  primitive_add_char (zmod n) F' :=
begin
  haveI : ne_zero ((n : ℕ) : F') := ⟨h⟩,
  exact
{ n := n,
  char := zmod_char n (is_cyclotomic_extension.zeta_pow n F' _),
  prim := zmod_char_primitive_of_primitive_root n (is_cyclotomic_extension.zeta_spec n F' _) }
end

/-!
### Existence of a primitive additive character on a finite field
-/

/-- There is a primitive additive character on the finite field `F` if the characteristic
of the target is different from that of `F`.
We obtain it as the composition of the trace from `F` to `zmod p` with a primitive
additive character on `zmod p`, where `p` is the characteristic of `F`. -/
noncomputable
def primitive_char_finite_field (F F': Type*) [field F] [fintype F] [field F']
  (h : ring_char F' ≠ ring_char F) :
  primitive_add_char F F' :=
begin
  let p := ring_char F,
  haveI hp : fact p.prime := ⟨char_p.char_is_prime F _⟩,
  let pp := p.to_pnat hp.1.pos,
  have hp₂ : ¬ ring_char F' ∣ p :=
  begin
    cases char_p.char_is_prime_or_zero F' (ring_char F') with hq hq,
    { exact mt (nat.prime.dvd_iff_eq hp.1 (nat.prime.ne_one hq)).mp h.symm, },
    { rw [hq],
      exact λ hf, nat.prime.ne_zero hp.1 (zero_dvd_iff.mp hf), },
  end,
  let ψ := primitive_zmod_char pp F' (ne_zero_iff.mp (ne_zero.of_not_dvd F' hp₂)),
  let ψ' := ψ.char.comp (algebra.trace (zmod p) F).to_add_monoid_hom.to_multiplicative,
  have hψ' : is_nontrivial ψ' :=
  begin
    obtain ⟨a, ha⟩ := finite_field.trace_to_zmod_nondegenerate F one_ne_zero,
    rw one_mul at ha,
    exact ⟨a, λ hf, ha $ (ψ.prim.zmod_char_eq_one_iff pp $ algebra.trace (zmod p) F a).mp hf⟩,
  end,
  exact
{ n := ψ.n,
  char := ψ',
  prim := hψ'.is_primitive },
end

/-!
### The sum of all character values
-/

open_locale big_operators

variables [fintype R]

/-- The sum over the values of a nontrivial additive character vanishes if the target ring
is a domain. -/
lemma sum_eq_zero_of_is_nontrivial [is_domain R'] {ψ : add_char R R'} (hψ : is_nontrivial ψ) :
  ∑ a, ψ a = 0 :=
begin
  rcases hψ with ⟨b, hb⟩,
  have h₁ : ∑ (a : R), ψ (b + a) = ∑ (a : R), ψ a :=
    fintype.sum_bijective _ (add_group.add_left_bijective b) _ _ (λ x, rfl),
  simp_rw [map_add_mul] at h₁,
  have h₂ : ∑ (a : R), ψ a = finset.univ.sum ⇑ψ := rfl,
  rw [← finset.mul_sum, h₂] at h₁,
  exact eq_zero_of_mul_eq_self_left hb h₁,
end

/-- The sum over the values of the trivial additive character is the cardinality of the source. -/
lemma sum_eq_card_of_is_trivial {ψ : add_char R R'} (hψ : ¬ is_nontrivial ψ) :
  ∑ a, ψ a = fintype.card R :=
begin
  simp only [is_nontrivial] at hψ,
  push_neg at hψ,
  simp only [hψ, finset.sum_const, nat.smul_one_eq_coe],
  refl,
end

/-- The sum over the values of `mul_shift ψ b` for `ψ` primitive is zero when `b ≠ 0`
and `#R` otherwise. -/
lemma sum_mul_shift [decidable_eq R] [is_domain R'] {ψ : add_char R R'} (b : R)
  (hψ : is_primitive ψ) :
  ∑ (x : R), ψ (x * b) = if b = 0 then fintype.card R else 0 :=
begin
  split_ifs with h,
  { -- case `b = 0`
    simp only [h, mul_zero, map_zero_one, finset.sum_const, nat.smul_one_eq_coe],
    refl, },
  { -- case `b ≠ 0`
    simp_rw mul_comm,
    exact sum_eq_zero_of_is_nontrivial (hψ b h), },
end

end additive

end add_char

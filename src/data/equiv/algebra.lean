/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import data.equiv.basic data.polynomial linear_algebra.multivariate_polynomial

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

namespace equiv

section group
variables [group α]

protected def mul_left (a : α) : α ≃ α :=
{ to_fun    := λx, a * x,
  inv_fun   := λx, a⁻¹ * x,
  left_inv  := assume x, show a⁻¹ * (a * x) = x, from inv_mul_cancel_left a x,
  right_inv := assume x, show a * (a⁻¹ * x) = x, from mul_inv_cancel_left a x }

attribute [to_additive equiv.add_left._proof_1] equiv.mul_left._proof_1
attribute [to_additive equiv.add_left._proof_2] equiv.mul_left._proof_2
attribute [to_additive equiv.add_left] equiv.mul_left

protected def mul_right (a : α) : α ≃ α :=
{ to_fun    := λx, x * a,
  inv_fun   := λx, x * a⁻¹,
  left_inv  := assume x, show (x * a) * a⁻¹ = x, from mul_inv_cancel_right x a,
  right_inv := assume x, show (x * a⁻¹) * a = x, from inv_mul_cancel_right x a }

attribute [to_additive equiv.add_right._proof_1] equiv.mul_right._proof_1
attribute [to_additive equiv.add_right._proof_2] equiv.mul_right._proof_2
attribute [to_additive equiv.add_right] equiv.mul_right

protected def inv (α) [group α] : α ≃ α :=
{ to_fun    := λa, a⁻¹,
  inv_fun   := λa, a⁻¹,
  left_inv  := assume a, inv_inv a,
  right_inv := assume a, inv_inv a }

attribute [to_additive equiv.neg._proof_1] equiv.inv._proof_1
attribute [to_additive equiv.neg._proof_2] equiv.inv._proof_2
attribute [to_additive equiv.neg] equiv.inv

def units_equiv_ne_zero (α : Type*) [field α] : units α ≃ {a : α | a ≠ 0} :=
⟨λ a, ⟨a.1, units.ne_zero _⟩, λ a, units.mk0 _ a.2, λ ⟨_, _, _, _⟩, units.ext rfl, λ ⟨_, _⟩, rfl⟩

@[simp] lemma coe_units_equiv_ne_zero [field α] (a : units α) :
  ((units_equiv_ne_zero α a) : α) = a := rfl

end group

section instances

variables (e : α ≃ β)

protected def has_zero [has_zero β] : has_zero α := ⟨e.symm 0⟩
lemma zero_def [has_zero β] : @has_zero.zero _ (equiv.has_zero e) = e.symm 0 := rfl

protected def has_one [has_one β] : has_one α := ⟨e.symm 1⟩
lemma one_def [has_one β] : @has_one.one _ (equiv.has_one e) = e.symm 1 := rfl

protected def has_mul [has_mul β] : has_mul α := ⟨λ x y, e.symm (e x * e y)⟩
lemma mul_def [has_mul β] (x y : α) :
  @has_mul.mul _ (equiv.has_mul e) x y = e.symm (e x * e y) := rfl

protected def has_add [has_add β] : has_add α := ⟨λ x y, e.symm (e x + e y)⟩
lemma add_def [has_add β] (x y : α) :
  @has_add.add _ (equiv.has_add e) x y = e.symm (e x + e y) := rfl

protected def has_inv [has_inv β] : has_inv α := ⟨λ x, e.symm (e x)⁻¹⟩
lemma inv_def [has_inv β] (x : α) : @has_inv.inv _ (equiv.has_inv e) x = e.symm (e x)⁻¹ := rfl

protected def has_neg [has_neg β] : has_neg α := ⟨λ x, e.symm (-e x)⟩
lemma neg_def [has_neg β] (x : α) : @has_neg.neg _ (equiv.has_neg e) x = e.symm (-e x) := rfl

protected def semigroup [semigroup β] : semigroup α :=
{ mul_assoc := by simp [mul_def, mul_assoc],
  ..equiv.has_mul e }

protected def comm_semigroup [comm_semigroup β] : comm_semigroup α :=
{ mul_comm := by simp [mul_def, mul_comm],
  ..equiv.semigroup e }

protected def monoid [monoid β] : monoid α :=
{ one_mul := by simp [mul_def, one_def],
  mul_one := by simp [mul_def, one_def],
  ..equiv.semigroup e,
  ..equiv.has_one e }

protected def comm_monoid [comm_monoid β] : comm_monoid α :=
{ ..equiv.comm_semigroup e,
  ..equiv.monoid e }

protected def group [group β] : group α :=
{ mul_left_inv := by simp [mul_def, inv_def, one_def],
  ..equiv.monoid e,
  ..equiv.has_inv e }

protected def comm_group [comm_group β] : comm_group α :=
{ ..equiv.group e,
  ..equiv.comm_semigroup e }

protected def add_semigroup [add_semigroup β] : add_semigroup α :=
@additive.add_semigroup _ (@equiv.semigroup _ _ e multiplicative.semigroup)

protected def add_comm_semigroup [add_comm_semigroup β] : add_comm_semigroup α :=
@additive.add_comm_semigroup _ (@equiv.comm_semigroup _ _ e multiplicative.comm_semigroup)

protected def add_monoid [add_monoid β] : add_monoid α :=
@additive.add_monoid _ (@equiv.monoid _ _ e multiplicative.monoid)

protected def add_comm_monoid [add_comm_monoid β] : add_comm_monoid α :=
@additive.add_comm_monoid _ (@equiv.comm_monoid _ _ e multiplicative.comm_monoid)

protected def add_group [add_group β] : add_group α :=
@additive.add_group _ (@equiv.group _ _ e multiplicative.group)

protected def add_comm_group [add_comm_group β] : add_comm_group α :=
@additive.add_comm_group _ (@equiv.comm_group _ _ e multiplicative.comm_group)

protected def semiring [semiring β] : semiring α :=
{ right_distrib := by simp [mul_def, add_def, add_mul],
  left_distrib := by simp [mul_def, add_def, mul_add],
  zero_mul := by simp [mul_def, zero_def],
  mul_zero := by simp [mul_def, zero_def],
  ..equiv.has_zero e,
  ..equiv.has_mul e,
  ..equiv.has_add e,
  ..equiv.monoid e,
  ..equiv.add_comm_monoid e }

protected def comm_semiring [comm_semiring β] : comm_semiring α :=
{ ..equiv.semiring e,
  ..equiv.comm_monoid e }

protected def ring [ring β] : ring α :=
{ ..equiv.semiring e,
  ..equiv.add_comm_group e }

protected def comm_ring [comm_ring β] : comm_ring α :=
{ ..equiv.comm_monoid e,
  ..equiv.ring e }

protected def zero_ne_one_class [zero_ne_one_class β] : zero_ne_one_class α :=
{ zero_ne_one := by simp [zero_def, one_def],
  ..equiv.has_zero e,
  ..equiv.has_one e }

protected def nonzero_comm_ring [nonzero_comm_ring β] : nonzero_comm_ring α :=
{ ..equiv.zero_ne_one_class e,
  ..equiv.comm_ring e }

protected def domain [domain β] : domain α :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := by simp [mul_def, zero_def, equiv.eq_symm_apply],
  ..equiv.has_zero e,
  ..equiv.zero_ne_one_class e,
  ..equiv.has_mul e,
  ..equiv.ring e }

protected def integral_domain [integral_domain β] : integral_domain α :=
{ ..equiv.domain e,
  ..equiv.nonzero_comm_ring e }

protected def division_ring [division_ring β] : division_ring α :=
{ inv_mul_cancel := λ _,
    by simp [mul_def, inv_def, zero_def, one_def, (equiv.symm_apply_eq _).symm];
      exact inv_mul_cancel,
  mul_inv_cancel := λ _,
    by simp [mul_def, inv_def, zero_def, one_def, (equiv.symm_apply_eq _).symm];
      exact mul_inv_cancel,
  ..equiv.has_zero e,
  ..equiv.has_one e,
  ..equiv.domain e,
  ..equiv.has_inv e }

protected def field [field β] : field α :=
{ ..equiv.integral_domain e,
  ..equiv.division_ring e }

protected def discrete_field [discrete_field β] : discrete_field α :=
{ has_decidable_eq := equiv.decidable_eq e,
  inv_zero := by simp [mul_def, inv_def, zero_def],
  ..equiv.has_mul e,
  ..equiv.has_inv e,
  ..equiv.has_zero e,
  ..equiv.field e }

end instances
end equiv

structure ring_equiv (α β : Type*) [ring α] [ring β] extends α ≃ β :=
(hom : is_ring_hom to_fun)

infix ` ≃r `:50 := ring_equiv

namespace ring_equiv

variables [ring α] [ring β] [ring γ]

instance {e : α ≃r β} : is_ring_hom e.to_equiv := hom _

protected def refl (α : Type*) [ring α] : α ≃r α :=
{ hom := is_ring_hom.id, .. equiv.refl α }

protected def symm {α β : Type*} [ring α] [ring β] (e : α ≃r β) : β ≃r α :=
{ hom := ⟨(equiv.symm_apply_eq _).2 e.hom.1.symm,
    λ x y, (equiv.symm_apply_eq _).2 $ show _ = e.to_equiv.to_fun _, by rw [e.2.2, e.1.4, e.1.4],
    λ x y, (equiv.symm_apply_eq _).2 $ show _ = e.to_equiv.to_fun _, by rw [e.2.3, e.1.4, e.1.4]⟩,
  .. e.to_equiv.symm }

protected def trans {α β γ : Type*} [ring α] [ring β] [ring γ]
  (e₁ : α ≃r β) (e₂ : β ≃r γ) : α ≃r γ :=
{ hom := is_ring_hom.comp _ _, .. e₁.1.trans e₂.1  }

end ring_equiv

namespace mv_polynomial

variables (α) [comm_ring α]
variables [decidable_eq α] [decidable_eq β] [decidable_eq γ]

def ring_equiv_of_equiv (e : β ≃ γ) : mv_polynomial β α ≃r mv_polynomial γ α :=
{ to_fun := eval₂ C (X ∘ e),
  inv_fun := eval₂ C (X ∘ e.symm),
  left_inv := λ f, induction_on f
    (λ r, by rw [eval₂_C, eval₂_C])
    (λ p q hp hq, by rw [eval₂_add, eval₂_add, hp, hq])
    (λ p s hp, by simp only [eval₂_mul, eval₂_X, hp, (∘), equiv.inverse_apply_apply]),
  right_inv := λ f, induction_on f
    (λ r, by rw [eval₂_C, eval₂_C])
    (λ p q hp hq, by rw [eval₂_add, eval₂_add, hp, hq])
    (λ p s hp, by simp only [eval₂_mul, eval₂_X, hp, (∘), equiv.apply_inverse_apply]),
  hom := by apply eval₂.is_ring_hom }

variables (β)
set_option class.instance_max_depth 10
def of_option : mv_polynomial (option β) α → polynomial (mv_polynomial β α) :=
eval₂ (polynomial.C ∘ C) (λ x, option.rec_on x polynomial.X (polynomial.C ∘ X))

def to_option : polynomial (mv_polynomial β α) → mv_polynomial (option β) α :=
polynomial.eval₂ (eval₂ C (X ∘ some)) (X none)

variables {α β}
theorem of_option_C (r : α) : of_option α β (C r) = polynomial.C (C r) :=
by convert eval₂_C _ _ _; convert is_semiring_hom.comp _ _; apply_instance

theorem of_option_X_none : of_option α β (X none) = polynomial.X :=
by convert eval₂_X _ _ _; convert is_semiring_hom.comp _ _; apply_instance

theorem of_option_X_some (n : β) : of_option α β (X (some n)) = polynomial.C (X n) :=
by convert eval₂_X _ _ _; convert is_semiring_hom.comp _ _; apply_instance

theorem of_option_add (p q) : of_option α β (p + q) = of_option α β p + of_option α β q :=
by convert eval₂_add _ _; convert is_semiring_hom.comp _ _; apply_instance

theorem of_option_mul (p q) : of_option α β (p * q) = of_option α β p * of_option α β q :=
by convert eval₂_mul _ _; convert is_semiring_hom.comp _ _; apply_instance

theorem to_option_C (g) : to_option α β (polynomial.C g) = eval₂ C (X ∘ some) g :=
by apply polynomial.eval₂_C _ _; apply eval₂.is_semiring_hom _ _; convert is_ring_hom.is_semiring_hom C; apply C.is_ring_hom

theorem to_option_C_C (r : α) : to_option α β (polynomial.C (C r)) = C r :=
by rw to_option_C; apply eval₂_C _ _ _; convert is_ring_hom.is_semiring_hom C; apply C.is_ring_hom

theorem to_option_C_X (n : β) : to_option α β (polynomial.C (X n)) = X (some n) :=
by rw to_option_C; apply eval₂_X _ _ _; convert is_ring_hom.is_semiring_hom C; apply C.is_ring_hom

theorem to_option_X : to_option α β (polynomial.X) = X none :=
by apply polynomial.eval₂_X _ _; apply eval₂.is_semiring_hom _ _; convert is_ring_hom.is_semiring_hom C; apply C.is_ring_hom

theorem to_option_add (p q) : to_option α β (p + q) = to_option α β p + to_option α β q :=
by apply polynomial.eval₂_add _ _; apply eval₂.is_semiring_hom _ _; convert is_ring_hom.is_semiring_hom C; apply C.is_ring_hom

theorem to_option_mul (p q) : to_option α β (p * q) = to_option α β p * to_option α β q :=
by apply polynomial.eval₂_mul _ _; apply eval₂.is_semiring_hom _ _; convert is_ring_hom.is_semiring_hom C; apply C.is_ring_hom

set_option class.instance_max_depth 15
theorem to_option_of_option (f) : to_option α β (of_option α β f) = f :=
induction_on f
  (λ r, by rw [of_option_C, to_option_C_C])
  (λ p q hp hq, by rw [of_option_add, to_option_add, hp, hq])
  (λ p n h, option.rec_on n (by rw [of_option_mul, to_option_mul, h, of_option_X_none, to_option_X]) $ λ n,
    by rw [of_option_mul, to_option_mul, h, of_option_X_some, to_option_C_X])

theorem of_option_to_option (f : polynomial (mv_polynomial β α)) : of_option α β (to_option α β f) = f :=
polynomial.induction_on f
  (λ g, induction_on g
    (λ r, by rw [to_option_C_C, of_option_C])
    (λ p q hp hq, by rw [polynomial.C_add, to_option_add, of_option_add, hp, hq])
    (λ p n h, by rw [polynomial.C_mul, to_option_mul, of_option_mul, h, to_option_C_X, of_option_X_some]))
  (λ p q hp hq, by rw [to_option_add, of_option_add, hp, hq])
  (λ n g h, by rw [to_option_mul, of_option_mul, pow_succ', to_option_mul, of_option_mul,
    ← mul_assoc, ← of_option_mul, ← to_option_mul, h, to_option_X, of_option_X_none, mul_assoc])

instance option_ring : ring (mv_polynomial (option β) α) :=
mv_polynomial.ring

instance polynomial_ring : ring (polynomial (mv_polynomial β α)) :=
@comm_ring.to_ring _ polynomial.comm_ring

def option_ring_equiv : mv_polynomial (option β) α ≃r polynomial (mv_polynomial β α) :=
{ to_fun := of_option α β,
  inv_fun := to_option α β,
  left_inv := to_option_of_option,
  right_inv := of_option_to_option,
  hom := ⟨of_option_C 1, of_option_mul, of_option_add⟩ }

def pempty_ring_equiv : mv_polynomial pempty α ≃r α :=
{ to_fun := mv_polynomial.eval₂ id $ pempty.rec _,
  inv_fun := C,
  left_inv := λ f, induction_on f (λ r, congr_arg _ $ eval₂_C _ _ _)
    (λ p q hp hq, by rw [eval₂_add, C_add, hp, hq])
    (λ p, pempty.rec _),
  right_inv := λ r, eval₂_C _ _ _,
  hom := eval₂.is_ring_hom _ _ }

end mv_polynomial

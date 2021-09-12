/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import algebra.module.basic
import algebra.regular.smul
import algebra.ring.pi

/-!
# Pi instances for module and multiplicative actions

This file defines instances for module, mul_action and related structures on Pi Types
-/

namespace pi
universes u v w
variable {I : Type u}     -- The indexing type
variable {f : I → Type v} -- The family of types already equipped with instances
variables (x y : Π i, f i) (i : I)

@[to_additive pi.has_vadd]
instance has_scalar {α : Type*} [Π i, has_scalar α $ f i] :
  has_scalar α (Π i : I, f i) :=
⟨λ s x, λ i, s • (x i)⟩

@[to_additive]
lemma smul_def {α : Type*} [Π i, has_scalar α $ f i] (s : α) : s • x = λ i, s • x i := rfl
@[simp, to_additive]
lemma smul_apply {α : Type*} [Π i, has_scalar α $ f i] (s : α) : (s • x) i = s • x i := rfl

@[to_additive pi.has_vadd']
instance has_scalar' {g : I → Type*} [Π i, has_scalar (f i) (g i)] :
  has_scalar (Π i, f i) (Π i : I, g i) :=
⟨λ s x, λ i, (s i) • (x i)⟩

@[simp, to_additive]
lemma smul_apply' {g : I → Type*} [∀ i, has_scalar (f i) (g i)] (s : Π i, f i) (x : Π i, g i) :
  (s • x) i = s i • x i :=
rfl

lemma _root_.is_smul_regular.pi {α : Type*} [Π i, has_scalar α $ f i] {k : α}
  (hk : Π i, is_smul_regular (f i) k) : is_smul_regular (Π i, f i) k :=
λ _ _ h, funext $ λ i, hk i (congr_fun h i : _)

instance is_scalar_tower {α β : Type*}
  [has_scalar α β] [Π i, has_scalar β $ f i] [Π i, has_scalar α $ f i]
  [Π i, is_scalar_tower α β (f i)] : is_scalar_tower α β (Π i : I, f i) :=
⟨λ x y z, funext $ λ i, smul_assoc x y (z i)⟩

instance is_scalar_tower' {g : I → Type*} {α : Type*}
  [Π i, has_scalar α $ f i] [Π i, has_scalar (f i) (g i)] [Π i, has_scalar α $ g i]
  [Π i, is_scalar_tower α (f i) (g i)] : is_scalar_tower α (Π i : I, f i) (Π i : I, g i) :=
⟨λ x y z, funext $ λ i, smul_assoc x (y i) (z i)⟩

instance is_scalar_tower'' {g : I → Type*} {h : I → Type*}
  [Π i, has_scalar (f i) (g i)] [Π i, has_scalar (g i) (h i)] [Π i, has_scalar (f i) (h i)]
  [Π i, is_scalar_tower (f i) (g i) (h i)] : is_scalar_tower (Π i, f i) (Π i, g i) (Π i, h i) :=
⟨λ x y z, funext $ λ i, smul_assoc (x i) (y i) (z i)⟩

@[to_additive]
instance smul_comm_class {α β : Type*}
  [Π i, has_scalar α $ f i] [Π i, has_scalar β $ f i] [∀ i, smul_comm_class α β (f i)] :
  smul_comm_class α β (Π i : I, f i) :=
⟨λ x y z, funext $ λ i, smul_comm x y (z i)⟩

@[to_additive]
instance smul_comm_class' {g : I → Type*} {α : Type*}
  [Π i, has_scalar α $ g i] [Π i, has_scalar (f i) (g i)] [∀ i, smul_comm_class α (f i) (g i)] :
  smul_comm_class α (Π i : I, f i) (Π i : I, g i) :=
⟨λ x y z, funext $ λ i, smul_comm x (y i) (z i)⟩

@[to_additive]
instance smul_comm_class'' {g : I → Type*} {h : I → Type*}
  [Π i, has_scalar (g i) (h i)] [Π i, has_scalar (f i) (h i)]
  [∀ i, smul_comm_class (f i) (g i) (h i)] : smul_comm_class (Π i, f i) (Π i, g i) (Π i, h i) :=
⟨λ x y z, funext $ λ i, smul_comm (x i) (y i) (z i)⟩

/-- If `f i` has a faithful scalar action for a given `i`, then so does `Π i, f i`. This is
not an instance as `i` cannot be inferred. -/
@[to_additive pi.has_faithful_vadd_at]
lemma has_faithful_scalar_at {α : Type*}
  [Π i, has_scalar α $ f i] [Π i, nonempty (f i)] (i : I) [has_faithful_scalar α (f i)] :
  has_faithful_scalar α (Π i, f i) :=
⟨λ x y h, eq_of_smul_eq_smul $ λ a : f i, begin
  classical,
  have := congr_fun (h $ function.update (λ j, classical.choice (‹Π i, nonempty (f i)› j)) i a) i,
  simpa using this,
end⟩

@[to_additive pi.has_faithful_vadd]
instance has_faithful_scalar {α : Type*}
  [nonempty I] [Π i, has_scalar α $ f i] [Π i, nonempty (f i)] [Π i, has_faithful_scalar α (f i)] :
  has_faithful_scalar α (Π i, f i) :=
let ⟨i⟩ := ‹nonempty I› in has_faithful_scalar_at i

instance smul_with_zero (α) [has_zero α]
  [Π i, has_zero (f i)] [Π i, smul_with_zero α (f i)] :
  smul_with_zero α (Π i, f i) :=
{ smul_zero := λ _, funext $ λ _, smul_zero' (f _) _,
  zero_smul := λ _, funext $ λ _, zero_smul _ _,
  ..pi.has_scalar }

instance smul_with_zero' {g : I → Type*} [Π i, has_zero (g i)]
  [Π i, has_zero (f i)] [Π i, smul_with_zero (g i) (f i)] :
  smul_with_zero (Π i, g i) (Π i, f i) :=
{ smul_zero := λ _, funext $ λ _, smul_zero' (f _) _,
  zero_smul := λ _, funext $ λ _, zero_smul _ _,
  ..pi.has_scalar' }

@[to_additive]
instance mul_action (α) {m : monoid α} [Π i, mul_action α $ f i] :
  @mul_action α (Π i : I, f i) m :=
{ smul := (•),
  mul_smul := λ r s f, funext $ λ i, mul_smul _ _ _,
  one_smul := λ f, funext $ λ i, one_smul α _ }

@[to_additive]
instance mul_action' {g : I → Type*} {m : Π i, monoid (f i)} [Π i, mul_action (f i) (g i)] :
  @mul_action (Π i, f i) (Π i : I, g i) (@pi.monoid I f m) :=
{ smul := (•),
  mul_smul := λ r s f, funext $ λ i, mul_smul _ _ _,
  one_smul := λ f, funext $ λ i, one_smul _ _ }

instance mul_action_with_zero (α) [monoid_with_zero α]
  [Π i, has_zero (f i)] [Π i, mul_action_with_zero α (f i)] :
  mul_action_with_zero α (Π i, f i) :=
{ ..pi.mul_action _,
  ..pi.smul_with_zero _ }

instance mul_action_with_zero' {g : I → Type*} [Π i, monoid_with_zero (g i)]
  [Π i, has_zero (f i)] [Π i, mul_action_with_zero (g i) (f i)] :
  mul_action_with_zero (Π i, g i) (Π i, f i) :=
{ ..pi.mul_action',
  ..pi.smul_with_zero' }

instance distrib_mul_action (α) {m : monoid α} {n : ∀ i, add_monoid $ f i}
  [∀ i, distrib_mul_action α $ f i] :
  @distrib_mul_action α (Π i : I, f i) m (@pi.add_monoid I f n) :=
{ smul_zero := λ c, funext $ λ i, smul_zero _,
  smul_add := λ c f g, funext $ λ i, smul_add _ _ _,
  ..pi.mul_action _ }

instance distrib_mul_action' {g : I → Type*} {m : Π i, monoid (f i)} {n : Π i, add_monoid $ g i}
  [Π i, distrib_mul_action (f i) (g i)] :
  @distrib_mul_action (Π i, f i) (Π i : I, g i) (@pi.monoid I f m) (@pi.add_monoid I g n) :=
{ smul_add := by { intros, ext x, apply smul_add },
  smul_zero := by { intros, ext x, apply smul_zero } }

lemma single_smul {α} [monoid α] [Π i, add_monoid $ f i]
  [Π i, distrib_mul_action α $ f i] [decidable_eq I] (i : I) (r : α) (x : f i) :
  single i (r • x) = r • single i x :=
single_op (λ i : I, ((•) r : f i → f i)) (λ j, smul_zero _) _ _

/-- A version of `pi.single_smul` for non-dependent functions. It is useful in cases Lean fails
to apply `pi.single_smul`. -/
lemma single_smul'' {α β} [monoid α] [add_monoid β]
  [distrib_mul_action α β] [decidable_eq I] (i : I) (r : α) (x : β) :
  single i (r • x) = r • single i x :=
single_smul i r x

lemma single_smul' {g : I → Type*} [Π i, monoid_with_zero (f i)] [Π i, add_monoid (g i)]
  [Π i, distrib_mul_action (f i) (g i)] [decidable_eq I] (i : I) (r : f i) (x : g i) :
  single i (r • x) = single i r • single i x :=
single_op₂ (λ i : I, ((•) : f i → g i → g i)) (λ j, smul_zero _) _ _ _

instance mul_distrib_mul_action (α) {m : monoid α} {n : Π i, monoid $ f i}
  [Π i, mul_distrib_mul_action α $ f i] :
  @mul_distrib_mul_action α (Π i : I, f i) m (@pi.monoid I f n) :=
{ smul_one := λ c, funext $ λ i, smul_one _,
  smul_mul := λ c f g, funext $ λ i, smul_mul' _ _ _,
  ..pi.mul_action _ }

instance mul_distrib_mul_action' {g : I → Type*} {m : Π i, monoid (f i)} {n : Π i, monoid $ g i}
  [Π i, mul_distrib_mul_action (f i) (g i)] :
  @mul_distrib_mul_action (Π i, f i) (Π i : I, g i) (@pi.monoid I f m) (@pi.monoid I g n) :=
{ smul_mul := by { intros, ext x, apply smul_mul' },
  smul_one := by { intros, ext x, apply smul_one } }

variables (I f)

instance module (α) {r : semiring α} {m : ∀ i, add_comm_monoid $ f i}
  [∀ i, module α $ f i] :
  @module α (Π i : I, f i) r (@pi.add_comm_monoid I f m) :=
{ add_smul := λ c f g, funext $ λ i, add_smul _ _ _,
  zero_smul := λ f, funext $ λ i, zero_smul α _,
  ..pi.distrib_mul_action _ }

variables {I f}

instance module' {g : I → Type*} {r : Π i, semiring (f i)} {m : Π i, add_comm_monoid (g i)}
  [Π i, module (f i) (g i)] :
  module (Π i, f i) (Π i, g i) :=
{ add_smul := by { intros, ext1, apply add_smul },
  zero_smul := by { intros, ext1, apply zero_smul } }

instance (α) {r : semiring α} {m : Π i, add_comm_monoid $ f i}
  [Π i, module α $ f i] [∀ i, no_zero_smul_divisors α $ f i] :
  no_zero_smul_divisors α (Π i : I, f i) :=
⟨λ c x h, or_iff_not_imp_left.mpr (λ hc, funext
  (λ i, (smul_eq_zero.mp (congr_fun h i)).resolve_left hc))⟩

end pi

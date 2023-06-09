/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import algebra.group.pi
import group_theory.group_action.defs

/-!
# Pi instances for multiplicative actions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines instances for mul_action and related structures on Pi types.

## See also

* `group_theory.group_action.option`
* `group_theory.group_action.prod`
* `group_theory.group_action.sigma`
* `group_theory.group_action.sum`
-/

universes u v w
variable {I : Type u}     -- The indexing type
variable {f : I → Type v} -- The family of types already equipped with instances
variables (x y : Π i, f i) (i : I)

namespace pi

@[to_additive pi.has_vadd']
instance has_smul' {g : I → Type*} [Π i, has_smul (f i) (g i)] :
  has_smul (Π i, f i) (Π i : I, g i) :=
⟨λ s x, λ i, (s i) • (x i)⟩

@[simp, to_additive]
lemma smul_apply' {g : I → Type*} [∀ i, has_smul (f i) (g i)] (s : Π i, f i) (x : Π i, g i) :
  (s • x) i = s i • x i :=
rfl

@[to_additive]
instance is_scalar_tower {α β : Type*}
  [has_smul α β] [Π i, has_smul β $ f i] [Π i, has_smul α $ f i]
  [Π i, is_scalar_tower α β (f i)] : is_scalar_tower α β (Π i : I, f i) :=
⟨λ x y z, funext $ λ i, smul_assoc x y (z i)⟩

@[to_additive]
instance is_scalar_tower' {g : I → Type*} {α : Type*}
  [Π i, has_smul α $ f i] [Π i, has_smul (f i) (g i)] [Π i, has_smul α $ g i]
  [Π i, is_scalar_tower α (f i) (g i)] : is_scalar_tower α (Π i : I, f i) (Π i : I, g i) :=
⟨λ x y z, funext $ λ i, smul_assoc x (y i) (z i)⟩

@[to_additive]
instance is_scalar_tower'' {g : I → Type*} {h : I → Type*}
  [Π i, has_smul (f i) (g i)] [Π i, has_smul (g i) (h i)] [Π i, has_smul (f i) (h i)]
  [Π i, is_scalar_tower (f i) (g i) (h i)] : is_scalar_tower (Π i, f i) (Π i, g i) (Π i, h i) :=
⟨λ x y z, funext $ λ i, smul_assoc (x i) (y i) (z i)⟩

@[to_additive]
instance smul_comm_class {α β : Type*}
  [Π i, has_smul α $ f i] [Π i, has_smul β $ f i] [∀ i, smul_comm_class α β (f i)] :
  smul_comm_class α β (Π i : I, f i) :=
⟨λ x y z, funext $ λ i, smul_comm x y (z i)⟩

@[to_additive]
instance smul_comm_class' {g : I → Type*} {α : Type*}
  [Π i, has_smul α $ g i] [Π i, has_smul (f i) (g i)] [∀ i, smul_comm_class α (f i) (g i)] :
  smul_comm_class α (Π i : I, f i) (Π i : I, g i) :=
⟨λ x y z, funext $ λ i, smul_comm x (y i) (z i)⟩

@[to_additive]
instance smul_comm_class'' {g : I → Type*} {h : I → Type*}
  [Π i, has_smul (g i) (h i)] [Π i, has_smul (f i) (h i)]
  [∀ i, smul_comm_class (f i) (g i) (h i)] : smul_comm_class (Π i, f i) (Π i, g i) (Π i, h i) :=
⟨λ x y z, funext $ λ i, smul_comm (x i) (y i) (z i)⟩

@[to_additive]
instance {α : Type*} [Π i, has_smul α $ f i] [Π i, has_smul αᵐᵒᵖ $ f i]
  [∀ i, is_central_scalar α (f i)] : is_central_scalar α (Π i, f i) :=
⟨λ r m, funext $ λ i, op_smul_eq_smul _ _⟩

/-- If `f i` has a faithful scalar action for a given `i`, then so does `Π i, f i`. This is
not an instance as `i` cannot be inferred. -/
@[to_additive pi.has_faithful_vadd_at "If `f i` has a faithful additive action for a given `i`, then
so does `Π i, f i`. This is not an instance as `i` cannot be inferred"]
lemma has_faithful_smul_at {α : Type*}
  [Π i, has_smul α $ f i] [Π i, nonempty (f i)] (i : I) [has_faithful_smul α (f i)] :
  has_faithful_smul α (Π i, f i) :=
⟨λ x y h, eq_of_smul_eq_smul $ λ a : f i, begin
  classical,
  have := congr_fun (h $ function.update (λ j, classical.choice (‹Π i, nonempty (f i)› j)) i a) i,
  simpa using this,
end⟩

@[to_additive pi.has_faithful_vadd]
instance has_faithful_smul {α : Type*}
  [nonempty I] [Π i, has_smul α $ f i] [Π i, nonempty (f i)] [Π i, has_faithful_smul α (f i)] :
  has_faithful_smul α (Π i, f i) :=
let ⟨i⟩ := ‹nonempty I› in has_faithful_smul_at i

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

instance smul_zero_class (α) {n : ∀ i, has_zero $ f i}
  [∀ i, smul_zero_class α $ f i] :
  @smul_zero_class α (Π i : I, f i) (@pi.has_zero I f n) :=
{ smul_zero := λ c, funext $ λ i, smul_zero _ }

instance smul_zero_class' {g : I → Type*} {n : Π i, has_zero $ g i}
  [Π i, smul_zero_class (f i) (g i)] :
  @smul_zero_class (Π i, f i) (Π i : I, g i) (@pi.has_zero I g n) :=
{ smul_zero := by { intros, ext x, apply smul_zero } }

instance distrib_smul (α) {n : ∀ i, add_zero_class $ f i} [∀ i, distrib_smul α $ f i] :
  @distrib_smul α (Π i : I, f i) (@pi.add_zero_class I f n) :=
{ smul_add := λ c f g, funext $ λ i, smul_add _ _ _ }

instance distrib_smul' {g : I → Type*} {n : Π i, add_zero_class $ g i}
  [Π i, distrib_smul (f i) (g i)] :
  @distrib_smul (Π i, f i) (Π i : I, g i) (@pi.add_zero_class I g n) :=
{ smul_add := by { intros, ext x, apply smul_add } }

instance distrib_mul_action (α) {m : monoid α} {n : ∀ i, add_monoid $ f i}
  [∀ i, distrib_mul_action α $ f i] :
  @distrib_mul_action α (Π i : I, f i) m (@pi.add_monoid I f n) :=
{ ..pi.mul_action _,
  ..pi.distrib_smul _ }

instance distrib_mul_action' {g : I → Type*} {m : Π i, monoid (f i)} {n : Π i, add_monoid $ g i}
  [Π i, distrib_mul_action (f i) (g i)] :
  @distrib_mul_action (Π i, f i) (Π i : I, g i) (@pi.monoid I f m) (@pi.add_monoid I g n) :=
{ .. pi.mul_action',
  .. pi.distrib_smul' }

lemma single_smul {α} [monoid α] [Π i, add_monoid $ f i]
  [Π i, distrib_mul_action α $ f i] [decidable_eq I] (i : I) (r : α) (x : f i) :
  single i (r • x) = r • single i x :=
single_op (λ i : I, ((•) r : f i → f i)) (λ j, smul_zero _) _ _

/-- A version of `pi.single_smul` for non-dependent functions. It is useful in cases Lean fails
to apply `pi.single_smul`. -/
lemma single_smul' {α β} [monoid α] [add_monoid β]
  [distrib_mul_action α β] [decidable_eq I] (i : I) (r : α) (x : β) :
  single i (r • x) = r • single i x :=
single_smul i r x

lemma single_smul₀ {g : I → Type*} [Π i, monoid_with_zero (f i)] [Π i, add_monoid (g i)]
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

end pi

namespace function

/-- Non-dependent version of `pi.has_smul`. Lean gets confused by the dependent instance if this
is not present. -/
@[to_additive "Non-dependent version of `pi.has_vadd`. Lean gets confused by the dependent instance
if this is not present."]
instance has_smul {ι R M : Type*} [has_smul R M] :
  has_smul R (ι → M) :=
pi.has_smul

/-- Non-dependent version of `pi.smul_comm_class`. Lean gets confused by the dependent instance if
this is not present. -/
@[to_additive "Non-dependent version of `pi.vadd_comm_class`. Lean gets confused by the dependent
instance if this is not present."]
instance smul_comm_class {ι α β M : Type*}
  [has_smul α M] [has_smul β M] [smul_comm_class α β M] :
  smul_comm_class α β (ι → M) :=
pi.smul_comm_class

@[to_additive]
lemma update_smul {α : Type*} [Π i, has_smul α (f i)] [decidable_eq I]
  (c : α) (f₁ : Π i, f i) (i : I) (x₁ : f i) :
  update (c • f₁) i (c • x₁) = c • update f₁ i x₁ :=
funext $ λ j, (apply_update (λ i, (•) c) f₁ i x₁ j).symm

end function

namespace set

@[to_additive]
lemma piecewise_smul {α : Type*} [Π i, has_smul α (f i)] (s : set I) [Π i, decidable (i ∈ s)]
  (c : α) (f₁ g₁ : Π i, f i) :
  s.piecewise (c • f₁) (c • g₁) = c • s.piecewise f₁ g₁ :=
s.piecewise_op _ _ (λ _, (•) c)

end set

section extend

@[to_additive] lemma function.extend_smul {R α β γ : Type*} [has_smul R γ]
  (r : R) (f : α → β) (g : α → γ) (e : β → γ) :
  function.extend f (r • g) (r • e) = r • function.extend f g e :=
funext $ λ _, by convert (apply_dite ((•) r) _ _ _).symm

end extend

/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import algebra.hom.aut
import group_theory.group_action.units

/-!
# Group actions applied to various types of group

This file contains lemmas about `smul` on `group_with_zero`, and `group`.
-/

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

section mul_action

/-- `monoid.to_mul_action` is faithful on cancellative monoids. -/
@[to_additive /-" `add_monoid.to_add_action` is faithful on additive cancellative monoids. "-/]
instance right_cancel_monoid.to_has_faithful_scalar [right_cancel_monoid α] :
  has_faithful_scalar α α :=
⟨λ x y h, mul_right_cancel (h 1)⟩

section group
variables [group α] [mul_action α β]

@[simp, to_additive] lemma inv_smul_smul (c : α) (x : β) : c⁻¹ • c • x = x :=
by rw [smul_smul, mul_left_inv, one_smul]

@[simp, to_additive] lemma smul_inv_smul (c : α) (x : β) : c • c⁻¹ • x = x :=
by rw [smul_smul, mul_right_inv, one_smul]

/-- Given an action of a group `α` on `β`, each `g : α` defines a permutation of `β`. -/
@[to_additive, simps] def mul_action.to_perm (a : α) : equiv.perm β :=
⟨λ x, a • x, λ x, a⁻¹ • x, inv_smul_smul a, smul_inv_smul a⟩

/-- Given an action of an additive group `α` on `β`, each `g : α` defines a permutation of `β`. -/
add_decl_doc add_action.to_perm

/-- `mul_action.to_perm` is injective on faithful actions. -/
@[to_additive] lemma mul_action.to_perm_injective [has_faithful_scalar α β] :
  function.injective (mul_action.to_perm : α → equiv.perm β) :=
(show function.injective (equiv.to_fun ∘ mul_action.to_perm), from smul_left_injective').of_comp

variables (α) (β)

/-- Given an action of a group `α` on a set `β`, each `g : α` defines a permutation of `β`. -/
@[simps]
def mul_action.to_perm_hom : α →* equiv.perm β :=
{ to_fun := mul_action.to_perm,
  map_one' := equiv.ext $ one_smul α,
  map_mul' := λ u₁ u₂, equiv.ext $ mul_smul (u₁:α) u₂ }

/-- Given an action of a additive group `α` on a set `β`, each `g : α` defines a permutation of
`β`. -/
@[simps]
def add_action.to_perm_hom (α : Type*) [add_group α] [add_action α β] :
  α →+ additive (equiv.perm β) :=
{ to_fun := λ a, additive.of_mul $ add_action.to_perm a,
  map_zero' := equiv.ext $ zero_vadd α,
  map_add' := λ a₁ a₂, equiv.ext $ add_vadd a₁ a₂ }

/-- The tautological action by `equiv.perm α` on `α`.

This generalizes `function.End.apply_mul_action`.-/
instance equiv.perm.apply_mul_action (α : Type*) : mul_action (equiv.perm α) α :=
{ smul := λ f a, f a,
  one_smul := λ _, rfl,
  mul_smul := λ _ _ _, rfl }

@[simp] protected lemma equiv.perm.smul_def {α : Type*} (f : equiv.perm α) (a : α) : f • a = f a :=
rfl

/-- `equiv.perm.apply_mul_action` is faithful. -/
instance equiv.perm.apply_has_faithful_scalar (α : Type*) : has_faithful_scalar (equiv.perm α) α :=
⟨λ x y, equiv.ext⟩

variables {α} {β}

@[to_additive] lemma inv_smul_eq_iff {a : α} {x y : β} : a⁻¹ • x = y ↔ x = a • y :=
(mul_action.to_perm a).symm_apply_eq

@[to_additive] lemma eq_inv_smul_iff {a : α} {x y : β} : x = a⁻¹ • y ↔ a • x = y :=
(mul_action.to_perm a).eq_symm_apply

lemma smul_inv [group β] [smul_comm_class α β β] [is_scalar_tower α β β] (c : α) (x : β) :
  (c • x)⁻¹ = c⁻¹ • x⁻¹  :=
by rw [inv_eq_iff_mul_eq_one, smul_mul_smul, mul_right_inv, mul_right_inv, one_smul]

lemma smul_zpow [group β] [smul_comm_class α β β] [is_scalar_tower α β β]
  (c : α) (x : β) (p : ℤ) :
  (c • x) ^ p = c ^ p • x ^ p :=
by { cases p; simp [smul_pow, smul_inv] }

@[simp] lemma commute.smul_right_iff [has_mul β] [smul_comm_class α β β] [is_scalar_tower α β β]
  {a b : β} (r : α) :
  commute a (r • b) ↔ commute a b :=
⟨λ h, inv_smul_smul r b ▸ h.smul_right r⁻¹, λ h, h.smul_right r⟩

@[simp] lemma commute.smul_left_iff [has_mul β] [smul_comm_class α β β] [is_scalar_tower α β β]
  {a b : β} (r : α) :
  commute (r • a) b ↔ commute a b :=
by rw [commute.symm_iff, commute.smul_right_iff, commute.symm_iff]

@[to_additive] protected lemma mul_action.bijective (g : α) : function.bijective (λ b : β, g • b) :=
(mul_action.to_perm g).bijective

@[to_additive] protected lemma mul_action.injective (g : α) : function.injective (λ b : β, g • b) :=
(mul_action.bijective g).injective

@[to_additive] lemma smul_left_cancel (g : α) {x y : β} (h : g • x = g • y) : x = y :=
mul_action.injective g h

@[simp, to_additive] lemma smul_left_cancel_iff (g : α) {x y : β} : g • x = g • y ↔ x = y :=
(mul_action.injective g).eq_iff

@[to_additive] lemma smul_eq_iff_eq_inv_smul (g : α) {x y : β} :
  g • x = y ↔ x = g⁻¹ • y :=
(mul_action.to_perm g).apply_eq_iff_eq_symm_apply

end group

/-- `monoid.to_mul_action` is faithful on nontrivial cancellative monoids with zero. -/
instance cancel_monoid_with_zero.to_has_faithful_scalar [cancel_monoid_with_zero α] [nontrivial α] :
  has_faithful_scalar α α :=
⟨λ x y h, mul_left_injective₀ one_ne_zero (h 1)⟩

section gwz
variables [group_with_zero α] [mul_action α β]

@[simp]
lemma inv_smul_smul₀ {c : α} (hc : c ≠ 0) (x : β) : c⁻¹ • c • x = x :=
inv_smul_smul (units.mk0 c hc) x

@[simp]
lemma smul_inv_smul₀ {c : α} (hc : c ≠ 0) (x : β) : c • c⁻¹ • x = x :=
smul_inv_smul (units.mk0 c hc) x

lemma inv_smul_eq_iff₀ {a : α} (ha : a ≠ 0) {x y : β} : a⁻¹ • x = y ↔ x = a • y :=
(mul_action.to_perm (units.mk0 a ha)).symm_apply_eq

lemma eq_inv_smul_iff₀ {a : α} (ha : a ≠ 0) {x y : β} : x = a⁻¹ • y ↔ a • x = y :=
(mul_action.to_perm (units.mk0 a ha)).eq_symm_apply

@[simp] lemma commute.smul_right_iff₀ [has_mul β] [smul_comm_class α β β] [is_scalar_tower α β β]
  {a b : β} {c : α} (hc : c ≠ 0) :
  commute a (c • b) ↔ commute a b :=
commute.smul_right_iff (units.mk0 c hc)

@[simp] lemma commute.smul_left_iff₀ [has_mul β] [smul_comm_class α β β] [is_scalar_tower α β β]
  {a b : β} {c : α} (hc : c ≠ 0) :
  commute (c • a) b ↔ commute a b :=
commute.smul_left_iff (units.mk0 c hc)

end gwz

end mul_action

section distrib_mul_action

section group
variables [group α] [add_monoid β] [distrib_mul_action α β]

variables (β)

/-- Each element of the group defines an additive monoid isomorphism.

This is a stronger version of `mul_action.to_perm`. -/
@[simps {simp_rhs := tt}]
def distrib_mul_action.to_add_equiv (x : α) : β ≃+ β :=
{ .. distrib_mul_action.to_add_monoid_hom β x,
  .. mul_action.to_perm_hom α β x }

variables (α β)

/-- Each element of the group defines an additive monoid isomorphism.

This is a stronger version of `mul_action.to_perm_hom`. -/
@[simps]
def distrib_mul_action.to_add_aut : α →* add_aut β :=
{ to_fun := distrib_mul_action.to_add_equiv β,
  map_one' := add_equiv.ext (one_smul _),
  map_mul' := λ a₁ a₂, add_equiv.ext (mul_smul _ _) }

variables {α β}

theorem smul_eq_zero_iff_eq (a : α) {x : β} : a • x = 0 ↔ x = 0 :=
⟨λ h, by rw [← inv_smul_smul a x, h, smul_zero], λ h, h.symm ▸ smul_zero _⟩

theorem smul_ne_zero_iff_ne (a : α) {x : β} : a • x ≠ 0 ↔ x ≠ 0 :=
not_congr $ smul_eq_zero_iff_eq a

end group

section gwz
variables [group_with_zero α] [add_monoid β] [distrib_mul_action α β]

theorem smul_eq_zero_iff_eq' {a : α} (ha : a ≠ 0) {x : β} : a • x = 0 ↔ x = 0 :=
smul_eq_zero_iff_eq (units.mk0 a ha)

theorem smul_ne_zero_iff_ne' {a : α} (ha : a ≠ 0) {x : β} : a • x ≠ 0 ↔ x ≠ 0 :=
smul_ne_zero_iff_ne (units.mk0 a ha)

end gwz

end distrib_mul_action

section mul_distrib_mul_action
variables [group α] [monoid β] [mul_distrib_mul_action α β]

variables (β)

/-- Each element of the group defines a multiplicative monoid isomorphism.

This is a stronger version of `mul_action.to_perm`. -/
@[simps {simp_rhs := tt}]
def mul_distrib_mul_action.to_mul_equiv (x : α) : β ≃* β :=
{ .. mul_distrib_mul_action.to_monoid_hom β x,
  .. mul_action.to_perm_hom α β x }

variables (α β)

/-- Each element of the group defines an multiplicative monoid isomorphism.

This is a stronger version of `mul_action.to_perm_hom`. -/
@[simps]
def mul_distrib_mul_action.to_mul_aut : α →* mul_aut β :=
{ to_fun := mul_distrib_mul_action.to_mul_equiv β,
  map_one' := mul_equiv.ext (one_smul _),
  map_mul' := λ a₁ a₂, mul_equiv.ext (mul_smul _ _) }

variables {α β}

end mul_distrib_mul_action

section arrow

/-- If `G` acts on `A`, then it acts also on `A → B`, by `(g • F) a = F (g⁻¹ • a)`. -/
@[simps] def arrow_action {G A B : Type*} [group G] [mul_action G A] : mul_action G (A → B) :=
{ smul := λ g F a, F (g⁻¹ • a),
  one_smul := by { intro, simp only [inv_one, one_smul] },
  mul_smul := by { intros, simp only [mul_smul, mul_inv_rev] } }

local attribute [instance] arrow_action

/-- When `B` is a monoid, `arrow_action` is additionally a `mul_distrib_mul_action`. -/
def arrow_mul_distrib_mul_action {G A B : Type*} [group G] [mul_action G A] [monoid B] :
  mul_distrib_mul_action G (A → B) :=
{ smul_one := λ g, rfl,
  smul_mul := λ g f₁ f₂, rfl }

local attribute [instance] arrow_mul_distrib_mul_action

/-- Given groups `G H` with `G` acting on `A`, `G` acts by
  multiplicative automorphisms on `A → H`. -/
@[simps] def mul_aut_arrow {G A H} [group G] [mul_action G A] [monoid H] : G →* mul_aut (A → H) :=
mul_distrib_mul_action.to_mul_aut _ _

end arrow

namespace is_unit

section mul_action
variables [monoid α] [mul_action α β]

@[to_additive] lemma smul_left_cancel {a : α} (ha : is_unit a) {x y : β} :
  a • x = a • y ↔ x = y :=
let ⟨u, hu⟩ := ha in hu ▸ smul_left_cancel_iff u

end mul_action

section distrib_mul_action
variables [monoid α] [add_monoid β] [distrib_mul_action α β]

@[simp] theorem smul_eq_zero {u : α} (hu : is_unit u) {x : β} :
  u • x = 0 ↔ x = 0 :=
exists.elim hu $ λ u hu, hu ▸ smul_eq_zero_iff_eq u

end distrib_mul_action

end is_unit

section smul

variables [group α] [monoid β]

@[simp] lemma is_unit_smul_iff [mul_action α β] [smul_comm_class α β β] [is_scalar_tower α β β]
  (g : α) (m : β) : is_unit (g • m) ↔ is_unit m :=
⟨λ h, inv_smul_smul g m ▸ h.smul g⁻¹, is_unit.smul g⟩

lemma is_unit.smul_sub_iff_sub_inv_smul
  [add_group β] [distrib_mul_action α β] [is_scalar_tower α β β] [smul_comm_class α β β]
  (r : α) (a : β) : is_unit (r • 1 - a) ↔ is_unit (1 - r⁻¹ • a) :=
by rw [←is_unit_smul_iff r (1 - r⁻¹ • a), smul_sub, smul_inv_smul]

end smul

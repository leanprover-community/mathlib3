/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import group_theory.coset

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

open_locale big_operators
open function

/-- Typeclass for types with a scalar multiplication operation, denoted `•` (`\bu`) -/
class has_scalar (α : Type u) (γ : Type v) := (smul : α → γ → γ)

infixr ` • `:73 := has_scalar.smul

section prio
set_option default_priority 100 -- see Note [default priority]
/-- Typeclass for multiplicative actions by monoids. This generalizes group actions. -/
@[protect_proj] class mul_action (α : Type u) (β : Type v) [monoid α] extends has_scalar α β :=
(one_smul : ∀ b : β, (1 : α) • b = b)
(mul_smul : ∀ (x y : α) (b : β), (x * y) • b = x • y • b)
end prio

section
variables [monoid α] [mul_action α β]

theorem mul_smul (a₁ a₂ : α) (b : β) : (a₁ * a₂) • b = a₁ • a₂ • b := mul_action.mul_smul _ _ _

lemma smul_smul (a₁ a₂ : α) (b : β) : a₁ • a₂ • b = (a₁ * a₂) • b := (mul_smul _ _ _).symm

lemma smul_comm {α : Type u} {β : Type v} [comm_monoid α] [mul_action α β] (a₁ a₂ : α) (b : β) :
  a₁ • a₂ • b = a₂ • a₁ • b := by rw [←mul_smul, ←mul_smul, mul_comm]

variable (α)
@[simp] theorem one_smul (b : β) : (1 : α) • b = b := mul_action.one_smul _

variables {α}

@[simp] lemma units.inv_smul_smul (u : units α) (x : β) :
  (↑u⁻¹:α) • (u:α) • x = x :=
by rw [smul_smul, u.inv_mul, one_smul]

@[simp] lemma units.smul_inv_smul (u : units α) (x : β) :
  (u:α) • (↑u⁻¹:α) • x = x :=
by rw [smul_smul, u.mul_inv, one_smul]

/-- Pullback a multiplicative action along an injective map respecting `•`. -/
protected def function.injective.mul_action [has_scalar α γ] (f : γ → β)
  (hf : injective f) (smul : ∀ (c : α) x, f (c • x) = c • f x) :
  mul_action α γ :=
{ smul := (•),
  one_smul := λ x, hf $ (smul _ _).trans $ one_smul _ (f x),
  mul_smul := λ c₁ c₂ x, hf $ by simp only [smul, mul_smul] }

/-- Pushforward a multiplicative action along a surjective map respecting `•`. -/
protected def function.surjective.mul_action [has_scalar α γ] (f : β → γ) (hf : surjective f)
  (smul : ∀ (c : α) x, f (c • x) = c • f x) :
  mul_action α γ :=
{ smul := (•),
  one_smul := λ y, by { rcases hf y with ⟨x, rfl⟩, rw [← smul, one_smul] },
  mul_smul := λ c₁ c₂ y, by { rcases hf y with ⟨x, rfl⟩, simp only [← smul, mul_smul] } }

section gwz

variables {G : Type*} [group_with_zero G] [mul_action G β]

lemma inv_smul_smul' {c : G} (hc : c ≠ 0) (x : β) : c⁻¹ • c • x = x :=
(units.mk0 c hc).inv_smul_smul x

lemma smul_inv_smul' {c : G} (hc : c ≠ 0) (x : β) : c • c⁻¹ • x = x :=
(units.mk0 c hc).smul_inv_smul x

lemma inv_smul_eq_iff {a : G} (ha : a ≠ 0) {x y : β} : a⁻¹ • x = y ↔ x = a • y :=
by { split; intro h, rw [← h, smul_inv_smul' ha], rw [h, inv_smul_smul' ha] }

lemma eq_inv_smul_iff {a : G} (ha : a ≠ 0) {x y : β} : x = a⁻¹ • y ↔ a • x = y :=
by { split; intro h, rw [h, smul_inv_smul' ha], rw [← h, inv_smul_smul' ha] }

end gwz

variables (p : Prop) [decidable p]

lemma ite_smul (a₁ a₂ : α) (b : β) : (ite p a₁ a₂) • b = ite p (a₁ • b) (a₂ • b) :=
by split_ifs; refl

lemma smul_ite (a : α) (b₁ b₂ : β) : a • (ite p b₁ b₂) = ite p (a • b₁) (a • b₂) :=
by split_ifs; refl

end

namespace mul_action

variables (α) [monoid α]

/-- The regular action of a monoid on itself by left multiplication. -/
def regular : mul_action α α :=
{ smul := λ a₁ a₂, a₁ * a₂,
  one_smul := λ a, one_mul a,
  mul_smul := λ a₁ a₂ a₃, mul_assoc _ _ _, }

variables [mul_action α β]

/-- The orbit of an element under an action. -/
def orbit (b : β) := set.range (λ x : α, x • b)

variable {α}

lemma mem_orbit_iff {b₁ b₂ : β} : b₂ ∈ orbit α b₁ ↔ ∃ x : α, x • b₁ = b₂ :=
iff.rfl

@[simp] lemma mem_orbit (b : β) (x : α) : x • b ∈ orbit α b :=
⟨x, rfl⟩

@[simp] lemma mem_orbit_self (b : β) : b ∈ orbit α b :=
⟨1, by simp [mul_action.one_smul]⟩

variable (α)

/-- The stabilizer of an element under an action, i.e. what sends the element to itself. -/
def stabilizer (b : β) : set α :=
{x : α | x • b = b}

variable {α}

@[simp] lemma mem_stabilizer_iff {b : β} {x : α} :
  x ∈ stabilizer α b ↔ x • b = b := iff.rfl

variables (α) (β)

/-- The set of elements fixed under the whole action. -/
def fixed_points : set β := {b : β | ∀ x, x ∈ stabilizer α b}

variables {α} (β)

@[simp] lemma mem_fixed_points {b : β} :
  b ∈ fixed_points α β ↔ ∀ x : α, x • b = b := iff.rfl

lemma mem_fixed_points' {b : β} : b ∈ fixed_points α β ↔
  (∀ b', b' ∈ orbit α b → b' = b) :=
⟨λ h b h₁, let ⟨x, hx⟩ := mem_orbit_iff.1 h₁ in hx ▸ h x,
λ h b, mem_stabilizer_iff.2 (h _ (mem_orbit _ _))⟩

/-- An action of `α` on `β` and a monoid homomorphism `γ → α` induce an action of `γ` on `β`. -/
def comp_hom [monoid γ] (g : γ → α) [is_monoid_hom g] :
  mul_action γ β :=
{ smul := λ x b, (g x) • b,
  one_smul := by simp [is_monoid_hom.map_one g, mul_action.one_smul],
  mul_smul := by simp [is_monoid_hom.map_mul g, mul_action.mul_smul] }

instance (b : β) : is_submonoid (stabilizer α b) :=
{ one_mem := one_smul _ b,
  mul_mem := λ a a' (ha : a • b = b) (hb : a' • b = b),
    by rw [mem_stabilizer_iff, ←smul_smul, hb, ha] }

end mul_action

namespace mul_action
variables [group α] [mul_action α β]

section
open mul_action quotient_group

@[simp] lemma inv_smul_smul (c : α) (x : β) : c⁻¹ • c • x = x :=
(to_units α c).inv_smul_smul x

@[simp] lemma smul_inv_smul (c : α) (x : β) : c • c⁻¹ • x = x :=
(to_units α c).smul_inv_smul x

variables (α) (β)

/-- Given an action of a group `α` on a set `β`, each `g : α` defines a permutation of `β`. -/
def to_perm (g : α) : equiv.perm β :=
{ to_fun := (•) g,
  inv_fun := (•) g⁻¹,
  left_inv := inv_smul_smul g,
  right_inv := smul_inv_smul g }

variables {α} {β}

instance : is_group_hom (to_perm α β) :=
{ map_mul := λ x y, equiv.ext (λ a, mul_action.mul_smul x y a) }

protected lemma bijective (g : α) : bijective (λ b : β, g • b) :=
(to_perm α β g).bijective

lemma orbit_eq_iff {a b : β} :
   orbit α a = orbit α b ↔ a ∈ orbit α b:=
⟨λ h, h ▸ mem_orbit_self _,
λ ⟨x, (hx : x • b = a)⟩, set.ext (λ c, ⟨λ ⟨y, (hy : y • a = c)⟩, ⟨y * x,
  show (y * x) • b = c, by rwa [mul_action.mul_smul, hx]⟩,
  λ ⟨y, (hy : y • b = c)⟩, ⟨y * x⁻¹,
    show (y * x⁻¹) • a = c, by
      conv {to_rhs, rw [← hy, ← mul_one y, ← inv_mul_self x, ← mul_assoc,
        mul_action.mul_smul, hx]}⟩⟩)⟩

instance (b : β) : is_subgroup (stabilizer α b) :=
{ one_mem := mul_action.one_smul _,
  mul_mem := λ x y (hx : x • b = b) (hy : y • b = b),
    show (x * y) • b = b, by rw mul_action.mul_smul; simp *,
  inv_mem := λ x (hx : x • b = b), show x⁻¹ • b = b,
    by rw [← hx, ← mul_action.mul_smul, inv_mul_self, mul_action.one_smul, hx] }

@[simp] lemma mem_orbit_smul (g : α) (a : β) : a ∈ orbit α (g • a) :=
⟨g⁻¹, by simp⟩

@[simp] lemma smul_mem_orbit_smul (g h : α) (a : β) : g • a ∈ orbit α (h • a) :=
⟨g * h⁻¹, by simp [mul_smul]⟩

variables (α) (β)
/-- The relation "in the same orbit". -/
def orbit_rel : setoid β :=
{ r := λ a b, a ∈ orbit α b,
  iseqv := ⟨mem_orbit_self, λ a b, by simp [orbit_eq_iff.symm, eq_comm],
    λ a b, by simp [orbit_eq_iff.symm, eq_comm] {contextual := tt}⟩ }

variables {β}

open quotient_group

/-- Orbit-stabilizer theorem. -/
noncomputable def orbit_equiv_quotient_stabilizer (b : β) :
  orbit α b ≃ quotient (stabilizer α b) :=
equiv.symm (equiv.of_bijective
  (λ x : quotient (stabilizer α b), quotient.lift_on' x
    (λ x, (⟨x • b, mem_orbit _ _⟩ : orbit α b))
    (λ g h (H : _ = _), subtype.eq $ (mul_action.bijective (g⁻¹)).1
      $ show g⁻¹ • (g • b) = g⁻¹ • (h • b),
      by rw [← mul_action.mul_smul, ← mul_action.mul_smul,
        H, inv_mul_self, mul_action.one_smul]))
⟨λ g h, quotient.induction_on₂' g h (λ g h H, quotient.sound' $
  have H : g • b = h • b := subtype.mk.inj H,
  show (g⁻¹ * h) • b = b,
  by rw [mul_action.mul_smul, ← H, ← mul_action.mul_smul, inv_mul_self, mul_action.one_smul]),
  λ ⟨b, ⟨g, hgb⟩⟩, ⟨g, subtype.eq hgb⟩⟩)

@[simp] theorem orbit_equiv_quotient_stabilizer_symm_apply (b : β) (a : α) :
  ((orbit_equiv_quotient_stabilizer α b).symm a : β) = a • b :=
rfl

end

open quotient_group mul_action is_subgroup

/-- Action on left cosets. -/
def mul_left_cosets (H : set α) [is_subgroup H]
  (x : α) (y : quotient H) : quotient H :=
quotient.lift_on' y (λ y, quotient_group.mk ((x : α) * y))
  (λ a b (hab : _ ∈ H), quotient_group.eq.2
    (by rwa [mul_inv_rev, ← mul_assoc, mul_assoc (a⁻¹), inv_mul_self, mul_one]))

instance (H : set α) [is_subgroup H] : mul_action α (quotient H) :=
{ smul := mul_left_cosets H,
  one_smul := λ a, quotient.induction_on' a (λ a, quotient_group.eq.2
    (by simp [is_submonoid.one_mem])),
  mul_smul := λ x y a, quotient.induction_on' a (λ a, quotient_group.eq.2
    (by simp [mul_inv_rev, is_submonoid.one_mem, mul_assoc])) }

instance mul_left_cosets_comp_subtype_val (H I : set α) [is_subgroup H] [is_subgroup I] :
  mul_action I (quotient H) :=
mul_action.comp_hom (quotient H) (subtype.val : I → α)

end mul_action

section prio
set_option default_priority 100 -- see Note [default priority]
/-- Typeclass for multiplicative actions on additive structures. This generalizes group modules. -/
class distrib_mul_action (α : Type u) (β : Type v) [monoid α] [add_monoid β] extends mul_action α β :=
(smul_add : ∀(r : α) (x y : β), r • (x + y) = r • x + r • y)
(smul_zero : ∀(r : α), r • (0 : β) = 0)
end prio

section
variables [monoid α] [add_monoid β] [distrib_mul_action α β]

theorem smul_add (a : α) (b₁ b₂ : β) : a • (b₁ + b₂) = a • b₁ + a • b₂ :=
distrib_mul_action.smul_add _ _ _

@[simp] theorem smul_zero (a : α) : a • (0 : β) = 0 :=
distrib_mul_action.smul_zero _

/-- Pullback a distributive multiplicative action along an injective additive monoid
homomorphism. -/
protected def function.injective.distrib_mul_action [add_monoid γ] [has_scalar α γ] (f : γ →+ β)
  (hf : injective f) (smul : ∀ (c : α) x, f (c • x) = c • f x) :
  distrib_mul_action α γ :=
{ smul := (•),
  smul_add := λ c x y, hf $ by simp only [smul, f.map_add, smul_add],
  smul_zero := λ c, hf $ by simp only [smul, f.map_zero, smul_zero],
  .. hf.mul_action f smul }

/-- Pushforward a distributive multiplicative action along a surjective additive monoid
homomorphism.-/
protected def function.surjective.distrib_mul_action [add_monoid γ] [has_scalar α γ] (f : β →+ γ)
  (hf : surjective f) (smul : ∀ (c : α) x, f (c • x) = c • f x) :
  distrib_mul_action α γ :=
{ smul := (•),
  smul_add := λ c x y, by { rcases hf x with ⟨x, rfl⟩, rcases hf y with ⟨y, rfl⟩,
    simp only [smul_add, ← smul, ← f.map_add] },
  smul_zero := λ c, by simp only [← f.map_zero, ← smul, smul_zero],
  .. hf.mul_action f smul }

theorem units.smul_eq_zero (u : units α) {x : β} : (u : α) • x = 0 ↔ x = 0 :=
⟨λ h, by rw [← u.inv_smul_smul x, h, smul_zero], λ h, h.symm ▸ smul_zero _⟩

theorem units.smul_ne_zero (u : units α) {x : β} : (u : α) • x ≠ 0 ↔ x ≠ 0 :=
not_congr u.smul_eq_zero

@[simp] theorem is_unit.smul_eq_zero {u : α} (hu : is_unit u) {x : β} :
  u • x = 0 ↔ x = 0 :=
exists.elim hu $ λ u hu, hu ▸ u.smul_eq_zero

variable (β)

/-- Scalar multiplication by `r` as an `add_monoid_hom`. -/
def const_smul_hom (r : α) : β →+ β :=
{ to_fun := (•) r,
  map_zero' := smul_zero r,
  map_add' := smul_add r }

variable {β}

@[simp] lemma const_smul_hom_apply (r : α) (x : β) :
  const_smul_hom β r x = r • x := rfl

lemma list.smul_sum {r : α} {l : list β} :
  r • l.sum = (l.map ((•) r)).sum :=
(const_smul_hom β r).map_list_sum l

end

section
variables [monoid α] [add_comm_monoid β] [distrib_mul_action α β]

lemma multiset.smul_sum {r : α} {s : multiset β} :
  r • s.sum = (s.map ((•) r)).sum :=
(const_smul_hom β r).map_multiset_sum s

lemma finset.smul_sum {r : α} {f : γ → β} {s : finset γ} :
  r • ∑ x in s, f x = ∑ x in s, r • f x :=
(const_smul_hom β r).map_sum f s

end

/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import data.set.finite group_theory.coset

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

/-- Typeclass for types with a scalar multiplication operation, denoted `•` (`\bu`) -/
class has_scalar (α : Type u) (γ : Type v) := (smul : α → γ → γ)

infixr ` • `:73 := has_scalar.smul

/-- Typeclass for multiplictive actions by monoids. This generalizes group actions. -/
class mul_action (α : Type u) (β : Type v) [monoid α] extends has_scalar α β :=
(one_smul : ∀ b : β, (1 : α) • b = b)
(mul_smul : ∀ (x y : α) (b : β), (x * y) • b = x • y • b)

section
variables [monoid α] [mul_action α β]

theorem mul_smul (a₁ a₂ : α) (b : β) : (a₁ * a₂) • b = a₁ • a₂ • b := mul_action.mul_smul _ _ _

variable (α)
@[simp] theorem one_smul (b : β) : (1 : α) • b = b := mul_action.one_smul α _

end

namespace mul_action

variables (α) [monoid α] [mul_action α β]

def orbit (b : β) := set.range (λ x : α, x • b)

variable {α}

@[simp] lemma mem_orbit_iff {b₁ b₂ : β} : b₂ ∈ orbit α b₁ ↔ ∃ x : α, x • b₁ = b₂ :=
iff.rfl

@[simp] lemma mem_orbit (b : β) (x : α) : x • b ∈ orbit α b :=
⟨x, rfl⟩

@[simp] lemma mem_orbit_self (b : β) : b ∈ orbit α b :=
⟨1, by simp [mul_action.one_smul]⟩

instance orbit_fintype (b : β) [fintype α] [decidable_eq β] :
  fintype (orbit α b) := set.fintype_range _

variable (α)

def stabilizer (b : β) : set α :=
{x : α | x • b = b}

variable {α}

@[simp] lemma mem_stabilizer_iff {b : β} {x : α} :
  x ∈ stabilizer α b ↔ x • b = b := iff.rfl

variables (α) (β)

def fixed_points : set β := {b : β | ∀ x, x ∈ stabilizer α b}

variables {α} (β)

@[simp] lemma mem_fixed_points {b : β} :
  b ∈ fixed_points α β ↔ ∀ x : α, x • b = b := iff.rfl

lemma mem_fixed_points' {b : β} : b ∈ fixed_points α β ↔
  (∀ b', b' ∈ orbit α b → b' = b) :=
⟨λ h b h₁, let ⟨x, hx⟩ := mem_orbit_iff.1 h₁ in hx ▸ h x,
λ h b, mem_stabilizer_iff.2 (h _ (mem_orbit _ _))⟩

def comp_hom [monoid γ] (g : γ → α) [is_monoid_hom g] :
  mul_action γ β :=
{ smul := λ x b, (g x) • b,
  one_smul := by simp [is_monoid_hom.map_one g, mul_action.one_smul],
  mul_smul := by simp [is_monoid_hom.map_mul g, mul_action.mul_smul] }

end mul_action

namespace mul_action
variables [group α] [mul_action α β]

section
open mul_action quotient_group

variables (α) (β)

def to_perm (g : α) : equiv.perm β :=
{ to_fun := (•) g,
  inv_fun := (•) g⁻¹,
  left_inv := λ a, by rw [← mul_action.mul_smul, inv_mul_self, mul_action.one_smul],
  right_inv := λ a, by rw [← mul_action.mul_smul, mul_inv_self, mul_action.one_smul] }

variables {α} {β}

instance : is_group_hom (to_perm α β) :=
{ map_mul := λ x y, equiv.ext _ _ (λ a, mul_action.mul_smul x y a) }

lemma bijective (g : α) : function.bijective (λ b : β, g • b) :=
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
{ one_mem := mul_action.one_smul _ _,
  mul_mem := λ x y (hx : x • b = b) (hy : y • b = b),
    show (x * y) • b = b, by rw mul_action.mul_smul; simp *,
  inv_mem := λ x (hx : x • b = b), show x⁻¹ • b = b,
    by rw [← hx, ← mul_action.mul_smul, inv_mul_self, mul_action.one_smul, hx] }


variables (α) (β)

def orbit_rel : setoid β :=
{ r := λ a b, a ∈ orbit α b,
  iseqv := ⟨mem_orbit_self, λ a b, by simp [orbit_eq_iff.symm, eq_comm],
    λ a b, by simp [orbit_eq_iff.symm, eq_comm] {contextual := tt}⟩ }

variables {β}

open quotient_group

/-- Two elements `g h` of a group send `b∈β` to the same point iff they belong
    to the same left class w.r.t the stabilizer of `b`. -/
lemma stabilizer_coset_iff_image (b : β) (g h : α) :
  @setoid.r _ (left_rel (stabilizer α b)) g h ↔ g • b = h • b :=
calc _ = b ↔ g • (g⁻¹ * h) • b = g • b : (mul_action.bijective g).1.eq_iff.symm
       ... ↔             h • b = g • b : by rw [← mul_action.mul_smul, mul_inv_cancel_left]
       ... ↔             g • b = h • b : ⟨eq.symm, eq.symm⟩

/-- Given an left coset w.r.t. the stabilizer of `b`, compute the image of `b`
    under elements of this coset. -/
def orbit_of_quotient_stabilizer (b : β) (x : quotient (stabilizer α b)) : orbit α b :=
quotient.lift_on' x
  (λ x, (⟨x • b, mem_orbit _ _⟩ : orbit α b))
  (λ g h H, subtype.eq $ (stabilizer_coset_iff_image α b g h).1 H)

/-- `orbit_of_quotient_stabilizer α b` sends `⟦x⟧` to `x • b`-/
def orbit_of_quotient_stabilizer_spec (b : β) (x : α) :
  (orbit_of_quotient_stabilizer α b (quotient.mk' x)).val = x • b :=
rfl

/-- The map sending left cosets w.r.t. the stabilizer of `b`
    to the orbit of `b` is bijective. -/
lemma orbit_of_quotient_stabilizer_bijective (b : β) :
  function.bijective (orbit_of_quotient_stabilizer α b) :=
⟨λ g h, quotient.induction_on₂' g h
  (λ g h H, quotient.sound'
            $ (stabilizer_coset_iff_image α b g h).2
            $ subtype.ext.1 H),
  λ ⟨b, ⟨g, hgb⟩⟩, ⟨g, subtype.eq hgb⟩⟩

/-- Natural equivalence between orbit of a point, and the set of left cosets
    w.r.t. the stabilizer of this point. For the computable part of this equivalence,
    see `orbit_of_quotient_stabilizer`. -/
noncomputable def orbit_equiv_quotient_stabilizer (b : β) :
  orbit α b ≃ quotient (stabilizer α b) :=
equiv.symm (equiv.of_bijective $ orbit_of_quotient_stabilizer_bijective α b)

end

open quotient_group mul_action is_subgroup

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

/-- Typeclass for multiplicative actions on additive structures. This generalizes group modules. -/
class distrib_mul_action (α : Type u) (β : Type v) [monoid α] [add_monoid β] extends mul_action α β :=
(smul_add : ∀(r : α) (x y : β), r • (x + y) = r • x + r • y)
(smul_zero {} : ∀(r : α), r • (0 : β) = 0)

section
variables [monoid α] [add_monoid β] [distrib_mul_action α β]

theorem smul_add (a : α) (b₁ b₂ : β) : a • (b₁ + b₂) = a • b₁ + a • b₂ :=
distrib_mul_action.smul_add _ _ _

@[simp] theorem smul_zero (a : α) : a • (0 : β) = 0 :=
distrib_mul_action.smul_zero _

end

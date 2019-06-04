/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
import data.set.finite data.set.lattice data.function.fixed_points group_theory.coset

universes u v w
variables (α : Type u) (β : Type v) {γ : Type w}

/-- Typeclass for types with a scalar multiplication operation, denoted `•` (`\bu`) -/
class has_scalar := (smul : α → β → β)

infixr ` • `:73 := has_scalar.smul

/-- Typeclass for multiplictive actions by monoids. This generalizes group actions. -/
class mul_action [monoid α] extends has_scalar α β :=
(one_smul : ∀ b : β, (1 : α) • b = b)
(mul_smul : ∀ (x y : α) (b : β), (x * y) • b = x • y • b)

variables {α β}

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

@[refl] lemma mem_orbit_self (b : β) : b ∈ orbit α b :=
⟨1, one_smul α b⟩

@[trans] lemma mem_orbit_trans (b₁ b₂ b₃ : β) : b₁ ∈ orbit α b₂ → b₂ ∈ orbit α b₃ → b₁ ∈ orbit α b₃ :=
assume ⟨x₁, (h₁ : x₁ • b₂ = b₁)⟩ ⟨x₂, (h₂ : x₂ • b₃ = b₂)⟩,
h₁ ▸ h₂ ▸ mul_smul x₁ x₂ b₃ ▸ mem_orbit _ _

instance orbit_fintype (b : β) [fintype α] [decidable_eq β] :
  fintype (orbit α b) := set.fintype_range _

variable (α)

def stabilizer (b : β) : set α :=
{x : α | x • b = b}

variable {α}

@[simp] lemma mem_stabilizer_iff {b : β} {x : α} :
  x ∈ stabilizer α b ↔ x • b = b := iff.rfl

lemma mem_stabilizer_iff_mem_fixed_points {b : β} {x : α} :
  x ∈ stabilizer α b ↔ b ∈ function.fixed_points ((•) x : β → β) := iff.rfl

variables (α) (β)

def fixed_points : set β := {b : β | ∀ x, x ∈ stabilizer α b}

variables {α} (β)

@[simp] lemma mem_fixed_points {b : β} :
  b ∈ fixed_points α β ↔ ∀ x : α, x • b = b := iff.rfl

lemma fixed_points_eq_Inter :
  fixed_points α β = ⋂ x : α, function.fixed_points ((•) x : β → β) :=
set.ext $
assume b,
iff.symm $
@set.mem_Inter β α b (λ x, function.fixed_points ((•) x : β → β))

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

@[simp] lemma smul_left_inv {x : α} {y : β} : x⁻¹ • x • y = y :=
by rw [← mul_smul, mul_left_inv, one_smul]

@[simp] lemma smul_right_inv {x : α} {y : β} : x • x⁻¹ • y = y :=
by rw [← mul_smul, mul_right_inv, one_smul]

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

@[symm] lemma mem_orbit_symm ⦃b₁ b₂ : β⦄ : b₁ ∈ orbit α b₂ → b₂ ∈ orbit α b₁ :=
λ ⟨x, (h : x • b₂ = b₁)⟩, ⟨x⁻¹, show x⁻¹ • b₁ = b₂, from h ▸ smul_left_inv⟩

variables (α)

instance stabilizer_is_subgroup (b : β) : is_subgroup (stabilizer α b) :=
{ one_mem := mul_action.one_smul _ _,
  mul_mem := λ x y (hx : x • b = b) (hy : y • b = b),
    show (x * y) • b = b, by rw mul_action.mul_smul; simp *,
  inv_mem := λ x (hx : x • b = b), show x⁻¹ • b = b,
    by rw [← hx, ← mul_action.mul_smul, inv_mul_self, mul_action.one_smul, hx] }


variables (α) (β)

def orbit_rel : setoid β :=
{ r := λ b₁ b₂, b₁ ∈ orbit α b₂,
  iseqv := ⟨mem_orbit_self, mem_orbit_symm, mem_orbit_trans⟩ }

instance orbit_rel_decidable [fintype α] [decidable_eq β] :
  decidable_rel (@setoid.r _ (orbit_rel α β)) :=
show decidable_rel (λ b₁ b₂, b₁ ∈ orbit α b₂),
from λ b₁ b₂, set.decidable_mem_of_fintype (orbit α b₂) b₁

def orbits : Type v := quotient $ orbit_rel α β

instance orbits_fintype [fintype α] [fintype β] [decidable_eq β] :
  fintype $ orbits α β :=
quotient.fintype _

variables {β}

open quotient_group

/-- Two elements `g h` of a group send `b∈β` to the same point iff they belong
    to the same left class w.r.t the stabilizer of `b`. -/
lemma stabilizer_coset_iff_image (b : β) (g h : α) :
  @setoid.r _ (left_rel (stabilizer α b)) g h ↔ g • b = h • b :=
calc _ = b ↔ g • (g⁻¹ * h) • b = g • b : (mul_action.bijective g).1.eq_iff.symm
       ... ↔             h • b = g • b : by rw [← mul_action.mul_smul, mul_inv_cancel_left]
       ... ↔             g • b = h • b : ⟨eq.symm, eq.symm⟩

/-- Given a left coset w.r.t. the stabilizer of `b`, compute the image of `b`
    under elements of this coset. -/
def quotient_stabilizer_smul (b : β) (x : quotient (stabilizer α b)) : orbit α b :=
quotient.lift_on' x
  (λ x, (⟨x • b, mem_orbit _ _⟩ : orbit α b))
  (λ g h H, subtype.eq $ (stabilizer_coset_iff_image α b g h).1 H)

/-- `orbit_of_quotient_stabilizer α b` sends `⟦x⟧` to `x • b`-/
def orbit_of_quotient_stabilizer_spec (b : β) (x : α) :
  (quotient_stabilizer_smul α b (quotient.mk' x)).val = x • b :=
rfl

/-- The map sending left cosets w.r.t. the stabilizer of `b`
    to the orbit of `b` is bijective. -/
lemma orbit_of_quotient_stabilizer_bijective (b : β) :
  function.bijective (quotient_stabilizer_smul α b) :=
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

noncomputable def orbit_prod_stabilizer_equiv_group (b : β) :
  (orbit α b × stabilizer α b) ≃ α :=
equiv.symm $
(mul_action.stabilizer_is_subgroup α b).group_equiv_quotient_times_subgroup.trans $
equiv.prod_congr
  (orbit_equiv_quotient_stabilizer α b).symm
  (equiv.refl _)

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

namespace mul_action

section units
variables [monoid α] [mul_action α β]

instance units_mul_action: mul_action (units α) β :=
{ smul := λ a b, a.val • b,
  one_smul := λ b, one_smul α b,
  mul_smul := λ a₁ a₂ b, mul_smul a₁.val a₂.val b }

variables {α β}

lemma conj_smul (a₁ : units α) (a₂ : α) (b : β) : (a₁.conj a₂) • b = (to_perm (units α) β a₁).conj((•) a₂) b :=
show (a₁.val * a₂ * a₁.inv) • b = a₁.val • a₂ • a₁.inv • b,
by simp only [mul_smul]

variables (β)

lemma conj_smul_funeq (a₁ : units α) (a₂ : α) :
  ((•) (a₁.conj a₂) : β → β) = (to_perm (units α) β a₁).conj((•) a₂) :=
funext $ conj_smul a₁ a₂

variables {β}

lemma mem_stabilizer_smul_iff (u : units α) (x : α) (b : β) :
  x ∈ stabilizer α b ↔ (u.conj x) ∈ stabilizer α (u.val • b) :=
begin
simp only [mem_stabilizer_iff_mem_fixed_points], -- rw twice
rw conj_smul_funeq,
apply equiv.mem_fixed_points_of_conj
end

lemma mem_stabilizer_self_iff_smul (u : units α) (x : α) (b : β) :
  x ∈ stabilizer α (u.val • b) ↔ u⁻¹.conj x ∈  stabilizer α b :=
(mem_stabilizer_smul_iff u⁻¹ x (u.val • b)).trans
  (eq.to_iff $ by congr; exact @smul_left_inv _ _ _ _ u b)

def stabilizer_equiv_smul_units (u : units α) (b : β) :
  stabilizer α b ≃ stabilizer α (u.val • b) :=
{ to_fun := λ x, ⟨u.conj x, (mem_stabilizer_smul_iff u x.val b).1 x.2⟩,
  inv_fun := λ x, ⟨(u⁻¹).conj x, (mem_stabilizer_self_iff_smul u x.val b).1 x.2⟩,
  left_inv := λ ⟨x, h⟩, by dsimp; congr; apply units.conj_inv_cancel_left,
  right_inv := λ ⟨x, h⟩, by dsimp; congr; apply units.conj_inv_cancel_right }

end units

variables [group α] [mul_action α β]

def stabilizer_equiv_smul (a : α) (b : β) : stabilizer α b ≃ stabilizer α (a • b) :=
stabilizer_equiv_smul_units (to_units a) b

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

/-
Copyright (c) 2021 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen, Yaël Dillies
-/
import algebra.punit_instances
import tactic.abel
import tactic.ring
import order.hom.lattice

/-!
# Boolean rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A Boolean ring is a ring where multiplication is idempotent. They are equivalent to Boolean
algebras.

## Main declarations

* `boolean_ring`: a typeclass for rings where multiplication is idempotent.
* `boolean_ring.to_boolean_algebra`: Turn a Boolean ring into a Boolean algebra.
* `boolean_algebra.to_boolean_ring`: Turn a Boolean algebra into a Boolean ring.
* `as_boolalg`: Type-synonym for the Boolean algebra associated to a Boolean ring.
* `as_boolring`: Type-synonym for the Boolean ring associated to a Boolean algebra.

## Implementation notes

We provide two ways of turning a Boolean algebra/ring into a Boolean ring/algebra:
* Instances on the same type accessible in locales `boolean_algebra_of_boolean_ring` and
  `boolean_ring_of_boolean_algebra`.
* Type-synonyms `as_boolalg` and `as_boolring`.

At this point in time, it is not clear the first way is useful, but we keep it for educational
purposes and because it is easier than dealing with
`of_boolalg`/`to_boolalg`/`of_boolring`/`to_boolring` explicitly.

## Tags

boolean ring, boolean algebra
-/

variables {α β γ : Type*}

/-- A Boolean ring is a ring where multiplication is idempotent. -/
class boolean_ring α extends ring α :=
(mul_self : ∀ a : α, a * a = a)

section boolean_ring
variables [boolean_ring α] (a b : α)

instance : is_idempotent α (*) := ⟨boolean_ring.mul_self⟩

@[simp] lemma mul_self : a * a = a := boolean_ring.mul_self _

@[simp] lemma add_self : a + a = 0 :=
have a + a = a + a + (a + a) :=
  calc a + a = (a+a) * (a+a)           : by rw mul_self
         ... = a*a + a*a + (a*a + a*a) : by rw [add_mul, mul_add]
         ... = a + a + (a + a)         : by rw mul_self,
by rwa self_eq_add_left at this

@[simp] lemma neg_eq : -a = a :=
calc -a = -a + 0      : by rw add_zero
    ... = -a + -a + a : by rw [←neg_add_self, add_assoc]
    ... = a           : by rw [add_self, zero_add]

lemma add_eq_zero' : a + b = 0 ↔ a = b :=
calc a + b = 0 ↔ a = -b : add_eq_zero_iff_eq_neg
           ... ↔ a = b  : by rw neg_eq

@[simp] lemma mul_add_mul : a*b + b*a = 0 :=
have a + b = a + b + (a*b + b*a) :=
  calc a + b = (a + b) * (a + b)       : by rw mul_self
         ... = a*a + a*b + (b*a + b*b) : by rw [add_mul, mul_add, mul_add]
         ... = a + a*b + (b*a + b)     : by simp only [mul_self]
         ... = a + b + (a*b + b*a)     : by abel,
by rwa self_eq_add_right at this

@[simp] lemma sub_eq_add : a - b = a + b :=
by rw [sub_eq_add_neg, add_right_inj, neg_eq]

@[simp] lemma mul_one_add_self : a * (1 + a) = 0 := by rw [mul_add, mul_one, mul_self, add_self]

@[priority 100] -- Note [lower instance priority]
instance boolean_ring.to_comm_ring : comm_ring α :=
{ mul_comm := λ a b, by rw [←add_eq_zero', mul_add_mul],
  .. (infer_instance : boolean_ring α) }

end boolean_ring

instance : boolean_ring punit := ⟨λ _, subsingleton.elim _ _⟩

/-! ### Turning a Boolean ring into a Boolean algebra -/

section ring_to_algebra

/-- Type synonym to view a Boolean ring as a Boolean algebra. -/
def as_boolalg (α : Type*) := α

/-- The "identity" equivalence between `as_boolalg α` and `α`. -/
def to_boolalg : α ≃ as_boolalg α := equiv.refl _

/-- The "identity" equivalence between `α` and `as_boolalg α`. -/
def of_boolalg : as_boolalg α ≃ α := equiv.refl _

@[simp] lemma to_boolalg_symm_eq : (@to_boolalg α).symm = of_boolalg := rfl
@[simp] lemma of_boolalg_symm_eq : (@of_boolalg α).symm = to_boolalg := rfl
@[simp] lemma to_boolalg_of_boolalg (a : as_boolalg α) : to_boolalg (of_boolalg a) = a := rfl
@[simp] lemma of_boolalg_to_boolalg (a : α) : of_boolalg (to_boolalg a) = a := rfl
@[simp] lemma to_boolalg_inj {a b : α} : to_boolalg a = to_boolalg b ↔ a = b := iff.rfl
@[simp] lemma of_boolalg_inj {a b : as_boolalg α} : of_boolalg a = of_boolalg b ↔ a = b := iff.rfl

instance [inhabited α] : inhabited (as_boolalg α) := ‹inhabited α›

variables [boolean_ring α] [boolean_ring β] [boolean_ring γ]

namespace boolean_ring

/-- The join operation in a Boolean ring is `x + y + x * y`. -/
def has_sup : has_sup α := ⟨λ x y, x + y + x * y⟩
/-- The meet operation in a Boolean ring is `x * y`. -/
def has_inf : has_inf α := ⟨(*)⟩

-- Note [lower instance priority]
localized "attribute [instance, priority 100] boolean_ring.has_sup" in
  boolean_algebra_of_boolean_ring
localized "attribute [instance, priority 100] boolean_ring.has_inf" in
  boolean_algebra_of_boolean_ring

lemma sup_comm (a b : α) : a ⊔ b = b ⊔ a := by { dsimp only [(⊔)], ring }
lemma inf_comm (a b : α) : a ⊓ b = b ⊓ a := by { dsimp only [(⊓)], ring }

lemma sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c) := by { dsimp only [(⊔)], ring }
lemma inf_assoc (a b c : α) : a ⊓ b ⊓ c = a ⊓ (b ⊓ c) := by { dsimp only [(⊓)], ring }

lemma sup_inf_self (a b : α) : a ⊔ a ⊓ b = a :=
by { dsimp only [(⊔), (⊓)], assoc_rw [mul_self, add_self, add_zero] }
lemma inf_sup_self (a b : α) : a ⊓ (a ⊔ b) = a :=
begin
  dsimp only [(⊔), (⊓)],
  rw [mul_add, mul_add, mul_self, ←mul_assoc, mul_self, add_assoc, add_self, add_zero]
end

lemma le_sup_inf_aux (a b c : α) : (a + b + a * b) * (a + c + a * c) = a + b * c + a * (b * c) :=
calc (a + b + a * b) * (a + c + a * c) =
        a * a + b * c + a * (b * c) +
          (a * b + (a * a) * b) +
          (a * c + (a * a) * c) +
          (a * b * c + (a * a) * b * c) : by ring
... = a + b * c + a * (b * c)           : by simp only [mul_self, add_self, add_zero]

lemma le_sup_inf (a b c : α) : (a ⊔ b) ⊓ (a ⊔ c) ⊔ (a ⊔ b ⊓ c) = a ⊔ b ⊓ c :=
by { dsimp only [(⊔), (⊓)], rw [le_sup_inf_aux, add_self, mul_self, zero_add] }

/--
The Boolean algebra structure on a Boolean ring.

The data is defined so that:
* `a ⊔ b` unfolds to `a + b + a * b`
* `a ⊓ b` unfolds to `a * b`
* `a ≤ b` unfolds to `a + b + a * b = b`
* `⊥` unfolds to `0`
* `⊤` unfolds to `1`
* `aᶜ` unfolds to `1 + a`
* `a \ b` unfolds to `a * (1 + b)`
-/
def to_boolean_algebra : boolean_algebra α :=
{ le_sup_inf := le_sup_inf,
  top := 1,
  le_top := λ a, show a + 1 + a * 1 = 1, by assoc_rw [mul_one, add_comm, add_self, add_zero],
  bot := 0,
  bot_le := λ a, show 0 + a + 0 * a = a, by rw [zero_mul, zero_add, add_zero],
  compl := λ a, 1 + a,
  inf_compl_le_bot := λ a,
    show a*(1+a) + 0 + a*(1+a)*0 = 0,
    by norm_num [mul_add, mul_self, add_self],
  top_le_sup_compl := λ a,
    begin
      change 1 + (a + (1+a) + a*(1+a)) + 1*(a + (1+a) + a*(1+a)) = a + (1+a) + a*(1+a),
      norm_num [mul_add, mul_self],
      rw [←add_assoc, add_self],
    end,
  .. lattice.mk' sup_comm sup_assoc inf_comm inf_assoc sup_inf_self inf_sup_self }

localized "attribute [instance, priority 100] boolean_ring.to_boolean_algebra" in
  boolean_algebra_of_boolean_ring

end boolean_ring

instance : boolean_algebra (as_boolalg α) := @boolean_ring.to_boolean_algebra α _

@[simp] lemma of_boolalg_top : of_boolalg (⊤ : as_boolalg α) = 1 := rfl
@[simp] lemma of_boolalg_bot : of_boolalg (⊥ : as_boolalg α) = 0 := rfl

@[simp] lemma of_boolalg_sup (a b : as_boolalg α) :
  of_boolalg (a ⊔ b) = of_boolalg a + of_boolalg b + of_boolalg a * of_boolalg b := rfl

@[simp] lemma of_boolalg_inf (a b : as_boolalg α) :
  of_boolalg (a ⊓ b) = of_boolalg a * of_boolalg b := rfl

@[simp] lemma of_boolalg_compl (a : as_boolalg α) : of_boolalg aᶜ = 1 + of_boolalg a := rfl

@[simp] lemma of_boolalg_sdiff (a b : as_boolalg α) :
  of_boolalg (a \ b) = of_boolalg a * (1 + of_boolalg b) := rfl

private lemma of_boolalg_symm_diff_aux (a b : α) : (a + b + a * b) * (1 + a * b) = a + b :=
calc (a + b + a * b) * (1 + a * b)
      = a + b + (a * b + (a * b) * (a * b)) + (a * (b * b) + (a * a) * b) : by ring
  ... = a + b : by simp only [mul_self, add_self, add_zero]

@[simp] lemma of_boolalg_symm_diff (a b : as_boolalg α) :
  of_boolalg (a ∆ b) = of_boolalg a + of_boolalg b :=
by { rw symm_diff_eq_sup_sdiff_inf, exact of_boolalg_symm_diff_aux _ _ }

@[simp] lemma of_boolalg_mul_of_boolalg_eq_left_iff {a b : as_boolalg α} :
  of_boolalg a * of_boolalg b = of_boolalg a ↔ a ≤ b :=
@inf_eq_left (as_boolalg α) _ _ _

@[simp] lemma to_boolalg_zero : to_boolalg (0 : α) = ⊥ := rfl
@[simp] lemma to_boolalg_one : to_boolalg (1 : α) = ⊤ := rfl

@[simp] lemma to_boolalg_mul (a b : α) :
  to_boolalg (a * b) = to_boolalg a ⊓ to_boolalg b := rfl

-- `to_boolalg_add` simplifies the LHS but this lemma is eligible to `dsimp`
@[simp, nolint simp_nf] lemma to_boolalg_add_add_mul (a b : α) :
  to_boolalg (a + b + a * b) = to_boolalg a ⊔ to_boolalg b := rfl

@[simp] lemma to_boolalg_add (a b : α) : to_boolalg (a + b) = to_boolalg a ∆ to_boolalg b :=
(of_boolalg_symm_diff _ _).symm

/-- Turn a ring homomorphism from Boolean rings `α` to `β` into a bounded lattice homomorphism
from `α` to `β` considered as Boolean algebras. -/
@[simps] protected def ring_hom.as_boolalg (f : α →+* β) :
  bounded_lattice_hom (as_boolalg α) (as_boolalg β) :=
{ to_fun := to_boolalg ∘ f ∘ of_boolalg,
  map_sup' := λ a b, begin
    dsimp,
    simp_rw [map_add f, map_mul f],
    refl,
  end,
  map_inf' := f.map_mul',
  map_top' := f.map_one',
  map_bot' := f.map_zero' }

@[simp] lemma ring_hom.as_boolalg_id : (ring_hom.id α).as_boolalg = bounded_lattice_hom.id _ := rfl

@[simp] lemma ring_hom.as_boolalg_comp (g : β →+* γ) (f : α →+* β) :
  (g.comp f).as_boolalg = g.as_boolalg.comp f.as_boolalg := rfl

end ring_to_algebra

/-! ### Turning a Boolean algebra into a Boolean ring -/

section algebra_to_ring

/-- Type synonym to view a Boolean ring as a Boolean algebra. -/
def as_boolring (α : Type*) := α

/-- The "identity" equivalence between `as_boolring α` and `α`. -/
def to_boolring : α ≃ as_boolring α := equiv.refl _

/-- The "identity" equivalence between `α` and `as_boolring α`. -/
def of_boolring : as_boolring α ≃ α := equiv.refl _

@[simp] lemma to_boolring_symm_eq : (@to_boolring α).symm = of_boolring := rfl
@[simp] lemma of_boolring_symm_eq : (@of_boolring α).symm = to_boolring := rfl
@[simp] lemma to_boolring_of_boolring (a : as_boolring α) : to_boolring (of_boolring a) = a := rfl
@[simp] lemma of_boolring_to_boolring (a : α) : of_boolring (to_boolring a) = a := rfl
@[simp] lemma to_boolring_inj {a b : α} : to_boolring a = to_boolring b ↔ a = b := iff.rfl
@[simp] lemma of_boolring_inj {a b : as_boolring α} : of_boolring a = of_boolring b ↔ a = b :=
iff.rfl

instance [inhabited α] : inhabited (as_boolring α) := ‹inhabited α›

/-- Every generalized Boolean algebra has the structure of a non unital commutative ring with the
following data:

* `a + b` unfolds to `a ∆ b` (symmetric difference)
* `a * b` unfolds to `a ⊓ b`
* `-a` unfolds to `a`
* `0` unfolds to `⊥`
-/
@[reducible] -- See note [reducible non-instances]
def generalized_boolean_algebra.to_non_unital_comm_ring [generalized_boolean_algebra α] :
  non_unital_comm_ring α :=
{ add := (∆),
  add_assoc := symm_diff_assoc,
  zero := ⊥,
  zero_add := bot_symm_diff,
  add_zero := symm_diff_bot,
  zero_mul := λ _, bot_inf_eq,
  mul_zero := λ _, inf_bot_eq,
  neg := id,
  add_left_neg := symm_diff_self,
  add_comm := symm_diff_comm,
  mul := (⊓),
  mul_assoc := λ _ _ _, inf_assoc,
  mul_comm := λ _ _, inf_comm,
  left_distrib := inf_symm_diff_distrib_left,
  right_distrib := inf_symm_diff_distrib_right }

instance [generalized_boolean_algebra α] : non_unital_comm_ring (as_boolring α) :=
@generalized_boolean_algebra.to_non_unital_comm_ring α _

variables [boolean_algebra α] [boolean_algebra β] [boolean_algebra γ]

/-- Every Boolean algebra has the structure of a Boolean ring with the following data:

* `a + b` unfolds to `a ∆ b` (symmetric difference)
* `a * b` unfolds to `a ⊓ b`
* `-a` unfolds to `a`
* `0` unfolds to `⊥`
* `1` unfolds to `⊤`
-/
@[reducible] -- See note [reducible non-instances]
def boolean_algebra.to_boolean_ring : boolean_ring α :=
{ one := ⊤,
  one_mul := λ _, top_inf_eq,
  mul_one := λ _, inf_top_eq,
  mul_self := λ b, inf_idem,
  ..generalized_boolean_algebra.to_non_unital_comm_ring }

localized "attribute [instance, priority 100] generalized_boolean_algebra.to_non_unital_comm_ring
  boolean_algebra.to_boolean_ring" in boolean_ring_of_boolean_algebra

instance : boolean_ring (as_boolring α) := @boolean_algebra.to_boolean_ring α _

@[simp] lemma of_boolring_zero : of_boolring (0 : as_boolring α) = ⊥ := rfl
@[simp] lemma of_boolring_one : of_boolring (1 : as_boolring α) = ⊤ := rfl

-- `sub_eq_add` proves this lemma but it is eligible for `dsimp`
@[simp, nolint simp_nf] lemma of_boolring_neg (a : as_boolring α) :
  of_boolring (-a) = of_boolring a := rfl

@[simp] lemma of_boolring_add (a b : as_boolring α) :
  of_boolring (a + b) = of_boolring a ∆ of_boolring b := rfl

-- `sub_eq_add` simplifies the LHS but this lemma is eligible for `dsimp`
@[simp, nolint simp_nf] lemma of_boolring_sub (a b : as_boolring α) :
  of_boolring (a - b) = of_boolring a ∆ of_boolring b := rfl

@[simp] lemma of_boolring_mul (a b : as_boolring α) :
  of_boolring (a * b) = of_boolring a ⊓ of_boolring b := rfl

@[simp] lemma of_boolring_le_of_boolring_iff {a b : as_boolring α} :
  of_boolring a ≤ of_boolring b ↔ a * b = a := inf_eq_left.symm

@[simp] lemma to_boolring_bot : to_boolring (⊥ : α) = 0 := rfl
@[simp] lemma to_boolring_top : to_boolring (⊤ : α) = 1 := rfl
@[simp] lemma to_boolring_inf (a b : α) : to_boolring (a ⊓ b) = to_boolring a * to_boolring b := rfl

@[simp] lemma to_boolring_symm_diff (a b : α) :
  to_boolring (a ∆ b) = to_boolring a + to_boolring b := rfl

/-- Turn a bounded lattice homomorphism from Boolean algebras `α` to `β` into a ring homomorphism
from `α` to `β` considered as Boolean rings. -/
@[simps] protected def bounded_lattice_hom.as_boolring (f : bounded_lattice_hom α β) :
  as_boolring α →+* as_boolring β :=
{ to_fun := to_boolring ∘ f ∘ of_boolring,
  map_zero' := f.map_bot',
  map_one' := f.map_top',
  map_add' := map_symm_diff' f,
  map_mul' := f.map_inf' }

@[simp] lemma bounded_lattice_hom.as_boolring_id :
  (bounded_lattice_hom.id α).as_boolring = ring_hom.id _ := rfl

@[simp] lemma bounded_lattice_hom.as_boolring_comp (g : bounded_lattice_hom β γ)
  (f : bounded_lattice_hom α β) :
  (g.comp f).as_boolring = g.as_boolring.comp f.as_boolring := rfl

end algebra_to_ring

/-! ### Equivalence between Boolean rings and Boolean algebras -/

/-- Order isomorphism between `α` considered as a Boolean ring considered as a Boolean algebra and
`α`. -/
@[simps] def order_iso.as_boolalg_as_boolring (α : Type*) [boolean_algebra α] :
  as_boolalg (as_boolring α) ≃o α :=
⟨of_boolalg.trans of_boolring, λ a b,
  of_boolring_le_of_boolring_iff.trans of_boolalg_mul_of_boolalg_eq_left_iff⟩

/-- Ring isomorphism between `α` considered as a Boolean algebra considered as a Boolean ring and
`α`. -/
@[simps] def ring_equiv.as_boolring_as_boolalg (α : Type*) [boolean_ring α] :
  as_boolring (as_boolalg α) ≃+* α :=
{ map_mul' := λ a b, rfl,
  map_add' := of_boolalg_symm_diff,
  ..of_boolring.trans of_boolalg }

open bool

instance : boolean_ring bool :=
{ add := bxor,
  add_assoc := bxor_assoc,
  zero := ff,
  zero_add := ff_bxor,
  add_zero := bxor_ff,
  neg := id,
  sub := bxor,
  sub_eq_add_neg := λ _ _, rfl,
  add_left_neg := bxor_self,
  add_comm := bxor_comm,
  one := tt,
  mul := band,
  mul_assoc := band_assoc,
  one_mul := tt_band,
  mul_one := band_tt,
  left_distrib := band_bxor_distrib_left,
  right_distrib := band_bxor_distrib_right,
  mul_self := band_self }

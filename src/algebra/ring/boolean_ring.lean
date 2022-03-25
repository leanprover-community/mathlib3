/-
Copyright (c) 2021 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import algebra.punit_instances
import order.hom.lattice
import order.symm_diff
import tactic.abel
import tactic.ring

/-!
# Boolean rings

A Boolean ring is a ring where multiplication is idempotent. They are equivalent to Boolean
algebras.

## Main declarations

* `boolean_ring`: a typeclass for rings where multiplication is idempotent.
* `boolean_ring.to_boolean_algebra`: every Boolean ring is a Boolean algebra; this definition and
  the `sup` and `inf` notations for `boolean_ring` are localized as instances in the
  `boolean_algebra_of_boolean_ring` locale.

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

lemma add_eq_zero : a + b = 0 ↔ a = b :=
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
{ mul_comm := λ a b, by rw [←add_eq_zero, mul_add_mul],
  .. (infer_instance : boolean_ring α) }

end boolean_ring

instance : boolean_ring punit := ⟨λ _, subsingleton.elim _ _⟩

/-! ### Turning a Boolean ring into a Boolean algebra -/

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

section ring_to_algebra
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
by { dsimp only [(⊔), (⊓)], assoc_rw [mul_add, mul_add, mul_self, mul_self, add_self, add_zero] }

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
boolean_algebra.of_core
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

@[simp] lemma to_boolalg_zero : to_boolalg (0 : α) = ⊥ := rfl
@[simp] lemma to_boolalg_one : to_boolalg (1 : α) = ⊤ := rfl

@[simp] lemma to_boolalg_mul (a b : α) :
  to_boolalg (a * b) = to_boolalg a ⊓ to_boolalg b := rfl

@[simp] lemma to_boolalg_add_add_mul (a b : α) :
  to_boolalg (a + b + a * b) = to_boolalg a ⊔ to_boolalg b := rfl

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

namespace boolean_algebra

/-- Every Boolean algebra has the structure of a Boolean ring with the following data:

* `a + b` unfolds to `a Δ b` (symmetric difference),
* `a * b` unfolds to `a ⊓ b`
* `-a` unfolds to `a`
* `0` unfolds to `⊥`
* `1` unfolds to `⊤`
-/
def to_boolean_ring (α : Type*) [boolean_algebra α] : boolean_ring α :=
{ add := (Δ),
  add_assoc := symm_diff_assoc,
  zero := ⊥,
  zero_add := λ b, by simp [(+), symm_diff_eq],
  add_zero := λ b, by simp [(+), symm_diff_eq],
  neg := λ a, a,
  add_left_neg := λ b,
    begin
      simp only [has_neg.neg, (+), add_semigroup.add, add_monoid.add, add_zero_class.add,
        symm_diff_eq, sup_bot_eq, inf_compl_eq_bot],
      refl,
    end,
  add_comm := symm_diff_comm,
  mul := (⊓),
  mul_assoc := λ a b c, by simp only [(*), inf_assoc],
  one := ⊤,
  one_mul := λ b, by simp [(*)],
  mul_one := λ b, by simp [(*)],
  left_distrib := λ a b c,
    begin
      simp only [symm_diff_eq, compl_inf, inf_sup_left, inf_assoc],
      rw [@inf_comm _ _ b aᶜ, ←@inf_assoc _ _ a aᶜ, inf_compl_eq_bot, bot_inf_eq,
        bot_sup_eq, @inf_comm _ _ c aᶜ, ←@inf_assoc _ _ a aᶜ,
        inf_compl_eq_bot, bot_inf_eq, bot_sup_eq],
    end,
  right_distrib := λ a b c,
    begin
      simp only [symm_diff_eq, compl_inf, inf_sup_right, inf_assoc, inf_sup_left],
      rw [@inf_comm _ _ c, @inf_comm _ _ c aᶜ, inf_compl_eq_bot, inf_bot_eq, inf_bot_eq,
        sup_bot_eq, sup_bot_eq],
    end,
  mul_self := λ b, inf_idem }

localized "attribute [instance, priority 100] boolean_algebra.to_boolean_ring" in
  boolean_ring_of_boolean_algebra

/-!
The following lemmas amount to a proof that applying `boolean_algebra.to_boolean_ring` and then
`boolean_ring.to_boolean_algebra` to a Boolean algebra results in the same Boolean algebra.
-/

variables {α : Type*} (BA : boolean_algebra α)

lemma to_boolean_ring.sup_eq :
  (@boolean_ring.to_boolean_algebra α (@boolean_algebra.to_boolean_ring α BA)).sup = BA.sup :=
symm_diff_symm_diff_sup _ _

lemma to_boolean_ring.le_iff :
  (@boolean_ring.to_boolean_algebra α (@boolean_algebra.to_boolean_ring α BA)).le = BA.le :=
begin
  ext a b,
  change a Δ b Δ (a ⊓ b) = b ↔ a ≤ b,
  simp [symm_diff_symm_diff_sup],
end

lemma to_boolean_ring.lt_iff :
  (@boolean_ring.to_boolean_algebra α (@boolean_algebra.to_boolean_ring α BA)).lt = BA.lt :=
begin
  ext a b,
  change a Δ b Δ (a ⊓ b) = b ∧ b Δ a Δ (b ⊓ a) ≠ a ↔ a < b,
  simp only [symm_diff_symm_diff_sup, lt_iff_le_not_le, sup_eq_right, ne.def],
  refl,
end

lemma to_boolean_ring.inf_eq :
  (@boolean_ring.to_boolean_algebra α (@to_boolean_ring α BA)).inf = BA.inf :=
rfl

lemma to_boolean_ring.top_eq :
  (@boolean_ring.to_boolean_algebra α (@to_boolean_ring α BA)).top = BA.top :=
rfl

lemma to_boolean_ring.bot_eq :
  (@boolean_ring.to_boolean_algebra α (@to_boolean_ring α BA)).bot = BA.bot :=
rfl

lemma to_boolean_ring.compl_eq :
  (@boolean_ring.to_boolean_algebra α (@to_boolean_ring α BA)).compl = BA.compl :=
top_symm_diff _

lemma to_boolean_ring.sdiff_eq :
  (@boolean_ring.to_boolean_algebra α (@to_boolean_ring α BA)).sdiff = BA.sdiff :=
begin
  ext a b,
  change a ⊓ (⊤ Δ b) = a \ b,
  rw [top_symm_diff, sdiff_eq],
end

end boolean_algebra

/-!
The following lemmas amount to a proof that applying `boolean_ring.to_boolean_algebra` and then
`boolean_algebra.to_boolean_ring` to a Boolean ring results in the same Boolean ring.
-/

namespace boolean_ring
variables {α : Type*} (BR : boolean_ring α)

lemma to_boolean_algebra.add_eq_aux [boolean_ring α] (a b : α) :
  (a * (1 + b)) + (b * (1 + a)) + (a * (1 + b)) * (b * (1 + a)) = a + b :=
calc (a * (1 + b)) + (b * (1 + a)) + (a * (1 + b)) * (b * (1 + a)) =
    a + b + (a * b + a * b) + (a * b + (a * a)*b) + (a * (b * b) + (a*a)*(b*b)) : by ring
  ... = a+b : by simp only [mul_self, add_self, add_zero]

lemma to_boolean_algebra.add_eq :
  (@boolean_algebra.to_boolean_ring α (@to_boolean_algebra α BR)).add = BR.add :=
begin
  ext a b,
  exact to_boolean_algebra.add_eq_aux _ _
end

lemma to_boolean_algebra.zero_eq :
  (@boolean_algebra.to_boolean_ring α (@to_boolean_algebra α BR)).zero = BR.zero :=
rfl

lemma to_boolean_algebra.neg_eq :
  (@boolean_algebra.to_boolean_ring α (@to_boolean_algebra α BR)).neg = BR.neg :=
funext $ λ a, (neg_eq a).symm

lemma to_boolean_algebra.sub_eq :
  (@boolean_algebra.to_boolean_ring α (@to_boolean_algebra α BR)).sub = BR.sub :=
begin
  ext a b,
  change  (a * (1 + b)) + (b * (1 + a)) + (a * (1 + b)) * (b * (1 + a)) = a - b,
  rw [to_boolean_algebra.add_eq_aux, sub_eq_add],
end

lemma to_boolean_algebra.mul_eq :
  (@boolean_algebra.to_boolean_ring α (@to_boolean_algebra α BR)).mul = BR.mul :=
rfl

lemma to_boolean_algebra.one_eq :
  (@boolean_algebra.to_boolean_ring α (@to_boolean_algebra α BR)).one = BR.one :=
rfl

/-- Boolean rings and Boolean algebras are equivalent. -/
def boolean_ring_equiv_boolean_algebra (α : Type*) : boolean_ring α ≃ boolean_algebra α :=
{ to_fun := @to_boolean_algebra α,
  inv_fun := @boolean_algebra.to_boolean_ring α,
  left_inv := λ BR,
    begin
      rcases BR with ⟨⟨⟩⟩,
      dsimp [to_boolean_algebra, boolean_algebra.to_boolean_ring],
      sorry
    end,
  right_inv := λ BA,
    begin
      rcases BA with ⟨⟩,
      dsimp [to_boolean_algebra, boolean_algebra.to_boolean_ring],
      sorry
    end, }

end boolean_ring

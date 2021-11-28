/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import data.equiv.mul_add

/-!
# Multiplicative opposite and algebraic operations on it

In this file we define `mul_opposite α = αᵐᵒᵖ` to be the multiplicative opposite of `α`. It
inherits all additive algebraic structures on `α`, and reverses the order of multipliers in
multiplicative structures, i.e., `op (x * y) = op x * op y`, where `mul_opposite.op` is the
canonical map from `α` to `αᵐᵒᵖ`.

## Notation

`αᵐᵒᵖ = mul_opposite α`
-/

universes u v
open function

/-- Multiplicative opposite of a type. This type inherits all additive structures on `α` and
reverses left and right in multiplication.-/
def mul_opposite (α : Type u) : Type u := α

postfix `ᵐᵒᵖ`:std.prec.max_plus := mul_opposite

namespace mul_opposite

variables {α : Type u}

/-- The element of `mul_opposite α` that represents `x : α`. -/
@[pp_nodot]
def op : α → αᵐᵒᵖ := id

/-- The element of `α` represented by `x : αᵐᵒᵖ`. -/
@[pp_nodot]
def unop : αᵐᵒᵖ → α := id

@[simp] lemma unop_op (x : α) : unop (op x) = x := rfl
@[simp] lemma op_unop (x : αᵐᵒᵖ) : op (unop x) = x := rfl
@[simp] lemma op_comp_unop : (op : α → αᵐᵒᵖ) ∘ unop = id := rfl
@[simp] lemma unop_comp_op : (unop : αᵐᵒᵖ → α) ∘ op = id := rfl

attribute [irreducible] mul_opposite

/-- A recursor for `opposite`. Use as `induction x using mul_opposite.rec`. -/
@[simp]
protected def rec {F : Π (X : αᵐᵒᵖ), Sort v} (h : Π X, F (op X)) : Π X, F X :=
λ X, h (unop X)

/-- The canonical bijection between `αᵐᵒᵖ` and `α`. -/
@[simps apply symm_apply { fully_applied := ff }]
def op_equiv : α ≃ αᵐᵒᵖ := ⟨op, unop, unop_op, op_unop⟩

lemma op_bijective : bijective (op : α → αᵐᵒᵖ) := op_equiv.bijective
lemma unop_bijective : bijective (unop : αᵐᵒᵖ → α) := op_equiv.symm.bijective
lemma op_injective : injective (op : α → αᵐᵒᵖ) := op_bijective.injective
lemma op_surjective : surjective (op : α → αᵐᵒᵖ) := op_bijective.surjective
lemma unop_injective : injective (unop : αᵐᵒᵖ → α) := unop_bijective.injective
lemma unop_surjective : surjective (unop : αᵐᵒᵖ → α) := unop_bijective.surjective

@[simp] lemma op_inj {x y : α} : op x = op y ↔ x = y := op_injective.eq_iff
@[simp] lemma unop_inj {x y : αᵐᵒᵖ} : unop x = unop y ↔ x = y := unop_injective.eq_iff

variable (α)

instance [nontrivial α] : nontrivial αᵐᵒᵖ := op_injective.nontrivial
instance [inhabited α] : inhabited αᵐᵒᵖ := ⟨op (default α)⟩
instance [subsingleton α] : subsingleton αᵐᵒᵖ := unop_injective.subsingleton
instance [unique α] : unique αᵐᵒᵖ := unique.mk' _
instance [is_empty α] : is_empty αᵐᵒᵖ := function.is_empty unop

instance [has_zero α] : has_zero αᵐᵒᵖ := { zero := op 0 }

instance [has_one α] : has_one αᵐᵒᵖ := { one := op 1 }

instance [has_add α] : has_add αᵐᵒᵖ :=
{ add := λ x y, op (unop x + unop y) }

instance [has_sub α] : has_sub αᵐᵒᵖ :=
{ sub := λ x y, op (unop x - unop y) }

instance [has_neg α] : has_neg αᵐᵒᵖ :=
{ neg := λ x, op $ -(unop x) }

instance [has_mul α] : has_mul αᵐᵒᵖ :=
{ mul := λ x y, op (unop y * unop x) }

instance [has_inv α] : has_inv αᵐᵒᵖ :=
{ inv := λ x, op $ (unop x)⁻¹ }

instance (R : Type*) [has_scalar R α] : has_scalar R αᵐᵒᵖ :=
{ smul := λ c x, op (c • unop x) }

section
variables (α)

@[simp] lemma op_zero [has_zero α] : op (0 : α) = 0 := rfl
@[simp] lemma unop_zero [has_zero α] : unop (0 : αᵐᵒᵖ) = 0 := rfl

@[simp] lemma op_one [has_one α] : op (1 : α) = 1 := rfl
@[simp] lemma unop_one [has_one α] : unop (1 : αᵐᵒᵖ) = 1 := rfl

variable {α}

@[simp] lemma op_add [has_add α] (x y : α) : op (x + y) = op x + op y := rfl
@[simp] lemma unop_add [has_add α] (x y : αᵐᵒᵖ) : unop (x + y) = unop x + unop y := rfl

@[simp] lemma op_neg [has_neg α] (x : α) : op (-x) = -op x := rfl
@[simp] lemma unop_neg [has_neg α] (x : αᵐᵒᵖ) : unop (-x) = -unop x := rfl

@[simp] lemma op_mul [has_mul α] (x y : α) : op (x * y) = op y * op x := rfl
@[simp] lemma unop_mul [has_mul α] (x y : αᵐᵒᵖ) : unop (x * y) = unop y * unop x := rfl

@[simp] lemma op_inv [has_inv α] (x : α) : op (x⁻¹) = (op x)⁻¹ := rfl
@[simp] lemma unop_inv [has_inv α] (x : αᵐᵒᵖ) : unop (x⁻¹) = (unop x)⁻¹ := rfl

@[simp] lemma op_sub [has_sub α] (x y : α) : op (x - y) = op x - op y := rfl
@[simp] lemma unop_sub [has_sub α] (x y : αᵐᵒᵖ) : unop (x - y) = unop x - unop y := rfl

@[simp] lemma op_smul {R : Type*} [has_scalar R α] (c : R) (a : α) : op (c • a) = c • op a := rfl
@[simp] lemma unop_smul {R : Type*} [has_scalar R α] (c : R) (a : αᵐᵒᵖ) :
  unop (c • a) = c • unop a := rfl

end

instance [add_semigroup α] : add_semigroup (αᵐᵒᵖ) :=
unop_injective.add_semigroup _ (λ x y, rfl)

instance [add_left_cancel_semigroup α] : add_left_cancel_semigroup αᵐᵒᵖ :=
unop_injective.add_left_cancel_semigroup _ (λ x y, rfl)

instance [add_right_cancel_semigroup α] : add_right_cancel_semigroup αᵐᵒᵖ :=
unop_injective.add_right_cancel_semigroup _ (λ x y, rfl)

instance [add_comm_semigroup α] : add_comm_semigroup αᵐᵒᵖ :=
{ add_comm := λ x y, unop_injective $ add_comm (unop x) (unop y),
  .. mul_opposite.add_semigroup α }

@[simp] lemma unop_eq_zero_iff {α} [has_zero α] (a : αᵐᵒᵖ) : a.unop = (0 : α) ↔ a = (0 : αᵐᵒᵖ) :=
unop_injective.eq_iff' rfl

@[simp] lemma op_eq_zero_iff {α} [has_zero α] (a : α) : op a = (0 : αᵐᵒᵖ) ↔ a = (0 : α) :=
op_injective.eq_iff' rfl

lemma unop_ne_zero_iff {α} [has_zero α] (a : αᵐᵒᵖ) : a.unop ≠ (0 : α) ↔ a ≠ (0 : αᵐᵒᵖ) :=
not_congr $ unop_eq_zero_iff a

lemma op_ne_zero_iff {α} [has_zero α] (a : α) : op a ≠ (0 : αᵐᵒᵖ) ↔ a ≠ (0 : α) :=
not_congr $ op_eq_zero_iff a

instance [add_zero_class α] : add_zero_class αᵐᵒᵖ :=
unop_injective.add_zero_class _ rfl (λ x y, rfl)

instance [add_monoid α] : add_monoid αᵐᵒᵖ :=
unop_injective.add_monoid_smul _ rfl (λ _ _, rfl) (λ _ _, rfl)

instance [add_comm_monoid α] : add_comm_monoid αᵐᵒᵖ :=
{ .. mul_opposite.add_monoid α, .. mul_opposite.add_comm_semigroup α }

instance [sub_neg_monoid α] : sub_neg_monoid αᵐᵒᵖ :=
unop_injective.sub_neg_monoid_smul _ rfl (λ _ _, rfl) (λ _, rfl)
  (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl)

instance [add_group α] : add_group αᵐᵒᵖ :=
unop_injective.add_group_smul _ rfl (λ _ _, rfl) (λ _, rfl)
  (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl)

instance [add_comm_group α] : add_comm_group αᵐᵒᵖ :=
{ .. mul_opposite.add_group α, .. mul_opposite.add_comm_monoid α }

instance [semigroup α] : semigroup αᵐᵒᵖ :=
{ mul_assoc := λ x y z, unop_injective $ eq.symm $ mul_assoc (unop z) (unop y) (unop x),
  .. mul_opposite.has_mul α }

instance [right_cancel_semigroup α] : left_cancel_semigroup αᵐᵒᵖ :=
{ mul_left_cancel := λ x y z H, unop_injective $ mul_right_cancel $ op_injective H,
  .. mul_opposite.semigroup α }

instance [left_cancel_semigroup α] : right_cancel_semigroup αᵐᵒᵖ :=
{ mul_right_cancel := λ x y z H, unop_injective $ mul_left_cancel $ op_injective H,
  .. mul_opposite.semigroup α }

instance [comm_semigroup α] : comm_semigroup αᵐᵒᵖ :=
{ mul_comm := λ x y, unop_injective $ mul_comm (unop y) (unop x),
  .. mul_opposite.semigroup α }

@[simp] lemma unop_eq_one_iff {α} [has_one α] (a : αᵐᵒᵖ) : a.unop = 1 ↔ a = 1 :=
unop_injective.eq_iff' rfl

@[simp] lemma op_eq_one_iff {α} [has_one α] (a : α) : op a = 1 ↔ a = 1 :=
op_injective.eq_iff' rfl

instance [mul_one_class α] : mul_one_class αᵐᵒᵖ :=
{ one_mul := λ x, unop_injective $ mul_one $ unop x,
  mul_one := λ x, unop_injective $ one_mul $ unop x,
  .. mul_opposite.has_mul α, .. mul_opposite.has_one α }

instance [monoid α] : monoid αᵐᵒᵖ :=
{ npow := λ n x, op $ x.unop ^ n,
  npow_zero' := λ x, unop_injective $ monoid.npow_zero' x.unop,
  npow_succ' := λ n x, unop_injective $ pow_succ' x.unop n,
  .. mul_opposite.semigroup α, .. mul_opposite.mul_one_class α }

instance [right_cancel_monoid α] : left_cancel_monoid αᵐᵒᵖ :=
{ .. mul_opposite.left_cancel_semigroup α, .. mul_opposite.monoid α }

instance [left_cancel_monoid α] : right_cancel_monoid αᵐᵒᵖ :=
{ .. mul_opposite.right_cancel_semigroup α, .. mul_opposite.monoid α }

instance [cancel_monoid α] : cancel_monoid αᵐᵒᵖ :=
{ .. mul_opposite.right_cancel_monoid α, .. mul_opposite.left_cancel_monoid α }

instance [comm_monoid α] : comm_monoid αᵐᵒᵖ :=
{ .. mul_opposite.monoid α, .. mul_opposite.comm_semigroup α }

instance [cancel_comm_monoid α] : cancel_comm_monoid αᵐᵒᵖ :=
{ .. mul_opposite.cancel_monoid α, .. mul_opposite.comm_monoid α }

instance [div_inv_monoid α] : div_inv_monoid αᵐᵒᵖ :=
{ zpow := λ n x, op $ x.unop ^ n,
  zpow_zero' := λ x, unop_injective $ div_inv_monoid.zpow_zero' x.unop,
  zpow_succ' := λ n x, unop_injective $
    by rw [unop_op, zpow_of_nat, zpow_of_nat, pow_succ', unop_mul, unop_op],
  zpow_neg' := λ z x, unop_injective $ div_inv_monoid.zpow_neg' z x.unop,
  .. mul_opposite.monoid α, .. mul_opposite.has_inv α }

instance [group α] : group αᵐᵒᵖ :=
{ mul_left_inv := λ x, unop_injective $ mul_inv_self $ unop x,
  .. mul_opposite.div_inv_monoid α, }

instance [comm_group α] : comm_group αᵐᵒᵖ :=
{ .. mul_opposite.group α, .. mul_opposite.comm_monoid α }

instance [mul_zero_class α] : mul_zero_class αᵐᵒᵖ :=
{ zero := 0,
  mul := (*),
  zero_mul := λ x, unop_injective $ mul_zero $ unop x,
  mul_zero := λ x, unop_injective $ zero_mul $ unop x }

instance [mul_zero_one_class α] : mul_zero_one_class αᵐᵒᵖ :=
{ .. mul_opposite.mul_zero_class α, .. mul_opposite.mul_one_class α }

instance [semigroup_with_zero α] : semigroup_with_zero αᵐᵒᵖ :=
{ .. mul_opposite.semigroup α, .. mul_opposite.mul_zero_class α }

instance [monoid_with_zero α] : monoid_with_zero αᵐᵒᵖ :=
{ .. mul_opposite.monoid α, .. mul_opposite.mul_zero_one_class α }

instance [has_zero α] [has_mul α] [no_zero_divisors α] : no_zero_divisors αᵐᵒᵖ :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := λ x y (H : op (_ * _) = op (0:α)),
    or.cases_on (eq_zero_or_eq_zero_of_mul_eq_zero $ op_injective H)
      (λ hy, or.inr $ unop_injective $ hy) (λ hx, or.inl $ unop_injective $ hx), }

instance [group_with_zero α] : group_with_zero αᵐᵒᵖ :=
{ mul_inv_cancel := λ x hx, unop_injective $ inv_mul_cancel $ unop_injective.ne hx,
  inv_zero := unop_injective inv_zero,
  .. mul_opposite.monoid_with_zero α, .. mul_opposite.div_inv_monoid α,
  .. mul_opposite.nontrivial α }

variable {α}

lemma semiconj_by.op [has_mul α] {a x y : α} (h : semiconj_by a x y) :
  semiconj_by (op a) (op y) (op x) :=
begin
  dunfold semiconj_by,
  rw [← op_mul, ← op_mul, h.eq]
end

lemma semiconj_by.unop [has_mul α] {a x y : αᵐᵒᵖ} (h : semiconj_by a x y) :
  semiconj_by (unop a) (unop y) (unop x) :=
begin
  dunfold semiconj_by,
  rw [← unop_mul, ← unop_mul, h.eq]
end

@[simp] lemma semiconj_by_op [has_mul α] {a x y : α} :
  semiconj_by (op a) (op y) (op x) ↔ semiconj_by a x y :=
begin
  split,
  { intro h,
    rw [← unop_op a, ← unop_op x, ← unop_op y],
    exact semiconj_by.unop h },
  { intro h,
    exact semiconj_by.op h }
end

@[simp] lemma semiconj_by_unop [has_mul α] {a x y : αᵐᵒᵖ} :
  semiconj_by (unop a) (unop y) (unop x) ↔ semiconj_by a x y :=
by conv_rhs { rw [← op_unop a, ← op_unop x, ← op_unop y, semiconj_by_op] }

lemma commute.op [has_mul α] {x y : α} (h : commute x y) : commute (op x) (op y) :=
begin
  dunfold commute at h ⊢,
  exact semiconj_by.op h
end

lemma commute.unop [has_mul α] {x y : αᵐᵒᵖ} (h : commute x y) : commute (unop x) (unop y) :=
begin
  dunfold commute at h ⊢,
  exact semiconj_by.unop h
end

@[simp] lemma commute_op [has_mul α] {x y : α} :
  commute (op x) (op y) ↔ commute x y :=
begin
  dunfold commute,
  rw semiconj_by_op
end

@[simp] lemma commute_unop [has_mul α] {x y : αᵐᵒᵖ} :
  commute (unop x) (unop y) ↔ commute x y :=
begin
  dunfold commute,
  rw semiconj_by_unop
end

/-- The function `unop` is an additive equivalence. -/
@[simps { fully_applied := ff, simp_rhs := tt }]
def op_add_equiv [has_add α] : α ≃+ αᵐᵒᵖ :=
{ map_add' := λ a b, rfl, .. op_equiv }

@[simp] lemma op_add_equiv_to_equiv [has_add α] :
  (op_add_equiv : α ≃+ αᵐᵒᵖ).to_equiv = op_equiv :=
rfl

end mul_opposite

open mul_opposite

/-- Inversion on a group is a `mul_equiv` to the opposite group. When `G` is commutative, there is
`mul_equiv.inv`. -/
@[simps { fully_applied := ff, simp_rhs := tt }]
def mul_equiv.inv' (G : Type*) [group G] : G ≃* Gᵐᵒᵖ :=
{ map_mul' := λ x y, unop_injective $ mul_inv_rev x y,
  .. (equiv.inv G).trans op_equiv }

/-- A monoid homomorphism `f : R →* S` such that `f x` commutes with `f y` for all `x, y` defines
a monoid homomorphism to `Sᵐᵒᵖ`. -/
@[simps {fully_applied := ff}]
def monoid_hom.to_opposite {R S : Type*} [mul_one_class R] [mul_one_class S] (f : R →* S)
  (hf : ∀ x y, commute (f x) (f y)) : R →* Sᵐᵒᵖ :=
{ to_fun := mul_opposite.op ∘ f,
  map_one' := congr_arg op f.map_one,
  map_mul' := λ x y, by simp [(hf x y).eq] }

/-- The units of the opposites are equivalent to the opposites of the units. -/
def units.op_equiv {R} [monoid R] : units Rᵐᵒᵖ ≃* (units R)ᵐᵒᵖ :=
{ to_fun := λ u, op ⟨unop u, unop ↑(u⁻¹), op_injective u.4, op_injective u.3⟩,
  inv_fun := mul_opposite.rec $ λ u, ⟨op ↑(u), op ↑(u⁻¹), unop_injective $ u.4, unop_injective u.3⟩,
  map_mul' := λ x y, unop_injective $ units.ext $ rfl,
  left_inv := λ x, units.ext $ by simp,
  right_inv := λ x, unop_injective $ units.ext $ rfl }

@[simp]
lemma units.coe_unop_op_equiv {R} [monoid R] (u : units Rᵐᵒᵖ) :
  ((units.op_equiv u).unop : R) = unop (u : Rᵐᵒᵖ) :=
rfl

@[simp]
lemma units.coe_op_equiv_symm {R} [monoid R] (u : (units R)ᵐᵒᵖ) :
  (units.op_equiv.symm u : Rᵐᵒᵖ) = op (u.unop : R) :=
rfl

/-- A hom `α →* β` can equivalently be viewed as a hom `αᵐᵒᵖ →* βᵐᵒᵖ`. This is the action of the
(fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps]
def monoid_hom.op {α β} [mul_one_class α] [mul_one_class β] :
  (α →* β) ≃ (αᵐᵒᵖ →* βᵐᵒᵖ) :=
{ to_fun    := λ f, { to_fun   := op ∘ f ∘ unop,
                      map_one' := congr_arg op f.map_one,
                      map_mul' := λ x y, unop_injective (f.map_mul y.unop x.unop) },
  inv_fun   := λ f, { to_fun   := unop ∘ f ∘ op,
                      map_one' := congr_arg unop f.map_one,
                      map_mul' := λ x y, congr_arg unop (f.map_mul (op y) (op x)) },
  left_inv  := λ f, by { ext, refl },
  right_inv := λ f, by { ext x, simp } }

/-- The 'unopposite' of a monoid hom `αᵐᵒᵖ →* βᵐᵒᵖ`. Inverse to `monoid_hom.op`. -/
@[simp] def monoid_hom.unop {α β} [mul_one_class α] [mul_one_class β] :
  (αᵐᵒᵖ →* βᵐᵒᵖ) ≃ (α →* β) := monoid_hom.op.symm

/-- A hom `α →+ β` can equivalently be viewed as a hom `αᵐᵒᵖ →+ βᵐᵒᵖ`. This is the action of the
(fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps]
def add_monoid_hom.op {α β} [add_zero_class α] [add_zero_class β] :
  (α →+ β) ≃ (αᵐᵒᵖ →+ βᵐᵒᵖ) :=
{ to_fun    := λ f, { to_fun    := op ∘ f ∘ unop,
                      map_zero' := unop_injective f.map_zero,
                      map_add'  := λ x y, unop_injective (f.map_add x.unop y.unop) },
  inv_fun   := λ f, { to_fun    := unop ∘ f ∘ op,
                      map_zero' := congr_arg unop f.map_zero,
                      map_add'  := λ x y, congr_arg unop (f.map_add (op x) (op y)) },
  left_inv  := λ f, by { ext, refl },
  right_inv := λ f, by { ext, simp } }

/-- The 'unopposite' of an additive monoid hom `αᵐᵒᵖ →+ βᵐᵒᵖ`. Inverse to `add_monoid_hom.op`. -/
@[simp] def add_monoid_hom.unop {α β} [add_zero_class α] [add_zero_class β] :
  (αᵐᵒᵖ →+ βᵐᵒᵖ) ≃ (α →+ β) := add_monoid_hom.op.symm

/-- A iso `α ≃+ β` can equivalently be viewed as an iso `αᵐᵒᵖ ≃+ βᵐᵒᵖ`. -/
@[simps]
def add_equiv.op {α β} [has_add α] [has_add β] :
  (α ≃+ β) ≃ (αᵐᵒᵖ ≃+ βᵐᵒᵖ) :=
{ to_fun    := λ f, op_add_equiv.symm.trans (f.trans op_add_equiv),
  inv_fun   := λ f, op_add_equiv.trans (f.trans op_add_equiv.symm),
  left_inv  := λ f, by { ext, refl },
  right_inv := λ f, by { ext, simp } }

/-- The 'unopposite' of an iso `αᵐᵒᵖ ≃+ βᵐᵒᵖ`. Inverse to `add_equiv.op`. -/
@[simp] def add_equiv.unop {α β} [has_add α] [has_add β] :
  (αᵐᵒᵖ ≃+ βᵐᵒᵖ) ≃ (α ≃+ β) := add_equiv.op.symm

/-- A iso `α ≃* β` can equivalently be viewed as an iso `αᵐᵒᵖ ≃+ βᵐᵒᵖ`. -/
@[simps]
def mul_equiv.op {α β} [has_mul α] [has_mul β] :
  (α ≃* β) ≃ (αᵐᵒᵖ ≃* βᵐᵒᵖ) :=
{ to_fun    := λ f, { to_fun   := op ∘ f ∘ unop,
                      inv_fun  := op ∘ f.symm ∘ unop,
                      left_inv := λ x, unop_injective (f.symm_apply_apply x.unop),
                      right_inv := λ x, unop_injective (f.apply_symm_apply x.unop),
                      map_mul' := λ x y, unop_injective (f.map_mul y.unop x.unop) },
  inv_fun   := λ f, { to_fun   := unop ∘ f ∘ op,
                      inv_fun  := unop ∘ f.symm ∘ op,
                      left_inv := λ x, by simp,
                      right_inv := λ x, by simp,
                      map_mul' := λ x y, congr_arg unop (f.map_mul (op y) (op x)) },
  left_inv  := λ f, by { ext, refl },
  right_inv := λ f, by { ext, simp } }

/-- The 'unopposite' of an iso `αᵐᵒᵖ ≃* βᵐᵒᵖ`. Inverse to `mul_equiv.op`. -/
@[simp] def mul_equiv.unop {α β} [has_mul α] [has_mul β] :
  (αᵐᵒᵖ ≃* βᵐᵒᵖ) ≃ (α ≃* β) := mul_equiv.op.symm

section ext

/-- This ext lemma change equalities on `αᵐᵒᵖ →+ β` to equalities on `α →+ β`.
This is useful because there are often ext lemmas for specific `α`s that will apply
to an equality of `α →+ β` such as `finsupp.add_hom_ext'`. -/
@[ext]
lemma add_monoid_hom.op_ext {α β} [add_zero_class α] [add_zero_class β]
  (f g : αᵐᵒᵖ →+ β)
  (h : f.comp (op_add_equiv : α ≃+ αᵐᵒᵖ).to_add_monoid_hom =
       g.comp (op_add_equiv : α ≃+ αᵐᵒᵖ).to_add_monoid_hom) : f = g :=
add_monoid_hom.ext $ mul_opposite.rec $ λ x, (add_monoid_hom.congr_fun h : _) x

end ext

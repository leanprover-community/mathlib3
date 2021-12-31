/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import algebra.group.inj_surj
import algebra.group.commute
import algebra.opposites
import data.equiv.mul_add

/-!
# Group structures on the multiplicative opposite
-/
universes u v
variables (α : Type u)

namespace mul_opposite

instance [add_semigroup α] : add_semigroup (αᵐᵒᵖ) :=
unop_injective.add_semigroup _ (λ x y, rfl)

instance [add_left_cancel_semigroup α] : add_left_cancel_semigroup αᵐᵒᵖ :=
unop_injective.add_left_cancel_semigroup _ (λ x y, rfl)

instance [add_right_cancel_semigroup α] : add_right_cancel_semigroup αᵐᵒᵖ :=
unop_injective.add_right_cancel_semigroup _ (λ x y, rfl)

instance [add_comm_semigroup α] : add_comm_semigroup αᵐᵒᵖ :=
{ add_comm := λ x y, unop_injective $ add_comm (unop x) (unop y),
  .. mul_opposite.add_semigroup α }

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

/-- A monoid homomorphism `f : R →* S` such that `f x` commutes with `f y` for all `x, y` defines
a monoid homomorphism from `Rᵐᵒᵖ`. -/
@[simps {fully_applied := ff}]
def monoid_hom.from_opposite {R S : Type*} [mul_one_class R] [mul_one_class S] (f : R →* S)
  (hf : ∀ x y, commute (f x) (f y)) : Rᵐᵒᵖ →* S :=
{ to_fun := f ∘ mul_opposite.unop,
  map_one' := f.map_one,
  map_mul' := λ x y, (f.map_mul _ _).trans (hf _ _).eq }

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

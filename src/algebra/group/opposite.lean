/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import algebra.group.inj_surj
import algebra.group.commute
import algebra.hom.equiv
import algebra.opposites

/-!
# Group structures on the multiplicative and additive opposites
-/
universes u v
variables (α : Type u)

namespace mul_opposite

/-!
### Additive structures on `αᵐᵒᵖ`
-/

instance [add_semigroup α] : add_semigroup (αᵐᵒᵖ) :=
unop_injective.add_semigroup _ (λ x y, rfl)

instance [add_left_cancel_semigroup α] : add_left_cancel_semigroup αᵐᵒᵖ :=
unop_injective.add_left_cancel_semigroup _ (λ x y, rfl)

instance [add_right_cancel_semigroup α] : add_right_cancel_semigroup αᵐᵒᵖ :=
unop_injective.add_right_cancel_semigroup _ (λ x y, rfl)

instance [add_comm_semigroup α] : add_comm_semigroup αᵐᵒᵖ :=
unop_injective.add_comm_semigroup _ (λ x y, rfl)

instance [add_zero_class α] : add_zero_class αᵐᵒᵖ :=
unop_injective.add_zero_class _ rfl (λ x y, rfl)

instance [add_monoid α] : add_monoid αᵐᵒᵖ :=
unop_injective.add_monoid _ rfl (λ _ _, rfl) (λ _ _, rfl)

instance [add_comm_monoid α] : add_comm_monoid αᵐᵒᵖ :=
unop_injective.add_comm_monoid _ rfl (λ _ _, rfl) (λ _ _, rfl)

instance [sub_neg_monoid α] : sub_neg_monoid αᵐᵒᵖ :=
unop_injective.sub_neg_monoid _ rfl (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl)

instance [add_group α] : add_group αᵐᵒᵖ :=
unop_injective.add_group _ rfl (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl)

instance [add_comm_group α] : add_comm_group αᵐᵒᵖ :=
unop_injective.add_comm_group _ rfl (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl)

/-!
### Multiplicative structures on `αᵐᵒᵖ`

We also generate additive structures on `αᵃᵒᵖ` using `to_additive`
-/

@[to_additive] instance [semigroup α] : semigroup αᵐᵒᵖ :=
{ mul_assoc := λ x y z, unop_injective $ eq.symm $ mul_assoc (unop z) (unop y) (unop x),
  .. mul_opposite.has_mul α }

@[to_additive] instance [right_cancel_semigroup α] : left_cancel_semigroup αᵐᵒᵖ :=
{ mul_left_cancel := λ x y z H, unop_injective $ mul_right_cancel $ op_injective H,
  .. mul_opposite.semigroup α }

@[to_additive] instance [left_cancel_semigroup α] : right_cancel_semigroup αᵐᵒᵖ :=
{ mul_right_cancel := λ x y z H, unop_injective $ mul_left_cancel $ op_injective H,
  .. mul_opposite.semigroup α }

@[to_additive] instance [comm_semigroup α] : comm_semigroup αᵐᵒᵖ :=
{ mul_comm := λ x y, unop_injective $ mul_comm (unop y) (unop x),
  .. mul_opposite.semigroup α }

@[to_additive] instance [mul_one_class α] : mul_one_class αᵐᵒᵖ :=
{ one_mul := λ x, unop_injective $ mul_one $ unop x,
  mul_one := λ x, unop_injective $ one_mul $ unop x,
  .. mul_opposite.has_mul α, .. mul_opposite.has_one α }

@[to_additive] instance [monoid α] : monoid αᵐᵒᵖ :=
{ npow := λ n x, op $ x.unop ^ n,
  npow_zero' := λ x, unop_injective $ monoid.npow_zero' x.unop,
  npow_succ' := λ n x, unop_injective $ pow_succ' x.unop n,
  .. mul_opposite.semigroup α, .. mul_opposite.mul_one_class α }

@[to_additive] instance [right_cancel_monoid α] : left_cancel_monoid αᵐᵒᵖ :=
{ .. mul_opposite.left_cancel_semigroup α, .. mul_opposite.monoid α }

@[to_additive] instance [left_cancel_monoid α] : right_cancel_monoid αᵐᵒᵖ :=
{ .. mul_opposite.right_cancel_semigroup α, .. mul_opposite.monoid α }

@[to_additive] instance [cancel_monoid α] : cancel_monoid αᵐᵒᵖ :=
{ .. mul_opposite.right_cancel_monoid α, .. mul_opposite.left_cancel_monoid α }

@[to_additive] instance [comm_monoid α] : comm_monoid αᵐᵒᵖ :=
{ .. mul_opposite.monoid α, .. mul_opposite.comm_semigroup α }

@[to_additive] instance [cancel_comm_monoid α] : cancel_comm_monoid αᵐᵒᵖ :=
{ .. mul_opposite.cancel_monoid α, .. mul_opposite.comm_monoid α }

@[to_additive add_opposite.sub_neg_monoid] instance [div_inv_monoid α] : div_inv_monoid αᵐᵒᵖ :=
{ zpow := λ n x, op $ x.unop ^ n,
  zpow_zero' := λ x, unop_injective $ div_inv_monoid.zpow_zero' x.unop,
  zpow_succ' := λ n x, unop_injective $
    by rw [unop_op, zpow_of_nat, zpow_of_nat, pow_succ', unop_mul, unop_op],
  zpow_neg' := λ z x, unop_injective $ div_inv_monoid.zpow_neg' z x.unop,
  .. mul_opposite.monoid α, .. mul_opposite.has_inv α }

@[to_additive add_opposite.subtraction_monoid] instance [division_monoid α] :
  division_monoid αᵐᵒᵖ :=
{ mul_inv_rev := λ a b, unop_injective $ mul_inv_rev _ _,
  inv_eq_of_mul := λ a b h, unop_injective $ inv_eq_of_mul_eq_one_left $ congr_arg unop h,
  .. mul_opposite.div_inv_monoid α, .. mul_opposite.has_involutive_inv α }

@[to_additive add_opposite.subtraction_comm_monoid] instance [division_comm_monoid α] :
  division_comm_monoid αᵐᵒᵖ :=
{ ..mul_opposite.division_monoid α, ..mul_opposite.comm_semigroup α }

@[to_additive] instance [group α] : group αᵐᵒᵖ :=
{ mul_left_inv := λ x, unop_injective $ mul_inv_self $ unop x,
  .. mul_opposite.div_inv_monoid α, }

@[to_additive] instance [comm_group α] : comm_group αᵐᵒᵖ :=
{ .. mul_opposite.group α, .. mul_opposite.comm_monoid α }

variable {α}

@[simp, to_additive] lemma unop_div [div_inv_monoid α] (x y : αᵐᵒᵖ) :
  unop (x / y) = (unop y)⁻¹ * unop x :=
rfl

@[simp, to_additive] lemma op_div [div_inv_monoid α] (x y : α) :
  op (x / y) = (op y)⁻¹ * op x :=
by simp [div_eq_mul_inv]

@[simp, to_additive] lemma semiconj_by_op [has_mul α] {a x y : α} :
  semiconj_by (op a) (op y) (op x) ↔ semiconj_by a x y :=
by simp only [semiconj_by, ← op_mul, op_inj, eq_comm]

@[simp, to_additive] lemma semiconj_by_unop [has_mul α] {a x y : αᵐᵒᵖ} :
  semiconj_by (unop a) (unop y) (unop x) ↔ semiconj_by a x y :=
by conv_rhs { rw [← op_unop a, ← op_unop x, ← op_unop y, semiconj_by_op] }

@[to_additive] lemma _root_.semiconj_by.op [has_mul α] {a x y : α} (h : semiconj_by a x y) :
  semiconj_by (op a) (op y) (op x) :=
semiconj_by_op.2 h

@[to_additive] lemma _root_.semiconj_by.unop [has_mul α] {a x y : αᵐᵒᵖ} (h : semiconj_by a x y) :
  semiconj_by (unop a) (unop y) (unop x) :=
semiconj_by_unop.2 h

@[to_additive] lemma _root_.commute.op [has_mul α] {x y : α} (h : commute x y) :
  commute (op x) (op y) := h.op

@[to_additive] lemma commute.unop [has_mul α] {x y : αᵐᵒᵖ} (h : commute x y) :
  commute (unop x) (unop y) := h.unop

@[simp, to_additive] lemma commute_op [has_mul α] {x y : α} :
  commute (op x) (op y) ↔ commute x y :=
semiconj_by_op

@[simp, to_additive] lemma commute_unop [has_mul α] {x y : αᵐᵒᵖ} :
  commute (unop x) (unop y) ↔ commute x y :=
semiconj_by_unop

/-- The function `mul_opposite.op` is an additive equivalence. -/
@[simps { fully_applied := ff, simp_rhs := tt }]
def op_add_equiv [has_add α] : α ≃+ αᵐᵒᵖ :=
{ map_add' := λ a b, rfl, .. op_equiv }

@[simp] lemma op_add_equiv_to_equiv [has_add α] :
  (op_add_equiv : α ≃+ αᵐᵒᵖ).to_equiv = op_equiv :=
rfl

end mul_opposite

/-!
### Multiplicative structures on `αᵃᵒᵖ`
-/

namespace add_opposite

instance [semigroup α] : semigroup (αᵃᵒᵖ) :=
unop_injective.semigroup _ (λ x y, rfl)

instance [left_cancel_semigroup α] : left_cancel_semigroup αᵃᵒᵖ :=
unop_injective.left_cancel_semigroup _ (λ x y, rfl)

instance [right_cancel_semigroup α] : right_cancel_semigroup αᵃᵒᵖ :=
unop_injective.right_cancel_semigroup _ (λ x y, rfl)

instance [comm_semigroup α] : comm_semigroup αᵃᵒᵖ :=
unop_injective.comm_semigroup _ (λ x y, rfl)

instance [mul_one_class α] : mul_one_class αᵃᵒᵖ :=
unop_injective.mul_one_class _ rfl (λ x y, rfl)

instance {β} [has_pow α β] : has_pow αᵃᵒᵖ β := { pow := λ a b, op (unop a ^ b) }

@[simp] lemma op_pow {β} [has_pow α β] (a : α) (b : β) : op (a ^ b) = op a ^ b := rfl
@[simp] lemma unop_pow {β} [has_pow α β] (a : αᵃᵒᵖ) (b : β) : unop (a ^ b) = unop a ^ b := rfl

instance [monoid α] : monoid αᵃᵒᵖ :=
unop_injective.monoid _ rfl (λ _ _, rfl) (λ _ _, rfl)

instance [comm_monoid α] : comm_monoid αᵃᵒᵖ :=
unop_injective.comm_monoid _ rfl (λ _ _, rfl) (λ _ _, rfl)

instance [div_inv_monoid α] : div_inv_monoid αᵃᵒᵖ :=
unop_injective.div_inv_monoid _ rfl (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl)

instance [group α] : group αᵃᵒᵖ :=
unop_injective.group _ rfl (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl)

instance [comm_group α] : comm_group αᵃᵒᵖ :=
unop_injective.comm_group _ rfl (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl)

variable {α}

/-- The function `add_opposite.op` is a multiplicative equivalence. -/
@[simps { fully_applied := ff, simp_rhs := tt }]
def op_mul_equiv [has_mul α] : α ≃* αᵃᵒᵖ :=
{ map_mul' := λ a b, rfl, .. op_equiv }

@[simp] lemma op_mul_equiv_to_equiv [has_mul α] :
  (op_mul_equiv : α ≃* αᵃᵒᵖ).to_equiv = op_equiv :=
rfl

end add_opposite

open mul_opposite

/-- Inversion on a group is a `mul_equiv` to the opposite group. When `G` is commutative, there is
`mul_equiv.inv`. -/
@[to_additive "Negation on an additive group is an `add_equiv` to the opposite group. When `G`
is commutative, there is `add_equiv.inv`.", simps { fully_applied := ff, simp_rhs := tt }]
def mul_equiv.inv' (G : Type*) [division_monoid G] : G ≃* Gᵐᵒᵖ :=
{ map_mul' := λ x y, unop_injective $ mul_inv_rev x y,
  .. (equiv.inv G).trans op_equiv }

/-- A semigroup homomorphism `f : M →ₙ* N` such that `f x` commutes with `f y` for all `x, y`
defines a semigroup homomorphism to `Nᵐᵒᵖ`. -/
@[to_additive "An additive semigroup homomorphism `f : add_hom M N` such that `f x` additively
commutes with `f y` for all `x, y` defines an additive semigroup homomorphism to `Sᵃᵒᵖ`.",
  simps {fully_applied := ff}]
def mul_hom.to_opposite {M N : Type*} [has_mul M] [has_mul N] (f : M →ₙ* N)
  (hf : ∀ x y, commute (f x) (f y)) : M →ₙ* Nᵐᵒᵖ :=
{ to_fun := mul_opposite.op ∘ f,
  map_mul' := λ x y, by simp [(hf x y).eq] }

/-- A semigroup homomorphism `f : M →ₙ* N` such that `f x` commutes with `f y` for all `x, y`
defines a semigroup homomorphism from `Mᵐᵒᵖ`. -/
@[to_additive "An additive semigroup homomorphism `f : add_hom M N` such that `f x` additively
commutes with `f y` for all `x`, `y` defines an additive semigroup homomorphism from `Mᵃᵒᵖ`.",
  simps {fully_applied := ff}]
def mul_hom.from_opposite {M N : Type*} [has_mul M] [has_mul N] (f : M →ₙ* N)
  (hf : ∀ x y, commute (f x) (f y)) : Mᵐᵒᵖ →ₙ* N :=
{ to_fun := f ∘ mul_opposite.unop,
  map_mul' := λ x y, (f.map_mul _ _).trans (hf _ _).eq }

/-- A monoid homomorphism `f : M →* N` such that `f x` commutes with `f y` for all `x, y` defines
a monoid homomorphism to `Nᵐᵒᵖ`. -/
@[to_additive "An additive monoid homomorphism `f : M →+ N` such that `f x` additively commutes
with `f y` for all `x, y` defines an additive monoid homomorphism to `Sᵃᵒᵖ`.",
  simps {fully_applied := ff}]
def monoid_hom.to_opposite {M N : Type*} [mul_one_class M] [mul_one_class N] (f : M →* N)
  (hf : ∀ x y, commute (f x) (f y)) : M →* Nᵐᵒᵖ :=
{ to_fun := mul_opposite.op ∘ f,
  map_one' := congr_arg op f.map_one,
  map_mul' := λ x y, by simp [(hf x y).eq] }

/-- A monoid homomorphism `f : M →* N` such that `f x` commutes with `f y` for all `x, y` defines
a monoid homomorphism from `Mᵐᵒᵖ`. -/
@[to_additive "An additive monoid homomorphism `f : M →+ N` such that `f x` additively commutes
with `f y` for all `x`, `y` defines an additive monoid homomorphism from `Mᵃᵒᵖ`.",
  simps {fully_applied := ff}]
def monoid_hom.from_opposite {M N : Type*} [mul_one_class M] [mul_one_class N] (f : M →* N)
  (hf : ∀ x y, commute (f x) (f y)) : Mᵐᵒᵖ →* N :=
{ to_fun := f ∘ mul_opposite.unop,
  map_one' := f.map_one,
  map_mul' := λ x y, (f.map_mul _ _).trans (hf _ _).eq }

/-- The units of the opposites are equivalent to the opposites of the units. -/
@[to_additive "The additive units of the additive opposites are equivalent to the additive opposites
of the additive units."]
def units.op_equiv {M} [monoid M] : (Mᵐᵒᵖ)ˣ ≃* (Mˣ)ᵐᵒᵖ :=
{ to_fun := λ u, op ⟨unop u, unop ↑(u⁻¹), op_injective u.4, op_injective u.3⟩,
  inv_fun := mul_opposite.rec $ λ u, ⟨op ↑(u), op ↑(u⁻¹), unop_injective $ u.4, unop_injective u.3⟩,
  map_mul' := λ x y, unop_injective $ units.ext $ rfl,
  left_inv := λ x, units.ext $ by simp,
  right_inv := λ x, unop_injective $ units.ext $ rfl }

@[simp, to_additive]
lemma units.coe_unop_op_equiv {M} [monoid M] (u : (Mᵐᵒᵖ)ˣ) :
  ((units.op_equiv u).unop : M) = unop (u : Mᵐᵒᵖ) :=
rfl

@[simp, to_additive]
lemma units.coe_op_equiv_symm {M} [monoid M] (u : (Mˣ)ᵐᵒᵖ) :
  (units.op_equiv.symm u : Mᵐᵒᵖ) = op (u.unop : M) :=
rfl

/-- A semigroup homomorphism `M →ₙ* N` can equivalently be viewed as a semigroup homomorphism
`Mᵐᵒᵖ →ₙ* Nᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[to_additive "An additive semigroup homomorphism `add_hom M N` can equivalently be viewed as an
additive semigroup homomorphism `add_hom Mᵃᵒᵖ Nᵃᵒᵖ`. This is the action of the (fully faithful)
`ᵃᵒᵖ`-functor on morphisms.", simps]
def mul_hom.op {M N} [has_mul M] [has_mul N] :
  (M →ₙ* N) ≃ (Mᵐᵒᵖ →ₙ* Nᵐᵒᵖ) :=
{ to_fun    := λ f, { to_fun   := op ∘ f ∘ unop,
                      map_mul' := λ x y, unop_injective (f.map_mul y.unop x.unop) },
  inv_fun   := λ f, { to_fun   := unop ∘ f ∘ op,
                      map_mul' := λ x y, congr_arg unop (f.map_mul (op y) (op x)) },
  left_inv  := λ f, by { ext, refl },
  right_inv := λ f, by { ext x, simp } }

/-- The 'unopposite' of a semigroup homomorphism `Mᵐᵒᵖ →ₙ* Nᵐᵒᵖ`. Inverse to `mul_hom.op`. -/
@[simp, to_additive "The 'unopposite' of an additive semigroup homomorphism `Mᵃᵒᵖ →ₙ+ Nᵃᵒᵖ`. Inverse
to `add_hom.op`."]
def mul_hom.unop {M N} [has_mul M] [has_mul N] :
  (Mᵐᵒᵖ →ₙ* Nᵐᵒᵖ) ≃ (M →ₙ* N) := mul_hom.op.symm

/-- An additive semigroup homomorphism `add_hom M N` can equivalently be viewed as an additive
homomorphism `add_hom Mᵐᵒᵖ Nᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on
morphisms. -/
@[simps]
def add_hom.mul_op {M N} [has_add M] [has_add N] :
  (add_hom M N) ≃ (add_hom Mᵐᵒᵖ Nᵐᵒᵖ) :=
{ to_fun    := λ f, { to_fun    := op ∘ f ∘ unop,
                      map_add'  := λ x y, unop_injective (f.map_add x.unop y.unop) },
  inv_fun   := λ f, { to_fun    := unop ∘ f ∘ op,
                      map_add'  := λ x y, congr_arg unop (f.map_add (op x) (op y)) },
  left_inv  := λ f, by { ext, refl },
  right_inv := λ f, by { ext, simp } }

/-- The 'unopposite' of an additive semigroup hom `αᵐᵒᵖ →+ βᵐᵒᵖ`. Inverse to
`add_hom.mul_op`. -/
@[simp] def add_hom.mul_unop {α β} [has_add α] [has_add β] :
  (add_hom αᵐᵒᵖ βᵐᵒᵖ) ≃ (add_hom α β) := add_hom.mul_op.symm

/-- A monoid homomorphism `M →* N` can equivalently be viewed as a monoid homomorphism
`Mᵐᵒᵖ →* Nᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[to_additive "An additive monoid homomorphism `M →+ N` can equivalently be viewed as an
additive monoid homomorphism `Mᵃᵒᵖ →+ Nᵃᵒᵖ`. This is the action of the (fully faithful)
`ᵃᵒᵖ`-functor on morphisms.", simps]
def monoid_hom.op {M N} [mul_one_class M] [mul_one_class N] :
  (M →* N) ≃ (Mᵐᵒᵖ →* Nᵐᵒᵖ) :=
{ to_fun    := λ f, { to_fun   := op ∘ f ∘ unop,
                      map_one' := congr_arg op f.map_one,
                      map_mul' := λ x y, unop_injective (f.map_mul y.unop x.unop) },
  inv_fun   := λ f, { to_fun   := unop ∘ f ∘ op,
                      map_one' := congr_arg unop f.map_one,
                      map_mul' := λ x y, congr_arg unop (f.map_mul (op y) (op x)) },
  left_inv  := λ f, by { ext, refl },
  right_inv := λ f, by { ext x, simp } }

/-- The 'unopposite' of a monoid homomorphism `Mᵐᵒᵖ →* Nᵐᵒᵖ`. Inverse to `monoid_hom.op`. -/
@[simp, to_additive "The 'unopposite' of an additive monoid homomorphism `Mᵃᵒᵖ →+ Nᵃᵒᵖ`. Inverse to
`add_monoid_hom.op`."]
def monoid_hom.unop {M N} [mul_one_class M] [mul_one_class N] :
  (Mᵐᵒᵖ →* Nᵐᵒᵖ) ≃ (M →* N) := monoid_hom.op.symm

/-- An additive homomorphism `M →+ N` can equivalently be viewed as an additive homomorphism
`Mᵐᵒᵖ →+ Nᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps]
def add_monoid_hom.mul_op {M N} [add_zero_class M] [add_zero_class N] :
  (M →+ N) ≃ (Mᵐᵒᵖ →+ Nᵐᵒᵖ) :=
{ to_fun    := λ f, { to_fun    := op ∘ f ∘ unop,
                      map_zero' := unop_injective f.map_zero,
                      map_add'  := λ x y, unop_injective (f.map_add x.unop y.unop) },
  inv_fun   := λ f, { to_fun    := unop ∘ f ∘ op,
                      map_zero' := congr_arg unop f.map_zero,
                      map_add'  := λ x y, congr_arg unop (f.map_add (op x) (op y)) },
  left_inv  := λ f, by { ext, refl },
  right_inv := λ f, by { ext, simp } }

/-- The 'unopposite' of an additive monoid hom `αᵐᵒᵖ →+ βᵐᵒᵖ`. Inverse to
`add_monoid_hom.mul_op`. -/
@[simp] def add_monoid_hom.mul_unop {α β} [add_zero_class α] [add_zero_class β] :
  (αᵐᵒᵖ →+ βᵐᵒᵖ) ≃ (α →+ β) := add_monoid_hom.mul_op.symm

/-- A iso `α ≃+ β` can equivalently be viewed as an iso `αᵐᵒᵖ ≃+ βᵐᵒᵖ`. -/
@[simps]
def add_equiv.mul_op {α β} [has_add α] [has_add β] :
  (α ≃+ β) ≃ (αᵐᵒᵖ ≃+ βᵐᵒᵖ) :=
{ to_fun    := λ f, op_add_equiv.symm.trans (f.trans op_add_equiv),
  inv_fun   := λ f, op_add_equiv.trans (f.trans op_add_equiv.symm),
  left_inv  := λ f, by { ext, refl },
  right_inv := λ f, by { ext, simp } }

/-- The 'unopposite' of an iso `αᵐᵒᵖ ≃+ βᵐᵒᵖ`. Inverse to `add_equiv.mul_op`. -/
@[simp] def add_equiv.mul_unop {α β} [has_add α] [has_add β] :
  (αᵐᵒᵖ ≃+ βᵐᵒᵖ) ≃ (α ≃+ β) := add_equiv.mul_op.symm

/-- A iso `α ≃* β` can equivalently be viewed as an iso `αᵐᵒᵖ ≃* βᵐᵒᵖ`. -/
@[to_additive "A iso `α ≃+ β` can equivalently be viewed as an iso `αᵃᵒᵖ ≃+ βᵃᵒᵖ`.", simps]
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
@[simp, to_additive "The 'unopposite' of an iso `αᵃᵒᵖ ≃+ βᵃᵒᵖ`. Inverse to `add_equiv.op`."]
def mul_equiv.unop {α β} [has_mul α] [has_mul β] :
  (αᵐᵒᵖ ≃* βᵐᵒᵖ) ≃ (α ≃* β) := mul_equiv.op.symm

section ext

/-- This ext lemma change equalities on `αᵐᵒᵖ →+ β` to equalities on `α →+ β`.
This is useful because there are often ext lemmas for specific `α`s that will apply
to an equality of `α →+ β` such as `finsupp.add_hom_ext'`. -/
@[ext]
lemma add_monoid_hom.mul_op_ext {α β} [add_zero_class α] [add_zero_class β]
  (f g : αᵐᵒᵖ →+ β)
  (h : f.comp (op_add_equiv : α ≃+ αᵐᵒᵖ).to_add_monoid_hom =
       g.comp (op_add_equiv : α ≃+ αᵐᵒᵖ).to_add_monoid_hom) : f = g :=
add_monoid_hom.ext $ mul_opposite.rec $ λ x, (add_monoid_hom.congr_fun h : _) x

end ext

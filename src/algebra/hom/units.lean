/-
Copyright (c) 2018 Johan Commelin All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Chris Hughes, Kevin Buzzard
-/
import algebra.hom.group
import algebra.group.units
/-!
# Monoid homomorphisms and units

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file allows to lift monoid homomorphisms to group homomorphisms of their units subgroups. It
also contains unrelated results about `units` that depend on `monoid_hom`.

## Main declarations

* `units.map`: Turn an homomorphism from `α` to `β` monoids into an homomorphism from `αˣ` to `βˣ`.
* `monoid_hom.to_hom_units`: Turn an homomorphism from a group `α` to `β` into an homomorphism from
  `α` to `βˣ`.

## TODO

The results that don't mention homomorphisms should be proved (earlier?) in a different file and be
used to golf the basic `group` lemmas.
-/

open function

universes u v w

@[to_additive] lemma group.is_unit {G} [group G] (g : G) : is_unit g :=
⟨⟨g, g⁻¹, mul_inv_self g, inv_mul_self g⟩, rfl⟩

section monoid_hom_class

/-- If two homomorphisms from a division monoid to a monoid are equal at a unit `x`, then they are
equal at `x⁻¹`. -/
@[to_additive "If two homomorphisms from a subtraction monoid to an additive monoid are equal at an
additive unit `x`, then they are equal at `-x`."]
lemma is_unit.eq_on_inv {F G N} [division_monoid G] [monoid N] [monoid_hom_class F G N] {x : G}
  (hx : is_unit x) (f g : F) (h : f x = g x) : f x⁻¹ = g x⁻¹ :=
left_inv_eq_right_inv (map_mul_eq_one f hx.inv_mul_cancel) $
  h.symm ▸ map_mul_eq_one g $ hx.mul_inv_cancel

/-- If two homomorphism from a group to a monoid are equal at `x`, then they are equal at `x⁻¹`. -/
@[to_additive "If two homomorphism from an additive group to an additive monoid are equal at `x`,
then they are equal at `-x`." ]
lemma eq_on_inv {F G M} [group G] [monoid M] [monoid_hom_class F G M] (f g : F) {x : G}
  (h : f x = g x) : f x⁻¹ = g x⁻¹ :=
(group.is_unit x).eq_on_inv f g h

end monoid_hom_class

namespace units
variables {α : Type*} {M : Type u} {N : Type v} {P : Type w} [monoid M] [monoid N] [monoid P]

/-- The group homomorphism on units induced by a `monoid_hom`. -/
@[to_additive "The `add_group` homomorphism on `add_unit`s induced by an `add_monoid_hom`."]
def map (f : M →* N) : Mˣ →* Nˣ :=
monoid_hom.mk'
  (λ u, ⟨f u.val, f u.inv,
                  by rw [← f.map_mul, u.val_inv, f.map_one],
                  by rw [← f.map_mul, u.inv_val, f.map_one]⟩)
  (λ x y, ext (f.map_mul x y))

@[simp, to_additive] lemma coe_map (f : M →* N) (x : Mˣ) : ↑(map f x) = f x := rfl

@[simp, to_additive] lemma coe_map_inv (f : M →* N) (u : Mˣ) :
  ↑(map f u)⁻¹ = f ↑u⁻¹ :=
rfl

@[simp, to_additive]
lemma map_comp (f : M →* N) (g : N →* P) : map (g.comp f) = (map g).comp (map f) := rfl

variables (M)
@[simp, to_additive] lemma map_id : map (monoid_hom.id M) = monoid_hom.id Mˣ :=
by ext; refl

/-- Coercion `Mˣ → M` as a monoid homomorphism. -/
@[to_additive "Coercion `add_units M → M` as an add_monoid homomorphism."]
def coe_hom : Mˣ →* M := ⟨coe, coe_one, coe_mul⟩

variable {M}

@[simp, to_additive] lemma coe_hom_apply (x : Mˣ) : coe_hom M x = ↑x := rfl

@[simp, norm_cast, to_additive]
lemma coe_pow (u : Mˣ) (n : ℕ) : ((u ^ n : Mˣ) : M) = u ^ n :=
(units.coe_hom M).map_pow u n

section division_monoid
variables [division_monoid α]

@[simp, norm_cast, to_additive] lemma coe_div : ∀ u₁ u₂ : αˣ, ↑(u₁ / u₂) = (u₁ / u₂ : α) :=
(units.coe_hom α).map_div

@[simp, norm_cast, to_additive] lemma coe_zpow : ∀ (u : αˣ) (n : ℤ), ((u ^ n : αˣ) : α) = u ^ n :=
(units.coe_hom α).map_zpow

@[field_simps] lemma _root_.divp_eq_div (a : α) (u : αˣ) : a /ₚ u = a / u :=
by rw [div_eq_mul_inv, divp, u.coe_inv]

@[simp, to_additive]
lemma _root_.map_units_inv {F : Type*} [monoid_hom_class F M α] (f : F) (u : units M) :
  f ↑u⁻¹ = (f u)⁻¹ :=
((f : M →* α).comp (units.coe_hom M)).map_inv u

end division_monoid

/-- If a map `g : M → Nˣ` agrees with a homomorphism `f : M →* N`, then
this map is a monoid homomorphism too. -/
@[to_additive "If a map `g : M → add_units N` agrees with a homomorphism `f : M →+ N`, then this map
is an add_monoid homomorphism too."]
def lift_right (f : M →* N) (g : M → Nˣ) (h : ∀ x, ↑(g x) = f x) :
  M →* Nˣ :=
{ to_fun := g,
  map_one' := units.ext $ (h 1).symm ▸ f.map_one,
  map_mul' := λ x y, units.ext $ by simp only [h, coe_mul, f.map_mul] }

@[simp, to_additive] lemma coe_lift_right {f : M →* N} {g : M → Nˣ}
  (h : ∀ x, ↑(g x) = f x) (x) : (lift_right f g h x : N) = f x := h x

@[simp, to_additive] lemma mul_lift_right_inv {f : M →* N} {g : M → Nˣ}
  (h : ∀ x, ↑(g x) = f x) (x) : f x * ↑(lift_right f g h x)⁻¹ = 1 :=
by rw [units.mul_inv_eq_iff_eq_mul, one_mul, coe_lift_right]

@[simp, to_additive] lemma lift_right_inv_mul {f : M →* N} {g : M → Nˣ}
  (h : ∀ x, ↑(g x) = f x) (x) : ↑(lift_right f g h x)⁻¹ * f x = 1 :=
by rw [units.inv_mul_eq_iff_eq_mul, mul_one, coe_lift_right]

end units

namespace monoid_hom

/-- If `f` is a homomorphism from a group `G` to a monoid `M`,
then its image lies in the units of `M`,
and `f.to_hom_units` is the corresponding monoid homomorphism from `G` to `Mˣ`. -/
@[to_additive "If `f` is a homomorphism from an additive group `G` to an additive monoid `M`,
then its image lies in the `add_units` of `M`,
and `f.to_hom_units` is the corresponding homomorphism from `G` to `add_units M`."]
def to_hom_units {G M : Type*} [group G] [monoid M] (f : G →* M) : G →* Mˣ :=
units.lift_right f
  (λ g, ⟨f g, f g⁻¹, map_mul_eq_one f (mul_inv_self _), map_mul_eq_one f (inv_mul_self _)⟩)
  (λ g, rfl)

@[simp, to_additive]
lemma coe_to_hom_units {G M : Type*} [group G] [monoid M] (f : G →* M) (g : G) :
  (f.to_hom_units g : M) = f g :=
rfl

end monoid_hom

namespace is_unit
variables {F G α M N : Type*}

section monoid
variables [monoid M] [monoid N]

@[to_additive] lemma map [monoid_hom_class F M N] (f : F) {x : M} (h : is_unit x) : is_unit (f x) :=
by rcases h with ⟨y, rfl⟩; exact (units.map (f : M →* N) y).is_unit

@[to_additive] lemma of_left_inverse [monoid_hom_class F M N] [monoid_hom_class G N M]
  {f : F} {x : M} (g : G) (hfg : function.left_inverse g f) (h : is_unit (f x)) :
  is_unit x :=
by simpa only [hfg x] using h.map g

@[to_additive] lemma _root_.is_unit_map_of_left_inverse
  [monoid_hom_class F M N] [monoid_hom_class G N M]
  {f : F} {x : M} (g : G) (hfg : function.left_inverse g f) :
  is_unit (f x) ↔ is_unit x :=
⟨of_left_inverse g hfg, map _⟩

/-- If a homomorphism `f : M →* N` sends each element to an `is_unit`, then it can be lifted
to `f : M →* Nˣ`. See also `units.lift_right` for a computable version. -/
@[to_additive "If a homomorphism `f : M →+ N` sends each element to an `is_add_unit`, then it can be
lifted to `f : M →+ add_units N`. See also `add_units.lift_right` for a computable version."]
noncomputable def lift_right (f : M →* N) (hf : ∀ x, is_unit (f x)) : M →* Nˣ :=
units.lift_right f (λ x, (hf x).unit) $ λ x, rfl

@[to_additive] lemma coe_lift_right (f : M →* N) (hf : ∀ x, is_unit (f x)) (x) :
  (is_unit.lift_right f hf x : N) = f x := rfl

@[simp, to_additive] lemma mul_lift_right_inv (f : M →* N) (h : ∀ x, is_unit (f x)) (x) :
  f x * ↑(is_unit.lift_right f h x)⁻¹ = 1 :=
units.mul_lift_right_inv (λ y, rfl) x

@[simp, to_additive] lemma lift_right_inv_mul (f : M →* N) (h : ∀ x, is_unit (f x)) (x) :
  ↑(is_unit.lift_right f h x)⁻¹ * f x = 1 :=
units.lift_right_inv_mul (λ y, rfl) x

end monoid

section division_monoid
variables [division_monoid α] {a b c : α}

/-- The element of the group of units, corresponding to an element of a monoid which is a unit. As
opposed to `is_unit.unit`, the inverse is computable and comes from the inversion on `α`. This is
useful to transfer properties of inversion in `units α` to `α`. See also `to_units`. -/
@[to_additive "The element of the additive group of additive units, corresponding to an element of
an additive monoid which is an additive unit. As opposed to `is_add_unit.add_unit`, the negation is
computable and comes from the negation on `α`. This is useful to transfer properties of negation in
`add_units α` to `α`. See also `to_add_units`.", simps]
def unit' (h : is_unit a) : αˣ := ⟨a, a⁻¹, h.mul_inv_cancel, h.inv_mul_cancel⟩

@[simp, to_additive] protected lemma mul_inv_cancel_left (h : is_unit a) : ∀ b, a * (a⁻¹ * b) = b :=
h.unit'.mul_inv_cancel_left

@[simp, to_additive] protected lemma inv_mul_cancel_left (h : is_unit a) : ∀ b, a⁻¹ * (a * b) = b :=
h.unit'.inv_mul_cancel_left

@[simp, to_additive] protected lemma mul_inv_cancel_right (h : is_unit b) (a : α) :
  a * b * b⁻¹ = a :=
h.unit'.mul_inv_cancel_right _

@[simp, to_additive] protected lemma inv_mul_cancel_right (h : is_unit b) (a : α) :
  a * b⁻¹ * b = a :=
h.unit'.inv_mul_cancel_right _

@[to_additive] protected lemma div_self (h : is_unit a) : a / a = 1 :=
by rw [div_eq_mul_inv, h.mul_inv_cancel]

@[to_additive] protected lemma eq_mul_inv_iff_mul_eq (h : is_unit c) : a = b * c⁻¹ ↔ a * c = b :=
h.unit'.eq_mul_inv_iff_mul_eq

@[to_additive] protected lemma eq_inv_mul_iff_mul_eq (h : is_unit b) : a = b⁻¹ * c ↔ b * a = c :=
h.unit'.eq_inv_mul_iff_mul_eq

@[to_additive] protected lemma inv_mul_eq_iff_eq_mul (h : is_unit a) : a⁻¹ * b = c ↔ b = a * c :=
h.unit'.inv_mul_eq_iff_eq_mul

@[to_additive] protected lemma mul_inv_eq_iff_eq_mul (h : is_unit b) : a * b⁻¹ = c ↔ a = c * b :=
h.unit'.mul_inv_eq_iff_eq_mul

@[to_additive] protected lemma mul_inv_eq_one (h : is_unit b) : a * b⁻¹ = 1 ↔ a = b :=
@units.mul_inv_eq_one _ _ h.unit' _

@[to_additive] protected lemma inv_mul_eq_one (h : is_unit a) : a⁻¹ * b = 1 ↔ a = b :=
@units.inv_mul_eq_one _ _ h.unit' _

@[to_additive] protected lemma mul_eq_one_iff_eq_inv (h : is_unit b) : a * b = 1 ↔ a = b⁻¹ :=
@units.mul_eq_one_iff_eq_inv _ _ h.unit' _

@[to_additive] protected lemma mul_eq_one_iff_inv_eq (h : is_unit a) : a * b = 1 ↔ a⁻¹ = b :=
@units.mul_eq_one_iff_inv_eq _ _ h.unit' _

@[simp, to_additive] protected lemma div_mul_cancel (h : is_unit b) (a : α) : a / b * b = a :=
by rw [div_eq_mul_inv, h.inv_mul_cancel_right]

@[simp, to_additive] protected lemma mul_div_cancel (h : is_unit b) (a : α) : a * b / b = a :=
by rw [div_eq_mul_inv, h.mul_inv_cancel_right]

@[to_additive] protected lemma mul_one_div_cancel (h : is_unit a) : a * (1 / a) = 1 := by simp [h]
@[to_additive] protected lemma one_div_mul_cancel (h : is_unit a) : (1 / a) * a = 1 := by simp [h]

@[to_additive] lemma inv : is_unit a → is_unit a⁻¹ :=
by { rintro ⟨u, rfl⟩, rw ←units.coe_inv, exact units.is_unit _ }

@[to_additive] lemma div (ha : is_unit a) (hb : is_unit b) : is_unit (a / b) :=
by { rw div_eq_mul_inv, exact ha.mul hb.inv }

@[to_additive] protected lemma div_left_inj (h : is_unit c) : a / c = b / c ↔ a = b :=
by { simp_rw div_eq_mul_inv, exact units.mul_left_inj h.inv.unit' }

@[to_additive] protected lemma div_eq_iff (h : is_unit b) : a / b = c ↔ a = c * b :=
by rw [div_eq_mul_inv, h.mul_inv_eq_iff_eq_mul]

@[to_additive] protected lemma eq_div_iff (h : is_unit c) : a = b / c ↔ a * c = b :=
by rw [div_eq_mul_inv, h.eq_mul_inv_iff_mul_eq]

@[to_additive] protected lemma div_eq_of_eq_mul (h : is_unit b) : a = c * b → a / b = c :=
h.div_eq_iff.2

@[to_additive] protected lemma eq_div_of_mul_eq (h : is_unit c) : a * c = b → a = b / c :=
h.eq_div_iff.2

@[to_additive] protected lemma div_eq_one_iff_eq (h : is_unit b) : a / b = 1 ↔ a = b :=
⟨eq_of_div_eq_one, λ hab, hab.symm ▸ h.div_self⟩

@[to_additive] protected lemma div_mul_left (h : is_unit b) : b / (a * b) = 1 / a :=
by rw [div_eq_mul_inv, mul_inv_rev, h.mul_inv_cancel_left, one_div]

@[to_additive] protected lemma mul_div_mul_right (h : is_unit c) (a b : α) :
  (a * c) / (b * c) = a / b :=
by simp only [div_eq_mul_inv, mul_inv_rev, mul_assoc, h.mul_inv_cancel_left]

@[to_additive] protected lemma mul_mul_div (a : α) (h : is_unit b) : a * b * (1 / b) = a :=
by simp [h]

end division_monoid

section division_comm_monoid
variables [division_comm_monoid α] {a b c d : α}

@[to_additive] protected lemma div_mul_right (h : is_unit a) (b : α) : a / (a * b) = 1 / b :=
by rw [mul_comm, h.div_mul_left]

@[to_additive] protected lemma mul_div_cancel_left (h : is_unit a) (b : α) : a * b / a = b :=
by rw [mul_comm, h.mul_div_cancel]

@[to_additive] protected lemma mul_div_cancel' (h : is_unit a) (b : α) : a * (b / a) = b :=
by rw [mul_comm, h.div_mul_cancel]

@[to_additive] protected lemma mul_div_mul_left (h : is_unit c) (a b : α) :
  (c * a) / (c * b) = a / b :=
by rw [mul_comm c, mul_comm c, h.mul_div_mul_right]

@[to_additive] protected lemma mul_eq_mul_of_div_eq_div (hb : is_unit b) (hd : is_unit d) (a c : α)
  (h : a / b = c / d) : a * d = c * b :=
by rw [←mul_one a, ←hb.div_self, ←mul_comm_div, h, div_mul_eq_mul_div, hd.div_mul_cancel]

@[to_additive] protected lemma div_eq_div_iff (hb : is_unit b) (hd : is_unit d) :
  a / b = c / d ↔ a * d = c * b :=
by rw [←(hb.mul hd).mul_left_inj, ←mul_assoc, hb.div_mul_cancel, ←mul_assoc, mul_right_comm,
  hd.div_mul_cancel]

@[to_additive] protected lemma div_div_cancel (h : is_unit a) : a / (a / b) = b :=
by rw [div_div_eq_mul_div, h.mul_div_cancel_left]

@[to_additive] protected lemma div_div_cancel_left (h : is_unit a) :
  a / b / a = b⁻¹ :=
by rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm, h.mul_inv_cancel, one_mul]

end division_comm_monoid
end is_unit

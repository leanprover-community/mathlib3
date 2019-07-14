/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johan Commelin

Various multiplicative and additive structures.
-/
import algebra.group.to_additive algebra.group.basic algebra.group.hom

universes u v
variable {α : Type u}

@[to_additive with_zero]
def with_one (α) := option α

namespace with_one

@[to_additive with_zero.monad]
instance : monad with_one := option.monad

@[to_additive with_zero.has_zero]
instance : has_one (with_one α) := ⟨none⟩

@[to_additive with_zero.has_coe_t]
instance : has_coe_t α (with_one α) := ⟨some⟩

@[simp, to_additive with_zero.zero_ne_coe]
lemma one_ne_coe {a : α} : (1 : with_one α) ≠ a :=
λ h, option.no_confusion h

@[simp, to_additive with_zero.coe_ne_zero]
lemma coe_ne_one {a : α} : (a : with_one α) ≠ (1 : with_one α) :=
λ h, option.no_confusion h

@[to_additive with_zero.ne_zero_iff_exists]
lemma ne_one_iff_exists : ∀ {x : with_one α}, x ≠ 1 ↔ ∃ (a : α), x = a
| 1       := ⟨λ h, false.elim $ h rfl, by { rintros ⟨a,ha⟩ h, simpa using h }⟩
| (a : α) := ⟨λ h, ⟨a, rfl⟩, λ h, with_one.coe_ne_one⟩

@[to_additive with_zero.coe_inj]
lemma coe_inj {a b : α} : (a : with_one α) = b ↔ a = b :=
option.some_inj

@[elab_as_eliminator, to_additive with_zero.cases_on]
protected lemma cases_on {P : with_one α → Prop} :
  ∀ (x : with_one α), P 1 → (∀ a : α, P a) → P x :=
option.cases_on

attribute [to_additive with_zero.has_zero.equations._eqn_1] with_one.has_one.equations._eqn_1

@[to_additive with_zero.has_add]
instance [has_mul α] : has_mul (with_one α) :=
{ mul := option.lift_or_get (*) }

@[simp, to_additive with_zero.add_coe]
lemma mul_coe [has_mul α] (a b : α) : (a : with_one α) * b = (a * b : α) := rfl

@[to_additive with_zero.coe_is_add_hom]
instance coe_is_mul_hom [has_mul α] : is_mul_hom (coe : α → with_one α) := { map_mul := λ a b, rfl }

attribute [to_additive with_zero.has_add.equations._eqn_1] with_one.has_mul.equations._eqn_1

instance [semigroup α] : monoid (with_one α) :=
{ mul_assoc := (option.lift_or_get_assoc _).1,
  one_mul   := (option.lift_or_get_is_left_id _).1,
  mul_one   := (option.lift_or_get_is_right_id _).1,
  ..with_one.has_one,
  ..with_one.has_mul }

attribute [to_additive with_zero.add_monoid._proof_1] with_one.monoid._proof_1
attribute [to_additive with_zero.add_monoid._proof_2] with_one.monoid._proof_2
attribute [to_additive with_zero.add_monoid._proof_3] with_one.monoid._proof_3
attribute [to_additive with_zero.add_monoid] with_one.monoid
attribute [to_additive with_zero.add_monoid.equations._eqn_1] with_one.monoid.equations._eqn_1

instance [comm_semigroup α] : comm_monoid (with_one α) :=
{ mul_comm := (option.lift_or_get_comm _).1,
  ..with_one.monoid }

attribute [to_additive with_zero.add_comm_monoid._proof_1] with_one.comm_monoid._proof_1
attribute [to_additive with_zero.add_comm_monoid._proof_2] with_one.comm_monoid._proof_2
attribute [to_additive with_zero.add_comm_monoid._proof_3] with_one.comm_monoid._proof_3
attribute [to_additive with_zero.add_comm_monoid._proof_4] with_one.comm_monoid._proof_4
attribute [to_additive with_zero.add_comm_monoid] with_one.comm_monoid

end with_one

namespace with_zero

instance [one : has_one α] : has_one (with_zero α) :=
{ ..one }

instance [has_one α] : zero_ne_one_class (with_zero α) :=
{ zero_ne_one := λ h, option.no_confusion h,
  ..with_zero.has_zero,
  ..with_zero.has_one }

lemma coe_one [has_one α] : ((1 : α) : with_zero α) = 1 := rfl

instance [has_mul α] : mul_zero_class (with_zero α) :=
{ mul       := λ o₁ o₂, o₁.bind (λ a, o₂.map (λ b, a * b)),
  zero_mul  := λ a, rfl,
  mul_zero  := λ a, by cases a; refl,
  ..with_zero.has_zero }

@[simp] lemma mul_coe [has_mul α] (a b : α) :
  (a : with_zero α) * b = (a * b : α) := rfl

instance [semigroup α] : semigroup (with_zero α) :=
{ mul_assoc := λ a b c, match a, b, c with
    | none,   _,      _      := rfl
    | some a, none,   _      := rfl
    | some a, some b, none   := rfl
    | some a, some b, some c := congr_arg some (mul_assoc _ _ _)
    end,
  ..with_zero.mul_zero_class }

instance [comm_semigroup α] : comm_semigroup (with_zero α) :=
{ mul_comm := λ a b, match a, b with
    | none,   _      := (mul_zero _).symm
    | some a, none   := rfl
    | some a, some b := congr_arg some (mul_comm _ _)
    end,
  ..with_zero.semigroup }

instance [monoid α] : monoid (with_zero α) :=
{ one_mul := λ a, match a with
    | none   := rfl
    | some a := congr_arg some $ one_mul _
    end,
  mul_one := λ a, match a with
    | none   := rfl
    | some a := congr_arg some $ mul_one _
    end,
  ..with_zero.zero_ne_one_class,
  ..with_zero.semigroup }

instance [comm_monoid α] : comm_monoid (with_zero α) :=
{ ..with_zero.monoid, ..with_zero.comm_semigroup }

definition inv [has_inv α] (x : with_zero α) : with_zero α :=
do a ← x, return a⁻¹

instance [has_inv α] : has_inv (with_zero α) := ⟨with_zero.inv⟩

@[simp] lemma inv_coe [has_inv α] (a : α) :
  (a : with_zero α)⁻¹ = (a⁻¹ : α) := rfl
@[simp] lemma inv_zero [has_inv α] :
  (0 : with_zero α)⁻¹ = 0 := rfl

section group
variables [group α]

@[simp] lemma inv_one : (1 : with_zero α)⁻¹ = 1 :=
show ((1⁻¹ : α) : with_zero α) = 1, by simp [coe_one]

definition with_zero.div (x y : with_zero α) : with_zero α :=
x * y⁻¹

instance : has_div (with_zero α) := ⟨with_zero.div⟩

@[simp] lemma zero_div (a : with_zero α) : 0 / a = 0 := rfl
@[simp] lemma div_zero (a : with_zero α) : a / 0 = 0 := by change a * _ = _; simp

lemma div_coe (a b : α) : (a : with_zero α) / b = (a * b⁻¹ : α) := rfl

lemma one_div (x : with_zero α) : 1 / x = x⁻¹ := one_mul _

@[simp] lemma div_one : ∀ (x : with_zero α), x / 1 = x
| 0       := rfl
| (a : α) := show _ * _ = _, by simp

@[simp] lemma mul_right_inv : ∀  (x : with_zero α) (h : x ≠ 0), x * x⁻¹ = 1
| 0       h := false.elim $ h rfl
| (a : α) h := by simp [coe_one]

@[simp] lemma mul_left_inv : ∀  (x : with_zero α) (h : x ≠ 0), x⁻¹ * x = 1
| 0       h := false.elim $ h rfl
| (a : α) h := by simp [coe_one]

@[simp] lemma mul_inv_rev : ∀ (x y : with_zero α), (x * y)⁻¹ = y⁻¹ * x⁻¹
| 0       0       := rfl
| 0       (b : α) := rfl
| (a : α) 0       := rfl
| (a : α) (b : α) := by simp

@[simp] lemma mul_div_cancel {a b : with_zero α} (hb : b ≠ 0) : a * b / b = a :=
show _ * _ * _ = _, by simp [mul_assoc, hb]

@[simp] lemma div_mul_cancel {a b : with_zero α} (hb : b ≠ 0) : a / b * b = a :=
show _ * _ * _ = _, by simp [mul_assoc, hb]

lemma div_eq_iff_mul_eq {a b c : with_zero α} (hb : b ≠ 0) : a / b = c ↔ c * b = a :=
by split; intro h; simp [h.symm, hb]

end group

section comm_group
variables [comm_group α] {a b c d : with_zero α}

lemma div_eq_div (hb : b ≠ 0) (hd : d ≠ 0) : a / b = c / d ↔ a * d = b * c :=
begin
  rw ne_zero_iff_exists at hb hd,
  rcases hb with ⟨b, rfl⟩,
  rcases hd with ⟨d, rfl⟩,
  induction a using with_zero.cases_on;
  induction c using with_zero.cases_on,
  { refl },
  { simp [div_coe] },
  { simp [div_coe] },
  erw [with_zero.coe_inj, with_zero.coe_inj],
  show a * b⁻¹ = c * d⁻¹ ↔ a * d = b * c,
  split; intro H,
  { rw mul_inv_eq_iff_eq_mul at H,
    rw [H, mul_right_comm, inv_mul_cancel_right, mul_comm] },
  { rw [mul_inv_eq_iff_eq_mul, mul_right_comm, mul_comm c, ← H, mul_inv_cancel_right] }
end

end comm_group

end with_zero

/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Chris Hughes, Michael Howes
-/
import algebra.group.semiconj
import algebra.group_with_zero.basic
import algebra.hom.aut
import algebra.hom.group

/-!
# Conjugacy of group elements

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

See also `mul_aut.conj` and `quandle.conj`.
-/

universes u v
variables {α : Type u} {β : Type v}

section monoid

variables [monoid α] [monoid β]

/-- We say that `a` is conjugate to `b` if for some unit `c` we have `c * a * c⁻¹ = b`. -/
def is_conj (a b : α) := ∃ c : αˣ, semiconj_by ↑c a b

@[refl] lemma is_conj.refl (a : α) : is_conj a a :=
⟨1, semiconj_by.one_left a⟩

@[symm] lemma is_conj.symm {a b : α} : is_conj a b → is_conj b a
| ⟨c, hc⟩ := ⟨c⁻¹, hc.units_inv_symm_left⟩

lemma is_conj_comm {g h : α} : is_conj g h ↔ is_conj h g :=
⟨is_conj.symm, is_conj.symm⟩

@[trans] lemma is_conj.trans {a b c : α} : is_conj a b → is_conj b c → is_conj a c
| ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩ := ⟨c₂ * c₁, hc₂.mul_left hc₁⟩

@[simp] lemma is_conj_iff_eq {α : Type*} [comm_monoid α] {a b : α} : is_conj a b ↔ a = b :=
⟨λ ⟨c, hc⟩, begin
  rw [semiconj_by, mul_comm, ← units.mul_inv_eq_iff_eq_mul, mul_assoc, c.mul_inv, mul_one] at hc,
  exact hc,
end, λ h, by rw h⟩

protected lemma monoid_hom.map_is_conj (f : α →* β) {a b : α} : is_conj a b → is_conj (f a) (f b)
| ⟨c, hc⟩ := ⟨units.map f c, by rw [units.coe_map, semiconj_by, ← f.map_mul, hc.eq, f.map_mul]⟩

end monoid

section cancel_monoid

variables [cancel_monoid α]
-- These lemmas hold for `right_cancel_monoid` with the current proofs, but for the sake of
-- not duplicating code (these lemmas also hold for `left_cancel_monoids`) we leave these
-- not generalised.

@[simp] lemma is_conj_one_right {a : α} : is_conj 1 a  ↔ a = 1 :=
⟨λ ⟨c, hc⟩, mul_right_cancel (hc.symm.trans ((mul_one _).trans (one_mul _).symm)), λ h, by rw [h]⟩

@[simp] lemma is_conj_one_left {a : α} : is_conj a 1 ↔ a = 1 :=
calc is_conj a 1 ↔ is_conj 1 a : ⟨is_conj.symm, is_conj.symm⟩
... ↔ a = 1 : is_conj_one_right

end cancel_monoid

section group

variables [group α]

@[simp] lemma is_conj_iff {a b : α} :
  is_conj a b ↔ ∃ c : α, c * a * c⁻¹ = b :=
⟨λ ⟨c, hc⟩, ⟨c, mul_inv_eq_iff_eq_mul.2 hc⟩, λ ⟨c, hc⟩,
  ⟨⟨c, c⁻¹, mul_inv_self c, inv_mul_self c⟩, mul_inv_eq_iff_eq_mul.1 hc⟩⟩

@[simp] lemma conj_inv {a b : α} : (b * a * b⁻¹)⁻¹ = b * a⁻¹ * b⁻¹ :=
((mul_aut.conj b).map_inv a).symm

@[simp] lemma conj_mul {a b c : α} : (b * a * b⁻¹) * (b * c * b⁻¹) = b * (a * c) * b⁻¹ :=
((mul_aut.conj b).map_mul a c).symm

@[simp] lemma conj_pow {i : ℕ} {a b : α} : (a * b * a⁻¹) ^ i = a * (b ^ i) * a⁻¹ :=
begin
  induction i with i hi,
  { simp },
  { simp [pow_succ, hi] }
end

@[simp] lemma conj_zpow {i : ℤ} {a b : α} : (a * b * a⁻¹) ^ i = a * (b ^ i) * a⁻¹ :=
begin
  induction i,
  { simp },
  { simp [zpow_neg_succ_of_nat, conj_pow] }
end

lemma conj_injective {x : α} : function.injective (λ (g : α), x * g * x⁻¹) :=
(mul_aut.conj x).injective

end group

@[simp] lemma is_conj_iff₀ [group_with_zero α] {a b : α} :
  is_conj a b ↔ ∃ c : α, c ≠ 0 ∧ c * a * c⁻¹ = b :=
⟨λ ⟨c, hc⟩, ⟨c, begin
    rw [← units.coe_inv, units.mul_inv_eq_iff_eq_mul],
    exact ⟨c.ne_zero, hc⟩,
  end⟩, λ ⟨c, c0, hc⟩,
  ⟨units.mk0 c c0, begin
    rw [semiconj_by, ← units.mul_inv_eq_iff_eq_mul, units.coe_inv, units.coe_mk0],
    exact hc
  end⟩⟩

namespace is_conj
/- This small quotient API is largely copied from the API of `associates`;
where possible, try to keep them in sync -/

/-- The setoid of the relation `is_conj` iff there is a unit `u` such that `u * x = y * u` -/
protected def setoid (α : Type*) [monoid α] : setoid α :=
{ r := is_conj, iseqv := ⟨is_conj.refl, λa b, is_conj.symm, λa b c, is_conj.trans⟩ }

end is_conj

local attribute [instance, priority 100] is_conj.setoid

/-- The quotient type of conjugacy classes of a group. -/
def conj_classes (α : Type*) [monoid α] : Type* :=
quotient (is_conj.setoid α)

namespace conj_classes

section monoid
variables [monoid α] [monoid β]

/-- The canonical quotient map from a monoid `α` into the `conj_classes` of `α` -/
protected def mk {α : Type*} [monoid α] (a : α) : conj_classes α :=
⟦a⟧

instance : inhabited (conj_classes α) := ⟨⟦1⟧⟩

theorem mk_eq_mk_iff_is_conj {a b : α} :
  conj_classes.mk a = conj_classes.mk b ↔ is_conj a b :=
iff.intro quotient.exact quot.sound

theorem quotient_mk_eq_mk (a : α) : ⟦ a ⟧ = conj_classes.mk a := rfl

theorem quot_mk_eq_mk (a : α) : quot.mk setoid.r a = conj_classes.mk a := rfl

theorem forall_is_conj {p : conj_classes α → Prop} :
  (∀a, p a) ↔ (∀a, p (conj_classes.mk a)) :=
iff.intro
  (assume h a, h _)
  (assume h a, quotient.induction_on a h)

theorem mk_surjective : function.surjective (@conj_classes.mk α _) :=
forall_is_conj.2 (λ a, ⟨a, rfl⟩)

instance : has_one (conj_classes α) := ⟨⟦ 1 ⟧⟩

theorem one_eq_mk_one : (1 : conj_classes α) = conj_classes.mk 1 := rfl

lemma exists_rep (a : conj_classes α) : ∃ a0 : α, conj_classes.mk a0 = a :=
quot.exists_rep a

/-- A `monoid_hom` maps conjugacy classes of one group to conjugacy classes of another. -/
def map (f : α →* β) : conj_classes α → conj_classes β :=
quotient.lift (conj_classes.mk ∘ f) (λ a b ab, mk_eq_mk_iff_is_conj.2 (f.map_is_conj ab))

lemma map_surjective {f : α →* β} (hf : function.surjective f) :
  function.surjective (conj_classes.map f) :=
begin
  intros b,
  obtain ⟨b, rfl⟩ := conj_classes.mk_surjective b,
  obtain ⟨a, rfl⟩ := hf b,
  exact ⟨conj_classes.mk a, rfl⟩,
end

/--
Certain instances trigger further searches when they are considered as candidate instances;
these instances should be assigned a priority lower than the default of 1000 (for example, 900).

The conditions for this rule are as follows:
 * a class `C` has instances `instT : C T` and `instT' : C T'`
 * types `T` and `T'` are both specializations of another type `S`
 * the parameters supplied to `S` to produce `T` are not (fully) determined by `instT`,
   instead they have to be found by instance search
If those conditions hold, the instance `instT` should be assigned lower priority.

For example, suppose the search for an instance of `decidable_eq (multiset α)` tries the
candidate instance `con.quotient.decidable_eq (c : con M) : decidable_eq c.quotient`.
Since `multiset` and `con.quotient` are both quotient types, unification will check
that the relations `list.perm` and `c.to_setoid.r` unify. However, `c.to_setoid` depends on
a `has_mul M` instance, so this unification triggers a search for `has_mul (list α)`;
this will traverse all subclasses of `has_mul` before failing.
On the other hand, the search for an instance of `decidable_eq (con.quotient c)` for `c : con M`
can quickly reject the candidate instance `multiset.has_decidable_eq` because the type of
`list.perm : list ?m_1 → list ?m_1 → Prop` does not unify with `M → M → Prop`.
Therefore, we should assign `con.quotient.decidable_eq` a lower priority because it fails slowly.
(In terms of the rules above, `C := decidable_eq`, `T := con.quotient`,
`instT := con.quotient.decidable_eq`, `T' := multiset`, `instT' := multiset.has_decidable_eq`,
and `S := quot`.)

If the type involved is a free variable (rather than an instantiation of some type `S`),
the instance priority should be even lower, see Note [lower instance priority].
-/
library_note "slow-failing instance priority"

@[priority 900] -- see Note [slow-failing instance priority]
instance [decidable_rel (is_conj : α → α → Prop)] : decidable_eq (conj_classes α) :=
quotient.decidable_eq

end monoid

section comm_monoid
variable [comm_monoid α]

lemma mk_injective : function.injective (@conj_classes.mk α _) :=
λ _ _, (mk_eq_mk_iff_is_conj.trans is_conj_iff_eq).1

lemma mk_bijective : function.bijective (@conj_classes.mk α _) :=
⟨mk_injective, mk_surjective⟩

/-- The bijection between a `comm_group` and its `conj_classes`. -/
def mk_equiv : α ≃ conj_classes α :=
⟨conj_classes.mk, quotient.lift id (λ (a : α) b, is_conj_iff_eq.1), quotient.lift_mk _ _,
  begin
    rw [function.right_inverse, function.left_inverse, forall_is_conj],
    intro x,
    rw [← quotient_mk_eq_mk, ← quotient_mk_eq_mk, quotient.lift_mk, id.def],
  end⟩

end comm_monoid
end conj_classes

section monoid

variables [monoid α]

/-- Given an element `a`, `conjugates a` is the set of conjugates. -/
def conjugates_of (a : α) : set α := {b | is_conj a b}

lemma mem_conjugates_of_self {a : α} : a ∈ conjugates_of a := is_conj.refl _

lemma is_conj.conjugates_of_eq {a b : α} (ab : is_conj a b) :
  conjugates_of a = conjugates_of b :=
set.ext (λ g, ⟨λ ag, (ab.symm).trans ag, λ bg, ab.trans bg⟩)

lemma is_conj_iff_conjugates_of_eq {a b : α} :
  is_conj a b ↔ conjugates_of a = conjugates_of b :=
⟨is_conj.conjugates_of_eq, λ h, begin
  have ha := mem_conjugates_of_self,
  rwa ← h at ha,
end⟩

end monoid

namespace conj_classes

variables [monoid α]

local attribute [instance] is_conj.setoid

/-- Given a conjugacy class `a`, `carrier a` is the set it represents. -/
def carrier : conj_classes α → set α :=
quotient.lift conjugates_of (λ (a : α) b ab, is_conj.conjugates_of_eq ab)

lemma mem_carrier_mk {a : α} : a ∈ carrier (conj_classes.mk a) := is_conj.refl _

lemma mem_carrier_iff_mk_eq {a : α} {b : conj_classes α} :
  a ∈ carrier b ↔ conj_classes.mk a = b :=
begin
  revert b,
  rw forall_is_conj,
  intro b,
  rw [carrier, eq_comm, mk_eq_mk_iff_is_conj, ← quotient_mk_eq_mk, quotient.lift_mk],
  refl,
end

lemma carrier_eq_preimage_mk {a : conj_classes α} :
  a.carrier = conj_classes.mk ⁻¹' {a} :=
set.ext (λ x, mem_carrier_iff_mk_eq)

end conj_classes

assert_not_exists multiset

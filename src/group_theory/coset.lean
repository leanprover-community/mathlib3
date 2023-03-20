/-
Copyright (c) 2018 Mitchell Rowett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Rowett, Scott Morrison
-/

import algebra.quotient
import data.fintype.prod
import group_theory.group_action.basic
import group_theory.subgroup.mul_opposite
import tactic.group

/-!
# Cosets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file develops the basic theory of left and right cosets.

## Main definitions

* `left_coset a s`: the left coset `a * s` for an element `a : α` and a subset `s ⊆ α`, for an
  `add_group` this is `left_add_coset a s`.
* `right_coset s a`: the right coset `s * a` for an element `a : α` and a subset `s ⊆ α`, for an
  `add_group` this is `right_add_coset s a`.
* `quotient_group.quotient s`: the quotient type representing the left cosets with respect to a
  subgroup `s`, for an `add_group` this is `quotient_add_group.quotient s`.
* `quotient_group.mk`: the canonical map from `α` to `α/s` for a subgroup `s` of `α`, for an
  `add_group` this is `quotient_add_group.mk`.
* `subgroup.left_coset_equiv_subgroup`: the natural bijection between a left coset and the subgroup,
  for an `add_group` this is `add_subgroup.left_coset_equiv_add_subgroup`.

## Notation

* `a *l s`: for `left_coset a s`.
* `a +l s`: for `left_add_coset a s`.
* `s *r a`: for `right_coset s a`.
* `s +r a`: for `right_add_coset s a`.

* `G ⧸ H` is the quotient of the (additive) group `G` by the (additive) subgroup `H`
-/

open set function

variable {α : Type*}

/-- The left coset `a * s` for an element `a : α` and a subset `s : set α` -/
@[to_additive left_add_coset "The left coset `a+s` for an element `a : α`
and a subset `s : set α`"]
def left_coset [has_mul α] (a : α) (s : set α) : set α := (λ x, a * x) '' s

/-- The right coset `s * a` for an element `a : α` and a subset `s : set α` -/
@[to_additive right_add_coset "The right coset `s+a` for an element `a : α`
and a subset `s : set α`"]
def right_coset [has_mul α] (s : set α) (a : α) : set α := (λ x, x * a) '' s

localized "infix (name := left_coset) ` *l `:70 := left_coset" in coset
localized "infix (name := left_add_coset) ` +l `:70 := left_add_coset" in coset
localized "infix (name := right_coset) ` *r `:70 := right_coset" in coset
localized "infix (name := right_add_coset) ` +r `:70 := right_add_coset" in coset

section coset_mul
variable [has_mul α]

@[to_additive mem_left_add_coset]
lemma mem_left_coset {s : set α} {x : α} (a : α) (hxS : x ∈ s) : a * x ∈ a *l s :=
mem_image_of_mem (λ b : α, a * b) hxS

@[to_additive mem_right_add_coset]
lemma mem_right_coset {s : set α} {x : α} (a : α) (hxS : x ∈ s) : x * a ∈ s *r a :=
mem_image_of_mem (λ b : α, b * a) hxS

/-- Equality of two left cosets `a * s` and `b * s`. -/
@[to_additive left_add_coset_equivalence "Equality of two left cosets `a + s` and `b + s`."]
def left_coset_equivalence (s : set α) (a b : α) := a *l s = b *l s

@[to_additive left_add_coset_equivalence_rel]
lemma left_coset_equivalence_rel (s : set α) : equivalence (left_coset_equivalence s) :=
mk_equivalence (left_coset_equivalence s) (λ a, rfl) (λ a b, eq.symm) (λ a b c, eq.trans)

/-- Equality of two right cosets `s * a` and `s * b`. -/
@[to_additive right_add_coset_equivalence "Equality of two right cosets `s + a` and `s + b`."]
def right_coset_equivalence (s : set α) (a b : α) := s *r a = s *r b

@[to_additive right_add_coset_equivalence_rel]
lemma right_coset_equivalence_rel (s : set α) : equivalence (right_coset_equivalence s) :=
mk_equivalence (right_coset_equivalence s) (λ a, rfl) (λ a b, eq.symm) (λ a b c, eq.trans)

end coset_mul

section coset_semigroup
variable [semigroup α]

@[simp, to_additive left_add_coset_assoc] lemma left_coset_assoc (s : set α) (a b : α) :
  a *l (b *l s) = (a * b) *l s :=
by simp [left_coset, right_coset, (image_comp _ _ _).symm, function.comp, mul_assoc]

@[simp, to_additive right_add_coset_assoc] lemma right_coset_assoc (s : set α) (a b : α) :
  s *r a *r b = s *r (a * b) :=
by simp [left_coset, right_coset, (image_comp _ _ _).symm, function.comp, mul_assoc]

@[to_additive left_add_coset_right_add_coset]
lemma left_coset_right_coset (s : set α) (a b : α) : a *l s *r b = a *l (s *r b) :=
by simp [left_coset, right_coset, (image_comp _ _ _).symm, function.comp, mul_assoc]

end coset_semigroup

section coset_monoid
variables [monoid α] (s : set α)

@[simp, to_additive zero_left_add_coset] lemma one_left_coset : 1 *l s = s :=
set.ext $ by simp [left_coset]

@[simp, to_additive right_add_coset_zero] lemma right_coset_one : s *r 1 = s :=
set.ext $ by simp [right_coset]

end coset_monoid

section coset_submonoid
open submonoid
variables [monoid α] (s : submonoid α)

@[to_additive mem_own_left_add_coset]
lemma mem_own_left_coset (a : α) : a ∈ a *l s :=
suffices a * 1 ∈ a *l s, by simpa,
mem_left_coset a (one_mem s : 1 ∈ s)

@[to_additive mem_own_right_add_coset]
lemma mem_own_right_coset (a : α) : a ∈ (s : set α) *r a :=
suffices 1 * a ∈ (s : set α) *r a, by simpa,
mem_right_coset a (one_mem s : 1 ∈ s)

@[to_additive mem_left_add_coset_left_add_coset]
lemma mem_left_coset_left_coset {a : α} (ha : a *l s = s) : a ∈ s :=
by rw [←set_like.mem_coe, ←ha]; exact mem_own_left_coset s a

@[to_additive mem_right_add_coset_right_add_coset]
lemma mem_right_coset_right_coset {a : α} (ha : (s : set α) *r a = s) : a ∈ s :=
by rw [←set_like.mem_coe, ←ha]; exact mem_own_right_coset s a

end coset_submonoid

section coset_group
variables [group α] {s : set α} {x : α}

@[to_additive mem_left_add_coset_iff]
lemma mem_left_coset_iff (a : α) : x ∈ a *l s ↔ a⁻¹ * x ∈ s :=
iff.intro
  (assume ⟨b, hb, eq⟩, by simp [eq.symm, hb])
  (assume h, ⟨a⁻¹ * x, h, by simp⟩)

@[to_additive mem_right_add_coset_iff]
lemma mem_right_coset_iff (a : α) : x ∈ s *r a ↔ x * a⁻¹ ∈ s :=
iff.intro
  (assume ⟨b, hb, eq⟩, by simp [eq.symm, hb])
  (assume h, ⟨x * a⁻¹, h, by simp⟩)

end coset_group

section coset_subgroup
open subgroup

variables [group α] (s : subgroup α)

@[to_additive left_add_coset_mem_left_add_coset]
lemma left_coset_mem_left_coset {a : α} (ha : a ∈ s) : a *l s = s :=
set.ext $ by simp [mem_left_coset_iff, mul_mem_cancel_left (s.inv_mem ha)]

@[to_additive right_add_coset_mem_right_add_coset]
lemma right_coset_mem_right_coset {a : α} (ha : a ∈ s) : (s : set α) *r a = s :=
set.ext $ assume b, by simp [mem_right_coset_iff, mul_mem_cancel_right (s.inv_mem ha)]

@[to_additive] lemma orbit_subgroup_eq_right_coset (a : α) : mul_action.orbit s a = s *r a :=
set.ext (λ b, ⟨λ ⟨c, d⟩, ⟨c, c.2, d⟩, λ ⟨c, d, e⟩, ⟨⟨c, d⟩, e⟩⟩)

@[to_additive] lemma orbit_subgroup_eq_self_of_mem {a : α} (ha : a ∈ s) :
  mul_action.orbit s a = s :=
(orbit_subgroup_eq_right_coset s a).trans (right_coset_mem_right_coset s ha)

@[to_additive] lemma orbit_subgroup_one_eq_self : mul_action.orbit s (1 : α) = s :=
orbit_subgroup_eq_self_of_mem s s.one_mem

@[to_additive eq_add_cosets_of_normal]
theorem eq_cosets_of_normal (N : s.normal) (g : α) : g *l s = s *r g :=
set.ext $ assume a, by simp [mem_left_coset_iff, mem_right_coset_iff]; rw [N.mem_comm_iff]

@[to_additive normal_of_eq_add_cosets]
theorem normal_of_eq_cosets (h : ∀ g : α, g *l s = s *r g) : s.normal :=
⟨assume a ha g, show g * a * g⁻¹ ∈ (s : set α),
  by rw [← mem_right_coset_iff, ← h]; exact mem_left_coset g ha⟩

@[to_additive normal_iff_eq_add_cosets]
theorem normal_iff_eq_cosets : s.normal ↔ ∀ g : α, g *l s = s *r g :=
⟨@eq_cosets_of_normal _ _ s, normal_of_eq_cosets s⟩

@[to_additive left_add_coset_eq_iff]
lemma left_coset_eq_iff {x y : α} : left_coset x s = left_coset y s ↔ x⁻¹ * y ∈ s :=
begin
  rw set.ext_iff,
  simp_rw [mem_left_coset_iff, set_like.mem_coe],
  split,
  { intro h, apply (h y).mpr, rw mul_left_inv, exact s.one_mem },
  { intros h z, rw ←mul_inv_cancel_right x⁻¹ y, rw mul_assoc, exact s.mul_mem_cancel_left h },
end

@[to_additive right_add_coset_eq_iff]
lemma right_coset_eq_iff {x y : α} : right_coset ↑s x = right_coset s y ↔ y * x⁻¹ ∈ s :=
begin
  rw set.ext_iff,
  simp_rw [mem_right_coset_iff, set_like.mem_coe],
  split,
  { intro h, apply (h y).mpr, rw mul_right_inv, exact s.one_mem },
  { intros h z, rw ←inv_mul_cancel_left y x⁻¹, rw ←mul_assoc, exact s.mul_mem_cancel_right h },
end

end coset_subgroup

run_cmd to_additive.map_namespace `quotient_group `quotient_add_group

namespace quotient_group

variables [group α] (s : subgroup α)

/-- The equivalence relation corresponding to the partition of a group by left cosets
of a subgroup.-/
@[to_additive "The equivalence relation corresponding to the partition of a group by left cosets
of a subgroup."]
def left_rel : setoid α := mul_action.orbit_rel s.opposite α

variables {s}

@[to_additive]
lemma left_rel_apply {x y : α} : @setoid.r _ (left_rel s) x y ↔ (x⁻¹ * y ∈ s) :=
calc (∃ a : s.opposite, y * mul_opposite.unop a = x)
    ↔ ∃ a : s, y * a = x : s.opposite_equiv.symm.exists_congr_left
... ↔ ∃ a : s, x⁻¹ * y = a⁻¹ : by simp only [inv_mul_eq_iff_eq_mul, eq_mul_inv_iff_mul_eq]
... ↔ x⁻¹ * y ∈ s : by simp [set_like.exists]

variables (s)

@[to_additive]
lemma left_rel_eq : @setoid.r _ (left_rel s) = λ x y, x⁻¹ * y ∈ s :=
funext₂ $ by { simp only [eq_iff_iff], apply left_rel_apply }

lemma left_rel_r_eq_left_coset_equivalence :
  @setoid.r _ (quotient_group.left_rel s) = left_coset_equivalence s :=
by { ext, rw left_rel_eq, exact (left_coset_eq_iff s).symm }

@[to_additive]
instance left_rel_decidable [decidable_pred (∈ s)] :
  decidable_rel (left_rel s).r :=
λ x y, by { rw left_rel_eq, exact ‹decidable_pred (∈ s)› _ }

/-- `α ⧸ s` is the quotient type representing the left cosets of `s`.
  If `s` is a normal subgroup, `α ⧸ s` is a group -/
@[to_additive "`α ⧸ s` is the quotient type representing the left cosets of `s`.  If `s` is a
normal subgroup, `α ⧸ s` is a group"]
instance : has_quotient α (subgroup α) := ⟨λ s, quotient (left_rel s)⟩

/-- The equivalence relation corresponding to the partition of a group by right cosets of a
subgroup. -/
@[to_additive "The equivalence relation corresponding to the partition of a group by right cosets of
a subgroup."]
def right_rel : setoid α := mul_action.orbit_rel s α

variables {s}

@[to_additive]
lemma right_rel_apply {x y : α} : @setoid.r _ (right_rel s) x y ↔ (y * x⁻¹ ∈ s) :=
calc (∃ a : s, (a:α) * y = x)
    ↔ ∃ a : s, y * x⁻¹ = a⁻¹ : by simp only [mul_inv_eq_iff_eq_mul, eq_inv_mul_iff_mul_eq]
... ↔ y * x⁻¹ ∈ s : by simp [set_like.exists]

variables (s)

@[to_additive]
lemma right_rel_eq : @setoid.r _ (right_rel s) = λ x y, y * x⁻¹ ∈ s :=
funext₂ $ by { simp only [eq_iff_iff], apply right_rel_apply }

lemma right_rel_r_eq_right_coset_equivalence :
  @setoid.r _ (quotient_group.right_rel s) = right_coset_equivalence s :=
by { ext, rw right_rel_eq, exact (right_coset_eq_iff s).symm }

@[to_additive]
instance right_rel_decidable [decidable_pred (∈ s)] :
  decidable_rel (right_rel s).r :=
λ x y, by { rw right_rel_eq, exact ‹decidable_pred (∈ s)› _ }

/-- Right cosets are in bijection with left cosets. -/
@[to_additive "Right cosets are in bijection with left cosets."]
def quotient_right_rel_equiv_quotient_left_rel : quotient (quotient_group.right_rel s) ≃ α ⧸ s :=
{ to_fun := quotient.map' (λ g, g⁻¹) (λ a b, by { rw [left_rel_apply, right_rel_apply],
      exact λ h, (congr_arg (∈ s) (by group)).mp (s.inv_mem h) }),
  inv_fun := quotient.map' (λ g, g⁻¹) (λ a b, by { rw [left_rel_apply, right_rel_apply],
      exact λ h, (congr_arg (∈ s) (by group)).mp (s.inv_mem h) }),
  left_inv := λ g, quotient.induction_on' g (λ g, quotient.sound' (by
  { simp only [inv_inv],
    exact quotient.exact' rfl })),
  right_inv := λ g, quotient.induction_on' g (λ g, quotient.sound' (by
  { simp only [inv_inv],
    exact quotient.exact' rfl })) }

@[to_additive] instance fintype_quotient_right_rel [fintype (α ⧸ s)] :
  fintype (quotient (quotient_group.right_rel s)) :=
fintype.of_equiv (α ⧸ s) (quotient_group.quotient_right_rel_equiv_quotient_left_rel s).symm

@[to_additive] lemma card_quotient_right_rel [fintype (α ⧸ s)] :
  fintype.card (quotient (quotient_group.right_rel s)) = fintype.card (α ⧸ s) :=
fintype.of_equiv_card (quotient_group.quotient_right_rel_equiv_quotient_left_rel s).symm

end quotient_group

namespace quotient_group

variables [group α] {s : subgroup α}

@[to_additive]
instance fintype [fintype α] (s : subgroup α) [decidable_rel (left_rel s).r] :
  fintype (α ⧸ s) :=
quotient.fintype (left_rel s)

/-- The canonical map from a group `α` to the quotient `α ⧸ s`. -/
@[to_additive "The canonical map from an `add_group` `α` to the quotient `α ⧸ s`."]
abbreviation mk (a : α) : α ⧸ s :=
quotient.mk' a

@[to_additive]
lemma mk_surjective : function.surjective $ @mk _ _ s := quotient.surjective_quotient_mk'

@[elab_as_eliminator, to_additive]
lemma induction_on {C : α ⧸ s → Prop} (x : α ⧸ s)
  (H : ∀ z, C (quotient_group.mk z)) : C x :=
quotient.induction_on' x H

@[to_additive]
instance : has_coe_t α (α ⧸ s) := ⟨mk⟩ -- note [use has_coe_t]

@[elab_as_eliminator, to_additive]
lemma induction_on' {C : α ⧸ s → Prop} (x : α ⧸ s)
  (H : ∀ z : α, C z) : C x :=
quotient.induction_on' x H

@[simp, to_additive]
lemma quotient_lift_on_coe {β} (f : α → β) (h) (x : α) :
  quotient.lift_on' (x : α ⧸ s) f h = f x := rfl

@[to_additive] lemma forall_coe {C : α ⧸ s → Prop} : (∀ x : α ⧸ s, C x) ↔ ∀ x : α, C x :=
mk_surjective.forall

@[to_additive] lemma exists_coe {C : α ⧸ s → Prop} : (∃ x : α ⧸ s, C x) ↔ ∃ x : α, C x :=
mk_surjective.exists

@[to_additive]
instance (s : subgroup α) : inhabited (α ⧸ s) :=
⟨((1 : α) : α ⧸ s)⟩

@[to_additive quotient_add_group.eq]
protected lemma eq {a b : α} : (a : α ⧸ s) = b ↔ a⁻¹ * b ∈ s :=
calc _ ↔ @setoid.r _ (left_rel s) a b : quotient.eq'
... ↔ _ : by rw left_rel_apply

@[to_additive quotient_add_group.eq']
lemma eq' {a b : α} : (mk a : α ⧸ s) = mk b ↔ a⁻¹ * b ∈ s :=
quotient_group.eq

@[simp, to_additive quotient_add_group.out_eq']
lemma out_eq' (a : α ⧸ s) : mk a.out' = a :=
quotient.out_eq' a

variables (s)

/- It can be useful to write `obtain ⟨h, H⟩ := mk_out'_eq_mul ...`, and then `rw [H]` or
  `simp_rw [H]` or `simp only [H]`. In order for `simp_rw` and `simp only` to work, this lemma is
  stated in terms of an arbitrary `h : s`, rathern that the specific `h = g⁻¹ * (mk g).out'`. -/
@[to_additive quotient_add_group.mk_out'_eq_mul]
lemma mk_out'_eq_mul (g : α) : ∃ h : s, (mk g : α ⧸ s).out' = g * h :=
⟨⟨g⁻¹ * (mk g).out', eq'.mp (mk g).out_eq'.symm⟩, by rw [set_like.coe_mk, mul_inv_cancel_left]⟩

variables {s} {a b : α}

@[simp, to_additive quotient_add_group.mk_add_of_mem]
lemma mk_mul_of_mem (a : α) (hb : b ∈ s) : (mk (a * b) : α ⧸ s) = mk a :=
by rwa [eq', mul_inv_rev, inv_mul_cancel_right, s.inv_mem_iff]

@[to_additive]
lemma eq_class_eq_left_coset (s : subgroup α) (g : α) :
  {x : α | (x : α ⧸ s) = g} = left_coset g s :=
set.ext $ λ z,
  by rw [mem_left_coset_iff, set.mem_set_of_eq, eq_comm, quotient_group.eq, set_like.mem_coe]

@[to_additive]
lemma preimage_image_coe (N : subgroup α) (s : set α) :
  coe ⁻¹' ((coe : α → α ⧸ N) '' s) = ⋃ x : N, (λ y : α, y * x) ⁻¹' s :=
begin
  ext x,
  simp only [quotient_group.eq, set_like.exists, exists_prop, set.mem_preimage, set.mem_Union,
    set.mem_image, set_like.coe_mk, ← eq_inv_mul_iff_mul_eq],
  exact ⟨λ ⟨y, hs, hN⟩, ⟨_, N.inv_mem hN, by simpa using hs⟩,
         λ ⟨z, hz, hxz⟩, ⟨x*z, hxz, by simpa using hz⟩⟩,
end

end quotient_group

namespace subgroup
open quotient_group
variables [group α] {s : subgroup α}

/-- The natural bijection between a left coset `g * s` and `s`. -/
@[to_additive "The natural bijection between the cosets `g + s` and `s`."]
def left_coset_equiv_subgroup (g : α) : left_coset g s ≃ s :=
⟨λ x, ⟨g⁻¹ * x.1, (mem_left_coset_iff _).1 x.2⟩,
 λ x, ⟨g * x.1, x.1, x.2, rfl⟩,
 λ ⟨x, hx⟩, subtype.eq $ by simp,
 λ ⟨g, hg⟩, subtype.eq $ by simp⟩

/-- The natural bijection between a right coset `s * g` and `s`. -/
@[to_additive "The natural bijection between the cosets `s + g` and `s`."]
def right_coset_equiv_subgroup (g : α) : right_coset ↑s g ≃ s :=
⟨λ x, ⟨x.1 * g⁻¹, (mem_right_coset_iff _).1 x.2⟩,
 λ x, ⟨x.1 * g, x.1, x.2, rfl⟩,
 λ ⟨x, hx⟩, subtype.eq $ by simp,
 λ ⟨g, hg⟩, subtype.eq $ by simp⟩

/-- A (non-canonical) bijection between a group `α` and the product `(α/s) × s` -/
@[to_additive "A (non-canonical) bijection between an add_group `α` and the product `(α/s) × s`"]
noncomputable def group_equiv_quotient_times_subgroup :
  α ≃ (α ⧸ s) × s :=
calc α ≃ Σ L : α ⧸ s, {x : α // (x : α ⧸ s) = L} :
  (equiv.sigma_fiber_equiv quotient_group.mk).symm
    ... ≃ Σ L : α ⧸ s, left_coset (quotient.out' L) s :
  equiv.sigma_congr_right (λ L,
    begin
      rw ← eq_class_eq_left_coset,
      show _root_.subtype (λ x : α, quotient.mk' x = L) ≃
        _root_.subtype (λ x : α, quotient.mk' x = quotient.mk' _),
      simp [-quotient.eq'],
    end)
    ... ≃ Σ L : α ⧸ s, s :
  equiv.sigma_congr_right (λ L, left_coset_equiv_subgroup _)
    ... ≃ (α ⧸ s) × s :
  equiv.sigma_equiv_prod _ _

variables {t : subgroup α}

/-- If two subgroups `M` and `N` of `G` are equal, their quotients are in bijection. -/
@[to_additive "If two subgroups `M` and `N` of `G` are equal, their quotients are in bijection."]
def quotient_equiv_of_eq (h : s = t) : α ⧸ s ≃ α ⧸ t :=
{ to_fun := quotient.map' id (λ a b h', h ▸ h'),
  inv_fun := quotient.map' id (λ a b h', h.symm ▸ h'),
  left_inv := λ q, induction_on' q (λ g, rfl),
  right_inv := λ q, induction_on' q (λ g, rfl) }

lemma quotient_equiv_of_eq_mk (h : s = t) (a : α) :
  quotient_equiv_of_eq h (quotient_group.mk a) = (quotient_group.mk a) :=
rfl

/-- If `H ≤ K`, then `G/H ≃ G/K × K/H` constructively, using the provided right inverse
of the quotient map `G → G/K`. The classical version is `quotient_equiv_prod_of_le`. -/
@[to_additive "If `H ≤ K`, then `G/H ≃ G/K × K/H` constructively, using the provided right inverse
of the quotient map `G → G/K`. The classical version is `quotient_equiv_prod_of_le`.", simps]
def quotient_equiv_prod_of_le' (h_le : s ≤ t)
  (f : α ⧸ t → α) (hf : function.right_inverse f quotient_group.mk) :
  α ⧸ s ≃ (α ⧸ t) × (t ⧸ s.subgroup_of t) :=
{ to_fun := λ a, ⟨a.map' id (λ b c h, left_rel_apply.mpr (h_le (left_rel_apply.mp h))),
    a.map' (λ g : α, ⟨(f (quotient.mk' g))⁻¹ * g, left_rel_apply.mp (quotient.exact' (hf g))⟩)
    (λ b c h, by
    { rw left_rel_apply,
      change ((f b)⁻¹ * b)⁻¹ * ((f c)⁻¹ * c) ∈ s,
      have key : f b = f c :=
        congr_arg f (quotient.sound' (left_rel_apply.mpr (h_le (left_rel_apply.mp h)))),
      rwa [key, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left, ← left_rel_apply] })⟩,
  inv_fun := λ a, a.2.map' (λ b, f a.1 * b) (λ b c h, by
  { rw left_rel_apply at ⊢ h,
    change (f a.1 * b)⁻¹ * (f a.1 * c) ∈ s,
    rwa [mul_inv_rev, mul_assoc, inv_mul_cancel_left] }),
  left_inv := by
  { refine quotient.ind' (λ a, _),
    simp_rw [quotient.map'_mk', id.def, set_like.coe_mk, mul_inv_cancel_left] },
  right_inv := by
  { refine prod.rec _,
    refine quotient.ind' (λ a, _),
    refine quotient.ind' (λ b, _),
    have key : quotient.mk' (f (quotient.mk' a) * b) = quotient.mk' a :=
      (quotient_group.mk_mul_of_mem (f a) b.2).trans (hf a),
    simp_rw [quotient.map'_mk', id.def, key, inv_mul_cancel_left, subtype.coe_eta] } }

/-- If `H ≤ K`, then `G/H ≃ G/K × K/H` nonconstructively.
The constructive version is `quotient_equiv_prod_of_le'`. -/
@[to_additive "If `H ≤ K`, then `G/H ≃ G/K × K/H` nonconstructively.
The constructive version is `quotient_equiv_prod_of_le'`.", simps]
noncomputable def quotient_equiv_prod_of_le (h_le : s ≤ t) :
  α ⧸ s ≃ (α ⧸ t) × (t ⧸ s.subgroup_of t) :=
quotient_equiv_prod_of_le' h_le quotient.out' quotient.out_eq'

/-- If `s ≤ t`, then there is an embedding `s ⧸ H.subgroup_of s ↪ t ⧸ H.subgroup_of t`. -/
@[to_additive "If `s ≤ t`, then there is an embedding
  `s ⧸ H.add_subgroup_of s ↪ t ⧸ H.add_subgroup_of t`."]
def quotient_subgroup_of_embedding_of_le (H : subgroup α) (h : s ≤ t) :
  s ⧸ H.subgroup_of s ↪ t ⧸ H.subgroup_of t :=
{ to_fun := quotient.map' (inclusion h) (λ a b, by { simp_rw left_rel_eq, exact id }),
  inj' := quotient.ind₂' $ by { intros a b h, simpa only [quotient.map'_mk', eq'] using h } }

@[simp, to_additive]
lemma quotient_subgroup_of_embedding_of_le_apply_mk (H : subgroup α) (h : s ≤ t) (g : s) :
  quotient_subgroup_of_embedding_of_le H h (quotient_group.mk g) =
    quotient_group.mk (inclusion h g) :=
rfl

/-- If `s ≤ t`, then there is a map `H ⧸ s.subgroup_of H → H ⧸ t.subgroup_of H`. -/
@[to_additive "If `s ≤ t`, then there is an map
  `H ⧸ s.add_subgroup_of H → H ⧸ t.add_subgroup_of H`."]
def quotient_subgroup_of_map_of_le (H : subgroup α) (h : s ≤ t) :
  H ⧸ s.subgroup_of H → H ⧸ t.subgroup_of H :=
quotient.map' id $ λ a b, by { simp_rw [left_rel_eq], apply h }

@[simp, to_additive]
lemma quotient_subgroup_of_map_of_le_apply_mk (H : subgroup α) (h : s ≤ t) (g : H) :
  quotient_subgroup_of_map_of_le H h (quotient_group.mk g) = quotient_group.mk g :=
rfl

/-- If `s ≤ t`, then there is a map `α ⧸ s → α ⧸ t`. -/
@[to_additive "If `s ≤ t`, then there is an map `α ⧸ s → α ⧸ t`."]
def quotient_map_of_le (h : s ≤ t) : α ⧸ s → α ⧸ t :=
quotient.map' id $ λ a b, by { simp_rw [left_rel_eq], apply h }

@[simp, to_additive]
lemma quotient_map_of_le_apply_mk (h : s ≤ t) (g : α) :
  quotient_map_of_le h (quotient_group.mk g) = quotient_group.mk g :=
rfl

/-- The natural embedding `H ⧸ (⨅ i, f i).subgroup_of H ↪ Π i, H ⧸ (f i).subgroup_of H`. -/
@[to_additive "The natural embedding
  `H ⧸ (⨅ i, f i).add_subgroup_of H) ↪ Π i, H ⧸ (f i).add_subgroup_of H`.", simps]
def quotient_infi_subgroup_of_embedding {ι : Type*} (f : ι → subgroup α) (H : subgroup α) :
  H ⧸ (⨅ i, f i).subgroup_of H ↪ Π i, H ⧸ (f i).subgroup_of H :=
{ to_fun := λ q i, quotient_subgroup_of_map_of_le H (infi_le f i) q,
  inj' := quotient.ind₂' $ by simp_rw [funext_iff, quotient_subgroup_of_map_of_le_apply_mk,
    eq', mem_subgroup_of, mem_infi, imp_self, forall_const] }

@[simp, to_additive] lemma quotient_infi_subgroup_of_embedding_apply_mk
  {ι : Type*} (f : ι → subgroup α) (H : subgroup α) (g : H) (i : ι) :
  quotient_infi_subgroup_of_embedding f H (quotient_group.mk g) i = quotient_group.mk g :=
rfl

/-- The natural embedding `α ⧸ (⨅ i, f i) ↪ Π i, α ⧸ f i`. -/
@[to_additive "The natural embedding `α ⧸ (⨅ i, f i) ↪ Π i, α ⧸ f i`.", simps]
def quotient_infi_embedding {ι : Type*} (f : ι → subgroup α) : α ⧸ (⨅ i, f i) ↪ Π i, α ⧸ f i :=
{ to_fun := λ q i, quotient_map_of_le (infi_le f i) q,
  inj' := quotient.ind₂' $ by simp_rw [funext_iff, quotient_map_of_le_apply_mk,
    eq', mem_infi, imp_self, forall_const] }

@[simp, to_additive] lemma quotient_infi_embedding_apply_mk
  {ι : Type*} (f : ι → subgroup α) (g : α) (i : ι) :
  quotient_infi_embedding f (quotient_group.mk g) i = quotient_group.mk g :=
rfl

@[to_additive] lemma card_eq_card_quotient_mul_card_subgroup
  [fintype α] (s : subgroup α) [fintype s] [decidable_pred (λ a, a ∈ s)] :
  fintype.card α = fintype.card (α ⧸ s) * fintype.card s :=
by rw ← fintype.card_prod;
  exact fintype.card_congr (subgroup.group_equiv_quotient_times_subgroup)

/-- **Lagrange's Theorem**: The order of a subgroup divides the order of its ambient group. -/
@[to_additive "**Lagrange's Theorem**: The order of an additive subgroup divides the order of its
ambient group."]
lemma card_subgroup_dvd_card [fintype α] (s : subgroup α) [fintype s] :
  fintype.card s ∣ fintype.card α :=
by classical; simp [card_eq_card_quotient_mul_card_subgroup s, @dvd_mul_left ℕ]

@[to_additive] lemma card_quotient_dvd_card [fintype α] (s : subgroup α) [decidable_pred (∈ s)] :
  fintype.card (α ⧸ s) ∣ fintype.card α :=
by simp [card_eq_card_quotient_mul_card_subgroup s, @dvd_mul_right ℕ]

open fintype

variables {H : Type*} [group H]

@[to_additive] lemma card_dvd_of_injective [fintype α] [fintype H] (f : α →* H)
  (hf : function.injective f) : card α ∣ card H :=
by classical;
calc card α = card (f.range : subgroup H) : card_congr (equiv.of_injective f hf)
...∣ card H : card_subgroup_dvd_card _

@[to_additive] lemma card_dvd_of_le {H K : subgroup α} [fintype H] [fintype K] (hHK : H ≤ K) :
  card H ∣ card K :=
card_dvd_of_injective (inclusion hHK) (inclusion_injective hHK)

@[to_additive] lemma card_comap_dvd_of_injective (K : subgroup H) [fintype K]
  (f : α →* H) [fintype (K.comap f)] (hf : function.injective f) :
  fintype.card (K.comap f) ∣ fintype.card K :=
by haveI : fintype ((K.comap f).map f) :=
  fintype.of_equiv _ (equiv_map_of_injective _ _ hf).to_equiv;
calc fintype.card (K.comap f) = fintype.card ((K.comap f).map f) :
       fintype.card_congr (equiv_map_of_injective _ _ hf).to_equiv
... ∣ fintype.card K : card_dvd_of_le (map_comap_le _ _)

end subgroup

namespace quotient_group

variables [group α]

/-- If `s` is a subgroup of the group `α`, and `t` is a subset of `α ⧸ s`, then there is a
(typically non-canonical) bijection between the preimage of `t` in `α` and the product `s × t`. -/
@[to_additive "If `s` is a subgroup of the additive group `α`, and `t` is a subset of `α ⧸ s`, then
there is a (typically non-canonical) bijection between the preimage of `t` in `α` and the product
`s × t`."]
noncomputable def preimage_mk_equiv_subgroup_times_set (s : subgroup α) (t : set (α ⧸ s)) :
  quotient_group.mk ⁻¹' t ≃ s × t :=
{ to_fun := λ a, ⟨⟨(quotient.out' (quotient_group.mk a))⁻¹ * a,
    left_rel_apply.mp (@quotient.exact' _ (left_rel s) _ _ $ (quotient.out_eq' _))⟩,
      ⟨quotient_group.mk a, a.2⟩⟩,
  inv_fun := λ a, ⟨quotient.out' a.2.1 * a.1.1, show quotient_group.mk _ ∈ t,
    by { rw [mk_mul_of_mem _ a.1.2, out_eq'], exact a.2.2 }⟩,
  left_inv := λ ⟨a, ha⟩, subtype.eq $ show _ * _ = a, by simp,
  right_inv := λ ⟨⟨a, ha⟩, ⟨x, hx⟩⟩, by ext; simp [ha] }

end quotient_group

/--
We use the class `has_coe_t` instead of `has_coe` if the first argument is a variable,
or if the second argument is a variable not occurring in the first.
Using `has_coe` would cause looping of type-class inference. See
<https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/remove.20all.20instances.20with.20variable.20domain>
-/
library_note "use has_coe_t"

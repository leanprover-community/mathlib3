/-
Copyright (c) 2018 Mitchell Rowett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Rowett, Scott Morrison
-/
import group_theory.subgroup data.equiv.basic data.quot
open set function

variable {α : Type*}

@[to_additive left_add_coset]
def left_coset [has_mul α] (a : α) (s : set α) : set α := (λ x, a * x) '' s
attribute [to_additive left_add_coset.equations._eqn_1] left_coset.equations._eqn_1

@[to_additive right_add_coset]
def right_coset [has_mul α] (s : set α) (a : α) : set α := (λ x, x * a) '' s
attribute [to_additive right_add_coset.equations._eqn_1] right_coset.equations._eqn_1

local infix ` *l `:70 := left_coset
local infix ` +l `:70 := left_add_coset
local infix ` *r `:70 := right_coset
local infix ` +r `:70 := right_add_coset

section coset_mul
variable [has_mul α]

@[to_additive mem_left_add_coset]
lemma mem_left_coset {s : set α} {x : α} (a : α) (hxS : x ∈ s) : a * x ∈ a *l s :=
mem_image_of_mem (λ b : α, a * b) hxS

@[to_additive mem_right_add_coset]
lemma mem_right_coset {s : set α} {x : α} (a : α) (hxS : x ∈ s) : x * a ∈ s *r a :=
mem_image_of_mem (λ b : α, b * a) hxS

@[to_additive left_add_coset_equiv]
def left_coset_equiv (s : set α) (a b : α) := a *l s = b *l s

@[to_additive left_add_coset_equiv_rel]
lemma left_coset_equiv_rel (s : set α) : equivalence (left_coset_equiv s) :=
mk_equivalence (left_coset_equiv s) (λ a, rfl) (λ a b, eq.symm) (λ a b c, eq.trans)

end coset_mul

section coset_semigroup
variable [semigroup α]

@[simp] lemma left_coset_assoc (s : set α) (a b : α) : a *l (b *l s) = (a * b) *l s :=
by simp [left_coset, right_coset, (image_comp _ _ _).symm, function.comp, mul_assoc]
attribute [to_additive left_add_coset_assoc] left_coset_assoc

@[simp] lemma right_coset_assoc (s : set α) (a b : α) : s *r a *r b = s *r (a * b) :=
by simp [left_coset, right_coset, (image_comp _ _ _).symm, function.comp, mul_assoc]
attribute [to_additive right_add_coset_assoc] right_coset_assoc

@[to_additive left_add_coset_right_add_coset]
lemma left_coset_right_coset (s : set α) (a b : α) : a *l s *r b = a *l (s *r b) :=
by simp [left_coset, right_coset, (image_comp _ _ _).symm, function.comp, mul_assoc]

end coset_semigroup

section coset_monoid
variables [monoid α] (s : set α)

@[simp] lemma one_left_coset : 1 *l s = s :=
set.ext $ by simp [left_coset]
attribute [to_additive zero_left_add_coset] one_left_coset

@[simp] lemma right_coset_one : s *r 1 = s :=
set.ext $ by simp [right_coset]
attribute [to_additive right_add_coset_zero] right_coset_one

end coset_monoid

section coset_submonoid
open is_submonoid
variables [monoid α] (s : set α) [is_submonoid s]

@[to_additive mem_own_left_add_coset]
lemma mem_own_left_coset (a : α) : a ∈ a *l s :=
suffices a * 1 ∈ a *l s, by simpa,
mem_left_coset a (one_mem s)

@[to_additive mem_own_right_add_coset]
lemma mem_own_right_coset (a : α) : a ∈ s *r a :=
suffices 1 * a ∈ s *r a, by simpa,
mem_right_coset a (one_mem s)

@[to_additive mem_left_add_coset_left_add_coset]
lemma mem_left_coset_left_coset {a : α} (ha : a *l s = s) : a ∈ s :=
by rw [←ha]; exact mem_own_left_coset s a

@[to_additive mem_right_add_coset_right_add_coset]
lemma mem_right_coset_right_coset {a : α} (ha : s *r a = s) : a ∈ s :=
by rw [←ha]; exact mem_own_right_coset s a

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
open is_submonoid
open is_subgroup
variables [group α] (s : set α) [is_subgroup s]

@[to_additive left_add_coset_mem_left_add_coset]
lemma left_coset_mem_left_coset {a : α} (ha : a ∈ s) : a *l s = s :=
set.ext $ by simp [mem_left_coset_iff, mul_mem_cancel_right s (inv_mem ha)]

@[to_additive right_add_coset_mem_right_add_coset]
lemma right_coset_mem_right_coset {a : α} (ha : a ∈ s) : s *r a = s :=
set.ext $ assume b, by simp [mem_right_coset_iff, mul_mem_cancel_left s (inv_mem ha)]

@[to_additive normal_of_eq_add_cosets]
theorem normal_of_eq_cosets [normal_subgroup s] (g : α) : g *l s = s *r g :=
set.ext $ assume a, by simp [mem_left_coset_iff, mem_right_coset_iff]; rw [mem_norm_comm_iff]

@[to_additive eq_add_cosets_of_normal]
theorem eq_cosets_of_normal (h : ∀ g, g *l s = s *r g) : normal_subgroup s :=
⟨assume a ha g, show g * a * g⁻¹ ∈ s,
  by rw [← mem_right_coset_iff, ← h]; exact mem_left_coset g ha⟩

@[to_additive normal_iff_eq_add_cosets]
theorem normal_iff_eq_cosets : normal_subgroup s ↔ ∀ g, g *l s = s *r g :=
⟨@normal_of_eq_cosets _ _ s _, eq_cosets_of_normal s⟩

end coset_subgroup

namespace quotient_group

def left_rel [group α] (s : set α) [is_subgroup s] : setoid α :=
⟨λ x y, x⁻¹ * y ∈ s,
  assume x, by simp [is_submonoid.one_mem],
  assume x y hxy,
  have (x⁻¹ * y)⁻¹ ∈ s, from is_subgroup.inv_mem hxy,
  by simpa using this,
  assume x y z hxy hyz,
  have x⁻¹ * y * (y⁻¹ * z) ∈ s, from is_submonoid.mul_mem hxy hyz,
  by simpa [mul_assoc] using this⟩
attribute [to_additive quotient_add_group.left_rel._proof_1] left_rel._proof_1
attribute [to_additive quotient_add_group.left_rel] left_rel
attribute [to_additive quotient_add_group.left_rel.equations._eqn_1] left_rel.equations._eqn_1

/-- `quotient s` is the quotient type representing the left cosets of `s`.
  If `s` is a normal subgroup, `quotient s` is a group -/
def quotient [group α] (s : set α) [is_subgroup s] : Type* := quotient (left_rel s)
attribute [to_additive quotient_add_group.quotient] quotient
attribute [to_additive quotient_add_group.quotient.equations._eqn_1] quotient.equations._eqn_1

variables [group α] {s : set α} [is_subgroup s]

@[to_additive quotient_add_group.mk]
def mk (a : α) : quotient s :=
quotient.mk' a
attribute [to_additive quotient_add_group.mk.equations._eqn_1] mk.equations._eqn_1

@[elab_as_eliminator, to_additive quotient_add_group.induction_on]
lemma induction_on {C : quotient s → Prop} (x : quotient s)
  (H : ∀ z, C (quotient_group.mk z)) : C x :=
quotient.induction_on' x H
attribute [elab_as_eliminator] quotient_add_group.induction_on

@[to_additive quotient_add_group.has_coe]
instance : has_coe α (quotient s) := ⟨mk⟩
attribute [to_additive quotient_add_group.has_coe.equations._eqn_1] has_coe.equations._eqn_1

@[elab_as_eliminator, to_additive quotient_add_group.induction_on']
lemma induction_on' {C : quotient s → Prop} (x : quotient s)
  (H : ∀ z : α, C z) : C x :=
quotient.induction_on' x H
attribute [elab_as_eliminator] quotient_add_group.induction_on'

@[to_additive quotient_add_group.inhabited]
instance [group α] (s : set α) [is_subgroup s] : inhabited (quotient s) :=
⟨((1 : α) : quotient s)⟩
attribute [to_additive quotient_add_group.inhabited.equations._eqn_1] inhabited.equations._eqn_1

@[to_additive quotient_add_group.eq]
protected lemma eq {a b : α} : (a : quotient s) = b ↔ a⁻¹ * b ∈ s :=
quotient.eq'

@[to_additive quotient_add_group.eq_class_eq_left_coset]
lemma eq_class_eq_left_coset [group α] (s : set α) [is_subgroup s] (g : α) :
  {x : α | (x : quotient s) = g} = left_coset g s :=
set.ext $ λ z, by rw [mem_left_coset_iff, set.mem_set_of_eq, eq_comm, quotient_group.eq]

end quotient_group

namespace is_subgroup
open quotient_group
variables [group α] {s : set α}

def left_coset_equiv_subgroup (g : α) : left_coset g s ≃ s :=
⟨λ x, ⟨g⁻¹ * x.1, (mem_left_coset_iff _).1 x.2⟩,
 λ x, ⟨g * x.1, x.1, x.2, rfl⟩,
 λ ⟨x, hx⟩, subtype.eq $ by simp,
 λ ⟨g, hg⟩, subtype.eq $ by simp⟩
attribute [to_additive is_add_subgroup.left_add_coset_equiv_subgroup._match_2] left_coset_equiv_subgroup._match_2
attribute [to_additive is_add_subgroup.left_add_coset_equiv_subgroup._match_1] left_coset_equiv_subgroup._match_1
attribute [to_additive is_add_subgroup.left_add_coset_equiv_subgroup._proof_4] left_coset_equiv_subgroup._proof_4
attribute [to_additive is_add_subgroup.left_add_coset_equiv_subgroup._proof_3] left_coset_equiv_subgroup._proof_3
attribute [to_additive is_add_subgroup.left_add_coset_equiv_subgroup._proof_2] left_coset_equiv_subgroup._proof_2
attribute [to_additive is_add_subgroup.left_add_coset_equiv_subgroup._proof_1] left_coset_equiv_subgroup._proof_1
attribute [to_additive is_add_subgroup.left_add_coset_equiv_subgroup] left_coset_equiv_subgroup
attribute [to_additive is_add_subgroup.left_add_coset_equiv_subgroup.equations._eqn_1] left_coset_equiv_subgroup.equations._eqn_1
attribute [to_additive is_add_subgroup.left_add_coset_equiv_subgroup._match_1.equations._eqn_1] left_coset_equiv_subgroup._match_1.equations._eqn_1
attribute [to_additive is_add_subgroup.left_add_coset_equiv_subgroup._match_2.equations._eqn_1] left_coset_equiv_subgroup._match_2.equations._eqn_1

noncomputable def group_equiv_quotient_times_subgroup (hs : is_subgroup s) :
  α ≃ (quotient s × s) :=
calc α ≃ Σ L : quotient s, {x : α // (x : quotient s)= L} :
  equiv.equiv_fib quotient_group.mk
    ... ≃ Σ L : quotient s, left_coset (quotient.out' L) s :
  equiv.sigma_congr_right (λ L,
    begin rw ← eq_class_eq_left_coset,
      show {x // quotient.mk' x = L} ≃ {x : α // quotient.mk' x = quotient.mk' _},
      simp [-quotient.eq']
    end)
    ... ≃ Σ L : quotient s, s :
  equiv.sigma_congr_right (λ L, left_coset_equiv_subgroup _)
    ... ≃ (quotient s × s) :
  equiv.sigma_equiv_prod _ _
attribute [to_additive is_add_subgroup.add_group_equiv_quotient_times_subgroup._proof_2] group_equiv_quotient_times_subgroup._proof_2
attribute [to_additive is_add_subgroup.add_group_equiv_quotient_times_subgroup._proof_1] group_equiv_quotient_times_subgroup._proof_1
attribute [to_additive is_add_subgroup.add_group_equiv_quotient_times_subgroup] group_equiv_quotient_times_subgroup
attribute [to_additive is_add_subgroup.add_group_equiv_quotient_times_subgroup.equations._eqn_1] group_equiv_quotient_times_subgroup.equations._eqn_1

end is_subgroup

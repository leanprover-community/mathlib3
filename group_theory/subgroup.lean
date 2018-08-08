/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mitchell Rowett, Scott Morrison
-/
import group_theory.submonoid
open set function

variables {α : Type*} {β : Type*} {s : set α} {a a₁ a₂ b c: α}

section group
variable [group α]

lemma injective_mul {a : α} : injective ((*) a) :=
assume a₁ a₂ h,
have a⁻¹ * a * a₁ = a⁻¹ * a * a₂, by rw [mul_assoc, mul_assoc, h],
by rwa [inv_mul_self, one_mul, one_mul] at this

/-- `s` is a subgroup: a set containing 1 and closed under multiplication and inverse. -/
class is_subgroup [group α] (s : set α) extends is_submonoid s : Prop :=
(inv_mem {a} : a ∈ s → a⁻¹ ∈ s)

instance subtype.group {s : set α} [is_subgroup s] : group s :=
{ inv          := λa, ⟨(a.1)⁻¹, is_subgroup.inv_mem a.2⟩,
  mul_left_inv := assume ⟨a, _⟩, subtype.eq $ mul_left_inv _,
  .. subtype.monoid }

theorem is_subgroup.of_div [group α] (s : set α)
  (one_mem : (1:α) ∈ s) (div_mem : ∀{a b:α}, a ∈ s → b ∈ s → a * b⁻¹ ∈ s):
  is_subgroup s :=
have inv_mem : ∀a, a ∈ s → a⁻¹ ∈ s, from
  assume a ha,
  have 1 * a⁻¹ ∈ s, from div_mem one_mem ha,
  by simpa,
{ inv_mem := inv_mem,
  mul_mem := assume a b ha hb,
    have a * b⁻¹⁻¹ ∈ s, from div_mem ha (inv_mem b hb),
    by simpa,
  one_mem := one_mem }

def gpowers (x : α) : set α := {y | ∃i:ℤ, x^i = y}

instance gpowers.is_subgroup (x : α) : is_subgroup (gpowers x) :=
{ one_mem := ⟨(0:ℤ), by simp⟩,
  mul_mem := assume x₁ x₂ ⟨i₁, h₁⟩ ⟨i₂, h₂⟩, ⟨i₁ + i₂, by simp [gpow_add, *]⟩,
  inv_mem := assume x₀ ⟨i, h⟩, ⟨-i, by simp [h.symm]⟩ }

lemma is_subgroup.gpow_mem {a : α} {s : set α} [is_subgroup s] (h : a ∈ s) : ∀{i:ℤ}, a ^ i ∈ s
| (n : ℕ) := is_submonoid.pow_mem h
| -[1+ n] := is_subgroup.inv_mem (is_submonoid.pow_mem h)

lemma mem_gpowers {a : α} : a ∈ gpowers a :=
⟨1, by simp⟩

end group

namespace is_subgroup
open is_submonoid
variable (s)
variables [group α] [is_subgroup s]

lemma inv_mem_iff : a⁻¹ ∈ s ↔ a ∈ s :=
iff.intro (assume h, have a⁻¹⁻¹ ∈ s, from inv_mem h, by simpa) inv_mem

lemma mul_mem_cancel_left (h : a ∈ s) : b * a ∈ s ↔ b ∈ s :=
iff.intro
  (assume hba,
    have (b * a) * a⁻¹ ∈ s, from mul_mem hba (inv_mem h),
    by simpa)
  (assume hb, mul_mem hb h)

lemma mul_mem_cancel_right (h : a ∈ s) : a * b ∈ s ↔ b ∈ s :=
iff.intro
  (assume hab,
    have a⁻¹ * (a * b) ∈ s, from mul_mem (inv_mem h) hab,
    by simpa)
  (mul_mem h)

end is_subgroup

namespace group
open is_submonoid is_subgroup

variable [group α]

inductive in_closure (s : set α) : α → Prop
| basic {a : α} : a ∈ s → in_closure a
| one : in_closure 1
| inv {a : α} : in_closure a → in_closure a⁻¹
| mul {a b : α} : in_closure a → in_closure b → in_closure (a * b)

/-- `group.closure s` is the subgroup closed over `s`, i.e. the smallest subgroup containg s. -/
def closure (s : set α) : set α := {a | in_closure s a }

lemma mem_closure {a : α} : a ∈ s → a ∈ closure s := in_closure.basic

instance closure.is_subgroup (s : set α) : is_subgroup (closure s) :=
{ one_mem := in_closure.one s, mul_mem := assume a b, in_closure.mul, inv_mem := assume a, in_closure.inv }

theorem subset_closure {s : set α} : s ⊆ closure s :=
assume a, in_closure.basic

theorem closure_subset {s t : set α} [is_subgroup t] (h : s ⊆ t) : closure s ⊆ t :=
assume a ha, by induction ha; simp [h _, *, one_mem, mul_mem, inv_mem_iff]

theorem gpowers_eq_closure {a : α} : gpowers a = closure {a} :=
subset.antisymm
  (assume x h, match x, h with _, ⟨i, rfl⟩ := gpow_mem (mem_closure $ by simp) end)
  (closure_subset $ by  simp [mem_gpowers])

end group

class normal_subgroup [group α] (s : set α) extends is_subgroup s : Prop :=
(normal : ∀ n ∈ s, ∀ g : α, g * n * g⁻¹ ∈ s)

namespace is_subgroup
variable [group α]

-- Normal subgroup properties
lemma mem_norm_comm {a b : α} {s : set α} [normal_subgroup s] (hab : a * b ∈ s) : b * a ∈ s :=
have h : a⁻¹ * (a * b) * a⁻¹⁻¹ ∈ s, from normal_subgroup.normal (a * b) hab a⁻¹,
by simp at h; exact h

lemma mem_norm_comm_iff {a b : α} {s : set α} [normal_subgroup s] : a * b ∈ s ↔ b * a ∈ s :=
iff.intro mem_norm_comm mem_norm_comm

/-- The trivial subgroup -/
def trivial (α : Type*) [group α] : set α := {1}

@[simp] lemma mem_trivial [group α] {g : α} : g ∈ trivial α ↔ g = 1 :=
by simp [trivial]

instance trivial_normal : normal_subgroup (trivial α) :=
by refine {..}; simp [trivial] {contextual := tt}

lemma trivial_eq_closure : trivial α = group.closure ∅ :=
subset.antisymm
  (by simp [set.subset_def, is_submonoid.one_mem])
  (group.closure_subset $ by simp)

instance univ_subgroup : normal_subgroup (@univ α) :=
by refine {..}; simp

def center (α : Type*) [group α] : set α := {z | ∀ g, g * z = z * g}

lemma mem_center {a : α} : a ∈ center α ↔ (∀g, g * a = a * g) :=
iff.refl _

instance center_normal : normal_subgroup (center α) :=
{ one_mem := by simp [center],
  mul_mem := assume a b ha hb g,
    by rw [←mul_assoc, mem_center.2 ha g, mul_assoc, mem_center.2 hb g, ←mul_assoc],
  inv_mem := assume a ha g,
    calc
      g * a⁻¹ = a⁻¹ * (g * a) * a⁻¹ : by simp [ha g]
      ...     = a⁻¹ * g             : by rw [←mul_assoc, mul_assoc]; simp,
  normal := assume n ha g h,
    calc
      h * (g * n * g⁻¹) = h * n           : by simp [ha g, mul_assoc]
      ...               = g * g⁻¹ * n * h : by rw ha h; simp
      ...               = g * n * g⁻¹ * h : by rw [mul_assoc g, ha g⁻¹, ←mul_assoc] }

end is_subgroup

-- Homomorphism subgroups
namespace is_group_hom
open is_submonoid is_subgroup
variables [group α] [group β]

def ker (f : α → β) [is_group_hom f] : set α := preimage f (trivial β)

lemma mem_ker (f : α → β) [is_group_hom f] {x : α} : x ∈ ker f ↔ f x = 1 :=
mem_trivial

lemma one_ker_inv (f : α → β) [is_group_hom f] {a b : α} (h : f (a * b⁻¹) = 1) : f a = f b :=
begin
  rw [mul f, inv f] at h,
  rw [←inv_inv (f b), eq_inv_of_mul_eq_one h]
end

lemma inv_ker_one (f : α → β) [is_group_hom f] {a b : α} (h : f a = f b) : f (a * b⁻¹) = 1 :=
have f a * (f b)⁻¹ = 1, by rw [h, mul_right_inv],
by rwa [←inv f, ←mul f] at this

lemma one_iff_ker_inv (f : α → β) [is_group_hom f] (a b : α) : f a = f b ↔ f (a * b⁻¹) = 1 :=
⟨inv_ker_one f, one_ker_inv f⟩

lemma inv_iff_ker (f : α → β) [w : is_group_hom f] (a b : α) : f a = f b ↔ a * b⁻¹ ∈ ker f :=
by rw [mem_ker]; exact one_iff_ker_inv _ _ _

instance image_subgroup (f : α → β) [is_group_hom f] (s : set α) [is_subgroup s] :
  is_subgroup (f '' s) :=
{ mul_mem := assume a₁ a₂ ⟨b₁, hb₁, eq₁⟩ ⟨b₂, hb₂, eq₂⟩,
             ⟨b₁ * b₂, mul_mem hb₁ hb₂, by simp [eq₁, eq₂, mul f]⟩,
  one_mem := ⟨1, one_mem s, one f⟩,
  inv_mem := assume a ⟨b, hb, eq⟩, ⟨b⁻¹, inv_mem hb, by rw inv f; simp *⟩ }

instance range_subgroup (f : α → β) [is_group_hom f] : is_subgroup (set.range f) :=
@set.image_univ _ _ f ▸ is_group_hom.image_subgroup f set.univ

local attribute [simp] one_mem inv_mem mul_mem normal_subgroup.normal

instance preimage (f : α → β) [is_group_hom f] (s : set β) [is_subgroup s] :
  is_subgroup (f ⁻¹' s) :=
by refine {..}; simp [mul f, one f, inv f, @inv_mem β _ _ s] {contextual:=tt}

instance preimage_normal (f : α → β) [is_group_hom f] (s : set β) [normal_subgroup s] :
  normal_subgroup (f ⁻¹' s) :=
⟨by simp [mul f, inv f] {contextual:=tt}⟩

instance normal_subgroup_ker (f : α → β) [is_group_hom f] : normal_subgroup (ker f) :=
is_group_hom.preimage_normal f (trivial β)

lemma inj_of_trivial_ker (f : α → β) [is_group_hom f] (h : ker f = trivial α) :
  function.injective f :=
begin
  intros a₁ a₂ hfa,
  simp [ext_iff, ker, is_subgroup.trivial] at h,
  have ha : a₁ * a₂⁻¹ = 1, by rw ←h; exact inv_ker_one f hfa,
  rw [eq_inv_of_mul_eq_one ha, inv_inv a₂]
end

lemma trivial_ker_of_inj (f : α → β) [is_group_hom f] (h : function.injective f) :
  ker f = trivial α :=
set.ext $ assume x, iff.intro
  (assume hx,
    suffices f x = f 1, by simpa using h this,
    by simp [one f]; rwa [mem_ker] at hx)
  (by simp [mem_ker, is_group_hom.one f] {contextual := tt})

lemma inj_iff_trivial_ker (f : α → β) [is_group_hom f] :
  function.injective f ↔ ker f = trivial α :=
⟨trivial_ker_of_inj f, inj_of_trivial_ker f⟩

end is_group_hom

/-
Copyright (c) 2019 Michael Howes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Howes, Scott Moririson

-/
import algebra.group
import group_theory.subgroup
import tactic.rewrite

variable {α : Type}
variable [group α]


@[simp] lemma conj_inv {a b : α} : (b * a * b⁻¹)⁻¹ = b * a⁻¹ * b⁻¹ :=
begin
  rw [mul_inv_rev _ b⁻¹, mul_inv_rev b _, inv_inv, mul_assoc],
end

@[simp] lemma conj_mul {a b c : α} : (b * a * b⁻¹) * (b * c * b⁻¹) = b * (a * c) * b⁻¹ :=
begin
  assoc_rw inv_mul_cancel_right,
  repeat {rw mul_assoc},
end

/--The normal closure of a set s is the subgroup closure of all the conjugates of
elements of s. It is the smallest normal subgroup containing s. -/

variables {s : set α}

/-- Given an element a, conjugates a is the set of conjugates. -/
def conjugates (a : α) : set α := {b | is_conj a b}

lemma mem_conjugates_self {a : α} : a ∈ conjugates a := is_conj_refl _

/-- Given a set s, conjugates_of_set s is the set of all conjugates of
the elements of s. -/
def conjugates_of_set (s : set α) : set α := {b | ∃ a ∈ s, is_conj a b}

lemma mem_conjugates_of_set_iff {x ∈ s} : x ∈ conjugates_of_set s ↔ ∃ a ∈ s, is_conj a x :=
  iff.rfl

theorem subset_conjugates_of_set : s ⊆ conjugates_of_set s :=
  λ (x : α) (h : x ∈ s), ⟨x, h, mem_conjugates_self⟩

theorem conjugates_of_set_mono {s t : set α} (h : s ⊆ t) :
  conjugates_of_set s ⊆ conjugates_of_set t :=
  λ a ⟨b, H, w⟩, ⟨b, set.mem_powerset h H, w⟩

theorem conjugates_of_set_subset {s t : set α} [normal_subgroup t] (h : s ⊆ t) :
  conjugates_of_set s ⊆ t :=
  λ a ⟨b, H, c, w⟩,
  begin
    have w' : c * b * c⁻¹ ∈ t := normal_subgroup.normal b (set.mem_powerset h H) c,
    rwa ←w,
  end

open group

/-- The normal closure of a set s is the subgroup closure of all the conjugates of
elements of s. It is the smallest normal subgroup containing s. -/
def normal_closure (s : set α) : set α := closure (conjugates_of_set s)

theorem conjugates_of_set_subset_normal_closure : conjugates_of_set s ⊆ normal_closure s :=
subset_closure

theorem subset_normal_closure : s ⊆ normal_closure s :=
set.subset.trans subset_conjugates_of_set conjugates_of_set_subset_normal_closure

/-- The normal closure of a set is a subgroup. -/
instance normal_closure.is_subgroup (s : set α): is_subgroup (normal_closure s) :=
closure.is_subgroup (conjugates_of_set s)

/-- The set of conjugates of s is closed under conjugation. -/
lemma conj_mem_conjugates_of_set {x c : α}: x ∈ conjugates_of_set s →
    (c * x * c⁻¹ ∈ conjugates_of_set s) :=
    λ ⟨a, H, h⟩, ⟨a , H, is_conj_trans h ⟨c, rfl⟩⟩

/-- The normal closure of s is a normal subgroup. -/
instance normal_closure.is_normal : normal_subgroup (normal_closure s) :=
⟨ λ n h g,
begin
  induction h with x hx x hx ihx x y hx hy ihx ihy,
  {exact (conjugates_of_set_subset_normal_closure (conj_mem_conjugates_of_set hx))},
  {simpa using (normal_closure.is_subgroup s).one_mem},
  {rw ←conj_inv,
   exact (is_subgroup.inv_mem ihx)},
  {rw ←conj_mul,
   exact (is_submonoid.mul_mem ihx ihy)},
end ⟩

/-- The normal closure of s is the smallest normal subgroup containing s. -/
theorem normal_closure_subset {s t : set α} [normal_subgroup t] (h : s ⊆ t) :
  normal_closure s ⊆ t :=
λ a w,
begin
  induction w with x hx x hx ihx x y hx hy ihx ihy,
  {exact (conjugates_of_set_subset h $ hx)},
  {exact is_submonoid.one_mem t},
  {exact is_subgroup.inv_mem ihx},
  {exact is_submonoid.mul_mem ihx ihy}
end

lemma normal_closure_subset_iff {s t : set α} [normal_subgroup t] : s ⊆ t ↔ normal_closure s ⊆ t :=
⟨normal_closure_subset, set.subset.trans (subset_normal_closure)⟩

theorem normal_closure_mono {s t : set α} : s ⊆ t → normal_closure s ⊆ normal_closure t :=
λ h, normal_closure_subset (set.subset.trans h (subset_normal_closure))

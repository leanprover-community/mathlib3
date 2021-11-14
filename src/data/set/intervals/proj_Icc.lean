/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Patrick Massot
-/
import data.set.intervals.basic

/-!
# Projection of a line onto a closed interval

Given a linearly ordered type `α`, in this file we define

* `set.proj_Icc (a b : α) (h : a ≤ b)` to be the map `α → [a, b]` sending `(-∞, a]` to `a`, `[b, ∞)`
  to `b`, and each point `x ∈ [a, b]` to itself;
* `set.Icc_extend {a b : α} (h : a ≤ b) (f : Icc a b → β)` to be the extension of `f` to `α` defined
  as `f ∘ proj_Icc a b h`.

We also prove some trivial properties of these maps.
-/

variables {α β : Type*} [linear_order α]

open function

namespace set

/-- Projection of `α` to the closed interval `[a, b]`. -/
def proj_Icc (a b : α) (h : a ≤ b) (x : α) : Icc a b :=
⟨max a (min b x), le_max_left _ _, max_le h (min_le_left _ _)⟩

variables {a b : α} (h : a ≤ b) {x : α}

lemma proj_Icc_of_le_left (hx : x ≤ a) : proj_Icc a b h x = ⟨a, left_mem_Icc.2 h⟩ :=
by simp [proj_Icc, hx, hx.trans h]

@[simp] lemma proj_Icc_left : proj_Icc a b h a = ⟨a, left_mem_Icc.2 h⟩ :=
proj_Icc_of_le_left h le_rfl

lemma proj_Icc_of_right_le (hx : b ≤ x) : proj_Icc a b h x = ⟨b, right_mem_Icc.2 h⟩ :=
by simp [proj_Icc, hx, h]

@[simp] lemma proj_Icc_right : proj_Icc a b h b = ⟨b, right_mem_Icc.2 h⟩ :=
proj_Icc_of_right_le h le_rfl

lemma proj_Icc_eq_left (h : a < b) : proj_Icc a b h.le x = ⟨a, left_mem_Icc.mpr h.le⟩ ↔ x ≤ a :=
begin
  refine ⟨λ h', _, proj_Icc_of_le_left _⟩,
  simp_rw [subtype.ext_iff_val, proj_Icc, max_eq_left_iff, min_le_iff, h.not_le, false_or] at h',
  exact h'
end

lemma proj_Icc_eq_right (h : a < b) : proj_Icc a b h.le x = ⟨b, right_mem_Icc.mpr h.le⟩ ↔ b ≤ x :=
begin
  refine ⟨λ h', _, proj_Icc_of_right_le _⟩,
  simp_rw [subtype.ext_iff_val, proj_Icc] at h',
  have := ((max_choice _ _).resolve_left (by simp [h.ne', h'])).symm.trans h',
  exact min_eq_left_iff.mp this
end

lemma proj_Icc_of_mem (hx : x ∈ Icc a b) : proj_Icc a b h x = ⟨x, hx⟩ :=
by simp [proj_Icc, hx.1, hx.2]

@[simp] lemma proj_Icc_coe (x : Icc a b) : proj_Icc a b h x = x :=
by { cases x, apply proj_Icc_of_mem }

lemma proj_Icc_surj_on : surj_on (proj_Icc a b h) (Icc a b) univ :=
λ x _, ⟨x, x.2, proj_Icc_coe h x⟩

lemma proj_Icc_surjective : surjective (proj_Icc a b h) :=
λ x, ⟨x, proj_Icc_coe h x⟩

@[simp] lemma range_proj_Icc : range (proj_Icc a b h) = univ :=
(proj_Icc_surjective h).range_eq

lemma monotone_proj_Icc : monotone (proj_Icc a b h) :=
λ x y hxy, max_le_max le_rfl $ min_le_min le_rfl hxy

lemma strict_mono_on_proj_Icc : strict_mono_on (proj_Icc a b h) (Icc a b) :=
λ x hx y hy hxy, by simpa only [proj_Icc_of_mem, hx, hy]

/-- Extend a function `[a, b] → β` to a map `α → β`. -/
def Icc_extend {a b : α} (h : a ≤ b) (f : Icc a b → β) : α → β :=
f ∘ proj_Icc a b h

@[simp] lemma Icc_extend_range (f : Icc a b → β) :
  range (Icc_extend h f) = range f :=
by simp [Icc_extend, range_comp f]

lemma Icc_extend_of_le_left (f : Icc a b → β) (hx : x ≤ a) :
  Icc_extend h f x = f ⟨a, left_mem_Icc.2 h⟩ :=
congr_arg f $ proj_Icc_of_le_left h hx

@[simp] lemma Icc_extend_left (f : Icc a b → β) :
  Icc_extend h f a = f ⟨a, left_mem_Icc.2 h⟩ :=
Icc_extend_of_le_left h f le_rfl

lemma Icc_extend_of_right_le (f : Icc a b → β) (hx : b ≤ x) :
  Icc_extend h f x = f ⟨b, right_mem_Icc.2 h⟩ :=
congr_arg f $ proj_Icc_of_right_le h hx

@[simp] lemma Icc_extend_right (f : Icc a b → β) :
  Icc_extend h f b = f ⟨b, right_mem_Icc.2 h⟩ :=
Icc_extend_of_right_le h f le_rfl

lemma Icc_extend_of_mem (f : Icc a b → β) (hx : x ∈ Icc a b) :
  Icc_extend h f x = f ⟨x, hx⟩ :=
congr_arg f $ proj_Icc_of_mem h hx

@[simp] lemma Icc_extend_coe (f : Icc a b → β) (x : Icc a b) :
  Icc_extend h f x = f x :=
congr_arg f $ proj_Icc_coe h x

end set

open set

variables [preorder β] {a b : α} (h : a ≤ b) {f : Icc a b → β}

lemma monotone.Icc_extend (hf : monotone f) : monotone (Icc_extend h f) :=
hf.comp $ monotone_proj_Icc h

lemma strict_mono.strict_mono_on_Icc_extend (hf : strict_mono f) :
  strict_mono_on (Icc_extend h f) (Icc a b) :=
hf.comp_strict_mono_on (strict_mono_on_proj_Icc h)

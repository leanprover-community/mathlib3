/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Patrick Massot
-/
import data.set.function
import data.set.intervals.basic

/-!
# Projection of a line onto a closed interval

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Given a linearly ordered type `α`, in this file we define

* `set.proj_Ici (a : α)` to be the map `α → [a, ∞[` sending `]-∞, a]` to `a`,
  and each point `x ∈ [a, ∞[` to itself;
* `set.proj_Iic (b : α)` to be the map `α → ]-∞, b[` sending `[b, ∞[` to `b`,
  and each point `x ∈ ]-∞, b]` to itself;
* `set.proj_Icc (a b : α) (h : a ≤ b)` to be the map `α → [a, b]` sending `(-∞, a]` to `a`, `[b, ∞)`
  to `b`, and each point `x ∈ [a, b]` to itself;
* `set.Ici_extend {a : α} (f : Ici a → β)` to be the extension of `f` to `α` defined
  as `f ∘ proj_Ici a`.
* `set.Iic_extend {b : α} (f : Iic b → β)` to be the extension of `f` to `α` defined
  as `f ∘ proj_Iic b`.
* `set.Icc_extend {a b : α} (h : a ≤ b) (f : Icc a b → β)` to be the extension of `f` to `α` defined
  as `f ∘ proj_Icc a b h`.

We also prove some trivial properties of these maps.
-/

variables {α β : Type*} [linear_order α]

open function

namespace set

/-- Projection of `α` to the closed interval `[a, ∞[`. -/
def proj_Ici (a x : α) : Ici a := ⟨max a x, le_max_left _ _⟩

/-- Projection of `α` to the closed interval `]-∞, b]`. -/
def proj_Iic (b x : α) : Iic b := ⟨min b x, min_le_left _ _⟩

/-- Projection of `α` to the closed interval `[a, b]`. -/
def proj_Icc (a b : α) (h : a ≤ b) (x : α) : Icc a b :=
⟨max a (min b x), le_max_left _ _, max_le h (min_le_left _ _)⟩

variables {a b : α} (h : a ≤ b) {x : α}

@[simp, norm_cast] lemma coe_proj_Ici (a x : α) : (proj_Ici a x : α) = max a x := rfl
@[simp, norm_cast] lemma coe_proj_Iic (b x : α) : (proj_Iic b x : α) = min b x := rfl
@[simp, norm_cast] lemma coe_proj_Icc (a b : α) (h : a ≤ b) (x : α) :
  (proj_Icc a b h x : α) = max a (min b x) := rfl

lemma proj_Ici_of_le (hx : x ≤ a) : proj_Ici a x = ⟨a, le_rfl⟩ := subtype.ext $ max_eq_left hx
lemma proj_Iic_of_le (hx : b ≤ x) : proj_Iic b x = ⟨b, le_rfl⟩ := subtype.ext $ min_eq_left hx

lemma proj_Icc_of_le_left (hx : x ≤ a) : proj_Icc a b h x = ⟨a, left_mem_Icc.2 h⟩ :=
by simp [proj_Icc, hx, hx.trans h]

lemma proj_Icc_of_right_le (hx : b ≤ x) : proj_Icc a b h x = ⟨b, right_mem_Icc.2 h⟩ :=
by simp [proj_Icc, hx, h]

@[simp] lemma proj_Ici_self (a : α) : proj_Ici a a = ⟨a, le_rfl⟩ := proj_Ici_of_le le_rfl
@[simp] lemma proj_Iic_self (b : α) : proj_Iic b b = ⟨b, le_rfl⟩ := proj_Iic_of_le le_rfl

@[simp] lemma proj_Icc_left : proj_Icc a b h a = ⟨a, left_mem_Icc.2 h⟩ :=
proj_Icc_of_le_left h le_rfl

@[simp] lemma proj_Icc_right : proj_Icc a b h b = ⟨b, right_mem_Icc.2 h⟩ :=
proj_Icc_of_right_le h le_rfl

lemma proj_Ici_eq_self : proj_Ici a x = ⟨a, le_rfl⟩ ↔ x ≤ a := by simp [subtype.ext_iff]
lemma proj_Iic_eq_self : proj_Iic b x = ⟨b, le_rfl⟩ ↔ b ≤ x := by simp [subtype.ext_iff]

lemma proj_Icc_eq_left (h : a < b) : proj_Icc a b h.le x = ⟨a, left_mem_Icc.mpr h.le⟩ ↔ x ≤ a :=
by simp [subtype.ext_iff, h.not_le]

lemma proj_Icc_eq_right (h : a < b) : proj_Icc a b h.le x = ⟨b, right_mem_Icc.mpr h.le⟩ ↔ b ≤ x :=
by simp [subtype.ext_iff, max_min_distrib_left, h.le, h.not_le]

lemma proj_Ici_of_mem (hx : x ∈ Ici a) : proj_Ici a x = ⟨x, hx⟩ := by simpa [proj_Ici]
lemma proj_Iic_of_mem (hx : x ∈ Iic b) : proj_Iic b x = ⟨x, hx⟩ := by simpa [proj_Iic]
lemma proj_Icc_of_mem (hx : x ∈ Icc a b) : proj_Icc a b h x = ⟨x, hx⟩ :=
by simp [proj_Icc, hx.1, hx.2]

@[simp] lemma proj_Ici_coe (x : Ici a) : proj_Ici a x = x := by { cases x, apply proj_Ici_of_mem }
@[simp] lemma proj_Iic_coe (x : Iic b) : proj_Iic b x = x := by { cases x, apply proj_Iic_of_mem }
@[simp] lemma proj_Icc_coe (x : Icc a b) : proj_Icc a b h x = x :=
by { cases x, apply proj_Icc_of_mem }

lemma proj_Ici_surj_on : surj_on (proj_Ici a) (Ici a) univ := λ x _, ⟨x, x.2, proj_Ici_coe x⟩
lemma proj_Iic_surj_on : surj_on (proj_Iic b) (Iic b) univ := λ x _, ⟨x, x.2, proj_Iic_coe x⟩
lemma proj_Icc_surj_on : surj_on (proj_Icc a b h) (Icc a b) univ :=
λ x _, ⟨x, x.2, proj_Icc_coe h x⟩

lemma proj_Ici_surjective : surjective (proj_Ici a) := λ x, ⟨x, proj_Ici_coe x⟩
lemma proj_Iic_surjective : surjective (proj_Iic b) := λ x, ⟨x, proj_Iic_coe x⟩
lemma proj_Icc_surjective : surjective (proj_Icc a b h) := λ x, ⟨x, proj_Icc_coe h x⟩

@[simp] lemma range_proj_Ici : range (proj_Ici a) = univ := proj_Ici_surjective.range_eq
@[simp] lemma range_proj_Iic : range (proj_Iic a) = univ := proj_Iic_surjective.range_eq
@[simp] lemma range_proj_Icc : range (proj_Icc a b h) = univ := (proj_Icc_surjective h).range_eq

lemma monotone_proj_Ici : monotone (proj_Ici a) := λ x y, max_le_max le_rfl
lemma monotone_proj_Iic : monotone (proj_Iic a) := λ x y, min_le_min le_rfl
lemma monotone_proj_Icc : monotone (proj_Icc a b h) :=
λ x y hxy, max_le_max le_rfl $ min_le_min le_rfl hxy

lemma strict_mono_on_proj_Ici : strict_mono_on (proj_Ici a) (Ici a) :=
λ x hx y hy hxy, by simpa only [proj_Ici_of_mem, hx, hy]
lemma strict_mono_on_proj_Iic : strict_mono_on (proj_Iic b) (Iic b) :=
λ x hx y hy hxy, by simpa only [proj_Iic_of_mem, hx, hy]
lemma strict_mono_on_proj_Icc : strict_mono_on (proj_Icc a b h) (Icc a b) :=
λ x hx y hy hxy, by simpa only [proj_Icc_of_mem, hx, hy]

/-- Extend a function `[a, ∞[ → β` to a map `α → β`. -/
def Ici_extend (f : Ici a → β) : α → β := f ∘ proj_Ici a

/-- Extend a function `]-∞, b] → β` to a map `α → β`. -/
def Iic_extend (f : Iic b → β) : α → β := f ∘ proj_Iic b

/-- Extend a function `[a, b] → β` to a map `α → β`. -/
def Icc_extend {a b : α} (h : a ≤ b) (f : Icc a b → β) : α → β :=
f ∘ proj_Icc a b h

@[simp] lemma range_Ici_extend (f : Ici a → β) : range (Ici_extend f) = range f :=
by simp only [Ici_extend, range_comp f, range_proj_Ici, range_id']

@[simp] lemma range_Iic_extend (f : Iic b → β) : range (Iic_extend f) = range f :=
by simp only [Iic_extend, range_comp f, range_proj_Iic, range_id']

@[simp] lemma Icc_extend_range (f : Icc a b → β) :
  range (Icc_extend h f) = range f :=
by simp only [Icc_extend, range_comp f, range_proj_Icc, range_id']

lemma Ici_extend_of_le (f : Ici a → β) (hx : x ≤ a) : Ici_extend f x = f ⟨a, le_rfl⟩ :=
congr_arg f $ proj_Ici_of_le hx

lemma Iic_extend_of_le (f : Iic b → β) (hx : b ≤ x) : Iic_extend f x = f ⟨b, le_rfl⟩ :=
congr_arg f $ proj_Iic_of_le hx

lemma Icc_extend_of_le_left (f : Icc a b → β) (hx : x ≤ a) :
  Icc_extend h f x = f ⟨a, left_mem_Icc.2 h⟩ :=
congr_arg f $ proj_Icc_of_le_left h hx

lemma Icc_extend_of_right_le (f : Icc a b → β) (hx : b ≤ x) :
  Icc_extend h f x = f ⟨b, right_mem_Icc.2 h⟩ :=
congr_arg f $ proj_Icc_of_right_le h hx

@[simp] lemma Ici_extend_self (f : Ici a → β) : Ici_extend f a = f ⟨a, le_rfl⟩ :=
Ici_extend_of_le f le_rfl

@[simp] lemma Iic_extend_self (f : Iic b → β) : Iic_extend f b = f ⟨b, le_rfl⟩ :=
Iic_extend_of_le f le_rfl

@[simp] lemma Icc_extend_left (f : Icc a b → β) :
  Icc_extend h f a = f ⟨a, left_mem_Icc.2 h⟩ :=
Icc_extend_of_le_left h f le_rfl

@[simp] lemma Icc_extend_right (f : Icc a b → β) :
  Icc_extend h f b = f ⟨b, right_mem_Icc.2 h⟩ :=
Icc_extend_of_right_le h f le_rfl

lemma Ici_extend_of_mem (f : Ici a → β) (hx : x ∈ Ici a) : Ici_extend f x = f ⟨x, hx⟩ :=
congr_arg f $ proj_Ici_of_mem hx

lemma Iic_extend_of_mem (f : Iic b → β) (hx : x ∈ Iic b) : Iic_extend f x = f ⟨x, hx⟩ :=
congr_arg f $ proj_Iic_of_mem hx

lemma Icc_extend_of_mem (f : Icc a b → β) (hx : x ∈ Icc a b) :
  Icc_extend h f x = f ⟨x, hx⟩ :=
congr_arg f $ proj_Icc_of_mem h hx

@[simp] lemma Ici_extend_coe (f : Ici a → β) (x : Ici a) : Ici_extend f x = f x :=
congr_arg f $ proj_Ici_coe x

@[simp] lemma Iic_extend_coe (f : Iic b → β) (x : Iic b) : Iic_extend f x = f x :=
congr_arg f $ proj_Iic_coe x

@[simp] lemma Icc_extend_coe (f : Icc a b → β) (x : Icc a b) :
  Icc_extend h f x = f x :=
congr_arg f $ proj_Icc_coe h x

end set

open set

variables [preorder β] {a b : α} (h : a ≤ b) {f : Icc a b → β}

protected lemma monotone.Ici_extend {f : Ici a → β} (hf : monotone f) : monotone (Ici_extend f) :=
hf.comp monotone_proj_Ici

protected lemma monotone.Iic_extend {f : Iic b → β} (hf : monotone f) : monotone (Iic_extend f) :=
hf.comp monotone_proj_Iic

protected lemma monotone.Icc_extend (hf : monotone f) : monotone (Icc_extend h f) :=
hf.comp $ monotone_proj_Icc h

lemma strict_mono.strict_mono_on_Ici_extend {f : Ici a → β} (hf : strict_mono f) :
  strict_mono_on (Ici_extend f) (Ici a) :=
hf.comp_strict_mono_on strict_mono_on_proj_Ici

lemma strict_mono.strict_mono_on_Iic_extend {f : Iic b → β} (hf : strict_mono f) :
  strict_mono_on (Iic_extend f) (Iic b) :=
hf.comp_strict_mono_on strict_mono_on_proj_Iic

lemma strict_mono.strict_mono_on_Icc_extend (hf : strict_mono f) :
  strict_mono_on (Icc_extend h f) (Icc a b) :=
hf.comp_strict_mono_on (strict_mono_on_proj_Icc h)

/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import data.finsupp.defs

/-!
# Locus of unequal values of finitely supported functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Let `α N` be two Types, assume that `N` has a `0` and let `f g : α →₀ N` be finitely supported
functions.

## Main definition

* `finsupp.ne_locus f g : finset α`, the finite subset of `α` where `f` and `g` differ.

In the case in which `N` is an additive group, `finsupp.ne_locus f g` coincides with
`finsupp.support (f - g)`.
-/

variables {α M N P : Type*}

namespace finsupp
variable [decidable_eq α]

section N_has_zero
variables [decidable_eq N] [has_zero N] (f g : α →₀ N)

/--  Given two finitely supported functions `f g : α →₀ N`, `finsupp.ne_locus f g` is the `finset`
where `f` and `g` differ. This generalizes `(f - g).support` to situations without subtraction. -/
def ne_locus (f g : α →₀ N) : finset α :=
(f.support ∪ g.support).filter (λ x, f x ≠ g x)

@[simp] lemma mem_ne_locus {f g : α →₀ N} {a : α} : a ∈ f.ne_locus g ↔ f a ≠ g a :=
by simpa only [ne_locus, finset.mem_filter, finset.mem_union, mem_support_iff,
    and_iff_right_iff_imp] using ne.ne_or_ne _

lemma not_mem_ne_locus {f g : α →₀ N} {a : α} : a ∉ f.ne_locus g ↔ f a = g a :=
mem_ne_locus.not.trans not_ne_iff

@[simp] lemma coe_ne_locus : ↑(f.ne_locus g) = {x | f x ≠ g x} :=
by { ext, exact mem_ne_locus }

@[simp] lemma ne_locus_eq_empty {f g : α →₀ N} : f.ne_locus g = ∅ ↔ f = g :=
⟨λ h, ext (λ a, not_not.mp (mem_ne_locus.not.mp (finset.eq_empty_iff_forall_not_mem.mp h a))),
  λ h, h ▸ by simp only [ne_locus, ne.def, eq_self_iff_true, not_true, finset.filter_false]⟩

@[simp] lemma nonempty_ne_locus_iff {f g : α →₀ N} : (f.ne_locus g).nonempty ↔ f ≠ g :=
finset.nonempty_iff_ne_empty.trans ne_locus_eq_empty.not

lemma ne_locus_comm : f.ne_locus g = g.ne_locus f :=
by simp_rw [ne_locus, finset.union_comm, ne_comm]

@[simp]
lemma ne_locus_zero_right : f.ne_locus 0 = f.support :=
by { ext, rw [mem_ne_locus, mem_support_iff, coe_zero, pi.zero_apply] }

@[simp]
lemma ne_locus_zero_left : (0 : α →₀ N).ne_locus f = f.support :=
(ne_locus_comm _ _).trans (ne_locus_zero_right _)

end N_has_zero

section ne_locus_and_maps

lemma subset_map_range_ne_locus [decidable_eq N] [has_zero N] [decidable_eq M] [has_zero M]
  (f g : α →₀ N) {F : N → M} (F0 : F 0 = 0) :
  (f.map_range F F0).ne_locus (g.map_range F F0) ⊆ f.ne_locus g :=
λ x, by simpa only [mem_ne_locus, map_range_apply, not_imp_not] using congr_arg F

lemma zip_with_ne_locus_eq_left [decidable_eq N] [has_zero M] [decidable_eq P] [has_zero P]
  [has_zero N] {F : M → N → P} (F0 : F 0 0 = 0)
  (f : α →₀ M) (g₁ g₂ : α →₀ N) (hF : ∀ f, function.injective (λ g, F f g)) :
  (zip_with F F0 f g₁).ne_locus (zip_with F F0 f g₂) = g₁.ne_locus g₂ :=
by { ext, simpa only [mem_ne_locus] using (hF _).ne_iff }

lemma zip_with_ne_locus_eq_right [decidable_eq M] [has_zero M] [decidable_eq P] [has_zero P]
  [has_zero N] {F : M → N → P} (F0 : F 0 0 = 0)
  (f₁ f₂ : α →₀ M) (g : α →₀ N) (hF : ∀ g, function.injective (λ f, F f g)) :
  (zip_with F F0 f₁ g).ne_locus (zip_with F F0 f₂ g) = f₁.ne_locus f₂ :=
by { ext, simpa only [mem_ne_locus] using (hF _).ne_iff }

lemma map_range_ne_locus_eq [decidable_eq N] [decidable_eq M] [has_zero M] [has_zero N]
  (f g : α →₀ N) {F : N → M} (F0 : F 0 = 0) (hF : function.injective F) :
  (f.map_range F F0).ne_locus (g.map_range F F0) = f.ne_locus g :=
by { ext, simpa only [mem_ne_locus] using hF.ne_iff }

end ne_locus_and_maps

variables [decidable_eq N]

@[simp] lemma ne_locus_add_left [add_left_cancel_monoid N] (f g h : α →₀ N) :
  (f + g).ne_locus (f + h) = g.ne_locus h :=
zip_with_ne_locus_eq_left _ _ _ _ add_right_injective

@[simp] lemma ne_locus_add_right [add_right_cancel_monoid N] (f g h : α →₀ N) :
  (f + h).ne_locus (g + h) = f.ne_locus g :=
zip_with_ne_locus_eq_right _ _ _ _ add_left_injective

section add_group
variables [add_group N] (f f₁ f₂ g g₁ g₂ : α →₀ N)

@[simp] lemma ne_locus_neg_neg : ne_locus (-f) (-g) = f.ne_locus g :=
map_range_ne_locus_eq _ _ neg_zero neg_injective

lemma ne_locus_neg : ne_locus (-f) g = f.ne_locus (-g) := by rw [←ne_locus_neg_neg, neg_neg]

lemma ne_locus_eq_support_sub : f.ne_locus g = (f - g).support :=
by rw [←ne_locus_add_right _ _ (-g), add_right_neg, ne_locus_zero_right, sub_eq_add_neg]

@[simp] lemma ne_locus_sub_left : ne_locus (f - g₁) (f - g₂) = ne_locus g₁ g₂ :=
by simp only [sub_eq_add_neg, ne_locus_add_left, ne_locus_neg_neg]

@[simp] lemma ne_locus_sub_right : ne_locus (f₁ - g) (f₂ - g) = ne_locus f₁ f₂ :=
by simpa only [sub_eq_add_neg] using ne_locus_add_right _ _ _

@[simp] lemma ne_locus_self_add_right : ne_locus f (f + g) = g.support :=
by rw [←ne_locus_zero_left, ←ne_locus_add_left f 0 g, add_zero]

@[simp] lemma ne_locus_self_add_left : ne_locus (f + g) f = g.support :=
by rw [ne_locus_comm, ne_locus_self_add_right]

@[simp] lemma ne_locus_self_sub_right : ne_locus f (f - g) = g.support :=
by rw [sub_eq_add_neg, ne_locus_self_add_right, support_neg]

@[simp] lemma ne_locus_self_sub_left : ne_locus (f - g) f = g.support :=
by rw [ne_locus_comm, ne_locus_self_sub_right]

end add_group
end finsupp

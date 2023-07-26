/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Junyan Xu
-/
import data.dfinsupp.basic

/-!
# Locus of unequal values of finitely supported dependent functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Let `N : α → Type*` be a type family, assume that `N a` has a `0` for all `a : α` and let
`f g : Π₀ a, N a` be finitely supported dependent functions.

## Main definition

* `dfinsupp.ne_locus f g : finset α`, the finite subset of `α` where `f` and `g` differ.
In the case in which `N a` is an additive group for all `a`, `dfinsupp.ne_locus f g` coincides with
`dfinsupp.support (f - g)`.
-/

variables {α : Type*} {N : α → Type*}

namespace dfinsupp
variable [decidable_eq α]

section N_has_zero
variables [Π a, decidable_eq (N a)] [Π a, has_zero (N a)] (f g : Π₀ a, N a)

/--  Given two finitely supported functions `f g : α →₀ N`, `finsupp.ne_locus f g` is the `finset`
where `f` and `g` differ. This generalizes `(f - g).support` to situations without subtraction. -/
def ne_locus (f g : Π₀ a, N a) : finset α :=
(f.support ∪ g.support).filter (λ x, f x ≠ g x)

@[simp] lemma mem_ne_locus {f g : Π₀ a, N a} {a : α} : a ∈ f.ne_locus g ↔ f a ≠ g a :=
by simpa only [ne_locus, finset.mem_filter, finset.mem_union, mem_support_iff,
    and_iff_right_iff_imp] using ne.ne_or_ne _

lemma not_mem_ne_locus {f g : Π₀ a, N a} {a : α} : a ∉ f.ne_locus g ↔ f a = g a :=
mem_ne_locus.not.trans not_ne_iff

@[simp] lemma coe_ne_locus : ↑(f.ne_locus g) = {x | f x ≠ g x} :=
set.ext $ λ x, mem_ne_locus

@[simp] lemma ne_locus_eq_empty {f g : Π₀ a, N a} : f.ne_locus g = ∅ ↔ f = g :=
⟨λ h, ext (λ a, not_not.mp (mem_ne_locus.not.mp (finset.eq_empty_iff_forall_not_mem.mp h a))),
  λ h, h ▸ by simp only [ne_locus, ne.def, eq_self_iff_true, not_true, finset.filter_false]⟩

@[simp] lemma nonempty_ne_locus_iff {f g : Π₀ a, N a} : (f.ne_locus g).nonempty ↔ f ≠ g :=
finset.nonempty_iff_ne_empty.trans ne_locus_eq_empty.not

lemma ne_locus_comm : f.ne_locus g = g.ne_locus f :=
by simp_rw [ne_locus, finset.union_comm, ne_comm]

@[simp]
lemma ne_locus_zero_right : f.ne_locus 0 = f.support :=
by { ext, rw [mem_ne_locus, mem_support_iff, coe_zero, pi.zero_apply] }

@[simp]
lemma ne_locus_zero_left : (0 : Π₀ a, N a).ne_locus f = f.support :=
(ne_locus_comm _ _).trans (ne_locus_zero_right _)

end N_has_zero

section ne_locus_and_maps

variables {M P : α → Type*} [Π a, has_zero (N a)] [Π a, has_zero (M a)] [Π a, has_zero (P a)]

lemma subset_map_range_ne_locus [Π a, decidable_eq (N a)] [Π a, decidable_eq (M a)]
  (f g : Π₀ a, N a) {F : Π a, N a → M a} (F0 : ∀ a, F a 0 = 0) :
  (f.map_range F F0).ne_locus (g.map_range F F0) ⊆ f.ne_locus g :=
λ a, by simpa only [mem_ne_locus, map_range_apply, not_imp_not] using congr_arg (F a)

lemma zip_with_ne_locus_eq_left [Π a, decidable_eq (N a)] [Π a, decidable_eq (P a)]
  {F : Π a, M a → N a → P a} (F0 : ∀ a, F a 0 0 = 0)
  (f : Π₀ a, M a) (g₁ g₂ : Π₀ a, N a) (hF : ∀ a f, function.injective (λ g, F a f g)) :
  (zip_with F F0 f g₁).ne_locus (zip_with F F0 f g₂) = g₁.ne_locus g₂ :=
by { ext, simpa only [mem_ne_locus] using (hF a _).ne_iff }

lemma zip_with_ne_locus_eq_right [Π a, decidable_eq (M a)] [Π a, decidable_eq (P a)]
  {F : Π a, M a → N a → P a} (F0 : ∀ a, F a 0 0 = 0)
  (f₁ f₂ : Π₀ a, M a) (g : Π₀ a, N a) (hF : ∀ a g, function.injective (λ f, F a f g)) :
  (zip_with F F0 f₁ g).ne_locus (zip_with F F0 f₂ g) = f₁.ne_locus f₂ :=
by { ext, simpa only [mem_ne_locus] using (hF a _).ne_iff }

lemma map_range_ne_locus_eq [Π a, decidable_eq (N a)] [Π a, decidable_eq (M a)] (f g : Π₀ a, N a)
  {F : Π a, N a → M a} (F0 : ∀ a, F a 0 = 0) (hF : ∀ a, function.injective (F a)) :
  (f.map_range F F0).ne_locus (g.map_range F F0) = f.ne_locus g :=
by { ext, simpa only [mem_ne_locus] using (hF a).ne_iff }

end ne_locus_and_maps

variables [Π a, decidable_eq (N a)]

@[simp] lemma ne_locus_add_left [Π a, add_left_cancel_monoid (N a)] (f g h : Π₀ a, N a) :
  (f + g).ne_locus (f + h) = g.ne_locus h  :=
zip_with_ne_locus_eq_left _ _ _ _ $ λ a, add_right_injective

@[simp] lemma ne_locus_add_right [Π a, add_right_cancel_monoid (N a)] (f g h : Π₀ a, N a) :
  (f + h).ne_locus (g + h) = f.ne_locus g  :=
zip_with_ne_locus_eq_right _ _ _ _ $ λ a, add_left_injective

section add_group
variables [Π a, add_group (N a)] (f f₁ f₂ g g₁ g₂ : Π₀ a, N a)

@[simp] lemma ne_locus_neg_neg : ne_locus (-f) (-g) = f.ne_locus g :=
map_range_ne_locus_eq _ _ (λ a, neg_zero) (λ a, neg_injective)

lemma ne_locus_neg : ne_locus (-f) g = f.ne_locus (-g) := by rw [←ne_locus_neg_neg, neg_neg]

lemma ne_locus_eq_support_sub : f.ne_locus g = (f - g).support :=
by rw [←@ne_locus_add_right α N _ _ _ _ _ (-g), add_right_neg, ne_locus_zero_right, sub_eq_add_neg]

@[simp] lemma ne_locus_sub_left : ne_locus (f - g₁) (f - g₂) = ne_locus g₁ g₂ :=
by simp only [sub_eq_add_neg, @ne_locus_add_left α N _ _ _, ne_locus_neg_neg]

@[simp] lemma ne_locus_sub_right : ne_locus (f₁ - g) (f₂ - g) = ne_locus f₁ f₂ :=
by simpa only [sub_eq_add_neg] using @ne_locus_add_right α N _ _ _ _ _ _

@[simp] lemma ne_locus_self_add_right : ne_locus f (f + g) = g.support :=
by rw [←ne_locus_zero_left, ←@ne_locus_add_left α N _ _ _ f 0 g, add_zero]

@[simp] lemma ne_locus_self_add_left : ne_locus (f + g) f = g.support :=
by rw [ne_locus_comm, ne_locus_self_add_right]

@[simp] lemma ne_locus_self_sub_right : ne_locus f (f - g) = g.support :=
by rw [sub_eq_add_neg, ne_locus_self_add_right, support_neg]

@[simp] lemma ne_locus_self_sub_left : ne_locus (f - g) f = g.support :=
by rw [ne_locus_comm, ne_locus_self_sub_right]

end add_group
end dfinsupp

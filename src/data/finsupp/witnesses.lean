/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import data.finsupp.basic

/-!
#  `diff` for finitely supported functions

Let `α N` be two Types, and assume that `N` has a `0` and let `f g : α →₀ N` be finitely supported
functions.

## Main definition

* `finsupp.diff f g : finset α`, the finite subset of `α` where `f` and `g` differ.

In the case in which `N` is an additive group, `finsupp.diff f g` coincides with
`finsupp.support (f - g)`.
-/

variables {α N : Type*}

namespace finsupp
variables [decidable_eq α] [decidable_eq N]

section diff

section N_has_zero
variables [has_zero N] {f g : α →₀ N}

/--  Given two finitely supported functions `f g : α →₀ N`, `finsupp.diff f g` is the `finset`
where `f` and `g` differ. This generalizes `(f - g).support` to situations without subtraction. -/
def diff (f g : α →₀ N) : finset α :=
(f.support ∪ g.support).filter (λ x, f x ≠ g x)

@[simp]
lemma mem_diff {a : α} : a ∈ f.diff g ↔ f a ≠ g a :=
by simpa only [diff, finset.mem_filter, finset.mem_union, mem_support_iff, and_iff_right_iff_imp]
    using ne.ne_or_ne _

lemma coe_diff : ↑(f.diff g) = {x | f x ≠ g x} :=
by { ext, exact mem_diff }

lemma diff_comm : f.diff g = g.diff f :=
by simp_rw [diff, finset.union_comm, ne_comm]

@[simp] lemma diff_eq_empty : f.diff g = ∅ ↔ f = g :=
begin
  refine ⟨λ h, _, λ h, h ▸ by simp [diff]⟩,
  ext a,
  refine not_ne_iff.mp (λ fg, not_ne_iff.mpr h _),
  refine finset.ne_empty_of_mem (_ : a ∈ _),
  simp only [diff, finset.mem_filter, finset.mem_union, finsupp.mem_support_iff],
  exact ⟨fg.ne_or_ne _, fg⟩,
end

@[simp] lemma nonempty_diff_iff : (f.diff g).nonempty ↔ f ≠ g :=
finset.nonempty_iff_ne_empty.trans diff_eq_empty.not

@[simp]
lemma diff_zero_right : f.diff 0 = f.support :=
by simp only [diff, coe_zero, pi.zero_apply, support_zero, finset.union_empty,
    finset.filter_true_of_mem, mem_support_iff, imp_self, implies_true_iff]

@[simp]
lemma diff_zero_left : (0 : α →₀ N).diff f = f.support :=
diff_comm.trans diff_zero_right

lemma subset_map_range_diff {M} [decidable_eq M] [has_zero M] {F : N → M} (F0 : F 0 = 0) :
  (f.map_range F F0).diff (g.map_range F F0) ⊆ f.diff g :=
begin
  refine λ x, _,
  simp only [mem_diff, map_range_apply, not_not],
  exact not_imp_not.mpr (λ h, h ▸ rfl),
end

lemma map_range_diff_eq {M} [decidable_eq M] [has_zero M]
  {F : N → M} (F0 : F 0 = 0) (hF : function.injective F) :
  (f.map_range F F0).diff (g.map_range F F0) = f.diff g :=
by { ext, simpa only [mem_diff] using hF.ne_iff }

end N_has_zero

lemma add_diff_add_eq_left [add_left_cancel_monoid N] (f : α →₀ N) {g h : α →₀ N} :
  (f + g).diff (f + h) = g.diff h  :=
begin
  ext,
  simp only [diff, ne.def, add_right_inj, finset.mem_filter, finset.mem_union, mem_support_iff,
    coe_add, pi.add_apply, and.congr_left_iff],
  exact λ bc, ⟨λ h, ne.ne_or_ne 0 bc, λ h, ne.ne_or_ne _ ((add_right_inj _).not.mpr bc)⟩,
end

--  can this proof by replaced by the previous one applied to `Nᵃᵒᵖ` and interlaced with `op unop`?
lemma add_diff_add_eq_right [add_right_cancel_monoid N] {f g : α →₀ N} (h : α →₀ N):
  (f + h).diff (g + h) = f.diff g  :=
begin
  ext,
  simp only [diff, ne.def, add_left_inj, finset.mem_filter, finset.mem_union, mem_support_iff,
    coe_add, pi.add_apply, and.congr_left_iff],
  exact λ bc, ⟨λ h, ne.ne_or_ne 0 bc, λ h, ne.ne_or_ne _ ((add_left_inj _).not.mpr bc)⟩,
end

lemma diff_neg [add_group N] {f g : α →₀ N} : (- f).diff g = f.diff (- g) :=
begin
  nth_rewrite 0 ← neg_neg g,
  exact map_range_diff_eq neg_zero neg_injective,
end

@[simp] lemma diff_eq_support_sub [add_group N] {f g : α →₀ N} :
  f.diff g = (f - g).support :=
by rw [← add_diff_add_eq_right (- g), add_right_neg, diff_zero_right, sub_eq_add_neg]

end diff

end finsupp

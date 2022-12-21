/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import data.dfinsupp.well_founded
import data.finsupp.lex

/-!
# Well-foundedness of the lexicographic and product orders on `finsupp`

`finsupp.lex.well_founded` and the two variants that follow it essentially say that if
`(>)` is a well order on `α`, `(<)` is well-founded on `N`, and `0` is a bottom element in `N`,
then the lexicographic `(<)` is well-founded on `α →₀ N`.

`finsupp.lex.well_founded_lt_of_finite` says that if `α` is finite and equipped with a linear
order and `(<)` is well-founded on `N`, then the lexicographic `(<)` is well-founded on `α →₀ N`.

`finsupp.well_founded_lt` and `well_founded_lt_of_finite` state the same results for the product
order `(<)`, but without the ordering conditions on `α`.

All results are transferred from `dfinsupp` via `finsupp.to_dfinsupp`.
-/

variables {α N : Type*}

namespace finsupp

variables [hz : has_zero N] {r : α → α → Prop} {s : N → N → Prop}
  (hbot : ∀ ⦃n⦄, ¬ s n 0) (hs : well_founded s)
include hbot hs

/-- Transferred from `dfinsupp.lex.acc`. See the top of that file for an explanation for the
  appearance of the relation `rᶜ ⊓ (≠)`. -/
lemma lex.acc (x : α →₀ N) (h : ∀ a ∈ x.support, acc (rᶜ ⊓ (≠)) a) : acc (finsupp.lex r s) x :=
begin
  rw lex_eq_inv_image_dfinsupp_lex, classical,
  refine inv_image.accessible to_dfinsupp (dfinsupp.lex.acc (λ a, hbot) (λ a, hs) _ _),
  simpa only [to_dfinsupp_support] using h,
end

theorem lex.well_founded (hr : well_founded $ rᶜ ⊓ (≠)) : well_founded (finsupp.lex r s) :=
⟨λ x, lex.acc hbot hs x $ λ a _, hr.apply a⟩

theorem lex.well_founded' [is_trichotomous α r]
  (hr : well_founded r.swap) : well_founded (finsupp.lex r s) :=
(lex_eq_inv_image_dfinsupp_lex r s).symm ▸
  inv_image.wf _ (dfinsupp.lex.well_founded' (λ a, hbot) (λ a, hs) hr)

omit hbot hs

instance lex.well_founded_lt [has_lt α] [is_trichotomous α (<)] [hα : well_founded_gt α]
  [canonically_ordered_add_monoid N] [hN : well_founded_lt N] : well_founded_lt (lex (α →₀ N)) :=
⟨lex.well_founded' (λ n, (zero_le n).not_lt) hN.wf hα.wf⟩

variable (r)

theorem lex.well_founded_of_finite [is_strict_total_order α r] [finite α] [has_zero N]
  (hs : well_founded s) : well_founded (finsupp.lex r s) :=
inv_image.wf (@equiv_fun_on_finite α N _ _) (pi.lex.well_founded r $ λ a, hs)

theorem lex.well_founded_lt_of_finite [linear_order α] [finite α] [has_zero N] [has_lt N]
  [hwf : well_founded_lt N] : well_founded_lt (lex (α →₀ N)) :=
⟨finsupp.lex.well_founded_of_finite (<) hwf.1⟩

protected theorem well_founded_lt [has_zero N] [preorder N] [well_founded_lt N]
  (hbot : ∀ n : N, ¬ n < 0) : well_founded_lt (α →₀ N) :=
⟨inv_image.wf to_dfinsupp (dfinsupp.well_founded_lt $ λ i a, hbot a).wf⟩

instance well_founded_lt' [canonically_ordered_add_monoid N]
  [well_founded_lt N] : well_founded_lt (α →₀ N) :=
finsupp.well_founded_lt $ λ a, (zero_le a).not_lt

instance well_founded_lt_of_finite [finite α] [has_zero N] [preorder N]
  [well_founded_lt N] : well_founded_lt (α →₀ N) :=
⟨inv_image.wf equiv_fun_on_finite function.well_founded_lt.wf⟩

end finsupp

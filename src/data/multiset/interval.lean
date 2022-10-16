/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.locally_finite
import data.dfinsupp.interval
import data.nat.interval

/-!
# Finite intervals of multiests

This file provides the `locally_finite_order` instance for `multiset α` and calculates the
cardinality of its finite intervals.

-/

open finset dfinsupp function
open_locale big_operators pointwise

variables {α : Type*} {β : α → Type*}

namespace dfinsupp

/-- Non-dependent special case of `dfinsupp.add_zero_class` to help typeclass search. -/
instance add_zero_class' {β} [add_zero_class β] : add_zero_class (Π₀ a : α, β) :=
@dfinsupp.add_zero_class α (λ _, β) _

/-- A computable version of `finsupp.to_multiset`. -/
def to_multiset [decidable_eq α] : (Π₀ a : α, ℕ) ≃+ multiset α :=
add_monoid_hom.to_add_equiv
  (dfinsupp.sum_add_hom (λ a : α, multiset.repeat_add_monoid_hom a))
  { to_fun := λ s,
    { to_fun := λ n, s.count n,
      support' := trunc.mk ⟨s, λ i, (em (i ∈ s)).imp_right multiset.count_eq_zero_of_not_mem⟩ },
    map_zero' := rfl,
    map_add' := λ s t, dfinsupp.ext $ λ _, multiset.count_add _ _ _ }
  (by {
    classical,
    refine @dfinsupp.add_hom_ext α (λ _, ℕ) _ _ _ _ _ _ (λ i hi, _),
    ext,
    dsimp,
    rw [dfinsupp.sum_add_hom_single, multiset.repeat_add_monoid_hom_apply, multiset.count_repeat,
      single_apply],
    simp [eq_comm], })
  (by {
    ext x : 1,
    dsimp,
    sorry
  })
-- { inv_fun := λ s, { to_fun := λ n, s.count n,
--     support' := trunc.mk ⟨s, λ i, (em (i ∈ s)).imp_right multiset.count_eq_zero_of_not_mem⟩ },
--   left_inv := λ f, dfinsupp.ext $ \lam by simp,
--   .. dfinsupp.sum_add_hom (λ a : α, multiset.repeat_add_monoid_hom a) }

end dfinsupp

namespace multiset

/-- A computable version of `multiset.to_finsupp` -/
def to_dfinsupp [decidable_eq α] : multiset α →+ Π₀ a : α, ℕ :=
add_equiv.symm (dfinsupp.to_multiset : (Π₀ a : α, ℕ) ≃+ multiset α)

@[simp] lemma to_dfinsupp_to_multiset [decidable_eq α] (s : multiset α) : s.to_dfinsupp.to_multiset = s :=
dfinsupp.to_multiset.apply_symm_apply s

end multiset

namespace multiset

variables [partial_order α] [has_zero α] [locally_finite_order α] (f g : multiset α)

example : locally_finite_order nat := by apply_instance

instance [decidable_eq α] : locally_finite_order (multiset α) :=
locally_finite_order.of_Icc (multiset α)
  (λ f g, (finset.Icc f.to_dfinsupp g.to_dfinsupp).map (dfinsupp.to_multiset.to_equiv.to_embedding))
  (λ f g x, begin
    conv_lhs { rw [←multiset.to_dfinsupp_to_multiset x]},
    erw finset.mem_map_equiv,
    simp,
    sorry
  end)

lemma Icc_eq [decidable_eq α] :
  finset.Icc f g = (finset.Icc f.to_dfinsupp g.to_dfinsupp).map (dfinsupp.to_multiset.to_equiv.to_embedding) := rfl

lemma card_Icc [decidable_eq α]  :
  (finset.Icc f g).card = ∏ i in (f + g).to_finset, (g.count i - f.count i) :=
sorry

lemma card_Ico [decidable_eq α] :
  (finset.Ico f g).card = ∏ i in (f + g).to_finset, (g.count i - f.count i) - 1 :=
by rw [card_Ico_eq_card_Icc_sub_one, card_Icc]

lemma card_Ioc [decidable_eq α] : (finset.Ioc f g).card = ∏ i in (f + g).to_finset, (g.count i - f.count i) - 1 :=
by rw [card_Ioc_eq_card_Icc_sub_one, card_Icc]

lemma card_Ioo [decidable_eq α] : (finset.Ioo f g).card = ∏ i in (f + g).to_finset, (g.count i - f.count i) - 2 :=
by rw [card_Ioo_eq_card_Icc_sub_two, card_Icc]

end multiset

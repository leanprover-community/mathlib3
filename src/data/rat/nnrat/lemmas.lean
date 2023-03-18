/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import algebra.algebra.basic
import algebra.indicator_function
import data.rat.basic

/-!
# Algebraic structures on the nonnegative rationals

This file provides additional results about `nnrat` that cannot live in earlier files due to import
cycles.
-/

open function
open_locale big_operators nnrat

namespace nnrat
variables {α : Type*} {p q : ℚ≥0}

/-- The rational numbers are an algebra over the non-negative rationals. -/
instance : algebra ℚ≥0 ℚ := coe_hom.to_algebra

/-- A `module` over `ℚ` restricts to a `module` over `ℚ≥0`. -/
instance [add_comm_monoid α] [module ℚ α] : module ℚ≥0 α := module.comp_hom α coe_hom

@[simp, norm_cast] lemma coe_indicator (s : set α) (f : α → ℚ≥0) (a : α) :
  ((s.indicator f a : ℚ≥0) : ℚ) = s.indicator (λ x, f x) a :=
(coe_hom : ℚ≥0 →+ ℚ).map_indicator _ _ _

@[norm_cast] lemma coe_list_sum (l : list ℚ≥0) : (l.sum : ℚ) = (l.map coe).sum :=
coe_hom.map_list_sum _

@[norm_cast] lemma coe_list_prod (l : list ℚ≥0) : (l.prod : ℚ) = (l.map coe).prod :=
coe_hom.map_list_prod _

@[norm_cast] lemma coe_multiset_sum (s : multiset ℚ≥0) : (s.sum : ℚ) = (s.map coe).sum :=
coe_hom.map_multiset_sum _

@[norm_cast] lemma coe_multiset_prod (s : multiset ℚ≥0) : (s.prod : ℚ) = (s.map coe).prod :=
coe_hom.map_multiset_prod _

@[norm_cast] lemma coe_sum {s : finset α} {f : α → ℚ≥0} : ↑(∑ a in s, f a) = ∑ a in s, (f a : ℚ) :=
coe_hom.map_sum _ _

lemma to_nnrat_sum_of_nonneg {s : finset α} {f : α → ℚ} (hf : ∀ a, a ∈ s → 0 ≤ f a) :
  (∑ a in s, f a).to_nnrat = ∑ a in s, (f a).to_nnrat :=
begin
  rw [←coe_inj, coe_sum, rat.coe_to_nnrat _ (finset.sum_nonneg hf)],
  exact finset.sum_congr rfl (λ x hxs, by rw rat.coe_to_nnrat _ (hf x hxs)),
end

@[norm_cast] lemma coe_prod {s : finset α} {f : α → ℚ≥0} : ↑(∏ a in s, f a) = ∏ a in s, (f a : ℚ) :=
coe_hom.map_prod _ _

lemma to_nnrat_prod_of_nonneg {s : finset α} {f : α → ℚ} (hf : ∀ a ∈ s, 0 ≤ f a) :
  (∏ a in s, f a).to_nnrat = ∏ a in s, (f a).to_nnrat :=
begin
  rw [←coe_inj, coe_prod, rat.coe_to_nnrat _ (finset.prod_nonneg hf)],
  exact finset.prod_congr rfl (λ x hxs, by rw rat.coe_to_nnrat _ (hf x hxs)),
end

end nnrat

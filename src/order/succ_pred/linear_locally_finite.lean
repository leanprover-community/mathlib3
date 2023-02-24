/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import order.locally_finite
import order.succ_pred.basic
import order.hom.basic
import data.countable.basic
import logic.encodable.basic

/-!
# Linear locally finite orders

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We prove that a `linear_order` which is a `locally_finite_order` also verifies
* `succ_order`
* `pred_order`
* `is_succ_archimedean`
* `is_pred_archimedean`
* `countable`

Furthermore, we show that there is an `order_iso` between such an order and a subset of `ℤ`.

## Main definitions

* `to_Z i0 i`: in a linear order on which we can define predecessors and successors and which is
  succ-archimedean, we can assign a unique integer `to_Z i0 i` to each element `i : ι` while
  respecting the order, starting from `to_Z i0 i0 = 0`.

## Main results

Instances about linear locally finite orders:
* `linear_locally_finite_order.succ_order`: a linear locally finite order has a successor function.
* `linear_locally_finite_order.pred_order`: a linear locally finite order has a predecessor
  function.
* `linear_locally_finite_order.is_succ_archimedean`: a linear locally finite order is
  succ-archimedean.
* `linear_order.pred_archimedean_of_succ_archimedean`: a succ-archimedean linear order is also
  pred-archimedean.
* `countable_of_linear_succ_pred_arch` : a succ-archimedean linear order is countable.

About `to_Z`:
* `order_iso_range_to_Z_of_linear_succ_pred_arch`: `to_Z` defines an `order_iso` between `ι` and its
  range.
* `order_iso_nat_of_linear_succ_pred_arch`: if the order has a bot but no top, `to_Z` defines an
  `order_iso` between `ι` and `ℕ`.
* `order_iso_int_of_linear_succ_pred_arch`: if the order has neither bot nor top, `to_Z` defines an
  `order_iso` between `ι` and `ℤ`.
* `order_iso_range_of_linear_succ_pred_arch`: if the order has both a bot and a top, `to_Z` gives an
  `order_iso` between `ι` and `finset.range ((to_Z ⊥ ⊤).to_nat + 1)`.

-/

open order

variables {ι : Type*} [linear_order ι]

namespace linear_locally_finite_order

/-- Successor in a linear order. This defines a true successor only when `i` is isolated from above,
i.e. when `i` is not the greatest lower bound of `(i, ∞)`. -/
noncomputable def succ_fn (i : ι) : ι := (exists_glb_Ioi i).some

lemma succ_fn_spec (i : ι) : is_glb (set.Ioi i) (succ_fn i) := (exists_glb_Ioi i).some_spec

lemma le_succ_fn (i : ι) : i ≤ succ_fn i :=
by { rw [le_is_glb_iff (succ_fn_spec i), mem_lower_bounds], exact λ x hx, (le_of_lt hx), }

lemma is_glb_Ioc_of_is_glb_Ioi {i j k : ι} (hij_lt : i < j) (h : is_glb (set.Ioi i) k) :
  is_glb (set.Ioc i j) k :=
begin
  simp_rw [is_glb, is_greatest, mem_upper_bounds, mem_lower_bounds] at h ⊢,
  refine ⟨λ x hx, h.1 x hx.1, λ x hx, h.2 x _⟩,
  intros y hy,
  cases le_or_lt y j with h_le h_lt,
  { exact hx y ⟨hy, h_le⟩, },
  { exact le_trans (hx j ⟨hij_lt, le_rfl⟩) h_lt.le, },
end

lemma is_max_of_succ_fn_le [locally_finite_order ι] (i : ι) (hi : succ_fn i ≤ i) : is_max i :=
begin
  refine λ j hij, not_lt.mp (λ hij_lt, _),
  have h_succ_fn_eq : succ_fn i = i := le_antisymm hi (le_succ_fn i),
  have h_glb : is_glb (finset.Ioc i j : set ι) i,
  { rw finset.coe_Ioc,
    have h := succ_fn_spec i,
    rw h_succ_fn_eq at h,
    exact is_glb_Ioc_of_is_glb_Ioi hij_lt h, },
  have hi_mem : i ∈ finset.Ioc i j,
  { refine finset.is_glb_mem _ h_glb _,
    exact ⟨_, finset.mem_Ioc.mpr ⟨hij_lt, le_rfl⟩⟩, },
  rw finset.mem_Ioc at hi_mem,
  exact lt_irrefl i hi_mem.1,
end

lemma succ_fn_le_of_lt (i j : ι) (hij : i < j) : succ_fn i ≤ j :=
by { have h := succ_fn_spec i, rw [is_glb, is_greatest, mem_lower_bounds] at h, exact h.1 j hij, }

lemma le_of_lt_succ_fn (j i : ι) (hij : j < succ_fn i) : j ≤ i :=
begin
  rw lt_is_glb_iff (succ_fn_spec i) at hij,
  obtain ⟨k, hk_lb, hk⟩ := hij,
  rw mem_lower_bounds at hk_lb,
  exact not_lt.mp (λ hi_lt_j, not_le.mpr hk (hk_lb j hi_lt_j)),
end

@[priority 100]
noncomputable instance [locally_finite_order ι] : succ_order ι :=
{ succ := succ_fn,
  le_succ := le_succ_fn,
  max_of_succ_le := is_max_of_succ_fn_le,
  succ_le_of_lt := succ_fn_le_of_lt,
  le_of_lt_succ := le_of_lt_succ_fn, }

@[priority 100]
noncomputable instance [locally_finite_order ι] : pred_order ι :=
@order_dual.pred_order ιᵒᵈ _ _

end linear_locally_finite_order

@[priority 100]
instance linear_locally_finite_order.is_succ_archimedean [locally_finite_order ι] :
  is_succ_archimedean ι :=
{ exists_succ_iterate_of_le := λ i j hij,
  begin
    rw le_iff_lt_or_eq at hij,
    cases hij,
    swap, { refine ⟨0, _⟩, simpa only [function.iterate_zero, id.def] using hij, },
    by_contra h,
    push_neg at h,
    have h_lt : ∀ n, succ^[n] i < j,
    { intro n,
      induction n with n hn,
      { simpa only [function.iterate_zero, id.def] using hij, },
      { refine lt_of_le_of_ne _ (h _),
        rw [function.iterate_succ', function.comp_app],
        exact succ_le_of_lt hn, }, },
    have h_mem : ∀ n, succ^[n] i ∈ finset.Icc i j,
      from λ n, finset.mem_Icc.mpr ⟨le_succ_iterate n i, (h_lt n).le⟩,
    obtain ⟨n, m, hnm, h_eq⟩ : ∃ n m, n < m ∧ (succ^[n] i = (succ^[m] i)),
    { let f : ℕ → finset.Icc i j := λ n, ⟨succ^[n] i, h_mem n⟩,
      obtain ⟨n, m, hnm_ne, hfnm⟩ : ∃ n m, n ≠ m ∧ f n = f m,
        from finite.exists_ne_map_eq_of_infinite f,
      have hnm_eq : (succ^[n] i) = (succ^[m] i),
      { simpa only [subtype.mk_eq_mk] using hfnm, },
      cases le_total n m with h_le h_le,
      { exact ⟨n, m, lt_of_le_of_ne h_le hnm_ne, hnm_eq⟩, },
      { exact ⟨m, n, lt_of_le_of_ne h_le hnm_ne.symm, hnm_eq.symm ⟩, }, },
    have h_max : is_max (succ^[n] i) := is_max_iterate_succ_of_eq_of_ne h_eq hnm.ne,
    exact not_le.mpr (h_lt n) (h_max (h_lt n).le),
  end }

@[priority 100]
instance linear_order.pred_archimedean_of_succ_archimedean [succ_order ι] [pred_order ι]
  [is_succ_archimedean ι] :
  is_pred_archimedean ι :=
{ exists_pred_iterate_of_le := λ i j hij,
  begin
    have h_exists := exists_succ_iterate_of_le hij,
    obtain ⟨n, hn_eq, hn_lt_ne⟩ : ∃ n, (succ^[n] i = j) ∧ (∀ m < n, succ^[m] i ≠ j),
      from ⟨nat.find h_exists, nat.find_spec h_exists, λ m hmn, nat.find_min h_exists hmn⟩,
    refine ⟨n, _⟩,
    rw ← hn_eq,
    induction n with n hn,
    { simp only [function.iterate_zero, id.def], },
    { rw pred_succ_iterate_of_not_is_max,
      rw [nat.succ_sub_succ_eq_sub, tsub_zero],
      suffices : (succ^[n] i) < (succ^[n.succ] i), from not_is_max_of_lt this,
      refine lt_of_le_of_ne _ _,
      { rw function.iterate_succ',
        exact le_succ _, },
      { rw hn_eq,
        exact hn_lt_ne _ (nat.lt_succ_self n), }, },
  end }


section to_Z

variables [succ_order ι] [is_succ_archimedean ι] [pred_order ι] {i0 i : ι}

/-- `to_Z` numbers elements of `ι` according to their order, starting from `i0`. We prove in
`order_iso_range_to_Z_of_linear_succ_pred_arch` that this defines an `order_iso` between `ι` and
the range of `to_Z`. -/
def to_Z (i0 i : ι) : ℤ :=
dite (i0 ≤ i) (λ hi, nat.find (exists_succ_iterate_of_le hi))
  (λ hi, - nat.find (exists_pred_iterate_of_le (not_le.mp hi).le))

lemma to_Z_of_ge (hi : i0 ≤ i) : to_Z i0 i = nat.find (exists_succ_iterate_of_le hi) := dif_pos hi

lemma to_Z_of_lt (hi : i < i0) : to_Z i0 i = - nat.find (exists_pred_iterate_of_le hi.le) :=
dif_neg (not_le.mpr hi)

@[simp] lemma to_Z_of_eq : to_Z i0 i0 = 0 :=
begin
  rw to_Z_of_ge le_rfl,
  norm_cast,
  refine le_antisymm (nat.find_le _) (zero_le _),
  rw [function.iterate_zero, id.def],
end

lemma iterate_succ_to_Z (i : ι) (hi : i0 ≤ i) : succ^[(to_Z i0 i).to_nat] i0 = i :=
by { rw [to_Z_of_ge hi, int.to_nat_coe_nat], exact nat.find_spec (exists_succ_iterate_of_le hi), }

lemma iterate_pred_to_Z (i : ι) (hi : i < i0) : pred^[(- to_Z i0 i).to_nat] i0 = i :=
begin
  rw [to_Z_of_lt hi, neg_neg, int.to_nat_coe_nat],
  exact nat.find_spec (exists_pred_iterate_of_le hi.le),
end

lemma to_Z_nonneg (hi : i0 ≤ i) : 0 ≤ to_Z i0 i :=
by { rw to_Z_of_ge hi, exact nat.cast_nonneg _, }

lemma to_Z_neg (hi : i < i0) : to_Z i0 i < 0 :=
begin
  refine lt_of_le_of_ne _ _,
  { rw [to_Z_of_lt hi, neg_nonpos], exact nat.cast_nonneg _, },
  { by_contra,
    have h_eq := iterate_pred_to_Z i hi,
    rw [← h_eq, h] at hi,
    simpa only [neg_zero, int.to_nat_zero, function.iterate_zero, id.def, lt_self_iff_false]
      using hi, },
end

lemma to_Z_iterate_succ_le (n : ℕ) : to_Z i0 (succ^[n] i0) ≤ n :=
begin
  rw to_Z_of_ge (le_succ_iterate _ _),
  norm_cast,
  exact nat.find_min' (exists_succ_iterate_of_le _) rfl,
end

lemma to_Z_iterate_pred_ge (n : ℕ) : -(n : ℤ) ≤ to_Z i0 (pred^[n] i0) :=
begin
  cases le_or_lt i0 (pred^[n] i0) with h h,
  { have h_eq : (pred^[n] i0) = i0 := le_antisymm (pred_iterate_le _ _) h,
    rw [h_eq, to_Z_of_eq],
    simp only [right.neg_nonpos_iff, nat.cast_nonneg],},
  { rw [to_Z_of_lt h, neg_le_neg_iff],
    norm_cast,
    exact nat.find_min' (exists_pred_iterate_of_le _) rfl, },
end

lemma to_Z_iterate_succ_of_not_is_max (n : ℕ) (hn : ¬ is_max (succ^[n] i0)) :
  to_Z i0 (succ^[n] i0) = n :=
begin
  let m := (to_Z i0 (succ^[n] i0)).to_nat,
  have h_eq : (succ^[m] i0) = (succ^[n] i0) := iterate_succ_to_Z _ (le_succ_iterate _ _),
  by_cases hmn : m = n,
  { nth_rewrite 1 ← hmn,
    simp_rw [m],
    rw [int.to_nat_eq_max, to_Z_of_ge (le_succ_iterate _ _), max_eq_left],
    exact nat.cast_nonneg _, },
  suffices : is_max (succ^[n] i0), from absurd this hn,
  exact is_max_iterate_succ_of_eq_of_ne h_eq.symm (ne.symm hmn),
end

lemma to_Z_iterate_pred_of_not_is_min (n : ℕ) (hn : ¬ is_min (pred^[n] i0)) :
  to_Z i0 (pred^[n] i0) = -n :=
begin
  cases n,
  { simp only [function.iterate_zero, id.def, to_Z_of_eq, nat.cast_zero, neg_zero], },
  have : (pred^[n.succ] i0) < i0,
  { refine lt_of_le_of_ne (pred_iterate_le _ _) (λ h_pred_iterate_eq, hn _),
    have h_pred_eq_pred : (pred^[n.succ] i0) = (pred^[0] i0),
    { rwa [function.iterate_zero, id.def], },
    exact is_min_iterate_pred_of_eq_of_ne h_pred_eq_pred (nat.succ_ne_zero n), },
  let m := (- to_Z i0 (pred^[n.succ] i0)).to_nat,
  have h_eq : (pred^[m] i0) = (pred^[n.succ] i0) := iterate_pred_to_Z _ this,
  by_cases hmn : m = n.succ,
  { nth_rewrite 1 ← hmn,
    simp_rw [m],
    rw [int.to_nat_eq_max, to_Z_of_lt this, max_eq_left, neg_neg],
    rw neg_neg,
    exact nat.cast_nonneg _, },
  { suffices : is_min (pred^[n.succ] i0), from absurd this hn,
    exact is_min_iterate_pred_of_eq_of_ne h_eq.symm (ne.symm hmn), },
end

lemma le_of_to_Z_le {j : ι} (h_le : to_Z i0 i ≤ to_Z i0 j) : i ≤ j :=
begin
  cases le_or_lt i0 i with hi hi; cases le_or_lt i0 j with hj hj,
  { rw [← iterate_succ_to_Z i hi, ← iterate_succ_to_Z j hj],
    exact monotone.monotone_iterate_of_le_map succ_mono (le_succ _) (int.to_nat_le_to_nat h_le), },
  { exact absurd ((to_Z_neg hj).trans_le (to_Z_nonneg hi)) (not_lt.mpr h_le), },
  { exact hi.le.trans hj, },
  { rw [← iterate_pred_to_Z i hi, ← iterate_pred_to_Z j hj],
    refine monotone.antitone_iterate_of_map_le pred_mono (pred_le _) (int.to_nat_le_to_nat _),
    exact neg_le_neg h_le, },
end

lemma to_Z_mono {i j : ι} (h_le : i ≤ j) : to_Z i0 i ≤ to_Z i0 j :=
begin
  by_cases hi_max : is_max i,
  { rw le_antisymm h_le (hi_max h_le), },
  by_cases hj_min : is_min j,
  { rw le_antisymm h_le (hj_min h_le), },
  cases le_or_lt i0 i with hi hi; cases le_or_lt i0 j with hj hj,
  { let m := nat.find (exists_succ_iterate_of_le h_le),
    have hm : (succ^[m] i = j) := nat.find_spec (exists_succ_iterate_of_le h_le),
    have hj_eq : j = (succ^[(to_Z i0 i).to_nat + m] i0),
    { rw [← hm, add_comm],
      nth_rewrite 0 ← iterate_succ_to_Z i hi,
      rw function.iterate_add, },
    by_contra h,
    push_neg at h,
    by_cases hm0 : m = 0,
    { rw [hm0, function.iterate_zero, id.def] at hm,
      rw hm at h,
      exact lt_irrefl _ h, },
    refine hi_max (max_of_succ_le (le_trans _ (@le_of_to_Z_le _ _ _ _ _ i0 _ _ _))),
    { exact j, },
    { have h_succ_le : (succ^[(to_Z i0 i).to_nat + 1] i0) ≤ j,
      { rw hj_eq,
        refine monotone.monotone_iterate_of_le_map succ_mono (le_succ i0) (add_le_add_left _ _),
        exact nat.one_le_iff_ne_zero.mpr hm0, },
      rwa [function.iterate_succ', function.comp_app, iterate_succ_to_Z i hi] at h_succ_le, },
    { exact h.le, }, },
  { exact absurd h_le (not_le.mpr (hj.trans_le hi)), },
  { exact (to_Z_neg hi).le.trans (to_Z_nonneg hj), },
  { let m := nat.find (exists_pred_iterate_of_le h_le),
    have hm : (pred^[m] j = i) := nat.find_spec (exists_pred_iterate_of_le h_le),
    have hj_eq : i = (pred^[(-to_Z i0 j).to_nat + m] i0),
    { rw [← hm, add_comm],
      nth_rewrite 0 ← iterate_pred_to_Z j hj,
      rw function.iterate_add, },
    by_contra h,
    push_neg at h,
    by_cases hm0 : m = 0,
    { rw [hm0, function.iterate_zero, id.def] at hm,
      rw hm at h,
      exact lt_irrefl _ h, },
    refine hj_min (min_of_le_pred _),
    refine (@le_of_to_Z_le _ _ _ _ _ i0 _ _ _).trans _,
    { exact i, },
    { exact h.le, },
    { have h_le_pred : i ≤ (pred^[(-to_Z i0 j).to_nat + 1] i0),
      { rw hj_eq,
        refine monotone.antitone_iterate_of_map_le pred_mono (pred_le i0) (add_le_add_left _ _),
        exact nat.one_le_iff_ne_zero.mpr hm0, },
      rwa [function.iterate_succ', function.comp_app, iterate_pred_to_Z j hj]
        at h_le_pred, }, },
end

lemma to_Z_le_iff (i j : ι) : to_Z i0 i ≤ to_Z i0 j ↔ i ≤ j :=
⟨le_of_to_Z_le, to_Z_mono⟩

lemma to_Z_iterate_succ [no_max_order ι] (n : ℕ) : to_Z i0 (succ^[n] i0) = n :=
to_Z_iterate_succ_of_not_is_max n (not_is_max _)

lemma to_Z_iterate_pred [no_min_order ι] (n : ℕ) : to_Z i0 (pred^[n] i0) = -n :=
to_Z_iterate_pred_of_not_is_min n (not_is_min _)

lemma injective_to_Z : function.injective (to_Z i0) :=
λ i j hij, le_antisymm (le_of_to_Z_le hij.le) (le_of_to_Z_le hij.symm.le)

end to_Z

section order_iso

variables [succ_order ι] [pred_order ι] [is_succ_archimedean ι]

/-- `to_Z` defines an `order_iso` between `ι` and its range. -/
noncomputable
def order_iso_range_to_Z_of_linear_succ_pred_arch [hι : nonempty ι] :
  ι ≃o set.range (to_Z hι.some) :=
{ to_equiv := equiv.of_injective _ injective_to_Z,
  map_rel_iff' := to_Z_le_iff, }

@[priority 100]
instance countable_of_linear_succ_pred_arch : countable ι :=
begin
  casesI is_empty_or_nonempty ι with _ hι,
  { apply_instance, },
  { exact countable.of_equiv _ (order_iso_range_to_Z_of_linear_succ_pred_arch).symm.to_equiv, },
end

/-- If the order has neither bot nor top, `to_Z` defines an `order_iso` between `ι` and `ℤ`. -/
noncomputable
def order_iso_int_of_linear_succ_pred_arch [no_max_order ι] [no_min_order ι] [hι : nonempty ι] :
  ι ≃o ℤ :=
{ to_fun := to_Z hι.some,
  inv_fun := λ n, if 0 ≤ n then (succ^[n.to_nat] hι.some) else (pred^[(-n).to_nat] hι.some),
  left_inv := λ i,
  begin
    cases le_or_lt hι.some i with hi hi,
    { have h_nonneg : 0 ≤ to_Z hι.some i := to_Z_nonneg hi,
      simp_rw if_pos h_nonneg,
      exact iterate_succ_to_Z i hi, },
    { have h_neg : to_Z hι.some i < 0 := to_Z_neg hi,
      simp_rw if_neg (not_le.mpr h_neg),
      exact iterate_pred_to_Z i hi, },
  end,
  right_inv := λ n,
  begin
    cases le_or_lt 0 n with hn hn,
    { simp_rw if_pos hn,
      rw to_Z_iterate_succ,
      exact int.to_nat_of_nonneg hn, },
    { simp_rw if_neg (not_le.mpr hn),
      rw to_Z_iterate_pred,
      simp only [hn.le, int.to_nat_of_nonneg, right.nonneg_neg_iff, neg_neg], },
  end,
  map_rel_iff' := to_Z_le_iff, }

/-- If the order has a bot but no top, `to_Z` defines an `order_iso` between `ι` and `ℕ`. -/
def order_iso_nat_of_linear_succ_pred_arch [no_max_order ι] [order_bot ι] :
  ι ≃o ℕ :=
{ to_fun := λ i, (to_Z ⊥ i).to_nat,
  inv_fun := λ n, succ^[n] ⊥,
  left_inv := λ i, by { simp_rw if_pos (to_Z_nonneg bot_le), exact iterate_succ_to_Z i bot_le, },
  right_inv := λ n,
  begin
    simp_rw if_pos bot_le,
    rw to_Z_iterate_succ,
    exact int.to_nat_coe_nat n,
  end,
  map_rel_iff' := λ i j,
  begin
    simp only [equiv.coe_fn_mk, int.to_nat_le],
    rw [← @to_Z_le_iff ι _ _ _ _ ⊥, int.to_nat_of_nonneg (to_Z_nonneg bot_le)],
  end, }

/-- If the order has both a bot and a top, `to_Z` gives an `order_iso` between `ι` and
`finset.range n` for some `n`. -/
def order_iso_range_of_linear_succ_pred_arch [order_bot ι] [order_top ι] :
  ι ≃o finset.range ((to_Z ⊥ (⊤ : ι)).to_nat + 1) :=
{ to_fun := λ i, ⟨(to_Z ⊥ i).to_nat,
    finset.mem_range_succ_iff.mpr (int.to_nat_le_to_nat ((to_Z_le_iff _ _).mpr le_top))⟩,
  inv_fun := λ n, succ^[n] ⊥,
  left_inv := λ i, iterate_succ_to_Z i bot_le,
  right_inv := λ n, begin
    ext1,
    simp only [subtype.coe_mk],
    refine le_antisymm _ _,
    { rw int.to_nat_le,
      exact (to_Z_iterate_succ_le _), },
    by_cases hn_max : is_max (succ^[↑n] (⊥ : ι)),
    { rw [← is_top_iff_is_max, is_top_iff_eq_top] at hn_max,
      rw hn_max,
      exact nat.lt_succ_iff.mp (finset.mem_range.mp n.prop), },
    { rw to_Z_iterate_succ_of_not_is_max _ hn_max,
      simp only [int.to_nat_coe_nat], },
  end,
  map_rel_iff' := λ i j,
  begin
    simp only [equiv.coe_fn_mk, subtype.mk_le_mk, int.to_nat_le],
    rw [← @to_Z_le_iff ι _ _ _ _ ⊥, int.to_nat_of_nonneg (to_Z_nonneg bot_le)],
  end, }

end order_iso

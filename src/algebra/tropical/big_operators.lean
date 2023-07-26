/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import algebra.big_operators.basic
import data.list.min_max
import algebra.tropical.basic
import order.conditionally_complete_lattice.finset

/-!

# Tropicalization of finitary operations

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides the "big-op" or notation-based finitary operations on tropicalized types.
This allows easy conversion between sums to Infs and prods to sums. Results here are important
for expressing that evaluation of tropical polynomials are the minimum over a finite piecewise
collection of linear functions.

## Main declarations

* `untrop_sum`

## Implementation notes

No concrete (semi)ring is used here, only ones with inferrable order/lattice structure, to support
real, rat, ereal, and others (erat is not yet defined).

Minima over `list α` are defined as producing a value in `with_top α` so proofs about lists do not
directly transfer to minima over multisets or finsets.

-/


open_locale big_operators

variables {R S : Type*}

open tropical finset

lemma list.trop_sum [add_monoid R] (l : list R) : trop l.sum = list.prod (l.map trop) :=
begin
  induction l with hd tl IH,
  { simp },
  { simp [←IH] }
end

lemma multiset.trop_sum [add_comm_monoid R] (s : multiset R) :
  trop s.sum = multiset.prod (s.map trop) :=
quotient.induction_on s (by simpa using list.trop_sum)

lemma trop_sum [add_comm_monoid R] (s : finset S) (f : S → R) :
  trop (∑ i in s, f i) = ∏ i in s, trop (f i) :=
begin
  cases s,
  convert multiset.trop_sum _,
  simp
end

lemma list.untrop_prod [add_monoid R] (l : list (tropical R)) :
  untrop l.prod = list.sum (l.map untrop) :=
begin
  induction l with hd tl IH,
  { simp },
  { simp [←IH] }
end

lemma multiset.untrop_prod [add_comm_monoid R] (s : multiset (tropical R)) :
  untrop s.prod = multiset.sum (s.map untrop) :=
quotient.induction_on s (by simpa using list.untrop_prod)

lemma untrop_prod [add_comm_monoid R] (s : finset S) (f : S → tropical R) :
  untrop (∏ i in s, f i) = ∑ i in s, untrop (f i) :=
begin
  cases s,
  convert multiset.untrop_prod _,
  simp
end

lemma list.trop_minimum [linear_order R] (l : list R) :
  trop l.minimum = list.sum (l.map (trop ∘ coe)) :=
begin
  induction l with hd tl IH,
  { simp },
  { simp [list.minimum_cons, ←IH] }
end

lemma multiset.trop_inf [linear_order R] [order_top R] (s : multiset R) :
  trop s.inf = multiset.sum (s.map trop) :=
begin
  induction s using multiset.induction with s x IH,
  { simp },
  { simp [←IH] }
end

lemma finset.trop_inf [linear_order R] [order_top R] (s : finset S) (f : S → R) :
  trop (s.inf f) = ∑ i in s, trop (f i) :=
begin
  cases s,
  convert multiset.trop_inf _,
  simp
end

lemma trop_Inf_image [conditionally_complete_linear_order R] (s : finset S)
  (f : S → with_top R) : trop (Inf (f '' s)) = ∑ i in s, trop (f i) :=
begin
  rcases s.eq_empty_or_nonempty with rfl|h,
  { simp only [set.image_empty, coe_empty, sum_empty, with_top.cInf_empty, trop_top] },
  rw [←inf'_eq_cInf_image _ h, inf'_eq_inf, s.trop_inf],
end

lemma trop_infi [conditionally_complete_linear_order R] [fintype S] (f : S → with_top R) :
  trop (⨅ (i : S), f i) = ∑ (i : S), trop (f i) :=
by rw [infi, ←set.image_univ, ←coe_univ, trop_Inf_image]

lemma multiset.untrop_sum [linear_order R] [order_top R] (s : multiset (tropical R)) :
  untrop s.sum = multiset.inf (s.map untrop) :=
begin
  induction s using multiset.induction with s x IH,
  { simp },
  { simpa [←IH] }
end

lemma finset.untrop_sum' [linear_order R] [order_top R] (s : finset S)
  (f : S → tropical R) : untrop (∑ i in s, f i) = s.inf (untrop ∘ f) :=
begin
  cases s,
  convert multiset.untrop_sum _,
  simpa
end

lemma untrop_sum_eq_Inf_image [conditionally_complete_linear_order R] (s : finset S)
  (f : S → tropical (with_top R)) :
  untrop (∑ i in s, f i) = Inf (untrop ∘ f '' s) :=
begin
  rcases s.eq_empty_or_nonempty with rfl|h,
  { simp only [set.image_empty, coe_empty, sum_empty, with_top.cInf_empty, untrop_zero] },
  rw [←inf'_eq_cInf_image _ h, inf'_eq_inf, finset.untrop_sum'],
end

lemma untrop_sum [conditionally_complete_linear_order R] [fintype S]
  (f : S → tropical (with_top R)) :
  untrop (∑ i : S, f i) = ⨅ i : S, untrop (f i) :=
by rw [infi, ←set.image_univ, ←coe_univ, untrop_sum_eq_Inf_image]

/-- Note we cannot use `i ∈ s` instead of `i : s` here
as it is simply not true on conditionally complete lattices! -/
lemma finset.untrop_sum [conditionally_complete_linear_order R] (s : finset S)
  (f : S → tropical (with_top R)) : untrop (∑ i in s, f i) = ⨅ i : s, untrop (f i) :=
by simpa [←untrop_sum] using sum_attach.symm

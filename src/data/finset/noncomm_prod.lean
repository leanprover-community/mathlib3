/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/

import data.finset.fold

/-!
# Products (respectively, sums) over a finset or a multiset.

The regular `finset.prod` and `multiset.prod` require `[comm_monoid α]`.
Often, there are collections `s : finset α` where `[monoid α]` and we know,
in a dependent fashion, that for all the terms `∀ (x ∈ s) (y ∈ s), commute x y`.
This allows to still have a well-defined product over `s`.

## Main definitions

- `finset.noncomm_prod`, requiring a proof of commutativity of held terms
- `multiset.noncomm_prod`, requiring a proof of commutativity of held terms

## Implementation details

The commutativity proof required has a somewhat unnecessary `x ≠ y` hypothesis.
It is unnecesary because `commute x x` is true by reflexivity. The `x ≠ y` hypothesis
is included to facilitate usage with `set.pairwise_on`, or in helping with implications
that deal with `disjoint`.

-/

variables {α : Type*} [monoid α]

namespace multiset

/-- Product of a `s : multiset α` with `[monoid α]`, given a proof that `*` commutes
on all elements `x ∈ s`. -/
@[to_additive "Sum of a `s : multiset α` with `[add_monoid α]`, given a proof that `*` commutes
on all elements `x ∈ s`." ]
def noncomm_prod : Π (s : multiset α) (comm : ∀ (x ∈ s) (y ∈ s) (h : x ≠ y), commute x y), α :=
λ s, quotient.hrec_on s (λ l h, l.prod)
  (λ l l' (h : l ~ l'),
    begin
      ext,
      { refine forall_congr (λ x, _),
        refine imp_congr h.mem_iff _,
        refine forall_congr (λ y, _),
        exact imp_congr h.mem_iff iff.rfl },
      { intros hl hl' _,
        rw heq_iff_eq,
        refine h.prod_eq' _,
        rw list.pairwise.imp_mem,
        refine list.pairwise_of_forall _,
        intros x y hx hy,
        by_cases hxy : x = y,
        { subst hxy },
        { exact hl x hx y hy hxy } }
    end)

@[simp, to_additive] lemma noncomm_prod_coe (l : list α) (comm) :
  noncomm_prod (l : multiset α) comm = l.prod := rfl

@[to_additive]
lemma noncomm_prod_congr_list_prod (s : multiset α) (l : list α) (comm) (hl : s = l) :
  s.noncomm_prod comm = l.prod :=
begin
  induction s using quotient.induction_on,
  simp only [quot_mk_to_coe, coe_eq_coe] at hl,
  simp only [quot_mk_to_coe, noncomm_prod_coe],
  refine hl.prod_eq' _,
  rw list.pairwise.imp_mem,
  refine list.pairwise_of_forall _,
  intros x y hx hy,
  by_cases hxy : x = y,
  { subst hxy },
  { exact comm _ hx _ hy hxy }
end

@[simp, to_additive] lemma noncomm_prod_empty (h) :
  noncomm_prod (0 : multiset α) h = 1 := rfl

@[simp, to_additive] lemma noncomm_prod_cons (s : multiset α) (a : α) (comm) :
  noncomm_prod (a ::ₘ s) comm = a * noncomm_prod s
    (λ x hx y hy, comm _ (mem_cons_of_mem hx) _ (mem_cons_of_mem hy)) :=
begin
  induction s using quotient.induction_on,
  simp
end

@[to_additive] lemma noncomm_prod_cons' (s : multiset α) (a : α) (comm) :
  noncomm_prod (a ::ₘ s) comm = noncomm_prod s
    (λ x hx y hy, comm _ (mem_cons_of_mem hx) _ (mem_cons_of_mem hy)) * a :=
begin
  induction s using quotient.induction_on with s,
  simp only [quot_mk_to_coe, cons_coe, noncomm_prod_coe, list.prod_cons],
  induction s with hd tl IH,
  { simp },
  { rw [list.prod_cons, mul_assoc, ←IH, ←mul_assoc, ←mul_assoc],
    { congr' 1,
      by_cases ha : a = hd,
      { subst ha },
      { refine comm _ _ _ _ ha,
        { simp },
        { simp } } },
    { intros x hx y hy,
      simp only [quot_mk_to_coe, list.mem_cons_iff, mem_coe, cons_coe] at hx hy,
      apply comm,
      { cases hx;
        simp [hx] },
      { cases hy;
        simp [hy] } } }
end

end multiset

namespace finset

/-- Product of a `s : finset α` with `[monoid α`], given a proof that `*` commutes
on all elements `x ∈ s`. -/
@[to_additive "Sum of a `s : finset α` with `[add_monoid α`], given a proof that `*` commutes
on all elements `x ∈ s`."]
def noncomm_prod (s : finset α) (comm) : α :=
s.1.noncomm_prod comm

@[simp, to_additive] lemma noncomm_prod_to_finset [decidable_eq α] (l : list α)
  (comm) (hl : l.nodup) :
  noncomm_prod l.to_finset comm = l.prod :=
begin
  rw ←list.erase_dup_eq_self at hl,
  simp [noncomm_prod, hl]
end

@[to_additive]
lemma noncomm_prod_congr_list_prod [decidable_eq α] (s : finset α) (l : list α)
  (comm) (hl : s = l.to_finset) (hn : l.nodup) :
  s.noncomm_prod comm = l.prod :=
begin
  rw noncomm_prod,
  rw ←list.erase_dup_eq_self at hn,
  refine multiset.noncomm_prod_congr_list_prod _ _ _ _,
  simp [hl, hn]
end

@[simp, to_additive] lemma noncomm_prod_empty (h) :
  noncomm_prod (∅ : finset α) h = 1 := rfl

@[simp, to_additive] lemma noncomm_prod_insert_of_not_mem [decidable_eq α] (s : finset α) (a : α)
  (comm) (ha : a ∉ s) :
  noncomm_prod (insert a s) comm = a * noncomm_prod s
    (λ x hx y hy, comm _ (mem_insert_of_mem hx) _ (mem_insert_of_mem hy)) :=
by simp [insert_val_of_not_mem ha, noncomm_prod]

@[to_additive] lemma noncomm_prod_insert_of_not_mem' [decidable_eq α] (s : finset α) (a : α)
  (comm) (ha : a ∉ s) :
  noncomm_prod (insert a s) comm = noncomm_prod s
    (λ x hx y hy, comm _ (mem_insert_of_mem hx) _ (mem_insert_of_mem hy)) * a :=
by simp only [noncomm_prod, insert_val_of_not_mem ha, multiset.noncomm_prod_cons']

end finset

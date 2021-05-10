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

While `list.prod` is defined via `list.foldl`, `noncomm_prod` is defined via
`list.foldr` for neater proofs and definitions. By the commutativity assumption,
the two must be equal.

-/

variables {α β : Type*} (f : α → β → β) (op : α → α → α)

namespace multiset

/-- Fold of a `s : multiset α` with `f : α → β → β`, given a proof that `left_commutative f`
on all elements `x ∈ s`. -/
def noncomm_foldr (s : multiset α) (comm) (b : β) : β :=
s.attach.foldr (f ∘ subtype.val) comm b

@[simp] lemma noncomm_foldr_coe (l : list α) (comm) (b : β) :
  noncomm_foldr f (l : multiset α) comm b = l.foldr f b :=
begin
  simp only [noncomm_foldr, coe_foldr, coe_attach, list.attach],
  rw ←list.foldr_map,
  simp [list.map_pmap, list.pmap_eq_map]
end

@[simp] lemma noncomm_foldr_empty (h) (b : β) :
  noncomm_foldr f (0 : multiset α) h b = b := rfl

lemma noncomm_foldr_cons (s : multiset α) (a : α) (h) (h') (b : β) :
  noncomm_foldr f (a ::ₘ s) h b = f a (noncomm_foldr f s h' b) :=
begin
  induction s using quotient.induction_on,
  simp
end

/-- Fold of a `s : multiset α` with `op : α → α → α`, given a proof that `left_commutative op`
on all elements `x ∈ s`. -/
def noncomm_fold (s : multiset α) (comm) (a : α) : α :=
noncomm_foldr op s comm a
-- s.attach.foldr (f ∘ subtype.val) comm a

@[simp] lemma noncomm_fold_coe (l : list α) (comm) (a : α) :
  noncomm_fold op (l : multiset α) comm a = l.foldr op a :=
by simp [noncomm_fold]

@[simp] lemma noncomm_fold_empty (h) (a : α) :
  noncomm_fold op (0 : multiset α) h a = a := rfl

lemma noncomm_fold_cons (s : multiset α) (a : α) (h) (h') (x : α) :
  noncomm_fold op (a ::ₘ s) h x = op a (noncomm_fold op s h' x) :=
begin
  induction s using quotient.induction_on,
  simp
end

variables [monoid α]

/-- Product of a `s : multiset α` with `[monoid α]`, given a proof that `*` commutes
on all elements `x ∈ s`. -/
@[to_additive "Sum of a `s : multiset α` with `[add_monoid α]`, given a proof that `*` commutes
on all elements `x ∈ s`." ]
def noncomm_prod (s : multiset α) (comm : ∀ (x ∈ s) (y ∈ s), commute x y) : α :=
s.noncomm_fold (*) (begin
    rintro ⟨x, hx⟩ ⟨y, hy⟩ b',
    simp [←mul_assoc, (comm x hx y hy).eq]
  end) 1

@[simp, to_additive] lemma noncomm_prod_coe (l : list α) (comm) :
  noncomm_prod (l : multiset α) comm = l.prod :=
begin
  rw [noncomm_prod],
  simp only [noncomm_fold_coe],
  induction l with hd tl hl,
  { simp },
  { rw [list.prod_cons, list.foldr, hl],
    intros x hx y hy,
    exact comm x (list.mem_cons_of_mem _ hx) y (list.mem_cons_of_mem _ hy) }
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
      apply comm;
      simp },
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

variables [monoid α]

/-- Product of a `s : finset α` with `[monoid α]`, given a proof that `*` commutes
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

@[simp, to_additive] lemma noncomm_prod_singleton (a : α) :
  noncomm_prod ({a} : finset α)
    (λ x hx y hy, by rw [mem_singleton.mp hx, mem_singleton.mp hy]) = a :=
by simp [noncomm_prod]

end finset

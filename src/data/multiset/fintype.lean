/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import algebra.big_operators.basic
import data.fintype.card
import data.prod.lex

/-!
# Multiset coercion to type

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This module defines a `has_coe_to_sort` instance for multisets and gives it a `fintype` instance.
It also defines `multiset.to_enum_finset`, which is another way to enumerate the elements of
a multiset. These coercions and definitions make it easier to sum over multisets using existing
`finset` theory.

## Main definitions

* A coercion from `m : multiset α` to a `Type*`. For `x : m`, then there is a coercion `↑x : α`,
  and `x.2` is a term of `fin (m.count x)`. The second component is what ensures each term appears
  with the correct multiplicity. Note that this coercion requires `decidable_eq α` due to
  `multiset.count`.
* `multiset.to_enum_finset` is a `finset` version of this.
* `multiset.coe_embedding` is the embedding `m ↪ α × ℕ`, whose first component is the coercion
  and whose second component enumerates elements with multiplicity.
* `multiset.coe_equiv` is the equivalence `m ≃ m.to_enum_finset`.

## Tags

multiset enumeration
-/

open_locale big_operators

variables {α : Type*} [decidable_eq α] {m : multiset α}

/-- Auxiliary definition for the `has_coe_to_sort` instance. This prevents the `has_coe m α`
instance from inadverently applying to other sigma types. One should not use this definition
directly. -/
@[nolint has_nonempty_instance]
def multiset.to_type (m : multiset α) : Type* := Σ (x : α), fin (m.count x)

/-- Create a type that has the same number of elements as the multiset.
Terms of this type are triples `⟨x, ⟨i, h⟩⟩` where `x : α`, `i : ℕ`, and `h : i < m.count x`.
This way repeated elements of a multiset appear multiple times with different values of `i`. -/
instance : has_coe_to_sort (multiset α) Type* := ⟨multiset.to_type⟩

@[simp] lemma multiset.coe_sort_eq : m.to_type = m := rfl

/-- Constructor for terms of the coercion of `m` to a type.
This helps Lean pick up the correct instances. -/
@[reducible, pattern] def multiset.mk_to_type (m : multiset α) (x : α) (i : fin (m.count x)) : m :=
⟨x, i⟩

/-- As a convenience, there is a coercion from `m : Type*` to `α` by projecting onto the first
component. -/
instance multiset.has_coe_to_sort.has_coe : has_coe m α := ⟨λ x, x.1⟩

@[simp] lemma multiset.fst_coe_eq_coe {x : m} : x.1 = x := rfl

@[simp] lemma multiset.coe_eq {x y : m} : (x : α) = (y : α) ↔ x.1 = y.1 :=
by { cases x, cases y, refl }

@[simp] lemma multiset.coe_mk {x : α} {i : fin (m.count x)} : ↑(m.mk_to_type x i) = x := rfl

@[simp] lemma multiset.coe_mem {x : m} : ↑x ∈ m := multiset.count_pos.mp (pos_of_gt x.2.2)

@[simp] protected lemma multiset.forall_coe (p : m → Prop) :
  (∀ (x : m), p x) ↔ ∀ (x : α) (i : fin (m.count x)), p ⟨x, i⟩ := sigma.forall

@[simp] protected lemma multiset.exists_coe (p : m → Prop) :
  (∃ (x : m), p x) ↔ ∃ (x : α) (i : fin (m.count x)), p ⟨x, i⟩ := sigma.exists

instance : fintype {p : α × ℕ | p.2 < m.count p.1} :=
fintype.of_finset
(m.to_finset.bUnion (λ x, (finset.range (m.count x)).map ⟨prod.mk x, prod.mk.inj_left x⟩))
begin
  rintro ⟨x, i⟩,
  simp only [finset.mem_bUnion, multiset.mem_to_finset, finset.mem_map, finset.mem_range,
    function.embedding.coe_fn_mk, prod.mk.inj_iff, exists_prop, exists_eq_right_right,
    set.mem_set_of_eq, and_iff_right_iff_imp],
  exact λ h, multiset.count_pos.mp (pos_of_gt h),
end

/-- Construct a finset whose elements enumerate the elements of the multiset `m`.
The `ℕ` component is used to differentiate between equal elements: if `x` appears `n` times
then `(x, 0)`, ..., and `(x, n-1)` appear in the `finset`. -/
def multiset.to_enum_finset (m : multiset α) : finset (α × ℕ) :=
{p : α × ℕ | p.2 < m.count p.1}.to_finset

@[simp] lemma multiset.mem_to_enum_finset (m : multiset α) (p : α × ℕ) :
  p ∈ m.to_enum_finset ↔ p.2 < m.count p.1 :=
set.mem_to_finset

lemma multiset.mem_of_mem_to_enum_finset {p : α × ℕ} (h : p ∈ m.to_enum_finset) : p.1 ∈ m :=
multiset.count_pos.mp $ pos_of_gt $ (m.mem_to_enum_finset p).mp h

@[mono]
lemma multiset.to_enum_finset_mono {m₁ m₂ : multiset α}
  (h : m₁ ≤ m₂) : m₁.to_enum_finset ⊆ m₂.to_enum_finset :=
begin
  intro p,
  simp only [multiset.mem_to_enum_finset],
  exact gt_of_ge_of_gt (multiset.le_iff_count.mp h p.1),
end

@[simp] lemma multiset.to_enum_finset_subset_iff {m₁ m₂ : multiset α} :
  m₁.to_enum_finset ⊆ m₂.to_enum_finset ↔ m₁ ≤ m₂ :=
begin
  refine ⟨λ h, _, multiset.to_enum_finset_mono⟩,
  rw multiset.le_iff_count,
  intro x,
  by_cases hx : x ∈ m₁,
  { apply nat.le_of_pred_lt,
    have : (x, m₁.count x - 1) ∈ m₁.to_enum_finset,
    { rw multiset.mem_to_enum_finset,
      exact nat.pred_lt (ne_of_gt (multiset.count_pos.mpr hx)), },
    simpa only [multiset.mem_to_enum_finset] using h this, },
  { simp [hx] },
end

/-- The embedding from a multiset into `α × ℕ` where the second coordinate enumerates repeats.

If you are looking for the function `m → α`, that would be plain `coe`. -/
@[simps]
def multiset.coe_embedding (m : multiset α) :
  m ↪ α × ℕ :=
{ to_fun := λ x, (x, x.2),
  inj' := begin
    rintro ⟨x, i, hi⟩ ⟨y, j, hj⟩,
    simp only [prod.mk.inj_iff, sigma.mk.inj_iff, and_imp, multiset.coe_eq, fin.coe_mk],
    rintro rfl rfl,
    exact ⟨rfl, heq.rfl⟩
  end }

/-- Another way to coerce a `multiset` to a type is to go through `m.to_enum_finset` and coerce
that `finset` to a type. -/
@[simps]
def multiset.coe_equiv (m : multiset α) :
  m ≃ m.to_enum_finset :=
{ to_fun := λ x, ⟨m.coe_embedding x, by { rw multiset.mem_to_enum_finset, exact x.2.2 }⟩,
  inv_fun := λ x, ⟨x.1.1, x.1.2, by { rw ← multiset.mem_to_enum_finset, exact x.2 }⟩,
  left_inv := by { rintro ⟨x, i, h⟩, refl },
  right_inv := by {rintro ⟨⟨x, i⟩, h⟩, refl } }

@[simp] lemma multiset.to_embedding_coe_equiv_trans (m : multiset α) :
  m.coe_equiv.to_embedding.trans (function.embedding.subtype _) = m.coe_embedding :=
by ext; simp

instance multiset.fintype_coe : fintype m :=
fintype.of_equiv m.to_enum_finset m.coe_equiv.symm

lemma multiset.map_univ_coe_embedding (m : multiset α) :
  (finset.univ : finset m).map m.coe_embedding = m.to_enum_finset :=
by { ext ⟨x, i⟩, simp only [fin.exists_iff, finset.mem_map, finset.mem_univ,
  multiset.coe_embedding_apply, prod.mk.inj_iff, exists_true_left, multiset.exists_coe,
  multiset.coe_mk, fin.coe_mk, exists_prop, exists_eq_right_right, exists_eq_right,
  multiset.mem_to_enum_finset, iff_self, true_and] }

lemma multiset.to_enum_finset_filter_eq (m : multiset α) (x : α) :
  m.to_enum_finset.filter (λ p, x = p.1) =
  (finset.range (m.count x)).map ⟨prod.mk x, prod.mk.inj_left x⟩ :=
begin
  ext ⟨y, i⟩,
  simp only [eq_comm, finset.mem_filter, multiset.mem_to_enum_finset, finset.mem_map,
    finset.mem_range, function.embedding.coe_fn_mk, prod.mk.inj_iff, exists_prop,
    exists_eq_right_right', and.congr_left_iff],
  rintro rfl,
  refl,
end

@[simp] lemma multiset.map_to_enum_finset_fst (m : multiset α) :
  m.to_enum_finset.val.map prod.fst = m :=
begin
  ext x,
  simp only [multiset.count_map, ← finset.filter_val, multiset.to_enum_finset_filter_eq,
    finset.map_val, finset.range_val, multiset.card_map, multiset.card_range],
end

@[simp] lemma multiset.image_to_enum_finset_fst (m : multiset α) :
  m.to_enum_finset.image prod.fst = m.to_finset :=
by rw [finset.image, multiset.map_to_enum_finset_fst]

@[simp] lemma multiset.map_univ_coe (m : multiset α) :
  (finset.univ : finset m).val.map coe = m :=
begin
  have := m.map_to_enum_finset_fst,
  rw ← m.map_univ_coe_embedding at this,
  simpa only [finset.map_val, multiset.coe_embedding_apply, multiset.map_map, function.comp_app]
    using this,
end

@[simp] lemma multiset.map_univ {β : Type*} (m : multiset α) (f : α → β) :
  (finset.univ : finset m).val.map (λ x, f x) = m.map f :=
by rw [← multiset.map_map, multiset.map_univ_coe]

@[simp] lemma multiset.card_to_enum_finset (m : multiset α) : m.to_enum_finset.card = m.card :=
begin
  change multiset.card _ = _,
  convert_to (m.to_enum_finset.val.map prod.fst).card = _,
  { rw multiset.card_map },
  { rw m.map_to_enum_finset_fst }
end

@[simp] lemma multiset.card_coe (m : multiset α) : fintype.card m = m.card :=
by { rw fintype.card_congr m.coe_equiv, simp }

@[to_additive]
lemma multiset.prod_eq_prod_coe [comm_monoid α] (m : multiset α) : m.prod = ∏ (x : m), x :=
by { congr, simp }

@[to_additive]
lemma multiset.prod_eq_prod_to_enum_finset [comm_monoid α] (m : multiset α) :
  m.prod = ∏ x in m.to_enum_finset, x.1 :=
by { congr, simp }

@[to_additive]
lemma multiset.prod_to_enum_finset {β : Type*} [comm_monoid β] (m : multiset α) (f : α → ℕ → β) :
  ∏ x in m.to_enum_finset, f x.1 x.2 = ∏ (x : m), f x x.2 :=
begin
  rw fintype.prod_equiv m.coe_equiv (λ x, f x x.2) (λ x, f x.1.1 x.1.2),
  { rw ← m.to_enum_finset.prod_coe_sort (λ x, f x.1 x.2),
    simp, },
  { simp }
end

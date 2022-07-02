/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import data.fintype.card
import algebra.big_operators

/-!
# Multiset coercion to type

This module defines a `has_coe_to_sort` instance for multisets and gives it a `fintype` instance.
It also defines `multiset.to_enum_finset`, which is another way to enumerate the elements of
a multiset. These coercions and definitions make it easier to sum over multisets using existing
`finset` theory.

## Tags

multiset enumeration
-/

open_locale big_operators

/-- Create a type that has the same number of elements as the multiset.
Terms of this type are triples `⟨x, ⟨i, h⟩⟩` where `x : α`, `i : ℕ`, and `i < m.count x`.
This way repeated elements of a multiset appear multiple times with different values of `i`. -/
instance {α : Type*} [decidable_eq α] : has_coe_to_sort (multiset α) Type* :=
⟨λ m, Σ (x : α), fin (m.count x)⟩

/-- As a convenience, there is a coercion from `m : Type*` to `α` by projecting onto the first
component. -/
instance multiset.has_coe_to_sort.has_coe {α : Type*} [decidable_eq α] (m : multiset α) :
  has_coe m α := ⟨λ x, x.1⟩

@[simp] lemma multiset.fst_coe_eq_coe {α : Type*} [decidable_eq α] (m : multiset α) (x : m) :
  x.1 = x := rfl

@[simp] lemma multiset.coe_eq {α : Type*} [decidable_eq α] {m : multiset α} {x y : m} :
  (x : α) = (y : α) ↔ x.1 = y.1 :=
by { cases x, cases y, refl }

@[simp]
lemma multiset.exists_coe {α : Type*} [decidable_eq α] (m : multiset α) (p : m → Prop) :
  (∃ (x : m), p x) ↔ ∃ (x : α) (i : ℕ) (h : i < m.count x), p ⟨x, i, h⟩ :=
begin
  split,
  { rintro ⟨⟨x, i, hx⟩, h⟩,
    exact ⟨x, i, hx, h⟩, },
  { rintro ⟨x, i, hx, h⟩,
    exact ⟨⟨x, i, hx⟩, h⟩, },
end

instance {α : Type*} [decidable_eq α] (m : multiset α) : fintype {p : α × ℕ | p.2 < m.count p.1} :=
fintype.of_finset
(m.to_finset.bUnion (λ x, (finset.range (m.count x)).map ⟨prod.mk x, prod.mk.inj_left x⟩))
begin
  rintro ⟨x, i⟩,
  simp only [finset.mem_bUnion, multiset.mem_to_finset, finset.mem_map, finset.mem_range,
    function.embedding.coe_fn_mk, prod.mk.inj_iff, exists_prop, exists_eq_right_right,
    set.mem_set_of_eq, and_iff_right_iff_imp],
  exact λ h, multiset.count_pos.mp (pos_of_gt h),
end

/-- The embedding from a multiset into `α × ℕ` where the second coordinate enumerates repeats. -/
@[simps]
def multiset.coe_embedding {α : Type*} [decidable_eq α] (m : multiset α) :
  m ↪ α × ℕ :=
{ to_fun := λ x, (x, x.2.1),
  inj' := begin
    rintro ⟨x, i, hi⟩ ⟨y, j, hj⟩,
    simp only [prod.mk.inj_iff, sigma.mk.inj_iff, and_imp, multiset.coe_eq],
    rintro rfl rfl,
    exact ⟨rfl, heq.rfl⟩
  end }

/-- Construct a finset whose elements enumerate the elements of the multiset `m`.
The `ℕ` component is used to differentiate between equal elements: if `x` appears `n` times
then `(x, 0)`, ..., `(x, n-1)` appear in the `finset`. -/
def multiset.to_enum_finset {α : Type*} [decidable_eq α] (m : multiset α) : finset (α × ℕ) :=
{p : α × ℕ | p.2 < m.count p.1}.to_finset

@[simp] lemma multiset.mem_to_enum_finset {α : Type*} [decidable_eq α]
  (m : multiset α) (p : α × ℕ) : p ∈ m.to_enum_finset ↔ p.2 < m.count p.1 :=
set.mem_to_finset

@[mono]
lemma multiset.to_enum_finset_mono {α : Type*} [decidable_eq α] {m₁ m₂ : multiset α}
  (h : m₁ ≤ m₂) : m₁.to_enum_finset ⊆ m₂.to_enum_finset :=
begin
  intro,
  simp only [multiset.mem_to_enum_finset],
  exact gt_of_ge_of_gt (multiset.le_iff_count.mp h a.1),
end

@[simp] lemma multiset.to_enum_finset_subset_iff {α : Type*} [decidable_eq α] {m₁ m₂ : multiset α} :
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

/-- Another way to coerce a `multiset` to a type is to go through `m.to_enum_finset` and coerce
that `finset` to a type. -/
@[simps]
def multiset.coe_equiv {α : Type*} [decidable_eq α] (m : multiset α) :
  m ≃ m.to_enum_finset :=
{ to_fun := λ x, ⟨m.coe_embedding x, by { rw multiset.mem_to_enum_finset, exact x.2.2 }⟩,
  inv_fun := λ x, ⟨x.1.1, x.1.2, by { rw ← multiset.mem_to_enum_finset, exact x.2 }⟩,
  left_inv := by { rintro ⟨x, i, h⟩, refl },
  right_inv := by {rintro ⟨⟨x, i⟩, h⟩, refl } }

instance multiset.fintype_coe {α : Type*} [decidable_eq α] (m : multiset α) : fintype m :=
fintype.of_equiv m.to_enum_finset m.coe_equiv.symm

lemma multiset.map_univ_coe_embedding {α : Type*} [decidable_eq α] (m : multiset α) :
  (finset.univ : finset m).map m.coe_embedding = m.to_enum_finset :=
begin
  ext ⟨x, i⟩,
  simp only [finset.mem_map, finset.mem_univ, multiset.coe_embedding_apply, fin.val_eq_coe,
    prod.mk.inj_iff, exists_true_left, multiset.mem_to_enum_finset, multiset.exists_coe, fin.coe_mk,
    exists_and_distrib_right, exists_eq_right],
  split,
  { rintro ⟨_, hi, rfl⟩,
    exact hi, },
  { intro h,
    exact ⟨_, h, rfl⟩, }
end

lemma multiset.to_enum_finset_filter_eq {α : Type*} [decidable_eq α] (m : multiset α) (x : α) :
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

@[simp] lemma multiset.map_to_enum_finset_fst {α : Type*} [decidable_eq α] (m : multiset α) :
  m.to_enum_finset.val.map prod.fst = m :=
begin
  ext x,
  simp only [multiset.count_map, ← finset.filter_val, multiset.to_enum_finset_filter_eq,
    finset.map_val, finset.range_coe, multiset.card_map, multiset.card_range],
end

@[simp] lemma multiset.image_to_enum_finset_fst {α : Type*} [decidable_eq α] (m : multiset α) :
  m.to_enum_finset.image prod.fst = m.to_finset :=
by rw [finset.image, multiset.map_to_enum_finset_fst]

@[simp] lemma multiset.map_univ_coe {α : Type*} [decidable_eq α] (m : multiset α) :
  (finset.univ : finset m).val.map (λ x, ↑x) = m :=
begin
  have := m.map_to_enum_finset_fst,
  rw ← m.map_univ_coe_embedding at this,
  simpa only [finset.map_val, multiset.coe_embedding_apply, multiset.map_map, function.comp_app]
    using this,
end

@[simp] lemma multiset.card_to_enum_finset {α : Type*} [decidable_eq α] {m : multiset α} :
  m.to_enum_finset.card = m.card :=
begin
  change multiset.card _ = _,
  convert_to (m.to_enum_finset.val.map prod.fst).card = _,
  { rw multiset.card_map },
  { rw m.map_to_enum_finset_fst }
end

@[simp] lemma multiset.card_coe {α : Type*} [decidable_eq α] (m : multiset α) :
  fintype.card m = m.card :=
by { rw fintype.card_congr m.coe_equiv, simp }

@[to_additive]
lemma multiset.prod_eq_prod_coe {α : Type*} [decidable_eq α] [comm_monoid α] (m : multiset α) :
  m.prod = ∏ (x : m), x :=
by { congr, simp }

@[to_additive]
lemma multiset.prod_eq_prod_to_enum_finset {α : Type*} [decidable_eq α] [comm_monoid α]
  (m : multiset α) :
  m.prod = ∏ x in m.to_enum_finset, x.1 :=
by { congr, simp }

@[to_additive]
lemma multiset.prod_to_enum_finset {α β : Type*} [decidable_eq α] [comm_monoid β] (m : multiset α)
  (f : α → ℕ → β) :
  ∏ x in m.to_enum_finset, f x.1 x.2 = ∏ (x : m), f x x.2 :=
begin
  rw fintype.prod_equiv m.coe_equiv (λ x, f x x.2) (λ x, f x.1.1 x.1.2),
  { rw ← m.to_enum_finset.prod_coe_sort (λ x, f x.1 x.2),
    simp, },
  { simp }
end

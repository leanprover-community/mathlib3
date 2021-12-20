/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.sigma.lex

/-!
# Orders on a sigma type

This file defines two orders on a sigma type:
* The disjoint sum of orders. `a` is less `b` iff `a` and `b` are in the same summand and `a` is
  less than `b` there.
* The lexicographical order. `a` is less than `b` if its summand is strictly less than the summand
  of `b` or they are in the same summand and `a` is less than `b` there.

## Implementation notes

We declare the disjoint sum of orders as the default instances. The lexicographical order can
override it in local by opening locale `lex`.

## TODO

The lexicographic order on `psigma` currently lives in `order.lexicographic`. Should we bring it
here?
-/

namespace sigma
variables {ι : Type*} {α : ι → Type*}

/-! ### Disjoint sum of orders on `sigma` -/

/-- Disjoint sum of orders. `⟨i, a⟩ ≤ ⟨j, b⟩` iff `i = j` and `a ≤ b`. -/
inductive le [Π i, has_le (α i)] : Π a b : Σ i, α i, Prop
| fiber (i : ι) (a b : α i) : a ≤ b → le ⟨i, a⟩ ⟨i, b⟩

/-- Disjoint sum of orders. `⟨i, a⟩ < ⟨j, b⟩` iff `i = j` and `a < b`. -/
inductive lt [Π i, has_lt (α i)] : Π a b : Σ i, α i, Prop
| fiber (i : ι) (a b : α i) : a < b → lt ⟨i, a⟩ ⟨i, b⟩

instance [Π i, has_le (α i)] : has_le (Σ i, α i) := ⟨le⟩
instance [Π i, has_lt (α i)] : has_lt (Σ i, α i) := ⟨lt⟩

@[simp] lemma mk_le_mk_iff [Π i, has_le (α i)] {i : ι} {a b : α i} :
  (⟨i, a⟩ : sigma α) ≤ ⟨i, b⟩ ↔ a ≤ b :=
⟨λ ⟨_, _, _, h⟩, h, le.fiber _ _ _⟩

@[simp] lemma mk_lt_mk_iff [Π i, has_lt (α i)] {i : ι} {a b : α i} :
  (⟨i, a⟩ : sigma α) < ⟨i, b⟩ ↔ a < b :=
⟨λ ⟨_, _, _, h⟩, h, lt.fiber _ _ _⟩

lemma le_def [Π i, has_le (α i)] {a b : Σ i, α i} : a ≤ b ↔ ∃ h : a.1 = b.1, h.rec a.2 ≤ b.2 :=
begin
  split,
  { rintro ⟨i, a, b, h⟩,
    exact ⟨rfl, h⟩ },
  { obtain ⟨i, a⟩ := a,
    obtain ⟨j, b⟩ := b,
    rintro ⟨(rfl : i = j), h⟩,
    exact le.fiber _ _ _ h }
end

lemma lt_def [Π i, has_lt (α i)] {a b : Σ i, α i} : a < b ↔ ∃ h : a.1 = b.1, h.rec a.2 < b.2 :=
begin
  split,
  { rintro ⟨i, a, b, h⟩,
    exact ⟨rfl, h⟩ },
  { obtain ⟨i, a⟩ := a,
    obtain ⟨j, b⟩ := b,
    rintro ⟨(rfl : i = j), h⟩,
    exact lt.fiber _ _ _ h }
end

instance [Π i, preorder (α i)] : preorder (Σ i, α i) :=
{ le_refl := λ ⟨i, a⟩, le.fiber i a a le_rfl,
  le_trans := begin
    rintro _ _ _ ⟨i, a, b, hab⟩ ⟨_, _, c, hbc⟩,
    exact le.fiber i a c (hab.trans hbc),
  end,
  lt_iff_le_not_le := λ _ _, begin
    split,
    { rintro ⟨i, a, b, hab⟩,
      rwa [mk_le_mk_iff, mk_le_mk_iff, ←lt_iff_le_not_le] },
    { rintro ⟨⟨i, a, b, hab⟩, h⟩,
      rw mk_le_mk_iff at h,
      exact mk_lt_mk_iff.2 (hab.lt_of_not_le h) }
  end,
  .. sigma.has_le,
  .. sigma.has_lt }

instance [Π i, partial_order (α i)] : partial_order (Σ i, α i) :=
{ le_antisymm := begin
    rintro _ _ ⟨i, a, b, hab⟩ ⟨_, _, _, hba⟩,
    exact ext rfl (heq_of_eq $ hab.antisymm hba),
  end,
  .. sigma.preorder }

/-! ### Lexicographical order on `sigma` -/

localized "attribute [-instance] sigma.has_le" in lex
localized "attribute [-instance] sigma.preorder" in lex
localized "attribute [-instance] sigma.partial_order" in lex

/-- The lexicographical `≤` on a sigma type. Turn this on by opening locale `lex`. -/
def lex.has_le [has_lt ι] [Π i, has_le (α i)] : has_le (Σ i, α i) := ⟨lex (<) (λ i, (≤))⟩

/-- The lexicographical `<` on a sigma type. Turn this on by opening locale `lex`. -/
def lex.has_lt [has_lt ι] [Π i, has_lt (α i)] : has_lt (Σ i, α i) := ⟨lex (<) (λ i, (<))⟩

localized "attribute [instance] lex.has_le" in lex
localized "attribute [instance] lex.has_lt" in lex

/-- The lexicographical preorder on a sigma type. Turn this on by opening locale `lex`. -/
def lex.preorder [preorder ι] [Π i, preorder (α i)] : preorder (Σ i, α i) :=
{ le_refl := λ ⟨i, a⟩, lex.right a a le_rfl,
  le_trans := λ _ _ _, trans,
  lt_iff_le_not_le := begin
    refine λ a b, ⟨λ hab, ⟨hab.mono_right (λ i a b, le_of_lt), _⟩, _⟩,
    { rintro (⟨j, i, b, a, hji⟩ | ⟨i, b, a, hba⟩);
        obtain (⟨_, _, _, _, hij⟩ | ⟨_, _, _, hab⟩) := hab,
      { exact hij.not_lt hji },
      { exact lt_irrefl _ hji },
      { exact lt_irrefl _ hij },
      { exact hab.not_le hba } },
    { rintro ⟨⟨i, j, a, b, hij⟩ |⟨i, a, b, hab⟩, hba⟩,
      { exact lex.left _ _ hij },
      { exact lex.right _ _ (hab.lt_of_not_le $ λ h, hba $ lex.right _ _ h) } }
  end,
  .. lex.has_le,
  .. lex.has_lt }

localized "attribute [instance] lex.preorder" in lex

/-- The lexicographical partial order on a sigma type. Turn this on by opening locale `lex`. -/
def lex.partial_order [preorder ι] [Π i, partial_order (α i)] : partial_order (Σ i, α i) :=
{ le_antisymm := λ _ _, antisymm,
  .. lex.preorder }

localized "attribute [instance] lex.partial_order" in lex

/-- The lexicographical linear order on a sigma type. Turn this on by opening locale `lex`. -/
def lex.linear_order [linear_order ι] [Π i, linear_order (α i)] : linear_order (Σ i, α i) :=
{ le_total := total_of _,
  decidable_eq := sigma.decidable_eq,
  decidable_le := lex.decidable _ _,
  .. lex.partial_order }

end sigma

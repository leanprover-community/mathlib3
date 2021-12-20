/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.sigma.order
import order.locally_finite

/-!
# Finite intervals in a sigma type

This file provides the `locally_finite_order` instance for the disjoint sum of orders `Σ i, α i` and
calculates the cardinality of its finite intervals.

## TODO

Do the same for the lexicographical order
-/

open finset function

namespace sigma
variables {ι : Type*} {α : ι → Type*}

/-! ### Disjoint sum of orders -/

section disjoint
variables [decidable_eq ι] [Π i, preorder (α i)] [Π i, locally_finite_order (α i)]

instance : locally_finite_order (Σ i, α i) :=
{ finset_Icc := λ a b, dite (a.1 = b.1)
    (λ h, (Icc (h.rec a.2) b.2).map $ embedding.sigma_mk _) (λ _, ∅),
  finset_Ico := λ a b, dite (a.1 = b.1)
    (λ h, (Ico (h.rec a.2) b.2).map $ embedding.sigma_mk _) (λ _, ∅),
  finset_Ioc := λ a b, dite (a.1 = b.1)
    (λ h, (Ioc (h.rec a.2) b.2).map $ embedding.sigma_mk _) (λ _, ∅),
  finset_Ioo := λ a b, dite (a.1 = b.1)
    (λ h, (Ioo (h.rec a.2) b.2).map $ embedding.sigma_mk _) (λ _, ∅),
  finset_mem_Icc := λ ⟨i, a⟩ ⟨j, b⟩ x, begin
    split_ifs,
    { rw mem_map,
      split,
      { rintro ⟨x, hx, rfl⟩,
        rw mem_Icc at hx,
        dsimp at x h,
        subst h,
        exact ⟨le.fiber _ _ _ hx.1, le.fiber _ _ _ hx.2⟩ },
      { rintro ⟨⟨i, a, x, ha⟩, ⟨_, _, b, hb⟩⟩,
        exact ⟨x, mem_Icc.2 ⟨ha, hb⟩, rfl⟩ } },
    { refine iff_of_false (not_mem_empty _) _,
      rintro ⟨⟨i, a, x, ha⟩, ⟨_, _, b, hb⟩⟩,
      exact h rfl }
  end,
  finset_mem_Ico := λ ⟨i, a⟩ ⟨j, b⟩ x, begin
    split_ifs,
    { rw mem_map,
      split,
      { rintro ⟨x, hx, rfl⟩,
        rw mem_Ico at hx,
        dsimp at x h,
        subst h,
        exact ⟨le.fiber _ _ _ hx.1, lt.fiber _ _ _ hx.2⟩ },
      { rintro ⟨⟨i, a, x, ha⟩, ⟨_, _, b, hb⟩⟩,
        exact ⟨x, mem_Ico.2 ⟨ha, hb⟩, rfl⟩ } },
    { refine iff_of_false (not_mem_empty _) _,
      rintro ⟨⟨i, a, x, ha⟩, ⟨_, _, b, hb⟩⟩,
      exact h rfl }
  end,
  finset_mem_Ioc := λ ⟨i, a⟩ ⟨j, b⟩ x, begin
    split_ifs,
    { rw mem_map,
      split,
      { rintro ⟨x, hx, rfl⟩,
        rw mem_Ioc at hx,
        dsimp at x h,
        subst h,
        exact ⟨lt.fiber _ _ _ hx.1, le.fiber _ _ _ hx.2⟩ },
      { rintro ⟨⟨i, a, x, ha⟩, ⟨_, _, b, hb⟩⟩,
        exact ⟨x, mem_Ioc.2 ⟨ha, hb⟩, rfl⟩ } },
    { refine iff_of_false (not_mem_empty _) _,
      rintro ⟨⟨i, a, x, ha⟩, ⟨_, _, b, hb⟩⟩,
      exact h rfl }
  end,
  finset_mem_Ioo := λ ⟨i, a⟩ ⟨j, b⟩ x, begin
    split_ifs,
    { rw mem_map,
      split,
      { rintro ⟨x, hx, rfl⟩,
        rw mem_Ioo at hx,
        dsimp at x h,
        subst h,
        exact ⟨lt.fiber _ _ _ hx.1, lt.fiber _ _ _ hx.2⟩ },
      { rintro ⟨⟨i, a, x, ha⟩, ⟨_, _, b, hb⟩⟩,
        exact ⟨x, mem_Ioo.2 ⟨ha, hb⟩, rfl⟩ } },
    { refine iff_of_false (not_mem_empty _) _,
      rintro ⟨⟨i, a, x, ha⟩, ⟨_, _, b, hb⟩⟩,
      exact h rfl }
  end }

section
variables (a b : Σ i, α i)

@[simp] lemma card_Icc : (Icc a b).card = dite (a.1 = b.1)
    (λ h, (Icc (h.rec a.2) b.2).card) (λ _, 0) :=
by { convert apply_dite _ _ _ _, ext h, exact (card_map _).symm }

@[simp] lemma card_Ico : (Ico a b).card = dite (a.1 = b.1)
    (λ h, (Ico (h.rec a.2) b.2).card) (λ _, 0) :=
by { convert apply_dite _ _ _ _, ext h, exact (card_map _).symm }

@[simp] lemma card_Ioc : (Ioc a b).card = dite (a.1 = b.1)
    (λ h, (Ioc (h.rec a.2) b.2).card) (λ _, 0) :=
by { convert apply_dite _ _ _ _, ext h, exact (card_map _).symm }

@[simp] lemma card_Ioo : (Ioo a b).card = dite (a.1 = b.1)
    (λ h, (Ioo (h.rec a.2) b.2).card) (λ _, 0) :=
by { convert apply_dite _ _ _ _, ext h, exact (card_map _).symm }

end

variables (i : ι) (a b : α i)

@[simp] lemma card_Icc_mk_mk : (Icc (⟨i, a⟩ : sigma α) ⟨i, b⟩).card = (Icc a b).card :=
by { convert card_map _, exact dif_pos rfl }

@[simp] lemma card_Ico_mk_mk : (Ico (⟨i, a⟩ : sigma α) ⟨i, b⟩).card = (Ico a b).card :=
by { convert card_map _, exact dif_pos rfl }

@[simp] lemma card_Ioc_mk_mk : (Ioc (⟨i, a⟩ : sigma α) ⟨i, b⟩).card = (Ioc a b).card :=
by { convert card_map _, exact dif_pos rfl }

@[simp] lemma card_Ioo_mk_mk : (Ioo (⟨i, a⟩ : sigma α) ⟨i, b⟩).card = (Ioo a b).card :=
by { convert card_map _, exact dif_pos rfl }

end disjoint
end sigma

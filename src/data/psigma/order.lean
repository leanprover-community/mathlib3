/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Minchao Wu
-/
import data.sigma.lex
import order.bounded_order

/-!
# Lexicographic order on a sigma type

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the lexicographic order on `Σₗ' i, α i`. `a` is less than `b` if its summand is
strictly less than the summand of `b` or they are in the same summand and `a` is less than `b`
there.

## Notation

* `Σₗ' i, α i`: Sigma type equipped with the lexicographic order. A type synonym of `Σ' i, α i`.

## See also

Related files are:
* `data.finset.colex`: Colexicographic order on finite sets.
* `data.list.lex`: Lexicographic order on lists.
* `data.pi.lex`: Lexicographic order on `Πₗ i, α i`.
* `data.sigma.order`: Lexicographic order on `Σₗ i, α i`. Basically a twin of this file.
* `data.prod.lex`: Lexicographic order on `α × β`.

## TODO

Define the disjoint order on `Σ' i, α i`, where `x ≤ y` only if `x.fst = y.fst`.

Prove that a sigma type is a `no_max_order`, `no_min_order`, `densely_ordered` when its summands
are.
-/

variables {ι : Type*} {α : ι → Type*}

namespace psigma

notation `Σₗ'` binders `, ` r:(scoped p, _root_.lex (psigma p)) := r

namespace lex

/-- The lexicographical `≤` on a sigma type. -/
instance has_le [has_lt ι] [Π i, has_le (α i)] : has_le (Σₗ' i, α i) := ⟨lex (<) (λ i, (≤))⟩

/-- The lexicographical `<` on a sigma type. -/
instance has_lt [has_lt ι] [Π i, has_lt (α i)] : has_lt (Σₗ' i, α i) := ⟨lex (<) (λ i, (<))⟩

instance preorder [preorder ι] [Π i, preorder (α i)] : preorder (Σₗ' i, α i) :=
{ le_refl := λ ⟨i, a⟩, lex.right _ le_rfl,
  le_trans :=
  begin
    rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ ⟨a₃, b₃⟩ ⟨h₁r⟩ ⟨h₂r⟩,
    { left, apply lt_trans, repeat { assumption } },
    { left, assumption },
    { left, assumption },
    { right, apply le_trans, repeat { assumption } }
  end,
  lt_iff_le_not_le :=
  begin
    refine λ a b, ⟨λ hab, ⟨hab.mono_right (λ i a b, le_of_lt), _⟩, _⟩,
    { rintro (⟨i, a, hji⟩ | ⟨i, hba⟩);
        obtain (⟨_, _, hij⟩ | ⟨_, hab⟩) := hab,
      { exact hij.not_lt hji },
      { exact lt_irrefl _ hji },
      { exact lt_irrefl _ hij },
      { exact hab.not_le hba } },
    { rintro ⟨⟨j, b, hij⟩ | ⟨i, hab⟩, hba⟩,
      { exact lex.left _ _ hij },
      { exact lex.right _ (hab.lt_of_not_le $ λ h, hba $ lex.right _ h) } }
  end,
  .. lex.has_le,
  .. lex.has_lt }

/-- Dictionary / lexicographic partial_order for dependent pairs. -/
instance partial_order [partial_order ι] [Π i, partial_order (α i)] :
  partial_order (Σₗ' i, α i) :=
{ le_antisymm :=
  begin
    rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ (⟨_, _, hlt₁⟩ | ⟨_, hlt₁⟩) (⟨_, _, hlt₂⟩ | ⟨_, hlt₂⟩),
    { exact (lt_irrefl a₁ $ hlt₁.trans hlt₂).elim },
    { exact (lt_irrefl a₁ hlt₁).elim },
    { exact (lt_irrefl a₁ hlt₂).elim },
    { rw hlt₁.antisymm hlt₂ }
  end
  .. lex.preorder }

/-- Dictionary / lexicographic linear_order for pairs. -/
instance linear_order [linear_order ι] [Π i, linear_order (α i)] : linear_order (Σₗ' i, α i) :=
{ le_total :=
  begin
  rintro ⟨i, a⟩ ⟨j, b⟩,
  obtain hij | rfl | hji := lt_trichotomy i j,
  { exact or.inl (lex.left _ _ hij) },
  { obtain hab | hba := le_total a b,
    { exact or.inl (lex.right _ hab) },
    { exact or.inr (lex.right _ hba) } },
  { exact or.inr (lex.left _ _ hji) }
  end,
  decidable_eq := psigma.decidable_eq,
  decidable_le := lex.decidable _ _,
  decidable_lt := lex.decidable _ _,
  .. lex.partial_order }

/-- The lexicographical linear order on a sigma type. -/
instance order_bot [partial_order ι] [order_bot ι] [Π i, preorder (α i)] [order_bot (α ⊥)] :
  order_bot (Σₗ' i, α i) :=
{ bot := ⟨⊥, ⊥⟩,
  bot_le := λ ⟨a, b⟩, begin
    obtain rfl | ha := eq_bot_or_bot_lt a,
    { exact lex.right _ bot_le },
    { exact lex.left _ _ ha }
  end }

/-- The lexicographical linear order on a sigma type. -/
instance order_top [partial_order ι] [order_top ι] [Π i, preorder (α i)] [order_top (α ⊤)] :
  order_top (Σₗ' i, α i) :=
{ top := ⟨⊤, ⊤⟩,
  le_top := λ ⟨a, b⟩, begin
    obtain rfl | ha := eq_top_or_lt_top a,
    { exact lex.right _ le_top },
    { exact lex.left _ _ ha }
  end }

/-- The lexicographical linear order on a sigma type. -/
instance bounded_order [partial_order ι] [bounded_order ι] [Π i, preorder (α i)]
  [order_bot (α ⊥)] [order_top (α ⊤)] :
  bounded_order (Σₗ' i, α i) :=
{ .. lex.order_bot, .. lex.order_top }

instance densely_ordered [preorder ι] [densely_ordered ι] [Π i, nonempty (α i)]
  [Π i, preorder (α i)] [Π i, densely_ordered (α i)] :
  densely_ordered (Σₗ' i, α i) :=
⟨begin
  rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | @⟨_, _, b, h⟩),
  { obtain ⟨k, hi, hj⟩ := exists_between h,
    obtain ⟨c⟩ : nonempty (α k) := infer_instance,
    exact ⟨⟨k, c⟩, left _ _ hi, left _ _ hj⟩ },
  { obtain ⟨c, ha, hb⟩ := exists_between h,
    exact ⟨⟨i, c⟩, right _ ha, right _ hb⟩ }
end⟩

instance densely_ordered_of_no_max_order [preorder ι] [Π i, preorder (α i)]
  [Π i, densely_ordered (α i)] [Π i, no_max_order (α i)] :
  densely_ordered (Σₗ' i, α i) :=
⟨begin
  rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | @⟨_, _, b, h⟩),
  { obtain ⟨c, ha⟩ := exists_gt a,
    exact ⟨⟨i, c⟩, right _ ha, left _ _ h⟩ },
  { obtain ⟨c, ha, hb⟩ := exists_between h,
    exact ⟨⟨i, c⟩, right _ ha, right _ hb⟩ }
end⟩

instance densely_ordered_of_no_min_order [preorder ι] [Π i, preorder (α i)]
  [Π i, densely_ordered (α i)] [Π i, no_min_order (α i)] :
  densely_ordered (Σₗ' i, α i) :=
⟨begin
  rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | @⟨_, _, b, h⟩),
  { obtain ⟨c, hb⟩ := exists_lt b,
    exact ⟨⟨j, c⟩, left _ _ h, right _ hb⟩ },
  { obtain ⟨c, ha, hb⟩ := exists_between h,
    exact ⟨⟨i, c⟩, right _ ha, right _ hb⟩ }
end⟩

instance no_max_order_of_nonempty [preorder ι] [Π i, preorder (α i)] [no_max_order ι]
  [Π i, nonempty (α i)] :
  no_max_order (Σₗ' i, α i) :=
⟨begin
  rintro ⟨i, a⟩,
  obtain ⟨j, h⟩ := exists_gt i,
  obtain ⟨b⟩ : nonempty (α j) := infer_instance,
  exact ⟨⟨j, b⟩, left _ _ h⟩
end⟩

instance no_min_order_of_nonempty [preorder ι] [Π i, preorder (α i)] [no_max_order ι]
  [Π i, nonempty (α i)] :
  no_max_order (Σₗ' i, α i) :=
⟨begin
  rintro ⟨i, a⟩,
  obtain ⟨j, h⟩ := exists_gt i,
  obtain ⟨b⟩ : nonempty (α j) := infer_instance,
  exact ⟨⟨j, b⟩, left _ _ h⟩
end⟩

instance no_max_order [preorder ι] [Π i, preorder (α i)] [Π i, no_max_order (α i)] :
  no_max_order (Σₗ' i, α i) :=
⟨by { rintro ⟨i, a⟩, obtain ⟨b, h⟩ := exists_gt a, exact ⟨⟨i, b⟩, right _ h⟩ }⟩

instance no_min_order [preorder ι] [Π i, preorder (α i)] [Π i, no_min_order (α i)] :
  no_min_order (Σₗ' i, α i) :=
⟨by { rintro ⟨i, a⟩, obtain ⟨b, h⟩ := exists_lt a, exact ⟨⟨i, b⟩, right _ h⟩ }⟩

end lex
end psigma

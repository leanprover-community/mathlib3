/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import order.well_founded
import algebra.group.pi
import order.min_max

/-!
# Lexicographic order on Pi types

This file defines the lexicographic order for Pi types. `a` is less than `b` if `a i = b i` for all
`i` up to some point `k`, and `a k < b k`.

## Notation

* `Πₗ i, α i`: Pi type equipped with the lexicographic order. Type synonym of `Π i, α i`.

## See also

Related files are:
* `data.finset.colex`: Colexicographic order on finite sets.
* `data.list.lex`: Lexicographic order on lists.
* `data.sigma.order`: Lexicographic order on `Σₗ i, α i`.
* `data.psigma.order`: Lexicographic order on `Σₗ' i, α i`.
* `data.prod.lex`: Lexicographic order on `α × β`.
-/

variables {ι : Type*} {β : ι → Type*} (r : ι → ι → Prop)
  (s : Π {i}, β i → β i → Prop)

namespace pi

instance {α : Type*} : Π [inhabited α], inhabited (lex α) := id

/-- The lexicographic relation on `Π i : ι, β i`, where `ι` is ordered by `r`,
  and each `β i` is ordered by `s`. -/
protected def lex (x y : Π i, β i) : Prop :=
∃ i, (∀ j, r j i → x j = y j) ∧ s (x i) (y i)

/- This unfortunately results in a type that isn't delta-reduced, so we keep the notation out of the
basic API, just in case -/
notation `Πₗ` binders `, ` r:(scoped p, lex (Π i, p i)) := r

@[simp] lemma to_lex_apply (x : Π i, β i) (i : ι) : to_lex x i = x i := rfl
@[simp] lemma of_lex_apply (x : lex (Π i, β i)) (i : ι) : of_lex x i = x i := rfl

lemma is_trichotomous_lex [∀ i, is_trichotomous (β i) s] (wf : well_founded r) :
  is_trichotomous (Π i, β i) (pi.lex r @s) :=
{ trichotomous := λ a b,
    begin
      cases eq_or_ne a b with hab hab,
      { exact or.inr (or.inl hab) },
      { rw function.ne_iff at hab,
        let i := wf.min _ hab,
        have hri : ∀ j, r j i → a j = b j,
        { intro j, rw ← not_imp_not,
          exact λ h', wf.not_lt_min _ h' },
        have hne : a i ≠ b i, from wf.min_mem _ hab,
        cases trichotomous_of s (a i) (b i) with hi hi,
        exacts [or.inl ⟨i, hri, hi⟩,
          or.inr $ or.inr $ ⟨i, λ j hj, (hri j hj).symm, hi.resolve_left hne⟩] },
    end }

instance [has_lt ι] [Π a, has_lt (β a)] : has_lt (lex (Π i, β i)) := ⟨pi.lex (<) (λ _, (<))⟩

instance lex.is_strict_order [linear_order ι] [∀ a, partial_order (β a)] :
  is_strict_order (lex (Π i, β i)) (<) :=
{ irrefl := λ a ⟨k, hk₁, hk₂⟩, lt_irrefl (a k) hk₂,
  trans :=
    begin
      rintro a b c ⟨N₁, lt_N₁, a_lt_b⟩ ⟨N₂, lt_N₂, b_lt_c⟩,
      rcases lt_trichotomy N₁ N₂ with (H|rfl|H),
      exacts [⟨N₁, λ j hj, (lt_N₁ _ hj).trans (lt_N₂ _ $ hj.trans H), lt_N₂ _ H ▸ a_lt_b⟩,
        ⟨N₁, λ j hj, (lt_N₁ _ hj).trans (lt_N₂ _ hj), a_lt_b.trans b_lt_c⟩,
        ⟨N₂, λ j hj, (lt_N₁ _ (hj.trans H)).trans (lt_N₂ _ hj), (lt_N₁ _ H).symm ▸ b_lt_c⟩]
    end }

instance [linear_order ι] [Π a, partial_order (β a)] : partial_order (lex (Π i, β i)) :=
partial_order_of_SO (<)

/-- `Πₗ i, α i` is a linear order if the original order is well-founded. -/
noncomputable instance [linear_order ι] [is_well_order ι (<)] [∀ a, linear_order (β a)] :
  linear_order (lex (Π i, β i)) :=
@linear_order_of_STO' (Πₗ i, β i) (<)
  { to_is_trichotomous := is_trichotomous_lex _ _ is_well_order.wf } (classical.dec_rel _)

lemma lex.le_of_forall_le [linear_order ι] [is_well_order ι (<)] [Π a, linear_order (β a)]
  {a b : lex (Π i, β i)} (h : ∀ i, a i ≤ b i) : a ≤ b :=
le_of_not_lt (λ ⟨i, hi⟩, (h i).not_lt hi.2)

lemma lex.le_of_of_lex_le [linear_order ι] [is_well_order ι (<)] [Π a, linear_order (β a)]
  {a b : lex (Π i, β i)} (h : of_lex a ≤ of_lex b) : a ≤ b :=
lex.le_of_forall_le h

lemma to_lex_monotone [linear_order ι] [is_well_order ι (<)] [Π a, linear_order (β a)] :
  monotone (@to_lex (Π i, β i)) :=
λ _ _, lex.le_of_forall_le

instance [linear_order ι] [is_well_order ι (<)] [Π a, linear_order (β a)]
  [Π a, order_bot (β a)] : order_bot (lex (Π a, β a)) :=
{ bot := to_lex ⊥,
  bot_le := λ f, lex.le_of_of_lex_le bot_le }

instance [linear_order ι] [is_well_order ι (<)] [Π a, linear_order (β a)]
  [Π a, order_top (β a)] : order_top (lex (Π a, β a)) :=
{ top := to_lex ⊤,
  le_top := λ f, lex.le_of_of_lex_le le_top }

instance [linear_order ι] [is_well_order ι (<)] [Π a, linear_order (β a)]
  [Π a, bounded_order (β a)] : bounded_order (lex (Π a, β a)) :=
{ .. pi.lex.order_bot, .. pi.lex.order_top }

--we might want the analog of `pi.ordered_cancel_comm_monoid` as well in the future
@[to_additive]
instance lex.ordered_comm_group [linear_order ι] [∀ a, ordered_comm_group (β a)] :
  ordered_comm_group (lex (Π i, β i)) :=
{ mul_le_mul_left := λ x y hxy z,
    hxy.elim
      (λ hxyz, hxyz ▸ le_rfl)
      (λ ⟨i, hi⟩,
        or.inr ⟨i, λ j hji, show z j * x j = z j * y j, by rw hi.1 j hji,
          mul_lt_mul_left' hi.2 _⟩),
  ..pi.lex.partial_order,
  ..pi.comm_group }

end pi

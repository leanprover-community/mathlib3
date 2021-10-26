/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import algebra.order.pi
import order.well_founded
import order.min_max


/-!
# Lexicographic order on Pi types

This file defines the lexicographic relation for Pi types of partial orders and linear orders. We
also provide a `pilex` analog of `pi.ordered_comm_group` (see `algebra.order.pi`).
-/

variables {ι : Type*} {β : ι → Type*} (r : ι → ι → Prop)
  (s : Π {i}, β i → β i → Prop)

/-- The lexicographic relation on `Π i : ι, β i`, where `ι` is ordered by `r`,
  and each `β i` is ordered by `s`. -/
def pi.lex (x y : Π i, β i) : Prop :=
∃ i, (∀ j, r j i → x j = y j) ∧ s (x i) (y i)

/-- The cartesian product of an indexed family, equipped with the lexicographic order. -/
def pilex (α : Type*) (β : α → Type*) : Type* := Π a, β a

instance [has_lt ι] [∀ a, has_lt (β a)] : has_lt (pilex ι β) :=
{ lt := pi.lex (<) (λ _, (<)) }

instance [∀ a, inhabited (β a)] : inhabited (pilex ι β) :=
by unfold pilex; apply_instance

instance pilex.is_strict_order [linear_order ι] [∀ a, partial_order (β a)] :
  is_strict_order (pilex ι β) (<) :=
{ irrefl := λ a ⟨k, hk₁, hk₂⟩, lt_irrefl (a k) hk₂,
  trans :=
    begin
      rintro a b c ⟨N₁, lt_N₁, a_lt_b⟩ ⟨N₂, lt_N₂, b_lt_c⟩,
      rcases lt_trichotomy N₁ N₂ with (H|rfl|H),
      exacts [⟨N₁, λ j hj, (lt_N₁ _ hj).trans (lt_N₂ _ $ hj.trans H), lt_N₂ _ H ▸ a_lt_b⟩,
        ⟨N₁, λ j hj, (lt_N₁ _ hj).trans (lt_N₂ _ hj), a_lt_b.trans b_lt_c⟩,
        ⟨N₂, λ j hj, (lt_N₁ _ (hj.trans H)).trans (lt_N₂ _ hj), (lt_N₁ _ H).symm ▸ b_lt_c⟩]
    end }

instance [linear_order ι] [∀ a, partial_order (β a)] : partial_order (pilex ι β) :=
partial_order_of_SO (<)

protected lemma pilex.is_strict_total_order' [linear_order ι]
  (wf : well_founded ((<) : ι → ι → Prop)) [∀ a, linear_order (β a)] :
  is_strict_total_order' (pilex ι β) (<) :=
{ trichotomous := λ a b,
    begin
      by_cases h : ∃ i, a i ≠ b i,
      { let i := wf.min _ h,
        have hlt_i : ∀ j < i, a j = b j,
        { intro j, rw ← not_imp_not,
          exact λ h', wf.not_lt_min _ _ h' },
        have : a i ≠ b i, from wf.min_mem _ h,
        exact this.lt_or_lt.imp (λ h, ⟨i, hlt_i, h⟩)
          (λ h, or.inr ⟨i, λ j hj, (hlt_i j hj).symm, h⟩) },
      { push_neg at h, exact or.inr (or.inl (funext h)) }
    end }

/-- `pilex` is a linear order if the original order is well-founded.
This cannot be an instance, since it depends on the well-foundedness of `<`. -/
protected noncomputable def pilex.linear_order [linear_order ι]
  (wf : well_founded ((<) : ι → ι → Prop)) [∀ a, linear_order (β a)] :
  linear_order (pilex ι β) :=
@linear_order_of_STO' (pilex ι β) (<) (pilex.is_strict_total_order' wf) (classical.dec_rel _)

lemma pilex.le_of_forall_le [linear_order ι]
  (wf : well_founded ((<) : ι → ι → Prop)) [∀ a, linear_order (β a)] {a b : pilex ι β}
  (h : ∀ i, a i ≤ b i) : a ≤ b :=
begin
  letI : linear_order (pilex ι β) := pilex.linear_order wf,
  exact le_of_not_lt (λ ⟨i, hi⟩, (h i).not_lt hi.2)
end

--we might want the analog of `pi.ordered_cancel_comm_monoid` as well in the future
@[to_additive]
instance [linear_order ι] [∀ a, ordered_comm_group (β a)] :
  ordered_comm_group (pilex ι β) :=
{ mul_le_mul_left := λ x y hxy z,
    hxy.elim
      (λ hxyz, hxyz ▸ le_refl _)
      (λ ⟨i, hi⟩,
        or.inr ⟨i, λ j hji, show z j * x j = z j * y j, by rw hi.1 j hji,
          mul_lt_mul_left' hi.2 _⟩),
  ..pilex.partial_order,
  ..pi.comm_group }

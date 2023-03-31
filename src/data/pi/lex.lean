/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import order.well_founded
import algebra.group.pi
import algebra.order.group.defs


/-!
# Lexicographic order on Pi types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

lemma lex_lt_of_lt_of_preorder [Π i, preorder (β i)] {r} (hwf : well_founded r)
  {x y : Π i, β i} (hlt : x < y) : ∃ i, (∀ j, r j i → x j ≤ y j ∧ y j ≤ x j) ∧ x i < y i :=
let h' := pi.lt_def.1 hlt, ⟨i, hi, hl⟩ := hwf.has_min _ h'.2 in
  ⟨i, λ j hj, ⟨h'.1 j, not_not.1 $ λ h, hl j (lt_of_le_not_le (h'.1 j) h) hj⟩, hi⟩

lemma lex_lt_of_lt [Π i, partial_order (β i)] {r} (hwf : well_founded r)
  {x y : Π i, β i} (hlt : x < y) : pi.lex r (λ i, (<)) x y :=
by { simp_rw [pi.lex, le_antisymm_iff], exact lex_lt_of_lt_of_preorder hwf hlt }

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
          exact λ h', wf.not_lt_min _ _ h' },
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
@linear_order_of_STO (Πₗ i, β i) (<)
  { to_is_trichotomous := is_trichotomous_lex _ _ is_well_founded.wf } (classical.dec_rel _)

section partial_order
variables [linear_order ι] [is_well_order ι (<)] [Π i, partial_order (β i)] {x y : Π i, β i} {i : ι}
  {a b : β i}

open function

lemma to_lex_monotone : monotone (@to_lex (Π i, β i)) :=
λ a b h, or_iff_not_imp_left.2 $ λ hne,
  let ⟨i, hi, hl⟩ := is_well_founded.wf.has_min {i | a i ≠ b i} (function.ne_iff.1 hne) in
  ⟨i, λ j hj, by { contrapose! hl, exact ⟨j, hl, hj⟩ }, (h i).lt_of_ne hi⟩

lemma to_lex_strict_mono : strict_mono (@to_lex (Π i, β i)) :=
λ a b h, let ⟨i, hi, hl⟩ := is_well_founded.wf.has_min {i | a i ≠ b i} (function.ne_iff.1 h.ne) in
  ⟨i, λ j hj, by { contrapose! hl, exact ⟨j, hl, hj⟩ }, (h.le i).lt_of_ne hi⟩

@[simp] lemma lt_to_lex_update_self_iff : to_lex x < to_lex (update x i a) ↔ x i < a :=
begin
  refine ⟨_, λ h, to_lex_strict_mono $ lt_update_self_iff.2 h⟩,
  rintro ⟨j, hj, h⟩,
  dsimp at h,
  obtain rfl : j = i,
  { by_contra H,
    rw update_noteq H at h,
    exact h.false },
  { rwa update_same at h }
end

@[simp] lemma to_lex_update_lt_self_iff : to_lex (update x i a) < to_lex x ↔ a < x i :=
begin
  refine ⟨_, λ h, to_lex_strict_mono $ update_lt_self_iff.2 h⟩,
  rintro ⟨j, hj, h⟩,
  dsimp at h,
  obtain rfl : j = i,
  { by_contra H,
    rw update_noteq H at h,
    exact h.false },
  { rwa update_same at h }
end

@[simp] lemma le_to_lex_update_self_iff : to_lex x ≤ to_lex (update x i a) ↔ x i ≤ a :=
by simp_rw [le_iff_lt_or_eq, lt_to_lex_update_self_iff, to_lex_inj, eq_update_self_iff]

@[simp] lemma to_lex_update_le_self_iff : to_lex (update x i a) ≤ to_lex x ↔ a ≤ x i :=
by simp_rw [le_iff_lt_or_eq, to_lex_update_lt_self_iff, to_lex_inj, update_eq_self_iff]

end partial_order

instance [linear_order ι] [is_well_order ι (<)] [Π a, partial_order (β a)]
  [Π a, order_bot (β a)] : order_bot (lex (Π a, β a)) :=
{ bot := to_lex ⊥,
  bot_le := λ f, to_lex_monotone bot_le }

instance [linear_order ι] [is_well_order ι (<)] [Π a, partial_order (β a)]
  [Π a, order_top (β a)] : order_top (lex (Π a, β a)) :=
{ top := to_lex ⊤,
  le_top := λ f, to_lex_monotone le_top }

instance [linear_order ι] [is_well_order ι (<)] [Π a, partial_order (β a)]
  [Π a, bounded_order (β a)] : bounded_order (lex (Π a, β a)) :=
{ .. pi.lex.order_bot, .. pi.lex.order_top }

instance [preorder ι] [Π i, has_lt (β i)] [Π i, densely_ordered (β i)] :
  densely_ordered (lex (Π i, β i)) :=
⟨begin
  rintro _ _ ⟨i, h, hi⟩,
  obtain ⟨a, ha₁, ha₂⟩ := exists_between hi,
  classical,
  refine ⟨a₂.update _ a, ⟨i, λ j hj, _, _⟩, i, λ j hj, _, _⟩,
  rw h j hj,
  iterate 2 { { rw a₂.update_noteq hj.ne a }, { rwa a₂.update_same i a } },
end⟩

lemma lex.no_max_order' [preorder ι] [Π i, has_lt (β i)] (i : ι) [no_max_order (β i)] :
  no_max_order (lex (Π i, β i)) :=
⟨λ a, begin
  classical,
  obtain ⟨b, hb⟩ := exists_gt (a i),
  exact ⟨a.update i b, i, λ j hj, (a.update_noteq hj.ne b).symm, by rwa a.update_same i b⟩
end⟩

instance [linear_order ι] [is_well_order ι (<)] [nonempty ι] [Π i, partial_order (β i)]
  [Π i, no_max_order (β i)] :
  no_max_order (lex (Π i, β i)) :=
⟨λ a, let ⟨b, hb⟩ := exists_gt (of_lex a) in ⟨_, to_lex_strict_mono hb⟩⟩

instance [linear_order ι] [is_well_order ι (<)] [nonempty ι] [Π i, partial_order (β i)]
  [Π i, no_min_order (β i)] :
  no_min_order (lex (Π i, β i)) :=
⟨λ a, let ⟨b, hb⟩ := exists_lt (of_lex a) in ⟨_, to_lex_strict_mono hb⟩⟩

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

/-- If we swap two strictly decreasing values in a function, then the result is lexicographically
smaller than the original function. -/
lemma lex_desc {α} [preorder ι] [decidable_eq ι] [preorder α] {f : ι → α} {i j : ι}
  (h₁ : i < j) (h₂ : f j < f i) :
  to_lex (f ∘ equiv.swap i j) < to_lex f :=
⟨i, λ k hik, congr_arg f (equiv.swap_apply_of_ne_of_ne hik.ne (hik.trans h₁).ne),
  by simpa only [pi.to_lex_apply, function.comp_app, equiv.swap_apply_left] using h₂⟩

end pi

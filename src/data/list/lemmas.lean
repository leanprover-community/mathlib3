/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, Yury Kudryashov
-/
import data.set.function
import data.list.basic

/-! # Some lemmas about lists involving sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Split out from `data.list.basic` to reduce its dependencies.
-/

open list

variables {α β γ : Type*}

namespace list

lemma range_map (f : α → β) : set.range (map f) = {l | ∀ x ∈ l, x ∈ set.range f} :=
begin
  refine set.subset.antisymm (set.range_subset_iff.2 $
    λ l, forall_mem_map_iff.2 $ λ y _, set.mem_range_self _) (λ l hl, _),
  induction l with a l ihl, { exact ⟨[], rfl⟩ },
  rcases ihl (λ x hx, hl x $ subset_cons _ _ hx) with ⟨l, rfl⟩,
  rcases hl a (mem_cons_self _ _) with ⟨a, rfl⟩,
  exact ⟨a :: l, map_cons _ _ _⟩
end

lemma range_map_coe (s : set α) : set.range (map (coe : s → α)) = {l | ∀ x ∈ l, x ∈ s} :=
by rw [range_map, subtype.range_coe]

/-- If each element of a list can be lifted to some type, then the whole list can be lifted to this
type. -/
instance can_lift (c) (p) [can_lift α β c p] :
  can_lift (list α) (list β) (list.map c) (λ l, ∀ x ∈ l, p x) :=
{ prf  := λ l H,
    begin
      rw [← set.mem_range, range_map],
      exact λ a ha, can_lift.prf a (H a ha),
    end}

lemma inj_on_insert_nth_index_of_not_mem (l : list α) (x : α) (hx : x ∉ l) :
  set.inj_on (λ k, insert_nth k x l) {n | n ≤ l.length} :=
begin
  induction l with hd tl IH,
  { intros n hn m hm h,
    simp only [set.mem_singleton_iff, set.set_of_eq_eq_singleton, length, nonpos_iff_eq_zero]
      at hn hm,
    simp [hn, hm] },
  { intros n hn m hm h,
    simp only [length, set.mem_set_of_eq] at hn hm,
    simp only [mem_cons_iff, not_or_distrib] at hx,
    cases n;
    cases m,
    { refl },
    { simpa [hx.left] using h },
    { simpa [ne.symm hx.left] using h },
    { simp only [true_and, eq_self_iff_true, insert_nth_succ_cons] at h,
      rw nat.succ_inj',
      refine IH hx.right _ _ h,
      { simpa [nat.succ_le_succ_iff] using hn },
      { simpa [nat.succ_le_succ_iff] using hm } } }
end

lemma foldr_range_subset_of_range_subset {f : β → α → α} {g : γ → α → α}
  (hfg : set.range f ⊆ set.range g) (a : α) :
  set.range (foldr f a) ⊆ set.range (foldr g a) :=
begin
  rintro _ ⟨l, rfl⟩,
  induction l with b l H,
  { exact ⟨[], rfl⟩ },
  { cases hfg (set.mem_range_self b) with c hgf,
    cases H with m hgf',
    rw [foldr_cons, ←hgf, ←hgf'],
    exact ⟨c :: m, rfl⟩ }
end

lemma foldl_range_subset_of_range_subset {f : α → β → α} {g : α → γ → α}
  (hfg : set.range (λ a c, f c a) ⊆ set.range (λ b c, g c b)) (a : α) :
  set.range (foldl f a) ⊆ set.range (foldl g a) :=
begin
  change set.range (λ l, _) ⊆ set.range (λ l, _),
  simp_rw ←foldr_reverse at hfg ⊢,
  simp_rw [set.range_comp _ list.reverse, reverse_involutive.bijective.surjective.range_eq,
    set.image_univ],
  exact foldr_range_subset_of_range_subset hfg a,
end

lemma foldr_range_eq_of_range_eq {f : β → α → α} {g : γ → α → α} (hfg : set.range f = set.range g)
  (a : α) :
  set.range (foldr f a) = set.range (foldr g a) :=
(foldr_range_subset_of_range_subset hfg.le a).antisymm (foldr_range_subset_of_range_subset hfg.ge a)

lemma foldl_range_eq_of_range_eq {f : α → β → α} {g : α → γ → α}
  (hfg : set.range (λ a c, f c a) = set.range (λ b c, g c b)) (a : α) :
  set.range (foldl f a) = set.range (foldl g a) :=
(foldl_range_subset_of_range_subset hfg.le a).antisymm (foldl_range_subset_of_range_subset hfg.ge a)

end list

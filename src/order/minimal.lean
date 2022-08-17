/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.antichain
import order.upper_lower
import order.zorn

/-!
# Minimal/maximal elements of a set

This file defines minimal and maximal of a set with respect to an arbitrary relation.

## Main declarations

* `maximals r s`: Maximal elements of `s` with respect to `r`.
* `minimals r s`: Minimal elements of `s` with respect to `r`.

## TODO

Do we need a `finset` version?
-/

open function set

variables {α : Type*} (r r₁ r₂ : α → α → Prop) (s t : set α) (a : α)

/-- Turns a set into an antichain by keeping only the "maximal" elements. -/
def maximals : set α := {a ∈ s | ∀ ⦃b⦄, b ∈ s → r a b → a = b}

/-- Turns a set into an antichain by keeping only the "minimal" elements. -/
def minimals : set α := {a ∈ s | ∀ ⦃b⦄, b ∈ s → r b a → a = b}

lemma maximals_subset : maximals r s ⊆ s := sep_subset _ _
lemma minimals_subset : minimals r s ⊆ s := sep_subset _ _

@[simp] lemma maximals_empty : maximals r ∅ = ∅ := sep_empty _
@[simp] lemma minimals_empty : minimals r ∅ = ∅ := sep_empty _

@[simp] lemma maximals_singleton : maximals r {a} = {a} :=
(maximals_subset _ _).antisymm $ singleton_subset_iff.2 $ ⟨rfl, λ b hb _, hb.symm⟩

@[simp] lemma minimals_singleton : minimals r {a} = {a} := maximals_singleton _ _

lemma maximals_swap : maximals (swap r) s = minimals r s := rfl
lemma minimals_swap : minimals (swap r) s = maximals r s := rfl

lemma maximals_antichain : is_antichain r (maximals r s) := λ a ha b hb hab h, hab $ ha.2 hb.1 h
lemma minimals_antichain : is_antichain r (minimals r s) := (maximals_antichain _ _).swap

lemma maximals_eq_minimals [is_symm α r] : maximals r s = minimals r s :=
by { congr, ext a b, exact comm }

variables {r r₁ r₂ s t a}

lemma set.subsingleton.maximals_eq (h : s.subsingleton) : maximals r s = s :=
h.induction_on (minimals_empty _) (maximals_singleton _)

lemma set.subsingleton.minimals_eq (h : s.subsingleton) : minimals r s = s := h.maximals_eq

lemma maximals_mono (h : ∀ a b, r₁ a b → r₂ a b) : maximals r₂ s ⊆ maximals r₁ s :=
λ a ha, ⟨ha.1, λ b hb, ha.2 hb ∘ h _ _⟩

lemma minimals_mono (h : ∀ a b, r₁ a b → r₂ a b) : minimals r₂ s ⊆ minimals r₁ s :=
λ a ha, ⟨ha.1, λ b hb, ha.2 hb ∘ h _ _⟩

lemma maximals_union : maximals r (s ∪ t) ⊆ maximals r s ∪ maximals r t :=
begin
  intros a ha,
  obtain h | h := ha.1,
  { exact or.inl ⟨h, λ b hb, ha.2 $ or.inl hb⟩ },
  { exact or.inr ⟨h, λ b hb, ha.2 $ or.inr hb⟩ }
end

lemma minimals_union : minimals r (s ∪ t) ⊆ minimals r s ∪ minimals r t := maximals_union

lemma maximals_inter_subset : maximals r s ∩ t ⊆ maximals r (s ∩ t) :=
λ a ha, ⟨⟨ha.1.1, ha.2⟩, λ b hb, ha.1.2 hb.1⟩

lemma minimals_inter_subset : minimals r s ∩ t ⊆ minimals r (s ∩ t) := maximals_inter_subset

lemma inter_maximals_subset : s ∩ maximals r t ⊆ maximals r (s ∩ t) :=
λ a ha, ⟨⟨ha.1, ha.2.1⟩, λ b hb, ha.2.2 hb.2⟩

lemma inter_minimals_subset : s ∩ minimals r t ⊆ minimals r (s ∩ t) := inter_maximals_subset

lemma _root_.is_antichain.maximals_eq (h : is_antichain r s) : maximals r s = s :=
(maximals_subset _ _).antisymm $ λ a ha, ⟨ha, λ b, h.eq ha⟩

lemma _root_.is_antichain.minimals_eq (h : is_antichain r s) : minimals r s = s :=
(minimals_subset _ _).antisymm $ λ a ha, ⟨ha, λ b, h.eq' ha⟩

@[simp] lemma maximals_idem : maximals r (maximals r s) = maximals r s :=
(maximals_antichain _ _).maximals_eq

@[simp] lemma minimals_idem : minimals r (minimals r s) = minimals r s := maximals_idem

/-- If `maximals r s` is included in but *shadows* the antichain `t`, then it is actually
equal to `t`. -/
lemma is_antichain.max_maximals (ht : is_antichain r t) (h : maximals r s ⊆ t)
  (hs : ∀ ⦃a⦄, a ∈ t → ∃ b ∈ maximals r s, r b a) :
  maximals r s = t :=
begin
  refine h.antisymm (λ a ha, _),
  obtain ⟨b, hb, hr⟩ := hs ha,
  rwa of_not_not (λ hab, ht (h hb) ha (ne.symm hab) hr),
end

/-- If `minimals r s` is included in but *shadows* the antichain `t`, then it is actually
equal to `t`. -/
lemma is_antichain.max_minimals (ht : is_antichain r t) (h : minimals r s ⊆ t)
  (hs : ∀ ⦃a⦄, a ∈ t → ∃ b ∈ minimals r s, r a b) :
  minimals r s = t :=
begin
  refine h.antisymm (λ a ha, _),
  obtain ⟨b, hb, hr⟩ := hs ha,
  rwa of_not_not (λ hab, ht ha (h hb) hab hr),
end

lemma exists_mem_maximals (hr₁ : reflexive r) (hr₂ : transitive r) (hr₃ : anti_symmetric r)
  {s : set α} (ih : ∀ c ⊆ s, is_chain r c → c.nonempty → ∃ ub ∈ s, ∀ z ∈ c, r z ub) (x ∈ s) :
  ∃ x' ∈ maximals r s, r x x' :=
begin
  resetI,
  suffices : ∃ m : s ∩ { y | r x y }, ∀ z : s ∩ { y | r x y }, r m z → r z m,
  { obtain ⟨⟨m, hm⟩, hm'⟩ := this,
    exact ⟨m, ⟨hm.1, λ y hy₁ hy₂,
      hr₃ hy₂ (hm' ⟨_, ⟨hy₁, hr₂ (show r x m, from hm.2) hy₂⟩⟩ hy₂)⟩, hm.2⟩ },
  haveI : nonempty (s ∩ { y | r x y } : _) := ⟨⟨x, H, hr₁ _⟩⟩,
  apply exists_maximal_of_nonempty_chains_bounded,
  rintro c hc hc',
  rcases c.eq_empty_or_nonempty with (rfl|⟨z, hz⟩),
  { exact ⟨⟨x, ⟨H, hr₁ _⟩⟩, λ _ h, h.elim⟩ },
  { obtain ⟨ub, h₁, h₂⟩ := ih (coe '' c) (λ x ⟨y, h⟩, h.2 ▸ y.prop.1)
      (hc.image _ _ _ (λ _ _, id)) (hc'.image _),
    exact ⟨⟨ub, ⟨h₁, hr₂ z.prop.2 (h₂ z ⟨z, hz, rfl⟩)⟩⟩, λ a ha, h₂ a ⟨a, ha, rfl⟩⟩ },
  { exact λ _ _ _ h₁ h₂, hr₂ h₁ h₂ }
end

lemma exists_mem_minimals (hr₁ : reflexive r) (hr₂ : transitive r) (hr₃ : anti_symmetric r)
  {s : set α} (ih : ∀ c ⊆ s, is_chain r c → c.nonempty → ∃ ub ∈ s, ∀ z ∈ c, r ub z) (x ∈ s) :
  ∃ x' ∈ minimals r s, r x' x :=
begin
  apply exists_mem_maximals,
  { exact hr₁ },
  { exact λ _ _ _ a b, hr₂ b a },
  { exactI λ _ _ a b, hr₃ b a },
  { exact λ c hc hc', ih c hc hc'.symm },
  { exact H }
end

variables [partial_order α]

lemma is_least.mem_minimals (h : is_least s a) : a ∈ minimals (≤) s :=
⟨h.1, λ b hb, (h.2 hb).antisymm⟩

lemma is_greatest.mem_maximals (h : is_greatest s a) : a ∈ maximals (≤) s :=
⟨h.1, λ b hb, (h.2 hb).antisymm'⟩

lemma is_least.minimals_eq (h : is_least s a) : minimals (≤) s = {a} :=
eq_singleton_iff_unique_mem.2 ⟨h.mem_minimals, λ b hb, hb.2 h.1 $ h.2 hb.1⟩

lemma is_greatest.maximals_eq (h : is_greatest s a) : maximals (≤) s = {a} :=
eq_singleton_iff_unique_mem.2 ⟨h.mem_maximals, λ b hb, hb.2 h.1 $ h.2 hb.1⟩

lemma is_antichain.minimals_upper_closure (hs : is_antichain (≤) s) :
  minimals (≤) (upper_closure s : set α) = s :=
hs.max_minimals (λ a ⟨⟨b, hb, hba⟩, h⟩, by rwa h (subset_upper_closure hb) hba) $ λ a ha,
  ⟨a, ⟨subset_upper_closure ha, λ b ⟨c, hc, hcb⟩ hba, hba.antisymm' $
    by rwa hs.eq' ha hc (hcb.trans hba)⟩, le_rfl⟩

lemma is_antichain.maximals_lower_closure (hs : is_antichain (≤) s) :
  maximals (≤) (lower_closure s : set α) = s :=
hs.to_dual.minimals_upper_closure

lemma exists_mem_maximals_le
  (ih : ∀ c ⊆ s, is_chain (≤) c → c.nonempty → ∃ ub ∈ s, ∀ z ∈ c, z ≤ ub) (x ∈ s) :
  ∃ x' ∈ maximals (≤) s, x ≤ x' :=
exists_mem_maximals le_refl (@le_trans α _) (@le_antisymm α _) ih x H

lemma exists_mem_minimals_le
  (ih : ∀ c ⊆ s, is_chain (≤) c → c.nonempty → ∃ lb ∈ s, ∀ z ∈ c, lb ≤ z) (x ∈ s) :
  ∃ x' ∈ minimals (≤) s, x' ≤ x :=
exists_mem_minimals le_refl (@le_trans α _) (@le_antisymm α _) ih x H

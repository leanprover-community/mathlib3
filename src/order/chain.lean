/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import data.set.pairwise
import data.set_like.basic

/-!
# Chains and flags

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines chains for an arbitrary relation and flags for an order and proves Hausdorff's
Maximality Principle.

## Main declarations

* `is_chain s`: A chain `s` is a set of comparable elements.
* `max_chain_spec`: Hausdorff's Maximality Principle.
* `flag`: The type of flags, aka maximal chains, of an order.

## Notes

Originally ported from Isabelle/HOL. The
[original file](https://isabelle.in.tum.de/dist/library/HOL/HOL/Zorn.html) was written by Jacques D.
Fleuriot, Tobias Nipkow, Christian Sternagel.
-/

open classical set

variables {α β : Type*}

/-! ### Chains -/

section chain
variables (r : α → α → Prop)

local infix ` ≺ `:50 := r

/-- A chain is a set `s` satisfying `x ≺ y ∨ x = y ∨ y ≺ x` for all `x y ∈ s`. -/
def is_chain (s : set α) : Prop := s.pairwise (λ x y, x ≺ y ∨ y ≺ x)

/-- `super_chain s t` means that `t` is a chain that strictly includes `s`. -/
def super_chain (s t : set α) : Prop := is_chain r t ∧ s ⊂ t

/-- A chain `s` is a maximal chain if there does not exists a chain strictly including `s`. -/
def is_max_chain (s : set α) : Prop := is_chain r s ∧ ∀ ⦃t⦄, is_chain r t → s ⊆ t → s = t

variables {r} {c c₁ c₂ c₃ s t : set α} {a b x y : α}

lemma is_chain_empty : is_chain r ∅ := set.pairwise_empty _

lemma set.subsingleton.is_chain (hs : s.subsingleton) : is_chain r s := hs.pairwise _

lemma is_chain.mono : s ⊆ t → is_chain r t → is_chain r s := set.pairwise.mono

lemma is_chain.mono_rel {r' : α → α → Prop} (h : is_chain r s)
  (h_imp : ∀ x y, r x y → r' x y) : is_chain r' s :=
h.mono' $ λ x y, or.imp (h_imp x y) (h_imp y x)

/-- This can be used to turn `is_chain (≥)` into `is_chain (≤)` and vice-versa. -/
lemma is_chain.symm (h : is_chain r s) : is_chain (flip r) s := h.mono' $ λ _ _, or.symm

lemma is_chain_of_trichotomous [is_trichotomous α r] (s : set α) : is_chain r s :=
λ a _ b _ hab, (trichotomous_of r a b).imp_right $ λ h, h.resolve_left hab

lemma is_chain.insert (hs : is_chain r s) (ha : ∀ b ∈ s, a ≠ b → a ≺ b ∨ b ≺ a) :
  is_chain r (insert a s) :=
hs.insert_of_symmetric (λ _ _, or.symm) ha

lemma is_chain_univ_iff : is_chain r (univ : set α) ↔ is_trichotomous α r :=
begin
  refine ⟨λ h, ⟨λ a b , _⟩, λ h, @is_chain_of_trichotomous _ _ h univ⟩,
  rw [or.left_comm, or_iff_not_imp_left],
  exact h trivial trivial,
end

lemma is_chain.image (r : α → α → Prop) (s : β → β → Prop) (f : α → β)
  (h : ∀ x y, r x y → s (f x) (f y)) {c : set α} (hrc : is_chain r c) :
  is_chain s (f '' c) :=
λ x ⟨a, ha₁, ha₂⟩ y ⟨b, hb₁, hb₂⟩, ha₂ ▸ hb₂ ▸ λ hxy,
  (hrc ha₁ hb₁ $ ne_of_apply_ne f hxy).imp (h _ _) (h _ _)

section total
variables [is_refl α r]

lemma is_chain.total (h : is_chain r s) (hx : x ∈ s) (hy : y ∈ s) : x ≺ y ∨ y ≺ x :=
(eq_or_ne x y).elim (λ e, or.inl $ e ▸ refl _) (h hx hy)

lemma is_chain.directed_on (H : is_chain r s) : directed_on r s :=
λ x hx y hy, (H.total hx hy).elim (λ h, ⟨y, hy, h, refl _⟩) $ λ h, ⟨x, hx, refl _, h⟩

protected lemma is_chain.directed {f : β → α} {c : set β} (h : is_chain (f ⁻¹'o r) c) :
  directed r (λ x : {a : β // a ∈ c}, f x) :=
λ ⟨a, ha⟩ ⟨b, hb⟩, by_cases
  (λ hab : a = b, by simp only [hab, exists_prop, and_self, subtype.exists];
    exact ⟨b, hb, refl _⟩) $
  λ hab, (h ha hb hab).elim (λ h, ⟨⟨b, hb⟩, h, refl _⟩) $ λ h, ⟨⟨a, ha⟩, refl _, h⟩

lemma is_chain.exists3 (hchain : is_chain r s) [is_trans α r] {a b c}
  (mem1 : a ∈ s) (mem2 : b ∈ s) (mem3 : c ∈ s) :
  ∃ (z) (mem4 : z ∈ s), r a z ∧ r b z ∧ r c z :=
begin
  rcases directed_on_iff_directed.mpr (is_chain.directed hchain) a mem1 b mem2 with
    ⟨z, mem4, H1, H2⟩,
  rcases directed_on_iff_directed.mpr (is_chain.directed hchain) z mem4 c mem3 with
    ⟨z', mem5, H3, H4⟩,
  exact ⟨z', mem5, trans H1 H3, trans H2 H3, H4⟩,
end

end total

lemma is_max_chain.is_chain (h : is_max_chain r s) : is_chain r s := h.1
lemma is_max_chain.not_super_chain (h : is_max_chain r s) : ¬super_chain r s t :=
λ ht, ht.2.ne $ h.2 ht.1 ht.2.1

lemma is_max_chain.bot_mem [has_le α] [order_bot α] (h : is_max_chain (≤) s) : ⊥ ∈ s :=
(h.2 (h.1.insert $ λ a _ _, or.inl bot_le) $ subset_insert _ _).symm ▸ mem_insert _ _

lemma is_max_chain.top_mem [has_le α] [order_top α] (h : is_max_chain (≤) s) : ⊤ ∈ s :=
(h.2 (h.1.insert $ λ a _ _, or.inr le_top) $ subset_insert _ _).symm ▸ mem_insert _ _

open_locale classical

/-- Given a set `s`, if there exists a chain `t` strictly including `s`, then `succ_chain s`
is one of these chains. Otherwise it is `s`. -/
def succ_chain (r : α → α → Prop) (s : set α) : set α :=
if h : ∃ t, is_chain r s ∧ super_chain r s t then some h else s

lemma succ_chain_spec (h : ∃ t, is_chain r s ∧ super_chain r s t) :
  super_chain r s (succ_chain r s) :=
let ⟨t, hc'⟩ := h in
have is_chain r s ∧ super_chain r s (some h),
  from @some_spec _ (λ t, is_chain r s ∧ super_chain r s t) _,
by simp [succ_chain, dif_pos, h, this.right]

lemma is_chain.succ (hs : is_chain r s) : is_chain r (succ_chain r s) :=
if h : ∃ t, is_chain r s ∧ super_chain r s t then (succ_chain_spec h).1
  else by { simp [succ_chain, dif_neg, h], exact hs }

lemma is_chain.super_chain_succ_chain (hs₁ : is_chain r s) (hs₂ : ¬ is_max_chain r s) :
  super_chain r s (succ_chain r s) :=
begin
  simp [is_max_chain, not_and_distrib, not_forall_not] at hs₂,
  obtain ⟨t, ht, hst⟩ := hs₂.neg_resolve_left hs₁,
  exact succ_chain_spec ⟨t, hs₁, ht, ssubset_iff_subset_ne.2 hst⟩,
end

lemma subset_succ_chain : s ⊆ succ_chain r s :=
if h : ∃ t, is_chain r s ∧ super_chain r s t then (succ_chain_spec h).2.1
  else by simp [succ_chain, dif_neg, h, subset.rfl]

/-- Predicate for whether a set is reachable from `∅` using `succ_chain` and `⋃₀`. -/
inductive chain_closure (r : α → α → Prop) : set α → Prop
| succ : ∀ {s}, chain_closure s → chain_closure (succ_chain r s)
| union : ∀ {s}, (∀ a ∈ s, chain_closure a) → chain_closure (⋃₀ s)

/-- An explicit maximal chain. `max_chain` is taken to be the union of all sets in `chain_closure`.
-/
def max_chain (r : α → α → Prop) := ⋃₀ set_of (chain_closure r)

lemma chain_closure_empty : chain_closure r ∅ :=
have chain_closure r (⋃₀ ∅),
  from chain_closure.union $ λ a h, h.rec _,
by simpa using this

lemma chain_closure_max_chain : chain_closure r (max_chain r) := chain_closure.union $ λ s, id

private lemma chain_closure_succ_total_aux (hc₁ : chain_closure r c₁) (hc₂ : chain_closure r c₂)
  (h : ∀ ⦃c₃⦄, chain_closure r c₃ → c₃ ⊆ c₂ → c₂ = c₃ ∨ succ_chain r c₃ ⊆ c₂) :
  succ_chain r c₂ ⊆ c₁ ∨ c₁ ⊆ c₂ :=
begin
  induction hc₁,
  case succ : c₃ hc₃ ih
  { cases ih with ih ih,
    { exact or.inl (ih.trans subset_succ_chain) },
    { exact (h hc₃ ih).imp_left (λ h, h ▸ subset.rfl) } },
  case union : s hs ih
  { refine (or_iff_not_imp_left.2 $ λ hn, sUnion_subset $ λ a ha, _),
    exact (ih a ha).resolve_left (λ h, hn $ h.trans $ subset_sUnion_of_mem ha) }
end

private lemma chain_closure_succ_total (hc₁ : chain_closure r c₁) (hc₂ : chain_closure r c₂)
  (h : c₁ ⊆ c₂) :
  c₂ = c₁ ∨ succ_chain r c₁ ⊆ c₂ :=
begin
  induction hc₂ generalizing c₁ hc₁ h,
  case succ : c₂ hc₂ ih
  { refine (chain_closure_succ_total_aux hc₁ hc₂ $ λ c₁, ih).imp h.antisymm' (λ h₁, _),
    obtain rfl | h₂ := ih hc₁ h₁,
    { exact subset.rfl },
    { exact h₂.trans subset_succ_chain } },
  case union : s hs ih
  { apply or.imp_left h.antisymm',
    apply classical.by_contradiction,
    simp [not_or_distrib, sUnion_subset_iff, not_forall],
    intros c₃ hc₃ h₁ h₂,
    obtain h | h := chain_closure_succ_total_aux hc₁ (hs c₃ hc₃) (λ c₄, ih _ hc₃),
    { exact h₁ (subset_succ_chain.trans h) },
    obtain h' | h' := ih c₃ hc₃ hc₁ h,
    { exact h₁ h'.subset },
    { exact h₂ (h'.trans $ subset_sUnion_of_mem hc₃) } }
end

lemma chain_closure.total (hc₁ : chain_closure r c₁) (hc₂ : chain_closure r c₂) :
  c₁ ⊆ c₂ ∨ c₂ ⊆ c₁ :=
(chain_closure_succ_total_aux hc₂ hc₁ $ λ c₃ hc₃, chain_closure_succ_total hc₃ hc₁).imp_left
  subset_succ_chain.trans

lemma chain_closure.succ_fixpoint (hc₁ : chain_closure r c₁) (hc₂ : chain_closure r c₂)
  (hc : succ_chain r c₂ = c₂) :
  c₁ ⊆ c₂ :=
begin
  induction hc₁,
  case succ : s₁ hc₁ h
  { exact (chain_closure_succ_total hc₁ hc₂ h).elim (λ h, h ▸ hc.subset) id },
  case union : s hs ih
  { exact sUnion_subset ih }
end

lemma chain_closure.succ_fixpoint_iff (hc : chain_closure r c) :
  succ_chain r c = c ↔ c = max_chain r :=
⟨λ h, (subset_sUnion_of_mem hc).antisymm $ chain_closure_max_chain.succ_fixpoint hc h,
  λ h, subset_succ_chain.antisymm' $ (subset_sUnion_of_mem hc.succ).trans h.symm.subset⟩

lemma chain_closure.is_chain (hc : chain_closure r c) : is_chain r c :=
begin
  induction hc,
  case succ : c hc h
  { exact h.succ },
  case union : s hs h
  { change ∀ c ∈ s, is_chain r c at h,
    exact λ c₁ ⟨t₁, ht₁, (hc₁ : c₁ ∈ t₁)⟩ c₂ ⟨t₂, ht₂, (hc₂ : c₂ ∈ t₂)⟩ hneq,
      ((hs _ ht₁).total $ hs _ ht₂).elim
        (λ ht, h t₂ ht₂ (ht hc₁) hc₂ hneq)
        (λ ht, h t₁ ht₁ hc₁ (ht hc₂) hneq) }
end

/-- **Hausdorff's maximality principle**

There exists a maximal totally ordered set of `α`.
Note that we do not require `α` to be partially ordered by `r`. -/
lemma max_chain_spec : is_max_chain r (max_chain r) :=
classical.by_contradiction $ λ h,
let ⟨h₁, H⟩ := chain_closure_max_chain.is_chain.super_chain_succ_chain h in
  H.ne (chain_closure_max_chain.succ_fixpoint_iff.mpr rfl).symm

end chain

/-! ### Flags -/

/-- The type of flags, aka maximal chains, of an order. -/
structure flag (α : Type*) [has_le α] :=
(carrier : set α)
(chain' : is_chain (≤) carrier)
(max_chain' : ∀ ⦃s⦄, is_chain (≤) s → carrier ⊆ s → carrier = s)

namespace flag
section has_le
variables [has_le α] {s t : flag α} {a : α}

instance : set_like (flag α) α :=
{ coe := carrier,
  coe_injective' := λ s t h, by { cases s, cases t, congr' } }

@[ext] lemma ext : (s : set α) = t → s = t := set_like.ext'
@[simp] lemma mem_coe_iff : a ∈ (s : set α) ↔ a ∈ s := iff.rfl
@[simp] lemma coe_mk (s : set α) (h₁ h₂) : (mk s h₁ h₂ : set α) = s := rfl
@[simp] lemma mk_coe (s : flag α) : mk (s : set α) s.chain' s.max_chain' = s := ext rfl

lemma chain_le (s : flag α) : is_chain (≤) (s : set α) := s.chain'
protected lemma max_chain (s : flag α) : is_max_chain (≤) (s : set α) := ⟨s.chain_le, s.max_chain'⟩

lemma top_mem [order_top α] (s : flag α) : (⊤ : α) ∈ s := s.max_chain.top_mem
lemma bot_mem [order_bot α] (s : flag α) : (⊥ : α) ∈ s := s.max_chain.bot_mem

end has_le

section preorder
variables [preorder α] {a b : α}

protected lemma le_or_le (s : flag α) (ha : a ∈ s) (hb : b ∈ s) : a ≤ b ∨ b ≤ a :=
s.chain_le.total ha hb

instance [order_top α] (s : flag α) : order_top s := subtype.order_top s.top_mem
instance [order_bot α] (s : flag α) : order_bot s := subtype.order_bot s.bot_mem
instance [bounded_order α] (s : flag α) : bounded_order s :=
subtype.bounded_order s.bot_mem s.top_mem

end preorder

section partial_order
variables [partial_order α]

lemma chain_lt (s : flag α) : is_chain (<) (s : set α) :=
λ a ha b hb h, (s.le_or_le ha hb).imp h.lt_of_le h.lt_of_le'

instance [decidable_eq α] [@decidable_rel α (≤)] [@decidable_rel α (<)] (s : flag α) :
  linear_order s :=
{ le_total := λ a b, s.le_or_le a.2 b.2,
  decidable_eq := subtype.decidable_eq,
  decidable_le := subtype.decidable_le,
  decidable_lt := subtype.decidable_lt,
  ..subtype.partial_order _ }

end partial_order

instance [linear_order α] : unique (flag α) :=
{ default := ⟨univ, is_chain_of_trichotomous _, λ s _, s.subset_univ.antisymm'⟩,
  uniq := λ s, set_like.coe_injective $ s.3 (is_chain_of_trichotomous _) $ subset_univ _ }

end flag

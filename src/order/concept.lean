/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.set.lattice

/-!
# Formal concept analysis

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines concept lattices. A concept of a relation `r : α → β → Prop` is a pair of sets
`s : set α` and `t : set β` such that `s` is the set of all `a : α` that are related to all elements
of `t`, and `t` is the set of all `b : β` that are related to all elements of `s`.

Ordering the concepts of a relation `r` by inclusion on the first component gives rise to a
*concept lattice*. Every concept lattice is complete and in fact every complete lattice arises as
the concept lattice of its `≤`.

## Implementation notes

Concept lattices are usually defined from a *context*, that is the triple `(α, β, r)`, but the type
of `r` determines `α` and `β` already, so we do not define contexts as a separate object.

## TODO

Prove the fundamental theorem of concept lattices.

## References

* [Davey, Priestley *Introduction to Lattices and Order*][davey_priestley]

## Tags

concept, formal concept analysis, intent, extend, attribute
-/

open function order_dual set

variables {ι : Sort*} {α β γ : Type*} {κ : ι → Sort*} (r : α → β → Prop) {s s₁ s₂ : set α}
  {t t₁ t₂ : set β}

/-! ### Intent and extent -/

/-- The intent closure of `s : set α` along a relation `r : α → β → Prop` is the set of all elements
which `r` relates to all elements of `s`. -/
def intent_closure (s : set α) : set β := {b | ∀ ⦃a⦄, a ∈ s → r a b}

/-- The extent closure of `t : set β` along a relation `r : α → β → Prop` is the set of all elements
which `r` relates to all elements of `t`. -/
def extent_closure (t : set β) : set α := {a | ∀ ⦃b⦄, b ∈ t → r a b}

variables {r}

lemma subset_intent_closure_iff_subset_extent_closure :
  t ⊆ intent_closure r s ↔ s ⊆ extent_closure r t :=
⟨λ h a ha b hb, h hb ha, λ h b hb a ha, h ha hb⟩

variables (r)

lemma gc_intent_closure_extent_closure :
  galois_connection (to_dual ∘ intent_closure r) (extent_closure r ∘ of_dual) :=
λ s t, subset_intent_closure_iff_subset_extent_closure

lemma intent_closure_swap (t : set β) : intent_closure (swap r) t = extent_closure r t := rfl
lemma extent_closure_swap (s : set α) : extent_closure (swap r) s = intent_closure r s := rfl

@[simp] lemma intent_closure_empty : intent_closure r ∅ = univ :=
eq_univ_of_forall $ λ _ _, false.elim

@[simp] lemma extent_closure_empty : extent_closure r ∅ = univ := intent_closure_empty _

@[simp] lemma intent_closure_union (s₁ s₂ : set α) :
  intent_closure r (s₁ ∪ s₂) = intent_closure r s₁ ∩ intent_closure r s₂ :=
set.ext $ λ _, ball_or_left_distrib

@[simp] lemma extent_closure_union (t₁ t₂ : set β) :
  extent_closure r (t₁ ∪ t₂) = extent_closure r t₁ ∩ extent_closure r t₂ :=
intent_closure_union _ _ _

@[simp] lemma intent_closure_Union (f : ι → set α) :
  intent_closure r (⋃ i, f i) = ⋂ i, intent_closure r (f i) :=
(gc_intent_closure_extent_closure r).l_supr

@[simp] lemma extent_closure_Union (f : ι → set β) :
  extent_closure r (⋃ i, f i) = ⋂ i, extent_closure r (f i) :=
intent_closure_Union _ _

@[simp] lemma intent_closure_Union₂ (f : Π i, κ i → set α) :
  intent_closure r (⋃ i j, f i j) = ⋂ i j, intent_closure r (f i j) :=
(gc_intent_closure_extent_closure r).l_supr₂

@[simp] lemma extent_closure_Union₂ (f : Π i, κ i → set β) :
  extent_closure r (⋃ i j, f i j) = ⋂ i j, extent_closure r (f i j) :=
intent_closure_Union₂ _ _

lemma subset_extent_closure_intent_closure (s : set α) :
  s ⊆ extent_closure r (intent_closure r s) :=
(gc_intent_closure_extent_closure r).le_u_l _

lemma subset_intent_closure_extent_closure (t : set β) :
  t ⊆ intent_closure r (extent_closure r t) :=
subset_extent_closure_intent_closure _ t

@[simp] lemma intent_closure_extent_closure_intent_closure (s : set α) :
  intent_closure r (extent_closure r $ intent_closure r s) = intent_closure r s :=
(gc_intent_closure_extent_closure r).l_u_l_eq_l _

@[simp] lemma extent_closure_intent_closure_extent_closure (t : set β) :
  extent_closure r (intent_closure r $ extent_closure r t) = extent_closure r t :=
intent_closure_extent_closure_intent_closure _ t

lemma intent_closure_anti : antitone (intent_closure r) :=
(gc_intent_closure_extent_closure r).monotone_l

lemma extent_closure_anti : antitone (extent_closure r) := intent_closure_anti _

/-! ### Concepts -/

variables (α β)

/-- The formal concepts of a relation. A concept of `r : α → β → Prop` is a pair of sets `s`, `t`
such that `s` is the set of all elements that are `r`-related to all of `t` and `t` is the set of
all elements that are `r`-related to all of `s`. -/
structure concept extends set α × set β :=
(closure_fst : intent_closure r fst = snd)
(closure_snd : extent_closure r snd = fst)

namespace concept
variables {r α β} {c d : concept α β r}

attribute [simp] closure_fst closure_snd

@[ext] lemma ext (h : c.fst = d.fst) : c = d :=
begin
  obtain ⟨⟨s₁, t₁⟩, h₁, _⟩ := c,
  obtain ⟨⟨s₂, t₂⟩, h₂, _⟩ := d,
  dsimp at h₁ h₂ h,
  subst h,
  subst h₁,
  subst h₂,
end

lemma ext' (h : c.snd = d.snd) : c = d :=
begin
  obtain ⟨⟨s₁, t₁⟩, _, h₁⟩ := c,
  obtain ⟨⟨s₂, t₂⟩, _, h₂⟩ := d,
  dsimp at h₁ h₂ h,
  subst h,
  subst h₁,
  subst h₂,
end

lemma fst_injective : injective (λ c : concept α β r, c.fst) := λ c d, ext
lemma snd_injective : injective (λ c : concept α β r, c.snd) := λ c d, ext'

instance : has_sup (concept α β r) :=
⟨λ c d, { fst := extent_closure r (c.snd ∩ d.snd),
  snd := c.snd ∩ d.snd,
  closure_fst := by rw [←c.closure_fst, ←d.closure_fst, ←intent_closure_union,
    intent_closure_extent_closure_intent_closure],
  closure_snd := rfl }⟩

instance : has_inf (concept α β r) :=
⟨λ c d, { fst := c.fst ∩ d.fst,
  snd := intent_closure r (c.fst ∩ d.fst),
  closure_fst := rfl,
  closure_snd := by rw [←c.closure_snd, ←d.closure_snd, ←extent_closure_union,
    extent_closure_intent_closure_extent_closure] }⟩

instance : semilattice_inf (concept α β r) := fst_injective.semilattice_inf _ $ λ _ _, rfl

@[simp] lemma fst_subset_fst_iff : c.fst ⊆ d.fst ↔ c ≤ d := iff.rfl
@[simp] lemma fst_ssubset_fst_iff : c.fst ⊂ d.fst ↔ c < d := iff.rfl

@[simp] lemma snd_subset_snd_iff : c.snd ⊆ d.snd ↔ d ≤ c :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rw [←fst_subset_fst_iff, ←c.closure_snd, ←d.closure_snd],
    exact extent_closure_anti _ h },
  { rw [←c.closure_fst, ←d.closure_fst],
    exact intent_closure_anti _ h }
end

@[simp] lemma snd_ssubset_snd_iff : c.snd ⊂ d.snd ↔ d < c :=
by rw [ssubset_iff_subset_not_subset, lt_iff_le_not_le, snd_subset_snd_iff, snd_subset_snd_iff]

lemma strict_mono_fst : strict_mono (prod.fst ∘ to_prod : concept α β r → set α) :=
λ c d, fst_ssubset_fst_iff.2

lemma strict_anti_snd : strict_anti (prod.snd ∘ to_prod : concept α β r → set β) :=
λ c d, snd_ssubset_snd_iff.2

instance : lattice (concept α β r) :=
{ sup := (⊔),
  le_sup_left := λ c d, snd_subset_snd_iff.1 $ inter_subset_left _ _,
  le_sup_right := λ c d, snd_subset_snd_iff.1 $ inter_subset_right _ _,
  sup_le := λ c d e, by { simp_rw ←snd_subset_snd_iff, exact subset_inter },
  ..concept.semilattice_inf }

instance : bounded_order (concept α β r) :=
{ top := ⟨⟨univ, intent_closure r univ⟩, rfl, eq_univ_of_forall $ λ a b hb, hb trivial⟩,
  le_top := λ _, subset_univ _,
  bot := ⟨⟨extent_closure r univ, univ⟩, eq_univ_of_forall $ λ b a ha, ha trivial, rfl⟩,
  bot_le := λ _, snd_subset_snd_iff.1 $ subset_univ _ }

instance : has_Sup (concept α β r) :=
⟨λ S, { fst := extent_closure r (⋂ c ∈ S, (c : concept _ _ _).snd),
        snd := ⋂ c ∈ S, (c : concept _ _ _).snd,
        closure_fst := by simp_rw [←closure_fst, ←intent_closure_Union₂,
          intent_closure_extent_closure_intent_closure],
        closure_snd := rfl }⟩

instance : has_Inf (concept α β r) :=
⟨λ S, { fst := ⋂ c ∈ S, (c : concept _ _ _).fst,
        snd := intent_closure r (⋂ c ∈ S, (c : concept _ _ _).fst),
        closure_fst := rfl,
        closure_snd := by simp_rw [←closure_snd, ←extent_closure_Union₂,
          extent_closure_intent_closure_extent_closure] }⟩

instance : complete_lattice (concept α β r) :=
{ Sup := Sup,
  le_Sup := λ S c hc, snd_subset_snd_iff.1 $ bInter_subset_of_mem hc,
  Sup_le := λ S c hc, snd_subset_snd_iff.1 $ subset_Inter₂ $ λ d hd, snd_subset_snd_iff.2 $ hc d hd,
  Inf := Inf,
  Inf_le := λ S c, bInter_subset_of_mem,
  le_Inf := λ S c, subset_Inter₂,
  ..concept.lattice, ..concept.bounded_order }

@[simp] lemma top_fst : (⊤ : concept α β r).fst = univ := rfl
@[simp] lemma top_snd : (⊤ : concept α β r).snd = intent_closure r univ := rfl
@[simp] lemma bot_fst : (⊥ : concept α β r).fst = extent_closure r univ := rfl
@[simp] lemma bot_snd : (⊥ : concept α β r).snd = univ := rfl
@[simp] lemma sup_fst (c d : concept α β r) : (c ⊔ d).fst = extent_closure r (c.snd ∩ d.snd) := rfl
@[simp] lemma sup_snd (c d : concept α β r) : (c ⊔ d).snd = c.snd ∩ d.snd := rfl
@[simp] lemma inf_fst (c d : concept α β r) : (c ⊓ d).fst = c.fst ∩ d.fst := rfl
@[simp] lemma inf_snd (c d : concept α β r) : (c ⊓ d).snd = intent_closure r (c.fst ∩ d.fst) := rfl
@[simp] lemma Sup_fst (S : set (concept α β r)) :
  (Sup S).fst = extent_closure r ⋂ c ∈ S, (c : concept _ _ _).snd := rfl
@[simp] lemma Sup_snd (S : set (concept α β r)) : (Sup S).snd = ⋂ c ∈ S, (c : concept _ _ _).snd :=
rfl
@[simp] lemma Inf_fst (S : set (concept α β r)) : (Inf S).fst = ⋂ c ∈ S, (c : concept _ _ _).fst :=
rfl
@[simp] lemma Inf_snd (S : set (concept α β r)) :
  (Inf S).snd = intent_closure r ⋂ c ∈ S, (c : concept _ _ _).fst := rfl

instance : inhabited (concept α β r) := ⟨⊥⟩

/-- Swap the sets of a concept to make it a concept of the dual context. -/
@[simps] def swap (c : concept α β r) : concept β α (swap r) :=
⟨c.to_prod.swap, c.closure_snd, c.closure_fst⟩

@[simp] lemma swap_swap (c : concept α β r) : c.swap.swap = c := ext rfl

@[simp] lemma swap_le_swap_iff : c.swap ≤ d.swap ↔ d ≤ c := snd_subset_snd_iff
@[simp] lemma swap_lt_swap_iff : c.swap < d.swap ↔ d < c := snd_ssubset_snd_iff

/-- The dual of a concept lattice is isomorphic to the concept lattice of the dual context. -/
@[simps] def swap_equiv : (concept α β r)ᵒᵈ ≃o concept β α (function.swap r) :=
{ to_fun := swap ∘ of_dual,
  inv_fun := to_dual ∘ swap,
  left_inv := swap_swap,
  right_inv := swap_swap,
  map_rel_iff' := λ c d, swap_le_swap_iff }

end concept

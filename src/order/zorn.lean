/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Zorn's lemmas.

Ported from Isabelle/HOL (written by Jacques D. Fleuriot, Tobias Nipkow, and Christian Sternagel).
-/
import data.set.lattice order.order_iso
noncomputable theory

universes u
open set classical
local attribute [instance] prop_decidable

namespace zorn

section chain
parameters {α : Type u} (r : α → α → Prop)
local infix ` ≺ `:50  := r

/-- A chain is a subset `c` satisfying
  `x ≺ y ∨ x = y ∨ y ≺ x` for all `x y ∈ c`. -/
def chain (c : set α) := pairwise_on c (λx y, x ≺ y ∨ y ≺ x)
parameters {r}

theorem chain.total_of_refl [is_refl α r]
  {c} (H : chain c) {x y} (hx : x ∈ c) (hy : y ∈ c) :
  x ≺ y ∨ y ≺ x :=
if e : x = y then or.inl (e ▸ refl _) else H _ hx _ hy e

theorem chain.directed [is_refl α r]
  {c} (H : chain c) {x y} (hx : x ∈ c) (hy : y ∈ c) :
  ∃ z, z ∈ c ∧ x ≺ z ∧ y ≺ z :=
match H.total_of_refl hx hy with
| or.inl h := ⟨y, hy, h, refl _⟩
| or.inr h := ⟨x, hx, refl _, h⟩
end

theorem chain.mono {c c'} : c' ⊆ c → chain c → chain c' :=
pairwise_on.mono

theorem chain.directed_on [is_refl α r] {c} (H : chain c) : directed_on (≺) c :=
λ x xc y yc, let ⟨z, hz, h⟩ := H.directed xc yc in ⟨z, hz, h⟩

theorem chain_insert {c : set α} {a : α} (hc : chain c) (ha : ∀b∈c, b ≠ a → a ≺ b ∨ b ≺ a) :
  chain (insert a c) :=
forall_insert_of_forall
  (assume x hx, forall_insert_of_forall (hc x hx) (assume hneq, (ha x hx hneq).symm))
  (forall_insert_of_forall (assume x hx hneq, ha x hx $ assume h', hneq h'.symm) (assume h, (h rfl).rec _))

def super_chain (c₁ c₂ : set α) := chain c₂ ∧ c₁ ⊂ c₂

def is_max_chain (c : set α) := chain c ∧ ¬ (∃c', super_chain c c')

def succ_chain (c : set α) :=
if h : ∃c', chain c ∧ super_chain c c' then some h else c

theorem succ_spec {c : set α} (h : ∃c', chain c ∧ super_chain c c') :
  super_chain c (succ_chain c) :=
let ⟨c', hc'⟩ := h in
have chain c ∧ super_chain c (some h),
  from @some_spec _ (λc', chain c ∧ super_chain c c') _,
by simp [succ_chain, dif_pos, h, this.right]

theorem chain_succ {c : set α} (hc : chain c) : chain (succ_chain c) :=
if h : ∃c', chain c ∧ super_chain c c' then
  (succ_spec h).left
else
  by simp [succ_chain, dif_neg, h]; exact hc

theorem super_of_not_max {c : set α} (hc₁ : chain c) (hc₂ : ¬ is_max_chain c) :
  super_chain c (succ_chain c) :=
begin
  simp [is_max_chain, not_and_distrib, not_forall_not] at hc₂,
  cases hc₂.neg_resolve_left hc₁ with c' hc',
  exact succ_spec ⟨c', hc₁, hc'⟩
end

theorem succ_increasing {c : set α} : c ⊆ succ_chain c :=
if h : ∃c', chain c ∧ super_chain c c' then
  have super_chain c (succ_chain c), from succ_spec h,
  this.right.left
else by simp [succ_chain, dif_neg, h, subset.refl]

inductive chain_closure : set α → Prop
| succ : ∀{s}, chain_closure s → chain_closure (succ_chain s)
| union : ∀{s}, (∀a∈s, chain_closure a) → chain_closure (⋃₀ s)

theorem chain_closure_empty : chain_closure ∅ :=
have chain_closure (⋃₀ ∅),
  from chain_closure.union $ assume a h, h.rec _,
by simp at this; assumption

theorem chain_closure_closure : chain_closure (⋃₀ chain_closure) :=
chain_closure.union $ assume s hs, hs

variables {c c₁ c₂ c₃ : set α}

private lemma chain_closure_succ_total_aux (hc₁ : chain_closure c₁) (hc₂ : chain_closure c₂)
  (h : ∀{c₃}, chain_closure c₃ → c₃ ⊆ c₂ → c₂ = c₃ ∨ succ_chain c₃ ⊆ c₂) :
  c₁ ⊆ c₂ ∨ succ_chain c₂ ⊆ c₁ :=
begin
  induction hc₁,
  case _root_.zorn.chain_closure.succ : c₃ hc₃ ih {
    cases ih with ih ih,
    { have h := h hc₃ ih,
      cases h with h h,
      { exact or.inr (h ▸ subset.refl _) },
      { exact or.inl h } },
    { exact or.inr (subset.trans ih succ_increasing) } },
  case _root_.zorn.chain_closure.union : s hs ih {
    refine (classical.or_iff_not_imp_right.2 $ λ hn, sUnion_subset $ λ a ha, _),
    apply (ih a ha).resolve_right,
    apply mt (λ h, _) hn,
    exact subset.trans h (subset_sUnion_of_mem ha) }
end

private lemma chain_closure_succ_total (hc₁ : chain_closure c₁) (hc₂ : chain_closure c₂) (h : c₁ ⊆ c₂) :
  c₂ = c₁ ∨ succ_chain c₁ ⊆ c₂ :=
begin
  induction hc₂ generalizing c₁ hc₁ h,
  case _root_.zorn.chain_closure.succ : c₂ hc₂ ih {
    have h₁ : c₁ ⊆ c₂ ∨ @succ_chain α r c₂ ⊆ c₁ :=
      (chain_closure_succ_total_aux hc₁ hc₂ $ assume c₁, ih),
    cases h₁ with h₁ h₁,
    { have h₂ := ih hc₁ h₁,
      cases h₂ with h₂ h₂,
      { exact (or.inr $ h₂ ▸ subset.refl _) },
      { exact (or.inr $ subset.trans h₂ succ_increasing) } },
    { exact (or.inl $ subset.antisymm h₁ h) } },
  case _root_.zorn.chain_closure.union : s hs ih {
    apply or.imp_left (assume h', subset.antisymm h' h),
    apply classical.by_contradiction,
    simp [not_or_distrib, sUnion_subset_iff, classical.not_forall],
    intros c₃ hc₃ h₁ h₂,
    have h := chain_closure_succ_total_aux hc₁ (hs c₃ hc₃) (assume c₄, ih _ hc₃),
    cases h with h h,
    { have h' := ih c₃ hc₃ hc₁ h,
      cases h' with h' h',
      { exact (h₁ $ h' ▸ subset.refl _) },
      { exact (h₂ $ subset.trans h' $ subset_sUnion_of_mem hc₃) } },
    { exact (h₁ $ subset.trans succ_increasing h) } }
end

theorem chain_closure_total (hc₁ : chain_closure c₁) (hc₂ : chain_closure c₂) : c₁ ⊆ c₂ ∨ c₂ ⊆ c₁ :=
have c₁ ⊆ c₂ ∨ succ_chain c₂ ⊆ c₁,
  from chain_closure_succ_total_aux hc₁ hc₂ $ assume c₃ hc₃, chain_closure_succ_total hc₃ hc₂,
or.imp_right (assume : succ_chain c₂ ⊆ c₁, subset.trans succ_increasing this) this

theorem chain_closure_succ_fixpoint (hc₁ : chain_closure c₁) (hc₂ : chain_closure c₂)
  (h_eq : succ_chain c₂ = c₂) : c₁ ⊆ c₂ :=
begin
  induction hc₁,
  case _root_.zorn.chain_closure.succ : c₁ hc₁ h {
    exact or.elim (chain_closure_succ_total hc₁ hc₂ h)
      (assume h, h ▸ h_eq.symm ▸ subset.refl c₂) id },
  case _root_.zorn.chain_closure.union : s hs ih {
    exact (sUnion_subset $ assume c₁ hc₁, ih c₁ hc₁) }
end

theorem chain_closure_succ_fixpoint_iff (hc : chain_closure c) :
  succ_chain c = c ↔ c = ⋃₀ chain_closure :=
⟨assume h, subset.antisymm
    (subset_sUnion_of_mem hc)
    (chain_closure_succ_fixpoint chain_closure_closure hc h),
  assume : c = ⋃₀{c : set α | chain_closure c},
  subset.antisymm
    (calc succ_chain c ⊆ ⋃₀{c : set α | chain_closure c} :
        subset_sUnion_of_mem $ chain_closure.succ hc
      ... = c : this.symm)
    succ_increasing⟩

theorem chain_chain_closure (hc : chain_closure c) : chain c :=
begin
  induction hc,
  case _root_.zorn.chain_closure.succ : c hc h {
    exact chain_succ h },
  case _root_.zorn.chain_closure.union : s hs h {
    have h : ∀c∈s, zorn.chain c := h,
    exact assume c₁ ⟨t₁, ht₁, (hc₁ : c₁ ∈ t₁)⟩ c₂ ⟨t₂, ht₂, (hc₂ : c₂ ∈ t₂)⟩ hneq,
      have t₁ ⊆ t₂ ∨ t₂ ⊆ t₁, from chain_closure_total (hs _ ht₁) (hs _ ht₂),
      or.elim this
        (assume : t₁ ⊆ t₂, h t₂ ht₂ c₁ (this hc₁) c₂ hc₂ hneq)
        (assume : t₂ ⊆ t₁, h t₁ ht₁ c₁ hc₁ c₂ (this hc₂) hneq) }
end

def max_chain := ⋃₀ chain_closure

/-- Hausdorff's maximality principle

There exists a maximal totally ordered subset of `α`.
Note that we do not require `α` to be partially ordered by `r`. -/
theorem max_chain_spec : is_max_chain max_chain :=
classical.by_contradiction $
assume : ¬ is_max_chain (⋃₀ chain_closure),
have super_chain (⋃₀ chain_closure) (succ_chain (⋃₀ chain_closure)),
  from super_of_not_max (chain_chain_closure chain_closure_closure) this,
let ⟨h₁, h₂, (h₃ : (⋃₀ chain_closure) ≠ succ_chain (⋃₀ chain_closure))⟩ := this in
have succ_chain (⋃₀ chain_closure) = (⋃₀ chain_closure),
  from (chain_closure_succ_fixpoint_iff chain_closure_closure).mpr rfl,
h₃ this.symm

/-- Zorn's lemma

If every chain has an upper bound, then there is a maximal element -/
theorem zorn (h : ∀c, chain c → ∃ub, ∀a∈c, a ≺ ub) (trans : ∀{a b c}, a ≺ b → b ≺ c → a ≺ c) :
  ∃m, ∀a, m ≺ a → a ≺ m :=
have ∃ub, ∀a∈max_chain, a ≺ ub,
  from h _ $ max_chain_spec.left,
let ⟨ub, (hub : ∀a∈max_chain, a ≺ ub)⟩ := this in
⟨ub, assume a ha,
  have chain (insert a max_chain),
    from chain_insert max_chain_spec.left $ assume b hb _, or.inr $ trans (hub b hb) ha,
  have a ∈ max_chain, from
    classical.by_contradiction $ assume h : a ∉ max_chain,
    max_chain_spec.right $ ⟨insert a max_chain, this, ssubset_insert h⟩,
  hub a this⟩

end chain

theorem zorn_partial_order {α : Type u} [partial_order α]
  (h : ∀c:set α, @chain α (≤) c → ∃ub, ∀a∈c, a ≤ ub) : ∃m:α, ∀a, m ≤ a → a = m :=
let ⟨m, hm⟩ := @zorn α (≤) h (assume a b c, le_trans) in
⟨m, assume a ha, le_antisymm (hm a ha) ha⟩

theorem zorn_partial_order₀ {α : Type u} [partial_order α] (s : set α)
  (ih : ∀ c ⊆ s, chain (≤) c → ∀ y ∈ c, ∃ ub ∈ s, ∀ z ∈ c, z ≤ ub)
  (x : α) (hxs : x ∈ s) : ∃ m ∈ s, x ≤ m ∧ ∀ z ∈ s, m ≤ z → z = m :=
let ⟨⟨m, hms, hxm⟩, h⟩ := @zorn_partial_order {m // m ∈ s ∧ x ≤ m} _ (λ c hc, classical.by_cases
  (assume hce : c = ∅, hce.symm ▸ ⟨⟨x, hxs, le_refl _⟩, λ _, false.elim⟩)
  (assume hce : c ≠ ∅, let ⟨m, hmc⟩ := set.exists_mem_of_ne_empty hce in
    let ⟨ub, hubs, hub⟩ := ih (subtype.val '' c) (image_subset_iff.2 $ λ z hzc, z.2.1)
    (by rintro _ ⟨p, hpc, rfl⟩ _ ⟨q, hqc, rfl⟩ hpq;
      exact hc p hpc q hqc (mt (by rintro rfl; refl) hpq)) m.1 (mem_image_of_mem _ hmc) in
    ⟨⟨ub, hubs, le_trans m.2.2 $ hub m.1 $ mem_image_of_mem _ hmc⟩, λ a hac, hub a.1 ⟨a, hac, rfl⟩⟩)) in
⟨m, hms, hxm, λ z hzs hmz, congr_arg subtype.val $ h ⟨z, hzs, le_trans hxm hmz⟩ hmz⟩

theorem zorn_subset {α : Type u} (S : set (set α))
  (h : ∀c ⊆ S, chain (⊆) c → ∃ub ∈ S, ∀ s ∈ c, s ⊆ ub) :
  ∃ m ∈ S, ∀a ∈ S, m ⊆ a → a = m :=
begin
  letI : partial_order S := partial_order.lift subtype.val (λ _ _, subtype.eq'),
  have : ∀c:set S, @chain S (≤) c → ∃ub, ∀a∈c, a ≤ ub,
  { intros c hc,
    rcases h (subtype.val '' c) (image_subset_iff.2 _) _ with ⟨s, sS, hs⟩,
    { exact ⟨⟨s, sS⟩, λ ⟨x, hx⟩ H, hs _ (mem_image_of_mem _ H)⟩ },
    { rintro ⟨x, hx⟩ _, exact hx },
    { rintro _ ⟨x, cx, rfl⟩ _ ⟨y, cy, rfl⟩ xy,
      exact hc x cx y cy (mt (congr_arg _) xy) } },
  rcases zorn_partial_order this with ⟨⟨m, mS⟩, hm⟩,
  exact ⟨m, mS, λ a aS ha, congr_arg subtype.val (hm ⟨a, aS⟩ ha)⟩
end

theorem zorn_subset₀ {α : Type u} (S : set (set α))
  (H : ∀c ⊆ S, chain (⊆) c → c ≠ ∅ → ∃ub ∈ S, ∀ s ∈ c, s ⊆ ub) (x) (hx : x ∈ S) :
  ∃ m ∈ S, x ⊆ m ∧ ∀a ∈ S, m ⊆ a → a = m :=
begin
  let T := {s ∈ S | x ⊆ s},
  rcases zorn_subset T _ with ⟨m, ⟨mS, mx⟩, hm⟩,
  { exact ⟨m, mS, mx, λ a ha ha', hm a ⟨ha, subset.trans mx ha'⟩ ha'⟩ },
  { intros c cT hc,
    by_cases c0 : c = ∅,
    { rw c0, exact ⟨x, ⟨hx, subset.refl _⟩, λ _, false.elim⟩ },
    { rcases H _ (subset.trans cT (sep_subset _ _)) hc c0 with ⟨ub, us, h⟩,
      refine ⟨ub, ⟨us, _⟩, h⟩,
      rcases ne_empty_iff_exists_mem.1 c0 with ⟨s, hs⟩,
      exact subset.trans (cT hs).2 (h _ hs) } }
end

theorem chain.total {α : Type u} [preorder α]
  {c} (H : @chain α (≤) c) :
  ∀ {x y}, x ∈ c → y ∈ c → x ≤ y ∨ y ≤ x :=
@chain.total_of_refl _ (≤) ⟨le_refl⟩ _ H

end zorn

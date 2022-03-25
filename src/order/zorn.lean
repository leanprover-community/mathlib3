/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import data.set.pairwise

/-!
# Chains and Zorn's lemmas

This file defines chains for an arbitrary relation and proves several formulations of Zorn's Lemma,
along with Hausdorff's Maximality Principle.

## Main declarations

* `is_chain s`: A chain `s` is a set of comparable elements.
* `max_chain_spec`: Hausdorff's Maximality Principle.
* `exists_maximal_of_chains_bounded`: Zorn's Lemma. Many variants are offered.

## Variants

The primary statement of Zorn's lemma is `exists_maximal_of_chains_bounded`. Then it is specialized
to particular relations:
* `(≤)` with `zorn_partial_order`
* `(⊆)` with `zorn_subset`
* `(⊇)` with `zorn_superset`

Lemma names carry modifiers:
* `₀`: Quantifies over a set, as opposed to over a type.
* `_nonempty`: Doesn't ask to prove that the empty chain is bounded and lets you give an element
  that will be smaller than the maximal element found (the maximal element is no smaller than any
  other element, but it can also be incomparable to some).

## How-to

This file comes across as confusing to those who haven't yet used it, so here is a detailed
walkthrough:
1. Know what relation on which type/set you're looking for. See Variants above. You can discharge
  some conditions to Zorn's lemma directly using a `_nonempty` variant.
2. Write down the definition of your type/set, put a `suffices : ∃ m, ∀ a, m ≺ a → a ≺ m, { ... },`
  (or whatever you actually need) followed by a `apply some_version_of_zorn`.
3. Fill in the details. This is where you start talking about chains.

A typical proof using Zorn could look like this
```lean
lemma zorny_lemma : zorny_statement :=
begin
  let s : set α := {x | whatever x},
  suffices : ∃ x ∈ s, ∀ y ∈ s, y ⊆ x → y = x, -- or with another operator
  { exact proof_post_zorn },
  apply zorn_subset, -- or another variant
  rintro c hcs hc,
  obtain rfl | hcnemp := c.eq_empty_or_nonempty, -- you might need to disjunct on c empty or not
  { exact ⟨edge_case_construction,
      proof_that_edge_case_construction_respects_whatever,
      proof_that_edge_case_construction_contains_all_stuff_in_c⟩ },
  exact ⟨construction,
    proof_that_construction_respects_whatever,
    proof_that_construction_contains_all_stuff_in_c⟩,
end
```

## Notes

Originally ported from Isabelle/HOL. The
[original file](https://isabelle.in.tum.de/dist/library/HOL/HOL/Zorn.html) was written by Jacques D.
Fleuriot, Tobias Nipkow, Christian Sternagel.
-/

noncomputable theory

open classical set

variables {α β : Type*} (r : α → α → Prop)

local infix ` ≺ `:50  := r

/-! ### Chains -/

section chain
variables (r)

/-- A chain is a subset `s` satisfying `x ≺ y ∨ x = y ∨ y ≺ x` for all `x y ∈ s`. -/
def is_chain (s : set α) := s.pairwise (λ x y, x ≺ y ∨ y ≺ x)

/-- `super_chain s t` means that `t` is a chain that strictly includes `s`. -/
def super_chain (s t : set α) : Prop := is_chain r t ∧ s ⊂ t

/-- A chain `s` is a maximal chain if there does not exists a chain strictly including `s`. -/
def is_max_chain (s : set α) := is_chain r s ∧ ∀ ⦃t⦄, is_chain r t → s ⊆ t → s = t

variables {r} {c c₁ c₂ c₃ s t : set α} {a b x y : α}

lemma is_chain_empty : is_chain r ∅ := set.pairwise_empty _

lemma set.subsingleton.is_chain (hs : s.subsingleton) : is_chain r s := hs.pairwise _

lemma is_chain.mono : s ⊆ t → is_chain r t → is_chain r s := set.pairwise.mono

lemma is_chain.total [is_refl α r] (h : is_chain r s) (hx : x ∈ s) (hy : y ∈ s) : x ≺ y ∨ y ≺ x :=
by { classical, exact if e : x = y then or.inl (e ▸ refl _) else h hx hy e }

/-- This can be used to turn `is_chain (≥)` into `is_chain (≤)` and vice-versa. -/
lemma is_chain.symm (h : is_chain r s) : is_chain (flip r) s := h.mono' $ λ _ _, or.symm

lemma is_chain_of_trichotomous [is_trichotomous α r] (s : set α) : is_chain r s :=
begin
  intros a _ b _ hab,
  obtain h | h | h := @trichotomous _ r _ a b,
  { exact or.inl h },
  { exact (hab h).elim },
  { exact or.inr h }
end

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

lemma is_chain.directed_on [is_refl α r] (H : is_chain r s) : directed_on (≺) s :=
λ x hx y hy,
match H.total hx hy with
| or.inl h := ⟨y, hy, h, refl _⟩
| or.inr h := ⟨x, hx, refl _, h⟩
end

lemma is_chain.directed {r} [is_refl β r] {f : α → β} {c : set α} (h : is_chain (f ⁻¹'o r) c) :
  directed r (λ x : {a : α // a ∈ c}, f x) :=
λ ⟨a, ha⟩ ⟨b, hb⟩, by_cases
  (λ hab : a = b, by simp only [hab, exists_prop, and_self, subtype.exists];
    exact ⟨b, hb, refl _⟩)
  (λ hab, (h ha hb hab).elim
    (λ h : r (f a) (f b), ⟨⟨b, hb⟩, h, refl _⟩)
    (λ h : r (f b) (f a), ⟨⟨a, ha⟩, refl _, h⟩))

lemma is_max_chain.is_chain (h : is_max_chain r s) : is_chain r s := h.1
lemma is_max_chain.not_super_chain (h : is_max_chain r s) : ¬super_chain r s t :=
λ ht, ht.2.ne $ h.2 ht.1 ht.2.1

open_locale classical

/-- Given a set `s`, if there exists a chain `t` strictly including `s`, then `succ_chain s`
is one of these chains. Otherwise it is `s`. -/
def succ_chain (r : α → α → Prop) (s : set α) : set α :=
if h : ∃ t, is_chain r s ∧ super_chain r s t then some h else s

lemma succ_spec (h : ∃ t, is_chain r s ∧ super_chain r s t) : super_chain r s (succ_chain r s) :=
let ⟨t, hc'⟩ := h in
have is_chain r s ∧ super_chain r s (some h),
  from @some_spec _ (λ t, is_chain r s ∧ super_chain r s t) _,
by simp [succ_chain, dif_pos, h, this.right]

lemma is_chain.succ (hs : is_chain r s) :  is_chain r (succ_chain r s) :=
if h : ∃ t, is_chain r s ∧ super_chain r s t then
  (succ_spec h).left
else
  by simp [succ_chain, dif_neg, h]; exact hs

lemma is_chain.super_chain_succ_chain (hs₁ : is_chain r s) (hs₂ : ¬ is_max_chain r s) :
  super_chain r s (succ_chain r s) :=
begin
  simp [is_max_chain, not_and_distrib, not_forall_not] at hs₂,
  obtain ⟨t, ht, hst⟩ := hs₂.neg_resolve_left hs₁,
  exact succ_spec ⟨t, hs₁, ht, ssubset_iff_subset_ne.2 hst⟩,
end

lemma succ_increasing {s : set α} : s ⊆ succ_chain r s :=
if h : ∃ t, is_chain r s ∧ super_chain r s t then
  have super_chain r s (succ_chain r s), from succ_spec h,
  this.right.left
else by simp [succ_chain, dif_neg, h, subset.refl]

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
  (h : ∀ {c₃}, chain_closure r c₃ → c₃ ⊆ c₂ → c₂ = c₃ ∨ succ_chain r c₃ ⊆ c₂) :
  c₁ ⊆ c₂ ∨ succ_chain r c₂ ⊆ c₁ :=
begin
  induction hc₁,
  case succ : c₃ hc₃ ih
  { cases ih with ih ih,
    { exact (h hc₃ ih).symm.imp_right (λ h, h ▸ subset.rfl) },
    { exact or.inr (subset.trans ih succ_increasing) } },
  case union : s hs ih
  { refine (or_iff_not_imp_right.2 $ λ hn, sUnion_subset $ λ a ha, _),
    exact (ih a ha).resolve_right (λ h, hn $ h.trans $ subset_sUnion_of_mem ha) }
end

private lemma chain_closure_succ_total (hc₁ : chain_closure r c₁) (hc₂ : chain_closure r c₂)
  (h : c₁ ⊆ c₂) :
  c₂ = c₁ ∨ succ_chain r c₁ ⊆ c₂ :=
begin
  induction hc₂ generalizing c₁ hc₁ h,
  case succ : c₂ hc₂ ih
  { have h₁ : c₁ ⊆ c₂ ∨ succ_chain r c₂ ⊆ c₁ :=
      (chain_closure_succ_total_aux hc₁ hc₂ $ λ c₁, ih),
    cases h₁ with h₁ h₁,
    { have h₂ := ih hc₁ h₁,
      cases h₂ with h₂ h₂,
      { exact (or.inr $ h₂ ▸ subset.refl _) },
      { exact (or.inr $ subset.trans h₂ succ_increasing) } },
    { exact (or.inl $ subset.antisymm h₁ h) } },
  case union : s hs ih
  { apply or.imp_left (λ h', subset.antisymm h' h),
    apply classical.by_contradiction,
    simp [not_or_distrib, sUnion_subset_iff, not_forall],
    intros c₃ hc₃ h₁ h₂,
    have h := chain_closure_succ_total_aux hc₁ (hs c₃ hc₃) (λ c₄, ih _ hc₃),
    cases h with h h,
    { have h' := ih c₃ hc₃ hc₁ h,
      cases h' with h' h',
      { exact h₁ h'.subset },
      { exact h₂ (h'.trans $ subset_sUnion_of_mem hc₃) } },
    { exact h₁ (succ_increasing.trans  h) } }
end

lemma chain_closure_total (hc₁ : chain_closure r c₁) (hc₂ : chain_closure r c₂) :
  c₁ ⊆ c₂ ∨ c₂ ⊆ c₁ :=
or.imp_right succ_increasing.trans $ chain_closure_succ_total_aux hc₁ hc₂ $ λ c₃ hc₃,
  chain_closure_succ_total hc₃ hc₂

lemma chain_closure.succ_fixpoint (hc₁ : chain_closure r c₁) (hc₂ : chain_closure r c₂)
  (h_eq : succ_chain r c₂ = c₂) :
  c₁ ⊆ c₂ :=
begin
  induction hc₁,
  case succ : s₁ hc₁ h
  { exact (chain_closure_succ_total hc₁ hc₂ h).elim (λ h, h ▸ h_eq.subset) id },
  case union : s hs ih
  { exact (sUnion_subset $ λ s₁ hc₁, ih s₁ hc₁) }
end

lemma chain_closure.succ_fixpoint_iff (hc : chain_closure r c) :
  succ_chain r c = c ↔ c = max_chain r :=
⟨λ h, (subset_sUnion_of_mem hc).antisymm (chain_closure_max_chain.succ_fixpoint hc h), λ h,
  subset.antisymm
    (calc succ_chain r c ⊆ ⋃₀ {c : set α | chain_closure r c} : subset_sUnion_of_mem hc.succ
      ... = c : h.symm)
    succ_increasing⟩

lemma chain_closure.is_chain (hc : chain_closure r c) : is_chain r c :=
begin
  induction hc,
  case succ : c hc h
  { exact h.succ },
  case union : s hs h
  { have h : ∀ c ∈ s, is_chain r c := h,
    exact λ c₁ ⟨t₁, ht₁, (hc₁ : c₁ ∈ t₁)⟩ c₂ ⟨t₂, ht₂, (hc₂ : c₂ ∈ t₂)⟩ hneq,
      have t₁ ⊆ t₂ ∨ t₂ ⊆ t₁, from chain_closure_total (hs _ ht₁) (hs _ ht₂),
      or.elim this
        (λ ht, h t₂ ht₂ (ht hc₁) hc₂ hneq)
        (λ ht, h t₁ ht₁ hc₁ (ht hc₂) hneq) }
end

/-- **Hausdorff's maximality principle**

There exists a maximal totally ordered subset of `α`.
Note that we do not require `α` to be partially ordered by `r`. -/
lemma max_chain_spec : is_max_chain r (max_chain r) :=
classical.by_contradiction $ λ h,
let ⟨h₁, H⟩ := chain_closure_max_chain.is_chain.super_chain_succ_chain h in
  H.ne (chain_closure_max_chain.succ_fixpoint_iff.mpr rfl).symm

end chain

/-! ### Zorn's lemma -/

section zorn
variables {r} {c : set α}

/-- **Zorn's lemma**

If every chain has an upper bound, then there exists a maximal element. -/
lemma exists_maximal_of_chains_bounded (h : ∀ c, is_chain r c → ∃ ub, ∀ a ∈ c, a ≺ ub)
  (trans : ∀ {a b c}, a ≺ b → b ≺ c → a ≺ c) :
  ∃ m, ∀ a, m ≺ a → a ≺ m :=
have ∃ ub, ∀ a ∈ max_chain r, a ≺ ub,
  from h _ $ max_chain_spec.left,
let ⟨ub, (hub : ∀ a ∈ max_chain r, a ≺ ub)⟩ := this in
⟨ub, λ a ha,
  have is_chain r (insert a $ max_chain r),
    from max_chain_spec.1.insert $ λ b hb _, or.inr $ trans (hub b hb) ha,
  hub a $ by { rw max_chain_spec.right this (subset_insert _ _), exact mem_insert _ _ }⟩

/-- A variant of Zorn's lemma. If every nonempty chain of a nonempty type has an upper bound, then
there is a maximal element.
-/
theorem exists_maximal_of_nonempty_chains_bounded [nonempty α]
  (h : ∀ c, is_chain r c → c.nonempty → ∃ ub, ∀ a ∈ c, a ≺ ub)
  (trans : ∀ {a b c}, a ≺ b → b ≺ c → a ≺ c) :
  ∃ m, ∀ a, m ≺ a → a ≺ m :=
exists_maximal_of_chains_bounded
  (λ c hc,
    (eq_empty_or_nonempty c).elim
      (λ h, ⟨classical.arbitrary α, λ x hx, (h ▸ hx : x ∈ (∅ : set α)).elim⟩)
      (h c hc))
  (λ a b c, trans)

section partial_order
variables [partial_order α]

lemma zorn_partial_order (h : ∀ c : set α, is_chain (≤) c → ∃ ub, ∀ a ∈ c, a ≤ ub) :
  ∃ m : α, ∀ a, m ≤ a → a = m :=
let ⟨m, hm⟩ := @exists_maximal_of_chains_bounded α (≤) h (λ a b c, le_trans) in
⟨m, λ a ha, le_antisymm (hm a ha) ha⟩

lemma zorn_nonempty_partial_order [nonempty α]
  (h : ∀ c : set α, is_chain (≤) c → c.nonempty → ∃ ub, ∀ a ∈ c, a ≤ ub) :
  ∃ (m : α), ∀ a, m ≤ a → a = m :=
let ⟨m, hm⟩ := @exists_maximal_of_nonempty_chains_bounded α (≤) _ h (λ a b c, le_trans) in
⟨m, λ a ha, le_antisymm (hm a ha) ha⟩

lemma zorn_partial_order₀ (s : set α)
  (ih : ∀ c ⊆ s, is_chain (≤) c → ∃ ub ∈ s, ∀ z ∈ c, z ≤ ub) :
  ∃ m ∈ s, ∀ z ∈ s, m ≤ z → z = m :=
let ⟨⟨m, hms⟩, h⟩ := @zorn_partial_order {m // m ∈ s} _
  (λ c hc,
    let ⟨ub, hubs, hub⟩ := ih (subtype.val '' c) (λ _ ⟨⟨x, hx⟩, _, h⟩, h ▸ hx)
      (by { rintro _ ⟨p, hpc, rfl⟩ _ ⟨q, hqc, rfl⟩ hpq;
        refine hc hpc hqc (λ t, hpq (subtype.ext_iff.1 t)) })
    in ⟨⟨ub, hubs⟩, λ ⟨y, hy⟩ hc, hub _ ⟨_, hc, rfl⟩⟩)
in ⟨m, hms, λ z hzs hmz, congr_arg subtype.val (h ⟨z, hzs⟩ hmz)⟩

lemma zorn_nonempty_partial_order₀ (s : set α)
  (ih : ∀ c ⊆ s, is_chain (≤) c → ∀ y ∈ c, ∃ ub ∈ s, ∀ z ∈ c, z ≤ ub) (x : α) (hxs : x ∈ s) :
  ∃ m ∈ s, x ≤ m ∧ ∀ z ∈ s, m ≤ z → z = m :=
let ⟨⟨m, hms, hxm⟩, h⟩ := @zorn_partial_order {m // m ∈ s ∧ x ≤ m} _
  (λ c hc, c.eq_empty_or_nonempty.elim
    (λ hce, hce.symm ▸ ⟨⟨x, hxs, le_rfl⟩, λ _, false.elim⟩)
    (λ ⟨m, hmc⟩,
      let ⟨ub, hubs, hub⟩ := ih (subtype.val '' c) (image_subset_iff.2 $ λ z hzc, z.2.1)
        (by rintro _ ⟨p, hpc, rfl⟩ _ ⟨q, hqc, rfl⟩ hpq;
          exact hc hpc hqc (ne_of_apply_ne _ hpq)) m.1 (mem_image_of_mem _ hmc) in
    ⟨⟨ub, hubs, le_trans m.2.2 $ hub m.1 $ mem_image_of_mem _ hmc⟩,
      λ a hac, hub a.1 ⟨a, hac, rfl⟩⟩)) in
⟨m, hms, hxm, λ z hzs hmz, congr_arg subtype.val $ h ⟨z, hzs, le_trans hxm hmz⟩ hmz⟩

end partial_order

lemma zorn_subset (S : set (set α)) (h : ∀ c ⊆ S, is_chain (⊆) c → ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub) :
  ∃ m ∈ S, ∀ a ∈ S, m ⊆ a → a = m :=
zorn_partial_order₀ S h

lemma zorn_subset_nonempty (S : set (set α))
  (H : ∀ c ⊆ S, is_chain (⊆) c → c.nonempty → ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub) (x) (hx : x ∈ S) :
  ∃ m ∈ S, x ⊆ m ∧ ∀ a ∈ S, m ⊆ a → a = m :=
zorn_nonempty_partial_order₀ _ (λ c cS hc y yc, H _ cS hc ⟨y, yc⟩) _ hx

lemma zorn_superset (S : set (set α))
  (h : ∀ c ⊆ S, is_chain (⊆) c → ∃ lb ∈ S, ∀ s ∈ c, lb ⊆ s) :
  ∃ m ∈ S, ∀ a ∈ S, a ⊆ m → a = m :=
@zorn_partial_order₀ (order_dual (set α)) _ S $ λ c cS hc, h c cS hc.symm

lemma zorn_superset_nonempty (S : set (set α))
  (H : ∀ c ⊆ S, is_chain (⊆) c → c.nonempty → ∃ lb ∈ S, ∀ s ∈ c, lb ⊆ s) (x) (hx : x ∈ S) :
  ∃ m ∈ S, m ⊆ x ∧ ∀ a ∈ S, a ⊆ m → a = m :=
@zorn_nonempty_partial_order₀ (order_dual (set α)) _ S (λ c cS hc y yc, H _ cS
  hc.symm ⟨y, yc⟩) _ hx

/-- Every chain is contained in a maximal chain. This generalizes Hausdorff's maximality principle.
-/
lemma is_chain.exists_max_chain (hc : is_chain r c) : ∃ M, @is_max_chain _ r M ∧ c ⊆ M :=
begin
  obtain ⟨M, ⟨_, hM₀⟩, hM₁, hM₂⟩ :=
    zorn_subset_nonempty {s | c ⊆ s ∧ is_chain r s} _ c ⟨subset.rfl, hc⟩,
  { exact ⟨M, ⟨hM₀, λ d hd hMd, (hM₂ _ ⟨hM₁.trans hMd, hd⟩ hMd).symm⟩, hM₁⟩ },
  rintros cs hcs₀ hcs₁ ⟨s, hs⟩,
  refine ⟨⋃₀ cs, ⟨λ _ ha, set.mem_sUnion_of_mem ((hcs₀ hs).left ha) hs, _⟩,
    λ _, set.subset_sUnion_of_mem⟩,
  rintros y ⟨sy, hsy, hysy⟩ z ⟨sz, hsz, hzsz⟩ hyz,
  obtain rfl | hsseq := eq_or_ne sy sz,
  { exact (hcs₀ hsy).right hysy hzsz hyz },
  cases hcs₁ hsy hsz hsseq with h h,
  { exact (hcs₀ hsz).right (h hysy) hzsz hyz },
  { exact (hcs₀ hsy).right hysy (h hzsz) hyz }
end

end zorn

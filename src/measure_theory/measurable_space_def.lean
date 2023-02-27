/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import data.set.countable
import logic.encodable.lattice
import order.disjointed

/-!
# Measurable spaces and measurable functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines measurable spaces and measurable functions.

A measurable space is a set equipped with a σ-algebra, a collection of
subsets closed under complementation and countable union. A function
between measurable spaces is measurable if the preimage of each
measurable subset is measurable.

σ-algebras on a fixed set `α` form a complete lattice. Here we order
σ-algebras by writing `m₁ ≤ m₂` if every set which is `m₁`-measurable is
also `m₂`-measurable (that is, `m₁` is a subset of `m₂`). In particular, any
collection of subsets of `α` generates a smallest σ-algebra which
contains all of them.

Do not add measurability lemmas (which could be tagged with
@[measurability]) to this file, since the measurability tactic is downstream
from here. Use `measure_theory.measurable_space` instead.

## References

* <https://en.wikipedia.org/wiki/Measurable_space>
* <https://en.wikipedia.org/wiki/Sigma-algebra>
* <https://en.wikipedia.org/wiki/Dynkin_system>

## Tags

measurable space, σ-algebra, measurable function
-/

open set encodable function equiv
open_locale classical


variables {α β γ δ δ' : Type*} {ι : Sort*} {s t u : set α}

/-- A measurable space is a space equipped with a σ-algebra. -/
structure measurable_space (α : Type*) :=
(measurable_set' : set α → Prop)
(measurable_set_empty : measurable_set' ∅)
(measurable_set_compl : ∀ s, measurable_set' s → measurable_set' sᶜ)
(measurable_set_Union : ∀ f : ℕ → set α, (∀ i, measurable_set' (f i)) → measurable_set' (⋃ i, f i))

attribute [class] measurable_space

instance [h : measurable_space α] : measurable_space αᵒᵈ := h

section

/-- `measurable_set s` means that `s` is measurable (in the ambient measure space on `α`) -/
def measurable_set [measurable_space α] : set α → Prop := ‹measurable_space α›.measurable_set'

localized "notation (name := measurable_set_of)
  `measurable_set[` m `]` := @measurable_set hole! m" in measure_theory

@[simp] lemma measurable_set.empty [measurable_space α] : measurable_set (∅ : set α) :=
‹measurable_space α›.measurable_set_empty

variable {m : measurable_space α}

include m

lemma measurable_set.compl : measurable_set s → measurable_set sᶜ :=
‹measurable_space α›.measurable_set_compl s

lemma measurable_set.of_compl (h : measurable_set sᶜ) : measurable_set s :=
compl_compl s ▸ h.compl

@[simp] lemma measurable_set.compl_iff : measurable_set sᶜ ↔ measurable_set s :=
⟨measurable_set.of_compl, measurable_set.compl⟩

@[simp] lemma measurable_set.univ : measurable_set (univ : set α) :=
by simpa using (@measurable_set.empty α _).compl

@[nontriviality] lemma subsingleton.measurable_set [subsingleton α] {s : set α} :
  measurable_set s :=
subsingleton.set_cases measurable_set.empty measurable_set.univ s

lemma measurable_set.congr {s t : set α} (hs : measurable_set s) (h : s = t) :
  measurable_set t :=
by rwa ← h

lemma measurable_set.bUnion_decode₂ [encodable β] ⦃f : β → set α⦄ (h : ∀ b, measurable_set (f b))
  (n : ℕ) : measurable_set (⋃ b ∈ decode₂ β n, f b) :=
encodable.Union_decode₂_cases measurable_set.empty h

lemma measurable_set.Union [countable ι] ⦃f : ι → set α⦄ (h : ∀ b, measurable_set (f b)) :
  measurable_set (⋃ b, f b) :=
begin
  casesI nonempty_encodable (plift ι),
  rw [←Union_plift_down, ←encodable.Union_decode₂],
  exact ‹measurable_space α›.measurable_set_Union _ (measurable_set.bUnion_decode₂ $ λ _, h _),
end

lemma measurable_set.bUnion {f : β → set α} {s : set β} (hs : s.countable)
  (h : ∀ b ∈ s, measurable_set (f b)) : measurable_set (⋃ b ∈ s, f b) :=
begin
  rw bUnion_eq_Union,
  haveI := hs.to_encodable,
  exact measurable_set.Union (by simpa using h)
end

lemma set.finite.measurable_set_bUnion {f : β → set α} {s : set β} (hs : s.finite)
  (h : ∀ b ∈ s, measurable_set (f b)) :
  measurable_set (⋃ b ∈ s, f b) :=
measurable_set.bUnion hs.countable h

lemma finset.measurable_set_bUnion {f : β → set α} (s : finset β)
  (h : ∀ b ∈ s, measurable_set (f b)) :
  measurable_set (⋃ b ∈ s, f b) :=
s.finite_to_set.measurable_set_bUnion h

lemma measurable_set.sUnion {s : set (set α)} (hs : s.countable) (h : ∀ t ∈ s, measurable_set t) :
  measurable_set (⋃₀ s) :=
by { rw sUnion_eq_bUnion, exact measurable_set.bUnion hs h }

lemma set.finite.measurable_set_sUnion {s : set (set α)} (hs : s.finite)
  (h : ∀ t ∈ s, measurable_set t) :
  measurable_set (⋃₀ s) :=
measurable_set.sUnion hs.countable h

lemma measurable_set.Inter [countable ι] {f : ι → set α} (h : ∀ b, measurable_set (f b)) :
  measurable_set (⋂ b, f b) :=
measurable_set.compl_iff.1 $
by { rw compl_Inter, exact measurable_set.Union (λ b, (h b).compl) }

lemma measurable_set.bInter {f : β → set α} {s : set β} (hs : s.countable)
  (h : ∀ b ∈ s, measurable_set (f b)) : measurable_set (⋂ b ∈ s, f b) :=
measurable_set.compl_iff.1 $
by { rw compl_Inter₂, exact measurable_set.bUnion hs (λ b hb, (h b hb).compl) }

lemma set.finite.measurable_set_bInter {f : β → set α} {s : set β} (hs : s.finite)
  (h : ∀ b ∈ s, measurable_set (f b)) : measurable_set (⋂ b ∈ s, f b) :=
measurable_set.bInter hs.countable h

lemma finset.measurable_set_bInter {f : β → set α} (s : finset β)
  (h : ∀ b ∈ s, measurable_set (f b)) : measurable_set (⋂ b ∈ s, f b) :=
s.finite_to_set.measurable_set_bInter h

lemma measurable_set.sInter {s : set (set α)} (hs : s.countable) (h : ∀ t ∈ s, measurable_set t) :
  measurable_set (⋂₀ s) :=
by { rw sInter_eq_bInter, exact measurable_set.bInter hs h }

lemma set.finite.measurable_set_sInter {s : set (set α)} (hs : s.finite)
  (h : ∀ t ∈ s, measurable_set t) : measurable_set (⋂₀ s) :=
measurable_set.sInter hs.countable h

@[simp] lemma measurable_set.union {s₁ s₂ : set α} (h₁ : measurable_set s₁)
  (h₂ : measurable_set s₂) :
  measurable_set (s₁ ∪ s₂) :=
by { rw union_eq_Union, exact measurable_set.Union (bool.forall_bool.2 ⟨h₂, h₁⟩) }

@[simp] lemma measurable_set.inter {s₁ s₂ : set α} (h₁ : measurable_set s₁)
  (h₂ : measurable_set s₂) :
  measurable_set (s₁ ∩ s₂) :=
by { rw inter_eq_compl_compl_union_compl, exact (h₁.compl.union h₂.compl).compl }

@[simp] lemma measurable_set.diff {s₁ s₂ : set α} (h₁ : measurable_set s₁)
  (h₂ : measurable_set s₂) :
  measurable_set (s₁ \ s₂) :=
h₁.inter h₂.compl

@[simp] lemma measurable_set.symm_diff {s₁ s₂ : set α}
  (h₁ : measurable_set s₁) (h₂ : measurable_set s₂) :
  measurable_set (s₁ ∆ s₂) :=
(h₁.diff h₂).union (h₂.diff h₁)

@[simp] lemma measurable_set.ite {t s₁ s₂ : set α} (ht : measurable_set t) (h₁ : measurable_set s₁)
  (h₂ : measurable_set s₂) :
  measurable_set (t.ite s₁ s₂) :=
(h₁.inter ht).union (h₂.diff ht)

lemma measurable_set.ite' {s t : set α} {p : Prop}
  (hs : p → measurable_set s) (ht : ¬ p → measurable_set t) :
  measurable_set (ite p s t) :=
by { split_ifs, exacts [hs h, ht h], }

@[simp] lemma measurable_set.cond {s₁ s₂ : set α} (h₁ : measurable_set s₁) (h₂ : measurable_set s₂)
  {i : bool} : measurable_set (cond i s₁ s₂) :=
by { cases i, exacts [h₂, h₁] }

@[simp] lemma measurable_set.disjointed {f : ℕ → set α} (h : ∀ i, measurable_set (f i)) (n) :
  measurable_set (disjointed f n) :=
disjointed_rec (λ t i ht, measurable_set.diff ht $ h _) (h n)

@[simp] lemma measurable_set.const (p : Prop) : measurable_set {a : α | p} :=
by { by_cases p; simp [h, measurable_set.empty]; apply measurable_set.univ }

/-- Every set has a measurable superset. Declare this as local instance as needed. -/
lemma nonempty_measurable_superset (s : set α) : nonempty { t // s ⊆ t ∧ measurable_set t} :=
⟨⟨univ, subset_univ s, measurable_set.univ⟩⟩

end

open_locale measure_theory

@[ext] lemma measurable_space.ext : ∀ {m₁ m₂ : measurable_space α},
  (∀ s : set α, measurable_set[m₁] s ↔ measurable_set[m₂] s) → m₁ = m₂
| ⟨s₁, _, _, _⟩ ⟨s₂, _, _, _⟩ h :=
  have s₁ = s₂, from funext $ assume x, propext $ h x,
  by subst this

@[ext] lemma measurable_space.ext_iff {m₁ m₂ : measurable_space α} :
  m₁ = m₂ ↔ (∀ s : set α, measurable_set[m₁] s ↔ measurable_set[m₂] s) :=
⟨by { unfreezingI {rintro rfl}, intro s, refl }, measurable_space.ext⟩

/-- A typeclass mixin for `measurable_space`s such that each singleton is measurable. -/
class measurable_singleton_class (α : Type*) [measurable_space α] : Prop :=
(measurable_set_singleton : ∀ x, measurable_set ({x} : set α))

export measurable_singleton_class (measurable_set_singleton)

attribute [simp] measurable_set_singleton

section measurable_singleton_class

variables [measurable_space α] [measurable_singleton_class α]

lemma measurable_set_eq {a : α} : measurable_set {x | x = a} :=
measurable_set_singleton a

lemma measurable_set.insert {s : set α} (hs : measurable_set s) (a : α) :
  measurable_set (insert a s) :=
(measurable_set_singleton a).union hs

@[simp] lemma measurable_set_insert {a : α} {s : set α} :
  measurable_set (insert a s) ↔ measurable_set s :=
⟨λ h, if ha : a ∈ s then by rwa ← insert_eq_of_mem ha
  else insert_diff_self_of_not_mem ha ▸ h.diff (measurable_set_singleton _),
  λ h, h.insert a⟩

lemma set.subsingleton.measurable_set {s : set α} (hs : s.subsingleton) : measurable_set s :=
hs.induction_on measurable_set.empty measurable_set_singleton

lemma set.finite.measurable_set {s : set α} (hs : s.finite) : measurable_set s :=
finite.induction_on hs measurable_set.empty $ λ a s ha hsf hsm, hsm.insert _

protected lemma finset.measurable_set (s : finset α) : measurable_set (↑s : set α) :=
s.finite_to_set.measurable_set

lemma set.countable.measurable_set {s : set α} (hs : s.countable) : measurable_set s :=
begin
  rw [← bUnion_of_singleton s],
  exact measurable_set.bUnion hs (λ b hb, measurable_set_singleton b)
end

end measurable_singleton_class

namespace measurable_space

section complete_lattice

instance : has_le (measurable_space α) :=
{ le          := λ m₁ m₂, ∀ s, measurable_set[m₁] s → measurable_set[m₂] s }

lemma le_def {α} {a b : measurable_space α} :
  a ≤ b ↔ a.measurable_set' ≤ b.measurable_set' := iff.rfl

instance : partial_order (measurable_space α) :=
{ lt := λ m₁ m₂, m₁ ≤ m₂ ∧ ¬m₂ ≤ m₁,
  .. measurable_space.has_le,
  .. partial_order.lift (@measurable_set α) (λ m₁ m₂ h, ext $ λ s, h ▸ iff.rfl) }

/-- The smallest σ-algebra containing a collection `s` of basic sets -/
inductive generate_measurable (s : set (set α)) : set α → Prop
| basic : ∀ u ∈ s, generate_measurable u
| empty : generate_measurable ∅
| compl : ∀ s, generate_measurable s → generate_measurable sᶜ
| union : ∀ f : ℕ → set α, (∀ n, generate_measurable (f n)) → generate_measurable (⋃ i, f i)

/-- Construct the smallest measure space containing a collection of basic sets -/
def generate_from (s : set (set α)) : measurable_space α :=
{ measurable_set'      := generate_measurable s,
  measurable_set_empty := generate_measurable.empty,
  measurable_set_compl := generate_measurable.compl,
  measurable_set_Union := generate_measurable.union }

lemma measurable_set_generate_from {s : set (set α)} {t : set α} (ht : t ∈ s) :
  @measurable_set _ (generate_from s) t :=
generate_measurable.basic t ht

@[elab_as_eliminator]
lemma generate_from_induction (p : set α → Prop) (C : set (set α))
  (hC : ∀ t ∈ C, p t) (h_empty : p ∅) (h_compl : ∀ t, p t → p tᶜ)
  (h_Union : ∀ f : ℕ → set α, (∀ n, p (f n)) → p (⋃ i, f i))
  {s : set α} (hs : measurable_set[generate_from C] s) :
  p s :=
by { induction hs, exacts [hC _ hs_H, h_empty, h_compl _ hs_ih, h_Union hs_f hs_ih], }

lemma generate_from_le {s : set (set α)} {m : measurable_space α}
  (h : ∀ t ∈ s, measurable_set[m] t) : generate_from s ≤ m :=
assume t (ht : generate_measurable s t), ht.rec_on h
  (measurable_set_empty m)
  (assume s _ hs, measurable_set_compl m s hs)
  (assume f _ hf, measurable_set_Union m f hf)

lemma generate_from_le_iff {s : set (set α)} (m : measurable_space α) :
  generate_from s ≤ m ↔ s ⊆ {t | measurable_set[m] t} :=
iff.intro
  (assume h u hu, h _ $ measurable_set_generate_from hu)
  (assume h, generate_from_le h)

@[simp] lemma generate_from_measurable_set [measurable_space α] :
  generate_from {s : set α | measurable_set s} = ‹_› :=
le_antisymm (generate_from_le $ λ _, id) $ λ s, measurable_set_generate_from

/-- If `g` is a collection of subsets of `α` such that the `σ`-algebra generated from `g` contains
the same sets as `g`, then `g` was already a `σ`-algebra. -/
protected def mk_of_closure (g : set (set α)) (hg : {t | measurable_set[generate_from g] t} = g) :
  measurable_space α :=
{ measurable_set'      := λ s, s ∈ g,
  measurable_set_empty := hg ▸ measurable_set_empty _,
  measurable_set_compl := hg ▸ measurable_set_compl _,
  measurable_set_Union := hg ▸ measurable_set_Union _ }

lemma mk_of_closure_sets {s : set (set α)}
  {hs : {t | measurable_set[generate_from s] t} = s} :
  measurable_space.mk_of_closure s hs = generate_from s :=
measurable_space.ext $ assume t, show t ∈ s ↔ _, by { conv_lhs { rw [← hs] }, refl }

/-- We get a Galois insertion between `σ`-algebras on `α` and `set (set α)` by using `generate_from`
  on one side and the collection of measurable sets on the other side. -/
def gi_generate_from : galois_insertion (@generate_from α) (λ m, {t | @measurable_set α m t}) :=
{ gc        := assume s, generate_from_le_iff,
  le_l_u    := assume m s, measurable_set_generate_from,
  choice    :=
    λ g hg, measurable_space.mk_of_closure g $ le_antisymm hg $ (generate_from_le_iff _).1 le_rfl,
  choice_eq := assume g hg, mk_of_closure_sets }

instance : complete_lattice (measurable_space α) :=
gi_generate_from.lift_complete_lattice

instance : inhabited (measurable_space α) := ⟨⊤⟩

@[mono] lemma generate_from_mono {s t : set (set α)} (h : s ⊆ t) :
  generate_from s ≤ generate_from t :=
gi_generate_from.gc.monotone_l h

lemma generate_from_sup_generate_from {s t : set (set α)} :
  generate_from s ⊔ generate_from t = generate_from (s ∪ t) :=
(@gi_generate_from α).gc.l_sup.symm

@[simp] lemma generate_from_insert_univ (S : set (set α)) :
  generate_from (insert set.univ S) = generate_from S :=
begin
  refine le_antisymm _ (generate_from_mono (set.subset_insert _ _)),
  rw generate_from_le_iff,
  intros t ht,
  cases ht,
  { rw ht,
    exact measurable_set.univ, },
  { exact measurable_set_generate_from ht, },
end

@[simp] lemma generate_from_insert_empty (S : set (set α)) :
  generate_from (insert ∅ S) = generate_from S :=
begin
  refine le_antisymm _ (generate_from_mono (set.subset_insert _ _)),
  rw generate_from_le_iff,
  intros t ht,
  cases ht,
  { rw ht,
    exact @measurable_set.empty _ (generate_from S), },
  { exact measurable_set_generate_from ht, },
end

@[simp] lemma generate_from_singleton_empty : generate_from {∅} = (⊥ : measurable_space α) :=
by { rw [eq_bot_iff, generate_from_le_iff], simp, }

@[simp] lemma generate_from_singleton_univ : generate_from {set.univ} = (⊥ : measurable_space α) :=
by { rw [eq_bot_iff, generate_from_le_iff], simp, }

lemma measurable_set_bot_iff {s : set α} : @measurable_set α ⊥ s ↔ (s = ∅ ∨ s = univ) :=
let b : measurable_space α :=
{ measurable_set'      := λ s, s = ∅ ∨ s = univ,
  measurable_set_empty := or.inl rfl,
  measurable_set_compl := by simp [or_imp_distrib] {contextual := tt},
  measurable_set_Union := assume f hf, classical.by_cases
    (assume h : ∃i, f i = univ,
      let ⟨i, hi⟩ := h in
      or.inr $ eq_univ_of_univ_subset $ hi ▸ le_supr f i)
    (assume h : ¬ ∃i, f i = univ,
      or.inl $ eq_empty_of_subset_empty $ Union_subset $ assume i,
        (hf i).elim (by simp {contextual := tt}) (assume hi, false.elim $ h ⟨i, hi⟩)) } in
have b = ⊥, from bot_unique $ assume s hs,
  hs.elim (λ s, s.symm ▸ @measurable_set_empty _ ⊥) (λ s, s.symm ▸ @measurable_set.univ _ ⊥),
this ▸ iff.rfl

@[simp] theorem measurable_set_top {s : set α} : @measurable_set _ ⊤ s := trivial

@[simp] theorem measurable_set_inf {m₁ m₂ : measurable_space α} {s : set α} :
  @measurable_set _ (m₁ ⊓ m₂) s ↔ @measurable_set _ m₁ s ∧ @measurable_set _ m₂ s :=
iff.rfl

@[simp] theorem measurable_set_Inf {ms : set (measurable_space α)} {s : set α} :
  @measurable_set _ (Inf ms) s ↔ ∀ m ∈ ms, @measurable_set _ m s :=
show s ∈ (⋂₀ _) ↔ _, by simp

@[simp] theorem measurable_set_infi {ι} {m : ι → measurable_space α} {s : set α} :
  @measurable_set _ (infi m) s ↔ ∀ i, @measurable_set _ (m i) s :=
by rw [infi, measurable_set_Inf, forall_range_iff]

theorem measurable_set_sup {m₁ m₂ : measurable_space α} {s : set α} :
  measurable_set[m₁ ⊔ m₂] s ↔ generate_measurable (measurable_set[m₁] ∪ measurable_set[m₂]) s :=
iff.refl _

theorem measurable_set_Sup {ms : set (measurable_space α)} {s : set α} :
  measurable_set[Sup ms] s ↔
    generate_measurable {s : set α | ∃ m ∈ ms, measurable_set[m] s} s :=
begin
  change @measurable_set' _ (generate_from $ ⋃₀ _) _ ↔ _,
  simp [generate_from, ← set_of_exists]
end

theorem measurable_set_supr {ι} {m : ι → measurable_space α} {s : set α} :
  @measurable_set _ (supr m) s ↔
    generate_measurable {s : set α | ∃ i, measurable_set[m i] s} s :=
by simp only [supr, measurable_set_Sup, exists_range_iff]

lemma measurable_space_supr_eq (m : ι → measurable_space α) :
  (⨆ n, m n) = generate_from {s | ∃ n, measurable_set[m n] s} :=
by { ext s, rw measurable_set_supr, refl, }

lemma generate_from_Union_measurable_set (m : ι → measurable_space α) :
  generate_from (⋃ n, {t | measurable_set[m n] t}) = ⨆ n, m n :=
(@gi_generate_from α).l_supr_u m

end complete_lattice

end measurable_space

section measurable_functions
open measurable_space

/-- A function `f` between measurable spaces is measurable if the preimage of every
  measurable set is measurable. -/
def measurable [measurable_space α] [measurable_space β] (f : α → β) : Prop :=
∀ ⦃t : set β⦄, measurable_set t → measurable_set (f ⁻¹' t)

localized "notation (name := measurable_of)
  `measurable[` m `]` := @measurable hole! hole! m hole!" in measure_theory

lemma measurable_id {ma : measurable_space α} : measurable (@id α) := λ t, id

lemma measurable_id' {ma : measurable_space α} : measurable (λ a : α, a) := measurable_id

lemma measurable.comp {mα : measurable_space α} {mβ : measurable_space β}
  {mγ : measurable_space γ} {g : β → γ} {f : α → β} (hg : measurable g) (hf : measurable f) :
  measurable (g ∘ f) :=
λ t ht, hf (hg ht)

@[simp] lemma measurable_const {ma : measurable_space α} {mb : measurable_space β} {a : α} :
  measurable (λ b : β, a) :=
assume s hs, measurable_set.const (a ∈ s)

lemma measurable.le {α} {m m0 : measurable_space α} {mb : measurable_space β} (hm : m ≤ m0)
  {f : α → β}
  (hf : measurable[m] f) : measurable[m0] f :=
λ s hs, hm _ (hf hs)

lemma measurable_space.top.measurable {α β : Type*} [measurable_space β] (f : α → β) :
  @measurable α β ⊤ _ f :=
λ s hs, measurable_space.measurable_set_top

end measurable_functions

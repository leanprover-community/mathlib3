/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import data.set.disjointed
import data.set.countable
import data.indicator_function
import data.equiv.encodable.lattice
import data.tprod
import order.filter.lift

/-!
# Measurable spaces and measurable functions

This file defines measurable spaces and the functions and isomorphisms
between them.

A measurable space is a set equipped with a σ-algebra, a collection of
subsets closed under complementation and countable union. A function
between measurable spaces is measurable if the preimage of each
measurable subset is measurable.

σ-algebras on a fixed set `α` form a complete lattice. Here we order
σ-algebras by writing `m₁ ≤ m₂` if every set which is `m₁`-measurable is
also `m₂`-measurable (that is, `m₁` is a subset of `m₂`). In particular, any
collection of subsets of `α` generates a smallest σ-algebra which
contains all of them. A function `f : α → β` induces a Galois connection
between the lattices of σ-algebras on `α` and `β`.

A measurable equivalence between measurable spaces is an equivalence
which respects the σ-algebras, that is, for which both directions of
the equivalence are measurable functions.

We say that a filter `f` is measurably generated if every set `s ∈ f` includes a measurable
set `t ∈ f`. This property is useful, e.g., to extract a measurable witness of `filter.eventually`.

## Notation

* We write `α ≃ᵐ β` for measurable equivalences between the measurable spaces `α` and `β`.
  This should not be confused with `≃ₘ` which is used for diffeomorphisms between manifolds.

## Implementation notes

Measurability of a function `f : α → β` between measurable spaces is
defined in terms of the Galois connection induced by f.

## References

* <https://en.wikipedia.org/wiki/Measurable_space>
* <https://en.wikipedia.org/wiki/Sigma-algebra>
* <https://en.wikipedia.org/wiki/Dynkin_system>

## Tags

measurable space, σ-algebra, measurable function, measurable equivalence, dynkin system,
π-λ theorem, π-system
-/

open set encodable function equiv
open_locale classical filter


variables {α β γ δ δ' : Type*} {ι : Sort*} {s t u : set α}

/-- A measurable space is a space equipped with a σ-algebra. -/
structure measurable_space (α : Type*) :=
(measurable_set' : set α → Prop)
(measurable_set_empty : measurable_set' ∅)
(measurable_set_compl : ∀ s, measurable_set' s → measurable_set' sᶜ)
(measurable_set_Union : ∀ f : ℕ → set α, (∀ i, measurable_set' (f i)) → measurable_set' (⋃ i, f i))

attribute [class] measurable_space

instance [h : measurable_space α] : measurable_space (order_dual α) := h

section
variable [measurable_space α]

/-- `measurable_set s` means that `s` is measurable (in the ambient measure space on `α`) -/
def measurable_set : set α → Prop := ‹measurable_space α›.measurable_set'

@[simp] lemma measurable_set.empty : measurable_set (∅ : set α) :=
‹measurable_space α›.measurable_set_empty

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

lemma measurable_set.bUnion_decode2 [encodable β] ⦃f : β → set α⦄ (h : ∀ b, measurable_set (f b))
  (n : ℕ) : measurable_set (⋃ b ∈ decode2 β n, f b) :=
encodable.Union_decode2_cases measurable_set.empty h

lemma measurable_set.Union [encodable β] ⦃f : β → set α⦄ (h : ∀ b, measurable_set (f b)) :
  measurable_set (⋃ b, f b) :=
begin
  rw ← encodable.Union_decode2,
  exact ‹measurable_space α›.measurable_set_Union _ (measurable_set.bUnion_decode2 h)
end

lemma measurable_set.bUnion {f : β → set α} {s : set β} (hs : countable s)
  (h : ∀ b ∈ s, measurable_set (f b)) : measurable_set (⋃ b ∈ s, f b) :=
begin
  rw bUnion_eq_Union,
  haveI := hs.to_encodable,
  exact measurable_set.Union (by simpa using h)
end

lemma set.finite.measurable_set_bUnion {f : β → set α} {s : set β} (hs : finite s)
  (h : ∀ b ∈ s, measurable_set (f b)) :
  measurable_set (⋃ b ∈ s, f b) :=
measurable_set.bUnion hs.countable h

lemma finset.measurable_set_bUnion {f : β → set α} (s : finset β)
  (h : ∀ b ∈ s, measurable_set (f b)) :
  measurable_set (⋃ b ∈ s, f b) :=
s.finite_to_set.measurable_set_bUnion h

lemma measurable_set.sUnion {s : set (set α)} (hs : countable s) (h : ∀ t ∈ s, measurable_set t) :
  measurable_set (⋃₀ s) :=
by { rw sUnion_eq_bUnion, exact measurable_set.bUnion hs h }

lemma set.finite.measurable_set_sUnion {s : set (set α)} (hs : finite s)
  (h : ∀ t ∈ s, measurable_set t) :
  measurable_set (⋃₀ s) :=
measurable_set.sUnion hs.countable h

lemma measurable_set.Union_Prop {p : Prop} {f : p → set α} (hf : ∀ b, measurable_set (f b)) :
  measurable_set (⋃ b, f b) :=
by { by_cases p; simp [h, hf, measurable_set.empty] }

lemma measurable_set.Inter [encodable β] {f : β → set α} (h : ∀ b, measurable_set (f b)) :
  measurable_set (⋂ b, f b) :=
measurable_set.compl_iff.1 $
by { rw compl_Inter, exact measurable_set.Union (λ b, (h b).compl) }

section fintype

local attribute [instance] fintype.encodable

lemma measurable_set.Union_fintype [fintype β] {f : β → set α} (h : ∀ b, measurable_set (f b)) :
  measurable_set (⋃ b, f b) :=
measurable_set.Union h

lemma measurable_set.Inter_fintype [fintype β] {f : β → set α} (h : ∀ b, measurable_set (f b)) :
  measurable_set (⋂ b, f b) :=
measurable_set.Inter h

end fintype

lemma measurable_set.bInter {f : β → set α} {s : set β} (hs : countable s)
  (h : ∀ b ∈ s, measurable_set (f b)) : measurable_set (⋂ b ∈ s, f b) :=
measurable_set.compl_iff.1 $
by { rw compl_bInter, exact measurable_set.bUnion hs (λ b hb, (h b hb).compl) }

lemma set.finite.measurable_set_bInter {f : β → set α} {s : set β} (hs : finite s)
  (h : ∀ b ∈ s, measurable_set (f b)) : measurable_set (⋂ b ∈ s, f b) :=
measurable_set.bInter hs.countable h

lemma finset.measurable_set_bInter {f : β → set α} (s : finset β)
  (h : ∀ b ∈ s, measurable_set (f b)) : measurable_set (⋂ b ∈ s, f b) :=
s.finite_to_set.measurable_set_bInter h

lemma measurable_set.sInter {s : set (set α)} (hs : countable s) (h : ∀ t ∈ s, measurable_set t) :
  measurable_set (⋂₀ s) :=
by { rw sInter_eq_bInter, exact measurable_set.bInter hs h }

lemma set.finite.measurable_set_sInter {s : set (set α)} (hs : finite s)
  (h : ∀ t ∈ s, measurable_set t) : measurable_set (⋂₀ s) :=
measurable_set.sInter hs.countable h

lemma measurable_set.Inter_Prop {p : Prop} {f : p → set α} (hf : ∀ b, measurable_set (f b)) :
  measurable_set (⋂ b, f b) :=
by { by_cases p; simp [h, hf, measurable_set.univ] }

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

@[simp] lemma measurable_set.ite {t s₁ s₂ : set α} (ht : measurable_set t) (h₁ : measurable_set s₁)
  (h₂ : measurable_set s₂) :
  measurable_set (t.ite s₁ s₂) :=
(h₁.inter ht).union (h₂.diff ht)

@[simp] lemma measurable_set.disjointed {f : ℕ → set α} (h : ∀ i, measurable_set (f i)) (n) :
  measurable_set (disjointed f n) :=
disjointed_induct (h n) (assume t i ht, measurable_set.diff ht $ h _)

@[simp] lemma measurable_set.const (p : Prop) : measurable_set {a : α | p} :=
by { by_cases p; simp [h, measurable_set.empty]; apply measurable_set.univ }

/-- Every set has a measurable superset. Declare this as local instance as needed. -/
lemma nonempty_measurable_superset (s : set α) : nonempty { t // s ⊆ t ∧ measurable_set t} :=
⟨⟨univ, subset_univ s, measurable_set.univ⟩⟩

end

@[ext] lemma measurable_space.ext : ∀ {m₁ m₂ : measurable_space α},
  (∀ s : set α, m₁.measurable_set' s ↔ m₂.measurable_set' s) → m₁ = m₂
| ⟨s₁, _, _, _⟩ ⟨s₂, _, _, _⟩ h :=
  have s₁ = s₂, from funext $ assume x, propext $ h x,
  by subst this

@[ext] lemma measurable_space.ext_iff {m₁ m₂ : measurable_space α} :
  m₁ = m₂ ↔ (∀ s : set α, m₁.measurable_set' s ↔ m₂.measurable_set' s) :=
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

lemma set.finite.measurable_set {s : set α} (hs : finite s) : measurable_set s :=
finite.induction_on hs measurable_set.empty $ λ a s ha hsf hsm, hsm.insert _

protected lemma finset.measurable_set (s : finset α) : measurable_set (↑s : set α) :=
s.finite_to_set.measurable_set

end measurable_singleton_class

namespace measurable_space

section complete_lattice

instance : partial_order (measurable_space α) :=
{ le          := λ m₁ m₂, m₁.measurable_set' ≤ m₂.measurable_set',
  le_refl     := assume a b, le_refl _,
  le_trans    := assume a b c, le_trans,
  le_antisymm := assume a b h₁ h₂, measurable_space.ext $ assume s, ⟨h₁ s, h₂ s⟩ }

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
  (generate_from s).measurable_set' t :=
generate_measurable.basic t ht

lemma generate_from_le {s : set (set α)} {m : measurable_space α}
  (h : ∀ t ∈ s, m.measurable_set' t) : generate_from s ≤ m :=
assume t (ht : generate_measurable s t), ht.rec_on h
  (measurable_set_empty m)
  (assume s _ hs, measurable_set_compl m s hs)
  (assume f _ hf, measurable_set_Union m f hf)

lemma generate_from_le_iff {s : set (set α)} (m : measurable_space α) :
  generate_from s ≤ m ↔ s ⊆ {t | m.measurable_set' t} :=
iff.intro
  (assume h u hu, h _ $ measurable_set_generate_from hu)
  (assume h, generate_from_le h)

@[simp] lemma generate_from_measurable_set [measurable_space α] :
  generate_from {s : set α | measurable_set s} = ‹_› :=
le_antisymm (generate_from_le $ λ _, id) $ λ s, measurable_set_generate_from

/-- If `g` is a collection of subsets of `α` such that the `σ`-algebra generated from `g` contains
the same sets as `g`, then `g` was already a `σ`-algebra. -/
protected def mk_of_closure (g : set (set α)) (hg : {t | (generate_from g).measurable_set' t} = g) :
  measurable_space α :=
{ measurable_set'      := λ s, s ∈ g,
  measurable_set_empty := hg ▸ measurable_set_empty _,
  measurable_set_compl := hg ▸ measurable_set_compl _,
  measurable_set_Union := hg ▸ measurable_set_Union _ }

lemma mk_of_closure_sets {s : set (set α)}
  {hs : {t | (generate_from s).measurable_set' t} = s} :
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
show s ∈ (⋂ m ∈ ms, {t | @measurable_set _ m t }) ↔ _, by simp

@[simp] theorem measurable_set_infi {ι} {m : ι → measurable_space α} {s : set α} :
  @measurable_set _ (infi m) s ↔ ∀ i, @measurable_set _ (m i) s :=
show s ∈ (λ m, {s | @measurable_set _ m s }) (infi m) ↔ _,
by { rw (@gi_generate_from α).gc.u_infi, simp }

theorem measurable_set_sup {m₁ m₂ : measurable_space α} {s : set α} :
  @measurable_set _ (m₁ ⊔ m₂) s ↔ generate_measurable (m₁.measurable_set' ∪ m₂.measurable_set') s :=
iff.refl _

theorem measurable_set_Sup {ms : set (measurable_space α)} {s : set α} :
  @measurable_set _ (Sup ms) s ↔
    generate_measurable {s : set α | ∃ m ∈ ms, @measurable_set _ m s} s :=
begin
  change @measurable_set' _ (generate_from $ ⋃ m ∈ ms, _) _ ↔ _,
  simp [generate_from, ← set_of_exists]
end

theorem measurable_set_supr {ι} {m : ι → measurable_space α} {s : set α} :
  @measurable_set _ (supr m) s ↔
    generate_measurable {s : set α | ∃ i, @measurable_set _ (m i) s} s :=
begin
  convert @measurable_set_Sup _ (range m) s,
  simp,
end

end complete_lattice

section functors
variables {m m₁ m₂ : measurable_space α} {m' : measurable_space β} {f : α → β} {g : β → α}

/-- The forward image of a measure space under a function. `map f m` contains the sets `s : set β`
  whose preimage under `f` is measurable. -/
protected def map (f : α → β) (m : measurable_space α) : measurable_space β :=
{ measurable_set'      := λ s, m.measurable_set' $ f ⁻¹' s,
  measurable_set_empty := m.measurable_set_empty,
  measurable_set_compl := assume s hs, m.measurable_set_compl _ hs,
  measurable_set_Union := assume f hf, by { rw preimage_Union, exact m.measurable_set_Union _ hf }}

@[simp] lemma map_id : m.map id = m :=
measurable_space.ext $ assume s, iff.rfl

@[simp] lemma map_comp {f : α → β} {g : β → γ} : (m.map f).map g = m.map (g ∘ f) :=
measurable_space.ext $ assume s, iff.rfl

/-- The reverse image of a measure space under a function. `comap f m` contains the sets `s : set α`
  such that `s` is the `f`-preimage of a measurable set in `β`. -/
protected def comap (f : α → β) (m : measurable_space β) : measurable_space α :=
{ measurable_set'      := λ s, ∃s', m.measurable_set' s' ∧ f ⁻¹' s' = s,
  measurable_set_empty := ⟨∅, m.measurable_set_empty, rfl⟩,
  measurable_set_compl := assume s ⟨s', h₁, h₂⟩, ⟨s'ᶜ, m.measurable_set_compl _ h₁, h₂ ▸ rfl⟩,
  measurable_set_Union := assume s hs,
    let ⟨s', hs'⟩ := classical.axiom_of_choice hs in
    ⟨⋃ i, s' i, m.measurable_set_Union _ (λ i, (hs' i).left), by simp [hs'] ⟩ }

@[simp] lemma comap_id : m.comap id = m :=
measurable_space.ext $ assume s, ⟨assume ⟨s', hs', h⟩, h ▸ hs', assume h, ⟨s, h, rfl⟩⟩

@[simp] lemma comap_comp {f : β → α} {g : γ → β} : (m.comap f).comap g = m.comap (f ∘ g) :=
measurable_space.ext $ assume s,
  ⟨assume ⟨t, ⟨u, h, hu⟩, ht⟩, ⟨u, h, ht ▸ hu ▸ rfl⟩, assume ⟨t, h, ht⟩, ⟨f ⁻¹' t, ⟨_, h, rfl⟩, ht⟩⟩

lemma comap_le_iff_le_map {f : α → β} : m'.comap f ≤ m ↔ m' ≤ m.map f :=
⟨assume h s hs, h _ ⟨_, hs, rfl⟩, assume h s ⟨t, ht, heq⟩, heq ▸ h _ ht⟩

lemma gc_comap_map (f : α → β) :
  galois_connection (measurable_space.comap f) (measurable_space.map f) :=
assume f g, comap_le_iff_le_map

lemma map_mono (h : m₁ ≤ m₂) : m₁.map f ≤ m₂.map f := (gc_comap_map f).monotone_u h
lemma monotone_map : monotone (measurable_space.map f) := assume a b h, map_mono h
lemma comap_mono (h : m₁ ≤ m₂) : m₁.comap g ≤ m₂.comap g := (gc_comap_map g).monotone_l h
lemma monotone_comap : monotone (measurable_space.comap g) := assume a b h, comap_mono h

@[simp] lemma comap_bot : (⊥ : measurable_space α).comap g = ⊥ := (gc_comap_map g).l_bot
@[simp] lemma comap_sup : (m₁ ⊔ m₂).comap g = m₁.comap g ⊔ m₂.comap g := (gc_comap_map g).l_sup
@[simp] lemma comap_supr {m : ι → measurable_space α} : (⨆i, m i).comap g = (⨆i, (m i).comap g) :=
(gc_comap_map g).l_supr

@[simp] lemma map_top : (⊤ : measurable_space α).map f = ⊤ := (gc_comap_map f).u_top
@[simp] lemma map_inf : (m₁ ⊓ m₂).map f = m₁.map f ⊓ m₂.map f := (gc_comap_map f).u_inf
@[simp] lemma map_infi {m : ι → measurable_space α} : (⨅i, m i).map f = (⨅i, (m i).map f) :=
(gc_comap_map f).u_infi

lemma comap_map_le : (m.map f).comap f ≤ m := (gc_comap_map f).l_u_le _
lemma le_map_comap : m ≤ (m.comap g).map g := (gc_comap_map g).le_u_l _

end functors

lemma generate_from_le_generate_from {s t : set (set α)} (h : s ⊆ t) :
  generate_from s ≤ generate_from t :=
gi_generate_from.gc.monotone_l h

lemma generate_from_sup_generate_from {s t : set (set α)} :
  generate_from s ⊔ generate_from t = generate_from (s ∪ t) :=
(@gi_generate_from α).gc.l_sup.symm

lemma comap_generate_from {f : α → β} {s : set (set β)} :
  (generate_from s).comap f = generate_from (preimage f '' s) :=
le_antisymm
  (comap_le_iff_le_map.2 $ generate_from_le $ assume t hts,
    generate_measurable.basic _ $ mem_image_of_mem _ $ hts)
  (generate_from_le $ assume t ⟨u, hu, eq⟩, eq ▸ ⟨u, generate_measurable.basic _ hu, rfl⟩)

end measurable_space

section measurable_functions
open measurable_space

/-- A function `f` between measurable spaces is measurable if the preimage of every
  measurable set is measurable. -/
def measurable [measurable_space α] [measurable_space β] (f : α → β) : Prop :=
∀ ⦃t : set β⦄, measurable_set t → measurable_set (f ⁻¹' t)

lemma measurable_iff_le_map {m₁ : measurable_space α} {m₂ : measurable_space β} {f : α → β} :
  measurable f ↔ m₂ ≤ m₁.map f :=
iff.rfl

alias measurable_iff_le_map ↔ measurable.le_map measurable.of_le_map

lemma measurable_iff_comap_le {m₁ : measurable_space α} {m₂ : measurable_space β} {f : α → β} :
  measurable f ↔ m₂.comap f ≤ m₁ :=
comap_le_iff_le_map.symm

alias measurable_iff_comap_le ↔ measurable.comap_le measurable.of_comap_le

lemma measurable.mono {ma ma' : measurable_space α} {mb mb' : measurable_space β} {f : α → β}
  (hf : @measurable α β ma mb f) (ha : ma ≤ ma') (hb : mb' ≤ mb) :
  @measurable α β ma' mb' f :=
λ t ht, ha _ $ hf $ hb _ ht

lemma measurable_from_top [measurable_space β] {f : α → β} : @measurable _ _ ⊤ _ f :=
λ s hs, trivial

lemma measurable_generate_from [measurable_space α] {s : set (set β)} {f : α → β}
  (h : ∀ t ∈ s, measurable_set (f ⁻¹' t)) : @measurable _ _ _ (generate_from s) f :=
measurable.of_le_map $ generate_from_le h

variables [measurable_space α] [measurable_space β] [measurable_space γ]

lemma measurable_id : measurable (@id α) := λ t, id

lemma measurable.comp {g : β → γ} {f : α → β} (hg : measurable g) (hf : measurable f) :
  measurable (g ∘ f) :=
λ t ht, hf (hg ht)

lemma measurable.iterate {f : α → α} (hf : measurable f) : ∀ n, measurable (f^[n])
| 0 := measurable_id
| (n+1) := (measurable.iterate n).comp hf

@[nontriviality] lemma subsingleton.measurable [subsingleton α] {f : α → β} : measurable f :=
λ s hs, @subsingleton.measurable_set α _ _ _

lemma measurable.piecewise {s : set α} {_ : decidable_pred s} {f g : α → β}
  (hs : measurable_set s) (hf : measurable f) (hg : measurable g) :
  measurable (piecewise s f g) :=
begin
  intros t ht,
  rw piecewise_preimage,
  exact hs.ite (hf ht) (hg ht)
end

/-- this is slightly different from `measurable.piecewise`. It can be used to show
`measurable (ite (x=0) 0 1)` by
`exact measurable.ite (measurable_set_singleton 0) measurable_const measurable_const`,
but replacing `measurable.ite` by `measurable.piecewise` in that example proof does not work. -/
lemma measurable.ite {p : α → Prop} {_ : decidable_pred p} {f g : α → β}
  (hp : measurable_set {a : α | p a}) (hf : measurable f) (hg : measurable g) :
  measurable (λ x, ite (p x) (f x) (g x)) :=
measurable.piecewise hp hf hg

@[simp] lemma measurable_const {a : α} : measurable (λ b : β, a) :=
assume s hs, measurable_set.const (a ∈ s)

lemma measurable.indicator [has_zero β] {s : set α} {f : α → β}
  (hf : measurable f) (hs : measurable_set s) : measurable (s.indicator f) :=
hf.piecewise hs measurable_const

@[to_additive]
lemma measurable_one [has_one α] : measurable (1 : β → α) := @measurable_const _ _ _ _ 1

lemma measurable_of_not_nonempty  (h : ¬ nonempty α) (f : α → β) : measurable f :=
begin
  assume s hs,
  convert measurable_set.empty,
  exact eq_empty_of_not_nonempty h _,
end

end measurable_functions

section constructions

variables [measurable_space α] [measurable_space β] [measurable_space γ]

instance : measurable_space empty := ⊤
instance : measurable_space punit := ⊤ -- this also works for `unit`
instance : measurable_space bool := ⊤
instance : measurable_space ℕ := ⊤
instance : measurable_space ℤ := ⊤
instance : measurable_space ℚ := ⊤

lemma measurable_to_encodable [encodable α] {f : β → α} (h : ∀ y, measurable_set (f ⁻¹' {f y})) :
  measurable f :=
begin
  assume s hs,
  rw [← bUnion_preimage_singleton],
  refine measurable_set.Union (λ y, measurable_set.Union_Prop $ λ hy, _),
  by_cases hyf : y ∈ range f,
  { rcases hyf with ⟨y, rfl⟩,
    apply h },
  { simp only [preimage_singleton_eq_empty.2 hyf, measurable_set.empty] }
end

lemma measurable_unit (f : unit → α) : measurable f :=
measurable_from_top

section nat

lemma measurable_from_nat {f : ℕ → α} : measurable f :=
measurable_from_top

lemma measurable_to_nat {f : α → ℕ} : (∀ y, measurable_set (f ⁻¹' {f y})) → measurable f :=
measurable_to_encodable

lemma measurable_find_greatest' {p : α → ℕ → Prop}
  {N} (hN : ∀ k ≤ N, measurable_set {x | nat.find_greatest (p x) N = k}) :
  measurable (λ x, nat.find_greatest (p x) N) :=
measurable_to_nat $ λ x, hN _ nat.find_greatest_le

lemma measurable_find_greatest {p : α → ℕ → Prop} {N} (hN : ∀ k ≤ N, measurable_set {x | p x k}) :
  measurable (λ x, nat.find_greatest (p x) N) :=
begin
  refine measurable_find_greatest' (λ k hk, _),
  simp only [nat.find_greatest_eq_iff, set_of_and, set_of_forall, ← compl_set_of],
  repeat { apply_rules [measurable_set.inter, measurable_set.const, measurable_set.Inter,
    measurable_set.Inter_Prop, measurable_set.compl, hN]; try { intros } }
end

lemma measurable_find {p : α → ℕ → Prop} (hp : ∀ x, ∃ N, p x N)
  (hm : ∀ k, measurable_set {x | p x k}) :
  measurable (λ x, nat.find (hp x)) :=
begin
  refine measurable_to_nat (λ x, _),
  simp only [set.preimage, mem_singleton_iff, nat.find_eq_iff, set_of_and, set_of_forall,
    ← compl_set_of],
  repeat { apply_rules [measurable_set.inter, hm, measurable_set.Inter, measurable_set.Inter_Prop,
    measurable_set.compl]; try { intros } }
end

end nat

section subtype

instance {α} {p : α → Prop} [m : measurable_space α] : measurable_space (subtype p) :=
m.comap (coe : _ → α)

lemma measurable_subtype_coe {p : α → Prop} : measurable (coe : subtype p → α) :=
measurable_space.le_map_comap

lemma measurable.subtype_coe {p : β → Prop} {f : α → subtype p} (hf : measurable f) :
  measurable (λ a : α, (f a : β)) :=
measurable_subtype_coe.comp hf

lemma measurable.subtype_mk {p : β → Prop} {f : α → β} (hf : measurable f) {h : ∀ x, p (f x)} :
  measurable (λ x, (⟨f x, h x⟩ : subtype p)) :=
λ t ⟨s, hs⟩, hs.2 ▸ by simp only [← preimage_comp, (∘), subtype.coe_mk, hf hs.1]

lemma measurable_set.subtype_image {s : set α} {t : set s}
  (hs : measurable_set s) : measurable_set t → measurable_set ((coe : s → α) '' t)
| ⟨u, (hu : measurable_set u), (eq : coe ⁻¹' u = t)⟩ :=
  begin
    rw [← eq, subtype.image_preimage_coe],
    exact hu.inter hs
  end

lemma measurable_of_measurable_union_cover
  {f : α → β} (s t : set α) (hs : measurable_set s) (ht : measurable_set t) (h : univ ⊆ s ∪ t)
  (hc : measurable (λ a : s, f a)) (hd : measurable (λ a : t, f a)) :
  measurable f :=
begin
  intros u hu,
  convert (hs.subtype_image (hc hu)).union (ht.subtype_image (hd hu)),
  change f ⁻¹' u = coe '' (coe ⁻¹' (f ⁻¹' u) : set s) ∪ coe '' (coe ⁻¹' (f ⁻¹' u) : set t),
  rw [image_preimage_eq_inter_range, image_preimage_eq_inter_range, subtype.range_coe,
      subtype.range_coe, ← inter_distrib_left, univ_subset_iff.1 h, inter_univ],
end

lemma measurable_of_measurable_on_compl_singleton [measurable_singleton_class α]
  {f : α → β} (a : α) (hf : measurable (set.restrict f {x | x ≠ a})) :
  measurable f :=
measurable_of_measurable_union_cover _ _ measurable_set_eq measurable_set_eq.compl
  (λ x hx, classical.em _)
  (@subsingleton.measurable {x | x = a} _ _ _ ⟨λ x y, subtype.eq $ x.2.trans y.2.symm⟩ _) hf

end subtype

section prod

instance {α β} [m₁ : measurable_space α] [m₂ : measurable_space β] : measurable_space (α × β) :=
m₁.comap prod.fst ⊔ m₂.comap prod.snd

lemma measurable_fst : measurable (prod.fst : α × β → α) :=
measurable.of_comap_le le_sup_left

lemma measurable.fst {f : α → β × γ} (hf : measurable f) : measurable (λ a : α, (f a).1) :=
measurable_fst.comp hf

lemma measurable_snd : measurable (prod.snd : α × β → β) :=
measurable.of_comap_le le_sup_right

lemma measurable.snd {f : α → β × γ} (hf : measurable f) : measurable (λ a : α, (f a).2) :=
measurable_snd.comp hf

lemma measurable.prod {f : α → β × γ}
  (hf₁ : measurable (λ a, (f a).1)) (hf₂ : measurable (λ a, (f a).2)) : measurable f :=
measurable.of_le_map $ sup_le
  (by { rw [measurable_space.comap_le_iff_le_map, measurable_space.map_comp], exact hf₁ })
  (by { rw [measurable_space.comap_le_iff_le_map, measurable_space.map_comp], exact hf₂ })

lemma measurable_prod {f : α → β × γ} : measurable f ↔
  measurable (λ a, (f a).1) ∧ measurable (λ a, (f a).2) :=
⟨λ hf, ⟨measurable_fst.comp hf, measurable_snd.comp hf⟩, λ h, measurable.prod h.1 h.2⟩

lemma measurable.prod_mk {f : α → β} {g : α → γ} (hf : measurable f) (hg : measurable g) :
  measurable (λ a : α, (f a, g a)) :=
measurable.prod hf hg

lemma measurable_prod_mk_left {x : α} : measurable (@prod.mk _ β x) :=
measurable_const.prod_mk measurable_id

lemma measurable_prod_mk_right {y : β} : measurable (λ x : α, (x, y)) :=
measurable_id.prod_mk measurable_const

lemma measurable.prod_map [measurable_space δ] {f : α → β} {g : γ → δ} (hf : measurable f)
  (hg : measurable g) : measurable (prod.map f g) :=
(hf.comp measurable_fst).prod_mk (hg.comp measurable_snd)

lemma measurable.of_uncurry_left {f : α → β → γ} (hf : measurable (uncurry f)) {x : α} :
  measurable (f x) :=
hf.comp measurable_prod_mk_left

lemma measurable.of_uncurry_right {f : α → β → γ} (hf : measurable (uncurry f)) {y : β} :
  measurable (λ x, f x y) :=
hf.comp measurable_prod_mk_right

lemma measurable_swap : measurable (prod.swap : α × β → β × α) :=
measurable.prod measurable_snd measurable_fst

lemma measurable_swap_iff {f : α × β → γ} : measurable (f ∘ prod.swap) ↔ measurable f :=
⟨λ hf, by { convert hf.comp measurable_swap, ext ⟨x, y⟩, refl }, λ hf, hf.comp measurable_swap⟩

lemma measurable_set.prod {s : set α} {t : set β} (hs : measurable_set s) (ht : measurable_set t) :
  measurable_set (s.prod t) :=
measurable_set.inter (measurable_fst hs) (measurable_snd ht)

lemma measurable_set_prod_of_nonempty {s : set α} {t : set β} (h : (s.prod t).nonempty) :
  measurable_set (s.prod t) ↔ measurable_set s ∧ measurable_set t :=
begin
  rcases h with ⟨⟨x, y⟩, hx, hy⟩,
  refine ⟨λ hst, _, λ h, h.1.prod h.2⟩,
  have : measurable_set ((λ x, (x, y)) ⁻¹' s.prod t) := measurable_id.prod_mk measurable_const hst,
  have : measurable_set (prod.mk x ⁻¹' s.prod t) := measurable_const.prod_mk measurable_id hst,
  simp * at *
end

lemma measurable_set_prod {s : set α} {t : set β} :
  measurable_set (s.prod t) ↔ (measurable_set s ∧ measurable_set t) ∨ s = ∅ ∨ t = ∅ :=
begin
  cases (s.prod t).eq_empty_or_nonempty with h h,
  { simp [h, prod_eq_empty_iff.mp h] },
  { simp [←not_nonempty_iff_eq_empty, prod_nonempty_iff.mp h, measurable_set_prod_of_nonempty h] }
end

lemma measurable_set_swap_iff {s : set (α × β)} :
  measurable_set (prod.swap ⁻¹' s) ↔ measurable_set s :=
⟨λ hs, by { convert measurable_swap hs, ext ⟨x, y⟩, refl }, λ hs, measurable_swap hs⟩

lemma measurable_from_prod_encodable [encodable β] [measurable_singleton_class β]
  {f : α × β → γ} (hf : ∀ y, measurable (λ x, f (x, y))) :
  measurable f :=
begin
  intros s hs,
  have : f ⁻¹' s = ⋃ y, ((λ x, f (x, y)) ⁻¹' s).prod {y},
  { ext1 ⟨x, y⟩,
    simp [and_assoc, and.left_comm] },
  rw this,
  exact measurable_set.Union (λ y, (hf y hs).prod (measurable_set_singleton y))
end

end prod

section pi

variables {π : δ → Type*}

instance measurable_space.pi [m : Π a, measurable_space (π a)] : measurable_space (Π a, π a) :=
⨆ a, (m a).comap (λ b, b a)

variables [Π a, measurable_space (π a)] [measurable_space γ]

lemma measurable_pi_iff {g : α → Π a, π a} :
  measurable g ↔ ∀ a, measurable (λ x, g x a) :=
by simp_rw [measurable_iff_comap_le, measurable_space.pi, measurable_space.comap_supr,
    measurable_space.comap_comp, function.comp, supr_le_iff]

lemma measurable_pi_apply (a : δ) : measurable (λ f : Π a, π a, f a) :=
measurable.of_comap_le $ le_supr _ a

lemma measurable.eval {a : δ} {g : α → Π a, π a}
  (hg : measurable g) : measurable (λ x, g x a) :=
(measurable_pi_apply a).comp hg

lemma measurable_pi_lambda (f : α → Π a, π a) (hf : ∀ a, measurable (λ c, f c a)) :
  measurable f :=
measurable_pi_iff.mpr hf

/-- The function `update f a : π a → Π a, π a` is always measurable.
  This doesn't require `f` to be measurable.
  This should not be confused with the statement that `update f a x` is measurable. -/
lemma measurable_update (f : Π (a : δ), π a) {a : δ} : measurable (update f a) :=
begin
  apply measurable_pi_lambda,
  intro x, by_cases hx : x = a,
  { cases hx, convert measurable_id, ext, simp },
  simp_rw [update_noteq hx], apply measurable_const,
end

/- Even though we cannot use projection notation, we still keep a dot to be consistent with similar
  lemmas, like `measurable_set.prod`. -/
lemma measurable_set.pi {s : set δ} {t : Π i : δ, set (π i)} (hs : countable s)
  (ht : ∀ i ∈ s, measurable_set (t i)) :
  measurable_set (s.pi t) :=
by { rw [pi_def], exact measurable_set.bInter hs (λ i hi, measurable_pi_apply _ (ht i hi)) }

lemma measurable_set.univ_pi [encodable δ] {t : Π i : δ, set (π i)}
  (ht : ∀ i, measurable_set (t i)) : measurable_set (pi univ t) :=
measurable_set.pi (countable_encodable _) (λ i _, ht i)

lemma measurable_set_pi_of_nonempty {s : set δ} {t : Π i, set (π i)} (hs : countable s)
  (h : (pi s t).nonempty) : measurable_set (pi s t) ↔ ∀ i ∈ s, measurable_set (t i) :=
begin
  rcases h with ⟨f, hf⟩, refine ⟨λ hst i hi, _, measurable_set.pi hs⟩,
  convert measurable_update f hst, rw [update_preimage_pi hi], exact λ j hj _, hf j hj
end

lemma measurable_set_pi {s : set δ} {t : Π i, set (π i)} (hs : countable s) :
  measurable_set (pi s t) ↔ (∀ i ∈ s, measurable_set (t i)) ∨ pi s t = ∅ :=
begin
  cases (pi s t).eq_empty_or_nonempty with h h,
  { simp [h] },
  { simp [measurable_set_pi_of_nonempty hs, h, ← not_nonempty_iff_eq_empty] }
end

section fintype

local attribute [instance] fintype.encodable

lemma measurable_set.pi_fintype [fintype δ] {s : set δ} {t : Π i, set (π i)}
  (ht : ∀ i ∈ s, measurable_set (t i)) : measurable_set (pi s t) :=
measurable_set.pi (countable_encodable _) ht

lemma measurable_set.univ_pi_fintype [fintype δ] {t : Π i, set (π i)}
  (ht : ∀ i, measurable_set (t i)) : measurable_set (pi univ t) :=
measurable_set.pi_fintype (λ i _, ht i)

end fintype
end pi

instance tprod.measurable_space (π : δ → Type*) [∀ x, measurable_space (π x)] :
  ∀ (l : list δ), measurable_space (list.tprod π l)
| []        := punit.measurable_space
| (i :: is) := @prod.measurable_space _ _ _ (tprod.measurable_space is)

section tprod

open list

variables {π : δ → Type*} [∀ x, measurable_space (π x)]

lemma measurable_tprod_mk (l : list δ) : measurable (@tprod.mk δ π l) :=
begin
  induction l with i l ih,
  { exact measurable_const },
  { exact (measurable_pi_apply i).prod_mk ih }
end

lemma measurable_tprod_elim : ∀ {l : list δ} {i : δ} (hi : i ∈ l),
  measurable (λ (v : tprod π l), v.elim hi)
| (i :: is) j hj := begin
  by_cases hji : j = i,
  { subst hji, simp [measurable_fst] },
  { rw [funext $ tprod.elim_of_ne _ hji],
    exact (measurable_tprod_elim (hj.resolve_left hji)).comp measurable_snd }
end

lemma measurable_tprod_elim' {l : list δ} (h : ∀ i, i ∈ l) :
  measurable (tprod.elim' h : tprod π l → Π i, π i) :=
measurable_pi_lambda _ (λ i, measurable_tprod_elim (h i))

lemma measurable_set.tprod (l : list δ) {s : ∀ i, set (π i)} (hs : ∀ i, measurable_set (s i)) :
  measurable_set (set.tprod l s) :=
by { induction l with i l ih, exact measurable_set.univ, exact (hs i).prod ih }

end tprod

instance {α β} [m₁ : measurable_space α] [m₂ : measurable_space β] : measurable_space (α ⊕ β) :=
m₁.map sum.inl ⊓ m₂.map sum.inr

section sum

lemma measurable_inl : measurable (@sum.inl α β) := measurable.of_le_map inf_le_left

lemma measurable_inr : measurable (@sum.inr α β) := measurable.of_le_map inf_le_right

lemma measurable_sum {f : α ⊕ β → γ}
  (hl : measurable (f ∘ sum.inl)) (hr : measurable (f ∘ sum.inr)) : measurable f :=
measurable.of_comap_le $ le_inf
  (measurable_space.comap_le_iff_le_map.2 $ hl)
  (measurable_space.comap_le_iff_le_map.2 $ hr)

lemma measurable.sum_elim {f : α → γ} {g : β → γ} (hf : measurable f) (hg : measurable g) :
  measurable (sum.elim f g) :=
measurable_sum hf hg

lemma measurable_set.inl_image {s : set α} (hs : measurable_set s) :
  measurable_set (sum.inl '' s : set (α ⊕ β)) :=
⟨show measurable_set (sum.inl ⁻¹' _), by { rwa [preimage_image_eq], exact (λ a b, sum.inl.inj) },
  have sum.inr ⁻¹' (sum.inl '' s : set (α ⊕ β)) = ∅ :=
    eq_empty_of_subset_empty $ assume x ⟨y, hy, eq⟩, by contradiction,
  show measurable_set (sum.inr ⁻¹' _), by { rw [this], exact measurable_set.empty }⟩

lemma measurable_set_range_inl : measurable_set (range sum.inl : set (α ⊕ β)) :=
by { rw [← image_univ], exact measurable_set.univ.inl_image }

lemma measurable_set_inr_image {s : set β} (hs : measurable_set s) :
  measurable_set (sum.inr '' s : set (α ⊕ β)) :=
⟨ have sum.inl ⁻¹' (sum.inr '' s : set (α ⊕ β)) = ∅ :=
    eq_empty_of_subset_empty $ assume x ⟨y, hy, eq⟩, by contradiction,
  show measurable_set (sum.inl ⁻¹' _), by { rw [this], exact measurable_set.empty },
  show measurable_set (sum.inr ⁻¹' _), by { rwa [preimage_image_eq], exact λ a b, sum.inr.inj }⟩

lemma measurable_set_range_inr : measurable_set (range sum.inr : set (α ⊕ β)) :=
by { rw [← image_univ], exact measurable_set_inr_image measurable_set.univ }

end sum

instance {α} {β : α → Type*} [m : Πa, measurable_space (β a)] : measurable_space (sigma β) :=
⨅a, (m a).map (sigma.mk a)

end constructions

/-- Equivalences between measurable spaces. Main application is the simplification of measurability
statements along measurable equivalences. -/
structure measurable_equiv (α β : Type*) [measurable_space α] [measurable_space β] extends α ≃ β :=
(measurable_to_fun : measurable to_fun)
(measurable_inv_fun : measurable inv_fun)

infix ` ≃ᵐ `:25 := measurable_equiv

namespace measurable_equiv

variables (α β) [measurable_space α] [measurable_space β] [measurable_space γ] [measurable_space δ]

instance : has_coe_to_fun (α ≃ᵐ β) :=
⟨λ _, α → β, λ e, e.to_equiv⟩

variables {α β}

lemma coe_eq (e : α ≃ᵐ β) : (e : α → β) = e.to_equiv := rfl

protected lemma measurable (e : α ≃ᵐ β) : measurable (e : α → β) :=
e.measurable_to_fun

@[simp] lemma coe_mk (e : α ≃ β) (h1 : measurable e) (h2 : measurable e.symm) :
  ((⟨e, h1, h2⟩ : α ≃ᵐ β) : α → β) = e := rfl

/-- Any measurable space is equivalent to itself. -/
def refl (α : Type*) [measurable_space α] : α ≃ᵐ α :=
{ to_equiv := equiv.refl α,
  measurable_to_fun := measurable_id, measurable_inv_fun := measurable_id }

instance : inhabited (α ≃ᵐ α) := ⟨refl α⟩

/-- The composition of equivalences between measurable spaces. -/
@[simps] def trans (ab : α ≃ᵐ β) (bc : β ≃ᵐ γ) :
  α ≃ᵐ γ :=
{ to_equiv := ab.to_equiv.trans bc.to_equiv,
  measurable_to_fun := bc.measurable_to_fun.comp ab.measurable_to_fun,
  measurable_inv_fun := ab.measurable_inv_fun.comp bc.measurable_inv_fun }

/-- The inverse of an equivalence between measurable spaces. -/
@[simps] def symm (ab : α ≃ᵐ β) : β ≃ᵐ α :=
{ to_equiv := ab.to_equiv.symm,
  measurable_to_fun := ab.measurable_inv_fun,
  measurable_inv_fun := ab.measurable_to_fun }

@[simp] lemma coe_symm_mk (e : α ≃ β) (h1 : measurable e) (h2 : measurable e.symm) :
  ((⟨e, h1, h2⟩ : α ≃ᵐ β).symm : β → α) = e.symm := rfl

@[simp] theorem symm_comp_self (e : α ≃ᵐ β) : e.symm ∘ e = id := funext e.left_inv

@[simp] theorem self_comp_symm (e : α ≃ᵐ β) : e ∘ e.symm = id := funext e.right_inv

/-- Equal measurable spaces are equivalent. -/
protected def cast {α β} [i₁ : measurable_space α] [i₂ : measurable_space β]
  (h : α = β) (hi : i₁ == i₂) : α ≃ᵐ β :=
{ to_equiv := equiv.cast h,
  measurable_to_fun  := by { substI h, substI hi, exact measurable_id },
  measurable_inv_fun := by { substI h, substI hi, exact measurable_id }}

protected lemma measurable_coe_iff {f : β → γ} (e : α ≃ᵐ β) :
  measurable (f ∘ e) ↔ measurable f :=
iff.intro
  (assume hfe,
    have measurable (f ∘ (e.symm.trans e).to_equiv) := hfe.comp e.symm.measurable,
    by rwa [trans_to_equiv, symm_to_equiv, equiv.symm_trans] at this)
  (λ h, h.comp e.measurable)

/-- Products of equivalent measurable spaces are equivalent. -/
def prod_congr (ab : α ≃ᵐ β) (cd : γ ≃ᵐ δ) : α × γ ≃ᵐ β × δ :=
{ to_equiv := prod_congr ab.to_equiv cd.to_equiv,
  measurable_to_fun := (ab.measurable_to_fun.comp measurable_id.fst).prod_mk
    (cd.measurable_to_fun.comp measurable_id.snd),
  measurable_inv_fun := (ab.measurable_inv_fun.comp measurable_id.fst).prod_mk
    (cd.measurable_inv_fun.comp measurable_id.snd) }

/-- Products of measurable spaces are symmetric. -/
def prod_comm : α × β ≃ᵐ β × α :=
{ to_equiv := prod_comm α β,
  measurable_to_fun  := measurable_id.snd.prod_mk measurable_id.fst,
  measurable_inv_fun := measurable_id.snd.prod_mk measurable_id.fst }

/-- Products of measurable spaces are associative. -/
def prod_assoc : (α × β) × γ ≃ᵐ α × (β × γ) :=
{ to_equiv := prod_assoc α β γ,
  measurable_to_fun  := measurable_fst.fst.prod_mk $ measurable_fst.snd.prod_mk measurable_snd,
  measurable_inv_fun := (measurable_fst.prod_mk measurable_snd.fst).prod_mk measurable_snd.snd }

/-- Sums of measurable spaces are symmetric. -/
def sum_congr (ab : α ≃ᵐ β) (cd : γ ≃ᵐ δ) : α ⊕ γ ≃ᵐ β ⊕ δ :=
{ to_equiv := sum_congr ab.to_equiv cd.to_equiv,
  measurable_to_fun :=
    begin
      cases ab with ab' abm, cases ab', cases cd with cd' cdm, cases cd',
      refine measurable_sum (measurable_inl.comp abm) (measurable_inr.comp cdm)
    end,
  measurable_inv_fun :=
    begin
      cases ab with ab' _ abm, cases ab', cases cd with cd' _ cdm, cases cd',
      refine measurable_sum (measurable_inl.comp abm) (measurable_inr.comp cdm)
    end }

/-- `set.prod s t ≃ (s × t)` as measurable spaces. -/
def set.prod (s : set α) (t : set β) : s.prod t ≃ᵐ s × t :=
{ to_equiv := equiv.set.prod s t,
  measurable_to_fun := measurable_id.subtype_coe.fst.subtype_mk.prod_mk
    measurable_id.subtype_coe.snd.subtype_mk,
  measurable_inv_fun := measurable.subtype_mk $ measurable_id.fst.subtype_coe.prod_mk
    measurable_id.snd.subtype_coe }

/-- `univ α ≃ α` as measurable spaces. -/
def set.univ (α : Type*) [measurable_space α] : (univ : set α) ≃ᵐ α :=
{ to_equiv := equiv.set.univ α,
  measurable_to_fun := measurable_id.subtype_coe,
  measurable_inv_fun := measurable_id.subtype_mk }

/-- `{a} ≃ unit` as measurable spaces. -/
def set.singleton (a : α) : ({a} : set α) ≃ᵐ unit :=
{ to_equiv := equiv.set.singleton a,
  measurable_to_fun := measurable_const,
  measurable_inv_fun := measurable_const }

/-- A set is equivalent to its image under a function `f` as measurable spaces,
  if `f` is an injective measurable function that sends measurable sets to measurable sets. -/
noncomputable def set.image (f : α → β) (s : set α) (hf : injective f)
  (hfm : measurable f) (hfi : ∀ s, measurable_set s → measurable_set (f '' s)) : s ≃ᵐ (f '' s) :=
{ to_equiv := equiv.set.image f s hf,
  measurable_to_fun  := (hfm.comp measurable_id.subtype_coe).subtype_mk,
  measurable_inv_fun :=
    begin
      rintro t ⟨u, hu, rfl⟩, simp [preimage_preimage, set.image_symm_preimage hf],
      exact measurable_subtype_coe (hfi u hu)
    end }

/-- The domain of `f` is equivalent to its range as measurable spaces,
  if `f` is an injective measurable function that sends measurable sets to measurable sets. -/
noncomputable def set.range (f : α → β) (hf : injective f) (hfm : measurable f)
  (hfi : ∀ s, measurable_set s → measurable_set (f '' s)) :
  α ≃ᵐ (range f) :=
(measurable_equiv.set.univ _).symm.trans $
  (measurable_equiv.set.image f univ hf hfm hfi).trans $
  measurable_equiv.cast (by rw image_univ) (by rw image_univ)

/-- `α` is equivalent to its image in `α ⊕ β` as measurable spaces. -/
def set.range_inl : (range sum.inl : set (α ⊕ β)) ≃ᵐ α :=
{ to_fun    := λ ab, match ab with
    | ⟨sum.inl a, _⟩ := a
    | ⟨sum.inr b, p⟩ := have false, by { cases p, contradiction }, this.elim
    end,
  inv_fun   := λ a, ⟨sum.inl a, a, rfl⟩,
  left_inv  := by { rintro ⟨ab, a, rfl⟩, refl },
  right_inv := assume a, rfl,
  measurable_to_fun  := assume s (hs : measurable_set s),
    begin
      refine ⟨_, hs.inl_image, set.ext _⟩,
      rintros ⟨ab, a, rfl⟩,
      simp [set.range_inl._match_1]
    end,
  measurable_inv_fun := measurable.subtype_mk measurable_inl }

/-- `β` is equivalent to its image in `α ⊕ β` as measurable spaces. -/
def set.range_inr : (range sum.inr : set (α ⊕ β)) ≃ᵐ β :=
{ to_fun    := λ ab, match ab with
    | ⟨sum.inr b, _⟩ := b
    | ⟨sum.inl a, p⟩ := have false, by { cases p, contradiction }, this.elim
    end,
  inv_fun   := λ b, ⟨sum.inr b, b, rfl⟩,
  left_inv  := by { rintro ⟨ab, b, rfl⟩, refl },
  right_inv := assume b, rfl,
  measurable_to_fun  := assume s (hs : measurable_set s),
    begin
      refine ⟨_, measurable_set_inr_image hs, set.ext _⟩,
      rintros ⟨ab, b, rfl⟩,
      simp [set.range_inr._match_1]
    end,
  measurable_inv_fun := measurable.subtype_mk measurable_inr }

/-- Products distribute over sums (on the right) as measurable spaces. -/
def sum_prod_distrib (α β γ) [measurable_space α] [measurable_space β] [measurable_space γ] :
  (α ⊕ β) × γ ≃ᵐ (α × γ) ⊕ (β × γ) :=
{ to_equiv := sum_prod_distrib α β γ,
  measurable_to_fun  :=
  begin
    refine measurable_of_measurable_union_cover
      ((range sum.inl).prod univ)
      ((range sum.inr).prod univ)
      (measurable_set_range_inl.prod measurable_set.univ)
      (measurable_set_range_inr.prod measurable_set.univ)
      (by { rintro ⟨a|b, c⟩; simp [set.prod_eq] })
      _
      _,
    { refine (set.prod (range sum.inl) univ).symm.measurable_coe_iff.1 _,
      refine (prod_congr set.range_inl (set.univ _)).symm.measurable_coe_iff.1 _,
      dsimp [(∘)],
      convert measurable_inl,
      ext ⟨a, c⟩, refl },
    { refine (set.prod (range sum.inr) univ).symm.measurable_coe_iff.1 _,
      refine (prod_congr set.range_inr (set.univ _)).symm.measurable_coe_iff.1 _,
      dsimp [(∘)],
      convert measurable_inr,
      ext ⟨b, c⟩, refl }
  end,
  measurable_inv_fun :=
    measurable_sum
      ((measurable_inl.comp measurable_fst).prod_mk measurable_snd)
      ((measurable_inr.comp measurable_fst).prod_mk measurable_snd) }

/-- Products distribute over sums (on the left) as measurable spaces. -/
def prod_sum_distrib (α β γ) [measurable_space α] [measurable_space β] [measurable_space γ] :
  α × (β ⊕ γ) ≃ᵐ (α × β) ⊕ (α × γ) :=
prod_comm.trans $ (sum_prod_distrib _ _ _).trans $ sum_congr prod_comm prod_comm

/-- Products distribute over sums as measurable spaces. -/
def sum_prod_sum (α β γ δ)
  [measurable_space α] [measurable_space β] [measurable_space γ] [measurable_space δ] :
  (α ⊕ β) × (γ ⊕ δ) ≃ᵐ ((α × γ) ⊕ (α × δ)) ⊕ ((β × γ) ⊕ (β × δ)) :=
(sum_prod_distrib _ _ _).trans $ sum_congr (prod_sum_distrib _ _ _) (prod_sum_distrib _ _ _)

variables {π π' : δ' → Type*} [∀ x, measurable_space (π x)] [∀ x, measurable_space (π' x)]

/-- A family of measurable equivalences `Π a, β₁ a ≃ᵐ β₂ a` generates a measurable equivalence
  between  `Π a, β₁ a` and `Π a, β₂ a`. -/
def Pi_congr_right (e : Π a, π a ≃ᵐ π' a) : (Π a, π a) ≃ᵐ (Π a, π' a) :=
{ to_equiv := Pi_congr_right (λ a, (e a).to_equiv),
  measurable_to_fun :=
    measurable_pi_lambda _ (λ i, (e i).measurable_to_fun.comp (measurable_pi_apply i)),
  measurable_inv_fun :=
    measurable_pi_lambda _ (λ i, (e i).measurable_inv_fun.comp (measurable_pi_apply i)) }

/-- Pi-types are measurably equivalent to iterated products. -/
noncomputable def pi_measurable_equiv_tprod {l : list δ'} (hnd : l.nodup) (h : ∀ i, i ∈ l) :
  (Π i, π i) ≃ᵐ list.tprod π l :=
{ to_equiv := list.tprod.pi_equiv_tprod hnd h,
  measurable_to_fun := measurable_tprod_mk l,
  measurable_inv_fun := measurable_tprod_elim' h }

end measurable_equiv

namespace filter

variables [measurable_space α]

/-- A filter `f` is measurably generates if each `s ∈ f` includes a measurable `t ∈ f`. -/
class is_measurably_generated (f : filter α) : Prop :=
(exists_measurable_subset : ∀ ⦃s⦄, s ∈ f → ∃ t ∈ f, measurable_set t ∧ t ⊆ s)

instance is_measurably_generated_bot : is_measurably_generated (⊥ : filter α) :=
⟨λ _ _, ⟨∅, mem_bot_sets, measurable_set.empty, empty_subset _⟩⟩

instance is_measurably_generated_top : is_measurably_generated (⊤ : filter α) :=
⟨λ s hs, ⟨univ, univ_mem_sets, measurable_set.univ, λ x _, hs x⟩⟩

lemma eventually.exists_measurable_mem {f : filter α} [is_measurably_generated f]
  {p : α → Prop} (h : ∀ᶠ x in f, p x) :
  ∃ s ∈ f, measurable_set s ∧ ∀ x ∈ s, p x :=
is_measurably_generated.exists_measurable_subset h

lemma eventually.exists_measurable_mem_of_lift' {f : filter α} [is_measurably_generated f]
  {p : set α → Prop} (h : ∀ᶠ s in f.lift' powerset, p s) :
  ∃ s ∈ f, measurable_set s ∧ p s :=
let ⟨s, hsf, hs⟩ := eventually_lift'_powerset.1 h,
  ⟨t, htf, htm, hts⟩ := is_measurably_generated.exists_measurable_subset hsf
in ⟨t, htf, htm, hs t hts⟩

instance inf_is_measurably_generated (f g : filter α) [is_measurably_generated f]
  [is_measurably_generated g] :
  is_measurably_generated (f ⊓ g) :=
begin
  refine ⟨_⟩,
  rintros t ⟨sf, hsf, sg, hsg, ht⟩,
  rcases is_measurably_generated.exists_measurable_subset hsf with ⟨s'f, hs'f, hmf, hs'sf⟩,
  rcases is_measurably_generated.exists_measurable_subset hsg with ⟨s'g, hs'g, hmg, hs'sg⟩,
  refine ⟨s'f ∩ s'g, inter_mem_inf_sets hs'f hs'g, hmf.inter hmg, _⟩,
  exact subset.trans (inter_subset_inter hs'sf hs'sg) ht
end

lemma principal_is_measurably_generated_iff {s : set α} :
  is_measurably_generated (𝓟 s) ↔ measurable_set s :=
begin
  refine ⟨_, λ hs, ⟨λ t ht, ⟨s, mem_principal_self s, hs, ht⟩⟩⟩,
  rintros ⟨hs⟩,
  rcases hs (mem_principal_self s) with ⟨t, ht, htm, hts⟩,
  have : t = s := subset.antisymm hts ht,
  rwa ← this
end

alias principal_is_measurably_generated_iff ↔
  _ measurable_set.principal_is_measurably_generated

instance infi_is_measurably_generated {f : ι → filter α} [∀ i, is_measurably_generated (f i)] :
  is_measurably_generated (⨅ i, f i) :=
begin
  refine ⟨λ s hs, _⟩,
  rw [← equiv.plift.surjective.infi_comp, mem_infi_iff] at hs,
  rcases hs with ⟨t, ht, ⟨V, hVf, hVs⟩⟩,
  choose U hUf hU using λ i, is_measurably_generated.exists_measurable_subset (hVf i),
  refine ⟨⋂ i : t, U i, _, _, _⟩,
  { rw [← equiv.plift.surjective.infi_comp, mem_infi_iff],
    refine ⟨t, ht, U, hUf, subset.refl _⟩ },
  { haveI := ht.countable.to_encodable,
    refine measurable_set.Inter (λ i, (hU i).1) },
  { exact subset.trans (Inter_subset_Inter $ λ i, (hU i).2) hVs }
end

end filter

/-- We say that a collection of sets is countably spanning if a countable subset spans the
  whole type. This is a useful condition in various parts of measure theory. For example, it is
  a needed condition to show that the product of two collections generate the product sigma algebra,
  see `generate_from_prod_eq`. -/
def is_countably_spanning (C : set (set α)) : Prop :=
∃ (s : ℕ → set α), (∀ n, s n ∈ C) ∧ (⋃ n, s n) = univ

lemma is_countably_spanning_measurable_set [measurable_space α] :
  is_countably_spanning {s : set α | measurable_set s} :=
⟨λ _, univ, λ _, measurable_set.univ, Union_const _⟩

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import data.set.finite
import data.countable.basic
import logic.equiv.list

/-!
# Countable sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/
noncomputable theory

open function set encodable

open classical (hiding some)
open_locale classical
universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

namespace set

/-- A set is countable if there exists an encoding of the set into the natural numbers.
An encoding is an injection with a partial inverse, which can be viewed as a
constructive analogue of countability. (For the most part, theorems about
`countable` will be classical and `encodable` will be constructive.)
-/
protected def countable (s : set α) : Prop := nonempty (encodable s)

@[simp] lemma countable_coe_iff {s : set α} : countable s ↔ s.countable :=
encodable.nonempty_encodable.symm

/-- Prove `set.countable` from a `countable` instance on the subtype. -/
lemma to_countable (s : set α) [countable s] : s.countable := countable_coe_iff.mp ‹_›

/-- Restate `set.countable` as a `countable` instance. -/
alias countable_coe_iff ↔ _root_.countable.to_set countable.to_subtype

protected lemma countable_iff_exists_injective {s : set α} :
  s.countable ↔ ∃ f : s → ℕ, injective f :=
countable_coe_iff.symm.trans (countable_iff_exists_injective s)

/-- A set `s : set α` is countable if and only if there exists a function `α → ℕ` injective
on `s`. -/
lemma countable_iff_exists_inj_on {s : set α} :
  s.countable ↔ ∃ f : α → ℕ, inj_on f s :=
set.countable_iff_exists_injective.trans exists_inj_on_iff_injective.symm

/-- Convert `set.countable s` to `encodable s` (noncomputable). -/
protected def countable.to_encodable {s : set α} : s.countable → encodable s :=
classical.choice

section enumerate

/-- Noncomputably enumerate elements in a set. The `default` value is used to extend the domain to
all of `ℕ`. -/

def enumerate_countable {s : set α} (h : s.countable) (default : α) : ℕ → α :=
assume n, match @encodable.decode s h.to_encodable n with
        | (some y) := y
        | (none)   := default
        end

lemma subset_range_enumerate {s : set α} (h : s.countable) (default : α) :
   s ⊆ range (enumerate_countable h default) :=
assume x hx,
⟨@encodable.encode s h.to_encodable ⟨x, hx⟩,
by simp [enumerate_countable, encodable.encodek]⟩

end enumerate

lemma countable.mono {s₁ s₂ : set α} (h : s₁ ⊆ s₂) : s₂.countable → s₁.countable
| ⟨H⟩ := ⟨@of_inj _ _ H _ (embedding_of_subset _ _ h).2⟩

lemma countable_range [countable ι] (f : ι → β) : (range f).countable :=
surjective_onto_range.countable.to_set

lemma countable_iff_exists_subset_range [nonempty α] {s : set α} :
  s.countable ↔ ∃ f : ℕ → α, s ⊆ range f :=
⟨λ h, by { inhabit α, exact ⟨enumerate_countable h default, subset_range_enumerate _ _⟩ },
  λ ⟨f, hsf⟩, (countable_range f).mono hsf⟩

/--
A non-empty set is countable iff there exists a surjection from the
natural numbers onto the subtype induced by the set.
-/
protected lemma countable_iff_exists_surjective {s : set α} (hs : s.nonempty) :
  s.countable ↔ ∃ f : ℕ → s, surjective f :=
countable_coe_iff.symm.trans $ @countable_iff_exists_surjective s hs.to_subtype

alias set.countable_iff_exists_surjective ↔ countable.exists_surjective _

lemma countable_univ [countable α] : (univ : set α).countable := to_countable univ

/-- If `s : set α` is a nonempty countable set, then there exists a map
`f : ℕ → α` such that `s = range f`. -/
lemma countable.exists_eq_range {s : set α} (hc : s.countable) (hs : s.nonempty) :
  ∃ f : ℕ → α, s = range f :=
begin
  rcases hc.exists_surjective hs with ⟨f, hf⟩,
  refine ⟨coe ∘ f, _⟩,
  rw [hf.range_comp, subtype.range_coe]
end

@[simp] lemma countable_empty : (∅ : set α).countable := to_countable _

@[simp] lemma countable_singleton (a : α) : ({a} : set α).countable :=
⟨of_equiv _ (equiv.set.singleton a)⟩

lemma countable.image {s : set α} (hs : s.countable) (f : α → β) : (f '' s).countable :=
by { rw [image_eq_range], haveI := hs.to_subtype, apply countable_range }

lemma maps_to.countable_of_inj_on {s : set α} {t : set β} {f : α → β}
  (hf : maps_to f s t) (hf' : inj_on f s) (ht : t.countable) :
  s.countable :=
have injective (hf.restrict f s t), from (inj_on_iff_injective.1 hf').cod_restrict _,
⟨@encodable.of_inj _ _ ht.to_encodable _ this⟩

lemma countable.preimage_of_inj_on {s : set β} (hs : s.countable) {f : α → β}
  (hf : inj_on f (f ⁻¹' s)) : (f ⁻¹' s).countable :=
(maps_to_preimage f s).countable_of_inj_on hf hs

protected lemma countable.preimage {s : set β} (hs : s.countable) {f : α → β} (hf : injective f) :
  (f ⁻¹' s).countable :=
hs.preimage_of_inj_on (hf.inj_on _)

lemma exists_seq_supr_eq_top_iff_countable [complete_lattice α] {p : α → Prop} (h : ∃ x, p x) :
  (∃ s : ℕ → α, (∀ n, p (s n)) ∧ (⨆ n, s n) = ⊤) ↔
    ∃ S : set α, S.countable ∧ (∀ s ∈ S, p s) ∧ Sup S = ⊤ :=
begin
  split,
  { rintro ⟨s, hps, hs⟩,
    refine ⟨range s, countable_range s, forall_range_iff.2 hps, _⟩, rwa Sup_range },
  { rintro ⟨S, hSc, hps, hS⟩,
    rcases eq_empty_or_nonempty S with rfl|hne,
    { rw [Sup_empty] at hS, haveI := subsingleton_of_bot_eq_top hS,
      rcases h with ⟨x, hx⟩, exact ⟨λ n, x, λ n, hx, subsingleton.elim _ _⟩ },
    { rcases (set.countable_iff_exists_surjective hne).1 hSc with ⟨s, hs⟩,
      refine ⟨λ n, s n, λ n, hps _ (s n).coe_prop, _⟩,
      rwa [hs.supr_comp, ← Sup_eq_supr'] } }
end

lemma exists_seq_cover_iff_countable {p : set α → Prop} (h : ∃ s, p s) :
  (∃ s : ℕ → set α, (∀ n, p (s n)) ∧ (⋃ n, s n) = univ) ↔
    ∃ S : set (set α), S.countable ∧ (∀ s ∈ S, p s) ∧ ⋃₀ S = univ :=
exists_seq_supr_eq_top_iff_countable h

lemma countable_of_injective_of_countable_image {s : set α} {f : α → β}
  (hf : inj_on f s) (hs : (f '' s).countable) : s.countable :=
let ⟨g, hg⟩ := countable_iff_exists_inj_on.1 hs in
countable_iff_exists_inj_on.2 ⟨g ∘ f, hg.comp hf (maps_to_image _ _)⟩

lemma countable_Union {t : ι → set α} [countable ι] (ht : ∀ i, (t i).countable) :
  (⋃ i, t i).countable :=
by { haveI := λ a, (ht a).to_subtype, rw Union_eq_range_psigma, apply countable_range }

@[simp] lemma countable_Union_iff [countable ι] {t : ι → set α} :
  (⋃ i, t i).countable ↔ ∀ i, (t i).countable :=
⟨λ h i, h.mono $ subset_Union _ _, countable_Union⟩

lemma countable.bUnion_iff {s : set α} {t : Π a ∈ s, set β} (hs : s.countable) :
  (⋃ a ∈ s, t a ‹_›).countable ↔ ∀ a ∈ s, (t a ‹_›).countable :=
by { haveI := hs.to_subtype, rw [bUnion_eq_Union, countable_Union_iff, set_coe.forall'] }

lemma countable.sUnion_iff {s : set (set α)} (hs : s.countable) :
  (⋃₀ s).countable ↔ ∀ a ∈ s, (a : _).countable :=
by rw [sUnion_eq_bUnion, hs.bUnion_iff]

alias countable.bUnion_iff ↔ _ countable.bUnion
alias countable.sUnion_iff ↔ _ countable.sUnion

@[simp] lemma countable_union {s t : set α} : (s ∪ t).countable ↔ s.countable ∧ t.countable :=
by simp [union_eq_Union, and.comm]

lemma countable.union {s t : set α} (hs : s.countable) (ht : t.countable) :
  (s ∪ t).countable :=
countable_union.2 ⟨hs, ht⟩

@[simp] lemma countable_insert {s : set α} {a : α} : (insert a s).countable ↔ s.countable :=
by simp only [insert_eq, countable_union, countable_singleton, true_and]

lemma countable.insert {s : set α} (a : α) (h : s.countable) : (insert a s).countable :=
countable_insert.2 h

lemma finite.countable {s : set α} : s.finite → s.countable
| ⟨h⟩ := trunc.nonempty (by exactI fintype.trunc_encodable s)

@[nontriviality] lemma countable.of_subsingleton [subsingleton α] (s : set α) :
  s.countable :=
(finite.of_subsingleton s).countable

lemma subsingleton.countable {s : set α} (hs : s.subsingleton) : s.countable :=
hs.finite.countable

lemma countable_is_top (α : Type*) [partial_order α] : {x : α | is_top x}.countable :=
(finite_is_top α).countable

lemma countable_is_bot (α : Type*) [partial_order α] : {x : α | is_bot x}.countable :=
(finite_is_bot α).countable

/-- The set of finite subsets of a countable set is countable. -/
lemma countable_set_of_finite_subset {s : set α} : s.countable →
  {t | set.finite t ∧ t ⊆ s}.countable | ⟨h⟩ :=
begin
  resetI,
  refine countable.mono _ (countable_range
    (λ t : finset s, {a | ∃ h:a ∈ s, subtype.mk a h ∈ t})),
  rintro t ⟨⟨ht⟩, ts⟩, resetI,
  refine ⟨finset.univ.map (embedding_of_subset _ _ ts), set.ext $ λ a, _⟩,
  simpa using @ts a
end

lemma countable_univ_pi {π : α → Type*} [finite α] {s : Π a, set (π a)}
  (hs : ∀ a, (s a).countable) : (pi univ s).countable :=
begin
  haveI := λ a, (hs a).to_subtype,
  exact (countable.of_equiv _ (equiv.set.univ_pi s).symm).to_set
end

lemma countable_pi {π : α → Type*} [finite α] {s : Πa, set (π a)} (hs : ∀a, (s a).countable) :
  {f : Πa, π a | ∀a, f a ∈ s a}.countable :=
by simpa only [← mem_univ_pi] using countable_univ_pi hs

protected lemma countable.prod {s : set α} {t : set β} (hs : s.countable) (ht : t.countable) :
  set.countable (s ×ˢ t) :=
begin
  haveI : countable s := hs.to_subtype,
  haveI : countable t := ht.to_subtype,
  exact (countable.of_equiv _ $ (equiv.set.prod _ _).symm).to_set
end

lemma countable.image2 {s : set α} {t : set β} (hs : s.countable) (ht : t.countable)
  (f : α → β → γ) : (image2 f s t).countable :=
by { rw ← image_prod, exact (hs.prod ht).image _ }

end set

lemma finset.countable_to_set (s : finset α) : set.countable (↑s : set α) :=
s.finite_to_set.countable

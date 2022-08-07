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
protected def countable (s : set α) : Prop := countable s

@[simp] lemma countable_coe_iff {s : set α} : countable s ↔ s.countable := nonempty_encodable.symm

/-- Prove `set.countable` from a `countable` instance on the subtype. -/
lemma to_countable (s : set α) [countable s] : s.countable := countable_coe_iff.mp ‹_›

/-- Restate `set.countable` as a `countable` instance. -/
alias countable_coe_iff ↔ _root_.countable.to_set countable.to_subtype

protected lemma countable_iff_exists_injective {s : set α} :
  s.countable ↔ ∃ f : s → ℕ, injective f :=
countable_iff_exists_injective

lemma countable_subtype_iff {s : set α} : countable s ↔ s.countable := iff.rfl

alias countable_subtype_iff ↔ _ countable.to_subtype

lemma countable.of_subtype (s : set α) [countable s] : s.countable := countable_subtype_iff.mp ‹_›

lemma countable.subset {s t : set α} (ht : t.countable) (h : s ⊆ t) : s.countable :=
by { haveI := ht.to_subtype, exact (inclusion_injective h).countable }

lemma subsingleton.countable {s : set α} (hs : s.subsingleton) : s.countable :=
@subsingleton.to_countable _ ((subsingleton_coe s).2 hs)

@[simp] lemma countable_empty : (∅ : set α).countable := subsingleton_empty.countable

@[simp] lemma countable_singleton (a : α) : ({a} : set α).countable :=
subsingleton_singleton.countable

/-- A set `s : set α` is countable if and only if there exists a function `α → ℕ` injective
on `s`. -/
lemma countable_iff_exists_inj_on {s : set α} :
  s.countable ↔ ∃ f : α → ℕ, inj_on f s :=
set.countable_iff_exists_injective.trans
⟨λ ⟨f, hf⟩, ⟨λ a, if h : a ∈ s then f ⟨a, h⟩ else 0,
   λ a as b bs h, congr_arg subtype.val $
     hf $ by simpa [as, bs] using h⟩,
 λ ⟨f, hf⟩, ⟨_,  hf.injective⟩⟩

/--
A non-empty set is countable iff there exists a surjection from the
natural numbers onto the subtype induced by the set.
-/
protected lemma countable_iff_exists_surjective {s : set α} (hs : s.nonempty) :
  s.countable ↔ ∃ f : ℕ → s, surjective f :=
@countable_iff_exists_surjective _ hs.to_subtype

alias set.countable_iff_exists_surjective ↔ countable.exists_surjective _

/-- If `s : set α` is a nonempty countable set, then there exists a map
`f : ℕ → α` such that `s = range f`. -/
lemma countable.exists_eq_range {s : set α} (hc : s.countable) (hs : s.nonempty) :
  ∃ f : ℕ → α, s = range f :=
let ⟨f, hf⟩ := hc.exists_surjective hs
in ⟨coe ∘ f, by rw [hf.range_comp, subtype.range_coe]⟩

lemma countable_range [countable ι] (f : ι → α) : (range f).countable :=
surjective_onto_range.countable

lemma countable.image {s : set α} (hs : s.countable) (f : α → β) : (f '' s).countable :=
by { haveI := hs.to_subtype, exact (surjective_maps_to_image_restrict f s).countable }

/-- Convert `set.countable s` to `encodable s` (noncomputable). -/
def countable.to_encodable {s : set α} : s.countable → encodable s :=
@encodable.of_countable _

section enumerate

/-- Enumerate elements in a countable set.-/
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

lemma countable_iff_exists_subset_range [nonempty α] {s : set α} :
  s.countable ↔ ∃ f : ℕ → α, s ⊆ range f :=
begin
  refine ⟨λ hs, _, λ ⟨f, hf⟩, (countable_range f).subset hf⟩,
  inhabit α,
  exact ⟨enumerate_countable hs default, subset_range_enumerate _ _⟩,
end

alias countable_iff_exists_subset_range ↔ set.countable.exists_subset_range _

lemma maps_to.countable_of_inj_on {s : set α} {t : set β} {f : α → β}
  (hf : maps_to f s t) (hf' : inj_on f s) (ht : t.countable) :
  s.countable :=
@injective.countable _ _ ht _ (hf'.injective.cod_restrict $ λ x, hf x.2)

lemma countable.preimage_of_inj_on {s : set β} (hs : s.countable) {f : α → β}
  (hf : inj_on f (f ⁻¹' s)) : (f ⁻¹' s).countable :=
(maps_to_preimage f s).countable_of_inj_on hf hs

lemma countable_Union {t : ι → set α} [countable ι] (ht : ∀ i, (t i).countable) :
  (⋃ i, t i).countable :=
by { haveI := λ a, (ht a).to_subtype, rw Union_eq_range_psigma, apply countable_range }

@[simp] lemma countable_Union_iff [countable ι] {s : ι → set α} :
  (⋃ i, s i).countable ↔ ∀ i, (s i).countable :=
⟨λ h i, h.subset $ subset_Union _ _, countable_Union⟩

lemma countable.bUnion
  {s : set α} {t : Π x ∈ s, set β} (hs : s.countable) (ht : ∀a∈s, (t a ‹_›).countable) :
  (⋃a∈s, t a ‹_›).countable :=
begin
  rw bUnion_eq_Union,
  haveI := hs.to_subtype,
  exact countable_Union (λ x, ht x x.2)
end

lemma countable.sUnion {s : set (set α)} (hs : s.countable) (h : ∀a∈s, (a : _).countable) :
  (⋃₀ s).countable :=
by rw sUnion_eq_bUnion; exact hs.bUnion h

@[simp] lemma countable_union {s t : set α} : (s ∪ t).countable ↔ s.countable ∧ t.countable :=
by rw [union_eq_Union, countable_Union_iff, bool.forall_bool, cond, cond, and.comm]

lemma countable.union {s t : set α} (hs : s.countable) (ht : t.countable) :
  (s ∪ t).countable :=
countable_union.2 ⟨hs, ht⟩

@[simp] lemma countable_insert {s : set α} {a : α} : (insert a s).countable ↔ s.countable :=
by simp [insert_eq]

lemma countable.insert {s : set α} (hs : s.countable) (a : α) : (insert a s).countable :=
countable_insert.2 hs

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
    { rcases hSc.exists_eq_range hne with ⟨s, rfl⟩,
      exact ⟨λ n, s n, λ n, hps _ (mem_range_self n), hS⟩ } }
end

lemma exists_seq_cover_iff_countable {p : set α → Prop} (h : ∃ s, p s) :
  (∃ s : ℕ → set α, (∀ n, p (s n)) ∧ (⋃ n, s n) = univ) ↔
    ∃ S : set (set α), S.countable ∧ (∀ s ∈ S, p s) ∧ ⋃₀ S = univ :=
exists_seq_supr_eq_top_iff_countable h

lemma countable_of_injective_of_countable_image {s : set α} {f : α → β}
  (hf : inj_on f s) (hs : (f '' s).countable) : s.countable :=
let ⟨g, hg⟩ := countable_iff_exists_inj_on.1 hs in
countable_iff_exists_inj_on.2 ⟨g ∘ f, hg.comp hf (maps_to_image _ _)⟩

lemma countable_Union_Prop {p : Prop} {t : p → set β} (ht : ∀h:p, (t h).countable) :
  (⋃h:p, t h).countable :=
by by_cases p; simp [h, ht]

lemma finite.countable {s : set α} (hs : s.finite) : s.countable :=
let ⟨h⟩ := hs in @finite.countable _ h.finite

@[nontriviality] lemma countable.of_subsingleton [subsingleton α] (s : set α) :
  s.countable :=
subsingleton_of_subsingleton.countable

lemma countable_is_top (α : Type*) [partial_order α] : {x : α | is_top x}.countable :=
(finite_is_top α).countable

lemma countable_is_bot (α : Type*) [partial_order α] : {x : α | is_bot x}.countable :=
(finite_is_bot α).countable

/-- The set of finite subsets of a countable set is countable. -/
lemma countable_set_of_finite_subset {s : set α} (hs : s.countable) :
  {t | set.finite t ∧ t ⊆ s}.countable :=
begin
  haveI := hs.to_encodable,
  refine countable.subset (countable_range
    (λ t : finset s, {a | ∃ h:a ∈ s, subtype.mk a h ∈ t})) _,
  rintro t ⟨⟨ht⟩, ts⟩, resetI,
  refine ⟨finset.univ.map (embedding_of_subset _ _ ts),
    set.ext $ λ a, _⟩,
  suffices : a ∈ s ∧ a ∈ t ↔ a ∈ t, by simpa,
  exact ⟨and.right, λ h, ⟨ts h, h⟩⟩
end

lemma countable_univ_pi {π : α → Type*} [finite α] {s : Π a, set (π a)} (hs : ∀ a, (s a).countable) :
  (pi univ s).countable :=
by { haveI := λ a, (hs a).to_subtype, exact countable.of_equiv _ (equiv.set.univ_pi s).symm }

lemma countable_pi {π : α → Type*} [finite α] {s : Π a, set (π a)} (hs : ∀ a, (s a).countable) :
  {f : Π a, π a | ∀ a, f a ∈ s a}.countable :=
by simpa only [← mem_univ_pi, set_of_mem_eq] using countable_univ_pi hs

protected lemma countable.prod {s : set α} {t : set β} (hs : s.countable) (ht : t.countable) :
  set.countable (s ×ˢ t) :=
begin
  haveI : countable s := hs.to_subtype,
  haveI : countable t := ht.to_subtype,
  exact countable.of_equiv _  (equiv.set.prod _ _).symm
end

lemma countable.image2 {s : set α} {t : set β} (hs : s.countable) (ht : t.countable)
  (f : α → β → γ) : (image2 f s t).countable :=
by { rw ← image_prod, exact (hs.prod ht).image _ }

end set

lemma finset.countable_to_set (s : finset α) : set.countable (↑s : set α) :=
s.finite_to_set.countable

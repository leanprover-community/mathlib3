/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import data.set.finite
import logic.equiv.list

/-!
# Countable sets
-/
noncomputable theory

open function set encodable

open classical (hiding some)
open_locale classical
universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

namespace set

/-- A set is countable if there exists an encoding of the set into the natural numbers.
An encoding is an injection with a partial inverse, which can be viewed as a
constructive analogue of countability. (For the most part, theorems about
`countable` will be classical and `encodable` will be constructive.)
-/
protected def countable (s : set α) : Prop := nonempty (encodable s)

protected lemma countable_iff_exists_injective {s : set α} :
  s.countable ↔ ∃f:s → ℕ, injective f :=
⟨λ ⟨h⟩, by exactI ⟨encode, encode_injective⟩,
 λ ⟨f, h⟩, ⟨⟨f, partial_inv f, partial_inv_left h⟩⟩⟩

/-- A set `s : set α` is countable if and only if there exists a function `α → ℕ` injective
on `s`. -/
lemma countable_iff_exists_inj_on {s : set α} :
  s.countable ↔ ∃ f : α → ℕ, inj_on f s :=
set.countable_iff_exists_injective.trans
⟨λ ⟨f, hf⟩, ⟨λ a, if h : a ∈ s then f ⟨a, h⟩ else 0,
   λ a as b bs h, congr_arg subtype.val $
     hf $ by simpa [as, bs] using h⟩,
 λ ⟨f, hf⟩, ⟨_, inj_on_iff_injective.1 hf⟩⟩

protected lemma countable_iff_exists_surjective [ne : nonempty α] {s : set α} :
  s.countable ↔ ∃f:ℕ → α, s ⊆ range f :=
⟨λ ⟨h⟩, by inhabit α; exactI ⟨λ n, ((decode s n).map subtype.val).iget,
  λ a as, ⟨encode (⟨a, as⟩ : s), by simp [encodek]⟩⟩,
 λ ⟨f, hf⟩, ⟨⟨
  λ x, inv_fun f x.1,
  λ n, if h : f n ∈ s then some ⟨f n, h⟩ else none,
  λ ⟨x, hx⟩, begin
    have := inv_fun_eq (hf hx), dsimp at this ⊢,
    simp [this, hx]
  end⟩⟩⟩

/--
A non-empty set is countable iff there exists a surjection from the
natural numbers onto the subtype induced by the set.
-/
lemma countable_iff_exists_surjective_to_subtype {s : set α} (hs : s.nonempty) :
  s.countable ↔ ∃ f : ℕ → s, surjective f :=
have inhabited s, from ⟨classical.choice hs.to_subtype⟩,
have s.countable → ∃ f : ℕ → s, surjective f, from assume ⟨h⟩,
  by exactI ⟨λ n, (decode s n).iget, λ a, ⟨encode a, by simp [encodek]⟩⟩,
have (∃ f : ℕ → s, surjective f) → s.countable, from assume ⟨f, fsurj⟩,
  ⟨⟨inv_fun f, option.some ∘ f,
    by intro h; simp [(inv_fun_eq (fsurj h) : f (inv_fun f h) = h)]⟩⟩,
by split; assumption

/-- Convert `set.countable s` to `encodable s` (noncomputable). -/
protected def countable.to_encodable {s : set α} : s.countable → encodable s :=
classical.choice

lemma countable_encodable' (s : set α) [H : encodable s] : s.countable :=
⟨H⟩

lemma countable_encodable [encodable α] (s : set α) : s.countable :=
⟨by apply_instance⟩

/-- If `s : set α` is a nonempty countable set, then there exists a map
`f : ℕ → α` such that `s = range f`. -/
lemma countable.exists_surjective {s : set α} (hc : s.countable) (hs : s.nonempty) :
  ∃f:ℕ → α, s = range f :=
begin
  letI : encodable s := countable.to_encodable hc,
  letI : nonempty s := hs.to_subtype,
  have : (univ : set s).countable := countable_encodable _,
  rcases set.countable_iff_exists_surjective.1 this with ⟨g, hg⟩,
  have : range g = univ := univ_subset_iff.1 hg,
  use coe ∘ g,
  simp only [range_comp, this, image_univ, subtype.range_coe]
end

@[simp] lemma countable_empty : (∅ : set α).countable :=
⟨⟨λ x, x.2.elim, λ n, none, λ x, x.2.elim⟩⟩

@[simp] lemma countable_singleton (a : α) : ({a} : set α).countable :=
⟨of_equiv _ (equiv.set.singleton a)⟩

lemma countable.mono {s₁ s₂ : set α} (h : s₁ ⊆ s₂) : s₂.countable → s₁.countable
| ⟨H⟩ := ⟨@of_inj _ _ H _ (embedding_of_subset _ _ h).2⟩

lemma countable.image {s : set α} (hs : s.countable) (f : α → β) : (f '' s).countable :=
have surjective ((maps_to_image f s).restrict _ _ _), from surjective_maps_to_image_restrict f s,
⟨@encodable.of_inj _ _ hs.to_encodable (surj_inv this) (injective_surj_inv this)⟩

lemma countable_range [encodable α] (f : α → β) : (range f).countable :=
by rw ← image_univ; exact (countable_encodable _).image _

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
    { rcases (countable_iff_exists_surjective_to_subtype hne).1 hSc with ⟨s, hs⟩,
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

lemma countable_Union {t : α → set β} [encodable α] (ht : ∀a, (t a).countable) :
  (⋃a, t a).countable :=
by haveI := (λ a, (ht a).to_encodable);
   rw Union_eq_range_sigma; apply countable_range

lemma countable.bUnion
  {s : set α} {t : Π x ∈ s, set β} (hs : s.countable) (ht : ∀a∈s, (t a ‹_›).countable) :
  (⋃a∈s, t a ‹_›).countable :=
begin
  rw bUnion_eq_Union,
  haveI := hs.to_encodable,
  exact countable_Union (by simpa using ht)
end

lemma countable.sUnion {s : set (set α)} (hs : s.countable) (h : ∀a∈s, (a : _).countable) :
  (⋃₀ s).countable :=
by rw sUnion_eq_bUnion; exact hs.bUnion h

lemma countable_Union_Prop {p : Prop} {t : p → set β} (ht : ∀h:p, (t h).countable) :
  (⋃h:p, t h).countable :=
by by_cases p; simp [h, ht]

lemma countable.union
  {s₁ s₂ : set α} (h₁ : s₁.countable) (h₂ : s₂.countable) : (s₁ ∪ s₂).countable :=
by rw union_eq_Union; exact
countable_Union (bool.forall_bool.2 ⟨h₂, h₁⟩)

@[simp] lemma countable_union {s t : set α} : (s ∪ t).countable ↔ s.countable ∧ t.countable :=
⟨λ h, ⟨h.mono (subset_union_left s t), h.mono (subset_union_right _ _)⟩, λ h, h.1.union h.2⟩

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

lemma countable_pi {π : α → Type*} [fintype α] {s : Πa, set (π a)} (hs : ∀a, (s a).countable) :
  {f : Πa, π a | ∀a, f a ∈ s a}.countable :=
countable.mono
  (show {f : Πa, π a | ∀a, f a ∈ s a} ⊆ range (λf : Πa, s a, λa, (f a).1), from
    assume f hf, ⟨λa, ⟨f a, hf a⟩, funext $ assume a, rfl⟩) $
have trunc (encodable (Π (a : α), s a)), from
  @encodable.fintype_pi α _ _ _ (assume a, (hs a).to_encodable),
trunc.induction_on this $ assume h,
@countable_range _ _ h _

protected lemma countable.prod {s : set α} {t : set β} (hs : s.countable) (ht : t.countable) :
  set.countable (s ×ˢ t) :=
begin
  haveI : encodable s := hs.to_encodable,
  haveI : encodable t := ht.to_encodable,
  exact ⟨of_equiv (s × t) (equiv.set.prod _ _)⟩
end

lemma countable.image2 {s : set α} {t : set β} (hs : s.countable) (ht : t.countable)
  (f : α → β → γ) : (image2 f s t).countable :=
by { rw ← image_prod, exact (hs.prod ht).image _ }

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

end set

lemma finset.countable_to_set (s : finset α) : set.countable (↑s : set α) :=
s.finite_to_set.countable

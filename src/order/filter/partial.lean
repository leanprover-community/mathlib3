/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Extends `tendsto` to relations and partial functions.
-/
import order.filter.basic
import data.pfun

universes u v w
namespace filter
variables {α : Type u} {β : Type v} {γ : Type w}

/-
Relations.
-/

def rmap (r : rel α β) (f : filter α) : filter β :=
{ sets             := r.core ⁻¹' f.sets,
  univ_sets        := by { simp [rel.core], apply univ_mem_sets },
  sets_of_superset := assume s t hs st, mem_sets_of_superset hs $ rel.core_mono _ st,
  inter_sets       := by { simp [set.preimage, rel.core_inter], exact λ s t, inter_mem_sets } }

theorem rmap_sets (r : rel α β) (f : filter α) : (rmap r f).sets = r.core ⁻¹' f.sets := rfl

@[simp]
theorem mem_rmap (r : rel α β) (l : filter α) (s : set β) :
  s ∈ l.rmap r ↔ r.core s ∈ l :=
iff.refl _

@[simp]
theorem rmap_rmap (r : rel α β) (s : rel β γ) (l : filter α) :
  rmap s (rmap r l) = rmap (r.comp s) l :=
filter_eq $
by simp [rmap_sets, set.preimage, rel.core_comp]

@[simp]
lemma rmap_compose (r : rel α β) (s : rel β γ) : rmap s ∘ rmap r = rmap (r.comp s) :=
funext $ rmap_rmap _ _

def rtendsto (r : rel α β) (l₁ : filter α) (l₂ : filter β) := l₁.rmap r ≤ l₂

theorem rtendsto_def (r : rel α β) (l₁ : filter α) (l₂ : filter β) :
  rtendsto r l₁ l₂ ↔ ∀ s ∈ l₂, r.core s ∈ l₁ :=
iff.refl _

def rcomap (r : rel α β) (f : filter β) : filter α :=
{ sets             := rel.image (λ s t, r.core s ⊆ t) f.sets,
  univ_sets        := ⟨set.univ, univ_mem_sets, set.subset_univ _⟩,
  sets_of_superset := assume a b ⟨a', ha', ma'a⟩ ab, ⟨a', ha', set.subset.trans ma'a ab⟩,
  inter_sets       := assume a b ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩,
                        ⟨a' ∩ b', inter_mem_sets ha₁ hb₁,
                          set.subset.trans (by rw rel.core_inter)
                                           (set.inter_subset_inter ha₂ hb₂)⟩ }

theorem rcomap_sets (r : rel α β) (f : filter β) :
  (rcomap r f).sets = rel.image (λ s t, r.core s ⊆ t) f.sets := rfl

@[simp]
theorem rcomap_rcomap (r : rel α β) (s : rel β γ) (l : filter γ) :
  rcomap r (rcomap s l) = rcomap (r.comp s) l :=
filter_eq $
begin
  ext t, simp [rcomap_sets, rel.image, rel.core_comp], split,
  { rintros ⟨u, ⟨v, vsets, hv⟩, h⟩,
    exact ⟨v, vsets, set.subset.trans (rel.core_mono _ hv) h⟩ },
  rintros ⟨t, tsets, ht⟩,
  exact ⟨rel.core s t, ⟨t, tsets, set.subset.refl _⟩, ht⟩
end

@[simp]
lemma rcomap_compose (r : rel α β) (s : rel β γ) : rcomap r ∘ rcomap s = rcomap (r.comp s) :=
funext $ rcomap_rcomap _ _

theorem rtendsto_iff_le_comap (r : rel α β) (l₁ : filter α) (l₂ : filter β) :
  rtendsto r l₁ l₂ ↔ l₁ ≤ l₂.rcomap r :=
begin
  rw rtendsto_def,
  change (∀ (s : set β), s ∈ l₂.sets → rel.core r s ∈ l₁) ↔ l₁ ≤ rcomap r l₂,
  simp [filter.le_def, rcomap, rel.mem_image], split,
  intros h s t tl₂ h',
  { exact mem_sets_of_superset (h t tl₂) h' },
  intros h t tl₂,
  apply h _ t tl₂ (set.subset.refl _),
end

-- Interestingly, there does not seem to be a way to express this relation using a forward map.
-- Given a filter `f` on `α`, we want a filter `f'` on `β` such that `r.preimage s ∈ f` if
-- and only if `s ∈ f'`. But the intersection of two sets satsifying the lhs may be empty.

def rcomap' (r : rel α β) (f : filter β) : filter α :=
{ sets             := rel.image (λ s t, r.preimage s ⊆ t) f.sets,
  univ_sets        := ⟨set.univ, univ_mem_sets, set.subset_univ _⟩,
  sets_of_superset := assume a b ⟨a', ha', ma'a⟩ ab, ⟨a', ha', set.subset.trans ma'a ab⟩,
  inter_sets       := assume a b ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩,
                        ⟨a' ∩ b', inter_mem_sets ha₁ hb₁,
                          set.subset.trans (@rel.preimage_inter _ _ r _ _)
                                           (set.inter_subset_inter ha₂ hb₂)⟩ }

@[simp]
def mem_rcomap' (r : rel α β) (l : filter β) (s : set α) :
  s ∈ l.rcomap' r ↔ ∃ t ∈ l, rel.preimage r t ⊆ s :=
iff.refl _

theorem rcomap'_sets (r : rel α β) (f : filter β) :
  (rcomap' r f).sets = rel.image (λ s t, r.preimage s ⊆ t) f.sets := rfl

@[simp]
theorem rcomap'_rcomap' (r : rel α β) (s : rel β γ) (l : filter γ) :
  rcomap' r (rcomap' s l) = rcomap' (r.comp s) l :=
filter_eq $
begin
  ext t, simp [rcomap'_sets, rel.image, rel.preimage_comp], split,
  { rintros ⟨u, ⟨v, vsets, hv⟩, h⟩,
    exact ⟨v, vsets, set.subset.trans (rel.preimage_mono _ hv) h⟩ },
  rintros ⟨t, tsets, ht⟩,
  exact ⟨rel.preimage s t, ⟨t, tsets, set.subset.refl _⟩, ht⟩
end

@[simp]
lemma rcomap'_compose (r : rel α β) (s : rel β γ) : rcomap' r ∘ rcomap' s = rcomap' (r.comp s) :=
funext $ rcomap'_rcomap' _ _

def rtendsto' (r : rel α β) (l₁ : filter α) (l₂ : filter β) := l₁ ≤ l₂.rcomap' r

theorem rtendsto'_def (r : rel α β) (l₁ : filter α) (l₂ : filter β) :
  rtendsto' r l₁ l₂ ↔ ∀ s ∈ l₂, r.preimage s ∈ l₁ :=
begin
  unfold rtendsto', unfold rcomap', simp [le_def, rel.mem_image], split,
  { intros h s hs, apply (h _ _ hs (set.subset.refl _)) },
  intros h s t ht h', apply mem_sets_of_superset (h t ht) h'
end

theorem tendsto_iff_rtendsto (l₁ : filter α) (l₂ : filter β) (f : α → β) :
  tendsto f l₁ l₂ ↔ rtendsto (function.graph' f) l₁ l₂ :=
by { simp [tendsto_def, function.graph', rtendsto_def, rel.core, set.preimage] }

theorem tendsto_iff_rtendsto' (l₁ : filter α) (l₂ : filter β) (f : α → β) :
  tendsto f l₁ l₂ ↔ rtendsto' (function.graph' f) l₁ l₂ :=
by { simp [tendsto_def, function.graph', rtendsto'_def, rel.preimage_def, set.preimage] }

/-
Partial functions.
-/

def pmap (f : α →. β) (l : filter α) : filter β :=
filter.rmap f.graph' l

@[simp]
def mem_pmap (f : α →. β) (l : filter α) (s : set β) : s ∈ l.pmap f ↔ f.core s ∈ l :=
iff.refl _

def ptendsto (f : α →. β) (l₁ : filter α) (l₂ : filter β) := l₁.pmap f ≤ l₂

theorem ptendsto_def (f : α →. β) (l₁ : filter α) (l₂ : filter β) :
  ptendsto f l₁ l₂ ↔ ∀ s ∈ l₂, f.core s ∈ l₁ :=
iff.refl _

theorem ptendsto_iff_rtendsto (l₁ : filter α) (l₂ : filter β) (f : α →. β) :
  ptendsto f l₁ l₂ ↔ rtendsto f.graph' l₁ l₂ :=
iff.refl _

theorem pmap_res (l : filter α) (s : set α) (f : α → β) :
  pmap (pfun.res f s) l = map f (l ⊓ principal s) :=
filter_eq $
begin
  apply set.ext, intro t, simp [pfun.core_res], split,
  { intro h, constructor, split, { exact h },
    constructor, split, { reflexivity },
    simp [set.inter_distrib_right], apply set.inter_subset_left },
  rintro ⟨t₁, h₁, t₂, h₂, h₃⟩, apply mem_sets_of_superset h₁, rw ← set.inter_subset,
  exact set.subset.trans (set.inter_subset_inter_right _ h₂) h₃
end

theorem tendsto_iff_ptendsto (l₁ : filter α) (l₂ : filter β) (s : set α) (f : α → β) :
  tendsto f (l₁ ⊓ principal s) l₂ ↔ ptendsto (pfun.res f s) l₁ l₂ :=
by simp only [tendsto, ptendsto, pmap_res]

theorem tendsto_iff_ptendsto_univ (l₁ : filter α) (l₂ : filter β) (f : α → β) :
  tendsto f l₁ l₂ ↔ ptendsto (pfun.res f set.univ) l₁ l₂ :=
by { rw ← tendsto_iff_ptendsto, simp [principal_univ] }

def pcomap' (f : α →. β) (l : filter β) : filter α :=
filter.rcomap' f.graph' l

def ptendsto' (f : α →. β) (l₁ : filter α) (l₂ : filter β) := l₁ ≤ l₂.rcomap' f.graph'

theorem ptendsto'_def (f : α →. β) (l₁ : filter α) (l₂ : filter β) :
  ptendsto' f l₁ l₂ ↔ ∀ s ∈ l₂, f.preimage s ∈ l₁ :=
rtendsto'_def _ _ _

theorem ptendsto_of_ptendsto' {f : α →. β} {l₁ : filter α} {l₂ : filter β} :
  ptendsto' f l₁ l₂ → ptendsto f l₁ l₂ :=
begin
  rw [ptendsto_def, ptendsto'_def],
  assume h s sl₂,
  exacts mem_sets_of_superset (h s sl₂) (pfun.preimage_subset_core _ _),
end

theorem ptendsto'_of_ptendsto {f : α →. β} {l₁ : filter α} {l₂ : filter β} (h : f.dom ∈ l₁) :
  ptendsto f l₁ l₂ → ptendsto' f l₁ l₂ :=
begin
  rw [ptendsto_def, ptendsto'_def],
  assume h' s sl₂,
  rw pfun.preimage_eq,
  show pfun.core f s ∩ pfun.dom f ∈ l₁,
  exact inter_mem_sets (h' s sl₂) h
end

end filter

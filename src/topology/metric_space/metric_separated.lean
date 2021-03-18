/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import topology.metric_space.emetric_space

/-!
# Metric separated pairs of sets

In this file we define the predicate `is_metric_separated`. We say that two sets in an (extended)
metric space are *metric separated* if the (extended) distance between `x ∈ s` and `y ∈ t` is
bounded from below by a positive constant.

This notion is useful, e.g., to define metric outer measures.
-/

open emetric set
noncomputable theory

/-- Two sets in an (extended) metric space are called *metric separated* if the (extended) distance
between `x ∈ s` and `y ∈ t` is bounded from below by a positive constant. -/
def is_metric_separated {X : Type*} [emetric_space X] (s t : set X) :=
∃ r ≠ 0, ∀ (x ∈ s) (y ∈ t), r ≤ edist x y

namespace is_metric_separated

variables {X : Type*} [emetric_space X] {s t : set X} {x y : X}

@[symm] lemma symm (h : is_metric_separated s t) : is_metric_separated t s :=
let ⟨r, r0, hr⟩ := h in ⟨r, r0, λ y hy x hx, edist_comm x y ▸ hr x hx y hy⟩

lemma comm : is_metric_separated s t ↔ is_metric_separated t s := ⟨symm, symm⟩

@[simp] lemma empty_left (s : set X) : is_metric_separated ∅ s :=
⟨1, ennreal.zero_lt_one.ne', λ x, false.elim⟩

@[simp] lemma empty_right (s : set X) : is_metric_separated s ∅ :=
(empty_left s).symm

protected lemma disjoint (h : is_metric_separated s t) : disjoint s t :=
let ⟨r, r0, hr⟩ := h in λ x hx, r0 $ by simpa using hr x hx.1 x hx.2

lemma subset_compl_right (h : is_metric_separated s t) : s ⊆ tᶜ :=
λ x hs ht, h.disjoint ⟨hs, ht⟩

@[mono] lemma mono {s' t'} (hs : s ⊆ s') (ht : t ⊆ t') :
  is_metric_separated s' t' → is_metric_separated s t :=
λ ⟨r, r0, hr⟩, ⟨r, r0, λ x hx y hy, hr x (hs hx) y (ht hy)⟩

lemma mono_left {s'} (h' : is_metric_separated s' t) (hs : s ⊆ s') :
  is_metric_separated s t :=
h'.mono hs subset.rfl

lemma mono_right {t'} (h' : is_metric_separated s t') (ht : t ⊆ t') :
  is_metric_separated s t :=
h'.mono subset.rfl ht

lemma union_left {s'} (h : is_metric_separated s t) (h' : is_metric_separated s' t) :
  is_metric_separated (s ∪ s') t :=
begin
  rcases ⟨h, h'⟩ with ⟨⟨r, r0, hr⟩, ⟨r', r0', hr'⟩⟩,
  refine ⟨min r r', _, λ x hx y hy, hx.elim _ _⟩,
  { rw [← pos_iff_ne_zero] at r0 r0' ⊢,
    exact lt_min r0 r0' },
  { exact λ hx, (min_le_left _ _).trans (hr _ hx _ hy) },
  { exact λ hx, (min_le_right _ _).trans (hr' _ hx _ hy) }
end

@[simp] lemma union_left_iff {s'} :
  is_metric_separated (s ∪ s') t ↔ is_metric_separated s t ∧ is_metric_separated s' t :=
⟨λ h, ⟨h.mono_left (subset_union_left _ _), h.mono_left (subset_union_right _ _)⟩,
  λ h, h.1.union_left h.2⟩

lemma union_right {t'} (h : is_metric_separated s t) (h' : is_metric_separated s t') :
  is_metric_separated s (t ∪ t') :=
(h.symm.union_left h'.symm).symm

@[simp] lemma union_right_iff {t'} :
  is_metric_separated s (t ∪ t') ↔ is_metric_separated s t ∧ is_metric_separated s t' :=
comm.trans $ union_left_iff.trans $ and_congr comm comm

lemma finite_Union_left_iff {ι : Type*} {I : set ι} (hI : finite I) {s : ι → set X} {t : set X} :
  is_metric_separated (⋃ i ∈ I, s i) t ↔ ∀ i ∈ I, is_metric_separated (s i) t :=
begin
  refine finite.induction_on hI (by simp) (λ i I hi _ hI, _),
  rw [bUnion_insert, ball_insert_iff, union_left_iff, hI]
end

alias finite_Union_left_iff ↔ _ is_metric_separated.finite_Union_left

lemma finite_Union_right_iff {ι : Type*} {I : set ι} (hI : finite I) {s : set X} {t : ι → set X} :
  is_metric_separated s (⋃ i ∈ I, t i) ↔ ∀ i ∈ I, is_metric_separated s (t i) :=
by simpa only [@comm _ _ s] using finite_Union_left_iff hI

@[simp] lemma finset_Union_left_iff {ι : Type*} {I : finset ι} {s : ι → set X} {t : set X} :
  is_metric_separated (⋃ i ∈ I, s i) t ↔ ∀ i ∈ I, is_metric_separated (s i) t :=
finite_Union_left_iff I.finite_to_set

alias finset_Union_left_iff ↔ _ is_metric_separated.finset_Union_left

@[simp] lemma finset_Union_right_iff {ι : Type*} {I : finset ι} {s : set X} {t : ι → set X} :
  is_metric_separated s (⋃ i ∈ I, t i) ↔ ∀ i ∈ I, is_metric_separated s (t i) :=
finite_Union_right_iff I.finite_to_set

alias finset_Union_right_iff ↔ _ is_metric_separated.finset_Union_right

end is_metric_separated

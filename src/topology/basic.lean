/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/

import order.filter

/-!
# Basic theory of topological spaces.

The main definition is the type class `topological space α` which endows a type `α` with a topology.
Then `set α` gets predicates `is_open`, `is_closed` and functions `interior`, `closure` and
`frontier`. Each point `x` of `α` gets a neighborhood filter `nhds x`, and relative versions
`nhds_within x s` for every set `s` in `α`.

This file also defines locally finite families of subsets of `α`.

For topological spaces `α` and `β`, a function `f : α → β` and a point `a : α`,
`continuous_at f a` means `f` is continuous at `a`, and global continuity is
`continuous f`. There are also relative versions `continuous_within_at` and `continuous_on`
and continuity `pcontinuous` for partially defined functions.

## Implementation notes

Topology in mathlib heavily uses filters (even more than in Bourbaki). See explanations in
`docs/theories/topological_spaces.md`.

## References

*  [N. Bourbaki, *General Topology*][bourbaki1966]
*  [I. M. James, *Topologies and Uniformities*][james1999]

## Tags

topological space, interior, closure, frontier, neighborhood, continuity, continuous function
-/

open set filter lattice classical
open_locale classical

universes u v w

/-- A topology on `α`. -/
structure topological_space (α : Type u) :=
(is_open       : set α → Prop)
(is_open_univ   : is_open univ)
(is_open_inter  : ∀s t, is_open s → is_open t → is_open (s ∩ t))
(is_open_sUnion : ∀s, (∀t∈s, is_open t) → is_open (⋃₀ s))

attribute [class] topological_space

section topological_space

variables {α : Type u} {β : Type v} {ι : Sort w} {a : α} {s s₁ s₂ : set α} {p p₁ p₂ : α → Prop}

@[extensionality]
lemma topological_space_eq : ∀ {f g : topological_space α}, f.is_open = g.is_open → f = g
| ⟨a, _, _, _⟩ ⟨b, _, _, _⟩ rfl := rfl

section
variables [t : topological_space α]
include t

/-- `is_open s` means that `s` is open in the ambient topological space on `α` -/
def is_open (s : set α) : Prop := topological_space.is_open t s

@[simp]
lemma is_open_univ : is_open (univ : set α) := topological_space.is_open_univ t

lemma is_open_inter (h₁ : is_open s₁) (h₂ : is_open s₂) : is_open (s₁ ∩ s₂) :=
topological_space.is_open_inter t s₁ s₂ h₁ h₂

lemma is_open_sUnion {s : set (set α)} (h : ∀t ∈ s, is_open t) : is_open (⋃₀ s) :=
topological_space.is_open_sUnion t s h

end

lemma is_open_fold {s : set α} {t : topological_space α} : t.is_open s = @is_open α t s :=
rfl

variables [topological_space α]

lemma is_open_Union {f : ι → set α} (h : ∀i, is_open (f i)) : is_open (⋃i, f i) :=
is_open_sUnion $ by rintro _ ⟨i, rfl⟩; exact h i

lemma is_open_bUnion {s : set β} {f : β → set α} (h : ∀i∈s, is_open (f i)) :
  is_open (⋃i∈s, f i) :=
is_open_Union $ assume i, is_open_Union $ assume hi, h i hi

lemma is_open_union (h₁ : is_open s₁) (h₂ : is_open s₂) : is_open (s₁ ∪ s₂) :=
by rw union_eq_Union; exact is_open_Union (bool.forall_bool.2 ⟨h₂, h₁⟩)

@[simp] lemma is_open_empty : is_open (∅ : set α) :=
by rw ← sUnion_empty; exact is_open_sUnion (assume a, false.elim)

lemma is_open_sInter {s : set (set α)} (hs : finite s) : (∀t ∈ s, is_open t) → is_open (⋂₀ s) :=
finite.induction_on hs (λ _, by rw sInter_empty; exact is_open_univ) $
λ a s has hs ih h, by rw sInter_insert; exact
is_open_inter (h _ $ mem_insert _ _) (ih $ λ t, h t ∘ mem_insert_of_mem _)

lemma is_open_bInter {s : set β} {f : β → set α} (hs : finite s) :
  (∀i∈s, is_open (f i)) → is_open (⋂i∈s, f i) :=
finite.induction_on hs
  (λ _, by rw bInter_empty; exact is_open_univ)
  (λ a s has hs ih h, by rw bInter_insert; exact
    is_open_inter (h a (mem_insert _ _)) (ih (λ i hi, h i (mem_insert_of_mem _ hi))))

lemma is_open_Inter [fintype β] {s : β → set α}
  (h : ∀ i, is_open (s i)) : is_open (⋂ i, s i) :=
suffices is_open (⋂ (i : β) (hi : i ∈ @univ β), s i), by simpa,
is_open_bInter finite_univ (λ i _, h i)

lemma is_open_Inter_prop {p : Prop} {s : p → set α}
  (h : ∀ h : p, is_open (s h)) : is_open (Inter s) :=
by by_cases p; simp *

lemma is_open_const {p : Prop} : is_open {a : α | p} :=
by_cases
  (assume : p, begin simp only [this]; exact is_open_univ end)
  (assume : ¬ p, begin simp only [this]; exact is_open_empty end)

lemma is_open_and : is_open {a | p₁ a} → is_open {a | p₂ a} → is_open {a | p₁ a ∧ p₂ a} :=
is_open_inter

/-- A set is closed if its complement is open -/
def is_closed (s : set α) : Prop := is_open (-s)

@[simp] lemma is_closed_empty : is_closed (∅ : set α) :=
by unfold is_closed; rw compl_empty; exact is_open_univ

@[simp] lemma is_closed_univ : is_closed (univ : set α) :=
by unfold is_closed; rw compl_univ; exact is_open_empty

lemma is_closed_union : is_closed s₁ → is_closed s₂ → is_closed (s₁ ∪ s₂) :=
λ h₁ h₂, by unfold is_closed; rw compl_union; exact is_open_inter h₁ h₂

lemma is_closed_sInter {s : set (set α)} : (∀t ∈ s, is_closed t) → is_closed (⋂₀ s) :=
by simp only [is_closed, compl_sInter, sUnion_image]; exact assume h, is_open_Union $ assume t, is_open_Union $ assume ht, h t ht

lemma is_closed_Inter {f : ι → set α} (h : ∀i, is_closed (f i)) : is_closed (⋂i, f i ) :=
is_closed_sInter $ assume t ⟨i, (heq : f i = t)⟩, heq ▸ h i

@[simp] lemma is_open_compl_iff {s : set α} : is_open (-s) ↔ is_closed s := iff.rfl

@[simp] lemma is_closed_compl_iff {s : set α} : is_closed (-s) ↔ is_open s :=
by rw [←is_open_compl_iff, compl_compl]

lemma is_open_diff {s t : set α} (h₁ : is_open s) (h₂ : is_closed t) : is_open (s \ t) :=
is_open_inter h₁ $ is_open_compl_iff.mpr h₂

lemma is_closed_inter (h₁ : is_closed s₁) (h₂ : is_closed s₂) : is_closed (s₁ ∩ s₂) :=
by rw [is_closed, compl_inter]; exact is_open_union h₁ h₂

lemma is_closed_bUnion {s : set β} {f : β → set α} (hs : finite s) :
  (∀i∈s, is_closed (f i)) → is_closed (⋃i∈s, f i) :=
finite.induction_on hs
  (λ _, by rw bUnion_empty; exact is_closed_empty)
  (λ a s has hs ih h, by rw bUnion_insert; exact
    is_closed_union (h a (mem_insert _ _)) (ih (λ i hi, h i (mem_insert_of_mem _ hi))))

lemma is_closed_Union [fintype β] {s : β → set α}
  (h : ∀ i, is_closed (s i)) : is_closed (Union s) :=
suffices is_closed (⋃ (i : β) (hi : i ∈ @univ β), s i),
  by convert this; simp [set.ext_iff],
is_closed_bUnion finite_univ (λ i _, h i)

lemma is_closed_Union_prop {p : Prop} {s : p → set α}
  (h : ∀ h : p, is_closed (s h)) : is_closed (Union s) :=
by by_cases p; simp *

lemma is_closed_imp {p q : α → Prop} (hp : is_open {x | p x})
  (hq : is_closed {x | q x}) : is_closed {x | p x → q x} :=
have {x | p x → q x} = (- {x | p x}) ∪ {x | q x}, from set.ext $ λ x, imp_iff_not_or,
by rw [this]; exact is_closed_union (is_closed_compl_iff.mpr hp) hq

lemma is_open_neg : is_closed {a | p a} → is_open {a | ¬ p a} :=
is_open_compl_iff.mpr

/-- The interior of a set `s` is the largest open subset of `s`. -/
def interior (s : set α) : set α := ⋃₀ {t | is_open t ∧ t ⊆ s}

lemma mem_interior {s : set α} {x : α} :
  x ∈ interior s ↔ ∃ t ⊆ s, is_open t ∧ x ∈ t :=
by simp only [interior, mem_set_of_eq, exists_prop, and_assoc, and.left_comm]

@[simp] lemma is_open_interior {s : set α} : is_open (interior s) :=
is_open_sUnion $ assume t ⟨h₁, h₂⟩, h₁

lemma interior_subset {s : set α} : interior s ⊆ s :=
sUnion_subset $ assume t ⟨h₁, h₂⟩, h₂

lemma interior_maximal {s t : set α} (h₁ : t ⊆ s) (h₂ : is_open t) : t ⊆ interior s :=
subset_sUnion_of_mem ⟨h₂, h₁⟩

lemma interior_eq_of_open {s : set α} (h : is_open s) : interior s = s :=
subset.antisymm interior_subset (interior_maximal (subset.refl s) h)

lemma interior_eq_iff_open {s : set α} : interior s = s ↔ is_open s :=
⟨assume h, h ▸ is_open_interior, interior_eq_of_open⟩

lemma subset_interior_iff_open {s : set α} : s ⊆ interior s ↔ is_open s :=
by simp only [interior_eq_iff_open.symm, subset.antisymm_iff, interior_subset, true_and]

lemma subset_interior_iff_subset_of_open {s t : set α} (h₁ : is_open s) :
  s ⊆ interior t ↔ s ⊆ t :=
⟨assume h, subset.trans h interior_subset, assume h₂, interior_maximal h₂ h₁⟩

lemma interior_mono {s t : set α} (h : s ⊆ t) : interior s ⊆ interior t :=
interior_maximal (subset.trans interior_subset h) is_open_interior

@[simp] lemma interior_empty : interior (∅ : set α) = ∅ :=
interior_eq_of_open is_open_empty

@[simp] lemma interior_univ : interior (univ : set α) = univ :=
interior_eq_of_open is_open_univ

@[simp] lemma interior_interior {s : set α} : interior (interior s) = interior s :=
interior_eq_of_open is_open_interior

@[simp] lemma interior_inter {s t : set α} : interior (s ∩ t) = interior s ∩ interior t :=
subset.antisymm
  (subset_inter (interior_mono $ inter_subset_left s t) (interior_mono $ inter_subset_right s t))
  (interior_maximal (inter_subset_inter interior_subset interior_subset) $ is_open_inter is_open_interior is_open_interior)

lemma interior_union_is_closed_of_interior_empty {s t : set α} (h₁ : is_closed s) (h₂ : interior t = ∅) :
  interior (s ∪ t) = interior s :=
have interior (s ∪ t) ⊆ s, from
  assume x ⟨u, ⟨(hu₁ : is_open u), (hu₂ : u ⊆ s ∪ t)⟩, (hx₁ : x ∈ u)⟩,
  classical.by_contradiction $ assume hx₂ : x ∉ s,
    have u \ s ⊆ t,
      from assume x ⟨h₁, h₂⟩, or.resolve_left (hu₂ h₁) h₂,
    have u \ s ⊆ interior t,
      by rwa subset_interior_iff_subset_of_open (is_open_diff hu₁ h₁),
    have u \ s ⊆ ∅,
      by rwa h₂ at this,
    this ⟨hx₁, hx₂⟩,
subset.antisymm
  (interior_maximal this is_open_interior)
  (interior_mono $ subset_union_left _ _)

lemma is_open_iff_forall_mem_open : is_open s ↔ ∀ x ∈ s, ∃ t ⊆ s, is_open t ∧ x ∈ t :=
by rw ← subset_interior_iff_open; simp only [subset_def, mem_interior]

/-- The closure of `s` is the smallest closed set containing `s`. -/
def closure (s : set α) : set α := ⋂₀ {t | is_closed t ∧ s ⊆ t}

@[simp] lemma is_closed_closure {s : set α} : is_closed (closure s) :=
is_closed_sInter $ assume t ⟨h₁, h₂⟩, h₁

lemma subset_closure {s : set α} : s ⊆ closure s :=
subset_sInter $ assume t ⟨h₁, h₂⟩, h₂

lemma closure_minimal {s t : set α} (h₁ : s ⊆ t) (h₂ : is_closed t) : closure s ⊆ t :=
sInter_subset_of_mem ⟨h₂, h₁⟩

lemma closure_eq_of_is_closed {s : set α} (h : is_closed s) : closure s = s :=
subset.antisymm (closure_minimal (subset.refl s) h) subset_closure

lemma closure_eq_iff_is_closed {s : set α} : closure s = s ↔ is_closed s :=
⟨assume h, h ▸ is_closed_closure, closure_eq_of_is_closed⟩

lemma closure_subset_iff_subset_of_is_closed {s t : set α} (h₁ : is_closed t) :
  closure s ⊆ t ↔ s ⊆ t :=
⟨subset.trans subset_closure, assume h, closure_minimal h h₁⟩

lemma closure_mono {s t : set α} (h : s ⊆ t) : closure s ⊆ closure t :=
closure_minimal (subset.trans h subset_closure) is_closed_closure

lemma is_closed_of_closure_subset {s : set α} (h : closure s ⊆ s) : is_closed s :=
by rw subset.antisymm subset_closure h; exact is_closed_closure

@[simp] lemma closure_empty : closure (∅ : set α) = ∅ :=
closure_eq_of_is_closed is_closed_empty

lemma closure_empty_iff (s : set α) : closure s = ∅ ↔ s = ∅ :=
begin
  split; intro h,
  { rw set.eq_empty_iff_forall_not_mem,
    intros x H,
    simpa only [h] using subset_closure H },
  { exact (eq.symm h) ▸ closure_empty },
end

@[simp] lemma closure_univ : closure (univ : set α) = univ :=
closure_eq_of_is_closed is_closed_univ

@[simp] lemma closure_closure {s : set α} : closure (closure s) = closure s :=
closure_eq_of_is_closed is_closed_closure

@[simp] lemma closure_union {s t : set α} : closure (s ∪ t) = closure s ∪ closure t :=
subset.antisymm
  (closure_minimal (union_subset_union subset_closure subset_closure) $ is_closed_union is_closed_closure is_closed_closure)
  (union_subset (closure_mono $ subset_union_left _ _) (closure_mono $ subset_union_right _ _))

lemma interior_subset_closure {s : set α} : interior s ⊆ closure s :=
subset.trans interior_subset subset_closure

lemma closure_eq_compl_interior_compl {s : set α} : closure s = - interior (- s) :=
begin
  unfold interior closure is_closed,
  rw [compl_sUnion, compl_image_set_of],
  simp only [compl_subset_compl]
end

@[simp] lemma interior_compl {s : set α} : interior (- s) = - closure s :=
by simp [closure_eq_compl_interior_compl]

@[simp] lemma closure_compl {s : set α} : closure (- s) = - interior s :=
by simp [closure_eq_compl_interior_compl]

theorem mem_closure_iff {s : set α} {a : α} : a ∈ closure s ↔ ∀ o, is_open o → a ∈ o → o ∩ s ≠ ∅ :=
⟨λ h o oo ao os,
  have s ⊆ -o, from λ x xs xo, @ne_empty_of_mem α (o∩s) x ⟨xo, xs⟩ os,
  closure_minimal this (is_closed_compl_iff.2 oo) h ao,
λ H c ⟨h₁, h₂⟩, classical.by_contradiction $ λ nc,
  let ⟨x, hc, hs⟩ := exists_mem_of_ne_empty (H _ h₁ nc) in hc (h₂ hs)⟩

lemma dense_iff_inter_open {s : set α} : closure s = univ ↔ ∀ U, is_open U → U ≠ ∅ → U ∩ s ≠ ∅ :=
begin
  split ; intro h,
  { intros U U_op U_ne,
    cases exists_mem_of_ne_empty U_ne with x x_in,
    exact mem_closure_iff.1 (by simp only [h]) U U_op x_in },
  { apply eq_univ_of_forall, intro x,
    rw mem_closure_iff,
    intros U U_op x_in,
    exact h U U_op (ne_empty_of_mem x_in) },
end

lemma dense_of_subset_dense {s₁ s₂ : set α} (h : s₁ ⊆ s₂) (hd : closure s₁ = univ) :
  closure s₂ = univ :=
by { rw [← univ_subset_iff, ← hd], exact closure_mono h }

/-- The frontier of a set is the set of points between the closure and interior. -/
def frontier (s : set α) : set α := closure s \ interior s

lemma frontier_eq_closure_inter_closure {s : set α} :
  frontier s = closure s ∩ closure (- s) :=
by rw [closure_compl, frontier, diff_eq]

@[simp] lemma frontier_compl (s : set α) : frontier (-s) = frontier s :=
by simp only [frontier_eq_closure_inter_closure, lattice.neg_neg, inter_comm]

lemma is_closed_frontier {s : set α} : is_closed (frontier s) :=
by rw frontier_eq_closure_inter_closure; exact is_closed_inter is_closed_closure is_closed_closure

lemma interior_frontier {s : set α} (h : is_closed s) : interior (frontier s) = ∅ :=
begin
  have A : frontier s = s \ interior s, by rw [frontier, closure_eq_of_is_closed h],
  have B : interior (frontier s) ⊆ interior s, by rw A; exact interior_mono (diff_subset _ _),
  have C : interior (frontier s) ⊆ frontier s := interior_subset,
  have : interior (frontier s) ⊆ (interior s) ∩ (s \ interior s) :=
    subset_inter B (by simpa [A] using C),
  rwa [inter_diff_self, subset_empty_iff] at this,
end

/-- neighbourhood filter -/
def nhds (a : α) : filter α := (⨅ s ∈ {s : set α | a ∈ s ∧ is_open s}, principal s)

lemma nhds_def (a : α) : nhds a = (⨅ s ∈ {s : set α | a ∈ s ∧ is_open s}, principal s) := rfl

lemma le_nhds_iff {f a} : f ≤ nhds a ↔ ∀ s : set α, a ∈ s → is_open s → s ∈ f :=
by simp [nhds_def]

lemma nhds_le_of_le {f a} {s : set α} (h : a ∈ s) (o : is_open s) (sf : principal s ≤ f) : nhds a ≤ f :=
by rw nhds_def; exact infi_le_of_le s (infi_le_of_le ⟨h, o⟩ sf)

lemma nhds_sets {a : α} : (nhds a).sets = {s | ∃t⊆s, is_open t ∧ a ∈ t} :=
calc (nhds a).sets = (⋃s∈{s : set α| a ∈ s ∧ is_open s}, (principal s).sets) : infi_sets_eq'
  (assume x ⟨hx₁, hx₂⟩ y ⟨hy₁, hy₂⟩,
    ⟨x ∩ y, ⟨⟨hx₁, hy₁⟩, is_open_inter hx₂ hy₂⟩,
      le_principal_iff.2 (inter_subset_left _ _),
      le_principal_iff.2 (inter_subset_right _ _)⟩)
  ⟨univ, mem_univ _, is_open_univ⟩
  ... = {s | ∃t⊆s, is_open t ∧ a ∈ t} :
    le_antisymm
      (supr_le $ assume i, supr_le $ assume ⟨hi₁, hi₂⟩ t ht, ⟨i, ht, hi₂, hi₁⟩)
      (assume t ⟨i, hi₁, hi₂, hi₃⟩, mem_Union.2 ⟨i, mem_Union.2 ⟨⟨hi₃, hi₂⟩, hi₁⟩⟩)

lemma map_nhds {a : α} {f : α → β} :
  map f (nhds a) = (⨅ s ∈ {s : set α | a ∈ s ∧ is_open s}, principal (image f s)) :=
calc map f (nhds a) = (⨅ s ∈ {s : set α | a ∈ s ∧ is_open s}, map f (principal s)) :
    map_binfi_eq
    (assume x ⟨hx₁, hx₂⟩ y ⟨hy₁, hy₂⟩,
      ⟨x ∩ y, ⟨⟨hx₁, hy₁⟩, is_open_inter hx₂ hy₂⟩,
      le_principal_iff.2 (inter_subset_left _ _),
      le_principal_iff.2 (inter_subset_right _ _)⟩)
    ⟨univ, mem_univ _, is_open_univ⟩
  ... = _ : by simp only [map_principal]

attribute [irreducible] nhds

lemma mem_nhds_sets_iff {a : α} {s : set α} :
 s ∈ nhds a ↔ ∃t⊆s, is_open t ∧ a ∈ t :=
by simp only [nhds_sets, mem_set_of_eq, exists_prop]

lemma mem_of_nhds {a : α} {s : set α} : s ∈ nhds a → a ∈ s :=
λ H, let ⟨t, ht, _, hs⟩ := mem_nhds_sets_iff.1 H in ht hs

lemma mem_nhds_sets {a : α} {s : set α} (hs : is_open s) (ha : a ∈ s) :
 s ∈ nhds a :=
mem_nhds_sets_iff.2 ⟨s, subset.refl _, hs, ha⟩

theorem all_mem_nhds (x : α) (P : set α → Prop) (hP : ∀ s t, s ⊆ t → P s → P t) :
  (∀ s ∈ nhds x, P s) ↔ (∀ s, is_open s → x ∈ s → P s) :=
iff.intro
  (λ h s os xs, h s (mem_nhds_sets os xs))
  (λ h t,
    begin
      change t ∈ (nhds x).sets → P t,
      rw nhds_sets,
      rintros ⟨s, hs, opens, xs⟩,
      exact hP _ _ hs (h s opens xs),
    end)

theorem all_mem_nhds_filter (x : α) (f : set α → set β) (hf : ∀ s t, s ⊆ t → f s ⊆ f t)
    (l : filter β) :
  (∀ s ∈ nhds x, f s ∈ l) ↔ (∀ s, is_open s → x ∈ s → f s ∈ l) :=
all_mem_nhds _ _ (λ s t ssubt h, mem_sets_of_superset h (hf s t ssubt))

theorem rtendsto_nhds {r : rel β α} {l : filter β} {a : α} :
  rtendsto r l (nhds a) ↔ (∀ s, is_open s → a ∈ s → r.core s ∈ l) :=
all_mem_nhds_filter _ _ (λ s t, id) _

theorem rtendsto'_nhds {r : rel β α} {l : filter β} {a : α} :
  rtendsto' r l (nhds a) ↔ (∀ s, is_open s → a ∈ s → r.preimage s ∈ l) :=
by { rw [rtendsto'_def], apply all_mem_nhds_filter, apply rel.preimage_mono }

theorem ptendsto_nhds {f : β →. α} {l : filter β} {a : α} :
  ptendsto f l (nhds a) ↔ (∀ s, is_open s → a ∈ s → f.core s ∈ l) :=
rtendsto_nhds

theorem ptendsto'_nhds {f : β →. α} {l : filter β} {a : α} :
  ptendsto' f l (nhds a) ↔ (∀ s, is_open s → a ∈ s → f.preimage s ∈ l) :=
rtendsto'_nhds

theorem tendsto_nhds {f : β → α} {l : filter β} {a : α} :
  tendsto f l (nhds a) ↔ (∀ s, is_open s → a ∈ s → f ⁻¹' s ∈ l) :=
all_mem_nhds_filter _ _ (λ s t h, preimage_mono h) _

lemma tendsto_const_nhds {a : α} {f : filter β} : tendsto (λb:β, a) f (nhds a) :=
tendsto_nhds.mpr $ assume s hs ha, univ_mem_sets' $ assume _, ha

lemma pure_le_nhds : pure ≤ (nhds : α → filter α) :=
assume a, by rw nhds_def; exact le_infi
  (assume s, le_infi $ assume ⟨h₁, _⟩, principal_mono.mpr $
    singleton_subset_iff.2 h₁)

lemma tendsto_pure_nhds {α : Type*} [topological_space β] (f : α → β) (a : α) :
  tendsto f (pure a) (nhds (f a)) :=
begin
  rw [tendsto, filter.map_pure],
  exact pure_le_nhds (f a)
end

@[simp] lemma nhds_neq_bot {a : α} : nhds a ≠ ⊥ :=
assume : nhds a = ⊥,
have pure a = (⊥ : filter α),
  from lattice.bot_unique $ this ▸ pure_le_nhds a,
pure_neq_bot this

lemma interior_eq_nhds {s : set α} : interior s = {a | nhds a ≤ principal s} :=
set.ext $ λ x, by simp only [mem_interior, le_principal_iff, mem_nhds_sets_iff]; refl

lemma mem_interior_iff_mem_nhds {s : set α} {a : α} :
  a ∈ interior s ↔ s ∈ nhds a :=
by simp only [interior_eq_nhds, le_principal_iff]; refl

lemma is_open_iff_nhds {s : set α} : is_open s ↔ ∀a∈s, nhds a ≤ principal s :=
calc is_open s ↔ s ⊆ interior s : subset_interior_iff_open.symm
  ... ↔ (∀a∈s, nhds a ≤ principal s) : by rw [interior_eq_nhds]; refl

lemma is_open_iff_mem_nhds {s : set α} : is_open s ↔ ∀a∈s, s ∈ nhds a :=
is_open_iff_nhds.trans $ forall_congr $ λ _, imp_congr_right $ λ _, le_principal_iff

lemma closure_eq_nhds {s : set α} : closure s = {a | nhds a ⊓ principal s ≠ ⊥} :=
calc closure s = - interior (- s) : closure_eq_compl_interior_compl
  ... = {a | ¬ nhds a ≤ principal (-s)} : by rw [interior_eq_nhds]; refl
  ... = {a | nhds a ⊓ principal s ≠ ⊥} : set.ext $ assume a, not_congr
    (inf_eq_bot_iff_le_compl
      (show principal s ⊔ principal (-s) = ⊤, by simp only [sup_principal, union_compl_self, principal_univ])
      (by simp only [inf_principal, inter_compl_self, principal_empty])).symm

theorem mem_closure_iff_nhds {s : set α} {a : α} : a ∈ closure s ↔ ∀ t ∈ nhds a, t ∩ s ≠ ∅ :=
mem_closure_iff.trans
⟨λ H t ht, subset_ne_empty
  (inter_subset_inter_left _ interior_subset)
  (H _ is_open_interior (mem_interior_iff_mem_nhds.2 ht)),
 λ H o oo ao, H _ (mem_nhds_sets oo ao)⟩

/-- `x` belongs to the closure of `s` if and only if some ultrafilter
  supported on `s` converges to `x`. -/
lemma mem_closure_iff_ultrafilter {s : set α} {x : α} :
  x ∈ closure s ↔ ∃ (u : ultrafilter α), s ∈ u.val ∧ u.val ≤ nhds x :=
begin
  rw closure_eq_nhds, change nhds x ⊓ principal s ≠ ⊥ ↔ _, symmetry,
  convert exists_ultrafilter_iff _, ext u,
  rw [←le_principal_iff, inf_comm, le_inf_iff]
end

lemma is_closed_iff_nhds {s : set α} : is_closed s ↔ ∀a, nhds a ⊓ principal s ≠ ⊥ → a ∈ s :=
calc is_closed s ↔ closure s = s : by rw [closure_eq_iff_is_closed]
  ... ↔ closure s ⊆ s : ⟨assume h, by rw h, assume h, subset.antisymm h subset_closure⟩
  ... ↔ (∀a, nhds a ⊓ principal s ≠ ⊥ → a ∈ s) : by rw [closure_eq_nhds]; refl

lemma closure_inter_open {s t : set α} (h : is_open s) : s ∩ closure t ⊆ closure (s ∩ t) :=
assume a ⟨hs, ht⟩,
have s ∈ nhds a, from mem_nhds_sets h hs,
have nhds a ⊓ principal s = nhds a, from inf_of_le_left $ by rwa le_principal_iff,
have nhds a ⊓ principal (s ∩ t) ≠ ⊥,
  from calc nhds a ⊓ principal (s ∩ t) = nhds a ⊓ (principal s ⊓ principal t) : by rw inf_principal
    ... = nhds a ⊓ principal t : by rw [←inf_assoc, this]
    ... ≠ ⊥ : by rw [closure_eq_nhds] at ht; assumption,
by rw [closure_eq_nhds]; assumption

lemma closure_diff {s t : set α} : closure s - closure t ⊆ closure (s - t) :=
calc closure s \ closure t = (- closure t) ∩ closure s : by simp only [diff_eq, inter_comm]
  ... ⊆ closure (- closure t ∩ s) : closure_inter_open $ is_open_compl_iff.mpr $ is_closed_closure
  ... = closure (s \ closure t) : by simp only [diff_eq, inter_comm]
  ... ⊆ closure (s \ t) : closure_mono $ diff_subset_diff (subset.refl s) subset_closure

lemma mem_of_closed_of_tendsto {f : β → α} {b : filter β} {a : α} {s : set α}
  (hb : b ≠ ⊥) (hf : tendsto f b (nhds a)) (hs : is_closed s) (h : f ⁻¹' s ∈ b) : a ∈ s :=
have b.map f ≤ nhds a ⊓ principal s,
  from le_trans (le_inf (le_refl _) (le_principal_iff.mpr h)) (inf_le_inf hf (le_refl _)),
is_closed_iff_nhds.mp hs a $ neq_bot_of_le_neq_bot (map_ne_bot hb) this

lemma mem_of_closed_of_tendsto' {f : β → α} {x : filter β} {a : α} {s : set α}
  (hf : tendsto f x (nhds a)) (hs : is_closed s) (h : x ⊓ principal (f ⁻¹' s) ≠ ⊥) : a ∈ s :=
is_closed_iff_nhds.mp hs _ $ neq_bot_of_le_neq_bot (@map_ne_bot _ _ _ f h) $
  le_inf (le_trans (map_mono $ inf_le_left) hf) $
    le_trans (map_mono $ inf_le_right_of_le $ by simp only [comap_principal, le_principal_iff]; exact subset.refl _) (@map_comap_le _ _ _ f)

lemma mem_closure_of_tendsto {f : β → α} {b : filter β} {a : α} {s : set α}
  (hb : b ≠ ⊥) (hf : tendsto f b (nhds a)) (h : f ⁻¹' s ∈ b) : a ∈ closure s :=
mem_of_closed_of_tendsto hb hf (is_closed_closure) $
  filter.mem_sets_of_superset h (preimage_mono subset_closure)


section lim
variables [inhabited α]

/-- If `f` is a filter, then `lim f` is a limit of the filter, if it exists. -/
noncomputable def lim (f : filter α) : α := epsilon $ λa, f ≤ nhds a

lemma lim_spec {f : filter α} (h : ∃a, f ≤ nhds a) : f ≤ nhds (lim f) := epsilon_spec h
end lim

/-- The "neighborhood within" filter. Elements of `nhds_within a s` are sets containing the
intersection of `s` and a neighborhood of `a`. -/
def nhds_within (a : α) (s : set α) : filter α := nhds a ⊓ principal s

theorem nhds_within_eq (a : α) (s : set α) :
  nhds_within a s = ⨅ t ∈ {t : set α | a ∈ t ∧ is_open t}, principal (t ∩ s) :=
have set.univ ∈ {s : set α | a ∈ s ∧ is_open s}, from ⟨set.mem_univ _, is_open_univ⟩,
begin
  rw [nhds_within, nhds, lattice.binfi_inf]; try { exact this },
  simp only [inf_principal]
end

theorem nhds_within_univ (a : α) : nhds_within a set.univ = nhds a :=
by rw [nhds_within, principal_univ, lattice.inf_top_eq]

theorem mem_nhds_within (t : set α) (a : α) (s : set α) :
  t ∈ nhds_within a s ↔ ∃ u, is_open u ∧ a ∈ u ∧ u ∩ s ⊆ t  :=
begin
  rw [nhds_within, mem_inf_principal, mem_nhds_sets_iff], split,
  { rintros ⟨u, hu, openu, au⟩,
    exact ⟨u, openu, au, λ x ⟨xu, xs⟩, hu xu xs⟩ },
  rintros ⟨u, openu, au, hu⟩,
  exact ⟨u, λ x xu xs, hu ⟨xu, xs⟩, openu, au⟩
end

theorem self_mem_nhds_within {a : α} {s : set α} : s ∈ nhds_within a s :=
begin
  rw [nhds_within, mem_inf_principal],
  simp only [imp_self],
  exact univ_mem_sets
end

theorem inter_mem_nhds_within (s : set α) {t : set α} {a : α} (h : t ∈ nhds a) :
  s ∩ t ∈ nhds_within a s :=
inter_mem_sets (mem_inf_sets_of_right (mem_principal_self s)) (mem_inf_sets_of_left h)

theorem nhds_within_mono (a : α) {s t : set α} (h : s ⊆ t) : nhds_within a s ≤ nhds_within a t :=
lattice.inf_le_inf (le_refl _) (principal_mono.mpr h)

theorem nhds_within_restrict'' {a : α} (s : set α) {t : set α} (h : t ∈ nhds_within a s) :
  nhds_within a s = nhds_within a (s ∩ t) :=
le_antisymm
  (lattice.le_inf lattice.inf_le_left (le_principal_iff.mpr (inter_mem_sets self_mem_nhds_within h)))
  (lattice.inf_le_inf (le_refl _) (principal_mono.mpr (set.inter_subset_left _ _)))

theorem nhds_within_restrict' {a : α} (s : set α) {t : set α} (h : t ∈ nhds a) :
  nhds_within a s = nhds_within a (s ∩ t) :=
nhds_within_restrict'' s $ mem_inf_sets_of_left h

theorem nhds_within_restrict {a : α} (s : set α) {t : set α} (h₀ : a ∈ t) (h₁ : is_open t) :
  nhds_within a s = nhds_within a (s ∩ t) :=
nhds_within_restrict' s (mem_nhds_sets h₁ h₀)

theorem nhds_within_le_of_mem {a : α} {s t : set α} (h : s ∈ nhds_within a t) :
  nhds_within a t ≤ nhds_within a s :=
begin
  rcases (mem_nhds_within _ _ _).1 h with ⟨u, u_open, au, uts⟩,
  have : nhds_within a t = nhds_within a (t ∩ u) := nhds_within_restrict _ au u_open,
  rw [this, inter_comm],
  exact nhds_within_mono _ uts
end

theorem nhds_within_eq_nhds_within {a : α} {s t u : set α}
    (h₀ : a ∈ s) (h₁ : is_open s) (h₂ : t ∩ s = u ∩ s) :
  nhds_within a t = nhds_within a u :=
by rw [nhds_within_restrict t h₀ h₁, nhds_within_restrict u h₀ h₁, h₂]

theorem nhds_within_eq_of_open {a : α} {s : set α} (h₀ : a ∈ s) (h₁ : is_open s) :
  nhds_within a s = nhds a :=
by rw [←nhds_within_univ]; apply nhds_within_eq_nhds_within h₀ h₁;
     rw [set.univ_inter, set.inter_self]

@[simp] theorem nhds_within_empty (a : α) : nhds_within a {} = ⊥ :=
by rw [nhds_within, principal_empty, lattice.inf_bot_eq]

theorem nhds_within_union (a : α) (s t : set α) :
  nhds_within a (s ∪ t) = nhds_within a s ⊔ nhds_within a t :=
by unfold nhds_within; rw [←lattice.inf_sup_left, sup_principal]

theorem nhds_within_inter (a : α) (s t : set α) :
  nhds_within a (s ∩ t) = nhds_within a s ⊓ nhds_within a t :=
by unfold nhds_within; rw [lattice.inf_left_comm, lattice.inf_assoc, inf_principal,
                             ←lattice.inf_assoc, lattice.inf_idem]

theorem nhds_within_inter' (a : α) (s t : set α) :
  nhds_within a (s ∩ t) = (nhds_within a s) ⊓ principal t :=
by { unfold nhds_within, rw [←inf_principal, lattice.inf_assoc] }

theorem tendsto_if_nhds_within {f g : α → β} {p : α → Prop} [decidable_pred p]
    {a : α} {s : set α} {l : filter β}
    (h₀ : tendsto f (nhds_within a (s ∩ p)) l)
    (h₁ : tendsto g (nhds_within a (s ∩ {x | ¬ p x})) l) :
  tendsto (λ x, if p x then f x else g x) (nhds_within a s) l :=
by apply tendsto_if; rw [←nhds_within_inter']; assumption

lemma map_nhds_within (f : α → β) (a : α) (s : set α) :
  map f (nhds_within a s) =
    ⨅ t ∈ {t : set α | a ∈ t ∧ is_open t}, principal (set.image f (t ∩ s)) :=
have h₀ : directed_on ((λ (i : set α), principal (i ∩ s)) ⁻¹'o ge)
        {x : set α | x ∈ {t : set α | a ∈ t ∧ is_open t}}, from
  assume x ⟨ax, openx⟩ y ⟨ay, openy⟩,
  ⟨x ∩ y, ⟨⟨ax, ay⟩, is_open_inter openx openy⟩,
    le_principal_iff.mpr (set.inter_subset_inter_left _ (set.inter_subset_left _ _)),
    le_principal_iff.mpr (set.inter_subset_inter_left _ (set.inter_subset_right _ _))⟩,
have h₁ : ∃ (i : set α), i ∈ {t : set α | a ∈ t ∧ is_open t},
  from ⟨set.univ, set.mem_univ _, is_open_univ⟩,
by { rw [nhds_within_eq, map_binfi_eq h₀ h₁], simp only [map_principal] }

theorem tendsto_nhds_within_mono_left {f : α → β} {a : α}
    {s t : set α} {l : filter β} (hst : s ⊆ t) (h : tendsto f (nhds_within a t) l) :
  tendsto f (nhds_within a s) l :=
tendsto_le_left (nhds_within_mono a hst) h

theorem tendsto_nhds_within_mono_right {f : β → α} {l : filter β}
    {a : α} {s t : set α} (hst : s ⊆ t) (h : tendsto f l (nhds_within a s)) :
  tendsto f l (nhds_within a t) :=
tendsto_le_right (nhds_within_mono a hst) h

theorem tendsto_nhds_within_of_tendsto_nhds {f : α → β} {a : α}
    {s : set α} {l : filter β} (h : tendsto f (nhds a) l) :
  tendsto f (nhds_within a s) l :=
by rw [←nhds_within_univ] at h; exact tendsto_nhds_within_mono_left (set.subset_univ _) h


/- locally finite family [General Topology (Bourbaki, 1995)] -/
section locally_finite

/-- A family of sets in `set α` is locally finite if at every point `x:α`,
  there is a neighborhood of `x` which meets only finitely many sets in the family -/
def locally_finite (f : β → set α) :=
∀x:α, ∃t ∈ nhds x, finite {i | f i ∩ t ≠ ∅ }

lemma locally_finite_of_finite {f : β → set α} (h : finite (univ : set β)) : locally_finite f :=
assume x, ⟨univ, univ_mem_sets, finite_subset h $ subset_univ _⟩

lemma locally_finite_subset
  {f₁ f₂ : β → set α} (hf₂ : locally_finite f₂) (hf : ∀b, f₁ b ⊆ f₂ b) : locally_finite f₁ :=
assume a,
let ⟨t, ht₁, ht₂⟩ := hf₂ a in
⟨t, ht₁, finite_subset ht₂ $ assume i hi,
  neq_bot_of_le_neq_bot hi $ inter_subset_inter (hf i) $ subset.refl _⟩

lemma is_closed_Union_of_locally_finite {f : β → set α}
  (h₁ : locally_finite f) (h₂ : ∀i, is_closed (f i)) : is_closed (⋃i, f i) :=
is_open_iff_nhds.mpr $ assume a, assume h : a ∉ (⋃i, f i),
  have ∀i, a ∈ -f i,
    from assume i hi, h $ mem_Union.2 ⟨i, hi⟩,
  have ∀i, - f i ∈ (nhds a).sets,
    by rw [nhds_sets]; exact assume i, ⟨- f i, subset.refl _, h₂ i, this i⟩,
  let ⟨t, h_sets, (h_fin : finite {i | f i ∩ t ≠ ∅ })⟩ := h₁ a in

  calc nhds a ≤ principal (t ∩ (⋂ i∈{i | f i ∩ t ≠ ∅ }, - f i)) :
  begin
    rw [le_principal_iff],
    apply @filter.inter_mem_sets _ (nhds a) _ _ h_sets,
    apply @filter.Inter_mem_sets _ (nhds a) _ _ _ h_fin,
    exact assume i h, this i
  end
  ... ≤ principal (- ⋃i, f i) :
  begin
    simp only [principal_mono, subset_def, mem_compl_eq, mem_inter_eq,
      mem_Inter, mem_set_of_eq, mem_Union, and_imp, not_exists,
      not_eq_empty_iff_exists, exists_imp_distrib, (≠)],
    exact assume x xt ht i xfi, ht i x xfi xt xfi
  end

end locally_finite

end topological_space

section continuous
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
variables [topological_space α] [topological_space β] [topological_space γ]

/-- A function between topological spaces is continuous if the preimage
  of every open set is open. -/
def continuous (f : α → β) := ∀s, is_open s → is_open (f ⁻¹' s)

/-- A function between topological spaces is continuous at a point `x₀`
if `f x` tends to `f x₀` when `x` tends to `x₀`. -/
def continuous_at (f : α → β) (x : α) := tendsto f (nhds x) (nhds (f x))

/-- A function between topological spaces is continuous at a point `x₀` within a subset `s`
if `f x` tends to `f x₀` when `x` tends to `x₀` while staying within `s`. -/
def continuous_within_at (f : α → β) (s : set α) (x : α) : Prop :=
tendsto f (nhds_within x s) (nhds (f x))

/-- A function between topological spaces is continuous on a subset `s`
when it's continuous at every point of `s` within `s`. -/
def continuous_on (f : α → β) (s : set α) : Prop := ∀ x ∈ s, continuous_within_at f s x

lemma continuous_id : continuous (id : α → α) :=
assume s h, h

lemma continuous.comp {g : β → γ} {f : α → β} (hg : continuous g) (hf : continuous f) :
  continuous (g ∘ f) :=
assume s h, hf _ (hg s h)

lemma continuous.tendsto {f : α → β} (hf : continuous f) (x) :
  tendsto f (nhds x) (nhds (f x)) | s :=
show s ∈ nhds (f x) → s ∈ map f (nhds x),
by simp [nhds_sets]; exact
assume t t_subset t_open fx_in_t,
  ⟨f ⁻¹' t, preimage_mono t_subset, hf t t_open, fx_in_t⟩

lemma continuous_iff_continuous_at {f : α → β} : continuous f ↔ ∀ x, continuous_at f x :=
⟨continuous.tendsto,
  assume hf : ∀x, tendsto f (nhds x) (nhds (f x)),
  assume s, assume hs : is_open s,
  have ∀a, f a ∈ s → s ∈ nhds (f a),
    by simp [nhds_sets]; exact assume a ha, ⟨s, subset.refl s, hs, ha⟩,
  show is_open (f ⁻¹' s),
    by simp [is_open_iff_nhds]; exact assume a ha, hf a (this a ha)⟩

lemma continuous_const {b : β} : continuous (λa:α, b) :=
continuous_iff_continuous_at.mpr $ assume a, tendsto_const_nhds

lemma continuous_iff_is_closed {f : α → β} :
  continuous f ↔ (∀s, is_closed s → is_closed (f ⁻¹' s)) :=
⟨assume hf s hs, hf (-s) hs,
  assume hf s, by rw [←is_closed_compl_iff, ←is_closed_compl_iff]; exact hf _⟩

lemma continuous_at_iff_ultrafilter {f : α → β} (x) : continuous_at f x ↔
  ∀ g, is_ultrafilter g → g ≤ nhds x → g.map f ≤ nhds (f x) :=
tendsto_iff_ultrafilter f (nhds x) (nhds (f x))

lemma continuous_iff_ultrafilter {f : α → β} :
  continuous f ↔ ∀ x g, is_ultrafilter g → g ≤ nhds x → g.map f ≤ nhds (f x) :=
by simp only [continuous_iff_continuous_at, continuous_at_iff_ultrafilter]

lemma continuous_if {p : α → Prop} {f g : α → β} {h : ∀a, decidable (p a)}
  (hp : ∀a∈frontier {a | p a}, f a = g a) (hf : continuous f) (hg : continuous g) :
  continuous (λa, @ite (p a) (h a) β (f a) (g a)) :=
continuous_iff_is_closed.mpr $
assume s hs,
have (λa, ite (p a) (f a) (g a)) ⁻¹' s =
    (closure {a | p a} ∩  f ⁻¹' s) ∪ (closure {a | ¬ p a} ∩ g ⁻¹' s),
  from set.ext $ assume a,
  classical.by_cases
    (assume : a ∈ frontier {a | p a},
      have hac : a ∈ closure {a | p a}, from this.left,
      have hai : a ∈ closure {a | ¬ p a},
        from have a ∈ - interior {a | p a}, from this.right, by rwa [←closure_compl] at this,
      by by_cases p a; simp [h, hp a this, hac, hai, iff_def] {contextual := tt})
    (assume hf : a ∈ - frontier {a | p a},
      classical.by_cases
        (assume : p a,
          have hc : a ∈ closure {a | p a}, from subset_closure this,
          have hnc : a ∉ closure {a | ¬ p a},
            by show a ∉ closure (- {a | p a}); rw [closure_compl]; simpa [frontier, hc] using hf,
          by simp [this, hc, hnc])
        (assume : ¬ p a,
          have hc : a ∈ closure {a | ¬ p a}, from subset_closure this,
          have hnc : a ∉ closure {a | p a},
            begin
              have hc : a ∈ closure (- {a | p a}), from hc,
              simp [closure_compl] at hc,
              simpa [frontier, hc] using hf
            end,
          by simp [this, hc, hnc])),
by rw [this]; exact is_closed_union
  (is_closed_inter is_closed_closure $ continuous_iff_is_closed.mp hf s hs)
  (is_closed_inter is_closed_closure $ continuous_iff_is_closed.mp hg s hs)


/- Continuity and partial functions -/

/-- Continuity of a partial function -/
def pcontinuous (f : α →. β) := ∀ s, is_open s → is_open (f.preimage s)

lemma open_dom_of_pcontinuous {f : α →. β} (h : pcontinuous f) : is_open f.dom :=
by rw [←pfun.preimage_univ]; exact h _ is_open_univ

lemma pcontinuous_iff' {f : α →. β} :
  pcontinuous f ↔ ∀ {x y} (h : y ∈ f x), ptendsto' f (nhds x) (nhds y) :=
begin
  split,
  { intros h x y h',
    rw [ptendsto'_def],
    change ∀ (s : set β), s ∈ (nhds y).sets → pfun.preimage f s ∈ (nhds x).sets,
    rw [nhds_sets, nhds_sets],
    rintros s ⟨t, tsubs, opent, yt⟩,
    exact ⟨f.preimage t, pfun.preimage_mono _ tsubs, h _ opent, ⟨y, yt, h'⟩⟩
  },
  intros hf s os,
  rw is_open_iff_nhds,
  rintros x ⟨y, ys, fxy⟩ t,
  rw [mem_principal_sets],
  assume h : f.preimage s ⊆ t,
  change t ∈ nhds x,
  apply mem_sets_of_superset _ h,
  have h' : ∀ s ∈ nhds y, f.preimage s ∈ nhds x,
  { intros s hs,
     have : ptendsto' f (nhds x) (nhds y) := hf fxy,
     rw ptendsto'_def at this,
     exact this s hs },
  show f.preimage s ∈ nhds x,
  apply h', rw mem_nhds_sets_iff, exact ⟨s, set.subset.refl _, os, ys⟩
end

lemma image_closure_subset_closure_image {f : α → β} {s : set α} (h : continuous f) :
  f '' closure s ⊆ closure (f '' s) :=
have ∀ (a : α), nhds a ⊓ principal s ≠ ⊥ → nhds (f a) ⊓ principal (f '' s) ≠ ⊥,
  from assume a ha,
  have h₁ : ¬ map f (nhds a ⊓ principal s) = ⊥,
    by rwa[map_eq_bot_iff],
  have h₂ : map f (nhds a ⊓ principal s) ≤ nhds (f a) ⊓ principal (f '' s),
    from le_inf
      (le_trans (map_mono inf_le_left) $ by rw [continuous_iff_continuous_at] at h; exact h a)
      (le_trans (map_mono inf_le_right) $ by simp; exact subset.refl _),
  neq_bot_of_le_neq_bot h₁ h₂,
by simp [image_subset_iff, closure_eq_nhds]; assumption

lemma mem_closure {s : set α} {t : set β} {f : α → β} {a : α}
  (hf : continuous f) (ha : a ∈ closure s) (ht : ∀a∈s, f a ∈ t) : f a ∈ closure t :=
subset.trans (image_closure_subset_closure_image hf) (closure_mono $ image_subset_iff.2 ht) $
  (mem_image_of_mem f ha)

end continuous

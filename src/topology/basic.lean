/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
import order.filter.ultrafilter
import order.filter.partial
import order.filter.bases

/-!
# Basic theory of topological spaces.

The main definition is the type class `topological space α` which endows a type `α` with a topology.
Then `set α` gets predicates `is_open`, `is_closed` and functions `interior`, `closure` and
`frontier`. Each point `x` of `α` gets a neighborhood filter `𝓝 x`. A filter `F` on `α` has
`x` as a cluster point if `is_cluster_pt x F : 𝓝 x ⊓ F ≠ ⊥`. A map `f : ι → α` clusters at `x`
along `F : filter ι` if `map_cluster_pt x F f : cluster_pt x (map f F)`. In particular
the notion of cluster point of a sequence `u` is `map_cluster_pt x at_top u`.

This file also defines locally finite families of subsets of `α`.

For topological spaces `α` and `β`, a function `f : α → β` and a point `a : α`,
`continuous_at f a` means `f` is continuous at `a`, and global continuity is
`continuous f`. There is also a version of continuity `pcontinuous` for
partially defined functions.

## Implementation notes

Topology in mathlib heavily uses filters (even more than in Bourbaki). See explanations in
<https://leanprover-community.github.io/theories/topology.html>.

## References

*  [N. Bourbaki, *General Topology*][bourbaki1966]
*  [I. M. James, *Topologies and Uniformities*][james1999]

## Tags

topological space, interior, closure, frontier, neighborhood, continuity, continuous function
-/

open set filter classical
open_locale classical filter

universes u v w

/-!
### Topological spaces
-/

/-- A topology on `α`. -/
@[protect_proj] structure topological_space (α : Type u) :=
(is_open        : set α → Prop)
(is_open_univ   : is_open univ)
(is_open_inter  : ∀s t, is_open s → is_open t → is_open (s ∩ t))
(is_open_sUnion : ∀s, (∀t∈s, is_open t) → is_open (⋃₀ s))

attribute [class] topological_space

/-- A constructor for topologies by specifying the closed sets,
and showing that they satisfy the appropriate conditions. -/
def topological_space.of_closed {α : Type u} (T : set (set α))
  (empty_mem : ∅ ∈ T) (sInter_mem : ∀ A ⊆ T, ⋂₀ A ∈ T) (union_mem : ∀ A B ∈ T, A ∪ B ∈ T) :
  topological_space α :=
{ is_open := λ X, Xᶜ ∈ T,
  is_open_univ := by simp [empty_mem],
  is_open_inter := λ s t hs ht, by simpa [set.compl_inter] using union_mem sᶜ tᶜ hs ht,
  is_open_sUnion := λ s hs,
    by rw set.compl_sUnion; exact sInter_mem (set.compl '' s)
    (λ z ⟨y, hy, hz⟩, by simpa [hz.symm] using hs y hy) }

section topological_space

variables {α : Type u} {β : Type v} {ι : Sort w} {a : α} {s s₁ s₂ : set α} {p p₁ p₂ : α → Prop}

@[ext]
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
def is_closed (s : set α) : Prop := is_open sᶜ

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

@[simp] lemma is_open_compl_iff {s : set α} : is_open sᶜ ↔ is_closed s := iff.rfl

@[simp] lemma is_closed_compl_iff {s : set α} : is_closed sᶜ ↔ is_open s :=
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
have {x | p x → q x} = {x | p x}ᶜ ∪ {x | q x}, from set.ext $ λ x, imp_iff_not_or,
by rw [this]; exact is_closed_union (is_closed_compl_iff.mpr hp) hq

lemma is_open_neg : is_closed {a | p a} → is_open {a | ¬ p a} :=
is_open_compl_iff.mpr

/-!
### Interior of a set
-/

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

/-!
### Closure of a set
-/

/-- The closure of `s` is the smallest closed set containing `s`. -/
def closure (s : set α) : set α := ⋂₀ {t | is_closed t ∧ s ⊆ t}

@[simp] lemma is_closed_closure {s : set α} : is_closed (closure s) :=
is_closed_sInter $ assume t ⟨h₁, h₂⟩, h₁

lemma subset_closure {s : set α} : s ⊆ closure s :=
subset_sInter $ assume t ⟨h₁, h₂⟩, h₂

lemma closure_minimal {s t : set α} (h₁ : s ⊆ t) (h₂ : is_closed t) : closure s ⊆ t :=
sInter_subset_of_mem ⟨h₂, h₁⟩

lemma is_closed.closure_eq {s : set α} (h : is_closed s) : closure s = s :=
subset.antisymm (closure_minimal (subset.refl s) h) subset_closure

lemma is_closed.closure_subset {s : set α} (hs : is_closed s) : closure s ⊆ s :=
closure_minimal (subset.refl _) hs

lemma is_closed.closure_subset_iff {s t : set α} (h₁ : is_closed t) :
  closure s ⊆ t ↔ s ⊆ t :=
⟨subset.trans subset_closure, assume h, closure_minimal h h₁⟩

lemma closure_mono {s t : set α} (h : s ⊆ t) : closure s ⊆ closure t :=
closure_minimal (subset.trans h subset_closure) is_closed_closure

lemma monotone_closure (α : Type*) [topological_space α] : monotone (@closure α _) :=
λ _ _, closure_mono

lemma closure_inter_subset_inter_closure (s t : set α) :
  closure (s ∩ t) ⊆ closure s ∩ closure t :=
(monotone_closure α).map_inf_le s t

lemma is_closed_of_closure_subset {s : set α} (h : closure s ⊆ s) : is_closed s :=
by rw subset.antisymm subset_closure h; exact is_closed_closure

lemma closure_eq_iff_is_closed {s : set α} : closure s = s ↔ is_closed s :=
⟨assume h, h ▸ is_closed_closure, is_closed.closure_eq⟩

lemma closure_subset_iff_is_closed {s : set α} : closure s ⊆ s ↔ is_closed s :=
⟨is_closed_of_closure_subset, is_closed.closure_subset⟩

@[simp] lemma closure_empty : closure (∅ : set α) = ∅ :=
is_closed_empty.closure_eq

@[simp] lemma closure_empty_iff (s : set α) : closure s = ∅ ↔ s = ∅ :=
⟨subset_eq_empty subset_closure, λ h, h.symm ▸ closure_empty⟩

lemma set.nonempty.closure {s : set α} (h : s.nonempty) :
  set.nonempty (closure s) :=
let ⟨x, hx⟩ := h in ⟨x, subset_closure hx⟩

@[simp] lemma closure_univ : closure (univ : set α) = univ :=
is_closed_univ.closure_eq

@[simp] lemma closure_closure {s : set α} : closure (closure s) = closure s :=
is_closed_closure.closure_eq

@[simp] lemma closure_union {s t : set α} : closure (s ∪ t) = closure s ∪ closure t :=
subset.antisymm
  (closure_minimal (union_subset_union subset_closure subset_closure) $ is_closed_union is_closed_closure is_closed_closure)
  ((monotone_closure α).le_map_sup s t)

lemma interior_subset_closure {s : set α} : interior s ⊆ closure s :=
subset.trans interior_subset subset_closure

lemma closure_eq_compl_interior_compl {s : set α} : closure s = (interior sᶜ)ᶜ :=
begin
  unfold interior closure is_closed,
  rw [compl_sUnion, compl_image_set_of],
  simp only [compl_subset_compl]
end

@[simp] lemma interior_compl {s : set α} : interior sᶜ = (closure s)ᶜ :=
by simp [closure_eq_compl_interior_compl]

@[simp] lemma closure_compl {s : set α} : closure sᶜ = (interior s)ᶜ :=
by simp [closure_eq_compl_interior_compl]

theorem mem_closure_iff {s : set α} {a : α} :
  a ∈ closure s ↔ ∀ o, is_open o → a ∈ o → (o ∩ s).nonempty :=
⟨λ h o oo ao, classical.by_contradiction $ λ os,
  have s ⊆ oᶜ, from λ x xs xo, os ⟨x, xo, xs⟩,
  closure_minimal this (is_closed_compl_iff.2 oo) h ao,
λ H c ⟨h₁, h₂⟩, classical.by_contradiction $ λ nc,
  let ⟨x, hc, hs⟩ := (H _ h₁ nc) in hc (h₂ hs)⟩

lemma dense_iff_inter_open {s : set α} :
  closure s = univ ↔ ∀ U, is_open U → U.nonempty → (U ∩ s).nonempty :=
begin
  split ; intro h,
  { rintros U U_op ⟨x, x_in⟩,
    exact mem_closure_iff.1 (by simp only [h]) U U_op x_in },
  { apply eq_univ_of_forall, intro x,
    rw mem_closure_iff,
    intros U U_op x_in,
    exact h U U_op ⟨_, x_in⟩ },
end

lemma dense_of_subset_dense {s₁ s₂ : set α} (h : s₁ ⊆ s₂) (hd : closure s₁ = univ) :
  closure s₂ = univ :=
by { rw [← univ_subset_iff, ← hd], exact closure_mono h }

/-!
### Frontier of a set
-/

/-- The frontier of a set is the set of points between the closure and interior. -/
def frontier (s : set α) : set α := closure s \ interior s

lemma frontier_eq_closure_inter_closure {s : set α} :
  frontier s = closure s ∩ closure sᶜ :=
by rw [closure_compl, frontier, diff_eq]

/-- The complement of a set has the same frontier as the original set. -/
@[simp] lemma frontier_compl (s : set α) : frontier sᶜ = frontier s :=
by simp only [frontier_eq_closure_inter_closure, compl_compl, inter_comm]

lemma frontier_inter_subset (s t : set α) :
  frontier (s ∩ t) ⊆ (frontier s ∩ closure t) ∪ (closure s ∩ frontier t) :=
begin
  simp only [frontier_eq_closure_inter_closure, compl_inter, closure_union],
  convert inter_subset_inter_left _ (closure_inter_subset_inter_closure s t),
  simp only [inter_distrib_left, inter_distrib_right, inter_assoc],
  congr' 2,
  apply inter_comm
end

lemma frontier_union_subset (s t : set α) :
  frontier (s ∪ t) ⊆ (frontier s ∩ closure tᶜ) ∪ (closure sᶜ ∩ frontier t) :=
by simpa only [frontier_compl, ← compl_union]
  using frontier_inter_subset sᶜ tᶜ

lemma is_closed.frontier_eq {s : set α} (hs : is_closed s) : frontier s = s \ interior s :=
by rw [frontier, hs.closure_eq]

lemma is_open.frontier_eq {s : set α} (hs : is_open s) : frontier s = closure s \ s :=
by rw [frontier, interior_eq_of_open hs]

/-- The frontier of a set is closed. -/
lemma is_closed_frontier {s : set α} : is_closed (frontier s) :=
by rw frontier_eq_closure_inter_closure; exact is_closed_inter is_closed_closure is_closed_closure

/-- The frontier of a closed set has no interior point. -/
lemma interior_frontier {s : set α} (h : is_closed s) : interior (frontier s) = ∅ :=
begin
  have A : frontier s = s \ interior s, from h.frontier_eq,
  have B : interior (frontier s) ⊆ interior s, by rw A; exact interior_mono (diff_subset _ _),
  have C : interior (frontier s) ⊆ frontier s := interior_subset,
  have : interior (frontier s) ⊆ (interior s) ∩ (s \ interior s) :=
    subset_inter B (by simpa [A] using C),
  rwa [inter_diff_self, subset_empty_iff] at this,
end

/-!
### Neighborhoods
-/

/-- neighbourhood filter -/
def nhds (a : α) : filter α := (⨅ s ∈ {s : set α | a ∈ s ∧ is_open s}, 𝓟 s)

localized "notation `𝓝` := nhds" in topological_space

lemma nhds_def (a : α) : 𝓝 a = (⨅ s ∈ {s : set α | a ∈ s ∧ is_open s}, 𝓟 s) := rfl

lemma nhds_basis_opens (a : α) : (𝓝 a).has_basis (λ s : set α, a ∈ s ∧ is_open s) (λ x, x) :=
has_basis_binfi_principal
  (λ s ⟨has, hs⟩ t ⟨hat, ht⟩, ⟨s ∩ t, ⟨⟨has, hat⟩, is_open_inter hs ht⟩,
    ⟨inter_subset_left _ _, inter_subset_right _ _⟩⟩)
  ⟨univ, ⟨mem_univ a, is_open_univ⟩⟩

lemma le_nhds_iff {f a} : f ≤ 𝓝 a ↔ ∀ s : set α, a ∈ s → is_open s → s ∈ f :=
by simp [nhds_def]

lemma nhds_le_of_le {f a} {s : set α} (h : a ∈ s) (o : is_open s) (sf : 𝓟 s ≤ f) : 𝓝 a ≤ f :=
by rw nhds_def; exact infi_le_of_le s (infi_le_of_le ⟨h, o⟩ sf)

lemma mem_nhds_sets_iff {a : α} {s : set α} :
  s ∈ 𝓝 a ↔ ∃t⊆s, is_open t ∧ a ∈ t :=
(nhds_basis_opens a).mem_iff.trans
  ⟨λ ⟨t, ⟨hat, ht⟩, hts⟩, ⟨t, hts, ht, hat⟩, λ ⟨t, hts, ht, hat⟩, ⟨t, ⟨hat, ht⟩, hts⟩⟩

lemma eventually_nhds_iff {a : α} {p : α → Prop} :
  (∀ᶠ x in 𝓝 a, p x) ↔ ∃ (t : set α), (∀ x ∈ t, p x) ∧ is_open t ∧ a ∈ t :=
mem_nhds_sets_iff.trans $ by simp only [subset_def, exists_prop, mem_set_of_eq]

lemma map_nhds {a : α} {f : α → β} :
  map f (𝓝 a) = (⨅ s ∈ {s : set α | a ∈ s ∧ is_open s}, 𝓟 (image f s)) :=
((nhds_basis_opens a).map f).eq_binfi

attribute [irreducible] nhds

lemma mem_of_nhds {a : α} {s : set α} : s ∈ 𝓝 a → a ∈ s :=
λ H, let ⟨t, ht, _, hs⟩ := mem_nhds_sets_iff.1 H in ht hs

lemma filter.eventually.self_of_nhds {p : α → Prop} {a : α}
  (h : ∀ᶠ y in 𝓝 a, p y) : p a :=
mem_of_nhds h

lemma mem_nhds_sets {a : α} {s : set α} (hs : is_open s) (ha : a ∈ s) :
  s ∈ 𝓝 a :=
mem_nhds_sets_iff.2 ⟨s, subset.refl _, hs, ha⟩

lemma nhds_basis_opens' (a : α) : (𝓝 a).has_basis (λ s : set α, s ∈ 𝓝 a ∧ is_open s) (λ x, x) :=
begin
  convert nhds_basis_opens a,
  ext s,
  split,
  { rintros ⟨s_in, s_op⟩,
    exact ⟨mem_of_nhds s_in, s_op⟩ },
  { rintros ⟨a_in, s_op⟩,
    exact ⟨mem_nhds_sets s_op a_in, s_op⟩ },
end

/-- If a predicate is true in a neighbourhood of `a`, then for `y` sufficiently close
to `a` this predicate is true in a neighbourhood of `y`. -/
lemma filter.eventually.eventually_nhds {p : α → Prop} {a : α} (h : ∀ᶠ y in 𝓝 a, p y) :
  ∀ᶠ y in 𝓝 a, ∀ᶠ x in 𝓝 y, p x :=
let ⟨t, htp, hto, ha⟩ := eventually_nhds_iff.1 h in
eventually_nhds_iff.2 ⟨t, λ x hx, eventually_nhds_iff.2 ⟨t, htp, hto, hx⟩, hto, ha⟩

@[simp] lemma eventually_eventually_nhds {p : α → Prop} {a : α} :
  (∀ᶠ y in 𝓝 a, ∀ᶠ x in 𝓝 y, p x) ↔ ∀ᶠ x in 𝓝 a, p x :=
⟨λ h, h.self_of_nhds, λ h, h.eventually_nhds⟩

@[simp] lemma nhds_bind_nhds : (𝓝 a).bind 𝓝 = 𝓝 a := filter.ext $ λ s, eventually_eventually_nhds

@[simp] lemma eventually_eventually_eq_nhds {f g : α → β} {a : α} :
  (∀ᶠ y in 𝓝 a, f =ᶠ[𝓝 y] g) ↔ f =ᶠ[𝓝 a] g :=
eventually_eventually_nhds

lemma filter.eventually_eq.eq_of_nhds {f g : α → β} {a : α} (h : f =ᶠ[𝓝 a] g) : f a = g a :=
let ⟨u, hu, H⟩ := h.exists_mem in H _ (mem_of_nhds hu)

@[simp] lemma eventually_eventually_le_nhds [has_le β] {f g : α → β} {a : α} :
  (∀ᶠ y in 𝓝 a, f ≤ᶠ[𝓝 y] g) ↔ f ≤ᶠ[𝓝 a] g :=
eventually_eventually_nhds

/-- If two functions are equal in a neighbourhood of `a`, then for `y` sufficiently close
to `a` these functions are equal in a neighbourhood of `y`. -/
lemma filter.eventually_eq.eventually_eq_nhds {f g : α → β} {a : α} (h : f =ᶠ[𝓝 a] g) :
  ∀ᶠ y in 𝓝 a, f =ᶠ[𝓝 y] g :=
h.eventually_nhds

/-- If `f x ≤ g x` in a neighbourhood of `a`, then for `y` sufficiently close to `a` we have
`f x ≤ g x` in a neighbourhood of `y`. -/
lemma filter.eventually_le.eventually_le_nhds [has_le β] {f g : α → β} {a : α} (h : f ≤ᶠ[𝓝 a] g) :
  ∀ᶠ y in 𝓝 a, f ≤ᶠ[𝓝 y] g :=
h.eventually_nhds

theorem all_mem_nhds (x : α) (P : set α → Prop) (hP : ∀ s t, s ⊆ t → P s → P t) :
  (∀ s ∈ 𝓝 x, P s) ↔ (∀ s, is_open s → x ∈ s → P s) :=
((nhds_basis_opens x).forall_iff hP).trans $ by simp only [and_comm (x ∈ _), and_imp]

theorem all_mem_nhds_filter (x : α) (f : set α → set β) (hf : ∀ s t, s ⊆ t → f s ⊆ f t)
    (l : filter β) :
  (∀ s ∈ 𝓝 x, f s ∈ l) ↔ (∀ s, is_open s → x ∈ s → f s ∈ l) :=
all_mem_nhds _ _ (λ s t ssubt h, mem_sets_of_superset h (hf s t ssubt))

theorem rtendsto_nhds {r : rel β α} {l : filter β} {a : α} :
  rtendsto r l (𝓝 a) ↔ (∀ s, is_open s → a ∈ s → r.core s ∈ l) :=
all_mem_nhds_filter _ _ (λ s t, id) _

theorem rtendsto'_nhds {r : rel β α} {l : filter β} {a : α} :
  rtendsto' r l (𝓝 a) ↔ (∀ s, is_open s → a ∈ s → r.preimage s ∈ l) :=
by { rw [rtendsto'_def], apply all_mem_nhds_filter, apply rel.preimage_mono }

theorem ptendsto_nhds {f : β →. α} {l : filter β} {a : α} :
  ptendsto f l (𝓝 a) ↔ (∀ s, is_open s → a ∈ s → f.core s ∈ l) :=
rtendsto_nhds

theorem ptendsto'_nhds {f : β →. α} {l : filter β} {a : α} :
  ptendsto' f l (𝓝 a) ↔ (∀ s, is_open s → a ∈ s → f.preimage s ∈ l) :=
rtendsto'_nhds

theorem tendsto_nhds {f : β → α} {l : filter β} {a : α} :
  tendsto f l (𝓝 a) ↔ (∀ s, is_open s → a ∈ s → f ⁻¹' s ∈ l) :=
all_mem_nhds_filter _ _ (λ s t h, preimage_mono h) _

lemma tendsto_const_nhds {a : α} {f : filter β} : tendsto (λb:β, a) f (𝓝 a) :=
tendsto_nhds.mpr $ assume s hs ha, univ_mem_sets' $ assume _, ha

lemma pure_le_nhds : pure ≤ (𝓝 : α → filter α) :=
assume a s hs, mem_pure_sets.2 $ mem_of_nhds hs

lemma tendsto_pure_nhds {α : Type*} [topological_space β] (f : α → β) (a : α) :
  tendsto f (pure a) (𝓝 (f a)) :=
tendsto_le_right (pure_le_nhds _) (tendsto_pure_pure f a)

lemma order_top.tendsto_at_top {α : Type*} [order_top α] [topological_space β] (f : α → β) :
  tendsto f at_top (𝓝 $ f ⊤) :=
tendsto_le_right (pure_le_nhds _) $ tendsto_at_top_pure f

@[simp] instance nhds_ne_bot {a : α} : ne_bot (𝓝 a) :=
ne_bot_of_le (pure_le_nhds a)

/-!
### Cluster points

In this section we define [cluster points](https://en.wikipedia.org/wiki/Limit_point)
(also known as limit points and accumulation points) of a filter and of a sequence.
-/

/-- A point `x` is a cluster point of a filter `F` if 𝓝 x ⊓ F ≠ ⊥. Also known as
an accumulation point or a limit point. -/
def cluster_pt (x : α) (F : filter α) : Prop := ne_bot (𝓝 x ⊓ F)

lemma cluster_pt.ne_bot {x : α} {F : filter α} (h : cluster_pt x F) : ne_bot (𝓝 x ⊓ F) := h

lemma cluster_pt_iff {x : α} {F : filter α} :
  cluster_pt x F ↔ ∀ {U V : set α}, U ∈ 𝓝 x → V ∈ F → (U ∩ V).nonempty :=
inf_ne_bot_iff

/-- `x` is a cluster point of a set `s` if every neighbourhood of `x` meets `s` on a nonempty
set. -/
lemma cluster_pt_principal_iff {x : α} {s : set α} :
  cluster_pt x (𝓟 s) ↔ ∀ U ∈ 𝓝 x, (U ∩ s).nonempty :=
inf_principal_ne_bot_iff

lemma cluster_pt.of_le_nhds {x : α} {f : filter α} (H : f ≤ 𝓝 x) [ne_bot f] : cluster_pt x f :=
by rwa [cluster_pt, inf_eq_right.mpr H]

lemma cluster_pt.of_le_nhds' {x : α} {f : filter α} (H : f ≤ 𝓝 x) (hf : ne_bot f) :
  cluster_pt x f :=
cluster_pt.of_le_nhds H

lemma cluster_pt.of_nhds_le {x : α} {f : filter α} (H : 𝓝 x ≤ f) : cluster_pt x f :=
by simp only [cluster_pt, inf_eq_left.mpr H, nhds_ne_bot]

lemma cluster_pt.mono {x : α} {f g : filter α} (H : cluster_pt x f) (h : f ≤ g) :
  cluster_pt x g :=
ne_bot_of_le_ne_bot H $ inf_le_inf_left _ h

lemma cluster_pt.of_inf_left {x : α} {f g : filter α} (H : cluster_pt x $ f ⊓ g) :
  cluster_pt x f :=
H.mono inf_le_left

lemma cluster_pt.of_inf_right {x : α} {f g : filter α} (H : cluster_pt x $ f ⊓ g) :
  cluster_pt x g :=
H.mono inf_le_right

/-- A point `x` is a cluster point of a sequence `u` along a filter `F` if it is a cluster point
of `map u F`. -/
def map_cluster_pt {ι :Type*} (x : α) (F : filter ι) (u : ι → α) : Prop := cluster_pt x (map u F)

lemma map_cluster_pt_iff {ι :Type*} (x : α) (F : filter ι) (u : ι → α) :
  map_cluster_pt x F u ↔ ∀ s ∈ 𝓝 x, ∃ᶠ a in F, u a ∈ s :=
by { simp_rw [map_cluster_pt, cluster_pt, inf_ne_bot_iff_frequently_left, frequently_map], refl }

lemma map_cluster_pt_of_comp {ι δ :Type*} {F : filter ι} {φ : δ → ι} {p : filter δ}
  {x : α} {u : ι → α} [ne_bot p] (h : tendsto φ p F) (H : tendsto (u ∘ φ) p (𝓝 x)) :
  map_cluster_pt x F u :=
begin
  have := calc
  map (u ∘ φ) p = map u (map φ p) : map_map
  ... ≤ map u F : map_mono h,
  have : map (u ∘ φ) p ≤ 𝓝 x ⊓ map u F,
    from le_inf H this,
  exact ne_bot_of_le this
end

/-!
### Interior, closure and frontier in terms of neighborhoods
-/

lemma interior_eq_nhds {s : set α} : interior s = {a | 𝓝 a ≤ 𝓟 s} :=
set.ext $ λ x, by simp only [mem_interior, le_principal_iff, mem_nhds_sets_iff]; refl

lemma mem_interior_iff_mem_nhds {s : set α} {a : α} :
  a ∈ interior s ↔ s ∈ 𝓝 a :=
by simp only [interior_eq_nhds, le_principal_iff]; refl

lemma subset_interior_iff_nhds {s V : set α} : s ⊆ interior V ↔ ∀ x ∈ s, V ∈ 𝓝 x :=
show (∀ x, x ∈ s →  x ∈ _) ↔ _, by simp_rw mem_interior_iff_mem_nhds

lemma is_open_iff_nhds {s : set α} : is_open s ↔ ∀a∈s, 𝓝 a ≤ 𝓟 s :=
calc is_open s ↔ s ⊆ interior s : subset_interior_iff_open.symm
  ... ↔ (∀a∈s, 𝓝 a ≤ 𝓟 s) : by rw [interior_eq_nhds]; refl

lemma is_open_iff_mem_nhds {s : set α} : is_open s ↔ ∀a∈s, s ∈ 𝓝 a :=
is_open_iff_nhds.trans $ forall_congr $ λ _, imp_congr_right $ λ _, le_principal_iff

lemma closure_eq_cluster_pts {s : set α} : closure s = {a | cluster_pt a (𝓟 s)} :=
calc closure s = (interior sᶜ)ᶜ : closure_eq_compl_interior_compl
  ... = {a | ¬ 𝓝 a ≤ 𝓟 sᶜ} : by rw [interior_eq_nhds]; refl
  ... = {a | cluster_pt a (𝓟 s)} : set.ext $ assume a, not_congr
    (is_compl_principal s).inf_left_eq_bot_iff.symm

theorem mem_closure_iff_cluster_pt {s : set α} {a : α} : a ∈ closure s ↔ cluster_pt a (𝓟 s) :=
by simp only [closure_eq_cluster_pts, mem_set_of_eq]

theorem mem_closure_iff_nhds {s : set α} {a : α} :
  a ∈ closure s ↔ ∀ t ∈ 𝓝 a, (t ∩ s).nonempty :=
mem_closure_iff_cluster_pt.trans cluster_pt_principal_iff

theorem mem_closure_iff_nhds' {s : set α} {a : α} :
  a ∈ closure s ↔ ∀ t ∈ 𝓝 a, ∃ y : s, ↑y ∈ t :=
by simp only [mem_closure_iff_nhds, set.nonempty_inter_iff_exists_right]

theorem mem_closure_iff_comap_ne_bot {A : set α} {x : α} :
  x ∈ closure A ↔ ne_bot (comap (coe : A → α) (𝓝 x)) :=
by simp_rw [mem_closure_iff_nhds, comap_ne_bot_iff, set.nonempty_inter_iff_exists_right]

theorem mem_closure_iff_nhds_basis {a : α} {p : β → Prop} {s : β → set α} (h : (𝓝 a).has_basis p s)
  {t : set α} :
  a ∈ closure t ↔ ∀ i, p i → ∃ y ∈ t, y ∈ s i :=
mem_closure_iff_nhds.trans
  ⟨λ H i hi, let ⟨x, hx⟩ := (H _ $ h.mem_of_mem hi) in ⟨x, hx.2, hx.1⟩,
    λ H t' ht', let ⟨i, hi, hit⟩ := h.mem_iff.1 ht', ⟨x, xt, hx⟩ := H i hi in
    ⟨x, hit hx, xt⟩⟩

/-- `x` belongs to the closure of `s` if and only if some ultrafilter
  supported on `s` converges to `x`. -/
lemma mem_closure_iff_ultrafilter {s : set α} {x : α} :
  x ∈ closure s ↔ ∃ (u : ultrafilter α), s ∈ u.val ∧ u.val ≤ 𝓝 x :=
begin
  rw closure_eq_cluster_pts, change cluster_pt x (𝓟 s) ↔ _, symmetry,
  convert exists_ultrafilter_iff _, ext u,
  rw [←le_principal_iff, inf_comm, le_inf_iff]
end

lemma is_closed_iff_cluster_pt {s : set α} : is_closed s ↔ ∀a, cluster_pt a (𝓟 s) → a ∈ s :=
calc is_closed s ↔ closure s ⊆ s : closure_subset_iff_is_closed.symm
  ... ↔ (∀a, cluster_pt a (𝓟 s) → a ∈ s) : by simp only [subset_def, mem_closure_iff_cluster_pt]

lemma closure_inter_open {s t : set α} (h : is_open s) : s ∩ closure t ⊆ closure (s ∩ t) :=
assume a ⟨hs, ht⟩,
have s ∈ 𝓝 a, from mem_nhds_sets h hs,
have 𝓝 a ⊓ 𝓟 s = 𝓝 a, by rwa [inf_eq_left, le_principal_iff],
have cluster_pt a (𝓟 (s ∩ t)),
  from calc 𝓝 a ⊓ 𝓟 (s ∩ t) = 𝓝 a ⊓ (𝓟 s ⊓ 𝓟 t) : by rw inf_principal
    ... = 𝓝 a ⊓ 𝓟 t : by rw [←inf_assoc, this]
    ... ≠ ⊥ : by rw [closure_eq_cluster_pts] at ht; assumption,
by rwa [closure_eq_cluster_pts]

lemma dense_inter_of_open_left {s t : set α} (hs : closure s = univ) (ht : closure t = univ)
  (hso : is_open s) :
  closure (s ∩ t) = univ :=
eq_univ_of_subset (closure_minimal (closure_inter_open hso) is_closed_closure) $
  by simp only [*, inter_univ]

lemma dense_inter_of_open_right {s t : set α} (hs : closure s = univ) (ht : closure t = univ)
  (hto : is_open t) :
  closure (s ∩ t) = univ :=
inter_comm t s ▸ dense_inter_of_open_left ht hs hto

lemma closure_diff {s t : set α} : closure s \ closure t ⊆ closure (s \ t) :=
calc closure s \ closure t = (closure t)ᶜ ∩ closure s : by simp only [diff_eq, inter_comm]
  ... ⊆ closure ((closure t)ᶜ ∩ s) : closure_inter_open $ is_open_compl_iff.mpr $ is_closed_closure
  ... = closure (s \ closure t) : by simp only [diff_eq, inter_comm]
  ... ⊆ closure (s \ t) : closure_mono $ diff_subset_diff (subset.refl s) subset_closure

lemma mem_of_closed_of_tendsto {f : β → α} {b : filter β} {a : α} {s : set α}
  [ne_bot b] (hf : tendsto f b (𝓝 a)) (hs : is_closed s) (h : f ⁻¹' s ∈ b) : a ∈ s :=
is_closed_iff_cluster_pt.mp hs a $ ne_bot_of_le $ le_inf hf (le_principal_iff.mpr h)

lemma mem_of_closed_of_tendsto' {f : β → α} {x : filter β} {a : α} {s : set α}
  (hf : tendsto f x (𝓝 a)) (hs : is_closed s) [ne_bot (x ⊓ 𝓟 (f ⁻¹' s))] : a ∈ s :=
have tendsto f (x ⊓ 𝓟 (f ⁻¹' s)) (𝓝 a) := tendsto_inf_left hf,
mem_of_closed_of_tendsto this hs $ mem_inf_sets_of_right $ mem_principal_self _

lemma mem_closure_of_tendsto {f : β → α} {b : filter β} {a : α} {s : set α}
  [ne_bot b] (hf : tendsto f b (𝓝 a)) (h : ∀ᶠ x in b, f x ∈ s) : a ∈ closure s :=
mem_of_closed_of_tendsto hf is_closed_closure $
  filter.mem_sets_of_superset h (preimage_mono subset_closure)

/-- Suppose that `f` sends the complement to `s` to a single point `a`, and `l` is some filter.
Then `f` tends to `a` along `l` restricted to `s` if and only it tends to `a` along `l`. -/
lemma tendsto_inf_principal_nhds_iff_of_forall_eq {f : β → α} {l : filter β} {s : set β}
  {a : α} (h : ∀ x ∉ s, f x = a) :
  tendsto f (l ⊓ 𝓟 s) (𝓝 a) ↔ tendsto f l (𝓝 a) :=
begin
  rw [tendsto_iff_comap, tendsto_iff_comap],
  replace h : 𝓟 sᶜ ≤ comap f (𝓝 a),
  { rintros U ⟨t, ht, htU⟩ x hx,
    have : f x ∈ t, from (h x hx).symm ▸ mem_of_nhds ht,
    exact htU this },
  refine ⟨λ h', _, le_trans inf_le_left⟩,
  have := sup_le h' h,
  rw [sup_inf_right, sup_principal, union_compl_self, principal_univ,
    inf_top_eq, sup_le_iff] at this,
  exact this.1
end

/-!
### Limits of filters in topological spaces
-/

section lim

/-- If `f` is a filter, then `Lim f` is a limit of the filter, if it exists. -/
noncomputable def Lim [nonempty α] (f : filter α) : α := epsilon $ λa, f ≤ 𝓝 a

/-- If `f` is a filter in `β` and `g : β → α` is a function, then `lim f` is a limit of `g` at `f`,
if it exists. -/
noncomputable def lim [nonempty α] (f : filter β) (g : β → α) : α :=
Lim (f.map g)

/-- If a filter `f` is majorated by some `𝓝 a`, then it is majorated by `𝓝 (Lim f)`. We formulate
this lemma with a `[nonempty α]` argument of `Lim` derived from `h` to make it useful for types
without a `[nonempty α]` instance. Because of the built-in proof irrelevance, Lean will unify
this instance with any other instance. -/
lemma Lim_spec {f : filter α} (h : ∃a, f ≤ 𝓝 a) : f ≤ 𝓝 (@Lim _ _ (nonempty_of_exists h) f) :=
epsilon_spec h

/-- If `g` tends to some `𝓝 a` along `f`, then it tends to `𝓝 (lim f g)`. We formulate
this lemma with a `[nonempty α]` argument of `lim` derived from `h` to make it useful for types
without a `[nonempty α]` instance. Because of the built-in proof irrelevance, Lean will unify
this instance with any other instance. -/
lemma lim_spec {f : filter β} {g : β → α} (h : ∃ a, tendsto g f (𝓝 a)) :
  tendsto g f (𝓝 $ @lim _ _ _ (nonempty_of_exists h) f g) :=
Lim_spec h

end lim

/-!
### Locally finite families
-/

/- locally finite family [General Topology (Bourbaki, 1995)] -/
section locally_finite

/-- A family of sets in `set α` is locally finite if at every point `x:α`,
  there is a neighborhood of `x` which meets only finitely many sets in the family -/
def locally_finite (f : β → set α) :=
∀x:α, ∃t ∈ 𝓝 x, finite {i | (f i ∩ t).nonempty }

lemma locally_finite_of_finite {f : β → set α} (h : finite (univ : set β)) : locally_finite f :=
assume x, ⟨univ, univ_mem_sets, h.subset $ subset_univ _⟩

lemma locally_finite_subset
  {f₁ f₂ : β → set α} (hf₂ : locally_finite f₂) (hf : ∀b, f₁ b ⊆ f₂ b) : locally_finite f₁ :=
assume a,
let ⟨t, ht₁, ht₂⟩ := hf₂ a in
⟨t, ht₁, ht₂.subset $ assume i hi, hi.mono $ inter_subset_inter (hf i) $ subset.refl _⟩

lemma is_closed_Union_of_locally_finite {f : β → set α}
  (h₁ : locally_finite f) (h₂ : ∀i, is_closed (f i)) : is_closed (⋃i, f i) :=
is_open_iff_nhds.mpr $ assume a, assume h : a ∉ (⋃i, f i),
  have ∀i, a ∈ (f i)ᶜ,
    from assume i hi, h $ mem_Union.2 ⟨i, hi⟩,
  have ∀i, (f i)ᶜ ∈ (𝓝 a),
    by simp only [mem_nhds_sets_iff]; exact assume i, ⟨(f i)ᶜ, subset.refl _, h₂ i, this i⟩,
  let ⟨t, h_sets, (h_fin : finite {i | (f i ∩ t).nonempty })⟩ := h₁ a in

  calc 𝓝 a ≤ 𝓟 (t ∩ (⋂ i∈{i | (f i ∩ t).nonempty }, (f i)ᶜ)) :
  begin
    rw [le_principal_iff],
    apply @filter.inter_mem_sets _ (𝓝 a) _ _ h_sets,
    apply @filter.Inter_mem_sets _ (𝓝 a) _ _ _ h_fin,
    exact assume i h, this i
  end
  ... ≤ 𝓟 (⋃i, f i)ᶜ :
  begin
    simp only [principal_mono, subset_def, mem_compl_eq, mem_inter_eq,
      mem_Inter, mem_set_of_eq, mem_Union, and_imp, not_exists,
      exists_imp_distrib, ne_empty_iff_nonempty, set.nonempty],
    exact assume x xt ht i xfi, ht i x xfi xt xfi
  end

end locally_finite

end topological_space

/-!
### Continuity
-/

section continuous
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
variables [topological_space α] [topological_space β] [topological_space γ]
open_locale topological_space

/-- A function between topological spaces is continuous if the preimage
  of every open set is open. -/
def continuous (f : α → β) := ∀s, is_open s → is_open (f ⁻¹' s)

lemma is_open.preimage {f : α → β} (hf : continuous f) {s : set β} (h : is_open s) :
  is_open (f ⁻¹' s) :=
hf s h

/-- A function between topological spaces is continuous at a point `x₀`
if `f x` tends to `f x₀` when `x` tends to `x₀`. -/
def continuous_at (f : α → β) (x : α) := tendsto f (𝓝 x) (𝓝 (f x))

lemma continuous_at.tendsto {f : α → β} {x : α} (h : continuous_at f x) :
  tendsto f (𝓝 x) (𝓝 (f x)) :=
h

lemma continuous_at.preimage_mem_nhds {f : α → β} {x : α} {t : set β} (h : continuous_at f x)
  (ht : t ∈ 𝓝 (f x)) : f ⁻¹' t ∈ 𝓝 x :=
h ht

lemma preimage_interior_subset_interior_preimage {f : α → β} {s : set β}
  (hf : continuous f) : f⁻¹' (interior s) ⊆ interior (f⁻¹' s) :=
interior_maximal (preimage_mono interior_subset) (hf _ is_open_interior)

lemma continuous_id : continuous (id : α → α) :=
assume s h, h

lemma continuous.comp {g : β → γ} {f : α → β} (hg : continuous g) (hf : continuous f) :
  continuous (g ∘ f) :=
assume s h, hf _ (hg s h)

lemma continuous.iterate {f : α → α} (h : continuous f) (n : ℕ) : continuous (f^[n]) :=
nat.rec_on n continuous_id (λ n ihn, ihn.comp h)

lemma continuous_at.comp {g : β → γ} {f : α → β} {x : α}
  (hg : continuous_at g (f x)) (hf : continuous_at f x) :
  continuous_at (g ∘ f) x :=
hg.comp hf

lemma continuous.tendsto {f : α → β} (hf : continuous f) (x) :
  tendsto f (𝓝 x) (𝓝 (f x)) :=
((nhds_basis_opens x).tendsto_iff $ nhds_basis_opens $ f x).2 $
  λ t ⟨hxt, ht⟩, ⟨f ⁻¹' t, ⟨hxt, hf _ ht⟩, subset.refl _⟩

lemma continuous.continuous_at {f : α → β} {x : α} (h : continuous f) :
  continuous_at f x :=
h.tendsto x

lemma continuous_iff_continuous_at {f : α → β} : continuous f ↔ ∀ x, continuous_at f x :=
⟨continuous.tendsto,
  assume hf : ∀x, tendsto f (𝓝 x) (𝓝 (f x)),
  assume s, assume hs : is_open s,
  have ∀a, f a ∈ s → s ∈ 𝓝 (f a),
    from λ a ha, mem_nhds_sets hs ha,
  show is_open (f ⁻¹' s),
    from is_open_iff_nhds.2 $ λ a ha, le_principal_iff.2 $ hf _ (this a ha)⟩

lemma continuous_const {b : β} : continuous (λa:α, b) :=
continuous_iff_continuous_at.mpr $ assume a, tendsto_const_nhds

lemma continuous_at_const {x : α} {b : β} : continuous_at (λ a:α, b) x :=
continuous_const.continuous_at

lemma continuous_at_id {x : α} : continuous_at id x :=
continuous_id.continuous_at

lemma continuous_at.iterate {f : α → α} {x : α} (hf : continuous_at f x) (hx : f x = x) (n : ℕ) :
  continuous_at (f^[n]) x :=
nat.rec_on n continuous_at_id $ λ n ihn,
show continuous_at (f^[n] ∘ f) x,
from continuous_at.comp (hx.symm ▸ ihn) hf

lemma continuous_iff_is_closed {f : α → β} :
  continuous f ↔ (∀s, is_closed s → is_closed (f ⁻¹' s)) :=
⟨assume hf s hs, hf sᶜ hs,
  assume hf s, by rw [←is_closed_compl_iff, ←is_closed_compl_iff]; exact hf _⟩

lemma is_closed.preimage {f : α → β} (hf : continuous f) {s : set β} (h : is_closed s) :
  is_closed (f ⁻¹' s) :=
continuous_iff_is_closed.mp hf s h

lemma continuous_at_iff_ultrafilter {f : α → β} (x) : continuous_at f x ↔
  ∀ g, is_ultrafilter g → g ≤ 𝓝 x → g.map f ≤ 𝓝 (f x) :=
tendsto_iff_ultrafilter f (𝓝 x) (𝓝 (f x))

lemma continuous_iff_ultrafilter {f : α → β} :
  continuous f ↔ ∀ x g, is_ultrafilter g → g ≤ 𝓝 x → g.map f ≤ 𝓝 (f x) :=
by simp only [continuous_iff_continuous_at, continuous_at_iff_ultrafilter]

/-- A piecewise defined function `if p then f else g` is continuous, if both `f` and `g`
are continuous, and they coincide on the frontier (boundary) of the set `{a | p a}`. -/
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
        from have a ∈ (interior {a | p a})ᶜ, from this.right, by rwa [←closure_compl] at this,
      by by_cases p a; simp [h, hp a this, hac, hai, iff_def] {contextual := tt})
    (assume hf : a ∈ (frontier {a | p a})ᶜ,
      classical.by_cases
        (assume : p a,
          have hc : a ∈ closure {a | p a}, from subset_closure this,
          have hnc : a ∉ closure {a | ¬ p a},
            by show a ∉ closure {a | p a}ᶜ; rw [closure_compl]; simpa [frontier, hc] using hf,
          by simp [this, hc, hnc])
        (assume : ¬ p a,
          have hc : a ∈ closure {a | ¬ p a}, from subset_closure this,
          have hnc : a ∉ closure {a | p a},
            begin
              have hc : a ∈ closure {a | p a}ᶜ, from hc,
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
  pcontinuous f ↔ ∀ {x y} (h : y ∈ f x), ptendsto' f (𝓝 x) (𝓝 y) :=
begin
  split,
  { intros h x y h',
    simp only [ptendsto'_def, mem_nhds_sets_iff],
    rintros s ⟨t, tsubs, opent, yt⟩,
    exact ⟨f.preimage t, pfun.preimage_mono _ tsubs, h _ opent, ⟨y, yt, h'⟩⟩
  },
  intros hf s os,
  rw is_open_iff_nhds,
  rintros x ⟨y, ys, fxy⟩ t,
  rw [mem_principal_sets],
  assume h : f.preimage s ⊆ t,
  change t ∈ 𝓝 x,
  apply mem_sets_of_superset _ h,
  have h' : ∀ s ∈ 𝓝 y, f.preimage s ∈ 𝓝 x,
  { intros s hs,
     have : ptendsto' f (𝓝 x) (𝓝 y) := hf fxy,
     rw ptendsto'_def at this,
     exact this s hs },
  show f.preimage s ∈ 𝓝 x,
  apply h', rw mem_nhds_sets_iff, exact ⟨s, set.subset.refl _, os, ys⟩
end

lemma image_closure_subset_closure_image {f : α → β} {s : set α} (h : continuous f) :
  f '' closure s ⊆ closure (f '' s) :=
have ∀ (a : α), cluster_pt a (𝓟 s) → cluster_pt (f a) (𝓟 (f '' s)),
  from assume a ha,
  have h₁ : ¬ map f (𝓝 a ⊓ 𝓟 s) = ⊥,
    by rwa[map_eq_bot_iff],
  have h₂ : map f (𝓝 a ⊓ 𝓟 s) ≤ 𝓝 (f a) ⊓ 𝓟 (f '' s),
    from le_inf
      (le_trans (map_mono inf_le_left) $ by rw [continuous_iff_continuous_at] at h; exact h a)
      (le_trans (map_mono inf_le_right) $ by simp [subset_preimage_image] ),
  ne_bot_of_le_ne_bot h₁ h₂,
by simp [image_subset_iff, closure_eq_cluster_pts]; assumption

lemma mem_closure {s : set α} {t : set β} {f : α → β} {a : α}
  (hf : continuous f) (ha : a ∈ closure s) (ht : ∀a∈s, f a ∈ t) : f a ∈ closure t :=
subset.trans (image_closure_subset_closure_image hf) (closure_mono $ image_subset_iff.2 ht) $
  (mem_image_of_mem f ha)

end continuous

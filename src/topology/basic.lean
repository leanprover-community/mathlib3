/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
import order.filter.ultrafilter
import algebra.support
import order.filter.lift

/-!
# Basic theory of topological spaces.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The main definition is the type class `topological_space α` which endows a type `α` with a topology.
Then `set α` gets predicates `is_open`, `is_closed` and functions `interior`, `closure` and
`frontier`. Each point `x` of `α` gets a neighborhood filter `𝓝 x`. A filter `F` on `α` has
`x` as a cluster point if `cluster_pt x F : 𝓝 x ⊓ F ≠ ⊥`. A map `f : ι → α` clusters at `x`
along `F : filter ι` if `map_cluster_pt x F f : cluster_pt x (map f F)`. In particular
the notion of cluster point of a sequence `u` is `map_cluster_pt x at_top u`.

For topological spaces `α` and `β`, a function `f : α → β` and a point `a : α`,
`continuous_at f a` means `f` is continuous at `a`, and global continuity is
`continuous f`. There is also a version of continuity `pcontinuous` for
partially defined functions.

## Notation

* `𝓝 x`: the filter `nhds x` of neighborhoods of a point `x`;
* `𝓟 s`: the principal filter of a set `s`;
* `𝓝[s] x`: the filter `nhds_within x s` of neighborhoods of a point `x` within a set `s`;
* `𝓝[≤] x`: the filter `nhds_within x (set.Iic x)` of left-neighborhoods of `x`;
* `𝓝[≥] x`: the filter `nhds_within x (set.Ici x)` of right-neighborhoods of `x`;
* `𝓝[<] x`: the filter `nhds_within x (set.Iio x)` of punctured left-neighborhoods of `x`;
* `𝓝[>] x`: the filter `nhds_within x (set.Ioi x)` of punctured right-neighborhoods of `x`;
* `𝓝[≠] x`: the filter `nhds_within x {x}ᶜ` of punctured neighborhoods of `x`.

## Implementation notes

Topology in mathlib heavily uses filters (even more than in Bourbaki). See explanations in
<https://leanprover-community.github.io/theories/topology.html>.

## References

*  [N. Bourbaki, *General Topology*][bourbaki1966]
*  [I. M. James, *Topologies and Uniformities*][james1999]

## Tags

topological space, interior, closure, frontier, neighborhood, continuity, continuous function
-/

noncomputable theory
open set filter classical
open_locale classical filter

universes u v w

/-!
### Topological spaces
-/

/-- A topology on `α`. -/
@[protect_proj] class topological_space (α : Type u) :=
(is_open        : set α → Prop)
(is_open_univ   : is_open univ)
(is_open_inter  : ∀s t, is_open s → is_open t → is_open (s ∩ t))
(is_open_sUnion : ∀s, (∀t∈s, is_open t) → is_open (⋃₀ s))

/-- A constructor for topologies by specifying the closed sets,
and showing that they satisfy the appropriate conditions. -/
def topological_space.of_closed {α : Type u} (T : set (set α))
  (empty_mem : ∅ ∈ T) (sInter_mem : ∀ A ⊆ T, ⋂₀ A ∈ T) (union_mem : ∀ A B ∈ T, A ∪ B ∈ T) :
  topological_space α :=
{ is_open := λ X, Xᶜ ∈ T,
  is_open_univ := by simp [empty_mem],
  is_open_inter := λ s t hs ht, by simpa only [compl_inter] using union_mem sᶜ hs tᶜ ht,
  is_open_sUnion := λ s hs,
    by rw set.compl_sUnion; exact sInter_mem (compl '' s)
    (λ z ⟨y, hy, hz⟩, by simpa [hz.symm] using hs y hy) }

section topological_space

variables {α : Type u} {β : Type v} {ι : Sort w} {a : α} {s s₁ s₂ t : set α} {p p₁ p₂ : α → Prop}

/-- `is_open s` means that `s` is open in the ambient topological space on `α` -/
def is_open [topological_space α] (s : set α) : Prop := @topological_space.is_open _ ‹_› s

localized "notation (name := is_open_of) `is_open[` t `]` := @is_open hole! t" in topology

lemma is_open_mk {p h₁ h₂ h₃} {s : set α} : is_open[⟨p, h₁, h₂, h₃⟩] s ↔ p s := iff.rfl

@[ext]
lemma topological_space_eq {f g : topological_space α} (h : is_open[f] = is_open[g]) : f = g :=
by unfreezingI { cases f, cases g, congr, exact h }

section
variables [topological_space α]

@[simp]
lemma is_open_univ : is_open (univ : set α) := topological_space.is_open_univ

lemma is_open.inter (h₁ : is_open s₁) (h₂ : is_open s₂) : is_open (s₁ ∩ s₂) :=
topological_space.is_open_inter s₁ s₂ h₁ h₂

lemma is_open_sUnion {s : set (set α)} (h : ∀t ∈ s, is_open t) : is_open (⋃₀ s) :=
topological_space.is_open_sUnion s h

end

lemma topological_space_eq_iff {t t' : topological_space α} :
  t = t' ↔ ∀ s, is_open[t] s ↔ is_open[t'] s :=
⟨λ h s, h ▸ iff.rfl, λ h, by { ext, exact h _ }⟩

lemma is_open_fold {s : set α} {t : topological_space α} : t.is_open s = is_open[t] s :=
rfl

variables [topological_space α]

lemma is_open_Union {f : ι → set α} (h : ∀i, is_open (f i)) : is_open (⋃i, f i) :=
is_open_sUnion $ by rintro _ ⟨i, rfl⟩; exact h i

lemma is_open_bUnion {s : set β} {f : β → set α} (h : ∀i∈s, is_open (f i)) :
  is_open (⋃i∈s, f i) :=
is_open_Union $ assume i, is_open_Union $ assume hi, h i hi

lemma is_open.union (h₁ : is_open s₁) (h₂ : is_open s₂) : is_open (s₁ ∪ s₂) :=
by rw union_eq_Union; exact is_open_Union (bool.forall_bool.2 ⟨h₂, h₁⟩)

@[simp] lemma is_open_empty : is_open (∅ : set α) :=
by rw ← sUnion_empty; exact is_open_sUnion (assume a, false.elim)

lemma is_open_sInter {s : set (set α)} (hs : s.finite) : (∀t ∈ s, is_open t) → is_open (⋂₀ s) :=
finite.induction_on hs (λ _, by rw sInter_empty; exact is_open_univ) $
λ a s has hs ih h, by rw sInter_insert; exact
is_open.inter (h _ $ mem_insert _ _) (ih $ λ t, h t ∘ mem_insert_of_mem _)

lemma is_open_bInter {s : set β} {f : β → set α} (hs : s.finite) :
  (∀i∈s, is_open (f i)) → is_open (⋂i∈s, f i) :=
finite.induction_on hs
  (λ _, by rw bInter_empty; exact is_open_univ)
  (λ a s has hs ih h, by rw bInter_insert; exact
    is_open.inter (h a (mem_insert _ _)) (ih (λ i hi, h i (mem_insert_of_mem _ hi))))

lemma is_open_Inter [finite β] {s : β → set α} (h : ∀ i, is_open (s i)) : is_open (⋂ i, s i) :=
suffices is_open (⋂ (i : β) (hi : i ∈ @univ β), s i), by simpa,
is_open_bInter finite_univ (λ i _, h i)

lemma is_open_Inter_prop {p : Prop} {s : p → set α}
  (h : ∀ h : p, is_open (s h)) : is_open (Inter s) :=
by by_cases p; simp *

lemma is_open_bInter_finset {s : finset β} {f : β → set α} (h : ∀ i ∈ s, is_open (f i)) :
  is_open (⋂ i ∈ s, f i) :=
is_open_bInter (to_finite _) h

lemma is_open_const {p : Prop} : is_open {a : α | p} :=
by_cases
  (assume : p, begin simp only [this]; exact is_open_univ end)
  (assume : ¬ p, begin simp only [this]; exact is_open_empty end)

lemma is_open.and : is_open {a | p₁ a} → is_open {a | p₂ a} → is_open {a | p₁ a ∧ p₂ a} :=
is_open.inter

/-- A set is closed if its complement is open -/
class is_closed (s : set α) : Prop :=
(is_open_compl : is_open sᶜ)

localized "notation (name := is_closed_of) `is_closed[` t `]` := @is_closed hole! t" in topology

@[simp] lemma is_open_compl_iff {s : set α} : is_open sᶜ ↔ is_closed s :=
⟨λ h, ⟨h⟩, λ h, h.is_open_compl⟩

@[simp] lemma is_closed_empty : is_closed (∅ : set α) :=
by { rw [← is_open_compl_iff, compl_empty], exact is_open_univ }

@[simp] lemma is_closed_univ : is_closed (univ : set α) :=
by { rw [← is_open_compl_iff, compl_univ], exact is_open_empty }

lemma is_closed.union : is_closed s₁ → is_closed s₂ → is_closed (s₁ ∪ s₂) :=
λ h₁ h₂, by { rw [← is_open_compl_iff] at *, rw compl_union, exact is_open.inter h₁ h₂ }

lemma is_closed_sInter {s : set (set α)} : (∀t ∈ s, is_closed t) → is_closed (⋂₀ s) :=
by simpa only [← is_open_compl_iff, compl_sInter, sUnion_image] using is_open_bUnion

lemma is_closed_Inter {f : ι → set α} (h : ∀i, is_closed (f i)) : is_closed (⋂i, f i ) :=
is_closed_sInter $ assume t ⟨i, (heq : f i = t)⟩, heq ▸ h i

lemma is_closed_bInter {s : set β} {f : β → set α} (h : ∀ i ∈ s, is_closed (f i)) :
  is_closed (⋂ i ∈ s, f i) :=
is_closed_Inter $ λ i, is_closed_Inter $ h i

@[simp] lemma is_closed_compl_iff {s : set α} : is_closed sᶜ ↔ is_open s :=
by rw [←is_open_compl_iff, compl_compl]

lemma is_open.is_closed_compl {s : set α} (hs : is_open s) : is_closed sᶜ :=
is_closed_compl_iff.2 hs

lemma is_open.sdiff {s t : set α} (h₁ : is_open s) (h₂ : is_closed t) : is_open (s \ t) :=
is_open.inter h₁ $ is_open_compl_iff.mpr h₂

lemma is_closed.inter (h₁ : is_closed s₁) (h₂ : is_closed s₂) : is_closed (s₁ ∩ s₂) :=
by { rw [← is_open_compl_iff] at *, rw compl_inter, exact is_open.union h₁ h₂ }

lemma is_closed.sdiff {s t : set α} (h₁ : is_closed s) (h₂ : is_open t) : is_closed (s \ t) :=
is_closed.inter h₁ (is_closed_compl_iff.mpr h₂)

lemma is_closed_bUnion {s : set β} {f : β → set α} (hs : s.finite) :
  (∀i∈s, is_closed (f i)) → is_closed (⋃i∈s, f i) :=
finite.induction_on hs
  (λ _, by rw bUnion_empty; exact is_closed_empty)
  (λ a s has hs ih h, by rw bUnion_insert; exact
    is_closed.union (h a (mem_insert _ _)) (ih (λ i hi, h i (mem_insert_of_mem _ hi))))

lemma is_closed_Union [finite β] {s : β → set α} (h : ∀ i, is_closed (s i)) :
  is_closed (⋃ i, s i) :=
suffices is_closed (⋃ (i : β) (hi : i ∈ @univ β), s i),
  by convert this; simp [set.ext_iff],
is_closed_bUnion finite_univ (λ i _, h i)

lemma is_closed_Union_prop {p : Prop} {s : p → set α}
  (h : ∀ h : p, is_closed (s h)) : is_closed (Union s) :=
by by_cases p; simp *

lemma is_closed_imp {p q : α → Prop} (hp : is_open {x | p x})
  (hq : is_closed {x | q x}) : is_closed {x | p x → q x} :=
have {x | p x → q x} = {x | p x}ᶜ ∪ {x | q x}, from set.ext $ λ x, imp_iff_not_or,
by rw [this]; exact is_closed.union (is_closed_compl_iff.mpr hp) hq

lemma is_closed.not : is_closed {a | p a} → is_open {a | ¬ p a} :=
is_open_compl_iff.mpr

/-!
### Interior of a set
-/

/-- The interior of a set `s` is the largest open subset of `s`. -/
def interior (s : set α) : set α := ⋃₀ {t | is_open t ∧ t ⊆ s}

lemma mem_interior {s : set α} {x : α} :
  x ∈ interior s ↔ ∃ t ⊆ s, is_open t ∧ x ∈ t :=
by simp only [interior, mem_sUnion, mem_set_of_eq, exists_prop, and_assoc, and.left_comm]

@[simp] lemma is_open_interior {s : set α} : is_open (interior s) :=
is_open_sUnion $ assume t ⟨h₁, h₂⟩, h₁

lemma interior_subset {s : set α} : interior s ⊆ s :=
sUnion_subset $ assume t ⟨h₁, h₂⟩, h₂

lemma interior_maximal {s t : set α} (h₁ : t ⊆ s) (h₂ : is_open t) : t ⊆ interior s :=
subset_sUnion_of_mem ⟨h₂, h₁⟩

lemma is_open.interior_eq {s : set α} (h : is_open s) : interior s = s :=
subset.antisymm interior_subset (interior_maximal (subset.refl s) h)

lemma interior_eq_iff_is_open {s : set α} : interior s = s ↔ is_open s :=
⟨assume h, h ▸ is_open_interior, is_open.interior_eq⟩

lemma subset_interior_iff_is_open {s : set α} : s ⊆ interior s ↔ is_open s :=
by simp only [interior_eq_iff_is_open.symm, subset.antisymm_iff, interior_subset, true_and]

lemma is_open.subset_interior_iff {s t : set α} (h₁ : is_open s) :
  s ⊆ interior t ↔ s ⊆ t :=
⟨assume h, subset.trans h interior_subset, assume h₂, interior_maximal h₂ h₁⟩

lemma subset_interior_iff {s t : set α} : t ⊆ interior s ↔ ∃ U, is_open U ∧ t ⊆ U ∧ U ⊆ s :=
⟨λ h, ⟨interior s, is_open_interior, h, interior_subset⟩,
  λ ⟨U, hU, htU, hUs⟩, htU.trans (interior_maximal hUs hU)⟩

@[mono] lemma interior_mono {s t : set α} (h : s ⊆ t) : interior s ⊆ interior t :=
interior_maximal (subset.trans interior_subset h) is_open_interior

@[simp] lemma interior_empty : interior (∅ : set α) = ∅ :=
is_open_empty.interior_eq

@[simp] lemma interior_univ : interior (univ : set α) = univ :=
is_open_univ.interior_eq

@[simp] lemma interior_eq_univ {s : set α} : interior s = univ ↔ s = univ :=
⟨λ h, univ_subset_iff.mp $ h.symm.trans_le interior_subset, λ h, h.symm ▸ interior_univ⟩

@[simp] lemma interior_interior {s : set α} : interior (interior s) = interior s :=
is_open_interior.interior_eq

@[simp] lemma interior_inter {s t : set α} : interior (s ∩ t) = interior s ∩ interior t :=
subset.antisymm
  (subset_inter (interior_mono $ inter_subset_left s t) (interior_mono $ inter_subset_right s t))
  (interior_maximal (inter_subset_inter interior_subset interior_subset) $
    is_open.inter is_open_interior is_open_interior)

@[simp] lemma finset.interior_Inter {ι : Type*} (s : finset ι) (f : ι → set α) :
  interior (⋂ i ∈ s, f i) = ⋂ i ∈ s, interior (f i) :=
begin
  classical,
  refine s.induction_on (by simp) _,
  intros i s h₁ h₂,
  simp [h₂],
end

@[simp] lemma interior_Inter {ι : Type*} [finite ι] (f : ι → set α) :
  interior (⋂ i, f i) = ⋂ i, interior (f i) :=
by { casesI nonempty_fintype ι, convert finset.univ.interior_Inter f; simp }

lemma interior_union_is_closed_of_interior_empty {s t : set α} (h₁ : is_closed s)
  (h₂ : interior t = ∅) :
  interior (s ∪ t) = interior s :=
have interior (s ∪ t) ⊆ s, from
  assume x ⟨u, ⟨(hu₁ : is_open u), (hu₂ : u ⊆ s ∪ t)⟩, (hx₁ : x ∈ u)⟩,
  classical.by_contradiction $ assume hx₂ : x ∉ s,
    have u \ s ⊆ t,
      from assume x ⟨h₁, h₂⟩, or.resolve_left (hu₂ h₁) h₂,
    have u \ s ⊆ interior t,
      by rwa (is_open.sdiff hu₁ h₁).subset_interior_iff,
    have u \ s ⊆ ∅,
      by rwa h₂ at this,
    this ⟨hx₁, hx₂⟩,
subset.antisymm
  (interior_maximal this is_open_interior)
  (interior_mono $ subset_union_left _ _)

lemma is_open_iff_forall_mem_open : is_open s ↔ ∀ x ∈ s, ∃ t ⊆ s, is_open t ∧ x ∈ t :=
by rw ← subset_interior_iff_is_open; simp only [subset_def, mem_interior]

lemma interior_Inter_subset (s : ι → set α) : interior (⋂ i, s i) ⊆ ⋂ i, interior (s i) :=
subset_Inter $ λ i, interior_mono $ Inter_subset _ _

lemma interior_Inter₂_subset (p : ι → Sort*) (s : Π i, p i → set α) :
  interior (⋂ i j, s i j) ⊆ ⋂ i j, interior (s i j) :=
(interior_Inter_subset _).trans $ Inter_mono $ λ i, interior_Inter_subset _

lemma interior_sInter_subset (S : set (set α)) : interior (⋂₀ S) ⊆ ⋂ s ∈ S, interior s :=
calc interior (⋂₀ S) = interior (⋂ s ∈ S, s) : by rw sInter_eq_bInter
                 ... ⊆ ⋂ s ∈ S, interior s  : interior_Inter₂_subset _ _

/-!
### Closure of a set
-/

/-- The closure of `s` is the smallest closed set containing `s`. -/
def closure (s : set α) : set α := ⋂₀ {t | is_closed t ∧ s ⊆ t}

@[simp] lemma is_closed_closure {s : set α} : is_closed (closure s) :=
is_closed_sInter $ assume t ⟨h₁, h₂⟩, h₁

lemma subset_closure {s : set α} : s ⊆ closure s :=
subset_sInter $ assume t ⟨h₁, h₂⟩, h₂

lemma not_mem_of_not_mem_closure {s : set α} {P : α} (hP : P ∉ closure s) : P ∉ s :=
λ h, hP (subset_closure h)

lemma closure_minimal {s t : set α} (h₁ : s ⊆ t) (h₂ : is_closed t) : closure s ⊆ t :=
sInter_subset_of_mem ⟨h₂, h₁⟩

lemma disjoint.closure_left {s t : set α} (hd : disjoint s t) (ht : is_open t) :
  disjoint (closure s) t :=
disjoint_compl_left.mono_left $ closure_minimal hd.subset_compl_right ht.is_closed_compl

lemma disjoint.closure_right {s t : set α} (hd : disjoint s t) (hs : is_open s) :
  disjoint s (closure t) :=
(hd.symm.closure_left hs).symm

lemma is_closed.closure_eq {s : set α} (h : is_closed s) : closure s = s :=
subset.antisymm (closure_minimal (subset.refl s) h) subset_closure

lemma is_closed.closure_subset {s : set α} (hs : is_closed s) : closure s ⊆ s :=
closure_minimal (subset.refl _) hs

lemma is_closed.closure_subset_iff {s t : set α} (h₁ : is_closed t) :
  closure s ⊆ t ↔ s ⊆ t :=
⟨subset.trans subset_closure, assume h, closure_minimal h h₁⟩

lemma is_closed.mem_iff_closure_subset {s : set α} (hs : is_closed s) {x : α} :
  x ∈ s ↔ closure ({x} : set α) ⊆ s :=
(hs.closure_subset_iff.trans set.singleton_subset_iff).symm

@[mono] lemma closure_mono {s t : set α} (h : s ⊆ t) : closure s ⊆ closure t :=
closure_minimal (subset.trans h subset_closure) is_closed_closure

lemma monotone_closure (α : Type*) [topological_space α] : monotone (@closure α _) :=
λ _ _, closure_mono

lemma diff_subset_closure_iff {s t : set α} :
  s \ t ⊆ closure t ↔ s ⊆ closure t :=
by rw [diff_subset_iff, union_eq_self_of_subset_left subset_closure]

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

@[simp] lemma closure_nonempty_iff {s : set α} : (closure s).nonempty ↔ s.nonempty :=
by simp only [nonempty_iff_ne_empty, ne.def, closure_empty_iff]

alias closure_nonempty_iff ↔ set.nonempty.of_closure set.nonempty.closure

@[simp] lemma closure_univ : closure (univ : set α) = univ :=
is_closed_univ.closure_eq

@[simp] lemma closure_closure {s : set α} : closure (closure s) = closure s :=
is_closed_closure.closure_eq

@[simp] lemma closure_union {s t : set α} : closure (s ∪ t) = closure s ∪ closure t :=
subset.antisymm
  (closure_minimal (union_subset_union subset_closure subset_closure) $
    is_closed.union is_closed_closure is_closed_closure)
  ((monotone_closure α).le_map_sup s t)

@[simp] lemma finset.closure_bUnion {ι : Type*} (s : finset ι) (f : ι → set α) :
  closure (⋃ i ∈ s, f i) = ⋃ i ∈ s, closure (f i) :=
begin
  classical,
  refine s.induction_on (by simp) _,
  intros i s h₁ h₂,
  simp [h₂],
end

@[simp] lemma closure_Union {ι : Type*} [finite ι] (f : ι → set α) :
  closure (⋃ i, f i) = ⋃ i, closure (f i) :=
by { casesI nonempty_fintype ι, convert finset.univ.closure_bUnion f; simp }

lemma interior_subset_closure {s : set α} : interior s ⊆ closure s :=
subset.trans interior_subset subset_closure

lemma closure_eq_compl_interior_compl {s : set α} : closure s = (interior sᶜ)ᶜ :=
begin
  rw [interior, closure, compl_sUnion, compl_image_set_of],
  simp only [compl_subset_compl, is_open_compl_iff],
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
  let ⟨x, hc, hs⟩ := (H _ h₁.is_open_compl nc) in hc (h₂ hs)⟩

lemma closure_inter_open_nonempty_iff {s t : set α} (h : is_open t) :
  (closure s ∩ t).nonempty ↔ (s ∩ t).nonempty :=
⟨λ ⟨x, hxcs, hxt⟩, inter_comm t s ▸ mem_closure_iff.1 hxcs t h hxt,
  λ h, h.mono $ inf_le_inf_right t subset_closure⟩

lemma filter.le_lift'_closure (l : filter α) : l ≤ l.lift' closure :=
le_lift'.2 $ λ s hs, mem_of_superset hs subset_closure

lemma filter.has_basis.lift'_closure {l : filter α} {p : ι → Prop} {s : ι → set α}
  (h : l.has_basis p s) :
  (l.lift' closure).has_basis p (λ i, closure (s i)) :=
h.lift' (monotone_closure α)

lemma filter.has_basis.lift'_closure_eq_self {l : filter α} {p : ι → Prop} {s : ι → set α}
  (h : l.has_basis p s) (hc : ∀ i, p i → is_closed (s i)) :
  l.lift' closure = l :=
le_antisymm (h.ge_iff.2 $ λ i hi, (hc i hi).closure_eq ▸ mem_lift' (h.mem_of_mem hi))
  l.le_lift'_closure

@[simp] lemma filter.lift'_closure_eq_bot {l : filter α} : l.lift' closure = ⊥ ↔ l = ⊥ :=
⟨λ h, bot_unique $ h ▸ l.le_lift'_closure,
  λ h, h.symm ▸ by rw [lift'_bot (monotone_closure _), closure_empty, principal_empty]⟩

/-- A set is dense in a topological space if every point belongs to its closure. -/
def dense (s : set α) : Prop := ∀ x, x ∈ closure s

lemma dense_iff_closure_eq {s : set α} : dense s ↔ closure s = univ :=
eq_univ_iff_forall.symm

lemma dense.closure_eq {s : set α} (h : dense s) : closure s = univ :=
dense_iff_closure_eq.mp h

lemma interior_eq_empty_iff_dense_compl {s : set α} : interior s = ∅ ↔ dense sᶜ :=
by rw [dense_iff_closure_eq, closure_compl, compl_univ_iff]

lemma dense.interior_compl {s : set α} (h : dense s) : interior sᶜ = ∅ :=
interior_eq_empty_iff_dense_compl.2 $ by rwa compl_compl

/-- The closure of a set `s` is dense if and only if `s` is dense. -/
@[simp] lemma dense_closure {s : set α} : dense (closure s) ↔ dense s :=
by rw [dense, dense, closure_closure]

alias dense_closure ↔ dense.of_closure dense.closure

@[simp] lemma dense_univ : dense (univ : set α) := λ x, subset_closure trivial

/-- A set is dense if and only if it has a nonempty intersection with each nonempty open set. -/
lemma dense_iff_inter_open {s : set α} :
  dense s ↔ ∀ U, is_open U → U.nonempty → (U ∩ s).nonempty :=
begin
  split ; intro h,
  { rintros U U_op ⟨x, x_in⟩,
    exact mem_closure_iff.1 (by simp only [h.closure_eq]) U U_op x_in },
  { intro x,
    rw mem_closure_iff,
    intros U U_op x_in,
    exact h U U_op ⟨_, x_in⟩ },
end

alias dense_iff_inter_open ↔ dense.inter_open_nonempty _

lemma dense.exists_mem_open {s : set α} (hs : dense s) {U : set α} (ho : is_open U)
  (hne : U.nonempty) :
  ∃ x ∈ s, x ∈ U :=
let ⟨x, hx⟩ := hs.inter_open_nonempty U ho hne in ⟨x, hx.2, hx.1⟩

lemma dense.nonempty_iff {s : set α} (hs : dense s) :
  s.nonempty ↔ nonempty α :=
⟨λ ⟨x, hx⟩, ⟨x⟩, λ ⟨x⟩,
  let ⟨y, hy⟩ := hs.inter_open_nonempty _ is_open_univ ⟨x, trivial⟩ in ⟨y, hy.2⟩⟩

lemma dense.nonempty [h : nonempty α] {s : set α} (hs : dense s) : s.nonempty :=
hs.nonempty_iff.2 h

@[mono]
lemma dense.mono {s₁ s₂ : set α} (h : s₁ ⊆ s₂) (hd : dense s₁) : dense s₂ :=
λ x, closure_mono h (hd x)

/-- Complement to a singleton is dense if and only if the singleton is not an open set. -/
lemma dense_compl_singleton_iff_not_open {x : α} : dense ({x}ᶜ : set α) ↔ ¬is_open ({x} : set α) :=
begin
  fsplit,
  { intros hd ho,
    exact (hd.inter_open_nonempty _ ho (singleton_nonempty _)).ne_empty (inter_compl_self _) },
  { refine λ ho, dense_iff_inter_open.2 (λ U hU hne, inter_compl_nonempty_iff.2 $ λ hUx, _),
    obtain rfl : U = {x}, from eq_singleton_iff_nonempty_unique_mem.2 ⟨hne, hUx⟩,
    exact ho hU }
end

/-!
### Frontier of a set
-/

/-- The frontier of a set is the set of points between the closure and interior. -/
def frontier (s : set α) : set α := closure s \ interior s

@[simp] lemma closure_diff_interior (s : set α) : closure s \ interior s = frontier s := rfl

@[simp] lemma closure_diff_frontier (s : set α) : closure s \ frontier s = interior s :=
by rw [frontier, diff_diff_right_self, inter_eq_self_of_subset_right interior_subset_closure]

@[simp] lemma self_diff_frontier (s : set α) : s \ frontier s = interior s :=
by rw [frontier, diff_diff_right, diff_eq_empty.2 subset_closure,
  inter_eq_self_of_subset_right interior_subset, empty_union]

lemma frontier_eq_closure_inter_closure {s : set α} :
  frontier s = closure s ∩ closure sᶜ :=
by rw [closure_compl, frontier, diff_eq]

lemma frontier_subset_closure {s : set α} : frontier s ⊆ closure s := diff_subset _ _

lemma is_closed.frontier_subset (hs : is_closed s) : frontier s ⊆ s :=
frontier_subset_closure.trans hs.closure_eq.subset

lemma frontier_closure_subset {s : set α} : frontier (closure s) ⊆ frontier s :=
diff_subset_diff closure_closure.subset $ interior_mono subset_closure

lemma frontier_interior_subset {s : set α} : frontier (interior s) ⊆ frontier s :=
diff_subset_diff (closure_mono interior_subset) interior_interior.symm.subset

/-- The complement of a set has the same frontier as the original set. -/
@[simp] lemma frontier_compl (s : set α) : frontier sᶜ = frontier s :=
by simp only [frontier_eq_closure_inter_closure, compl_compl, inter_comm]

@[simp] lemma frontier_univ : frontier (univ : set α) = ∅ := by simp [frontier]

@[simp] lemma frontier_empty : frontier (∅ : set α) = ∅ := by simp [frontier]

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
by rw [frontier, hs.interior_eq]

lemma is_open.inter_frontier_eq {s : set α} (hs : is_open s) : s ∩ frontier s = ∅ :=
by rw [hs.frontier_eq, inter_diff_self]

/-- The frontier of a set is closed. -/
lemma is_closed_frontier {s : set α} : is_closed (frontier s) :=
by rw frontier_eq_closure_inter_closure; exact is_closed.inter is_closed_closure is_closed_closure

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

lemma closure_eq_interior_union_frontier (s : set α) : closure s = interior s ∪ frontier s :=
(union_diff_cancel interior_subset_closure).symm

lemma closure_eq_self_union_frontier (s : set α) : closure s = s ∪ frontier s :=
(union_diff_cancel' interior_subset subset_closure).symm

lemma disjoint.frontier_left (ht : is_open t) (hd : disjoint s t) : disjoint (frontier s) t :=
subset_compl_iff_disjoint_right.1 $ frontier_subset_closure.trans $ closure_minimal
  (disjoint_left.1 hd) $ is_closed_compl_iff.2 ht

lemma disjoint.frontier_right (hs : is_open s) (hd : disjoint s t) : disjoint s (frontier t) :=
(hd.symm.frontier_left hs).symm

lemma frontier_eq_inter_compl_interior {s : set α} :
  frontier s = (interior s)ᶜ ∩ (interior (sᶜ))ᶜ :=
by { rw [←frontier_compl, ←closure_compl], refl }

lemma compl_frontier_eq_union_interior {s : set α} :
  (frontier s)ᶜ = interior s ∪ interior sᶜ :=
begin
  rw frontier_eq_inter_compl_interior,
  simp only [compl_inter, compl_compl],
end

/-!
### Neighborhoods
-/

/-- A set is called a neighborhood of `a` if it contains an open set around `a`. The set of all
neighborhoods of `a` forms a filter, the neighborhood filter at `a`, is here defined as the
infimum over the principal filters of all open sets containing `a`. -/
@[irreducible] def nhds (a : α) : filter α := (⨅ s ∈ {s : set α | a ∈ s ∧ is_open s}, 𝓟 s)

localized "notation (name := nhds) `𝓝` := nhds" in topology

/-- The "neighborhood within" filter. Elements of `𝓝[s] a` are sets containing the
intersection of `s` and a neighborhood of `a`. -/
def nhds_within (a : α) (s : set α) : filter α := 𝓝 a ⊓ 𝓟 s

localized "notation (name := nhds_within) `𝓝[` s `] ` x:100 := nhds_within x s" in topology
localized "notation (name := nhds_within.ne) `𝓝[≠] ` x:100 := nhds_within x {x}ᶜ" in topology
localized "notation (name := nhds_within.ge) `𝓝[≥] ` x:100 := nhds_within x (set.Ici x)" in topology
localized "notation (name := nhds_within.le) `𝓝[≤] ` x:100 := nhds_within x (set.Iic x)" in topology
localized "notation (name := nhds_within.gt) `𝓝[>] ` x:100 := nhds_within x (set.Ioi x)" in topology
localized "notation (name := nhds_within.lt) `𝓝[<] ` x:100 := nhds_within x (set.Iio x)" in topology

lemma nhds_def (a : α) : 𝓝 a = (⨅ s ∈ {s : set α | a ∈ s ∧ is_open s}, 𝓟 s) := by rw nhds

lemma nhds_def' (a : α) : 𝓝 a = ⨅ (s : set α) (hs : is_open s) (ha : a ∈ s), 𝓟 s :=
by simp only [nhds_def, mem_set_of_eq, and_comm (a ∈ _), infi_and]

/-- The open sets containing `a` are a basis for the neighborhood filter. See `nhds_basis_opens'`
for a variant using open neighborhoods instead. -/
lemma nhds_basis_opens (a : α) : (𝓝 a).has_basis (λ s : set α, a ∈ s ∧ is_open s) (λ s, s) :=
begin
  rw nhds_def,
  exact has_basis_binfi_principal
    (λ s ⟨has, hs⟩ t ⟨hat, ht⟩, ⟨s ∩ t, ⟨⟨has, hat⟩, is_open.inter hs ht⟩,
      ⟨inter_subset_left _ _, inter_subset_right _ _⟩⟩)
    ⟨univ, ⟨mem_univ a, is_open_univ⟩⟩
end

lemma nhds_basis_closeds (a : α) : (𝓝 a).has_basis (λ s : set α, a ∉ s ∧ is_closed s) compl :=
⟨λ t, (nhds_basis_opens a).mem_iff.trans $ compl_surjective.exists.trans $
  by simp only [is_open_compl_iff, mem_compl_iff]⟩

/-- A filter lies below the neighborhood filter at `a` iff it contains every open set around `a`. -/
lemma le_nhds_iff {f a} : f ≤ 𝓝 a ↔ ∀ s : set α, a ∈ s → is_open s → s ∈ f :=
by simp [nhds_def]

/-- To show a filter is above the neighborhood filter at `a`, it suffices to show that it is above
the principal filter of some open set `s` containing `a`. -/
lemma nhds_le_of_le {f a} {s : set α} (h : a ∈ s) (o : is_open s) (sf : 𝓟 s ≤ f) : 𝓝 a ≤ f :=
by rw nhds_def; exact infi_le_of_le s (infi_le_of_le ⟨h, o⟩ sf)

lemma mem_nhds_iff {a : α} {s : set α} :
  s ∈ 𝓝 a ↔ ∃ t ⊆ s, is_open t ∧ a ∈ t :=
(nhds_basis_opens a).mem_iff.trans
  ⟨λ ⟨t, ⟨hat, ht⟩, hts⟩, ⟨t, hts, ht, hat⟩, λ ⟨t, hts, ht, hat⟩, ⟨t, ⟨hat, ht⟩, hts⟩⟩

/-- A predicate is true in a neighborhood of `a` iff it is true for all the points in an open set
containing `a`. -/
lemma eventually_nhds_iff {a : α} {p : α → Prop} :
  (∀ᶠ x in 𝓝 a, p x) ↔ ∃ (t : set α), (∀ x ∈ t, p x) ∧ is_open t ∧ a ∈ t :=
mem_nhds_iff.trans $ by simp only [subset_def, exists_prop, mem_set_of_eq]

lemma map_nhds {a : α} {f : α → β} :
  map f (𝓝 a) = (⨅ s ∈ {s : set α | a ∈ s ∧ is_open s}, 𝓟 (image f s)) :=
((nhds_basis_opens a).map f).eq_binfi

lemma mem_of_mem_nhds {a : α} {s : set α} : s ∈ 𝓝 a → a ∈ s :=
λ H, let ⟨t, ht, _, hs⟩ := mem_nhds_iff.1 H in ht hs

/-- If a predicate is true in a neighborhood of `a`, then it is true for `a`. -/
lemma filter.eventually.self_of_nhds {p : α → Prop} {a : α}
  (h : ∀ᶠ y in 𝓝 a, p y) : p a :=
mem_of_mem_nhds h

lemma is_open.mem_nhds {a : α} {s : set α} (hs : is_open s) (ha : a ∈ s) :
  s ∈ 𝓝 a :=
mem_nhds_iff.2 ⟨s, subset.refl _, hs, ha⟩

lemma is_open.mem_nhds_iff {a : α} {s : set α} (hs : is_open s) : s ∈ 𝓝 a ↔ a ∈ s :=
⟨mem_of_mem_nhds, λ ha, mem_nhds_iff.2 ⟨s, subset.refl _, hs, ha⟩⟩

lemma is_closed.compl_mem_nhds {a : α} {s : set α} (hs : is_closed s) (ha : a ∉ s) : sᶜ ∈ 𝓝 a :=
hs.is_open_compl.mem_nhds (mem_compl ha)

lemma is_open.eventually_mem {a : α} {s : set α} (hs : is_open s) (ha : a ∈ s) :
  ∀ᶠ x in 𝓝 a, x ∈ s :=
is_open.mem_nhds hs ha

/-- The open neighborhoods of `a` are a basis for the neighborhood filter. See `nhds_basis_opens`
for a variant using open sets around `a` instead. -/
lemma nhds_basis_opens' (a : α) : (𝓝 a).has_basis (λ s : set α, s ∈ 𝓝 a ∧ is_open s) (λ x, x) :=
begin
  convert nhds_basis_opens a,
  ext s,
  exact and.congr_left_iff.2 is_open.mem_nhds_iff
end

/-- If `U` is a neighborhood of each point of a set `s` then it is a neighborhood of `s`:
it contains an open set containing `s`. -/
lemma exists_open_set_nhds {s U : set α} (h : ∀ x ∈ s, U ∈ 𝓝 x) :
  ∃ V : set α, s ⊆ V ∧ is_open V ∧ V ⊆ U :=
begin
  have := λ x hx, (nhds_basis_opens x).mem_iff.1 (h x hx),
  choose! Z hZ hZU using this, choose hZmem hZo using hZ,
  exact ⟨⋃ x ∈ s, Z x, λ x hx, mem_bUnion hx (hZmem x hx), is_open_bUnion hZo, Union₂_subset hZU⟩
end

/-- If `U` is a neighborhood of each point of a set `s` then it is a neighborhood of s:
it contains an open set containing `s`. -/
lemma exists_open_set_nhds' {s U : set α} (h : U ∈ ⨆ x ∈ s, 𝓝 x) :
  ∃ V : set α, s ⊆ V ∧ is_open V ∧ V ⊆ U :=
exists_open_set_nhds (by simpa using h)

/-- If a predicate is true in a neighbourhood of `a`, then for `y` sufficiently close
to `a` this predicate is true in a neighbourhood of `y`. -/
lemma filter.eventually.eventually_nhds {p : α → Prop} {a : α} (h : ∀ᶠ y in 𝓝 a, p y) :
  ∀ᶠ y in 𝓝 a, ∀ᶠ x in 𝓝 y, p x :=
let ⟨t, htp, hto, ha⟩ := eventually_nhds_iff.1 h in
eventually_nhds_iff.2 ⟨t, λ x hx, eventually_nhds_iff.2 ⟨t, htp, hto, hx⟩, hto, ha⟩

@[simp] lemma eventually_eventually_nhds {p : α → Prop} {a : α} :
  (∀ᶠ y in 𝓝 a, ∀ᶠ x in 𝓝 y, p x) ↔ ∀ᶠ x in 𝓝 a, p x :=
⟨λ h, h.self_of_nhds, λ h, h.eventually_nhds⟩

@[simp] lemma frequently_frequently_nhds {p : α → Prop} {a : α} :
  (∃ᶠ y in 𝓝 a, ∃ᶠ x in 𝓝 y, p x) ↔ (∃ᶠ x in 𝓝 a, p x) :=
begin
  rw ← not_iff_not,
  simp_rw not_frequently,
  exact eventually_eventually_nhds,
end

@[simp] lemma eventually_mem_nhds {s : set α} {a : α} :
  (∀ᶠ x in 𝓝 a, s ∈ 𝓝 x) ↔ s ∈ 𝓝 a :=
eventually_eventually_nhds

@[simp] lemma nhds_bind_nhds : (𝓝 a).bind 𝓝 = 𝓝 a := filter.ext $ λ s, eventually_eventually_nhds

@[simp] lemma eventually_eventually_eq_nhds {f g : α → β} {a : α} :
  (∀ᶠ y in 𝓝 a, f =ᶠ[𝓝 y] g) ↔ f =ᶠ[𝓝 a] g :=
eventually_eventually_nhds

lemma filter.eventually_eq.eq_of_nhds {f g : α → β} {a : α} (h : f =ᶠ[𝓝 a] g) : f a = g a :=
h.self_of_nhds

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
all_mem_nhds _ _ (λ s t ssubt h, mem_of_superset h (hf s t ssubt))

theorem tendsto_nhds {f : β → α} {l : filter β} {a : α} :
  tendsto f l (𝓝 a) ↔ (∀ s, is_open s → a ∈ s → f ⁻¹' s ∈ l) :=
all_mem_nhds_filter _ _ (λ s t h, preimage_mono h) _

lemma tendsto_at_top_nhds [nonempty β] [semilattice_sup β] {f : β → α} {a : α} :
  (tendsto f at_top (𝓝 a)) ↔ ∀ U : set α, a ∈ U → is_open U → ∃ N, ∀ n, N ≤ n → f n ∈ U :=
(at_top_basis.tendsto_iff (nhds_basis_opens a)).trans $
  by simp only [and_imp, exists_prop, true_and, mem_Ici, ge_iff_le]

lemma tendsto_const_nhds {a : α} {f : filter β} : tendsto (λb:β, a) f (𝓝 a) :=
tendsto_nhds.mpr $ assume s hs ha, univ_mem' $ assume _, ha

lemma tendsto_at_top_of_eventually_const {ι : Type*} [semilattice_sup ι] [nonempty ι]
  {x : α} {u : ι → α} {i₀ : ι} (h : ∀ i ≥ i₀, u i = x) : tendsto u at_top (𝓝 x) :=
tendsto.congr' (eventually_eq.symm (eventually_at_top.mpr ⟨i₀, h⟩)) tendsto_const_nhds

lemma tendsto_at_bot_of_eventually_const {ι : Type*} [semilattice_inf ι] [nonempty ι]
  {x : α} {u : ι → α} {i₀ : ι} (h : ∀ i ≤ i₀, u i = x) : tendsto u at_bot (𝓝 x) :=
tendsto.congr' (eventually_eq.symm (eventually_at_bot.mpr ⟨i₀, h⟩)) tendsto_const_nhds

lemma pure_le_nhds : pure ≤ (𝓝 : α → filter α) :=
assume a s hs, mem_pure.2 $ mem_of_mem_nhds hs

lemma tendsto_pure_nhds {α : Type*} [topological_space β] (f : α → β) (a : α) :
  tendsto f (pure a) (𝓝 (f a)) :=
(tendsto_pure_pure f a).mono_right (pure_le_nhds _)

lemma order_top.tendsto_at_top_nhds {α : Type*} [partial_order α] [order_top α]
  [topological_space β] (f : α → β) : tendsto f at_top (𝓝 $ f ⊤) :=
(tendsto_at_top_pure f).mono_right (pure_le_nhds _)

@[simp] instance nhds_ne_bot {a : α} : ne_bot (𝓝 a) :=
ne_bot_of_le (pure_le_nhds a)

/-!
### Cluster points

In this section we define [cluster points](https://en.wikipedia.org/wiki/Limit_point)
(also known as limit points and accumulation points) of a filter and of a sequence.
-/

/-- A point `x` is a cluster point of a filter `F` if `𝓝 x ⊓ F ≠ ⊥`. Also known as
an accumulation point or a limit point, but beware that terminology varies. This
is *not* the same as asking `𝓝[≠] x ⊓ F ≠ ⊥`. See `mem_closure_iff_cluster_pt` in particular. -/
def cluster_pt (x : α) (F : filter α) : Prop := ne_bot (𝓝 x ⊓ F)

lemma cluster_pt.ne_bot {x : α} {F : filter α} (h : cluster_pt x F) : ne_bot (𝓝 x ⊓ F) := h

lemma filter.has_basis.cluster_pt_iff {ιa ιF} {pa : ιa → Prop} {sa : ιa → set α}
  {pF : ιF → Prop} {sF : ιF → set α} {F : filter α}
  (ha : (𝓝 a).has_basis pa sa) (hF : F.has_basis pF sF) :
  cluster_pt a F ↔ ∀ ⦃i⦄ (hi : pa i) ⦃j⦄ (hj : pF j), (sa i ∩ sF j).nonempty :=
ha.inf_basis_ne_bot_iff hF

lemma cluster_pt_iff {x : α} {F : filter α} :
  cluster_pt x F ↔ ∀ ⦃U : set α⦄ (hU : U ∈ 𝓝 x) ⦃V⦄ (hV : V ∈ F), (U ∩ V).nonempty :=
inf_ne_bot_iff

/-- `x` is a cluster point of a set `s` if every neighbourhood of `x` meets `s` on a nonempty
set. See also `mem_closure_iff_cluster_pt`. -/
lemma cluster_pt_principal_iff {x : α} {s : set α} :
  cluster_pt x (𝓟 s) ↔ ∀ U ∈ 𝓝 x, (U ∩ s).nonempty :=
inf_principal_ne_bot_iff

lemma cluster_pt_principal_iff_frequently {x : α} {s : set α} :
  cluster_pt x (𝓟 s) ↔ ∃ᶠ y in 𝓝 x, y ∈ s :=
by simp only [cluster_pt_principal_iff, frequently_iff, set.nonempty, exists_prop, mem_inter_iff]

lemma cluster_pt.of_le_nhds {x : α} {f : filter α} (H : f ≤ 𝓝 x) [ne_bot f] : cluster_pt x f :=
by rwa [cluster_pt, inf_eq_right.mpr H]

lemma cluster_pt.of_le_nhds' {x : α} {f : filter α} (H : f ≤ 𝓝 x) (hf : ne_bot f) :
  cluster_pt x f :=
cluster_pt.of_le_nhds H

lemma cluster_pt.of_nhds_le {x : α} {f : filter α} (H : 𝓝 x ≤ f) : cluster_pt x f :=
by simp only [cluster_pt, inf_eq_left.mpr H, nhds_ne_bot]

lemma cluster_pt.mono {x : α} {f g : filter α} (H : cluster_pt x f) (h : f ≤ g) :
  cluster_pt x g :=
⟨ne_bot_of_le_ne_bot H.ne $ inf_le_inf_left _ h⟩

lemma cluster_pt.of_inf_left {x : α} {f g : filter α} (H : cluster_pt x $ f ⊓ g) :
  cluster_pt x f :=
H.mono inf_le_left

lemma cluster_pt.of_inf_right {x : α} {f g : filter α} (H : cluster_pt x $ f ⊓ g) :
  cluster_pt x g :=
H.mono inf_le_right

lemma ultrafilter.cluster_pt_iff {x : α} {f : ultrafilter α} : cluster_pt x f ↔ ↑f ≤ 𝓝 x :=
⟨f.le_of_inf_ne_bot', λ h, cluster_pt.of_le_nhds h⟩

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

/--A point `x` is an accumulation point of a filter `F` if `𝓝[≠] x ⊓ F ≠ ⊥`.-/
def acc_pt (x : α) (F : filter α) : Prop := ne_bot (𝓝[≠] x ⊓ F)

lemma acc_iff_cluster (x : α) (F : filter α) : acc_pt x F ↔ cluster_pt x (𝓟 {x}ᶜ ⊓ F) :=
by rw [acc_pt, nhds_within, cluster_pt, inf_assoc]

/-- `x` is an accumulation point of a set `C` iff it is a cluster point of `C ∖ {x}`.-/
lemma acc_principal_iff_cluster (x : α) (C : set α) :
  acc_pt x (𝓟 C) ↔ cluster_pt x (𝓟(C \ {x})) :=
by rw [acc_iff_cluster, inf_principal, inter_comm]; refl

/-- `x` is an accumulation point of a set `C` iff every neighborhood
of `x` contains a point of `C` other than `x`. -/
lemma acc_pt_iff_nhds (x : α) (C : set α) : acc_pt x (𝓟 C) ↔ ∀ U ∈ 𝓝 x, ∃ y ∈ U ∩ C, y ≠ x :=
by simp [acc_principal_iff_cluster, cluster_pt_principal_iff, set.nonempty, exists_prop,
  and_assoc, and_comm (¬ _ = x)]

/-- `x` is an accumulation point of a set `C` iff
there are points near `x` in `C` and different from `x`.-/
lemma acc_pt_iff_frequently (x : α) (C : set α) : acc_pt x (𝓟 C) ↔ ∃ᶠ y in 𝓝 x, y ≠ x ∧ y ∈ C :=
by simp [acc_principal_iff_cluster, cluster_pt_principal_iff_frequently, and_comm]

/-- If `x` is an accumulation point of `F` and `F ≤ G`, then
`x` is an accumulation point of `D. -/
lemma acc_pt.mono {x : α} {F G : filter α} (h : acc_pt x F) (hFG : F ≤ G) : acc_pt x G :=
⟨ne_bot_of_le_ne_bot h.ne (inf_le_inf_left _ hFG)⟩

/-!
### Interior, closure and frontier in terms of neighborhoods
-/

lemma interior_eq_nhds' {s : set α} : interior s = {a | s ∈ 𝓝 a} :=
set.ext $ λ x, by simp only [mem_interior, mem_nhds_iff, mem_set_of_eq]

lemma interior_eq_nhds {s : set α} : interior s = {a | 𝓝 a ≤ 𝓟 s} :=
interior_eq_nhds'.trans $ by simp only [le_principal_iff]

lemma mem_interior_iff_mem_nhds {s : set α} {a : α} :
  a ∈ interior s ↔ s ∈ 𝓝 a :=
by rw [interior_eq_nhds', mem_set_of_eq]

@[simp] lemma interior_mem_nhds {s : set α} {a : α} :
  interior s ∈ 𝓝 a ↔ s ∈ 𝓝 a :=
⟨λ h, mem_of_superset h interior_subset,
  λ h, is_open.mem_nhds is_open_interior (mem_interior_iff_mem_nhds.2 h)⟩

lemma interior_set_of_eq {p : α → Prop} :
  interior {x | p x} = {x | ∀ᶠ y in 𝓝 x, p y} :=
interior_eq_nhds'

lemma is_open_set_of_eventually_nhds {p : α → Prop} :
  is_open {x | ∀ᶠ y in 𝓝 x, p y} :=
by simp only [← interior_set_of_eq, is_open_interior]

lemma subset_interior_iff_nhds {s V : set α} : s ⊆ interior V ↔ ∀ x ∈ s, V ∈ 𝓝 x :=
show (∀ x, x ∈ s →  x ∈ _) ↔ _, by simp_rw mem_interior_iff_mem_nhds

lemma is_open_iff_nhds {s : set α} : is_open s ↔ ∀a∈s, 𝓝 a ≤ 𝓟 s :=
calc is_open s ↔ s ⊆ interior s : subset_interior_iff_is_open.symm
  ... ↔ (∀a∈s, 𝓝 a ≤ 𝓟 s) : by rw [interior_eq_nhds]; refl

lemma is_open_iff_mem_nhds {s : set α} : is_open s ↔ ∀a∈s, s ∈ 𝓝 a :=
is_open_iff_nhds.trans $ forall_congr $ λ _, imp_congr_right $ λ _, le_principal_iff

/-- A set `s` is open iff for every point `x` in `s` and every `y` close to `x`, `y` is in `s`. -/
lemma is_open_iff_eventually {s : set α} : is_open s ↔ ∀ x, x ∈ s → ∀ᶠ y in 𝓝 x, y ∈ s :=
is_open_iff_mem_nhds

theorem is_open_iff_ultrafilter {s : set α} :
  is_open s ↔ (∀ (x ∈ s) (l : ultrafilter α), ↑l ≤ 𝓝 x → s ∈ l) :=
by simp_rw [is_open_iff_mem_nhds, ← mem_iff_ultrafilter]

lemma is_open_singleton_iff_nhds_eq_pure (a : α) :
  is_open ({a} : set α) ↔ 𝓝 a = pure a :=
begin
  split,
  { intros h,
    apply le_antisymm _ (pure_le_nhds a),
    rw le_pure_iff,
    exact h.mem_nhds (mem_singleton a) },
  { intros h,
    simp [is_open_iff_nhds, h] }
end

lemma is_open_singleton_iff_punctured_nhds {α : Type*} [topological_space α] (a : α) :
  is_open ({a} : set α) ↔ (𝓝[≠] a) = ⊥ :=
by rw [is_open_singleton_iff_nhds_eq_pure, nhds_within, ← mem_iff_inf_principal_compl,
        ← le_pure_iff, nhds_ne_bot.le_pure_iff]

lemma mem_closure_iff_frequently {s : set α} {a : α} : a ∈ closure s ↔ ∃ᶠ x in 𝓝 a, x ∈ s :=
by rw [filter.frequently, filter.eventually, ← mem_interior_iff_mem_nhds,
  closure_eq_compl_interior_compl]; refl

alias mem_closure_iff_frequently ↔ _ filter.frequently.mem_closure

/-- A set `s` is closed iff for every point `x`, if there is a point `y` close to `x` that belongs
to `s` then `x` is in `s`. -/
lemma is_closed_iff_frequently {s : set α} : is_closed s ↔ ∀ x, (∃ᶠ y in 𝓝 x, y ∈ s) → x ∈ s :=
begin
  rw ← closure_subset_iff_is_closed,
  apply forall_congr (λ x, _),
  rw mem_closure_iff_frequently
end

/-- The set of cluster points of a filter is closed. In particular, the set of limit points
of a sequence is closed. -/
lemma is_closed_set_of_cluster_pt {f : filter α} : is_closed {x | cluster_pt x f} :=
begin
  simp only [cluster_pt, inf_ne_bot_iff_frequently_left, set_of_forall, imp_iff_not_or],
  refine is_closed_Inter (λ p, is_closed.union _ _); apply is_closed_compl_iff.2,
  exacts [is_open_set_of_eventually_nhds, is_open_const]
end

theorem mem_closure_iff_cluster_pt {s : set α} {a : α} : a ∈ closure s ↔ cluster_pt a (𝓟 s) :=
mem_closure_iff_frequently.trans cluster_pt_principal_iff_frequently.symm

lemma mem_closure_iff_nhds_ne_bot {s : set α} : a ∈ closure s ↔ 𝓝 a ⊓ 𝓟 s ≠ ⊥ :=
mem_closure_iff_cluster_pt.trans ne_bot_iff

lemma mem_closure_iff_nhds_within_ne_bot {s : set α} {x : α} :
  x ∈ closure s ↔ ne_bot (𝓝[s] x) :=
mem_closure_iff_cluster_pt

/-- If `x` is not an isolated point of a topological space, then `{x}ᶜ` is dense in the whole
space. -/
lemma dense_compl_singleton (x : α) [ne_bot (𝓝[≠] x)] : dense ({x}ᶜ : set α) :=
begin
  intro y,
  unfreezingI { rcases eq_or_ne y x with rfl|hne },
  { rwa mem_closure_iff_nhds_within_ne_bot },
  { exact subset_closure hne }
end

/-- If `x` is not an isolated point of a topological space, then the closure of `{x}ᶜ` is the whole
space. -/
@[simp] lemma closure_compl_singleton (x : α) [ne_bot (𝓝[≠] x)] :
  closure {x}ᶜ = (univ : set α) :=
(dense_compl_singleton x).closure_eq

/-- If `x` is not an isolated point of a topological space, then the interior of `{x}` is empty. -/
@[simp] lemma interior_singleton (x : α) [ne_bot (𝓝[≠] x)] :
  interior {x} = (∅ : set α) :=
interior_eq_empty_iff_dense_compl.2 (dense_compl_singleton x)

lemma not_is_open_singleton (x : α) [ne_bot (𝓝[≠] x)] : ¬ is_open ({x} : set α) :=
dense_compl_singleton_iff_not_open.1 (dense_compl_singleton x)

lemma closure_eq_cluster_pts {s : set α} : closure s = {a | cluster_pt a (𝓟 s)} :=
set.ext $ λ x, mem_closure_iff_cluster_pt

theorem mem_closure_iff_nhds {s : set α} {a : α} :
  a ∈ closure s ↔ ∀ t ∈ 𝓝 a, (t ∩ s).nonempty :=
mem_closure_iff_cluster_pt.trans cluster_pt_principal_iff

theorem mem_closure_iff_nhds' {s : set α} {a : α} :
  a ∈ closure s ↔ ∀ t ∈ 𝓝 a, ∃ y : s, ↑y ∈ t :=
by simp only [mem_closure_iff_nhds, set.inter_nonempty_iff_exists_right,
              set_coe.exists, subtype.coe_mk]

theorem mem_closure_iff_comap_ne_bot {A : set α} {x : α} :
  x ∈ closure A ↔ ne_bot (comap (coe : A → α) (𝓝 x)) :=
by simp_rw [mem_closure_iff_nhds, comap_ne_bot_iff, set.inter_nonempty_iff_exists_right,
            set_coe.exists, subtype.coe_mk]

theorem mem_closure_iff_nhds_basis' {a : α} {p : ι → Prop} {s : ι → set α} (h : (𝓝 a).has_basis p s)
  {t : set α} :
  a ∈ closure t ↔ ∀ i, p i → (s i ∩ t).nonempty :=
mem_closure_iff_cluster_pt.trans $ (h.cluster_pt_iff (has_basis_principal _)).trans $
  by simp only [exists_prop, forall_const]

theorem mem_closure_iff_nhds_basis {a : α} {p : ι → Prop} {s : ι → set α} (h : (𝓝 a).has_basis p s)
  {t : set α} :
  a ∈ closure t ↔ ∀ i, p i → ∃ y ∈ t, y ∈ s i :=
(mem_closure_iff_nhds_basis' h).trans $
  by simp only [set.nonempty, mem_inter_iff, exists_prop, and_comm]

/-- `x` belongs to the closure of `s` if and only if some ultrafilter
  supported on `s` converges to `x`. -/
lemma mem_closure_iff_ultrafilter {s : set α} {x : α} :
  x ∈ closure s ↔ ∃ (u : ultrafilter α), s ∈ u ∧ ↑u ≤ 𝓝 x :=
by simp [closure_eq_cluster_pts, cluster_pt, ← exists_ultrafilter_iff, and.comm]

lemma is_closed_iff_cluster_pt {s : set α} : is_closed s ↔ ∀a, cluster_pt a (𝓟 s) → a ∈ s :=
calc is_closed s ↔ closure s ⊆ s : closure_subset_iff_is_closed.symm
  ... ↔ (∀a, cluster_pt a (𝓟 s) → a ∈ s) : by simp only [subset_def, mem_closure_iff_cluster_pt]

lemma is_closed_iff_nhds {s : set α} : is_closed s ↔ ∀ x, (∀ U ∈ 𝓝 x, (U ∩ s).nonempty) → x ∈ s :=
by simp_rw [is_closed_iff_cluster_pt, cluster_pt, inf_principal_ne_bot_iff]

lemma is_closed.interior_union_left {s t : set α} (h : is_closed s) :
  interior (s ∪ t) ⊆ s ∪ interior t :=
λ a ⟨u, ⟨⟨hu₁, hu₂⟩, ha⟩⟩, (classical.em (a ∈ s)).imp_right $ λ h, mem_interior.mpr
  ⟨u ∩ sᶜ, λ x hx, (hu₂ hx.1).resolve_left hx.2, is_open.inter hu₁ is_closed.is_open_compl, ⟨ha, h⟩⟩

lemma is_closed.interior_union_right {s t : set α} (h : is_closed t) :
  interior (s ∪ t) ⊆ interior s ∪ t :=
by simpa only [union_comm] using h.interior_union_left

lemma is_open.inter_closure {s t : set α} (h : is_open s) : s ∩ closure t ⊆ closure (s ∩ t) :=
compl_subset_compl.mp $ by simpa only [← interior_compl, compl_inter]
  using is_closed.interior_union_left h.is_closed_compl

lemma is_open.closure_inter {s t : set α} (h : is_open t) : closure s ∩ t ⊆ closure (s ∩ t) :=
by simpa only [inter_comm] using h.inter_closure

lemma dense.open_subset_closure_inter {s t : set α} (hs : dense s) (ht : is_open t) :
  t ⊆ closure (t ∩ s) :=
calc t = t ∩ closure s   : by rw [hs.closure_eq, inter_univ]
   ... ⊆ closure (t ∩ s) : ht.inter_closure

lemma mem_closure_of_mem_closure_union {s₁ s₂ : set α} {x : α} (h : x ∈ closure (s₁ ∪ s₂))
  (h₁ : s₁ᶜ ∈ 𝓝 x) : x ∈ closure s₂ :=
begin
  rw mem_closure_iff_nhds_ne_bot at *,
  rwa ← calc
    𝓝 x ⊓ principal (s₁ ∪ s₂) = 𝓝 x ⊓ (principal s₁ ⊔ principal s₂) : by rw sup_principal
    ... = (𝓝 x ⊓ principal s₁) ⊔ (𝓝 x ⊓ principal s₂) : inf_sup_left
    ... = ⊥ ⊔ 𝓝 x ⊓ principal s₂ : by rw inf_principal_eq_bot.mpr h₁
    ... = 𝓝 x ⊓ principal s₂ : bot_sup_eq
end

/-- The intersection of an open dense set with a dense set is a dense set. -/
lemma dense.inter_of_open_left {s t : set α} (hs : dense s) (ht : dense t) (hso : is_open s) :
  dense (s ∩ t) :=
λ x, (closure_minimal hso.inter_closure is_closed_closure) $
  by simp [hs.closure_eq, ht.closure_eq]

/-- The intersection of a dense set with an open dense set is a dense set. -/
lemma dense.inter_of_open_right {s t : set α} (hs : dense s) (ht : dense t) (hto : is_open t) :
  dense (s ∩ t) :=
inter_comm t s ▸ ht.inter_of_open_left hs hto

lemma dense.inter_nhds_nonempty {s t : set α} (hs : dense s) {x : α} (ht : t ∈ 𝓝 x) :
  (s ∩ t).nonempty :=
let ⟨U, hsub, ho, hx⟩ := mem_nhds_iff.1 ht in
  (hs.inter_open_nonempty U ho ⟨x, hx⟩).mono $ λ y hy, ⟨hy.2, hsub hy.1⟩

lemma closure_diff {s t : set α} : closure s \ closure t ⊆ closure (s \ t) :=
calc closure s \ closure t = (closure t)ᶜ ∩ closure s : by simp only [diff_eq, inter_comm]
  ... ⊆ closure ((closure t)ᶜ ∩ s) : (is_open_compl_iff.mpr $ is_closed_closure).inter_closure
  ... = closure (s \ closure t) : by simp only [diff_eq, inter_comm]
  ... ⊆ closure (s \ t) : closure_mono $ diff_subset_diff (subset.refl s) subset_closure

lemma filter.frequently.mem_of_closed {a : α} {s : set α} (h : ∃ᶠ x in 𝓝 a, x ∈ s)
  (hs : is_closed s) : a ∈ s :=
hs.closure_subset h.mem_closure

lemma is_closed.mem_of_frequently_of_tendsto {f : β → α} {b : filter β} {a : α} {s : set α}
  (hs : is_closed s) (h : ∃ᶠ x in b, f x ∈ s) (hf : tendsto f b (𝓝 a)) : a ∈ s :=
(hf.frequently $ show ∃ᶠ x in b, (λ y, y ∈ s) (f x), from h).mem_of_closed hs

lemma is_closed.mem_of_tendsto {f : β → α} {b : filter β} {a : α} {s : set α}
  [ne_bot b] (hs : is_closed s) (hf : tendsto f b (𝓝 a)) (h : ∀ᶠ x in b, f x ∈ s) : a ∈ s :=
hs.mem_of_frequently_of_tendsto h.frequently hf

lemma mem_closure_of_frequently_of_tendsto {f : β → α} {b : filter β} {a : α} {s : set α}
  (h : ∃ᶠ x in b, f x ∈ s) (hf : tendsto f b (𝓝 a)) : a ∈ closure s :=
filter.frequently.mem_closure $ hf.frequently h

lemma mem_closure_of_tendsto {f : β → α} {b : filter β} {a : α} {s : set α}
  [ne_bot b] (hf : tendsto f b (𝓝 a)) (h : ∀ᶠ x in b, f x ∈ s) : a ∈ closure s :=
mem_closure_of_frequently_of_tendsto h.frequently hf

/-- Suppose that `f` sends the complement to `s` to a single point `a`, and `l` is some filter.
Then `f` tends to `a` along `l` restricted to `s` if and only if it tends to `a` along `l`. -/
lemma tendsto_inf_principal_nhds_iff_of_forall_eq {f : β → α} {l : filter β} {s : set β}
  {a : α} (h : ∀ x ∉ s, f x = a) :
  tendsto f (l ⊓ 𝓟 s) (𝓝 a) ↔ tendsto f l (𝓝 a) :=
begin
  rw [tendsto_iff_comap, tendsto_iff_comap],
  replace h : 𝓟 sᶜ ≤ comap f (𝓝 a),
  { rintros U ⟨t, ht, htU⟩ x hx,
    have : f x ∈ t, from (h x hx).symm ▸ mem_of_mem_nhds ht,
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

/--
If `f` is a filter satisfying `ne_bot f`, then `Lim' f` is a limit of the filter, if it exists.
-/
def Lim' (f : filter α) [ne_bot f] : α := @Lim _ _ (nonempty_of_ne_bot f) f

/--
If `F` is an ultrafilter, then `filter.ultrafilter.Lim F` is a limit of the filter, if it exists.
Note that dot notation `F.Lim` can be used for `F : ultrafilter α`.
-/
def ultrafilter.Lim : ultrafilter α → α := λ F, Lim' F

/-- If `f` is a filter in `β` and `g : β → α` is a function, then `lim f` is a limit of `g` at `f`,
if it exists. -/
noncomputable def lim [nonempty α] (f : filter β) (g : β → α) : α :=
Lim (f.map g)

/-- If a filter `f` is majorated by some `𝓝 a`, then it is majorated by `𝓝 (Lim f)`. We formulate
this lemma with a `[nonempty α]` argument of `Lim` derived from `h` to make it useful for types
without a `[nonempty α]` instance. Because of the built-in proof irrelevance, Lean will unify
this instance with any other instance. -/
lemma le_nhds_Lim {f : filter α} (h : ∃a, f ≤ 𝓝 a) : f ≤ 𝓝 (@Lim _ _ (nonempty_of_exists h) f) :=
epsilon_spec h

/-- If `g` tends to some `𝓝 a` along `f`, then it tends to `𝓝 (lim f g)`. We formulate
this lemma with a `[nonempty α]` argument of `lim` derived from `h` to make it useful for types
without a `[nonempty α]` instance. Because of the built-in proof irrelevance, Lean will unify
this instance with any other instance. -/
lemma tendsto_nhds_lim {f : filter β} {g : β → α} (h : ∃ a, tendsto g f (𝓝 a)) :
  tendsto g f (𝓝 $ @lim _ _ _ (nonempty_of_exists h) f g) :=
le_nhds_Lim h

end lim

end topological_space

/-!
### Continuity
-/

section continuous
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
variables [topological_space α] [topological_space β] [topological_space γ]
open_locale topology

/-- A function between topological spaces is continuous if the preimage
  of every open set is open. Registered as a structure to make sure it is not unfolded by Lean. -/
structure continuous (f : α → β) : Prop :=
(is_open_preimage : ∀s, is_open s → is_open (f ⁻¹' s))

lemma continuous_def {f : α → β} : continuous f ↔ (∀s, is_open s → is_open (f ⁻¹' s)) :=
⟨λ hf s hs, hf.is_open_preimage s hs, λ h, ⟨h⟩⟩

lemma is_open.preimage {f : α → β} (hf : continuous f) {s : set β} (h : is_open s) :
  is_open (f ⁻¹' s) :=
hf.is_open_preimage s h

lemma continuous.congr {f g : α → β} (h : continuous f) (h' : ∀ x, f x = g x) : continuous g :=
by { convert h, ext, rw h' }

/-- A function between topological spaces is continuous at a point `x₀`
if `f x` tends to `f x₀` when `x` tends to `x₀`. -/
def continuous_at (f : α → β) (x : α) := tendsto f (𝓝 x) (𝓝 (f x))

lemma continuous_at.tendsto {f : α → β} {x : α} (h : continuous_at f x) :
  tendsto f (𝓝 x) (𝓝 (f x)) :=
h

lemma continuous_at_def {f : α → β} {x : α} : continuous_at f x ↔ ∀ A ∈ 𝓝 (f x), f ⁻¹' A ∈ 𝓝 x :=
iff.rfl

lemma continuous_at_congr {f g : α → β} {x : α} (h : f =ᶠ[𝓝 x] g) :
  continuous_at f x ↔ continuous_at g x :=
by simp only [continuous_at, tendsto_congr' h, h.eq_of_nhds]

lemma continuous_at.congr {f g : α → β} {x : α} (hf : continuous_at f x) (h : f =ᶠ[𝓝 x] g) :
  continuous_at g x :=
(continuous_at_congr h).1 hf

lemma continuous_at.preimage_mem_nhds {f : α → β} {x : α} {t : set β} (h : continuous_at f x)
  (ht : t ∈ 𝓝 (f x)) : f ⁻¹' t ∈ 𝓝 x :=
h ht

lemma eventually_eq_zero_nhds {M₀} [has_zero M₀] {a : α} {f : α → M₀} :
  f =ᶠ[𝓝 a] 0 ↔ a ∉ closure (function.support f) :=
by rw [← mem_compl_iff, ← interior_compl, mem_interior_iff_mem_nhds, function.compl_support]; refl

lemma cluster_pt.map {x : α} {la : filter α} {lb : filter β} (H : cluster_pt x la)
  {f : α → β} (hfc : continuous_at f x) (hf : tendsto f la lb) :
  cluster_pt (f x) lb :=
⟨ne_bot_of_le_ne_bot ((map_ne_bot_iff f).2 H).ne $ hfc.tendsto.inf hf⟩

/-- See also `interior_preimage_subset_preimage_interior`. -/
lemma preimage_interior_subset_interior_preimage {f : α → β} {s : set β}
  (hf : continuous f) : f⁻¹' (interior s) ⊆ interior (f⁻¹' s) :=
interior_maximal (preimage_mono interior_subset) (is_open_interior.preimage hf)

lemma continuous_id : continuous (id : α → α) :=
continuous_def.2 $ assume s h, h

lemma continuous.comp {g : β → γ} {f : α → β} (hg : continuous g) (hf : continuous f) :
  continuous (g ∘ f) :=
continuous_def.2 $ assume s h, (h.preimage hg).preimage hf

lemma continuous.iterate {f : α → α} (h : continuous f) (n : ℕ) : continuous (f^[n]) :=
nat.rec_on n continuous_id (λ n ihn, ihn.comp h)

lemma continuous_at.comp {g : β → γ} {f : α → β} {x : α}
  (hg : continuous_at g (f x)) (hf : continuous_at f x) :
  continuous_at (g ∘ f) x :=
hg.comp hf

lemma continuous.tendsto {f : α → β} (hf : continuous f) (x) :
  tendsto f (𝓝 x) (𝓝 (f x)) :=
((nhds_basis_opens x).tendsto_iff $ nhds_basis_opens $ f x).2 $
  λ t ⟨hxt, ht⟩, ⟨f ⁻¹' t, ⟨hxt, ht.preimage hf⟩, subset.refl _⟩

/-- A version of `continuous.tendsto` that allows one to specify a simpler form of the limit.
E.g., one can write `continuous_exp.tendsto' 0 1 exp_zero`. -/
lemma continuous.tendsto' {f : α → β} (hf : continuous f) (x : α) (y : β) (h : f x = y) :
  tendsto f (𝓝 x) (𝓝 y) :=
h ▸ hf.tendsto x

lemma continuous.continuous_at {f : α → β} {x : α} (h : continuous f) :
  continuous_at f x :=
h.tendsto x

lemma continuous_iff_continuous_at {f : α → β} : continuous f ↔ ∀ x, continuous_at f x :=
⟨continuous.tendsto,
  assume hf : ∀x, tendsto f (𝓝 x) (𝓝 (f x)),
  continuous_def.2 $
  assume s, assume hs : is_open s,
  have ∀a, f a ∈ s → s ∈ 𝓝 (f a),
    from λ a ha, is_open.mem_nhds hs ha,
  show is_open (f ⁻¹' s),
    from is_open_iff_nhds.2 $ λ a ha, le_principal_iff.2 $ hf _ (this a ha)⟩

lemma continuous_at_const {x : α} {b : β} : continuous_at (λ a:α, b) x :=
tendsto_const_nhds

lemma continuous_const {b : β} : continuous (λa:α, b) :=
continuous_iff_continuous_at.mpr $ assume a, continuous_at_const

lemma filter.eventually_eq.continuous_at {x : α} {f : α → β} {y : β} (h : f =ᶠ[𝓝 x] (λ _, y)) :
  continuous_at f x :=
(continuous_at_congr h).2 tendsto_const_nhds

lemma continuous_of_const {f : α → β} (h : ∀ x y, f x = f y) : continuous f :=
continuous_iff_continuous_at.mpr $ λ x, filter.eventually_eq.continuous_at $
  eventually_of_forall (λ y, h y x)

lemma continuous_at_id {x : α} : continuous_at id x :=
continuous_id.continuous_at

lemma continuous_at.iterate {f : α → α} {x : α} (hf : continuous_at f x) (hx : f x = x) (n : ℕ) :
  continuous_at (f^[n]) x :=
nat.rec_on n continuous_at_id $ λ n ihn,
show continuous_at (f^[n] ∘ f) x,
from continuous_at.comp (hx.symm ▸ ihn) hf

lemma continuous_iff_is_closed {f : α → β} :
  continuous f ↔ (∀s, is_closed s → is_closed (f ⁻¹' s)) :=
⟨assume hf s hs, by simpa using (continuous_def.1 hf sᶜ hs.is_open_compl).is_closed_compl,
  assume hf, continuous_def.2 $ assume s,
    by rw [←is_closed_compl_iff, ←is_closed_compl_iff]; exact hf _⟩

lemma is_closed.preimage {f : α → β} (hf : continuous f) {s : set β} (h : is_closed s) :
  is_closed (f ⁻¹' s) :=
continuous_iff_is_closed.mp hf s h

lemma mem_closure_image {f : α → β} {x : α} {s : set α} (hf : continuous_at f x)
  (hx : x ∈ closure s) : f x ∈ closure (f '' s) :=
mem_closure_of_frequently_of_tendsto
  ((mem_closure_iff_frequently.1 hx).mono (λ x, mem_image_of_mem _)) hf

lemma continuous_at_iff_ultrafilter {f : α → β} {x} : continuous_at f x ↔
  ∀ g : ultrafilter α, ↑g ≤ 𝓝 x → tendsto f g (𝓝 (f x)) :=
tendsto_iff_ultrafilter f (𝓝 x) (𝓝 (f x))

lemma continuous_iff_ultrafilter {f : α → β} :
  continuous f ↔ ∀ x (g : ultrafilter α), ↑g ≤ 𝓝 x → tendsto f g (𝓝 (f x)) :=
by simp only [continuous_iff_continuous_at, continuous_at_iff_ultrafilter]

lemma continuous.closure_preimage_subset {f : α → β}
  (hf : continuous f) (t : set β) :
  closure (f ⁻¹' t) ⊆ f ⁻¹' (closure t) :=
begin
  rw ← (is_closed_closure.preimage hf).closure_eq,
  exact closure_mono (preimage_mono subset_closure),
end

lemma continuous.frontier_preimage_subset
  {f : α → β} (hf : continuous f) (t : set β) :
  frontier (f ⁻¹' t) ⊆ f ⁻¹' (frontier t) :=
diff_subset_diff (hf.closure_preimage_subset t) (preimage_interior_subset_interior_preimage hf)

/-- If a continuous map `f` maps `s` to `t`, then it maps `closure s` to `closure t`. -/
lemma set.maps_to.closure {s : set α} {t : set β} {f : α → β} (h : maps_to f s t)
  (hc : continuous f) : maps_to f (closure s) (closure t) :=
begin
  simp only [maps_to, mem_closure_iff_cluster_pt],
  exact λ x hx, hx.map hc.continuous_at (tendsto_principal_principal.2 h)
end

lemma image_closure_subset_closure_image {f : α → β} {s : set α} (h : continuous f) :
  f '' closure s ⊆ closure (f '' s) :=
((maps_to_image f s).closure h).image_subset

lemma closure_subset_preimage_closure_image {f : α → β} {s : set α} (h : continuous f) :
  closure s ⊆ f ⁻¹' (closure (f '' s)) :=
by { rw ← set.image_subset_iff, exact image_closure_subset_closure_image h }

lemma map_mem_closure {s : set α} {t : set β} {f : α → β} {a : α}
  (hf : continuous f) (ha : a ∈ closure s) (ht : maps_to f s t) : f a ∈ closure t :=
ht.closure hf ha

/-- If a continuous map `f` maps `s` to a closed set `t`, then it maps `closure s` to `t`. -/
lemma set.maps_to.closure_left {s : set α} {t : set β} {f : α → β} (h : maps_to f s t)
  (hc : continuous f) (ht : is_closed t) : maps_to f (closure s) t :=
ht.closure_eq ▸ h.closure hc

/-!
### Function with dense range
-/

section dense_range
variables {κ ι : Type*} (f : κ → β) (g : β → γ)

/-- `f : ι → β` has dense range if its range (image) is a dense subset of β. -/
def dense_range := dense (range f)

variables {f}

/-- A surjective map has dense range. -/
lemma function.surjective.dense_range (hf : function.surjective f) : dense_range f :=
λ x, by simp [hf.range_eq]

lemma dense_range_id : dense_range (id : α → α) :=
function.surjective.dense_range function.surjective_id

lemma dense_range_iff_closure_range : dense_range f ↔ closure (range f) = univ :=
dense_iff_closure_eq

lemma dense_range.closure_range (h : dense_range f) : closure (range f) = univ :=
h.closure_eq

lemma dense.dense_range_coe {s : set α} (h : dense s) : dense_range (coe : s → α) :=
by simpa only [dense_range, subtype.range_coe_subtype]

lemma continuous.range_subset_closure_image_dense {f : α → β} (hf : continuous f)
  {s : set α} (hs : dense s) :
  range f ⊆ closure (f '' s) :=
by { rw [← image_univ, ← hs.closure_eq], exact image_closure_subset_closure_image hf }

/-- The image of a dense set under a continuous map with dense range is a dense set. -/
lemma dense_range.dense_image {f : α → β} (hf' : dense_range f) (hf : continuous f)
  {s : set α} (hs : dense s) :
  dense (f '' s)  :=
(hf'.mono $ hf.range_subset_closure_image_dense hs).of_closure

/-- If `f` has dense range and `s` is an open set in the codomain of `f`, then the image of the
preimage of `s` under `f` is dense in `s`. -/
lemma dense_range.subset_closure_image_preimage_of_is_open (hf : dense_range f) {s : set β}
  (hs : is_open s) : s ⊆ closure (f '' (f ⁻¹' s)) :=
by { rw image_preimage_eq_inter_range, exact hf.open_subset_closure_inter hs }

/-- If a continuous map with dense range maps a dense set to a subset of `t`, then `t` is a dense
set. -/
lemma dense_range.dense_of_maps_to {f : α → β} (hf' : dense_range f) (hf : continuous f)
  {s : set α} (hs : dense s) {t : set β} (ht : maps_to f s t) :
  dense t :=
(hf'.dense_image hf hs).mono ht.image_subset

/-- Composition of a continuous map with dense range and a function with dense range has dense
range. -/
lemma dense_range.comp {g : β → γ} {f : κ → β} (hg : dense_range g) (hf : dense_range f)
  (cg : continuous g) :
  dense_range (g ∘ f) :=
by { rw [dense_range, range_comp], exact hg.dense_image cg hf }

lemma dense_range.nonempty_iff (hf : dense_range f) : nonempty κ ↔ nonempty β :=
range_nonempty_iff_nonempty.symm.trans hf.nonempty_iff

lemma dense_range.nonempty [h : nonempty β] (hf : dense_range f) : nonempty κ :=
hf.nonempty_iff.mpr h

/-- Given a function `f : α → β` with dense range and `b : β`, returns some `a : α`. -/
def dense_range.some (hf : dense_range f) (b : β) : κ :=
classical.choice $ hf.nonempty_iff.mpr ⟨b⟩

lemma dense_range.exists_mem_open (hf : dense_range f) {s : set β} (ho : is_open s)
  (hs : s.nonempty) :
  ∃ a, f a ∈ s :=
exists_range_iff.1 $ hf.exists_mem_open ho hs

lemma dense_range.mem_nhds {f : κ → β} (h : dense_range f) {b : β} {U : set β}
  (U_in : U ∈ 𝓝 b) : ∃ a, f a ∈ U :=
let ⟨a, ha⟩ := h.exists_mem_open is_open_interior ⟨b, mem_interior_iff_mem_nhds.2 U_in⟩
in ⟨a, interior_subset ha⟩

end dense_range

end continuous

/--
The library contains many lemmas stating that functions/operations are continuous. There are many
ways to formulate the continuity of operations. Some are more convenient than others.
Note: for the most part this note also applies to other properties
(`measurable`, `differentiable`, `continuous_on`, ...).

### The traditional way
As an example, let's look at addition `(+) : M → M → M`. We can state that this is continuous
in different definitionally equal ways (omitting some typing information)
* `continuous (λ p, p.1 + p.2)`;
* `continuous (function.uncurry (+))`;
* `continuous ↿(+)`. (`↿` is notation for recursively uncurrying a function)

However, lemmas with this conclusion are not nice to use in practice because
1. They confuse the elaborator. The following two examples fail, because of limitations in the
  elaboration process.
  ```
  variables {M : Type*} [has_add M] [topological_space M] [has_continuous_add M]
  example : continuous (λ x : M, x + x) :=
  continuous_add.comp _

  example : continuous (λ x : M, x + x) :=
  continuous_add.comp (continuous_id.prod_mk continuous_id)
  ```
  The second is a valid proof, which is accepted if you write it as
  `continuous_add.comp (continuous_id.prod_mk continuous_id : _)`

2. If the operation has more than 2 arguments, they are impractical to use, because in your
  application the arguments in the domain might be in a different order or associated differently.

### The convenient way
A much more convenient way to write continuity lemmas is like `continuous.add`:
```
continuous.add {f g : X → M} (hf : continuous f) (hg : continuous g) : continuous (λ x, f x + g x)
```
The conclusion can be `continuous (f + g)`, which is definitionally equal.
This has the following advantages
* It supports projection notation, so is shorter to write.
* `continuous.add _ _` is recognized correctly by the elaborator and gives useful new goals.
* It works generally, since the domain is a variable.

As an example for an unary operation, we have `continuous.neg`.
```
continuous.neg {f : α → G} (hf : continuous f) : continuous (λ x, -f x)
```
For unary functions, the elaborator is not confused when applying the traditional lemma
(like `continuous_neg`), but it's still convenient to have the short version available (compare
`hf.neg.neg.neg` with `continuous_neg.comp $ continuous_neg.comp $ continuous_neg.comp hf`).

As a harder example, consider an operation of the following type:
```
def strans {x : F} (γ γ' : path x x) (t₀ : I) : path x x
```
The precise definition is not important, only its type.
The correct continuity principle for this operation is something like this:
```
{f : X → F} {γ γ' : ∀ x, path (f x) (f x)} {t₀ s : X → I}
  (hγ : continuous ↿γ) (hγ' : continuous ↿γ')
  (ht : continuous t₀) (hs : continuous s) :
  continuous (λ x, strans (γ x) (γ' x) (t x) (s x))
```
Note that *all* arguments of `strans` are indexed over `X`, even the basepoint `x`, and the last
argument `s` that arises since `path x x` has a coercion to `I → F`. The paths `γ` and `γ'` (which
are unary functions from `I`) become binary functions in the continuity lemma.

### Summary
* Make sure that your continuity lemmas are stated in the most general way, and in a convenient
  form. That means that:
  - The conclusion has a variable `X` as domain (not something like `Y × Z`);
  - Wherever possible, all point arguments `c : Y` are replaced by functions `c : X → Y`;
  - All `n`-ary function arguments are replaced by `n+1`-ary functions
    (`f : Y → Z` becomes `f : X → Y → Z`);
  - All (relevant) arguments have continuity assumptions, and perhaps there are additional
    assumptions needed to make the operation continuous;
  - The function in the conclusion is fully applied.
* These remarks are mostly about the format of the *conclusion* of a continuity lemma.
  In assumptions it's fine to state that a function with more than 1 argument is continuous using
  `↿` or `function.uncurry`.

### Functions with discontinuities

In some cases, you want to work with discontinuous functions, and in certain expressions they are
still continuous. For example, consider the fractional part of a number, `fract : ℝ → ℝ`.
In this case, you want to add conditions to when a function involving `fract` is continuous, so you
get something like this: (assumption `hf` could be weakened, but the important thing is the shape
of the conclusion)
```
lemma continuous_on.comp_fract {X Y : Type*} [topological_space X] [topological_space Y]
  {f : X → ℝ → Y} {g : X → ℝ} (hf : continuous ↿f) (hg : continuous g) (h : ∀ s, f s 0 = f s 1) :
  continuous (λ x, f x (fract (g x)))
```
With `continuous_at` you can be even more precise about what to prove in case of discontinuities,
see e.g. `continuous_at.comp_div_cases`.
-/
library_note "continuity lemma statement"

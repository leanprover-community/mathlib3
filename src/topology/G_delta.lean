/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import topology.metric_space.emetric_space

/-!
# `Gδ` sets

In this file we define `Gδ` sets and prove their basic properties.

## Main definitions

* `is_Gδ`: a set `s` is a `Gδ` set if it can be represented as an intersection
  of countably many open sets;

* `residual`: the filter of residual sets. A set `s` is called *residual* if it includes a dense
  `Gδ` set. In a Baire space (e.g., in a complete (e)metric space), residual sets form a filter.

  For technical reasons, we define `residual` in any topological space but the definition agrees
  with the description above only in Baire spaces.

## Main results

We prove that finite or countable intersections of Gδ sets is a Gδ set. We also prove that the
continuity set of a function from a topological space to an (e)metric space is a Gδ set.

## Tags

Gδ set, residual set
-/

noncomputable theory
open_locale classical topological_space filter uniformity

open filter encodable set

variables {α : Type*} {β : Type*} {γ : Type*} {ι : Type*}

section is_Gδ
variable [topological_space α]

/-- A Gδ set is a countable intersection of open sets. -/
def is_Gδ (s : set α) : Prop :=
  ∃T : set (set α), (∀t ∈ T, is_open t) ∧ countable T ∧ s = (⋂₀ T)

/-- An open set is a Gδ set. -/
lemma is_open.is_Gδ {s : set α} (h : is_open s) : is_Gδ s :=
⟨{s}, by simp [h], countable_singleton _, (set.sInter_singleton _).symm⟩

@[simp] lemma is_Gδ_empty : is_Gδ (∅ : set α) := is_open_empty.is_Gδ

@[simp] lemma is_Gδ_univ : is_Gδ (univ : set α) := is_open_univ.is_Gδ

lemma is_Gδ_bInter_of_open {I : set ι} (hI : countable I) {f : ι → set α}
  (hf : ∀i ∈ I, is_open (f i)) : is_Gδ (⋂i∈I, f i) :=
⟨f '' I, by rwa ball_image_iff, hI.image _, by rw sInter_image⟩

lemma is_Gδ_Inter_of_open [encodable ι] {f : ι → set α}
  (hf : ∀i, is_open (f i)) : is_Gδ (⋂i, f i) :=
⟨range f, by rwa forall_range_iff, countable_range _, by rw sInter_range⟩

/-- The intersection of an encodable family of Gδ sets is a Gδ set. -/
lemma is_Gδ_Inter [encodable ι] {s : ι → set α} (hs : ∀ i, is_Gδ (s i)) : is_Gδ (⋂ i, s i) :=
begin
  choose T hTo hTc hTs using hs,
  obtain rfl : s = λ i, ⋂₀ T i := funext hTs,
  refine ⟨⋃ i, T i, _, countable_Union hTc, (sInter_Union _).symm⟩,
  simpa [@forall_swap ι] using hTo
end

lemma is_Gδ_bInter {s : set ι} (hs : countable s) {t : Π i ∈ s, set α}
  (ht : ∀ i ∈ s, is_Gδ (t i ‹_›)) : is_Gδ (⋂ i ∈ s, t i ‹_›) :=
begin
  rw [bInter_eq_Inter],
  haveI := hs.to_encodable,
  exact is_Gδ_Inter (λ x, ht x x.2)
end

/-- A countable intersection of Gδ sets is a Gδ set. -/
lemma is_Gδ_sInter {S : set (set α)} (h : ∀s∈S, is_Gδ s) (hS : countable S) : is_Gδ (⋂₀ S) :=
by simpa only [sInter_eq_bInter] using is_Gδ_bInter hS h

lemma is_Gδ.inter {s t : set α} (hs : is_Gδ s) (ht : is_Gδ t) : is_Gδ (s ∩ t) :=
by { rw inter_eq_Inter, exact is_Gδ_Inter (bool.forall_bool.2 ⟨ht, hs⟩) }

/-- The union of two Gδ sets is a Gδ set. -/
lemma is_Gδ.union {s t : set α} (hs : is_Gδ s) (ht : is_Gδ t) : is_Gδ (s ∪ t) :=
begin
  rcases hs with ⟨S, Sopen, Scount, rfl⟩,
  rcases ht with ⟨T, Topen, Tcount, rfl⟩,
  rw [sInter_union_sInter],
  apply is_Gδ_bInter_of_open (Scount.prod Tcount),
  rintros ⟨a, b⟩ ⟨ha, hb⟩,
  exact (Sopen a ha).union (Topen b hb)
end

/-- The union of finitely many Gδ sets is a Gδ set. -/
lemma is_Gδ_bUnion {s : set ι} (hs : s.finite) {f : ι → set α} (h : ∀ i ∈ s, is_Gδ (f i)) :
  is_Gδ (⋃ i ∈ s, f i) :=
begin
  refine finite.induction_on hs (by simp) _ h,
  simp only [ball_insert_iff, bUnion_insert],
  exact λ a s _ _ ihs H, H.1.union (ihs H.2)
end

lemma is_closed.is_Gδ' {α} [uniform_space α] {s : set α} (hs : is_closed s)
  (H : (𝓤 α).is_countably_generated) : is_Gδ s :=
begin
  rcases H.exists_antitone_subbasis uniformity_has_basis_open with ⟨U, hUo, hU, -, -⟩,
  rw [← hs.closure_eq, ← hU.bInter_bUnion_ball],
  refine is_Gδ_bInter (countable_encodable _) (λ n hn, is_open.is_Gδ _),
  exact is_open_bUnion (λ x hx, uniform_space.is_open_ball _ (hUo _).2)
end

lemma is_closed.is_Gδ {α} [pseudo_emetric_space α] {s : set α} (hs : is_closed s) : is_Gδ s :=
hs.is_Gδ' emetric.uniformity_has_countable_basis

section t1_space

variable [t1_space α]

lemma is_Gδ_compl_singleton (a : α) : is_Gδ ({a}ᶜ : set α) :=
is_open_compl_singleton.is_Gδ

lemma set.countable.is_Gδ_compl {s : set α} (hs : countable s) : is_Gδ sᶜ :=
begin
  rw [← bUnion_of_singleton s, compl_bUnion],
  exact is_Gδ_bInter hs (λ x _, is_Gδ_compl_singleton x)
end

lemma set.finite.is_Gδ_compl {s : set α} (hs : finite s) : is_Gδ sᶜ :=
hs.countable.is_Gδ_compl

lemma set.subsingleton.is_Gδ_compl {s : set α} (hs : s.subsingleton) : is_Gδ sᶜ :=
hs.finite.is_Gδ_compl

lemma finset.is_Gδ_compl (s : finset α) : is_Gδ (sᶜ : set α) :=
s.finite_to_set.is_Gδ_compl

open topological_space

variables [first_countable_topology α]

lemma is_Gδ_singleton (a : α) : is_Gδ ({a} : set α) :=
begin
  rcases (is_countably_generated_nhds a).exists_antitone_subbasis (nhds_basis_opens _)
    with ⟨U, hU, h_basis⟩,
  rw [← bInter_basis_nhds h_basis.to_has_basis],
  exact is_Gδ_bInter (countable_encodable _) (λ n hn, (hU n).2.is_Gδ),
end

lemma set.finite.is_Gδ {s : set α} (hs : finite s) : is_Gδ s :=
finite.induction_on hs is_Gδ_empty $ λ a s _ _ hs, (is_Gδ_singleton a).union hs

end t1_space

end is_Gδ

section continuous_at

open topological_space
open_locale uniformity

variables [topological_space α]

lemma is_Gδ_set_of_continuous_at_of_countably_generated_uniformity
  [uniform_space β] (hU : is_countably_generated (𝓤 β)) (f : α → β) :
  is_Gδ {x | continuous_at f x} :=
begin
  obtain ⟨U, hUo, hU⟩ := hU.exists_antitone_subbasis uniformity_has_basis_open_symmetric,
  simp only [uniform.continuous_at_iff_prod, nhds_prod_eq],
  simp only [(nhds_basis_opens _).prod_self.tendsto_iff hU.to_has_basis, forall_prop_of_true,
    set_of_forall, id],
  refine is_Gδ_Inter (λ k, is_open.is_Gδ $ is_open_iff_mem_nhds.2 $ λ x, _),
  rintros ⟨s, ⟨hsx, hso⟩, hsU⟩,
  filter_upwards [is_open.mem_nhds hso hsx],
  intros y hy,
  exact ⟨s, ⟨hy, hso⟩, hsU⟩
end

/-- The set of points where a function is continuous is a Gδ set. -/
lemma is_Gδ_set_of_continuous_at [pseudo_emetric_space β] (f : α → β) :
  is_Gδ {x | continuous_at f x} :=
is_Gδ_set_of_continuous_at_of_countably_generated_uniformity
  emetric.uniformity_has_countable_basis _

end continuous_at

/-- A set `s` is called *residual* if it includes a dense `Gδ` set. If `α` is a Baire space
(e.g., a complete metric space), then residual sets form a filter, see `mem_residual`.

For technical reasons we define the filter `residual` in any topological space but in a non-Baire
space it is not useful because it may contain some non-residual sets. -/
def residual (α : Type*) [topological_space α] : filter α :=
⨅ t (ht : is_Gδ t) (ht' : dense t), 𝓟 t

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import measure_theory.measure.ae_disjoint

/-!
# Null measurable sets and complete measures

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

### Null measurable sets and functions

A set `s : set α` is called *null measurable* (`measure_theory.null_measurable_set`) if it satisfies
any of the following equivalent conditions:

* there exists a measurable set `t` such that `s =ᵐ[μ] t` (this is used as a definition);
* `measure_theory.to_measurable μ s =ᵐ[μ] s`;
* there exists a measurable subset `t ⊆ s` such that `t =ᵐ[μ] s` (in this case the latter equality
  means that `μ (s \ t) = 0`);
* `s` can be represented as a union of a measurable set and a set of measure zero;
* `s` can be represented as a difference of a measurable set and a set of measure zero.

Null measurable sets form a σ-algebra that is registered as a `measurable_space` instance on
`measure_theory.null_measurable_space α μ`. We also say that `f : α → β` is
`measure_theory.null_measurable` if the preimage of a measurable set is a null measurable set.
In other words, `f : α → β` is null measurable if it is measurable as a function
`measure_theory.null_measurable_space α μ → β`.

### Complete measures

We say that a measure `μ` is complete w.r.t. the `measurable_space α` σ-algebra (or the σ-algebra is
complete w.r.t measure `μ`) if every set of measure zero is measurable. In this case all null
measurable sets and functions are measurable.

For each measure `μ`, we define `measure_theory.measure.completion μ` to be the same measure
interpreted as a measure on `measure_theory.null_measurable_space α μ` and prove that this is a
complete measure.

## Implementation notes

We define `measure_theory.null_measurable_set` as `@measurable_set (null_measurable_space α μ) _` so
that theorems about `measurable_set`s like `measurable_set.union` can be applied to
`null_measurable_set`s. However, these lemmas output terms of the same form
`@measurable_set (null_measurable_space α μ) _ _`. While this is definitionally equal to the
expected output `null_measurable_set s μ`, it looks different and may be misleading. So we copy all
standard lemmas about measurable sets to the `measure_theory.null_measurable_set` namespace and fix
the output type.

## Tags

measurable, measure, null measurable, completion
-/

open filter set encodable

variables {ι α β γ : Type*}

namespace measure_theory

/-- A type tag for `α` with `measurable_set` given by `null_measurable_set`. -/
@[nolint unused_arguments]
def null_measurable_space (α : Type*) [measurable_space α] (μ : measure α . volume_tac) : Type* := α

section

variables {m0 : measurable_space α} {μ : measure α} {s t : set α}

instance [h : inhabited α] : inhabited (null_measurable_space α μ) := h
instance [h : subsingleton α] : subsingleton (null_measurable_space α μ) := h

instance : measurable_space (null_measurable_space α μ) :=
{ measurable_set' := λ s, ∃ t, measurable_set t ∧ s =ᵐ[μ] t,
  measurable_set_empty := ⟨∅, measurable_set.empty, ae_eq_refl _⟩,
  measurable_set_compl := λ s ⟨t, htm, hts⟩, ⟨tᶜ, htm.compl, hts.compl⟩,
  measurable_set_Union := λ s hs, by { choose t htm hts using hs,
    exact ⟨⋃ i, t i, measurable_set.Union htm, eventually_eq.countable_Union hts⟩ } }

/-- A set is called `null_measurable_set` if it can be approximated by a measurable set up to
a set of null measure. -/
def null_measurable_set [measurable_space α] (s : set α) (μ : measure α . volume_tac) : Prop :=
@measurable_set (null_measurable_space α μ) _ s

@[simp] lemma _root_.measurable_set.null_measurable_set (h : measurable_set s) :
  null_measurable_set s μ :=
⟨s, h, ae_eq_refl _⟩

@[simp] lemma null_measurable_set_empty : null_measurable_set ∅ μ := measurable_set.empty

@[simp] lemma null_measurable_set_univ : null_measurable_set univ μ := measurable_set.univ

namespace null_measurable_set

lemma of_null (h : μ s = 0) : null_measurable_set s μ :=
⟨∅, measurable_set.empty, ae_eq_empty.2 h⟩

lemma compl (h : null_measurable_set s μ) : null_measurable_set sᶜ μ := h.compl

lemma of_compl (h : null_measurable_set sᶜ μ) : null_measurable_set s μ := h.of_compl

@[simp] lemma compl_iff : null_measurable_set sᶜ μ ↔ null_measurable_set s μ :=
measurable_set.compl_iff

@[nontriviality]
lemma of_subsingleton [subsingleton α] : null_measurable_set s μ := subsingleton.measurable_set

protected lemma congr (hs : null_measurable_set s μ) (h : s =ᵐ[μ] t) :
  null_measurable_set t μ :=
let ⟨s', hm, hs'⟩ := hs in ⟨s', hm, h.symm.trans hs'⟩

protected lemma Union {ι : Sort*} [countable ι] {s : ι → set α}
  (h : ∀ i, null_measurable_set (s i) μ) :
  null_measurable_set (⋃ i, s i) μ :=
measurable_set.Union h

protected lemma bUnion_decode₂ [encodable ι] ⦃f : ι → set α⦄ (h : ∀ i, null_measurable_set (f i) μ)
  (n : ℕ) : null_measurable_set (⋃ b ∈ encodable.decode₂ ι n, f b) μ :=
measurable_set.bUnion_decode₂ h n

protected lemma bUnion {f : ι → set α} {s : set ι} (hs : s.countable)
  (h : ∀ b ∈ s, null_measurable_set (f b) μ) : null_measurable_set (⋃ b ∈ s, f b) μ :=
measurable_set.bUnion hs h

protected lemma sUnion {s : set (set α)} (hs : s.countable) (h : ∀ t ∈ s, null_measurable_set t μ) :
  null_measurable_set (⋃₀ s) μ :=
by { rw sUnion_eq_bUnion, exact measurable_set.bUnion hs h }

protected lemma Inter {ι : Sort*} [countable ι] {f : ι → set α}
  (h : ∀ i, null_measurable_set (f i) μ) :
  null_measurable_set (⋂ i, f i) μ :=
measurable_set.Inter h

protected lemma bInter {f : β → set α} {s : set β} (hs : s.countable)
  (h : ∀ b ∈ s, null_measurable_set (f b) μ) : null_measurable_set (⋂ b ∈ s, f b) μ :=
measurable_set.bInter hs h

protected lemma sInter {s : set (set α)} (hs : s.countable) (h : ∀ t ∈ s, null_measurable_set t μ) :
  null_measurable_set (⋂₀ s) μ :=
measurable_set.sInter hs h

@[simp] protected lemma union (hs : null_measurable_set s μ) (ht : null_measurable_set t μ) :
  null_measurable_set (s ∪ t) μ :=
hs.union ht

protected lemma union_null (hs : null_measurable_set s μ) (ht : μ t = 0) :
  null_measurable_set (s ∪ t) μ :=
hs.union (of_null ht)

@[simp] protected lemma inter (hs : null_measurable_set s μ) (ht : null_measurable_set t μ) :
  null_measurable_set (s ∩ t) μ :=
hs.inter ht

@[simp] protected lemma diff (hs : null_measurable_set s μ) (ht : null_measurable_set t μ) :
  null_measurable_set (s \ t) μ :=
hs.diff ht

@[simp] protected lemma disjointed {f : ℕ → set α} (h : ∀ i, null_measurable_set (f i) μ) (n) :
  null_measurable_set (disjointed f n) μ :=
measurable_set.disjointed h n

@[simp] protected lemma const (p : Prop) : null_measurable_set {a : α | p} μ :=
measurable_set.const p

instance [measurable_singleton_class α] : measurable_singleton_class (null_measurable_space α μ) :=
⟨λ x, (@measurable_set_singleton α _ _ x).null_measurable_set⟩

protected lemma insert [measurable_singleton_class (null_measurable_space α μ)]
  (hs : null_measurable_set s μ) (a : α) :
  null_measurable_set (insert a s) μ :=
hs.insert a

lemma exists_measurable_superset_ae_eq (h : null_measurable_set s μ) :
  ∃ t ⊇ s, measurable_set t ∧ t =ᵐ[μ] s :=
begin
  rcases h with ⟨t, htm, hst⟩,
  refine ⟨t ∪ to_measurable μ (s \ t), _, htm.union (measurable_set_to_measurable _ _), _⟩,
  { exact diff_subset_iff.1 (subset_to_measurable _ _) },
  { have : to_measurable μ (s \ t) =ᵐ[μ] (∅ : set α), by simp [ae_le_set.1 hst.le],
    simpa only [union_empty] using hst.symm.union this }
end

lemma to_measurable_ae_eq (h : null_measurable_set s μ) :
  to_measurable μ s =ᵐ[μ] s :=
begin
  rw [to_measurable, dif_pos],
  exact h.exists_measurable_superset_ae_eq.some_spec.snd.2
end

lemma compl_to_measurable_compl_ae_eq (h : null_measurable_set s μ) :
  (to_measurable μ sᶜ)ᶜ =ᵐ[μ] s :=
by simpa only [compl_compl] using h.compl.to_measurable_ae_eq.compl

lemma exists_measurable_subset_ae_eq (h : null_measurable_set s μ) :
  ∃ t ⊆ s, measurable_set t ∧ t =ᵐ[μ] s :=
⟨(to_measurable μ sᶜ)ᶜ, compl_subset_comm.2 $ subset_to_measurable _ _,
  (measurable_set_to_measurable _ _).compl, h.compl_to_measurable_compl_ae_eq⟩

end null_measurable_set

/-- If `sᵢ` is a countable family of (null) measurable pairwise `μ`-a.e. disjoint sets, then there
exists a subordinate family `tᵢ ⊆ sᵢ` of measurable pairwise disjoint sets such that
`tᵢ =ᵐ[μ] sᵢ`. -/
lemma exists_subordinate_pairwise_disjoint [countable ι] {s : ι → set α}
  (h : ∀ i, null_measurable_set (s i) μ) (hd : pairwise (ae_disjoint μ on s)) :
  ∃ t : ι → set α, (∀ i, t i ⊆ s i) ∧ (∀ i, s i =ᵐ[μ] t i) ∧ (∀ i, measurable_set (t i)) ∧
    pairwise (disjoint on t) :=
begin
  choose t ht_sub htm ht_eq using λ i, (h i).exists_measurable_subset_ae_eq,
  rcases exists_null_pairwise_disjoint_diff hd with ⟨u, hum, hu₀, hud⟩,
  exact ⟨λ i, t i \ u i, λ i, (diff_subset _ _).trans (ht_sub _),
    λ i, (ht_eq _).symm.trans (diff_null_ae_eq_self (hu₀ i)).symm,
    λ i, (htm i).diff (hum i), hud.mono $
      λ i j h, h.mono (diff_subset_diff_left (ht_sub i)) (diff_subset_diff_left (ht_sub j))⟩
end

lemma measure_Union {m0 : measurable_space α} {μ : measure α} [countable ι] {f : ι → set α}
  (hn : pairwise (disjoint on f)) (h : ∀ i, measurable_set (f i)) :
  μ (⋃ i, f i) = ∑' i, μ (f i) :=
begin
  rw [measure_eq_extend (measurable_set.Union h),
    extend_Union measurable_set.empty _ measurable_set.Union _ hn h],
  { simp [measure_eq_extend, h] },
  { exact μ.empty },
  { exact μ.m_Union }
end

lemma measure_Union₀ [countable ι] {f : ι → set α} (hd : pairwise (ae_disjoint μ on f))
  (h : ∀ i, null_measurable_set (f i) μ) :
  μ (⋃ i, f i) = ∑' i, μ (f i) :=
begin
  rcases exists_subordinate_pairwise_disjoint h hd with ⟨t, ht_sub, ht_eq, htm, htd⟩,
  calc μ (⋃ i, f i) = μ (⋃ i, t i) : measure_congr (eventually_eq.countable_Union ht_eq)
  ... = ∑' i, μ (t i) : measure_Union htd htm
  ... = ∑' i, μ (f i) : tsum_congr (λ i, measure_congr (ht_eq _).symm)
end

lemma measure_union₀_aux (hs : null_measurable_set s μ) (ht : null_measurable_set t μ)
  (hd : ae_disjoint μ s t) :
  μ (s ∪ t) = μ s + μ t :=
begin
  rw [union_eq_Union, measure_Union₀, tsum_fintype, fintype.sum_bool, cond, cond],
  exacts [(pairwise_on_bool ae_disjoint.symmetric).2 hd, λ b, bool.cases_on b ht hs]
end

/-- A null measurable set `t` is Carathéodory measurable: for any `s`, we have
`μ (s ∩ t) + μ (s \ t) = μ s`. -/
lemma measure_inter_add_diff₀ (s : set α) (ht : null_measurable_set t μ) :
  μ (s ∩ t) + μ (s \ t) = μ s :=
begin
  refine le_antisymm _ _,
  { rcases exists_measurable_superset μ s with ⟨s', hsub, hs'm, hs'⟩,
    replace hs'm : null_measurable_set s' μ := hs'm.null_measurable_set,
    calc μ (s ∩ t) + μ (s \ t) ≤ μ (s' ∩ t) + μ (s' \ t) :
      add_le_add (measure_mono $ inter_subset_inter_left _ hsub)
        (measure_mono $ diff_subset_diff_left hsub)
    ... = μ (s' ∩ t ∪ s' \ t) :
      (measure_union₀_aux (hs'm.inter ht) (hs'm.diff ht) $
        (@disjoint_inf_sdiff _ s' t _).ae_disjoint).symm
    ... = μ s' : congr_arg μ (inter_union_diff _ _)
    ... = μ s : hs' },
  { calc μ s = μ (s ∩ t ∪ s \ t) : by rw inter_union_diff
    ... ≤ μ (s ∩ t) + μ (s \ t) : measure_union_le _ _ }
end

lemma measure_union_add_inter₀ (s : set α) (ht : null_measurable_set t μ) :
  μ (s ∪ t) + μ (s ∩ t) = μ s + μ t :=
by rw [← measure_inter_add_diff₀ (s ∪ t) ht, union_inter_cancel_right, union_diff_right,
  ← measure_inter_add_diff₀ s ht, add_comm, ← add_assoc, add_right_comm]

lemma measure_union_add_inter₀' (hs : null_measurable_set s μ) (t : set α) :
  μ (s ∪ t) + μ (s ∩ t) = μ s + μ t :=
by rw [union_comm, inter_comm, measure_union_add_inter₀ t hs, add_comm]

lemma measure_union₀ (ht : null_measurable_set t μ) (hd : ae_disjoint μ s t) :
  μ (s ∪ t) = μ s + μ t :=
by rw [← measure_union_add_inter₀ s ht, hd.eq, add_zero]

lemma measure_union₀' (hs : null_measurable_set s μ) (hd : ae_disjoint μ s t) :
  μ (s ∪ t) = μ s + μ t :=
by rw [union_comm, measure_union₀ hs hd.symm, add_comm]

lemma measure_add_measure_compl₀ {s : set α} (hs : null_measurable_set s μ) :
  μ s + μ sᶜ = μ univ :=
by rw [← measure_union₀' hs ae_disjoint_compl_right, union_compl_self]

section measurable_singleton_class

variable [measurable_singleton_class (null_measurable_space α μ)]

lemma null_measurable_set_singleton (x : α) : null_measurable_set {x} μ :=
measurable_set_singleton x

@[simp] lemma null_measurable_set_insert {a : α} {s : set α} :
  null_measurable_set (insert a s) μ ↔ null_measurable_set s μ :=
measurable_set_insert

lemma null_measurable_set_eq {a : α} : null_measurable_set {x | x = a} μ :=
null_measurable_set_singleton a

protected lemma _root_.set.finite.null_measurable_set (hs : s.finite) : null_measurable_set s μ :=
finite.measurable_set hs

protected lemma _root_.finset.null_measurable_set (s : finset α) : null_measurable_set ↑s μ :=
finset.measurable_set s

end measurable_singleton_class

lemma _root_.set.finite.null_measurable_set_bUnion {f : ι → set α} {s : set ι} (hs : s.finite)
  (h : ∀ b ∈ s, null_measurable_set (f b) μ) :
  null_measurable_set (⋃ b ∈ s, f b) μ :=
finite.measurable_set_bUnion hs h

lemma _root_.finset.null_measurable_set_bUnion {f : ι → set α} (s : finset ι)
  (h : ∀ b ∈ s, null_measurable_set (f b) μ) :
  null_measurable_set (⋃ b ∈ s, f b) μ :=
finset.measurable_set_bUnion s h

lemma _root_.set.finite.null_measurable_set_sUnion {s : set (set α)} (hs : s.finite)
  (h : ∀ t ∈ s, null_measurable_set t μ) :
  null_measurable_set (⋃₀ s) μ :=
finite.measurable_set_sUnion hs h

lemma _root_.set.finite.null_measurable_set_bInter {f : ι → set α} {s : set ι} (hs : s.finite)
  (h : ∀ b ∈ s, null_measurable_set (f b) μ) : null_measurable_set (⋂ b ∈ s, f b) μ :=
finite.measurable_set_bInter hs h

lemma _root_.finset.null_measurable_set_bInter {f : ι → set α} (s : finset ι)
  (h : ∀ b ∈ s, null_measurable_set (f b) μ) : null_measurable_set (⋂ b ∈ s, f b) μ :=
s.finite_to_set.null_measurable_set_bInter h

lemma _root_.set.finite.null_measurable_set_sInter {s : set (set α)} (hs : s.finite)
  (h : ∀ t ∈ s, null_measurable_set t μ) : null_measurable_set (⋂₀ s) μ :=
null_measurable_set.sInter hs.countable h

lemma null_measurable_set_to_measurable : null_measurable_set (to_measurable μ s) μ :=
(measurable_set_to_measurable _ _).null_measurable_set

end

section null_measurable

variables [measurable_space α] [measurable_space β] [measurable_space γ]
  {f : α → β} {μ : measure α}

/-- A function `f : α → β` is null measurable if the preimage of a measurable set is a null
measurable set. -/
def null_measurable (f : α → β) (μ : measure α . volume_tac) : Prop :=
∀ ⦃s : set β⦄, measurable_set s → null_measurable_set (f ⁻¹' s) μ

protected lemma _root_.measurable.null_measurable (h : measurable f) : null_measurable f μ :=
λ s hs, (h hs).null_measurable_set

protected lemma null_measurable.measurable' (h : null_measurable f μ) :
  @measurable (null_measurable_space α μ) β _ _ f := h

lemma measurable.comp_null_measurable {g : β → γ} (hg : measurable g)
  (hf : null_measurable f μ) : null_measurable (g ∘ f) μ :=
hg.comp hf

lemma null_measurable.congr {g : α → β} (hf : null_measurable f μ) (hg : f =ᵐ[μ] g) :
  null_measurable g μ :=
λ s hs, (hf hs).congr $ eventually_eq_set.2 $ hg.mono $
  λ x hx, by rw [mem_preimage, mem_preimage, hx]

end null_measurable

section is_complete

/-- A measure is complete if every null set is also measurable.
  A null set is a subset of a measurable set with measure `0`.
  Since every measure is defined as a special case of an outer measure, we can more simply state
  that a set `s` is null if `μ s = 0`. -/
class measure.is_complete {_ : measurable_space α} (μ : measure α) : Prop :=
(out' : ∀ s, μ s = 0 → measurable_set s)

variables {m0 : measurable_space α} {μ : measure α} {s t : set α}

theorem measure.is_complete_iff :
  μ.is_complete ↔ ∀ s, μ s = 0 → measurable_set s := ⟨λ h, h.1, λ h, ⟨h⟩⟩
theorem measure.is_complete.out (h : μ.is_complete) :
  ∀ s, μ s = 0 → measurable_set s := h.1

theorem measurable_set_of_null [μ.is_complete] (hs : μ s = 0) : measurable_set s :=
measure_theory.measure.is_complete.out' s hs

theorem null_measurable_set.measurable_of_complete (hs : null_measurable_set s μ) [μ.is_complete] :
  measurable_set s :=
diff_diff_cancel_left (subset_to_measurable μ s) ▸ (measurable_set_to_measurable _ _).diff
  (measurable_set_of_null (ae_le_set.1 hs.to_measurable_ae_eq.le))

theorem null_measurable.measurable_of_complete [μ.is_complete] {m1 : measurable_space β} {f : α → β}
  (hf : null_measurable f μ) : measurable f :=
λ s hs, (hf hs).measurable_of_complete

lemma _root_.measurable.congr_ae {α β} [measurable_space α] [measurable_space β] {μ : measure α}
  [hμ : μ.is_complete] {f g : α → β} (hf : measurable f) (hfg : f =ᵐ[μ] g) :
  measurable g :=
(hf.null_measurable.congr hfg).measurable_of_complete

namespace measure

/-- Given a measure we can complete it to a (complete) measure on all null measurable sets. -/
def completion {_ : measurable_space α} (μ : measure α) :
  @measure_theory.measure (null_measurable_space α μ) _ :=
{ to_outer_measure := μ.to_outer_measure,
  m_Union := λ s hs hd, measure_Union₀ (hd.mono $ λ i j h, h.ae_disjoint) hs,
  trimmed := begin
    refine le_antisymm (λ s, _) (outer_measure.le_trim _),
    rw outer_measure.trim_eq_infi, simp only [to_outer_measure_apply],
    refine (infi₂_mono _).trans_eq (measure_eq_infi _).symm,
    exact λ t ht, infi_mono' (λ h, ⟨h.null_measurable_set, le_rfl⟩)
  end }

instance completion.is_complete {m : measurable_space α} (μ : measure α) :
  μ.completion.is_complete :=
⟨λ z hz, null_measurable_set.of_null hz⟩

@[simp] lemma coe_completion {_ : measurable_space α} (μ : measure α) :
  ⇑μ.completion = μ := rfl

lemma completion_apply {_ : measurable_space α} (μ : measure α) (s : set α) :
  μ.completion s = μ s := rfl

end measure

end is_complete

end measure_theory

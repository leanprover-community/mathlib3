/-
Copyright (c) 2023 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher
-/
import topology.metric_space.pi_nat

/-!
# (Topological) Schemes and their induced maps

In topology, and especially descriptive set theory, one often constructs functions `(ℕ → β) → α`,
where α is some topological space and β is a discrete space, as an appropriate limit of some map
`list β → set α`. We call the latter type of map a "`β`-scheme on `α`".

This file develops the basic, abstract theory of these schemes and the functions they induce.

## Main Definitions

* `cantor_scheme.induced_map A` : The aforementioned "limit" of a scheme `A : list β → set α`.
  This is a partial function from `ℕ → β` to `a`,
  implemented here as an object of type `Σ s : set (ℕ → β), s → α`.
  That is, `(induced_map A).1` is the domain and `(induced_map A).2` is the function.

## Implementation Notes

We consider end-appending to be the fundamental way to build lists (say on `β`) inductively,
as this interacts better with the topology on `ℕ → β`.
As a result, functions like `list.nth` or `stream.take` do not have their intended meaning
in this file. We define an analogue of `stream.take`, `res`, for our purposes.
It is related by the equation `res x n = (stream.take n x).reverse`

## References

* [kechris1995] (Chapters 6-7)

## Tags

Scheme.

-/

namespace cantor_scheme

open list function filter set pi_nat
open_locale classical topological_space

variables {β α : Type*} (A : list β → set α)

/-- From a `β`-scheme on `α` `A`, we define a partial function from `(ℕ → β)` to `α`
which sends each infinite sequence `x` to an element of the intersection along the
branch corresponding to `x`, if it exists.
We call this the map induced by the scheme. -/
noncomputable def induced_map : Σ s : set (ℕ → β), s → α :=
⟨λ x, set.nonempty ⋂ n : ℕ, A (res x n), λ ⟨x, hx⟩, hx.some⟩

section topology

/-- A scheme is antitone if each set contains its children.  -/
protected def antitone : Prop := ∀ l : list β, ∀ a : β, A (a :: l) ⊆ A l

/-- A useful strengthening of being antitone is to require that each set contains
the closure of each of its children. -/
def closure_antitone [topological_space α] : Prop :=
∀ l : list β, ∀ a : β, closure(A (a :: l)) ⊆ A l

/-- A scheme is disjoint if the children of each set of pairwise disjoint. -/
protected def disjoint : Prop :=
∀ l : list β, _root_.pairwise $ λ a b, disjoint (A (a :: l)) (A (b :: l))

variable {A}

/-- If `x` is in the domain of the induced map of a scheme `A`,
its image under this map is in each set along the corresponding branch. -/
lemma map_mem {x : ℕ → β} (hx : x ∈ (induced_map A).1) (n : ℕ) :
  (induced_map A).2 ⟨x, hx⟩ ∈ A (res x n) :=
begin
  have := hx.some_mem,
  rw mem_Inter at this,
  exact this n,
end

protected lemma closure_antitone.antitone [topological_space α] (hA : closure_antitone A) :
  cantor_scheme.antitone A :=
λ l a, subset_closure.trans (hA l a)

protected lemma antitone.closure_antitone [topological_space α] (hanti : cantor_scheme.antitone A)
  (hclosed : ∀ l, is_closed (A l)) : closure_antitone A :=
λ l a, (hclosed _).closure_eq.subset.trans (hanti _ _)

/-- A scheme where the children of each set are pairwise disjoint induces an injective map. -/
theorem disjoint.map_injective (hA : cantor_scheme.disjoint A) : injective (induced_map A).2 :=
begin
  rintros ⟨x, hx⟩ ⟨y, hy⟩ hxy,
  rw [← subtype.val_inj, ← res_eq_iff_eq],
  intro n,
  induction n with n ih, { simp },
  simp only [res_succ],
  refine ⟨_, ih⟩,
  contrapose hA,
  simp only [cantor_scheme.disjoint, _root_.pairwise, ne.def, not_forall, exists_prop],
  refine ⟨res x n, _, _, hA, _⟩,
  rw not_disjoint_iff,
  use (induced_map A).2 ⟨x, hx⟩,
  split,
  { rw ← res_succ,
    apply map_mem, },
  rw [hxy, ih, ← res_succ],
  apply map_mem,
end

end topology

section metric

variable [pseudo_metric_space α]

variable (A)

/-- A scheme on a metric space has vanishing diameter if diameter approaches 0 along each branch. -/
def vanishing_diam : Prop :=
∀ x : ℕ → β, tendsto (λ n : ℕ, emetric.diam (A (res x n))) at_top (𝓝 0)

variable {A}

lemma vanishing_diam.dist_lt (hA : vanishing_diam A) (ε : ℝ) (ε_pos : 0 < ε) (x : ℕ → β) :
  ∃ n : ℕ, ∀ y z ∈ A (res x n), dist y z < ε :=
begin
  specialize hA x,
  rw ennreal.tendsto_at_top_zero at hA,
  cases hA (ennreal.of_real (ε / 2))
    (by { simp only [gt_iff_lt, ennreal.of_real_pos], linarith }) with n hn,
  use n,
  intros y hy z hz,
  rw [← ennreal.of_real_lt_of_real_iff ε_pos, ← edist_dist],
  apply lt_of_le_of_lt (emetric.edist_le_diam_of_mem hy hz),
  apply lt_of_le_of_lt (hn _ (le_refl _)),
  rw ennreal.of_real_lt_of_real_iff ε_pos,
  linarith,
end

/-- A scheme with vanishing diameter along each branch induces a continuous map. -/
theorem vanishing_diam.map_continuous [topological_space β] [discrete_topology β]
  (hA : vanishing_diam A) : continuous (induced_map A).2 :=
begin
  rw metric.continuous_iff',
  rintros ⟨x, hx⟩ ε ε_pos,
  cases hA.dist_lt _ ε_pos x with n hn,
  rw _root_.eventually_nhds_iff,
  refine ⟨coe ⁻¹' (cylinder x n), _, _, by simp⟩,
  { rintros ⟨y, hy⟩ hyx,
    rw [mem_preimage, subtype.coe_mk, cylinder_eq_res, mem_set_of] at hyx,
    apply hn,
    { rw ← hyx,
      apply map_mem, },
    apply map_mem, },
  apply continuous_subtype_coe.is_open_preimage,
  apply is_open_cylinder,
end

/-- A scheme on a complete space with vanishing diameter
such that each set contains the closure of its children
induces a total map. -/
theorem closure_antitone.map_of_vanishing_diam [complete_space α]
  (hdiam : vanishing_diam A) (hanti : closure_antitone A) (hnonempty : ∀ l, (A l).nonempty) :
  (induced_map A).1 = univ :=
begin
  rw eq_univ_iff_forall,
  intro x,
  have : ∀ n : ℕ, (A (res x n)).nonempty := λ n, hnonempty _,
  choose u hu using this,
  have umem : ∀ n m : ℕ, n ≤ m → u m ∈ A (res x n),
  { have : antitone (λ n : ℕ, A (res x n)),
    { refine antitone_nat_of_succ_le _,
      intro n,
      apply hanti.antitone, },
    intros n m hnm,
    exact this hnm (hu _), },
  have : cauchy_seq u,
  { rw metric.cauchy_seq_iff,
    intros ε ε_pos,
    cases hdiam.dist_lt _ ε_pos x with n hn,
    use n,
    intros m₀ hm₀ m₁ hm₁,
    apply hn; apply umem; assumption, },
  cases cauchy_seq_tendsto_of_complete this with y hy,
  use y,
  rw mem_Inter,
  intro n,
  apply hanti _ (x n),
  apply mem_closure_of_tendsto hy,
  rw eventually_at_top,
  exact ⟨n.succ, umem _⟩,
end

end metric

end cantor_scheme

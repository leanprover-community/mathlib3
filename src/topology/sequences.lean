/-
Copyright (c) 2018 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow

Sequences in topological spaces.

In this file we define sequences in topological spaces and show how they are related to
filters and the topology. In particular, we
* associate a filter with a sequence and prove equivalence of convergence of the two,
* define the sequential closure of a set and prove that it's contained in the closure,
* define a type class "sequential_space" in which closure and sequential closure agree,
* define sequential continuity and show that it coincides with continuity in sequential spaces,
* provide an instance that shows that every first-countable (and in particular metric) space is a sequential space.

TODO:
* Sequential compactness should be handled here.
-/

import topology.basic
import topology.bases

open set filter

variables {α : Type*} {β : Type*}

local notation f ` ⟶ ` limit := tendsto f at_top (nhds limit)

/- Statements about sequences in general topological spaces. -/
section topological_space
variables [topological_space α] [topological_space β]

/-- A sequence converges in the sence of topological spaces iff the associated statement for filter
holds. -/
lemma topological_space.seq_tendsto_iff {x : ℕ → α} {limit : α} :
  tendsto x at_top (nhds limit) ↔
    ∀ U : set α, limit ∈ U → is_open U → ∃ n0 : ℕ, ∀ n ≥ n0, (x n) ∈ U :=
iff.intro
  (assume ttol : tendsto x at_top (nhds limit),
    show ∀ U : set α, limit ∈ U → is_open U → ∃ n0 : ℕ, ∀ n ≥ n0, (x n) ∈ U, from
      assume U limitInU isOpenU,
      have {n | (x n) ∈ U} ∈ at_top :=
        mem_map.mp $ le_def.mp ttol U $ mem_nhds_sets isOpenU limitInU,
      show ∃ n0 : ℕ, ∀ n ≥ n0, (x n) ∈ U, from mem_at_top_sets.mp this)
  (assume xtol : ∀ U : set α, limit ∈ U → is_open U → ∃ n0 : ℕ, ∀ n ≥ n0, (x n) ∈ U,
    suffices ∀ U, is_open U → limit ∈ U → x ⁻¹' U ∈ at_top,
      from tendsto_nhds.mpr this,
    assume U isOpenU limitInU,
    suffices ∃ n0 : ℕ, ∀ n ≥ n0, (x n) ∈ U, by simp [this],
    xtol U limitInU isOpenU)

/-- The sequential closure of a subset M ⊆ α of a topological space α is
the set of all p ∈ α which arise as limit of sequences in M. -/
def sequential_closure (M : set α) : set α :=
{p | ∃ x : ℕ → α, (∀ n : ℕ, x n ∈ M) ∧ (x ⟶ p)}

lemma subset_sequential_closure (M : set α) : M ⊆ sequential_closure M :=
assume p (_ : p ∈ M), show p ∈ sequential_closure M, from
  ⟨λ n, p, assume n, ‹p ∈ M›, tendsto_const_nhds⟩

def is_seq_closed (A : set α) : Prop := A = sequential_closure A

/-- A convenience lemma for showing that a set is sequentially closed. -/
lemma is_seq_closed_of_def {A : set α}
  (h : ∀(x : ℕ → α) (p : α), (∀ n : ℕ, x n ∈ A) → (x ⟶ p) → p ∈ A) : is_seq_closed A :=
show A = sequential_closure A, from subset.antisymm
  (subset_sequential_closure A)
  (show ∀ p, p ∈ sequential_closure A → p ∈ A, from
    (assume p ⟨x, _, _⟩, show p ∈ A, from h x p ‹∀ n : ℕ, ((x n) ∈ A)› ‹(x ⟶ p)›))

/-- The sequential closure of a set is contained in the closure of that set.
The converse is not true. -/
lemma sequential_closure_subset_closure (M : set α) : sequential_closure M ⊆ closure M :=
show ∀ p, p ∈ sequential_closure M → p ∈ closure M, from
assume p,
assume : ∃ x : ℕ → α, (∀ n : ℕ, ((x n) ∈ M)) ∧ (x ⟶ p),
let ⟨x, ⟨_, _⟩⟩ := this in
show p ∈ closure M, from
-- we have to show that p is in the closure of M
-- using mem_closure_iff, this is equivalent to proving that every open neighbourhood
-- has nonempty intersection with M, but this is witnessed by our sequence x
suffices ∀ O, is_open O → p ∈ O → O ∩ M ≠ ∅, from mem_closure_iff.mpr this,
have ∀ (U : set α), p ∈ U → is_open U → (∃ n0, ∀ n, n ≥ n0 → x n ∈ U), by rwa[←topological_space.seq_tendsto_iff],
assume O is_open_O p_in_O,
let ⟨n0, _⟩ := this O ‹p ∈ O› ‹is_open O› in
have (x n0) ∈ O, from ‹∀ n ≥ n0, x n ∈ O› n0 (show n0 ≥ n0, from le_refl n0),
have (x n0) ∈ O ∩ M, from ⟨this, ‹∀n, x n ∈ M› n0⟩,
set.ne_empty_of_mem this

/-- A set is sequentially closed if it is closed. -/
lemma is_seq_closed_of_is_closed (M : set α) (_ : is_closed M) : is_seq_closed M :=
suffices sequential_closure M ⊆ M, from
  set.eq_of_subset_of_subset (subset_sequential_closure M) this,
calc sequential_closure M ⊆ closure M : sequential_closure_subset_closure M
  ... = M : closure_eq_of_is_closed ‹is_closed M›

/-- The limit of a convergent sequence in a sequentially closed set is in that set.-/
lemma mem_of_is_seq_closed {A : set α} (_ : is_seq_closed A) {x : ℕ → α}
  (_ : ∀ n, x n ∈ A) {limit : α} (_ : (x ⟶ limit)) : limit ∈ A :=
have limit ∈ sequential_closure A, from
  show ∃ x : ℕ → α, (∀ n : ℕ, x n ∈ A) ∧ (x ⟶ limit), from ⟨x, ‹∀ n, x n ∈ A›, ‹(x ⟶ limit)›⟩,
eq.subst (eq.symm ‹is_seq_closed A›) ‹limit ∈ sequential_closure A›

/-- The limit of a convergent sequence in a closed set is in that set.-/
lemma mem_of_is_closed_sequential {A : set α} (_ : is_closed A) {x : ℕ → α}
  (_ : ∀ n, x n ∈ A) {limit : α} (_ : x ⟶ limit) : limit ∈ A :=
mem_of_is_seq_closed (is_seq_closed_of_is_closed A ‹is_closed A›) ‹∀ n, x n ∈ A› ‹(x ⟶ limit)›

/-- A sequential space is a space in which 'sequences are enough to probe the topology'. This can be
 formalised by demanding that the sequential closure and the closure coincide. The following
 statements show that other topological properties can be deduced from sequences in sequential
 spaces. -/
class sequential_space (α : Type*) [topological_space α] : Prop :=
(sequential_closure_eq_closure : ∀ M : set α, sequential_closure M = closure M)

/-- In a sequential space, a set is closed iff it's sequentially closed. -/
lemma is_seq_closed_iff_is_closed [sequential_space α] {M : set α} :
  is_seq_closed M ↔ is_closed M :=
iff.intro
  (assume _, closure_eq_iff_is_closed.mp (eq.symm
    (calc M = sequential_closure M : by assumption
        ... = closure M            : sequential_space.sequential_closure_eq_closure M)))
  (is_seq_closed_of_is_closed M)

/-- A function between topological spaces is sequentially continuous if it commutes with limit of
 convergent sequences. -/
def sequentially_continuous (f : α → β) : Prop :=
∀ (x : ℕ → α), ∀ {limit : α}, (x ⟶ limit) → (f∘x ⟶ f limit)

/- A continuous function is sequentially continuous. -/
lemma continuous.to_sequentially_continuous {f : α → β} (_ : continuous f) :
  sequentially_continuous f :=
assume x limit (_ : x ⟶ limit),
have tendsto f (nhds limit) (nhds (f limit)), from continuous.tendsto ‹continuous f› limit,
show (f ∘ x) ⟶ (f limit), from tendsto.comp this ‹(x ⟶ limit)›

/-- In a sequential space, continuity and sequential continuity coincide. -/
lemma continuous_iff_sequentially_continuous {f : α → β} [sequential_space α] :
  continuous f ↔ sequentially_continuous f :=
iff.intro
  (assume _, ‹continuous f›.to_sequentially_continuous)
  (assume : sequentially_continuous f, show continuous f, from
    suffices h : ∀ {A : set β}, is_closed A → is_seq_closed (f ⁻¹' A), from
      continuous_iff_is_closed.mpr (assume A _, is_seq_closed_iff_is_closed.mp $ h ‹is_closed A›),
    assume A (_ : is_closed A),
      is_seq_closed_of_def $
        assume (x : ℕ → α) p (_ : ∀ n, f (x n) ∈ A) (_ : x ⟶ p),
        have (f ∘ x) ⟶ (f p), from ‹sequentially_continuous f› x ‹(x ⟶ p)›,
        show f p ∈ A, from
          mem_of_is_closed_sequential ‹is_closed A› ‹∀ n, f (x n) ∈ A› ‹(f∘x ⟶ f p)›)

end topological_space

namespace topological_space

namespace first_countable_topology

/-- Every first-countable space is sequential. -/
instance [topological_space α] [first_countable_topology α] : sequential_space α :=
⟨show ∀ M, sequential_closure M = closure M, from assume M,
  suffices closure M ⊆ sequential_closure M,
    from set.subset.antisymm (sequential_closure_subset_closure M) this,
  assume (p : α) (hp : p ∈ closure M),
  exists.elim (mono_seq_of_has_countable_basis _
    (nhds_generated_countable p)) $ assume g ⟨gmon, gbasis⟩,
  have x : ∀ i, (g i ∩ M : set α), {
    rw mem_closure_iff_nhds at hp,
    intro i, apply classical.choice, rw coe_nonempty_iff_ne_empty,
    apply hp, rw gbasis, rw ← le_principal_iff, apply lattice.infi_le_of_le i _, apply le_refl _
  },
  have gssnhds : ∀ s ∈ nhds p, ∃ i, g i ⊆ s, {
    intro s, rw gbasis, rw mem_infi,
    { simp, intros i hi, use i, assumption },
    { apply directed_of_mono, intros, apply principal_mono.mpr, apply gmon, assumption },
    { apply_instance }
  },
  ⟨λ i, (x i).val, by intro i; simp [(x i).property.right],
    begin
      rw tendsto_at_top', intros s nhdss,
      rcases gssnhds s nhdss with ⟨i, hi⟩,
      use i, intros j hij, apply hi, apply gmon _ _ hij,
      simp [(x j).property.left]
    end⟩⟩

end first_countable_topology

end topological_space

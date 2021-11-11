/-
Copyright (c) 2021 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Kyle Miller
-/

import combinatorics.simple_graph.subgraph
import data.nat.lattice

/-!
# Graph Coloring

This module defines colorings of simple graphs (also known as proper
colorings in the literature). A graph coloring is the attribution of
"colors" to all of its vertices such that adjacent vertices have
different colors. A coloring can be represented as a homomorphism into
a complete graph, whose vertices represent the colors.

## Main definitions

* `G.coloring α` is the type of `α`-colorings of a simple graph `G`,
  with `α` being the set of available colors. The type is defined to
  be homomorphisms from `G` into the complete graph on `α`.

* `G.colorable n` is the proposition that `G` is `n`-colorable, which
  is whether there exists a coloring with at most *n* colors.

* `G.chromatic_number` is the minimal `n` such that `G` is
  `n`-colorable, or `0` if it cannot be colored with finitely many
  colors.

## Todo:

  * Gather material from:
    * https://github.com/leanprover-community/mathlib/blob/simple_graph_matching/src/combinatorics/simple_graph/coloring.lean
    * https://github.com/kmill/lean-graphcoloring/blob/master/src/graph.lean

  * Lowerbound for cliques

  * Trees

  * Bipartite graphs

  * Planar graphs

  * develop API for partial colorings, likely as colorings of subgraphs (`H.coe.coloring α`)
-/

universes u v

namespace simple_graph
variables {V : Type u} (G : simple_graph V)

/--
An `α`-coloring of a simple graph `G` is a homomorphism of `G` into the complete graph on `α`.
This is also known as a proper coloring.
-/
abbreviation coloring (α : Type v) := G →g (⊤ : simple_graph α)

variables {G} {α : Type v} (C : G.coloring α)

lemma coloring.valid (v w : V) (h : G.adj v w) : C v ≠ C w :=
C.map_rel h

/--
Construct a term of `simple_graph.coloring` using a function that
assigns vertices to colors and a proof that it is as proper coloring.

(Note: this is a definitionally the constructor for `simple_graph.hom`,
but with a syntactically better proper coloring hypothesis.)
-/
@[pattern] def coloring.mk
  (color : V → α)
  (valid : ∀ {v w : V}, G.adj v w → color v ≠ color w) :
  G.coloring α := ⟨color, @valid⟩

variables (G)

/-- Whether a graph can be colored by at most `n` colors. -/
def colorable (n : ℕ) : Prop := nonempty (G.coloring (fin n))

/-- The coloring of an empty graph. -/
def coloring_of_is_empty [is_empty V] : G.coloring α :=
coloring.mk is_empty_elim (λ v, is_empty_elim)

lemma colorable_of_is_empty [is_empty V] (n : ℕ) : G.colorable n :=
⟨G.coloring_of_is_empty⟩

lemma is_empty_of_colorable_zero (h : G.colorable 0) : is_empty V :=
begin
  split,
  intro v,
  obtain ⟨i, hi⟩ := h.some v,
  exact nat.not_lt_zero _ hi,
end

/-- The "tautological" coloring of a graph, using the vertices of the graph as colors. -/
def self_coloring : G.coloring V :=
coloring.mk id (λ v w, G.ne_of_adj)

/-- The chromatic number of a graph is the minimal number of colors needed to color it.
If `G` isn't colorable with finitely many colors, this will be 0. -/
noncomputable def chromatic_number : ℕ :=
Inf { n : ℕ | G.colorable n }

-- TODO move to basic.lean
/--
Embeddings of types induce embeddings of complete graphs on those types.
-/
def complete_graph.of_embedding {α β : Type*} (f : α ↪ β) : complete_graph α ↪g complete_graph β :=
{ to_fun := f,
  inj' := f.inj',
  map_rel_iff' := by simp }

/-- Given an embedding, there is an induced embedding of colorings. -/
def recolor_of_embedding {α β : Type*} (f : α ↪ β) : G.coloring α ↪ G.coloring β :=
{ to_fun := λ C, (complete_graph.of_embedding f).to_hom.comp C,
  inj' := begin -- this was strangely painful; seems like missing lemmas about embeddings
    intros C C' h,
    dsimp only at h,
    ext v,
    apply (complete_graph.of_embedding f).inj',
    change ((complete_graph.of_embedding f).to_hom.comp C) v = _,
    rw h,
    refl,
  end }

/-- Given an equivalence, there is an induced equivalence between colorings. -/
def recolor_of_equiv {α β : Type*} (f : α ≃ β) : G.coloring α ≃ G.coloring β :=
{ to_fun := G.recolor_of_embedding f.to_embedding,
  inv_fun := G.recolor_of_embedding f.symm.to_embedding,
  left_inv := λ C, by { ext v, apply equiv.symm_apply_apply },
  right_inv := λ C, by { ext v, apply equiv.apply_symm_apply } }

/-- There is a noncomputable embedding of `α`-colorings to `β`-colorings if
`β` has at least as large a cardinality as `α`. -/
noncomputable def recolor_of_card_le {α β : Type*} [fintype α] [fintype β]
  (hn : fintype.card α ≤ fintype.card β) :
  G.coloring α ↪ G.coloring β :=
G.recolor_of_embedding $ (function.embedding.nonempty_of_card_le hn).some

variables {G}

lemma colorable.of_le {n m : ℕ} (hc : G.colorable n) (h : n ≤ m) : G.colorable m :=
⟨G.recolor_of_card_le (by simp [h]) hc.some⟩

lemma coloring.to_colorable [fintype α] (C : G.coloring α) :
  G.colorable (fintype.card α) :=
⟨G.recolor_of_card_le (by simp) C⟩

lemma colorable_of_fintype (G : simple_graph V) [fintype V] :
  G.colorable (fintype.card V) :=
G.self_coloring.to_colorable

/-- Noncomputably get a coloring from colorability. -/
noncomputable def colorable.to_coloring [fintype α] {n : ℕ} (hc : G.colorable n)
  (hn : n ≤ fintype.card α) :
  G.coloring α :=
begin
  rw ←fintype.card_fin n at hn,
  exact G.recolor_of_card_le hn hc.some,
end

lemma colorable_iff_exists_bdd_nat_coloring (n : ℕ) :
  G.colorable n ↔ ∃ (C : G.coloring ℕ), ∀ v, C v < n :=
begin
  split,
  { rintro hc,
    have C : G.coloring (fin n) := hc.to_coloring (by simp),
    let f := complete_graph.of_embedding (fin.coe_embedding n).to_embedding,
    use f.to_hom.comp C,
    intro v,
    cases C with color valid,
    exact fin.is_lt (color v), },
  { rintro ⟨C, Cf⟩,
    refine ⟨coloring.mk _ _⟩,
    { exact λ v, ⟨C v, Cf v⟩, },
    { rintro v w hvw,
      simp only [complete_graph_eq_top, top_adj, subtype.mk_eq_mk, ne.def],
      exact C.valid v w hvw, } }
end

lemma colorable_set_nonempty_of_colorable {n : ℕ} (h : G.colorable n) :
  {n : ℕ | G.colorable n}.nonempty :=
⟨n, h⟩

lemma chromatic_number_bdd_below : bdd_below {n : ℕ | G.colorable n} :=
⟨0, λ _ _, zero_le _⟩

lemma chromatic_number_le [fintype α] (C : G.coloring α) :
  G.chromatic_number ≤ fintype.card α :=
cInf_le chromatic_number_bdd_below C.to_colorable

lemma colorable_chromatic_number {m : ℕ} (hc : G.colorable m) :
  G.colorable G.chromatic_number :=
begin
  dsimp only [chromatic_number],
  rw nat.Inf_def,
  apply nat.find_spec,
  exact colorable_set_nonempty_of_colorable hc,
end

lemma colorable_chromatic_number_of_fintype (G : simple_graph V) [fintype V] :
  G.colorable G.chromatic_number :=
colorable_chromatic_number G.colorable_of_fintype

lemma chromatic_number_leq_one_of_subsingleton (G : simple_graph V) [subsingleton V] :
  G.chromatic_number ≤ 1 :=
begin
  rw chromatic_number,
  apply cInf_le chromatic_number_bdd_below,
  fsplit,
  refine coloring.mk (λ _, 0) _,
  intros v w,
  rw subsingleton.elim v w,
  simp,
end

lemma chromatic_number_eq_zero_of_isempty (G : simple_graph V) [is_empty V] :
  G.chromatic_number = 0 :=
begin
  rw ←nonpos_iff_eq_zero,
  apply cInf_le chromatic_number_bdd_below,
  apply colorable_of_is_empty,
end

lemma is_empty_of_chromatic_number_eq_zero (G : simple_graph V) [fintype V]
  (h : G.chromatic_number = 0) : is_empty V :=
begin
  have h' := G.colorable_chromatic_number_of_fintype,
  rw h at h',
  exact G.is_empty_of_colorable_zero h',
end

lemma zero_le_chromatic_number [nonempty V] {n : ℕ} (hc : G.colorable n) :
  0 < G.chromatic_number :=
begin
  rw [nat.lt_iff_add_one_le, chromatic_number, zero_add],
  apply le_cInf (colorable_set_nonempty_of_colorable hc),
  intros m hm,
  by_contra h',
  simp only [not_le, nat.lt_one_iff] at h',
  subst h',
  obtain ⟨i, hi⟩ := hm.some (classical.arbitrary V),
  exact nat.not_lt_zero _ hi,
end

-- todo: move to basic.lean
/-- The induced map for spanning subgraphs, which is the identity. -/
def map {G G' : simple_graph V} (h : G ≤ G') : G →g G' :=
{ to_fun := id,
  map_rel' := h }

lemma colorable_lower_bound {G' : simple_graph V} (h : G ≤ G') (n : ℕ) (hc : G'.colorable n) :
  G.colorable n :=
⟨hc.some.comp (map h)⟩

lemma chromatic_number_le_of_forall_imp {G' : simple_graph V}
  {m : ℕ} (hc : G'.colorable m)
  (h : ∀ n, G'.colorable n → G.colorable n) :
  G.chromatic_number ≤ G'.chromatic_number :=
begin
  apply cInf_le chromatic_number_bdd_below,
  apply h,
  apply colorable_chromatic_number hc,
end

lemma chromatic_number_lower_bound (G' : simple_graph V)
  {m : ℕ} (hc : G'.colorable m) (h : G ≤ G') :
  G.chromatic_number ≤ G'.chromatic_number :=
begin
  apply chromatic_number_le_of_forall_imp hc,
  exact colorable_lower_bound h,
end

lemma chromatic_number_minimal [fintype α] (C : G.coloring α)
  (h : ∀ (C' : G.coloring α), set.range C' = set.univ) :
  G.chromatic_number = fintype.card α :=
begin
  apply le_antisymm,
  { apply chromatic_number_le C, },
  { by_contra hc,
    simp only [not_le] at hc,
    obtain ⟨n, cn, hc⟩ := exists_lt_of_cInf_lt
      (colorable_set_nonempty_of_colorable C.to_colorable) hc,
    specialize h (cn.to_coloring (le_of_lt hc)),
    -- hc and h are contradictory, using the fact that
    -- (cn.to_coloring (le_of_lt hc)) uses at most n colors
    -- (not sure how to organize this proof though;
    -- needs more lemmas about to_coloring)
    sorry
  },
end

end simple_graph

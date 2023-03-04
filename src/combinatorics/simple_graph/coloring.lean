/-
Copyright (c) 2021 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Kyle Miller
-/

import combinatorics.simple_graph.clique
import data.nat.lattice
import data.setoid.partition
import order.antichain

/-!
# Graph Coloring

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This module defines colorings of simple graphs (also known as proper
colorings in the literature). A graph coloring is the attribution of
"colors" to all of its vertices such that adjacent vertices have
different colors. A coloring can be represented as a homomorphism into
a complete graph, whose vertices represent the colors.

## Main definitions

* `G.coloring α` is the type of `α`-colorings of a simple graph `G`,
  with `α` being the set of available colors. The type is defined to
  be homomorphisms from `G` into the complete graph on `α`, and
  colorings have a coercion to `V → α`.

* `G.colorable n` is the proposition that `G` is `n`-colorable, which
  is whether there exists a coloring with at most *n* colors.

* `G.chromatic_number` is the minimal `n` such that `G` is
  `n`-colorable, or `0` if it cannot be colored with finitely many
  colors.

* `C.color_class c` is the set of vertices colored by `c : α` in the
  coloring `C : G.coloring α`.

* `C.color_classes` is the set containing all color classes.

## Todo:

  * Gather material from:
    * https://github.com/leanprover-community/mathlib/blob/simple_graph_matching/src/combinatorics/simple_graph/coloring.lean
    * https://github.com/kmill/lean-graphcoloring/blob/master/src/graph.lean

  * Trees

  * Planar graphs

  * Chromatic polynomials

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

lemma coloring.valid {v w : V} (h : G.adj v w) : C v ≠ C w :=
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

/--
The color class of a given color.
-/
def coloring.color_class (c : α) : set V := {v : V | C v = c}

/-- The set containing all color classes. -/
def coloring.color_classes : set (set V) := (setoid.ker C).classes

lemma coloring.mem_color_class (v : V) :
  v ∈ C.color_class (C v) := by exact rfl

lemma coloring.color_classes_is_partition :
  setoid.is_partition C.color_classes :=
setoid.is_partition_classes (setoid.ker C)

lemma coloring.mem_color_classes {v : V} : C.color_class (C v) ∈ C.color_classes :=
⟨v, rfl⟩

lemma coloring.color_classes_finite [finite α] : C.color_classes.finite :=
setoid.finite_classes_ker _

lemma coloring.card_color_classes_le [fintype α] [fintype C.color_classes] :
  fintype.card C.color_classes ≤ fintype.card α :=
setoid.card_classes_ker_le C

lemma coloring.not_adj_of_mem_color_class {c : α} {v w : V}
  (hv : v ∈ C.color_class c) (hw : w ∈ C.color_class c) :
  ¬G.adj v w :=
λ h, C.valid h (eq.trans hv (eq.symm hw))

lemma coloring.color_classes_independent (c : α) :
  is_antichain G.adj (C.color_class c) :=
λ v hv w hw h, C.not_adj_of_mem_color_class hv hw

-- TODO make this computable
noncomputable
instance [fintype V] [fintype α] : fintype (coloring G α) :=
begin
  classical,
  change fintype (rel_hom G.adj (⊤ : simple_graph α).adj),
  apply fintype.of_injective _ rel_hom.coe_fn_injective,
  apply_instance,
end

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

/-- Given an embedding, there is an induced embedding of colorings. -/
def recolor_of_embedding {α β : Type*} (f : α ↪ β) : G.coloring α ↪ G.coloring β :=
{ to_fun := λ C, (embedding.complete_graph f).to_hom.comp C,
  inj' := begin -- this was strangely painful; seems like missing lemmas about embeddings
    intros C C' h,
    dsimp only at h,
    ext v,
    apply (embedding.complete_graph f).inj',
    change ((embedding.complete_graph f).to_hom.comp C) v = _,
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

lemma colorable.mono {n m : ℕ} (h : n ≤ m) (hc : G.colorable n) : G.colorable m :=
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

lemma colorable.of_embedding {V' : Type*} {G' : simple_graph V'}
  (f : G ↪g G') {n : ℕ} (h : G'.colorable n) : G.colorable n :=
⟨(h.to_coloring (by simp)).comp f⟩

lemma colorable_iff_exists_bdd_nat_coloring (n : ℕ) :
  G.colorable n ↔ ∃ (C : G.coloring ℕ), ∀ v, C v < n :=
begin
  split,
  { rintro hc,
    have C : G.coloring (fin n) := hc.to_coloring (by simp),
    let f := embedding.complete_graph fin.coe_embedding,
    use f.to_hom.comp C,
    intro v,
    cases C with color valid,
    exact fin.is_lt (color v), },
  { rintro ⟨C, Cf⟩,
    refine ⟨coloring.mk _ _⟩,
    { exact λ v, ⟨C v, Cf v⟩, },
    { rintro v w hvw,
      simp only [fin.mk_eq_mk, ne.def],
      exact C.valid hvw, } }
end

lemma colorable_set_nonempty_of_colorable {n : ℕ} (hc : G.colorable n) :
  {n : ℕ | G.colorable n}.nonempty :=
⟨n, hc⟩

lemma chromatic_number_bdd_below : bdd_below {n : ℕ | G.colorable n} :=
⟨0, λ _ _, zero_le _⟩

lemma chromatic_number_le_of_colorable {n : ℕ} (hc : G.colorable n) :
  G.chromatic_number ≤ n :=
begin
  rw chromatic_number,
  apply cInf_le chromatic_number_bdd_below,
  fsplit,
  exact classical.choice hc,
end

lemma chromatic_number_le_card [fintype α] (C : G.coloring α) :
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

lemma colorable_chromatic_number_of_fintype (G : simple_graph V) [finite V] :
  G.colorable G.chromatic_number :=
by { casesI nonempty_fintype V, exact colorable_chromatic_number G.colorable_of_fintype }

lemma chromatic_number_le_one_of_subsingleton (G : simple_graph V) [subsingleton V] :
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

lemma is_empty_of_chromatic_number_eq_zero (G : simple_graph V) [finite V]
  (h : G.chromatic_number = 0) : is_empty V :=
begin
  have h' := G.colorable_chromatic_number_of_fintype,
  rw h at h',
  exact G.is_empty_of_colorable_zero h',
end

lemma chromatic_number_pos [nonempty V] {n : ℕ} (hc : G.colorable n) :
  0 < G.chromatic_number :=
begin
  apply le_cInf (colorable_set_nonempty_of_colorable hc),
  intros m hm,
  by_contra h',
  simp only [not_le, nat.lt_one_iff] at h',
  subst h',
  obtain ⟨i, hi⟩ := hm.some (classical.arbitrary V),
  exact nat.not_lt_zero _ hi,
end

lemma colorable_of_chromatic_number_pos (h : 0 < G.chromatic_number) :
  G.colorable G.chromatic_number :=
begin
  obtain ⟨h, hn⟩ := nat.nonempty_of_pos_Inf h,
  exact colorable_chromatic_number hn,
end

lemma colorable.mono_left {G' : simple_graph V} (h : G ≤ G') {n : ℕ}
  (hc : G'.colorable n) : G.colorable n :=
⟨hc.some.comp (hom.map_spanning_subgraphs h)⟩

lemma colorable.chromatic_number_le_of_forall_imp {V' : Type*} {G' : simple_graph V'}
  {m : ℕ} (hc : G'.colorable m)
  (h : ∀ n, G'.colorable n → G.colorable n) :
  G.chromatic_number ≤ G'.chromatic_number :=
begin
  apply cInf_le chromatic_number_bdd_below,
  apply h,
  apply colorable_chromatic_number hc,
end

lemma colorable.chromatic_number_mono (G' : simple_graph V)
  {m : ℕ} (hc : G'.colorable m) (h : G ≤ G') :
  G.chromatic_number ≤ G'.chromatic_number :=
hc.chromatic_number_le_of_forall_imp (λ n, colorable.mono_left h)

lemma colorable.chromatic_number_mono_of_embedding {V' : Type*} {G' : simple_graph V'}
  {n : ℕ} (h : G'.colorable n) (f : G ↪g G') :
  G.chromatic_number ≤ G'.chromatic_number :=
h.chromatic_number_le_of_forall_imp (λ _, colorable.of_embedding f)

lemma chromatic_number_eq_card_of_forall_surj [fintype α] (C : G.coloring α)
  (h : ∀ (C' : G.coloring α), function.surjective C') :
  G.chromatic_number = fintype.card α :=
begin
  apply le_antisymm,
  { apply chromatic_number_le_card C, },
  { by_contra hc,
    rw not_le at hc,
    obtain ⟨n, cn, hc⟩ := exists_lt_of_cInf_lt
      (colorable_set_nonempty_of_colorable C.to_colorable) hc,
    rw ←fintype.card_fin n at hc,
    have f := (function.embedding.nonempty_of_card_le (le_of_lt hc)).some,
    have C' := cn.some,
    specialize h (G.recolor_of_embedding f C'),
    change function.surjective (f ∘ C') at h,
    have h1 : function.surjective f := function.surjective.of_comp h,
    have h2 := fintype.card_le_of_surjective _ h1,
    exact nat.lt_le_antisymm hc h2, },
end

lemma chromatic_number_bot [nonempty V] :
  (⊥ : simple_graph V).chromatic_number = 1 :=
begin
  let C : (⊥ : simple_graph V).coloring (fin 1) :=
    coloring.mk (λ _, 0) (λ v w h, false.elim h),
  apply le_antisymm,
  { exact chromatic_number_le_card C, },
  { exact chromatic_number_pos C.to_colorable, },
end

@[simp] lemma chromatic_number_top [fintype V] :
  (⊤ : simple_graph V).chromatic_number = fintype.card V :=
begin
  apply chromatic_number_eq_card_of_forall_surj (self_coloring _),
  intro C,
  rw ←finite.injective_iff_surjective,
  intros v w,
  contrapose,
  intro h,
  exact C.valid h,
end

lemma chromatic_number_top_eq_zero_of_infinite (V : Type*) [infinite V] :
  (⊤ : simple_graph V).chromatic_number = 0 :=
begin
  let n := (⊤ : simple_graph V).chromatic_number,
  by_contra hc,
  replace hc := pos_iff_ne_zero.mpr hc,
  apply nat.not_succ_le_self n,
  convert_to (⊤ : simple_graph {m | m < n + 1}).chromatic_number ≤ _,
  { simp, },
  refine (colorable_of_chromatic_number_pos hc).chromatic_number_mono_of_embedding _,
  apply embedding.complete_graph,
  exact (function.embedding.subtype _).trans (infinite.nat_embedding V),
end

/-- The bicoloring of a complete bipartite graph using whether a vertex
is on the left or on the right. -/
def complete_bipartite_graph.bicoloring (V W : Type*) :
  (complete_bipartite_graph V W).coloring bool :=
coloring.mk (λ v, v.is_right) begin
  intros v w,
  cases v; cases w; simp,
end

lemma complete_bipartite_graph.chromatic_number {V W : Type*} [nonempty V] [nonempty W] :
  (complete_bipartite_graph V W).chromatic_number = 2 :=
begin
  apply chromatic_number_eq_card_of_forall_surj (complete_bipartite_graph.bicoloring V W),
  intros C b,
  have v := classical.arbitrary V,
  have w := classical.arbitrary W,
  have h : (complete_bipartite_graph V W).adj (sum.inl v) (sum.inr w) := by simp,
  have hn := C.valid h,
  by_cases he : C (sum.inl v) = b,
  { exact ⟨_, he⟩ },
  { by_cases he' : C (sum.inr w) = b,
    { exact ⟨_, he'⟩ },
    { exfalso,
      cases b;
      simp only [eq_tt_eq_not_eq_ff, eq_ff_eq_not_eq_tt] at he he';
      rw [he, he'] at hn;
      contradiction }, },
end

/-! ### Cliques -/

lemma is_clique.card_le_of_coloring {s : finset V} (h : G.is_clique s)
  [fintype α] (C : G.coloring α) :
  s.card ≤ fintype.card α :=
begin
  rw is_clique_iff_induce_eq at h,
  have f : G.induce ↑s ↪g G := embedding.induce ↑s,
  rw h at f,
  convert fintype.card_le_of_injective _ (C.comp f.to_hom).injective_of_top_hom using 1,
  simp,
end

lemma is_clique.card_le_of_colorable {s : finset V} (h : G.is_clique s)
  {n : ℕ} (hc : G.colorable n) :
  s.card ≤ n :=
begin
  convert h.card_le_of_coloring hc.some,
  simp,
end

-- TODO eliminate `finite V` constraint once chromatic numbers are refactored.
-- This is just to ensure the chromatic number exists.
lemma is_clique.card_le_chromatic_number [finite V] {s : finset V} (h : G.is_clique s) :
  s.card ≤ G.chromatic_number :=
by { casesI nonempty_fintype V,
  exact h.card_le_of_colorable G.colorable_chromatic_number_of_fintype }

protected
lemma colorable.clique_free {n m : ℕ} (hc : G.colorable n) (hm : n < m) : G.clique_free m :=
begin
  by_contra h,
  simp only [clique_free, is_n_clique_iff, not_forall, not_not] at h,
  obtain ⟨s, h, rfl⟩ := h,
  exact nat.lt_le_antisymm hm (h.card_le_of_colorable hc),
end

-- TODO eliminate `finite V` constraint once chromatic numbers are refactored.
-- This is just to ensure the chromatic number exists.
lemma clique_free_of_chromatic_number_lt [finite V] {n : ℕ} (hc : G.chromatic_number < n) :
  G.clique_free n :=
G.colorable_chromatic_number_of_fintype.clique_free hc

end simple_graph

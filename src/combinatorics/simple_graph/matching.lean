/-
Copyright (c) 2020 Alena Gusakov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov, Kyle Miller
-/
import data.fintype.basic
import data.sym2
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.coloring
import combinatorics.simple_graph.subgraph
import data.fin
import data.set.finite
/-!
# Matchings


## Main definitions

* a `matching` on a simple graph is a subset of its edge set such that
   no two edges share an endpoint.

* a `perfect_matching` on a simple graph is a matching in which every
   vertex belongs to an edge.

TODO:
  - Lemma stating that the existence of a perfect matching on `G` implies that
    the cardinality of `V` is even (assuming it's finite)
  - Hall's Marriage Theorem
  - Tutte's Theorem
  - consider coercions instead of type definition for `matching`:
    https://github.com/leanprover-community/mathlib/pull/5156#discussion_r532935457
  - consider expressing `matching_verts` as union:
    https://github.com/leanprover-community/mathlib/pull/5156#discussion_r532906131

TODO: Tutte and Hall require a definition of subgraphs.
-/
open finset
universe u

namespace simple_graph
variables {V : Type u} (G : simple_graph V)

/--
A matching on `G` is a subset of its edges such that no two edges share a vertex.
-/
structure matching :=
(edges : set (sym2 V))
(sub_edges : edges ⊆ G.edge_set)
(disjoint : ∀ (x y ∈ edges) (v : V), v ∈ x → v ∈ y → x = y)

/-- The empty matching of a graph. -/
def matching.empty : G.matching :=
⟨∅, set.empty_subset _, λ _ _ hx, false.elim (set.not_mem_empty _ hx)⟩

instance : inhabited (matching G) :=
⟨matching.empty G⟩

namespace matching
variables {G}

/--
`M.support` is the set of vertices of `G` that are
contained in some edge of the matching `M`
-/
def support (M : G.matching) : set V :=
{v : V | ∃ x, x ∈ M.edges ∧ v ∈ x}

@[simp] lemma mem_support (M : G.matching) (v : V) :
  v ∈ M.support ↔ ∃ x, x ∈ M.edges ∧ v ∈ x :=
iff.rfl

@[simp] lemma empty_support : (matching.empty G).support = ∅ :=
by { ext, simp [empty], }

/--
A perfect matching `M` on graph `G` is a matching such that
  every vertex is contained in an edge of `M`.
-/
def is_perfect (M : G.matching) : Prop :=
M.support = set.univ

lemma is_perfect_iff (M : G.matching) :
  M.is_perfect ↔ ∀ (v : V), ∃ e, e ∈ M.edges ∧ v ∈ e :=
set.eq_univ_iff_forall

/--
A matching defines a partion involutive function on the vertex set.
-/
noncomputable
def opposite (M : G.matching) (v : V) (h : v ∈ M.support) : V :=
(classical.some_spec ((M.mem_support v).mp h)).2.other

lemma opposite_spec (M : G.matching) (v : V) (h : v ∈ M.support) :
  ⟦(v, M.opposite v h)⟧ ∈ M.edges :=
begin
  erw sym2.mem_other_spec, exact (classical.some_spec ((M.mem_support v).mp h)).1,
end

lemma opposite_mem_support (M : G.matching) (v : V) (h : v ∈ M.support) :
  M.opposite v h ∈ M.support :=
⟨⟦(v, M.opposite v h)⟧, M.opposite_spec v h, sym2.mk_has_mem_right _ _⟩

lemma opposite_invol (M : G.matching) (v : V) (h : v ∈ M.support) :
  M.opposite (M.opposite v h) (M.opposite_mem_support v h) = v :=
begin
  have h1 := M.opposite_spec v h,
  have h2 := M.opposite_spec (M.opposite v h) (M.opposite_mem_support v h),
  have hh := M.disjoint _ _ h1 h2 (M.opposite v h) (sym2.mk_has_mem_right _ _) (sym2.mk_has_mem _ _),
  rw sym2.eq_swap at hh, rw sym2.congr_right at hh,
  exact hh.symm,
end

@[simp]
lemma opposite_bij (M : G.matching) (v w : V) (hv : v ∈ M.support) (hw : w ∈ M.support) :
  M.opposite v hv = M.opposite w hw ↔ v = w :=
begin
  split,
  { intro h,
    have h1 := M.opposite_spec v hv,
    have h2 := M.opposite_spec w hw,
    rw h at h1,
    have hh := M.disjoint _ _ h1 h2 (M.opposite w hw) (sym2.mk_has_mem_right _ _) (sym2.mk_has_mem_right _ _),
    exact sym2.congr_left.mp hh },
  { rintro rfl, refl },
end

lemma opposite_ne (M : G.matching) (v : V) (h : v ∈ M.support) :
  M.opposite v h ≠ v :=
(G.edge_not_loop (M.sub_edges (M.opposite_spec v h))).symm

/--
Given a set saturated by a matching, get the set of vertices opposite that set.
-/
def opposite_set (M : G.matching) (S : set V) (h : S ⊆ M.support) : set V :=
{v | ∃ (w : V) (wel : w ∈ S), M.opposite w (h wel) = v}

@[simp]
lemma mem_opposite_set (M : G.matching) (S : set V) (h : S ⊆ M.support) (v : V) :
  v ∈ M.opposite_set S h ↔ ∃ (w : V) (wel : w ∈ S), M.opposite w (h wel) = v :=
by refl

lemma opposite_set_subneighbor_set' (M : G.matching) (S : set V) (h : S ⊆ M.support) :
  M.opposite_set S h ⊆ G.neighbor_set' S :=
begin
  rintros v ⟨w, wel, hw⟩,
  rw mem_neighbor_set',
  use [w, wel],
  have hh := M.sub_edges (M.opposite_spec w (h wel)),
  simpa [hw] using hh,
end

lemma mem_iff_mem_opposite_set (M : G.matching)
  (S : set V) (hS : S ⊆ M.support) (v : V) (hv : v ∈ M.support) :
  v ∈ S ↔ M.opposite v hv ∈ M.opposite_set S hS :=
by simp [opposite_set]

lemma opposite_set_saturated (M : G.matching) (S : set V) (h : S ⊆ M.support) :
  (M.opposite_set S h) ⊆ M.support :=
begin
  rintros v ⟨w, H, hv⟩,
  use ⟦(w, v)⟧,
  refine ⟨_, sym2.mk_has_mem_right _ _⟩,
  convert M.opposite_spec w (h H),
  rw hv,
end

noncomputable
def opposite_set_equiv (M : G.matching) (S : set V) (h : S ⊆ M.support) :
  M.opposite_set S h ≃ S :=
{ to_fun := λ vv, ⟨classical.some vv.2, begin
    rcases classical.some_spec vv.2 with ⟨hw, _⟩,
    exact hw
  end⟩,
  inv_fun := λ vv, ⟨M.opposite vv.1 (h vv.2), (M.mem_iff_mem_opposite_set S h _ (h vv.2)).mp vv.2⟩,
  left_inv := λ ⟨v, hv⟩, begin
    rcases classical.some_spec hv with ⟨he, hop⟩,
    simp [hop],
  end,
  right_inv := λ ⟨v, hv⟩, begin
    dsimp only, congr,
    rcases classical.some_spec ((M.mem_iff_mem_opposite_set S h v (h hv)).mp hv) with ⟨w, hw⟩,
    rwa M.opposite_bij at hw,
  end }

noncomputable
instance opposite_set.fintype
  (M : G.matching) {S : set V} [fintype S] (h : S ⊆ M.support) :
  fintype (M.opposite_set S h) :=
fintype.of_equiv _ ((M.opposite_set_equiv S h).symm)

lemma opposites_card_eq (M : G.matching) {S : set V} [fintype S] (h : S ⊆ M.support) :
  fintype.card (M.opposite_set S h) = fintype.card S :=
begin
--  rw ←fintype.card_coe,
  exact fintype.card_congr (M.opposite_set_equiv S h),
end

lemma opposite_set_support_eq (M : G.matching) :
  (M.opposite_set M.support (set.subset.refl M.support)) = M.support :=
begin
  apply set.subset.antisymm,
  { apply M.opposite_set_saturated, },
  { rintros v ⟨e, he, hv⟩,
    have hs : v ∈ M.support := ⟨e, he, hv⟩,
    exact ⟨M.opposite v hs, M.opposite_mem_support v hs, M.opposite_invol v hs⟩, },
end

/-noncomputable
def support_opposite (M : G.matching) : M.support → M.support :=
λ vv, ⟨M.opposite vv.1 (vv.2 ∈ M.support),
begin
  have h := (M.mem_iff_mem_opposite_set M.support M.saturates_support _ (M.saturates_support vv.2)).mp vv.2,
  rwa M.opposite_set_support_eq at h,
end⟩

lemma support_opposite_invol (M : G.matching) : function.involutive M.support_opposite :=
by { rintros ⟨v, hv⟩, dunfold support_opposite, simp only [subtype.mk_eq_mk, M.opposite_invol] }

lemma support_opposite_ne (M : G.matching) (v : M.support) :
  M.support_opposite v ≠ v :=
by { rcases v with ⟨v, hv⟩, simp [support_opposite, opposite_ne] }-/

lemma card_even_if_fixedpoint_free_invol {α : Type*} [fintype α] [decidable_eq α] (f : α → α)
  (hi : function.involutive f) (hn : ∀ x, x ≠ f x) : even (fintype.card α) :=
begin
/-  let orbit : α → finset α := λ x, {x, f x},
  have horbit' : ∀ x, orbit x = orbit (f x),
  { intro x, ext y, simp [hi x], rw or.comm },
  have horbit : ∀ x y, y ∈ orbit x → f y ∈ orbit x,
  { intros x y hy, simp only [finset.mem_insert, finset.mem_singleton] at hy,
    rcases hy with ⟨rfl, hy⟩, simp, rw hy, rw hi, simp },
  have htwo : ∀ x, (orbit x).card = 2,
  { intro x,
    rw finset.card_insert_of_not_mem, rw card_singleton,
    rw mem_singleton, apply hn },
  let orbits : set (finset α) := orbit '' set.univ,
  have hne : ∀ (s : orbits), s.1.nonempty,
  { rintro ⟨s, hs⟩, use classical.some hs, have aa := (classical.some_spec hs).2,
    convert_to classical.some hs ∈ s,
    have hh : classical.some hs ∈ orbit (classical.some hs), simp only [mem_insert, true_or, eq_self_iff_true],
    rwa aa at hh, },
  choose repr hrepr using hne,
  let R0 := repr '' set.univ,
  let R1 := R0ᶜ,
  have hc : ∀ x, x ∈ R0 ↔ f x ∈ R1,
  { intro x,
    split,
    rintros ⟨⟨o1,ho1⟩,-,hr1⟩ ⟨⟨o2,ho2⟩,-,hr2⟩,
    have hh1 := hrepr ⟨o1, ho1⟩,
    have hh2 := hrepr ⟨o2, ho2⟩,
    rw hr1 at hh1, rw hr2 at hh2,
    have heq : o1 = o2,
    { rcases ho1 with ⟨y1,_,hy1⟩, rcases ho2 with ⟨y2,_,hy2⟩,
      rw [←hy1,←hy2],
      simp only at hh1 hh2, rw ←hy1 at hh1, rw ← hy2 at hh2,
      simp at hh1 hh2,
      cases hh1, subst y1, cases hh2, subst y2, apply horbit',
      have hh2' := hi.injective hh2, subst y2,
      have hh1' := congr_arg f hh1, rw hi y1 at hh1', subst y1,
      cases hh2, subst y2, rw hh2, rw ←horbit', },
    subst o2,
    rw hr1 at hr2, exact hn _ hr2,

    simp, intro h,
    by_contra h', push_neg at h',
    specialize h (orbit x) ⟨x,by simp⟩,
    specialize h' (orbit x) ⟨x,by simp⟩,
    sorry
  }, -/
  sorry
end

/-lemma support_card_even [fintype V] [decidable_eq V] (M : G.matching) : even (fintype.card M.support) :=
card_even_if_fixedpoint_free_invol M.support_opposite (support_opposite_invol M) (λ x, (support_opposite_ne M x).symm)-/

/-
noncomputable for now...
instance decide_edge_set_is_matching [fintype V] [decidable_eq V] [decidable_rel G.adj] :
  decidable_pred (λ (s : set (sym2 V)), ∃ (M : G.matching), M.edges = s) :=
begin
  intro edges,
  by_cases sub_edges : edges ⊆ G.edge_set,
  by_cases disjoint : ∀ (x y ∈ edges) (v : V), v ∈ x → v ∈ y → x = y,
  apply decidable.is_true,
  use ⟨edges, sub_edges, disjoint⟩,
  apply decidable.is_false, dsimp, rintro ⟨M, h⟩, cases M, subst edges, exact disjoint M_disjoint,
  apply decidable.is_false, dsimp, rintro ⟨M, h⟩, cases M, subst edges, exact sub_edges M_sub_edges,
end
-/

noncomputable
instance matching_fintype [fintype V] [decidable_eq V] : fintype G.matching :=
begin
  let S := {s : set (sym2 V) | ∃ (M : G.matching), M.edges = s},
  haveI : fintype S := by apply_instance,
  let eqv : G.matching ≃ S :=
  { to_fun := λ M, ⟨M.edges, by use M⟩,
    inv_fun := λ s, {edges := s.1,
                     sub_edges := begin rcases s with ⟨s,M,h⟩, dsimp only, rw ←h, exact M.sub_edges end,
                     disjoint := begin rcases s with ⟨s,M,h⟩, dsimp only, rw ←h, exact M.disjoint end},
    left_inv := begin intro x, cases x, simp, end,
    right_inv := begin intro x, cases x, simp, end,
  },
  exact fintype.of_equiv _ eqv.symm,
end


end matching

open finset
variables (M : G.matching) [fintype M.support]

section bipartite
variables [fintype V] [decidable_eq V] (f : G.bipartition)

/-lemma not_saturates_iff_exists : ¬M.saturates (f.color_set 0) ↔ ∃ u, u ∈ f.color_set 0 ∧ ¬u ∈ M.support :=
begin
  rw ←not_iff_not, push_neg, rw ←set.subset, refl,
end-/

def matching.disjoint_union (M M' : G.matching) (h : disjoint M.support M'.support) : G.matching :=
{ edges := M.edges ∪ M'.edges,
  sub_edges :=
    begin
      simp [M.sub_edges, M'.sub_edges],
    end,
  disjoint := λ e f he hf v hve hvf,
    begin
      let w := hve.other,
      simp at *,
      wlog : e ∈ M.edges := he using M M',
      have hvM : v ∈ M.support,
      rw matching.mem_support,
      refine ⟨e, he, hve⟩,
      have hwM : w ∈ M.support,
      rw matching.mem_support,
      refine ⟨e, he, sym2.mem_other_mem hve⟩,
      have hfM : f ∉ M'.edges,
      let x := hvf.other,
      have hvM' : v ∉ M'.support,
      apply set.disjoint_left.mp h hvM,
      by_contra hfM',
      apply hvM',
      rw matching.mem_support,
      refine ⟨f, hfM', hvf⟩,
      apply M.disjoint e f he,
      tauto,
      exact hve,
      exact hvf,
    end }

/-def matching.disjoint_union' (M M' : G.matching) (e f : sym2 V) (v : V)
 (h : (e ∈ M.edges ∧ f ∈ M'.edges) ∧ v ∈ e ∩ f → e = f) : G.matching :=
{ edges := M.edges ∪ M'.edges,
  sub_edges :=
    begin
      simp [M.sub_edges, M'.sub_edges],
    end,
  disjoint := λ e f he hf v hve hvf,
    begin
      have : v ∈ M.support ∪ M'.support,
      simp at *,
      cases he with hM hM',
      use e,
      refine ⟨hM, hve⟩,
      right,
      use e,
      refine ⟨hM', hve⟩,
      sorry,
    end }-/
  -- h : (e ∈ M.edges ∧ f ∈ M'.edges) ∧ v ∈ e ∩ f → e = f

/--
`alternating_path b u v` is a path starting at u and ending at v, where the edges alternating between being in M and being outside M.
-/
inductive alternating_path (M : G.matching) : bool → V → V → Type u
| start (u : V) : alternating_path tt u u
| consM {u v w : V} (p : alternating_path tt u v) (h : ⟦(v,w)⟧ ∈ M.edges) : alternating_path ff u w
| consNot {u v w : V} (p : alternating_path ff u v) (h : ⟦(v,w)⟧ ∈ G.edge_set \ M.edges) : alternating_path tt u w


-- If Hall's condition is true for $G$, we show that it is satisfied for $G'$
-- induced by $S \cup \Gamma(S)$ for any $S \subseteq A$.
-- shit


theorem hall_marriage_theorem
  (h2 : fintype.card (f.color_set 0) ≤ fintype.card (f.color_set 1)) :
  (∃ (M : G.matching), (f.color_set 0) ⊆ M.support) ↔
  (∀ (S ⊆ f.color_set 0),
    fintype.card S ≤ fintype.card (G.neighbor_set' S)) :=
begin
  split,
  { rintros ⟨M, hM⟩ S hs,
    have Ssat := set.subset.trans hs hM,
    rw ←M.opposites_card_eq Ssat,
    have Sopp := M.opposites_card_eq Ssat,
    exact set.card_le_of_subset (M.opposite_set_subneighbor_set' S Ssat) },
  { intro hh,
    -- we have `to_partial`, that's what i need to do my strong induction proof
    -- either every subset of the left class has a neighbour set larger than it,
    -- or there's one where the neighbour set is the same
    have h : (∀ (S ⊆ f.color_set 0), fintype.card S < fintype.card (G.neighbor_set' S)) ∨
        (∃ (S ⊆ f.color_set 0), fintype.card S = fintype.card (G.neighbor_set' S)),
    { --simp_rw le_iff_eq_or_lt at hh,
      rw or_iff_not_imp_left,
      intro ha,
      push_neg at ha,
      cases ha with x hx,
      use x,
      specialize hh x,
      cases hx with h3 h4,
      specialize hh h3,
      have h7 := le_antisymm hh h4,
      split,
      exact h3,
      exact h7 },
      cases h with ha he,
      {

        sorry },
      -- jesus fuck
    -- ∀ x, x ≤ f x → (∀ x, x < f x) ∨ (∃ x, x = f x)
    --by_contra hv,

    -- induction on `|f.color_set 0|` using partial colorings
      --
      -- have `partial_coloring.restrict f.to_partial`
    -- base case: `|f.color_set 0| = 0`, i.e. `f.color_set 0 = ∅`
      -- this is trivial

    -- IH: `∀ (S ⊆ f.color_set 0), fintype.card S ≤ fintype.card (G.neighbor_set' S))`
    -- ` → ∃ (M : G.matching), (f.color_set 0) ⊆ M.support`
      -- what i mean by this is `f.color_set 0` when you push `f` through to an induced subgraph
    sorry },
end

/- TO DO:

-


-/

end bipartite

end simple_graph

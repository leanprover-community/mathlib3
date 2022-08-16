import data.set.finite
import data.sym.sym2
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import topology.metric_space.basic
import data.setoid.partition
import category_theory.functor.basic
import .mathlib

open function finset set classical simple_graph.walk relation

local attribute [instance] prop_decidable

universes u v w

noncomputable theory

namespace simple_graph


variables  {V : Type u} (G : simple_graph V)
            [Gpc : preconnected G] (K : finset V)


@[reducible, simp] def compl (S : set V) : subgraph G := (⊤ : subgraph G).delete_verts S

lemma outside_to_compl {S : set V} {v : V} (h : v ∉ S) : v ∈ (G.compl S).verts := by simp [h]

instance compl_coe {K L : set V} {G : simple_graph V} (h : K ⊆ L) : has_coe (set ↥((G.compl K).verts)) (set ↥((G.compl L).verts)) := {
  coe := λ S, λ vL,
    match vL with
      | ⟨v, htop, hnL⟩ := S ⟨v, htop, λ hK, hnL (h hK)⟩
    end }

-- `def` rather than `instance` because of typeclass problems
def finset_verts_compl_coe {K L : finset V} {G : simple_graph V} (h : K ⊆ L) : (set ↥((G.compl ↑K).verts)) → (set ↥((G.compl ↑L).verts)) := λ S, λ vL,
      match vL with
        | ⟨v, htop, hnL⟩ := S ⟨v, htop, λ hK, hnL (h hK)⟩
      end

def conn_comp_outside : Type u :=
  (G.compl K).coe.connected_component

/- The vertices in the compl of `K` that lie in the component `C` -/
@[reducible, simp] def conn_comp_outside.verts {G : simple_graph V} {K : finset V} (C : conn_comp_outside G K) :=
  {v : (G.compl K).verts | connected_component_mk _ v = C}

def inf_conn_comp_outside :=
 {C : G.conn_comp_outside K // infinite C.verts}

def fin_conn_comp_outside :=
  {C : G.conn_comp_outside K // finite C.verts}


namespace conn_comp_outside

@[reducible] def component_of (v : (G.compl K).verts) : conn_comp_outside G K := connected_component_mk _ v

def component_of_set (S : set V) (hnonempty : S.nonempty) (hdisjoint : disjoint S K) (hconn : subgraph.connected (subgraph.induce (G.compl K) S)) : conn_comp_outside G K := sorry -- Strategy: pick a random point in `S` and form the connected component containing it. The choice does not matter since `S` is connected

/- The boundary of a set, consisting of all adjacent vertices not in the set -/
def bdry (S : set V) := {v : (G.compl S).verts | ∃ x ∈ S, G.adj v x}

/- This is the portion of the connected component that is a part of the boundary -/
def border {G : simple_graph V} {K : finset V} (C : conn_comp_outside G K) : set (compl G K).verts := C.verts ∩ (bdry G K)

lemma components_cover : set.Union (λ C : conn_comp_outside G K, C.verts) = ⊤ :=
begin
  ext, simp [verts], use component_of G K x,
end

lemma components_nonempty : ∀ (C : conn_comp_outside G K), nonempty (C.verts) :=
begin
  apply connected_component.ind,
  rintro v, apply nonempty.intro,
  use v, dsimp [verts], refl,
end

-- TODO: Show that the boundary is precisely the union of all the borders.
lemma bdry_eq_border_union : (bdry G K) = set.Union (λ C : conn_comp_outside G K, C.border) :=
  calc bdry G K = ⊤ ∩ (bdry G K) : by simp
  ... = (set.Union (λ C : conn_comp_outside G K, C.verts)) ∩ (bdry G K) : by rw [components_cover]
  ... = set.Union (λ C : conn_comp_outside G K, C.verts ∩ (bdry G K)) : (bdry G K).Union_inter (λ (i : conn_comp_outside G K), i.verts)
  ... = set.Union (λ C : conn_comp_outside G K, C.border) : by refl

-- for mathlib:
lemma symm_iff {X : Type u} (P : X → X → Prop) : (∀ {a b}, P a b → P b a) → (∀ {a b}, P a b ↔ P b a) := by tidy

lemma bdry.iff : bdry G K = set.Union (λ k : K, {v : (G.compl K).verts | v.val ∈ G.neighbor_set k}) :=
begin
  ext, unfold bdry, simp,
  conv in (G.adj ↑_ _)
    {rw [symm_iff G.adj (λ _ _, G.adj_symm)],},
end

lemma bdry_finite [Glocfin : locally_finite G] : (bdry G K).finite :=
begin
  rw [bdry.iff], refine finite_Union _, rintro k,
  apply set.finite.preimage,
  { apply injective.inj_on, tidy, },
  { exact (neighbor_set G k).to_finite, }
end

lemma border_finite [locally_finite G] (C : conn_comp_outside G K) :  (border C).finite :=
begin
  refine finite.inter_of_right _ C.verts, apply bdry_finite,
end

-- for mathlib
lemma reachable_of_adj {u v : V} : G.adj u v → G.reachable u v := sorry

lemma walk.to_boundary {G : simple_graph V} (S : set V) (src : (G.compl S).verts) (tgt : S) (w : G.walk ↑src tgt) : ∃ b ∈ bdry G S, (G.compl S).coe.reachable src b :=
  match src, tgt, w with
    | ⟨_, hSc⟩, ⟨_, _⟩, nil := by {simp at hSc, contradiction,}
    | src, tgt, cons' _ b _ adj_src w' :=
      if h : b ∈ S then
       ⟨src, ⟨b, h, adj_src⟩, reachable.rfl⟩
      else by {
        rcases (_match ⟨b, G.outside_to_compl h⟩ tgt w') with ⟨b', hbdry, hreach⟩,
        use b', use hbdry,
        refine reachable.trans _ hreach,
        apply reachable_of_adj,
        dsimp [adj],
        tidy?,
      }
  end

lemma border_nonempty [Gpc : preconnected G] (Knempty : K.nonempty) : ∀ (C : conn_comp_outside G K), nonempty (border C) :=
begin
  rcases Knempty with ⟨k,kK⟩,
  apply connected_component.ind,
  rintro ⟨x, xKc⟩, -- is it possible without this pattern matching?
  let w := (Gpc x k).some,
  have : k ∉ (↑K)ᶜ := set.not_mem_compl_iff.mpr kK,
  have : x ∉ K := by {simp at xKc, assumption,},
  rcases walk.pred_adj_non_pred x k w Kᶜ ‹x ∉ K› ‹k ∉ (↑K)ᶜ› with ⟨u, v, adj_uv, uKc, vKcc⟩,
  apply nonempty.intro, dsimp only [border, bdry],
  use u,
  {apply outside_to_compl, assumption,},
  {simp, split,
    -- we need a walk entirely outside `K`
    { dsimp only [reachable], apply nonempty.intro, sorry,},
    {use v, exact ⟨set.not_mem_compl_iff.mp vKcc, adj_uv⟩,} } -- from tidy (but with a tidier output)
end

lemma finite_components [Glf : locally_finite G] [Gpc : preconnected G] :
  fintype (conn_comp_outside G K) :=
begin
  by_cases Knempty : K.nonempty,
  {
     refine fintype_of_not_infinite _,
     intro hinf,
     sorry -- needs some lemmas about boundary
  },
  { rw [finset.not_nonempty_iff_eq_empty] at Knempty,
    subst Knempty,
    dsimp [conn_comp_outside, simple_graph.subgraph.delete_verts],
    have : (univ : set V) \ ∅ = univ := sdiff_bot,
    rw [this, ← simple_graph.induce_eq_coe_induce_top],
    refine ⟨{_}, _⟩,
    sorry, -- need to use `Gpc` here
    sorry
   }
end

lemma nonempty_components (Vinf : (univ : set V).infinite) : nonempty (conn_comp_outside G K) :=
begin
  suffices inh : nonempty (G.compl K).verts, from nonempty.intro (component_of G K (nonempty.some inh)),
  suffices inf : ((univ : set V) \ ↑K).infinite, from by { rcases set.nonempty_def.mp (set.infinite.nonempty inf) with ⟨v, h⟩, exact nonempty.intro ⟨v, h⟩,},
  apply set.infinite.diff,
  exact Vinf, exact K.finite_to_set,
end


lemma conn_comp_outside_back_unique {K L : finset V} (h : K ⊆ L) :
∀ C : conn_comp_outside G L,
  ∃! D : conn_comp_outside G K,
    C.verts ⊆ (finset_verts_compl_coe h D.verts) := sorry

-- this is the `bwd_map`
def conn_comp_outside_back {K L : finset V} (h : K ⊆ L) (C : conn_comp_outside G L) : conn_comp_outside G K :=
  classical.some (exists_of_exists_unique (conn_comp_outside_back_unique G h C))

def conn_comp_outside_back.iff {K L : finset V} (h : K ⊆ L) (C : conn_comp_outside G L) (D : conn_comp_outside G K):
  conn_comp_outside_back G h C = D ↔ C.verts ⊆ (finset_verts_compl_coe h D.verts) :=
begin
  split,
  { rintro equ, induction equ, exact (exists_of_exists_unique (conn_comp_outside_back_unique G h C)).some_spec},
  { exact unique_of_exists_unique (conn_comp_outside_back_unique G h C) (exists_of_exists_unique (conn_comp_outside_back_unique G h C)).some_spec},
end

lemma conn_comp_outside_back.refl (K : finset V) (C : conn_comp_outside G K) :
  conn_comp_outside_back G (finset.subset.refl K) C = C :=
  sorry
/-
unique_of_exists_unique
  (conn_comp_outside_back_unique G (finset.subset.refl K) C)
  (classical.some_spec (exists_of_exists_unique (conn_comp_outside_back_unique G (finset.subset.refl K) C)))
  (set.subset.refl C.verts)
-/

lemma conn_comp_outside_back.comm  {J K L : finset V} (k : J ⊆ K) (h : K ⊆ L) (C : conn_comp_outside G L) :
  conn_comp_outside_back G k (conn_comp_outside_back G h C) = conn_comp_outside_back G (k.trans h) C := sorry
/-
unique_of_exists_unique
  (conn_comp_outside_back_unique G (k.trans h) C)
  ((exists_of_exists_unique (conn_comp_outside_back_unique G h C)).some_spec.trans
     (exists_of_exists_unique (conn_comp_outside_back_unique G k (conn_comp_outside_back G h C))).some_spec)
  (classical.some_spec (exists_of_exists_unique (conn_comp_outside_back_unique G (k.trans h) C)))
-/

-- TODO: An infinite graph has at least one infinite connected component
lemma inf_graph_has_conn_comp [infinite V] : nonempty (conn_comp_outside G K) := sorry

-- TODO: A locally finite graph has finitely many infinite connected components
lemma inf_graph_fin_inf_conn_comp [locally_finite G] : finite (inf_conn_comp_outside G K) := sorry

-- def ends_system := category_theory.functor.mk (conn_comp_outside G) (conn_comp_outside_back G)

-- TODO: Mapping of connected sets under homomorphisms
-- TODO: Show that components are preserved under isomorphisms

-- Returns K ∪ (all finite connected components in the compl)
def conn_comp_outside.extend_fin [Glf : locally_finite G] (K : finset V) : finset V := sorry

-- TODO: Build all the associated lemmas. Mainly prove that the resulting set of connected components are precisely the infinite connected components of the original graph.

-- TODO: Prove lemmas about cofinite infinite components

end conn_comp_outside

end simple_graph

/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.big_operators.basic
import combinatorics.quiver
import data.real.nnreal
import data.sym.sym2

/-!
# Indexed multigraphs
-/

open finset function
open_locale big_operators nnreal

variables {F E α β 𝒸 W : Type*}

structure index_multigraph (E α : Type*) :=
(edges : E → sym2 α)

structure index_weight_multigraph (E α W : Type*) extends index_multigraph E α :=
(edge_weight : E → W)

namespace index_weight_multigraph
section weight
variables (G : index_weight_multigraph E α W)

structure edge_coloring (G : index_weight_multigraph E α W) (𝒸 : Type*) :=
(color : E → 𝒸)

def weight_coloring : G.edge_coloring W := ⟨G.edge_weight⟩

def is_matching (s : set E) : Prop := ∀ (e₁ e₂ ∈ s) x, x ∈ G.edges e₁ → x ∈ G.edges e₂ → e₁ = e₂

def is_perfect_matching (s : set E) : Prop := G.is_matching s ∧ ∀ x, ∃ e ∈ s, x ∈ G.edges e

@[ext] structure perfect_matching :=
(get : α → E)
(mem_get (a : α) : a ∈ G.edges (get a))
(matching_get : G.is_matching (set.range get))

noncomputable instance [fintype α] [fintype E] : fintype G.perfect_matching :=
begin
  haveI := classical.dec_eq α,
  exact fintype.of_injective perfect_matching.get perfect_matching.ext,
end

end weight

section weight_color
variables (G : index_weight_multigraph E α (𝒸 × W))

namespace perfect_matching
variables {G} (G' : G.perfect_matching)

def ivc (ecol : E → 𝒸) (a : α) : 𝒸 := ecol $ G'.get a

section comm_monoid
variables [decidable_eq E] [fintype α] [comm_monoid W]

protected def weight : W := ∏ e in univ.image G'.get, (G.edge_weight e).2

end comm_monoid

end perfect_matching

section semiring
variables [fintype α] [fintype E] [comm_semiring W]

open_locale classical

noncomputable def coloring_weight (vcol : α → 𝒸) : W :=
∑ G' in (univ : finset G.perfect_matching).filter
  (λ G', ∀ a, vcol a = (G.edge_weight $ G'.get a).1),
    G'.weight

def weight_monochromatic : Prop :=
(∀ c, G.coloring_weight (const _ c) = 1) ∧
  ∀ vcol, G.coloring_weight vcol ≠ 0 → ∃ c, vcol = const _ c

variables [fintype 𝒸]

noncomputable def nonzero_vertex_coloring : finset (α → 𝒸) :=
univ.filter $ λ vcol, G.coloring_weight vcol ≠ 0

lemma weight_bogdanov2 (hα : 5 ≤ fintype.card α) : G.nonzero_vertex_coloring.card ≤ 2 := sorry

lemma weight_bogdanov3 : G.nonzero_vertex_coloring.card ≤ 3 := sorry

end semiring
end weight_color

section real
variables [fintype E] [fintype α] [fintype 𝒸] (G : index_weight_multigraph E α (𝒸 × ℝ))

lemma exists_le_card_nonzero_vertex_coloring :
  ∃ G : index_weight_multigraph E α (𝒸 × ℝ), 0 ≤ G.nonzero_vertex_coloring.card :=
begin
  refine ⟨{ edges := _,
  edge_weight := _ }, _⟩,
end

lemma canon_bogdanov3 : G.nonzero_vertex_coloring.card ≤ 3 := sorry

end real

section nnreal
variables [fintype E] [fintype α] [fintype 𝒸] (G : index_weight_multigraph E α (𝒸 × ℝ≥0))

lemma canon_bogdanov2 (hα : 5 ≤ fintype.card α) : G.nonzero_vertex_coloring.card ≤ 2 := sorry

lemma canon_bogdanov3 : G.nonzero_vertex_coloring.card ≤ 3 := sorry

end nnreal
end index_weight_multigraph

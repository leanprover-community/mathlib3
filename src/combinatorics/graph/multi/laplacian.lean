/-
Copyright (c) 2022 Yaël Dillies, Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Antoine Labelle
-/
import combinatorics.graph.multi.link

/-!
# Laplacian of a multigraph

-/

open fintype (card)
open_locale big_operators

namespace multigraph
variables (G : multigraph) (R M : Type*) [ring R] [add_comm_group M] [module R M]


/-- The coboundary of a `0`-chain. It sends a `0`-chain `f` to the `1`-chain obtained by taking the
difference of `f` at the two endpoints of each edge. -/
@[simps] def coboundary : (G → M) →ₗ[R] C₁ G R M :=
{ to_fun := λ f, ⟨λ e, f (G.fst e) - f (G.snd e), λ e, by simp⟩ ,
  map_add' := λ f g, by { ext, simp [add_sub_add_comm] },
  map_smul' := λ r f, by { ext, simp [smul_sub] } }

variable {G}

@[simp] lemma coboundary_apply (f : G → M) (e : G.E) :
  coboundary G R M f e = f (G.fst e) - f (G.snd e) := rfl

variable (G)

/-- The genus of a graph is its first Betti number, namely the number of eges minus the number of
vertices plus one. -/
def genus [fintype G] [fintype G.E] : ℤ := card G.E - card G + 1

variables [locally_finite G]

/-- The boundary of a `1`-chain. It sends a `1`-chain `f` to the `0`-chain obtained by summing `f`
over the edges going out at each vertex. -/
@[simps] def boundary : C₁ G R M →ₗ[R] G → M :=
{ to_fun := λ f v, ∑ e : G.link v, f e,
  map_add' := λ f g, by { ext, simp [finset.sum_add_distrib] },
  map_smul' := λ r f, by { ext, simp [finset.smul_sum] } }

/-- The Laplacian of a multigraph. -/
def laplacian : (G → M) →ₗ[R] G → M := G.boundary R M ∘ₗ G.coboundary R M

variable {G}

@[simp] lemma laplacian_apply (f : G → M) (v : G) :
  G.laplacian R M f v = G.degree v • f v - ∑ e : G.link v, f (G.snd e) :=
by simp [laplacian, degree, fintype.card]

variables [fintype G]

lemma sum_laplacian (f : G → M) : ∑ v, G.laplacian R M f v = 0 :=
by { haveI := G.fintype_E, simp [sum_link (f ∘ G.snd)] }

end multigraph

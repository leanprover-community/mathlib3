/-
Copyright (c) 2022 Yaël Dillies, Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Antoine Labelle
-/
import algebra.module.submodule.basic
import combinatorics.graph.multi.basic

/-!
# Degree of a vertex in a multigraph

This file defines stuff.

## Main declarations

* `multigraph.link`: Edges incident to a given vertex.
* `multigraph.C₁`: `1`-chains.
* `multigraph.coboundary`:
* `multigraph.boundary`:
* `multigraph.laplacian`: The Laplacian of a multigraph.
-/

open_locale big_operators

namespace multigraph
variables (G : multigraph) (R M : Type*) [ring R] [add_comm_group M] [module R M]

/-- The link of a vertex is the edges that leave from it. -/
@[reducible] def link (v : G.V) := {e : G.E // G.fst e = v}

@[simp] lemma link_fst (v : G.V) (e : G.link v) : G.fst e = v := e.2

/-- A multigraph is locally finite if each vertex has only finitely many edges leaving from it. -/
abbreviation locally_finite := Π v, fintype (G.link v)

/-- The degree of a vertex is the number of edges incident to it. -/
def degree [locally_finite G] (v : G.V) : ℕ := fintype.card (G.link v)

/-- The `1`-chains with coefficients in `M`. -/
def C₁ : submodule R (G.E → M) :=
{ carrier := {f | ∀ e, f (G.inv e) = -f e},
  zero_mem' := by simp,
  add_mem' := λ f g hf hg e, by simp [hf e, hg e, add_comm],
  smul_mem' := λ r f hf e, by simp [hf e] }

namespace C₁

instance : has_coe_to_fun (C₁ G R M) (λ _, G.E → M) := ⟨subtype.val⟩

@[simp, norm_cast] lemma coe_zero : ⇑(0 : C₁ G R M) = 0 := rfl
@[simp, norm_cast] lemma coe_neg (f : C₁ G R M) : ⇑(-f) = -f := rfl
@[simp, norm_cast] lemma coe_add (f g : C₁ G R M) : ⇑(f + g) = f + g := rfl
@[simp, norm_cast] lemma coe_sub (f g : C₁ G R M) : ⇑(f - g) = f - g := rfl
@[simp, norm_cast] lemma coe_smul (r : R) (f : C₁ G R M) : ⇑(r • f) = r • f := rfl
@[simp, norm_cast] lemma coe_nsmul (n : ℕ) (f : C₁ G R M) : ⇑(n • f) = n • f := rfl
@[simp, norm_cast] lemma coe_zsmul (n : ℤ) (f : C₁ G R M) : ⇑(n • f) = n • f := rfl

@[simp] lemma zero_apply (e : G.E) : (0 : C₁ G R M) e = 0 := rfl
@[simp] lemma neg_apply (f : C₁ G R M) (e : G.E) : (-f) e = -f e := rfl
@[simp] lemma add_apply (f g : C₁ G R M) (e : G.E) : (f + g) e = f e + g e := rfl
@[simp] lemma sub_apply (f g : C₁ G R M) (e : G.E) : (f - g) e = f e - g e := rfl
@[simp] lemma smul_apply (r : R) (f : C₁ G R M) (e : G.E) : (r • f) e = r • f e := rfl
@[simp] lemma nsmul_apply (n : ℕ) (f : C₁ G R M) (e : G.E) : (n • f) e = n • f e := rfl
@[simp] lemma zsmul_apply (n : ℤ) (f : C₁ G R M) (e : G.E) : (n • f) e = n • f e := rfl

end C₁

/-- The coboundary of a divisor. -/
@[simps] def coboundary : (G.V → M) →ₗ[R] C₁ G R M :=
{ to_fun := λ f, ⟨λ e, f (G.fst e) - f (G.snd e), λ e, by simp⟩ ,
  map_add' := λ f g, by { ext, simp [add_sub_add_comm] },
  map_smul' := λ r f, by { ext, simp [smul_sub] } }

@[simp] lemma coboundary_apply (f : G.V → M) (e : G.E) :
  coboundary G R M f e = f (G.fst e) - f (G.snd e) := rfl

variables [locally_finite G]

/-- The boundary of a `1`-chain. -/
@[simps] def boundary : C₁ G R M →ₗ[R] G.V → M :=
{ to_fun := λ f v, ∑ e : G.link v, f e,
  map_add' := λ f g, by { ext, simp [finset.sum_add_distrib] },
  map_smul' := λ r f, by { ext, simp [finset.smul_sum] } }

/-- The Laplacian of a multigraph. -/
def laplacian : (G.V → M) →ₗ[R] G.V → M := G.boundary R M ∘ₗ G.coboundary R M

lemma laplacian_apply (f : G.V → M) (v : G.V) :
  G.laplacian R M f v = G.degree v • f v - ∑ e : G.link v, f (G.snd e) :=
by simp [laplacian, degree, fintype.card]

end multigraph

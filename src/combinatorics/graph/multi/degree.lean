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

open fintype (card)
open_locale big_operators

namespace multigraph
variables (G : multigraph) (R M : Type*) [ring R] [add_comm_group M] [module R M]

/-- The link of a vertex is the edges that leave from it. -/
@[reducible] def link (v : G) := {e : G.E // G.fst e = v}

@[simp] lemma link_fst (v : G) (e : G.link v) : G.fst e = v := e.2

/-- The type of egdes is a disjoint union of all the links. -/
@[simps] def union_link : (Σ (v : G), G.link v) ≃ G.E :=
{ to_fun := λ e, e.snd,
  inv_fun := λ e, ⟨G.fst e, ⟨e, rfl⟩⟩,
  left_inv := λ e, by {ext; simp},
  right_inv := λ e, rfl }

/-- A multigraph is locally finite if each vertex has only finitely many edges leaving from it. -/
abbreviation locally_finite := Π v, fintype (G.link v)

/-- The degree of a vertex is the number of edges incident to it. -/
def degree [locally_finite G] (v : G) : ℕ := fintype.card (G.link v)

instance [fintype G] [locally_finite G] : fintype G.E := fintype.of_equiv _ G.union_link

variable {G}

@[simp] lemma sum_link [fintype G] [locally_finite G] {α : Type*} [add_comm_monoid α]
  (f : G.E → α) : ∑ (v : G) (e : G.link v), f e = ∑ (e : G.E), f e :=
by {rw finset.sum_sigma', exact fintype.sum_equiv G.union_link _ _ (λ _, rfl)}

@[simp] lemma sum_map_inv [fintype G] [locally_finite G] {α : Type*} [add_comm_monoid α]
  (f : G.E → α) : ∑ (e : G.E), f (G.inv e) = ∑ (e : G.E), f e :=
equiv.sum_comp inv_equiv _

@[simp] lemma sum_map_fst [fintype G] [locally_finite G] {α : Type*} [add_comm_monoid α]
  (f : G → α) : ∑ (e : G.E), f (G.fst e) = ∑ (v : G), G.degree v • f v :=
by {simp_rw [←sum_link,link_fst, finset.sum_const], refl}

@[simp] lemma sum_map_snd [fintype G] [locally_finite G] {α : Type*} [add_comm_monoid α]
  (f : G → α) : ∑ (e : G.E), f (G.snd e) = ∑ (v : G), G.degree v • f v :=
by simp_rw [←inv_fst, sum_map_inv (f ∘ G.fst), sum_map_fst]

variable (G)

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

@[simp] lemma sum_laplacian (f : G → M) : ∑ v, G.laplacian R M f v = 0 :=
by simp [sum_link (f ∘ G.snd)]

end multigraph

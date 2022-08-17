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

/-- The type of egdes is the disjoint union of all the links. -/
@[simps] def sigma_link : (Σ v, G.link v) ≃ G.E :=
{ to_fun := λ e, e.snd,
  inv_fun := λ e, ⟨G.fst e, ⟨e, rfl⟩⟩,
  left_inv := λ e, by {ext; simp},
  right_inv := λ e, rfl }

/-- A multigraph is locally finite if each vertex has only finitely many edges leaving from it. -/
abbreviation locally_finite := Π v, fintype (G.link v)

/-- The degree of a vertex is the number of edges incident to it. -/
def degree [locally_finite G] (v : G) : ℕ := fintype.card (G.link v)

/-- A locally finite multigraph with finitely many vertices has finitely many edges. -/
def fintype_E [fintype G] [locally_finite G] : fintype G.E := fintype.of_equiv _ G.sigma_link

section sum
variables {G} {α : Type*} [add_comm_monoid α] [fintype G.E]

@[simp] lemma sum_map_inv (f : G.E → α) : ∑ e, f (G.inv e) = ∑ e, f e := equiv.sum_comp inv_equiv _

variables [fintype G] [locally_finite G]

@[simp] lemma sum_link (f : G.E → α) : ∑ v (e : G.link v), f e = ∑ e, f e :=
by { rw finset.sum_sigma', exact fintype.sum_equiv G.sigma_link _ _ (λ _, rfl) }

@[simp] lemma sum_map_fst (f : G → α) : ∑ e, f (G.fst e) = ∑ v, G.degree v • f v :=
by { simp_rw [←sum_link, link_fst, finset.sum_const], refl }

@[simp] lemma sum_map_snd (f : G → α) : ∑ e, f (G.snd e) = ∑ v, G.degree v • f v :=
by simp_rw [←inv_fst, sum_map_inv (f ∘ G.fst), sum_map_fst]

end sum

/-- The `1`-chains with coefficients in `M`. -/
def C₁ : submodule R (G.E → M) :=
{ carrier := {f | ∀ e, f (G.inv e) = -f e},
  zero_mem' := by simp,
  add_mem' := λ f g hf hg e, by simp [hf e, hg e, add_comm],
  smul_mem' := λ r f hf e, by simp [hf e] }

@[simp] lemma coe_C₁ : (C₁ G R M : set (G.E → M)) = {f | ∀ e, f (G.inv e) = -f e} := rfl
@[simp] lemma mem_C₁ {f : G.E → M} : f ∈ C₁ G R M ↔ ∀ e, f (G.inv e) = -f e := iff.rfl

namespace C₁

instance fun_like : fun_like (C₁ G R M) G.E (λ _, M) :=
{ coe := coe,
  coe_injective' := subtype.coe_injective }

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
end multigraph

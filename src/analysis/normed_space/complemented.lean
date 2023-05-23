/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.normed_space.banach
import analysis.normed_space.finite_dimension

/-!
# Complemented subspaces of normed vector spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A submodule `p` of a topological module `E` over `R` is called *complemented* if there exists
a continuous linear projection `f : E →ₗ[R] p`, `∀ x : p, f x = x`. We prove that for
a closed subspace of a normed space this condition is equivalent to existence of a closed
subspace `q` such that `p ⊓ q = ⊥`, `p ⊔ q = ⊤`. We also prove that a subspace of finite codimension
is always a complemented subspace.

## Tags

complemented subspace, normed vector space
-/

variables {𝕜 E F G : Type*} [nontrivially_normed_field 𝕜] [normed_add_comm_group E]
  [normed_space 𝕜 E] [normed_add_comm_group F] [normed_space 𝕜 F] [normed_add_comm_group G]
  [normed_space 𝕜 G]

noncomputable theory

open linear_map (ker range)

namespace continuous_linear_map

section

variables [complete_space 𝕜]

lemma ker_closed_complemented_of_finite_dimensional_range (f : E →L[𝕜] F)
  [finite_dimensional 𝕜 (range f)] :
  (ker f).closed_complemented :=
begin
  set f' : E →L[𝕜] (range f) := f.cod_restrict _ (f : E →ₗ[𝕜] F).mem_range_self,
  rcases f'.exists_right_inverse_of_surjective (f : E →ₗ[𝕜] F).range_range_restrict with ⟨g, hg⟩,
  simpa only [ker_cod_restrict] using f'.closed_complemented_ker_of_right_inverse g (ext_iff.1 hg)
end

end

variables [complete_space E] [complete_space (F × G)]

/-- If `f : E →L[R] F` and `g : E →L[R] G` are two surjective linear maps and
their kernels are complement of each other, then `x ↦ (f x, g x)` defines
a linear equivalence `E ≃L[R] F × G`. -/
def equiv_prod_of_surjective_of_is_compl (f : E →L[𝕜] F) (g : E →L[𝕜] G) (hf : range f = ⊤)
  (hg : range g = ⊤) (hfg : is_compl (ker f) (ker g)) :
  E ≃L[𝕜] F × G :=
((f : E →ₗ[𝕜] F).equiv_prod_of_surjective_of_is_compl ↑g hf hg
  hfg).to_continuous_linear_equiv_of_continuous (f.continuous.prod_mk g.continuous)

@[simp] lemma coe_equiv_prod_of_surjective_of_is_compl {f : E →L[𝕜] F} {g : E →L[𝕜] G}
  (hf : range f = ⊤) (hg : range g = ⊤) (hfg : is_compl (ker f) (ker g)) :
  (equiv_prod_of_surjective_of_is_compl f g hf hg hfg : E →ₗ[𝕜] F × G) = f.prod g :=
rfl

@[simp] lemma equiv_prod_of_surjective_of_is_compl_to_linear_equiv {f : E →L[𝕜] F} {g : E →L[𝕜] G}
  (hf : range f = ⊤) (hg : range g = ⊤) (hfg : is_compl (ker f) (ker g)) :
  (equiv_prod_of_surjective_of_is_compl f g hf hg hfg).to_linear_equiv =
    linear_map.equiv_prod_of_surjective_of_is_compl f g hf hg hfg :=
rfl

@[simp] lemma equiv_prod_of_surjective_of_is_compl_apply {f : E →L[𝕜] F} {g : E →L[𝕜] G}
  (hf : range f = ⊤) (hg : range g = ⊤) (hfg : is_compl (ker f) (ker g)) (x : E) :
  equiv_prod_of_surjective_of_is_compl f g hf hg hfg x = (f x, g x) :=
rfl

end continuous_linear_map

namespace subspace

variables [complete_space E] (p q : subspace 𝕜 E)

/-- If `q` is a closed complement of a closed subspace `p`, then `p × q` is continuously
isomorphic to `E`. -/
def prod_equiv_of_closed_compl (h : is_compl p q) (hp : is_closed (p : set E))
  (hq : is_closed (q : set E)) : (p × q) ≃L[𝕜] E :=
begin
  haveI := hp.complete_space_coe, haveI := hq.complete_space_coe,
  refine (p.prod_equiv_of_is_compl q h).to_continuous_linear_equiv_of_continuous _,
  exact (p.subtypeL.coprod q.subtypeL).continuous
end

/-- Projection to a closed submodule along a closed complement. -/
def linear_proj_of_closed_compl (h : is_compl p q) (hp : is_closed (p : set E))
  (hq : is_closed (q : set E)) :
  E →L[𝕜] p :=
(continuous_linear_map.fst 𝕜 p q) ∘L ↑(prod_equiv_of_closed_compl p q h hp hq).symm

variables {p q}

@[simp] lemma coe_prod_equiv_of_closed_compl (h : is_compl p q) (hp : is_closed (p : set E))
  (hq : is_closed (q : set E)) :
  ⇑(p.prod_equiv_of_closed_compl q h hp hq) = p.prod_equiv_of_is_compl q h := rfl

@[simp] lemma coe_prod_equiv_of_closed_compl_symm (h : is_compl p q) (hp : is_closed (p : set E))
  (hq : is_closed (q : set E)) :
  ⇑(p.prod_equiv_of_closed_compl q h hp hq).symm = (p.prod_equiv_of_is_compl q h).symm := rfl

@[simp] lemma coe_continuous_linear_proj_of_closed_compl (h : is_compl p q)
  (hp : is_closed (p : set E)) (hq : is_closed (q : set E)) :
  (p.linear_proj_of_closed_compl q h hp hq : E →ₗ[𝕜] p) = p.linear_proj_of_is_compl q h := rfl

@[simp] lemma coe_continuous_linear_proj_of_closed_compl' (h : is_compl p q)
  (hp : is_closed (p : set E)) (hq : is_closed (q : set E)) :
  ⇑(p.linear_proj_of_closed_compl q h hp hq) = p.linear_proj_of_is_compl q h := rfl

lemma closed_complemented_of_closed_compl (h : is_compl p q) (hp : is_closed (p : set E))
  (hq : is_closed (q : set E)) : p.closed_complemented :=
⟨p.linear_proj_of_closed_compl q h hp hq, submodule.linear_proj_of_is_compl_apply_left h⟩

lemma closed_complemented_iff_has_closed_compl : p.closed_complemented ↔
  is_closed (p : set E) ∧ ∃ (q : subspace 𝕜 E) (hq : is_closed (q : set E)), is_compl p q :=
⟨λ h, ⟨h.is_closed, h.has_closed_complement⟩,
  λ ⟨hp, ⟨q, hq, hpq⟩⟩, closed_complemented_of_closed_compl hpq hp hq⟩

lemma closed_complemented_of_quotient_finite_dimensional [complete_space 𝕜]
  [finite_dimensional 𝕜 (E ⧸ p)] (hp : is_closed (p : set E)) :
  p.closed_complemented :=
begin
  obtain ⟨q, hq⟩ : ∃ q, is_compl p q := p.exists_is_compl,
  haveI : finite_dimensional 𝕜 q := (p.quotient_equiv_of_is_compl q hq).finite_dimensional,
  exact closed_complemented_of_closed_compl hq hp q.closed_of_finite_dimensional
end

end subspace

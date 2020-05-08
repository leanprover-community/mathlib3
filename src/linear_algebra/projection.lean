/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov
-/
import linear_algebra.basic

/-!
# Projection to a subspace

In this file we define
* `linear_proj_of_is_compl (p q : submodule R E) (h : is_compl p q)`: the projection of a module `E`
  to a submodule `p` along its complement `q`; it is the unique linear map `f : E → p` such that
  `f x = x` for `x ∈ p` and `f x = 0` for `x ∈ q`.
* `is_compl_equiv_proj p`: equivalence between submodules `q` such that `is_compl p q` and
  projections `f : E → p`, `∀ x ∈ p, f x = x`.

We also provide some lemmas justifying correctness of our definitions.

## Tags

projection, complement subspace
-/

variables {R : Type*} {E : Type*} [ring R] [add_comm_group E] [module R E] (p q : submodule R E)

noncomputable theory

namespace submodule

open linear_map

-- TODO[calc comp]: I'd like to rewrite it using `calc` but it doesn't agree with `linear_map.comp`
-- on the order of arguments.

/-- Projection to a submodule along its complement. -/
def linear_proj_of_is_compl (h : is_compl p q) :
  E →ₗ[R] p :=
((comap p.subtype (p ⊓ q)).quot_equiv_of_eq_bot
  (eq_bot_mono (comap_mono inf_le_right) $ disjoint_iff_comap_eq_bot.1 h.disjoint) :
  (comap p.subtype (p ⊓ q)).quotient →ₗ[R] p).comp $
((quotient_inf_equiv_sup_quotient p q).symm :
  (comap (p ⊔ q).subtype q).quotient →ₗ[R] (comap p.subtype (p ⊓ q)).quotient).comp $
(comap (p ⊔ q).subtype q).mkq.comp
((linear_equiv.of_top (p ⊔ q) h.sup_eq_top).symm : E →ₗ[R] (p ⊔ q : submodule R E))

lemma linear_proj_of_is_compl_apply_left' (h : is_compl p q) (x : E) (hx : x ∈ p) :
  linear_proj_of_is_compl p q h x = ⟨x, hx⟩ :=
begin
  simp only [linear_proj_of_is_compl, linear_equiv.coe_coe, linear_map.comp_apply, mkq_apply],
  rw [linear_equiv.of_top_symm_apply, quotient_inf_equiv_sup_quotient_symm_apply_left,
    quot_equiv_of_eq_bot_apply_mk]; simp only [subtype.coe_mk, hx]
end

@[simp] lemma linear_proj_of_is_compl_apply_left (h : is_compl p q) (x : p) :
  linear_proj_of_is_compl p q h x = x :=
by rw [linear_proj_of_is_compl_apply_left' p q h x x.2, submodule.eta]

@[simp] lemma linear_proj_of_is_compl_range (h : is_compl p q) :
  (linear_proj_of_is_compl p q h).range = ⊤ :=
by simp [linear_proj_of_is_compl, range_comp]

lemma linear_proj_of_is_compl_apply_eq_zero_iff (h : is_compl p q) {x : E} :
  linear_proj_of_is_compl p q h x = 0 ↔ x ∈ q:=
by simp [linear_proj_of_is_compl]

lemma linear_proj_of_is_compl_apply_right' (h : is_compl p q) (x : E) (hx : x ∈ q) :
  linear_proj_of_is_compl p q h x = 0 :=
(linear_proj_of_is_compl_apply_eq_zero_iff p q h).2 hx

@[simp] lemma linear_proj_of_is_compl_apply_right (h : is_compl p q) (x : q) :
  linear_proj_of_is_compl p q h x = 0 :=
linear_proj_of_is_compl_apply_right' p q h x x.2

@[simp] lemma linear_proj_of_is_compl_ker (h : is_compl p q) :
  (linear_proj_of_is_compl p q h).ker = q :=
ext $ λ x, mem_ker.trans (linear_proj_of_is_compl_apply_eq_zero_iff p q h)

lemma linear_proj_of_is_compl_idempotent (h : is_compl p q) (x : E) :
  linear_proj_of_is_compl p q h (linear_proj_of_is_compl p q h x) =
    linear_proj_of_is_compl p q h x :=
linear_proj_of_is_compl_apply_left p q h _

end submodule

namespace linear_map

variable {p}

open submodule

lemma is_compl_of_proj (f : E →ₗ[R] p) (hf : ∀ x : p, f x = x) :
  is_compl p f.ker :=
begin
  split,
  { rintros x ⟨hpx, hfx⟩,
    erw [mem_coe, mem_ker, hf ⟨x, hpx⟩, mk_eq_zero] at hfx,
    simp only [hfx, mem_coe, zero_mem] },
  { intros x hx,
    rw [mem_coe, mem_sup'],
    refine ⟨f x, ⟨x - f x, _⟩, add_sub_cancel'_right _ _⟩,
    rw [mem_ker, linear_map.map_sub, hf, sub_self] }
end

@[simp] lemma linear_proj_of_is_compl_of_proj (f : E →ₗ[R] p) (hf : ∀ x : p, f x = x) :
  p.linear_proj_of_is_compl f.ker (f.is_compl_of_proj hf) = f :=
begin
  ext x,
  have : x ∈ p ⊔ f.ker,
  { simp only [(f.is_compl_of_proj hf).sup_eq_top, mem_top] },
  rcases mem_sup'.1 this with ⟨x, y, rfl⟩,
  simp [hf]
end

end linear_map

namespace submodule

/-- Equivalence between submoddules `q` such that `is_compl p q` and linear maps `f : E →ₗ[R] p`
such that `∀ x : p, f x = x`. -/
def is_compl_equiv_proj :
  {q // is_compl p q} ≃ {f : E →ₗ[R] p // ∀ x : p, f x = x} :=
{ to_fun := λ q, ⟨linear_proj_of_is_compl p q q.2, linear_proj_of_is_compl_apply_left p q q.2⟩,
  inv_fun := λ f, ⟨(f : E →ₗ[R] p).ker, f.1.is_compl_of_proj f.2⟩,
  left_inv := λ ⟨q, hq⟩, by simp only [linear_proj_of_is_compl_ker, subtype.coe_mk],
  right_inv := λ ⟨f, hf⟩, subtype.eq $ f.linear_proj_of_is_compl_of_proj hf }

@[simp] lemma coe_is_compl_equiv_proj_apply (q : {q // is_compl p q}) :
  (p.is_compl_equiv_proj q : E →ₗ[R] p) = linear_proj_of_is_compl p q q.2 := rfl

@[simp] lemma coe_is_compl_equiv_proj_symm_apply (f : {f : E →ₗ[R] p // ∀ x : p, f x = x}) :
  (p.is_compl_equiv_proj.symm f : submodule R E) = (f : E →ₗ[R] p).ker := rfl

end submodule


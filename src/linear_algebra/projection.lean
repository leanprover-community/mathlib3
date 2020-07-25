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

variables {R : Type*} [ring R] {E : Type*} [add_comm_group E] [module R E]
  {F : Type*} [add_comm_group F] [module R F]
  {G : Type*} [add_comm_group G] [module R G] (p q : submodule R E)

noncomputable theory

namespace linear_map

variable {p}

open submodule

lemma ker_id_sub_eq_of_proj {f : E →ₗ[R] p} (hf : ∀ x : p, f x = x) :
  ker (id - p.subtype.comp f) = p :=
begin
  ext x,
  simp only [comp_apply, mem_ker, subtype_apply, sub_apply, id_apply, sub_eq_zero],
  exact ⟨λ h, h.symm ▸ submodule.coe_mem _, λ hx, by erw [hf ⟨x, hx⟩, subtype.coe_mk]⟩
end

lemma range_eq_of_proj {f : E →ₗ[R] p} (hf : ∀ x : p, f x = x) :
  range f = ⊤ :=
range_eq_top.2 $ λ x, ⟨x, hf x⟩

lemma is_compl_of_proj {f : E →ₗ[R] p} (hf : ∀ x : p, f x = x) :
  is_compl p f.ker :=
begin
  split,
  { rintros x ⟨hpx, hfx⟩,
    erw [mem_coe, mem_ker, hf ⟨x, hpx⟩, mk_eq_zero] at hfx,
    simp only [hfx, mem_coe, zero_mem] },
  { intros x hx,
    rw [mem_sup'],
    refine ⟨f x, ⟨x - f x, _⟩, add_sub_cancel'_right _ _⟩,
    rw [mem_ker, linear_map.map_sub, hf, sub_self] }
end

end linear_map

namespace submodule

open linear_map

/-- If `q` is a complement of `p`, then `M/p ≃ q`. -/
def quotient_equiv_of_is_compl (h : is_compl p q) : p.quotient ≃ₗ[R] q :=
linear_equiv.symm $ linear_equiv.of_bijective (p.mkq.comp q.subtype)
  (by simp only [ker_comp, ker_mkq, disjoint_iff_comap_eq_bot.1 h.symm.disjoint])
  (by simp only [range_comp, range_subtype, map_mkq_eq_top, h.sup_eq_top])

@[simp] lemma quotient_equiv_of_is_compl_symm_apply (h : is_compl p q) (x : q) :
  (quotient_equiv_of_is_compl p q h).symm x = quotient.mk x := rfl

@[simp] lemma quotient_equiv_of_is_compl_apply_mk_coe (h : is_compl p q) (x : q) :
  quotient_equiv_of_is_compl p q h (quotient.mk x) = x :=
(quotient_equiv_of_is_compl p q h).apply_symm_apply x

@[simp] lemma mk_quotient_equiv_of_is_compl_apply (h : is_compl p q) (x : p.quotient) :
  (quotient.mk (quotient_equiv_of_is_compl p q h x) : p.quotient) = x :=
(quotient_equiv_of_is_compl p q h).symm_apply_apply x

/-- If `q` is a complement of `p`, then `p × q` is isomorphic to `E`. It is the unique
linear map `f : E → p` such that `f x = x` for `x ∈ p` and `f x = 0` for `x ∈ q`. -/
def prod_equiv_of_is_compl (h : is_compl p q) : (p × q) ≃ₗ[R] E :=
begin
  apply linear_equiv.of_bijective (p.subtype.coprod q.subtype),
  { simp only [ker_eq_bot', prod.forall, subtype_apply, prod.mk_eq_zero, coprod_apply],
    -- TODO: if I add `submodule.forall`, it unfolds the outer `∀` but not the inner one.
    rintros ⟨x, hx⟩ ⟨y, hy⟩,
    simp only [coe_mk, mk_eq_zero, ← eq_neg_iff_add_eq_zero],
    rintro rfl,
    rw [neg_mem_iff] at hx,
    simp [disjoint_def.1 h.disjoint y hx hy] },
  { rw [← sup_eq_range, h.sup_eq_top] }
end

@[simp] lemma coe_prod_equiv_of_is_compl (h : is_compl p q) :
  (prod_equiv_of_is_compl p q h : (p × q) →ₗ[R] E) = p.subtype.coprod q.subtype := rfl

@[simp] lemma coe_prod_equiv_of_is_compl' (h : is_compl p q) (x : p × q) :
  prod_equiv_of_is_compl p q h x = x.1 + x.2 := rfl

@[simp] lemma prod_equiv_of_is_compl_symm_apply_left (h : is_compl p q) (x : p) :
  (prod_equiv_of_is_compl p q h).symm x = (x, 0) :=
(prod_equiv_of_is_compl p q h).symm_apply_eq.2 $ by simp

@[simp] lemma prod_equiv_of_is_compl_symm_apply_right (h : is_compl p q) (x : q) :
  (prod_equiv_of_is_compl p q h).symm x = (0, x) :=
(prod_equiv_of_is_compl p q h).symm_apply_eq.2 $ by simp

@[simp] lemma prod_equiv_of_is_compl_symm_apply_fst_eq_zero (h : is_compl p q) {x : E} :
  ((prod_equiv_of_is_compl p q h).symm x).1 = 0 ↔ x ∈ q :=
begin
  conv_rhs { rw [← (prod_equiv_of_is_compl p q h).apply_symm_apply x] },
  rw [coe_prod_equiv_of_is_compl', submodule.add_mem_iff_left _ (submodule.coe_mem _),
    mem_right_iff_eq_zero_of_disjoint h.disjoint]
end

@[simp] lemma prod_equiv_of_is_compl_symm_apply_snd_eq_zero (h : is_compl p q) {x : E} :
  ((prod_equiv_of_is_compl p q h).symm x).2 = 0 ↔ x ∈ p :=
begin
  conv_rhs { rw [← (prod_equiv_of_is_compl p q h).apply_symm_apply x] },
  rw [coe_prod_equiv_of_is_compl', submodule.add_mem_iff_right _ (submodule.coe_mem _),
    mem_left_iff_eq_zero_of_disjoint h.disjoint]
end

/-- Projection to a submodule along its complement. -/
def linear_proj_of_is_compl (h : is_compl p q) :
  E →ₗ[R] p :=
(linear_map.fst R p q).comp $ (prod_equiv_of_is_compl p q h).symm

variables {p q}

@[simp] lemma linear_proj_of_is_compl_apply_left (h : is_compl p q) (x : p) :
  linear_proj_of_is_compl p q h x = x :=
by simp [linear_proj_of_is_compl]

@[simp] lemma linear_proj_of_is_compl_range (h : is_compl p q) :
  (linear_proj_of_is_compl p q h).range = ⊤ :=
range_eq_of_proj (linear_proj_of_is_compl_apply_left h)

@[simp] lemma linear_proj_of_is_compl_apply_eq_zero_iff (h : is_compl p q) {x : E} :
  linear_proj_of_is_compl p q h x = 0 ↔ x ∈ q:=
by simp [linear_proj_of_is_compl]

lemma linear_proj_of_is_compl_apply_right' (h : is_compl p q) (x : E) (hx : x ∈ q) :
  linear_proj_of_is_compl p q h x = 0 :=
(linear_proj_of_is_compl_apply_eq_zero_iff h).2 hx

@[simp] lemma linear_proj_of_is_compl_apply_right (h : is_compl p q) (x : q) :
  linear_proj_of_is_compl p q h x = 0 :=
linear_proj_of_is_compl_apply_right' h x x.2

@[simp] lemma linear_proj_of_is_compl_ker (h : is_compl p q) :
  (linear_proj_of_is_compl p q h).ker = q :=
ext $ λ x, mem_ker.trans (linear_proj_of_is_compl_apply_eq_zero_iff h)

lemma linear_proj_of_is_compl_comp_subtype (h : is_compl p q) :
  (linear_proj_of_is_compl p q h).comp p.subtype = id :=
linear_map.ext $ linear_proj_of_is_compl_apply_left h

lemma linear_proj_of_is_compl_idempotent (h : is_compl p q) (x : E) :
  linear_proj_of_is_compl p q h (linear_proj_of_is_compl p q h x) =
    linear_proj_of_is_compl p q h x :=
linear_proj_of_is_compl_apply_left h _

end submodule

namespace linear_map

variable {p}

open submodule

@[simp] lemma linear_proj_of_is_compl_of_proj (f : E →ₗ[R] p) (hf : ∀ x : p, f x = x) :
  p.linear_proj_of_is_compl f.ker (is_compl_of_proj hf) = f :=
begin
  ext x,
  have : x ∈ p ⊔ f.ker,
  { simp only [(is_compl_of_proj hf).sup_eq_top, mem_top] },
  rcases mem_sup'.1 this with ⟨x, y, rfl⟩,
  simp [hf]
end

/-- If `f : E →ₗ[R] F` and `g : E →ₗ[R] G` are two surjective linear maps and
their kernels are complement of each other, then `x ↦ (f x, g x)` defines
a linear equivalence `E ≃ₗ[R] F × G`. -/
def equiv_prod_of_surjective_of_is_compl (f : E →ₗ[R] F) (g : E →ₗ[R] G) (hf : f.range = ⊤)
  (hg : g.range = ⊤) (hfg : is_compl f.ker g.ker) :
  E ≃ₗ[R] F × G :=
linear_equiv.of_bijective (f.prod g) (by simp [hfg.inf_eq_bot])
  (by simp [range_prod_eq hfg.sup_eq_top, *])

@[simp] lemma coe_equiv_prod_of_surjective_of_is_compl {f : E →ₗ[R] F} {g : E →ₗ[R] G}
  (hf : f.range = ⊤) (hg : g.range = ⊤) (hfg : is_compl f.ker g.ker) :
  (equiv_prod_of_surjective_of_is_compl f g hf hg hfg : E →ₗ[R] F × G) = f.prod g :=
rfl

@[simp] lemma equiv_prod_of_surjective_of_is_compl_apply {f : E →ₗ[R] F} {g : E →ₗ[R] G}
  (hf : f.range = ⊤) (hg : g.range = ⊤) (hfg : is_compl f.ker g.ker) (x : E):
  equiv_prod_of_surjective_of_is_compl f g hf hg hfg x = (f x, g x) :=
rfl

end linear_map

namespace submodule

open linear_map

/-- Equivalence between submodules `q` such that `is_compl p q` and linear maps `f : E →ₗ[R] p`
such that `∀ x : p, f x = x`. -/
def is_compl_equiv_proj :
  {q // is_compl p q} ≃ {f : E →ₗ[R] p // ∀ x : p, f x = x} :=
{ to_fun := λ q, ⟨linear_proj_of_is_compl p q q.2, linear_proj_of_is_compl_apply_left q.2⟩,
  inv_fun := λ f, ⟨(f : E →ₗ[R] p).ker, is_compl_of_proj f.2⟩,
  left_inv := λ ⟨q, hq⟩, by simp only [linear_proj_of_is_compl_ker, subtype.coe_mk],
  right_inv := λ ⟨f, hf⟩, subtype.eq $ f.linear_proj_of_is_compl_of_proj hf }

@[simp] lemma coe_is_compl_equiv_proj_apply (q : {q // is_compl p q}) :
  (p.is_compl_equiv_proj q : E →ₗ[R] p) = linear_proj_of_is_compl p q q.2 := rfl

@[simp] lemma coe_is_compl_equiv_proj_symm_apply (f : {f : E →ₗ[R] p // ∀ x : p, f x = x}) :
  (p.is_compl_equiv_proj.symm f : submodule R E) = (f : E →ₗ[R] p).ker := rfl

end submodule

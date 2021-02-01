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

lemma exists_unique_add_of_is_compl (hc : is_compl p q) (x : E) :
  ∃ (u : p) (v : q), ((u : E) + v = x ∧ ∀ (r : p) (s : q),
    (r : E) + s = x → r = u ∧ s = v) :=
begin
  obtain ⟨u, v, h⟩ :=
    submodule.mem_sup'.1 ((eq_top_iff.2 hc.2).symm ▸ mem_top : x ∈ p ⊔ q),
  refine ⟨u, v, h, λ r s hrs, _⟩,
  erw [← h, ← @add_right_cancel_iff _ _ (-s : E) (r + s) (u + v),
       add_assoc, add_neg_self, add_zero,
       ← @add_left_cancel_iff _ _ (-u : E) r (u + v + -s),
       ← add_assoc, ← add_assoc, add_left_neg, zero_add, add_comm,
       ← sub_eq_add_neg, ← sub_eq_add_neg] at hrs,
  split; rw [← sub_eq_zero],
  { suffices : r.1 - u.1 ∈ q,
    { rw [← coe_eq_coe, coe_sub],
      exact (submodule.mem_bot _).1 (hc.1 ⟨p.sub_mem r.2 u.2, this⟩) },
    erw hrs, exact q.sub_mem v.2 s.2 },
  { suffices : s.1 - v.1 ∈ p,
    { rw [← coe_eq_coe, coe_sub],
      exact (submodule.mem_bot _).1 (hc.1 ⟨this, q.sub_mem s.2 v.2⟩) },
    erw [← neg_mem_iff, neg_sub, ← hrs],
    exact p.sub_mem r.2 u.2 }
end .

lemma exists_unique_add_of_is_compl_prod (hc : is_compl p q) (x : E) :
  ∃! (u : p × q), (u.fst : E) + u.snd = x :=
begin
  sorry
  -- obtain ⟨u, v, h⟩ :=
  --   submodule.mem_sup'.1 ((eq_top_iff.2 hc.2).symm ▸ mem_top : x ∈ p ⊔ q),
  -- refine ⟨u, v, h, λ r s hrs, _⟩,
  -- erw [← h, ← @add_right_cancel_iff _ _ (-s : E) (r + s) (u + v),
  --      add_assoc, add_neg_self, add_zero,
  --      ← @add_left_cancel_iff _ _ (-u : E) r (u + v + -s),
  --      ← add_assoc, ← add_assoc, add_left_neg, zero_add, add_comm,
  --      ← sub_eq_add_neg, ← sub_eq_add_neg] at hrs,
  -- split; rw [← sub_eq_zero],
  -- { suffices : r.1 - u.1 ∈ q,
  --   { rw [← coe_eq_coe, coe_sub],
  --     exact (submodule.mem_bot _).1 (hc.1 ⟨p.sub_mem r.2 u.2, this⟩) },
  --   erw hrs, exact q.sub_mem v.2 s.2 },
  -- { suffices : s.1 - v.1 ∈ p,
  --   { rw [← coe_eq_coe, coe_sub],
  --     exact (submodule.mem_bot _).1 (hc.1 ⟨this, q.sub_mem s.2 v.2⟩) },
  --   erw [← neg_mem_iff, neg_sub, ← hrs],
  --   exact p.sub_mem r.2 u.2 }
end .

/-- Given linear maps `φ` and `ψ` from complement submodules, `of_is_compl` is
the induced linear map over the entire module. -/
def of_is_compl (h : is_compl p q) (φ : p →ₗ[R] F) (ψ : q →ₗ[R] F) : E →ₗ[R] F :=
φ.comp (linear_proj_of_is_compl p q h) + ψ.comp (linear_proj_of_is_compl q p h.symm)

def of_is_compl_prod (h : is_compl p q) (φ : (p →ₗ[R] F) × (q →ₗ[R] F)) : E →ₗ[R] F :=
of_is_compl h φ.1 φ.2

@[simp] lemma of_is_compl_left_apply
  (h : is_compl p q) {φ : p →ₗ[R] F} {ψ : q →ₗ[R] F} (u : p) :
  of_is_compl h φ ψ (u : E) = φ u :=
by erw [of_is_compl, linear_map.add_apply, linear_map.comp_apply,
        linear_proj_of_is_compl_apply_left, linear_map.comp_apply,
        linear_proj_of_is_compl_apply_right, linear_map.map_zero, add_zero]

@[simp] lemma of_is_compl_right_apply
  (h : is_compl p q) {φ : p →ₗ[R] F} {ψ : q →ₗ[R] F} (v : q) :
  of_is_compl h φ ψ (v : E) = ψ v :=
by erw [of_is_compl, linear_map.add_apply, linear_map.comp_apply,
        linear_proj_of_is_compl_apply_right, linear_map.comp_apply,
        linear_proj_of_is_compl_apply_left, linear_map.map_zero, zero_add]

@[simp] lemma of_is_compl_zero (h : is_compl p q) :
  (of_is_compl h 0 0 : E →ₗ[R] F) = 0 :=
begin
  ext, obtain ⟨_, _, rfl, _⟩ := exists_unique_add_of_is_compl h x,
  erw [linear_map.map_add, of_is_compl_left_apply, add_zero, linear_map.zero_apply]
end

@[simp] lemma of_is_compl_add (h : is_compl p q)
  {φ₁ φ₂ : p →ₗ[R] F} {ψ₁ ψ₂ : q →ₗ[R] F} :
  of_is_compl h (φ₁ + φ₂) (ψ₁ + ψ₂) = of_is_compl h φ₁ ψ₁ + of_is_compl h φ₂ ψ₂ :=
begin
  ext, obtain ⟨_, _, rfl, _⟩ := exists_unique_add_of_is_compl h x,
  simp only [of_is_compl_left_apply, of_is_compl_right_apply,
    linear_map.add_apply, linear_map.map_add, subtype.val_eq_coe],
end

@[simp] lemma of_is_compl_smul
  {R : Type*} [comm_ring R] {E : Type*} [add_comm_group E] [module R E]
  {F : Type*} [add_comm_group F] [module R F] {p q : submodule R E}
  (h : is_compl p q) {φ : p →ₗ[R] F} {ψ : q →ₗ[R] F} (c : R) :
  of_is_compl h (c • φ) (c • ψ) = c • of_is_compl h φ ψ :=
begin
  ext, obtain ⟨_, _, rfl, _⟩ := exists_unique_add_of_is_compl h x,
  simp only [of_is_compl_left_apply, of_is_compl_right_apply, linear_map.smul_apply,
    eq_self_iff_true, linear_map.map_add, subtype.val_eq_coe],
end

section

variables {R₁ : Type*} [comm_ring R₁] [module R₁ E] [module R₁ F]

def of_is_compl_prod' {p q : submodule R₁ E} (h : is_compl p q) :
  ((p →ₗ[R₁] F) × (q →ₗ[R₁] F)) →ₗ[R₁] (E →ₗ[R₁] F) :=
{ to_fun := of_is_compl_prod h,
  map_add' :=
    begin
      intros φ ψ,
      rw [of_is_compl_prod, prod.snd_add, prod.fst_add, of_is_compl_add], refl,
    end,
  map_smul' :=
    begin
      intros c φ,
      rw [of_is_compl_prod, prod.smul_snd, prod.smul_fst, of_is_compl_smul], refl,
    end }

def of_is_compl_prod_equiv {p q : submodule R₁ E} (h : is_compl p q) :
  ((p →ₗ[R₁] F) × (q →ₗ[R₁] F)) ≃ₗ[R₁] (E →ₗ[R₁] F) :=
{ inv_fun := λ φ, ⟨φ.dom_restrict p, φ.dom_restrict q⟩,
  left_inv :=
    begin
      intros φ, ext,
      { exact of_is_compl_left_apply h x },
      { exact of_is_compl_right_apply h x }
    end,
  right_inv :=
    begin
      intro φ, ext,
      obtain ⟨a, b, hab, _⟩ := exists_unique_add_of_is_compl h x,
      change (of_is_compl h (φ.dom_restrict p) (φ.dom_restrict q)) x = φ x,
      rw [← hab, linear_map.map_add, of_is_compl_left_apply, of_is_compl_right_apply,
        dom_restrict_apply, dom_restrict_apply, linear_map.map_add],
    end, .. of_is_compl_prod' h }

end

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

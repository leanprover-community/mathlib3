/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import linear_algebra.quotient
import linear_algebra.prod

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

section ring

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
    erw [set_like.mem_coe, mem_ker, hf ⟨x, hpx⟩, mk_eq_zero] at hfx,
    simp only [hfx, set_like.mem_coe, zero_mem] },
  { intros x hx,
    rw [mem_sup'],
    refine ⟨f x, ⟨x - f x, _⟩, add_sub_cancel'_right _ _⟩,
    rw [mem_ker, linear_map.map_sub, hf, sub_self] }
end

end linear_map

namespace submodule

open linear_map

/-- If `q` is a complement of `p`, then `M/p ≃ q`. -/
def quotient_equiv_of_is_compl (h : is_compl p q) : (E ⧸ p) ≃ₗ[R] q :=
linear_equiv.symm $ linear_equiv.of_bijective (p.mkq.comp q.subtype)
  (by simp only [← ker_eq_bot, ker_comp, ker_mkq, disjoint_iff_comap_eq_bot.1 h.symm.disjoint])
  (by simp only [← range_eq_top, range_comp, range_subtype, map_mkq_eq_top, h.sup_eq_top])

@[simp] lemma quotient_equiv_of_is_compl_symm_apply (h : is_compl p q) (x : q) :
  (quotient_equiv_of_is_compl p q h).symm x = quotient.mk x := rfl

@[simp] lemma quotient_equiv_of_is_compl_apply_mk_coe (h : is_compl p q) (x : q) :
  quotient_equiv_of_is_compl p q h (quotient.mk x) = x :=
(quotient_equiv_of_is_compl p q h).apply_symm_apply x

@[simp] lemma mk_quotient_equiv_of_is_compl_apply (h : is_compl p q) (x : E ⧸ p) :
  (quotient.mk (quotient_equiv_of_is_compl p q h x) : E ⧸ p) = x :=
(quotient_equiv_of_is_compl p q h).symm_apply_apply x

/-- If `q` is a complement of `p`, then `p × q` is isomorphic to `E`. It is the unique
linear map `f : E → p` such that `f x = x` for `x ∈ p` and `f x = 0` for `x ∈ q`. -/
def prod_equiv_of_is_compl (h : is_compl p q) : (p × q) ≃ₗ[R] E :=
begin
  apply linear_equiv.of_bijective (p.subtype.coprod q.subtype),
  { simp only [←ker_eq_bot, ker_eq_bot', prod.forall, subtype_apply, prod.mk_eq_zero, coprod_apply],
    -- TODO: if I add `submodule.forall`, it unfolds the outer `∀` but not the inner one.
    rintros ⟨x, hx⟩ ⟨y, hy⟩,
    simp only [coe_mk, mk_eq_zero, ← eq_neg_iff_add_eq_zero],
    rintro rfl,
    rw [neg_mem_iff] at hx,
    simp [disjoint_def.1 h.disjoint y hx hy] },
  { rw [← range_eq_top, ← sup_eq_range, h.sup_eq_top] }
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

@[simp]
lemma prod_comm_trans_prod_equiv_of_is_compl (h : is_compl p q) :
  linear_equiv.prod_comm R q p ≪≫ₗ prod_equiv_of_is_compl p q h =
    prod_equiv_of_is_compl q p h.symm :=
linear_equiv.ext $ λ _, add_comm _ _

/-- Projection to a submodule along its complement. -/
def linear_proj_of_is_compl (h : is_compl p q) :
  E →ₗ[R] p :=
(linear_map.fst R p q) ∘ₗ ↑(prod_equiv_of_is_compl p q h).symm

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

lemma exists_unique_add_of_is_compl_prod (hc : is_compl p q) (x : E) :
  ∃! (u : p × q), (u.fst : E) + u.snd = x :=
(prod_equiv_of_is_compl _ _ hc).to_equiv.bijective.exists_unique _

lemma exists_unique_add_of_is_compl (hc : is_compl p q) (x : E) :
  ∃ (u : p) (v : q), ((u : E) + v = x ∧ ∀ (r : p) (s : q),
    (r : E) + s = x → r = u ∧ s = v) :=
let ⟨u, hu₁, hu₂⟩ := exists_unique_add_of_is_compl_prod hc x in
  ⟨u.1, u.2, hu₁, λ r s hrs, prod.eq_iff_fst_eq_snd_eq.1 (hu₂ ⟨r, s⟩ hrs)⟩

lemma linear_proj_add_linear_proj_of_is_compl_eq_self (hpq : is_compl p q) (x : E) :
  (p.linear_proj_of_is_compl q hpq x + q.linear_proj_of_is_compl p hpq.symm x : E) = x :=
begin
  dunfold linear_proj_of_is_compl,
  rw ←prod_comm_trans_prod_equiv_of_is_compl _ _ hpq,
  exact (prod_equiv_of_is_compl _ _ hpq).apply_symm_apply x,
end

end submodule

namespace linear_map

open submodule

/-- Given linear maps `φ` and `ψ` from complement submodules, `of_is_compl` is
the induced linear map over the entire module. -/
def of_is_compl {p q : submodule R E} (h : is_compl p q)
  (φ : p →ₗ[R] F) (ψ : q →ₗ[R] F) : E →ₗ[R] F :=
(linear_map.coprod φ ψ) ∘ₗ ↑(submodule.prod_equiv_of_is_compl _ _ h).symm

variables {p q}

@[simp] lemma of_is_compl_left_apply
  (h : is_compl p q) {φ : p →ₗ[R] F} {ψ : q →ₗ[R] F} (u : p) :
  of_is_compl h φ ψ (u : E) = φ u := by simp [of_is_compl]

@[simp] lemma of_is_compl_right_apply
  (h : is_compl p q) {φ : p →ₗ[R] F} {ψ : q →ₗ[R] F} (v : q) :
  of_is_compl h φ ψ (v : E) = ψ v := by simp [of_is_compl]

lemma of_is_compl_eq (h : is_compl p q)
  {φ : p →ₗ[R] F} {ψ : q →ₗ[R] F} {χ : E →ₗ[R] F}
  (hφ : ∀ u, φ u = χ u) (hψ : ∀ u, ψ u = χ u) :
  of_is_compl h φ ψ = χ :=
begin
  ext x,
  obtain ⟨_, _, rfl, _⟩ := exists_unique_add_of_is_compl h x,
  simp [of_is_compl, hφ, hψ]
end

lemma of_is_compl_eq' (h : is_compl p q)
  {φ : p →ₗ[R] F} {ψ : q →ₗ[R] F} {χ : E →ₗ[R] F}
  (hφ : φ = χ.comp p.subtype) (hψ : ψ = χ.comp q.subtype) :
  of_is_compl h φ ψ = χ :=
of_is_compl_eq h (λ _, hφ.symm ▸ rfl) (λ _, hψ.symm ▸ rfl)

@[simp] lemma of_is_compl_zero (h : is_compl p q) :
  (of_is_compl h 0 0 : E →ₗ[R] F) = 0 :=
of_is_compl_eq _ (λ _, rfl) (λ _, rfl)

@[simp] lemma of_is_compl_add (h : is_compl p q)
  {φ₁ φ₂ : p →ₗ[R] F} {ψ₁ ψ₂ : q →ₗ[R] F} :
  of_is_compl h (φ₁ + φ₂) (ψ₁ + ψ₂) = of_is_compl h φ₁ ψ₁ + of_is_compl h φ₂ ψ₂ :=
of_is_compl_eq _ (by simp) (by simp)

@[simp] lemma of_is_compl_smul
  {R : Type*} [comm_ring R] {E : Type*} [add_comm_group E] [module R E]
  {F : Type*} [add_comm_group F] [module R F] {p q : submodule R E}
  (h : is_compl p q) {φ : p →ₗ[R] F} {ψ : q →ₗ[R] F} (c : R) :
  of_is_compl h (c • φ) (c • ψ) = c • of_is_compl h φ ψ :=
of_is_compl_eq _ (by simp) (by simp)

section

variables {R₁ : Type*} [comm_ring R₁] [module R₁ E] [module R₁ F]

/-- The linear map from `(p →ₗ[R₁] F) × (q →ₗ[R₁] F)` to `E →ₗ[R₁] F`. -/
def of_is_compl_prod {p q : submodule R₁ E} (h : is_compl p q) :
  ((p →ₗ[R₁] F) × (q →ₗ[R₁] F)) →ₗ[R₁] (E →ₗ[R₁] F) :=
{ to_fun := λ φ, of_is_compl h φ.1 φ.2,
  map_add' := by { intros φ ψ, rw [prod.snd_add, prod.fst_add, of_is_compl_add] },
  map_smul' := by { intros c φ, simp [prod.smul_snd, prod.smul_fst, of_is_compl_smul] } }

@[simp] lemma of_is_compl_prod_apply {p q : submodule R₁ E} (h : is_compl p q)
  (φ : (p →ₗ[R₁] F) × (q →ₗ[R₁] F)) : of_is_compl_prod h φ = of_is_compl h φ.1 φ.2 := rfl

/-- The natural linear equivalence between `(p →ₗ[R₁] F) × (q →ₗ[R₁] F)` and `E →ₗ[R₁] F`. -/
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
      rw [← hab], simp,
    end, .. of_is_compl_prod h }

end

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
linear_equiv.of_bijective (f.prod g) (by simp [← ker_eq_bot, hfg.inf_eq_bot])
  (by simp [← range_eq_top, range_prod_eq hfg.sup_eq_top, *])

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

namespace linear_map

open submodule

/--
A linear endomorphism of a module `E` is a projection onto a submodule `p` if it sends every element
of `E` to `p` and fixes every element of `p`.
The definition allow more generally any `fun_like` type and not just linear maps, so that it can be
used for example with `continuous_linear_map` or `matrix`.
-/
structure is_proj {F : Type*} [fun_like F E (λ _, E)] (f : F) : Prop :=
(map_mem : ∀ x, f x ∈ p)
(map_id : ∀ x ∈ p, f x = x)

lemma is_proj_iff_idempotent (f : E →ₗ[R] E) : (∃ p : submodule R E, is_proj p f) ↔ f ∘ₗ f = f :=
begin
  split,
  { intro h, obtain ⟨p, hp⟩ := h, ext, rw comp_apply, exact hp.map_id (f x) (hp.map_mem x), },
  { intro h, use f.range, split,
    { intro x, exact mem_range_self f x, },
    { intros x hx, obtain ⟨y, hy⟩ := mem_range.1 hx, rw [←hy, ←comp_apply, h], }, },
end

namespace is_proj

variables {p}

/--
Restriction of the codomain of a projection of onto a subspace `p` to `p` instead of the whole
space.
-/
def cod_restrict {f : E →ₗ[R] E} (h : is_proj p f) : E →ₗ[R] p :=
f.cod_restrict p h.map_mem

@[simp]
lemma cod_restrict_apply {f : E →ₗ[R] E} (h : is_proj p f) (x : E) :
  ↑(h.cod_restrict x) = f x := f.cod_restrict_apply p x

@[simp]
lemma cod_restrict_apply_cod {f : E →ₗ[R] E} (h : is_proj p f) (x : p) :
  h.cod_restrict x = x :=
by {ext, rw [cod_restrict_apply], exact h.map_id x x.2}

lemma cod_restrict_ker {f : E →ₗ[R] E} (h : is_proj p f) :
  h.cod_restrict.ker = f.ker := f.ker_cod_restrict p _

lemma is_compl {f : E →ₗ[R] E} (h : is_proj p f) : is_compl p f.ker :=
by { rw ←cod_restrict_ker, exact is_compl_of_proj h.cod_restrict_apply_cod, }

lemma eq_conj_prod_map' {f : E →ₗ[R] E} (h : is_proj p f) :
  f = (p.prod_equiv_of_is_compl f.ker h.is_compl).to_linear_map ∘ₗ prod_map id 0 ∘ₗ
    (p.prod_equiv_of_is_compl f.ker h.is_compl).symm.to_linear_map :=
begin
  refine (linear_map.cancel_right
    (p.prod_equiv_of_is_compl f.ker h.is_compl).surjective).1 _,
  ext,
  { simp only [coe_comp, linear_equiv.coe_to_linear_map, coe_inl, function.comp_app,
  linear_equiv.of_top_apply, linear_equiv.of_injective_apply, coprod_apply, submodule.coe_subtype,
  coe_zero, add_zero, prod_equiv_of_is_compl_symm_apply_left, prod_map_apply, id_coe, id.def,
  zero_apply, coe_prod_equiv_of_is_compl', h.map_id x x.2], },
  {simp only [coe_comp, linear_equiv.coe_to_linear_map, coe_inr, function.comp_app,
  linear_equiv.of_top_apply, linear_equiv.of_injective_apply, coprod_apply, submodule.coe_subtype,
  coe_zero, zero_add, map_coe_ker, prod_equiv_of_is_compl_symm_apply_right, prod_map_apply, id_coe,
  id.def, zero_apply, coe_prod_equiv_of_is_compl'], }
end

end is_proj

end linear_map

end ring

section comm_ring

namespace linear_map

variables {R : Type*} [comm_ring R] {E : Type*} [add_comm_group E] [module R E]  {p : submodule R E}

lemma is_proj.eq_conj_prod_map {f : E →ₗ[R] E} (h : is_proj p f) :
  f = (p.prod_equiv_of_is_compl f.ker h.is_compl).conj (prod_map id 0) :=
by {rw linear_equiv.conj_apply, exact h.eq_conj_prod_map'}

end linear_map

end comm_ring

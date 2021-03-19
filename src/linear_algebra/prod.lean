/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Eric Wieser
-/
import linear_algebra.basic

/-! ### Products of semimodules

This file defines constructors for linear maps whose domains or codomains are products.

It contains theorems relating these to each other, as well as to `submodule.prod`, `submodule.map`,
`submodule.comap`, `linear_map.range`, and `linear_map.ker`.

## Main definitions

- products in the domain:
  - `linear_map.fst`
  - `linear_map.snd`
  - `linear_map.coprod`
  - `linear_map.prod_ext`
- products in the codomain:
  - `linear_map.inl`
  - `linear_map.inr`
  - `linear_map.prod`
- products in both domain and codomain:
  - `linear_map.prod_map`
  - `linear_equiv.prod_map`
  - `linear_equiv.skew_prod`
-/

universes u v w x y z u' v' w' y'
variables {R : Type u} {K : Type u'} {M : Type v} {V : Type v'} {M₂ : Type w} {V₂ : Type w'}
variables {M₃ : Type y} {V₃ : Type y'} {M₄ : Type z} {ι : Type x}


section prod

namespace linear_map

variables (S : Type*) [semiring R] [semiring S]
variables [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [add_comm_monoid M₄]
variables [semimodule R M] [semimodule R M₂] [semimodule R M₃] [semimodule R M₄]
variables (f : M →ₗ[R] M₂)

section
variables (R M M₂)

/-- The first projection of a product is a linear map. -/
def fst : M × M₂ →ₗ[R] M := ⟨prod.fst, λ x y, rfl, λ x y, rfl⟩

/-- The second projection of a product is a linear map. -/
def snd : M × M₂ →ₗ[R] M₂ := ⟨prod.snd, λ x y, rfl, λ x y, rfl⟩
end

@[simp] theorem fst_apply (x : M × M₂) : fst R M M₂ x = x.1 := rfl
@[simp] theorem snd_apply (x : M × M₂) : snd R M M₂ x = x.2 := rfl

/-- The prod of two linear maps is a linear map. -/
@[simps] def prod (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) : (M →ₗ[R] M₂ × M₃) :=
{ to_fun    := λ x, (f x, g x),
  map_add'  := λ x y, by simp only [prod.mk_add_mk, map_add],
  map_smul' := λ c x, by simp only [prod.smul_mk, map_smul] }


@[simp] theorem fst_prod (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) :
  (fst R M₂ M₃).comp (prod f g) = f := by ext; refl

@[simp] theorem snd_prod (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) :
  (snd R M₂ M₃).comp (prod f g) = g := by ext; refl

@[simp] theorem pair_fst_snd : prod (fst R M M₂) (snd R M M₂) = linear_map.id :=
by ext; refl

/-- Taking the product of two maps with the same domain is equivalent to taking the product of
their codomains.

See note [bundled maps over different rings] for why separate `R` and `S` semirings are used. -/
@[simps] def prod_equiv
  [semimodule S M₂] [semimodule S M₃] [smul_comm_class R S M₂] [smul_comm_class R S M₃] :
  ((M →ₗ[R] M₂) × (M →ₗ[R] M₃)) ≃ₗ[S] (M →ₗ[R] M₂ × M₃) :=
{ to_fun := λ f, f.1.prod f.2,
  inv_fun := λ f, ((fst _ _ _).comp f, (snd _ _ _).comp f),
  left_inv := λ f, by ext; refl,
  right_inv := λ f, by ext; refl,
  map_add' := λ a b, rfl,
  map_smul' := λ r a, rfl }

section
variables (R M M₂)

/-- The left injection into a product is a linear map. -/
def inl : M →ₗ[R] M × M₂ := prod linear_map.id 0

/-- The right injection into a product is a linear map. -/
def inr : M₂ →ₗ[R] M × M₂ := prod 0 linear_map.id

end

@[simp] theorem inl_apply (x : M) : inl R M M₂ x = (x, 0) := rfl
@[simp] theorem inr_apply (x : M₂) : inr R M M₂ x = (0, x) := rfl

theorem inl_eq_prod : inl R M M₂ = prod linear_map.id 0 := rfl

theorem inr_eq_prod : inr R M M₂ = prod 0 linear_map.id := rfl

theorem inl_injective : function.injective (inl R M M₂) :=
λ _, by simp

theorem inr_injective : function.injective (inr R M M₂) :=
λ _, by simp

/-- The coprod function `λ x : M × M₂, f.1 x.1 + f.2 x.2` is a linear map. -/
def coprod (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) : M × M₂ →ₗ[R] M₃ :=
f.comp (fst _ _ _) + g.comp (snd _ _ _)

@[simp] theorem coprod_apply (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) (x : M × M₂) :
  coprod f g x = f x.1 + g x.2 := rfl

@[simp] theorem coprod_inl (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) :
  (coprod f g).comp (inl R M M₂) = f :=
by ext; simp only [map_zero, add_zero, coprod_apply, inl_apply, comp_apply]

@[simp] theorem coprod_inr (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) :
  (coprod f g).comp (inr R M M₂) = g :=
by ext; simp only [map_zero, coprod_apply, inr_apply, zero_add, comp_apply]

@[simp] theorem coprod_inl_inr : coprod (inl R M M₂) (inr R M M₂) = linear_map.id :=
by ext; simp only [prod.mk_add_mk, add_zero, id_apply, coprod_apply,
  inl_apply, inr_apply, zero_add]

theorem comp_coprod (f : M₃ →ₗ[R] M₄) (g₁ : M →ₗ[R] M₃) (g₂ : M₂ →ₗ[R] M₃) :
  f.comp (g₁.coprod g₂) = (f.comp g₁).coprod (f.comp g₂) :=
ext $ λ x, f.map_add (g₁ x.1) (g₂ x.2)

theorem fst_eq_coprod : fst R M M₂ = coprod linear_map.id 0 := by ext; simp

theorem snd_eq_coprod : snd R M M₂ = coprod 0 linear_map.id := by ext; simp

@[simp] theorem coprod_comp_prod (f : M₂ →ₗ[R] M₄) (g : M₃ →ₗ[R] M₄)
  (f' : M →ₗ[R] M₂) (g' : M →ₗ[R] M₃) :
  (f.coprod g).comp (f'.prod g') = f.comp f' + g.comp g' :=
rfl

/-- Taking the product of two maps with the same codomain is equivalent to taking the product of
their domains.

See note [bundled maps over different rings] for why separate `R` and `S` semirings are used. -/
@[simps] def coprod_equiv [semimodule S M₃] [smul_comm_class R S M₃] :
  ((M →ₗ[R] M₃) × (M₂ →ₗ[R] M₃)) ≃ₗ[S] (M × M₂ →ₗ[R] M₃) :=
{ to_fun := λ f, f.1.coprod f.2,
  inv_fun := λ f, (f.comp (inl _ _ _), f.comp (inr _ _ _)),
  left_inv := λ f, by simp only [prod.mk.eta, coprod_inl, coprod_inr],
  right_inv := λ f, by simp only [←comp_coprod, comp_id, coprod_inl_inr],
  map_add' := λ a b,
    by { ext, simp only [prod.snd_add, add_apply, coprod_apply, prod.fst_add], ac_refl },
  map_smul' := λ r a,
    by { ext, simp only [smul_add, smul_apply, prod.smul_snd, prod.smul_fst, coprod_apply] } }

theorem prod_ext_iff {f g : M × M₂ →ₗ[R] M₃} :
  f = g ↔ f.comp (inl _ _ _) = g.comp (inl _ _ _) ∧ f.comp (inr _ _ _) = g.comp (inr _ _ _) :=
(coprod_equiv ℕ).symm.injective.eq_iff.symm.trans prod.ext_iff

/--
Split equality of linear maps from a product into linear maps over each component, to allow `ext`
to apply lemmas specific to `M →ₗ M₃` and `M₂ →ₗ M₃`.

See note [partially-applied ext lemmas]. -/
@[ext] theorem prod_ext {f g : M × M₂ →ₗ[R] M₃}
  (hl : f.comp (inl _ _ _) = g.comp (inl _ _ _))
  (hr : f.comp (inr _ _ _) = g.comp (inr _ _ _)) :
  f = g :=
prod_ext_iff.2 ⟨hl, hr⟩

/-- `prod.map` of two linear maps. -/
def prod_map (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₄) : (M × M₂) →ₗ[R] (M₃ × M₄) :=
(f.comp (fst R M M₂)).prod (g.comp (snd R M M₂))

@[simp] theorem prod_map_apply (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₄) (x) :
  f.prod_map g x = (f x.1, g x.2) := rfl

end linear_map

end prod

namespace linear_map
open submodule

variables [semiring R]
  [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [add_comm_monoid M₄]
  [semimodule R M] [semimodule R M₂] [semimodule R M₃] [semimodule R M₄]

lemma range_coprod (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) :
  (f.coprod g).range = f.range ⊔ g.range :=
submodule.ext $ λ x, by simp [mem_sup]

lemma is_compl_range_inl_inr : is_compl (inl R M M₂).range (inr R M M₂).range :=
begin
  split,
  { rintros ⟨_, _⟩ ⟨⟨x, -, hx⟩, ⟨y, -, hy⟩⟩,
    simp only [prod.ext_iff, inl_apply, inr_apply, mem_bot] at hx hy ⊢,
    exact ⟨hy.1.symm, hx.2.symm⟩ },
  { rintros ⟨x, y⟩ -,
    simp only [mem_sup, mem_range, exists_prop],
    refine ⟨(x, 0), ⟨x, rfl⟩, (0, y), ⟨y, rfl⟩, _⟩,
    simp }
end

lemma sup_range_inl_inr : (inl R M M₂).range ⊔ (inr R M M₂).range = ⊤ :=
is_compl_range_inl_inr.sup_eq_top

lemma disjoint_inl_inr : disjoint (inl R M M₂).range (inr R M M₂).range :=
by simp [disjoint_def, @eq_comm M 0, @eq_comm M₂ 0] {contextual := tt}; intros; refl
theorem map_coprod_prod (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃)
  (p : submodule R M) (q : submodule R M₂) :
  map (coprod f g) (p.prod q) = map f p ⊔ map g q :=
begin
  refine le_antisymm _ (sup_le (map_le_iff_le_comap.2 _) (map_le_iff_le_comap.2 _)),
  { rw set_like.le_def, rintro _ ⟨x, ⟨h₁, h₂⟩, rfl⟩,
    exact mem_sup.2 ⟨_, ⟨_, h₁, rfl⟩, _, ⟨_, h₂, rfl⟩, rfl⟩ },
  { exact λ x hx, ⟨(x, 0), by simp [hx]⟩ },
  { exact λ x hx, ⟨(0, x), by simp [hx]⟩ }
end

theorem comap_prod_prod (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃)
  (p : submodule R M₂) (q : submodule R M₃) :
  comap (prod f g) (p.prod q) = comap f p ⊓ comap g q :=
submodule.ext $ λ x, iff.rfl

theorem prod_eq_inf_comap (p : submodule R M) (q : submodule R M₂) :
  p.prod q = p.comap (linear_map.fst R M M₂) ⊓ q.comap (linear_map.snd R M M₂) :=
submodule.ext $ λ x, iff.rfl

theorem prod_eq_sup_map (p : submodule R M) (q : submodule R M₂) :
  p.prod q = p.map (linear_map.inl R M M₂) ⊔ q.map (linear_map.inr R M M₂) :=
by rw [← map_coprod_prod, coprod_inl_inr, map_id]

lemma span_inl_union_inr {s : set M} {t : set M₂} :
  span R (inl R M  M₂ '' s ∪ inr R M M₂ '' t) = (span R s).prod (span R t) :=
by rw [span_union, prod_eq_sup_map, ← span_image, ← span_image]

@[simp] lemma ker_prod (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) :
  ker (prod f g) = ker f ⊓ ker g :=
by rw [ker, ← prod_bot, comap_prod_prod]; refl

lemma range_prod_le (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) :
  range (prod f g) ≤ (range f).prod (range g) :=
begin
  simp only [set_like.le_def, prod_apply, mem_range, set_like.mem_coe, mem_prod,
    exists_imp_distrib],
  rintro _ x rfl,
  exact ⟨⟨x, rfl⟩, ⟨x, rfl⟩⟩
end

end linear_map

namespace submodule
open linear_map

variables [semiring R]
variables [add_comm_monoid M] [add_comm_monoid M₂]
variables [semimodule R M] [semimodule R M₂]

lemma sup_eq_range (p q : submodule R M) : p ⊔ q = (p.subtype.coprod q.subtype).range :=
submodule.ext $ λ x, by simp [submodule.mem_sup, set_like.exists]

variables (p : submodule R M) (q : submodule R M₂)

@[simp] theorem map_inl : p.map (inl R M M₂) = prod p ⊥ :=
by { ext ⟨x, y⟩, simp only [and.left_comm, eq_comm, mem_map, prod.mk.inj_iff, inl_apply, mem_bot,
  exists_eq_left', mem_prod] }

@[simp] theorem map_inr : q.map (inr R M M₂) = prod ⊥ q :=
by ext ⟨x, y⟩; simp [and.left_comm, eq_comm]

@[simp] theorem comap_fst : p.comap (fst R M M₂) = prod p ⊤ :=
by ext ⟨x, y⟩; simp

@[simp] theorem comap_snd : q.comap (snd R M M₂) = prod ⊤ q :=
by ext ⟨x, y⟩; simp

@[simp] theorem prod_comap_inl : (prod p q).comap (inl R M M₂) = p := by ext; simp

@[simp] theorem prod_comap_inr : (prod p q).comap (inr R M M₂) = q := by ext; simp

@[simp] theorem prod_map_fst : (prod p q).map (fst R M M₂) = p :=
by ext x; simp [(⟨0, zero_mem _⟩ : ∃ x, x ∈ q)]

@[simp] theorem prod_map_snd : (prod p q).map (snd R M M₂) = q :=
by ext x; simp [(⟨0, zero_mem _⟩ : ∃ x, x ∈ p)]

@[simp] theorem ker_inl : (inl R M M₂).ker = ⊥ :=
by rw [ker, ← prod_bot, prod_comap_inl]

@[simp] theorem ker_inr : (inr R M M₂).ker = ⊥ :=
by rw [ker, ← prod_bot, prod_comap_inr]

@[simp] theorem range_fst : (fst R M M₂).range = ⊤ :=
by rw [range, ← prod_top, prod_map_fst]

@[simp] theorem range_snd : (snd R M M₂).range = ⊤ :=
by rw [range, ← prod_top, prod_map_snd]

end submodule

namespace linear_equiv
section

variables [semiring R]
variables [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [add_comm_monoid M₄]
variables {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂}
variables {semimodule_M₃ : semimodule R M₃} {semimodule_M₄ : semimodule R M₄}
variables (e₁ : M ≃ₗ[R] M₂) (e₂ : M₃ ≃ₗ[R] M₄)

/-- Product of linear equivalences; the maps come from `equiv.prod_congr`. -/
protected def prod :
  (M × M₃) ≃ₗ[R] (M₂ × M₄) :=
{ map_add'  := λ x y, prod.ext (e₁.map_add _ _) (e₂.map_add _ _),
  map_smul' := λ c x, prod.ext (e₁.map_smul c _) (e₂.map_smul c _),
  .. equiv.prod_congr e₁.to_equiv e₂.to_equiv }

lemma prod_symm : (e₁.prod e₂).symm = e₁.symm.prod e₂.symm := rfl

@[simp] lemma prod_apply (p) :
  e₁.prod e₂ p = (e₁ p.1, e₂ p.2) := rfl

@[simp, norm_cast] lemma coe_prod :
  (e₁.prod e₂ : (M × M₃) →ₗ[R] (M₂ × M₄)) = (e₁ : M →ₗ[R] M₂).prod_map (e₂ : M₃ →ₗ[R] M₄) := rfl

end

section
variables [semiring R]
variables [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [add_comm_group M₄]
variables {semimodule_M : semimodule R M} {semimodule_M₂ : semimodule R M₂}
variables {semimodule_M₃ : semimodule R M₃} {semimodule_M₄ : semimodule R M₄}
variables (e₁ : M ≃ₗ[R] M₂) (e₂ : M₃ ≃ₗ[R] M₄)

/-- Equivalence given by a block lower diagonal matrix. `e₁` and `e₂` are diagonal square blocks,
  and `f` is a rectangular block below the diagonal. -/
protected def skew_prod (f : M →ₗ[R] M₄) :
  (M × M₃) ≃ₗ[R] M₂ × M₄ :=
{ inv_fun := λ p : M₂ × M₄, (e₁.symm p.1, e₂.symm (p.2 - f (e₁.symm p.1))),
  left_inv := λ p, by simp,
  right_inv := λ p, by simp,
  .. ((e₁ : M →ₗ[R] M₂).comp (linear_map.fst R M M₃)).prod
    ((e₂ : M₃ →ₗ[R] M₄).comp (linear_map.snd R M M₃) +
      f.comp (linear_map.fst R M M₃)) }

@[simp] lemma skew_prod_apply (f : M →ₗ[R] M₄) (x) :
  e₁.skew_prod e₂ f x = (e₁ x.1, e₂ x.2 + f x.1) := rfl

@[simp] lemma skew_prod_symm_apply (f : M →ₗ[R] M₄) (x) :
  (e₁.skew_prod e₂ f).symm x = (e₁.symm x.1, e₂.symm (x.2 - f (e₁.symm x.1))) := rfl

end
end linear_equiv

namespace linear_map
open submodule

variables [ring R]
variables [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃]
variables [semimodule R M] [semimodule R M₂] [semimodule R M₃]

/-- If the union of the kernels `ker f` and `ker g` spans the domain, then the range of
`prod f g` is equal to the product of `range f` and `range g`. -/
lemma range_prod_eq {f : M →ₗ[R] M₂} {g : M →ₗ[R] M₃} (h : ker f ⊔ ker g = ⊤) :
  range (prod f g) = (range f).prod (range g) :=
begin
  refine le_antisymm (f.range_prod_le g) _,
  simp only [le_def', prod_apply, mem_range, mem_coe, mem_prod, exists_imp_distrib, and_imp,
    prod.forall],
  rintros _ _ x rfl y rfl,
  simp only [prod.mk.inj_iff, ← sub_mem_ker_iff],
  have : y - x ∈ ker f ⊔ ker g, { simp only [h, mem_top] },
  rcases mem_sup.1 this with ⟨x', hx', y', hy', H⟩,
  refine ⟨x' + x, _, _⟩,
  { rwa add_sub_cancel },
  { rwa [← eq_sub_iff_add_eq.1 H, add_sub_add_right_eq_sub, ← neg_mem_iff, neg_sub,
      add_sub_cancel'] }
end

end linear_map

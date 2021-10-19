/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.lie.nilpotent
import algebra.lie.tensor_product
import algebra.lie.character
import algebra.lie.cartan_subalgebra
import linear_algebra.eigenspace
import ring_theory.tensor_product

/-!
# Weights and roots of Lie modules and Lie algebras

Just as a key tool when studying the behaviour of a linear operator is to decompose the space on
which it acts into a sum of (generalised) eigenspaces, a key tool when studying a representation `M`
of Lie algebra `L` is to decompose `M` into a sum of simultaneous eigenspaces of `x` as `x` ranges
over `L`. These simultaneous generalised eigenspaces are known as the weight spaces of `M`.

When `L` is nilpotent, it follows from the binomial theorem that weight spaces are Lie submodules.
Even when `L` is not nilpotent, it may be useful to study its representations by restricting them
to a nilpotent subalgebra (e.g., a Cartan subalgebra). In the particular case when we view `L` as a
module over itself via the adjoint action, the weight spaces of `L` restricted to a nilpotent
subalgebra are known as root spaces.

Basic definitions and properties of the above ideas are provided in this file.

## Main definitions

  * `lie_module.weight_space`
  * `lie_module.is_weight`
  * `lie_algebra.root_space`
  * `lie_algebra.is_root`
  * `lie_algebra.root_space_weight_space_product`
  * `lie_algebra.root_space_product`

## References

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 7--9*](bourbaki1975b)

## Tags

lie character, eigenvalue, eigenspace, weight, weight vector, root, root vector
-/

universes u v w w₁ w₂ w₃

variables {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L]
variables (H : lie_subalgebra R L) [lie_algebra.is_nilpotent R H]
variables (M : Type w) [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M]

namespace lie_module

open lie_algebra
open tensor_product
open tensor_product.lie_module

open_locale big_operators
open_locale tensor_product

/-- Given a Lie module `M` over a Lie algebra `L`, the pre-weight space of `M` with respect to a
map `χ : L → R` is the simultaneous generalized eigenspace of the action of all `x : L` on `M`,
with eigenvalues `χ x`.

See also `lie_module.weight_space`. -/
def pre_weight_space (χ : L → R) : submodule R M :=
⨅ (x : L), (to_endomorphism R L M x).maximal_generalized_eigenspace (χ x)

lemma mem_pre_weight_space (χ : L → R) (m : M) :
  m ∈ pre_weight_space M χ ↔ ∀ x, ∃ (k : ℕ), ((to_endomorphism R L M x - (χ x) • 1)^k) m = 0 :=
by simp [pre_weight_space, -linear_map.pow_apply]

variables (L)

/-- See also `bourbaki1975b` Chapter VII §1.1, Proposition 2 (ii). -/
protected lemma weight_vector_multiplication (M₁ : Type w₁) (M₂ : Type w₂) (M₃ : Type w₃)
  [add_comm_group M₁] [module R M₁] [lie_ring_module L M₁] [lie_module R L M₁]
  [add_comm_group M₂] [module R M₂] [lie_ring_module L M₂] [lie_module R L M₂]
  [add_comm_group M₃] [module R M₃] [lie_ring_module L M₃] [lie_module R L M₃]
 (g : M₁ ⊗[R] M₂ →ₗ⁅R,L⁆ M₃) (χ₁ χ₂ : L → R) :
  ((g : M₁ ⊗[R] M₂ →ₗ[R] M₃).comp
  (map_incl (pre_weight_space M₁ χ₁) (pre_weight_space M₂ χ₂))).range ≤
    pre_weight_space M₃ (χ₁ + χ₂) :=
begin
  /- Unpack the statement of the goal. -/
  intros m₃,
  simp only [lie_module_hom.coe_to_linear_map, pi.add_apply, function.comp_app,
    mem_pre_weight_space, linear_map.coe_comp, tensor_product.map_incl, exists_imp_distrib,
    linear_map.mem_range],
  rintros t rfl x,

  /- Set up some notation. -/
  let F : module.End R M₃ := (to_endomorphism R L M₃ x) - (χ₁ x + χ₂ x) • 1,
  change ∃ k, (F^k) (g _) = 0,

  /- The goal is linear in `t` so use induction to reduce to the case that `t` is a pure tensor. -/
  apply t.induction_on,
  { use 0, simp only [linear_map.map_zero, lie_module_hom.map_zero], },
  swap,
  { rintros t₁ t₂ ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩, use max k₁ k₂,
    simp only [lie_module_hom.map_add, linear_map.map_add,
      linear_map.pow_map_zero_of_le (le_max_left k₁ k₂) hk₁,
      linear_map.pow_map_zero_of_le (le_max_right k₁ k₂) hk₂, add_zero], },

  /- Now the main argument: pure tensors. -/
  rintros ⟨m₁, hm₁⟩ ⟨m₂, hm₂⟩,
  change ∃ k, (F^k) ((g : M₁ ⊗[R] M₂ →ₗ[R] M₃) (m₁ ⊗ₜ m₂)) = 0,

  /- Eliminate `g` from the picture. -/
  let f₁ : module.End R (M₁ ⊗[R] M₂) := (to_endomorphism R L M₁ x - (χ₁ x) • 1).rtensor M₂,
  let f₂ : module.End R (M₁ ⊗[R] M₂) := (to_endomorphism R L M₂ x - (χ₂ x) • 1).ltensor M₁,
  have h_comm_square : F ∘ₗ ↑g = (g : M₁ ⊗[R] M₂ →ₗ[R] M₃).comp (f₁ + f₂),
  { ext m₁ m₂, simp only [← g.map_lie x (m₁ ⊗ₜ m₂), add_smul, sub_tmul, tmul_sub, smul_tmul,
      lie_tmul_right, tmul_smul, to_endomorphism_apply_apply, lie_module_hom.map_smul,
      linear_map.one_apply, lie_module_hom.coe_to_linear_map, linear_map.smul_apply,
      function.comp_app, linear_map.coe_comp, linear_map.rtensor_tmul, lie_module_hom.map_add,
      linear_map.add_apply, lie_module_hom.map_sub, linear_map.sub_apply, linear_map.ltensor_tmul,
      algebra_tensor_module.curry_apply, curry_apply, linear_map.to_fun_eq_coe,
      linear_map.coe_restrict_scalars_eq_coe], abel, },
  suffices : ∃ k, ((f₁ + f₂)^k) (m₁ ⊗ₜ m₂) = 0,
  { obtain ⟨k, hk⟩ := this, use k,
    rw [← linear_map.comp_apply, linear_map.commute_pow_left_of_commute h_comm_square,
      linear_map.comp_apply, hk, linear_map.map_zero], },

  /- Unpack the information we have about `m₁`, `m₂`. -/
  simp only [mem_pre_weight_space] at hm₁ hm₂,
  obtain ⟨k₁, hk₁⟩ := hm₁ x,
  obtain ⟨k₂, hk₂⟩ := hm₂ x,
  have hf₁ : (f₁^k₁) (m₁ ⊗ₜ m₂) = 0,
  { simp only [hk₁, zero_tmul, linear_map.rtensor_tmul, linear_map.rtensor_pow], },
  have hf₂ : (f₂^k₂) (m₁ ⊗ₜ m₂) = 0,
  { simp only [hk₂, tmul_zero, linear_map.ltensor_tmul, linear_map.ltensor_pow], },

  /- It's now just an application of the binomial theorem. -/
  use k₁ + k₂ - 1,
  have hf_comm : commute f₁ f₂,
  { ext m₁ m₂, simp only [linear_map.mul_apply, linear_map.rtensor_tmul, linear_map.ltensor_tmul,
      algebra_tensor_module.curry_apply, linear_map.to_fun_eq_coe, linear_map.ltensor_tmul,
      curry_apply, linear_map.coe_restrict_scalars_eq_coe], },
  rw hf_comm.add_pow',
  simp only [tensor_product.map_incl, submodule.subtype_apply, finset.sum_apply,
    submodule.coe_mk, linear_map.coe_fn_sum, tensor_product.map_tmul, linear_map.smul_apply],

  /- The required sum is zero because each individual term is zero. -/
  apply finset.sum_eq_zero,
  rintros ⟨i, j⟩ hij,

  /- Eliminate the binomial coefficients from the picture. -/
  suffices : (f₁^i * f₂^j) (m₁ ⊗ₜ m₂) = 0, { rw this, apply smul_zero, },

  /- Finish off with appropriate case analysis. -/
  cases nat.le_or_le_of_add_eq_add_pred (finset.nat.mem_antidiagonal.mp hij) with hi hj,
  { rw [(hf_comm.pow_pow i j).eq, linear_map.mul_apply, linear_map.pow_map_zero_of_le hi hf₁,
    linear_map.map_zero], },
  { rw [linear_map.mul_apply, linear_map.pow_map_zero_of_le hj hf₂, linear_map.map_zero], },
end

variables {L M}

lemma lie_mem_pre_weight_space_of_mem_pre_weight_space {χ₁ χ₂ : L → R} {x : L} {m : M}
  (hx : x ∈ pre_weight_space L χ₁) (hm : m ∈ pre_weight_space M χ₂) :
  ⁅x, m⁆ ∈ pre_weight_space M (χ₁ + χ₂) :=
begin
  apply lie_module.weight_vector_multiplication L L M M (to_module_hom R L M) χ₁ χ₂,
  simp only [lie_module_hom.coe_to_linear_map, function.comp_app, linear_map.coe_comp,
    tensor_product.map_incl, linear_map.mem_range],
  use [⟨x, hx⟩ ⊗ₜ ⟨m, hm⟩],
  simp only [submodule.subtype_apply, to_module_hom_apply, tensor_product.map_tmul],
  refl,
end

variables (M)

/-- If a Lie algebra is nilpotent, then pre-weight spaces are Lie submodules. -/
def weight_space [lie_algebra.is_nilpotent R L] (χ : L → R) : lie_submodule R L M :=
{ lie_mem := λ x m hm,
  begin
    rw ← zero_add χ,
    refine lie_mem_pre_weight_space_of_mem_pre_weight_space _ hm,
    suffices : pre_weight_space L (0 : L → R) = ⊤, { simp only [this, submodule.mem_top], },
    exact lie_algebra.infi_max_gen_zero_eigenspace_eq_top_of_nilpotent R L,
  end,
  .. pre_weight_space M χ }

lemma mem_weight_space [lie_algebra.is_nilpotent R L] (χ : L → R) (m : M) :
  m ∈ weight_space M χ ↔ m ∈ pre_weight_space M χ :=
iff.rfl

/-- See also the more useful form `lie_module.zero_weight_space_eq_top_of_nilpotent`. -/
@[simp] lemma zero_weight_space_eq_top_of_nilpotent'
  [lie_algebra.is_nilpotent R L] [is_nilpotent R L M] :
  weight_space M (0 : L → R) = ⊤ :=
begin
  rw [← lie_submodule.coe_to_submodule_eq_iff, lie_submodule.top_coe_submodule],
  exact infi_max_gen_zero_eigenspace_eq_top_of_nilpotent R L M,
end

lemma coe_weight_space_of_top [lie_algebra.is_nilpotent R L] (χ : L → R) :
  (weight_space M (χ ∘ (⊤ : lie_subalgebra R L).incl) : submodule R M) = weight_space M χ :=
begin
  ext m,
  simp only [weight_space, lie_submodule.coe_to_submodule_mk, lie_subalgebra.coe_bracket_of_module,
    function.comp_app, mem_pre_weight_space],
  split; intros h x,
  { obtain ⟨k, hk⟩ := h ⟨x, set.mem_univ x⟩, use k, exact hk, },
  { obtain ⟨k, hk⟩ := h x, use k, exact hk, },
end

@[simp] lemma zero_weight_space_eq_top_of_nilpotent
  [lie_algebra.is_nilpotent R L] [is_nilpotent R L M] :
  weight_space M (0 : (⊤ : lie_subalgebra R L) → R) = ⊤ :=
begin
  /- We use `coe_weight_space_of_top` as a trick to circumvent the fact that we don't (yet) know
    `is_nilpotent R (⊤ : lie_subalgebra R L) M` is equivalent to `is_nilpotent R L M`. -/
  have h₀ : (0 : L → R) ∘ (⊤ : lie_subalgebra R L).incl = 0, { ext, refl, },
  rw [← lie_submodule.coe_to_submodule_eq_iff, lie_submodule.top_coe_submodule, ← h₀,
    coe_weight_space_of_top, ← infi_max_gen_zero_eigenspace_eq_top_of_nilpotent R L M],
  refl,
end

/-- Given a Lie module `M` of a Lie algebra `L`, a weight of `M` with respect to a nilpotent
subalgebra `H ⊆ L` is a Lie character whose corresponding weight space is non-empty. -/
def is_weight (χ : lie_character R H) : Prop := weight_space M χ ≠ ⊥

/-- For a non-trivial nilpotent Lie module over a nilpotent Lie algebra, the zero character is a
weight with respect to the `⊤` Lie subalgebra. -/
lemma is_weight_zero_of_nilpotent
   [nontrivial M] [lie_algebra.is_nilpotent R L] [is_nilpotent R L M] :
   is_weight (⊤ : lie_subalgebra R L) M 0 :=
by { rw [is_weight, lie_hom.coe_zero, zero_weight_space_eq_top_of_nilpotent], exact top_ne_bot, }

end lie_module

namespace lie_algebra

open_locale tensor_product
open tensor_product.lie_module
open lie_module

/-- Given a nilpotent Lie subalgebra `H ⊆ L`, the root space of a map `χ : H → R` is the weight
space of `L` regarded as a module of `H` via the adjoint action. -/
abbreviation root_space (χ : H → R) : lie_submodule R H L := weight_space L χ

@[simp] lemma zero_root_space_eq_top_of_nilpotent [h : is_nilpotent R L] :
  root_space (⊤ : lie_subalgebra R L) 0 = ⊤ :=
zero_weight_space_eq_top_of_nilpotent L

/-- A root of a Lie algebra `L` with respect to a nilpotent subalgebra `H ⊆ L` is a weight of `L`,
regarded as a module of `H` via the adjoint action. -/
abbreviation is_root := is_weight H L

@[simp] lemma root_space_comap_eq_weight_space (χ : H → R) :
  (root_space H χ).comap H.incl' = weight_space H χ :=
begin
  ext x,
  let f : H → module.End R L := λ y, to_endomorphism R H L y - (χ y) • 1,
  let g : H → module.End R H := λ y, to_endomorphism R H H y - (χ y) • 1,
  suffices : (∀ (y : H), ∃ (k : ℕ), ((f y)^k).comp (H.incl : H →ₗ[R] L) x = 0) ↔
              ∀ (y : H), ∃ (k : ℕ), (H.incl : H →ₗ[R] L).comp ((g y)^k) x = 0,
  { simp only [lie_hom.coe_to_linear_map, lie_subalgebra.coe_incl, function.comp_app,
      linear_map.coe_comp, submodule.coe_eq_zero] at this,
    simp only [mem_weight_space, mem_pre_weight_space,
      lie_subalgebra.coe_incl', lie_submodule.mem_comap, this], },
  have hfg : ∀ (y : H), (f y).comp (H.incl : H →ₗ[R] L) = (H.incl : H →ₗ[R] L).comp (g y),
  { rintros ⟨y, hz⟩, ext ⟨z, hz⟩,
    simp only [submodule.coe_sub, to_endomorphism_apply_apply, lie_hom.coe_to_linear_map,
      linear_map.one_apply, lie_subalgebra.coe_incl, lie_subalgebra.coe_bracket_of_module,
      lie_subalgebra.coe_bracket, linear_map.smul_apply, function.comp_app,
      submodule.coe_smul_of_tower, linear_map.coe_comp, linear_map.sub_apply], },
  simp_rw [linear_map.commute_pow_left_of_commute (hfg _)],
end

variables {H M}

lemma lie_mem_weight_space_of_mem_weight_space {χ₁ χ₂ : H → R} {x : L} {m : M}
  (hx : x ∈ root_space H χ₁) (hm : m ∈ weight_space M χ₂) : ⁅x, m⁆ ∈ weight_space M (χ₁ + χ₂) :=
begin
  apply lie_module.weight_vector_multiplication
    H L M M ((to_module_hom R L M).restrict_lie H) χ₁ χ₂,
  simp only [lie_module_hom.coe_to_linear_map, function.comp_app, linear_map.coe_comp,
    tensor_product.map_incl, linear_map.mem_range],
  use [⟨x, hx⟩ ⊗ₜ ⟨m, hm⟩],
  simp only [submodule.subtype_apply, to_module_hom_apply, submodule.coe_mk,
    lie_module_hom.coe_restrict_lie, tensor_product.map_tmul],
end

variables (R L H M)

/--
Auxiliary definition for `root_space_weight_space_product`,
which is close to the deterministic timeout limit.
-/
def root_space_weight_space_product_aux {χ₁ χ₂ χ₃ : H → R} (hχ : χ₁ + χ₂ = χ₃) :
  (root_space H χ₁) →ₗ[R] (weight_space M χ₂) →ₗ[R] (weight_space M χ₃) :=
{ to_fun    := λ x,
  { to_fun    :=
      λ m, ⟨⁅(x : L), (m : M)⁆,
            hχ ▸ (lie_mem_weight_space_of_mem_weight_space x.property m.property) ⟩,
    map_add'  := λ m n, by { simp only [lie_submodule.coe_add, lie_add], refl, },
    map_smul' := λ t m, by { conv_lhs { congr, rw [lie_submodule.coe_smul, lie_smul], }, refl, }, },
  map_add'  := λ x y, by ext m; rw [linear_map.add_apply, linear_map.coe_mk, linear_map.coe_mk,
    linear_map.coe_mk, subtype.coe_mk, lie_submodule.coe_add, lie_submodule.coe_add, add_lie,
    subtype.coe_mk, subtype.coe_mk],
  map_smul' := λ t x,
  begin
    simp only [ring_hom.id_apply],
    ext m,
    rw [linear_map.smul_apply, linear_map.coe_mk, linear_map.coe_mk,
      subtype.coe_mk, lie_submodule.coe_smul, smul_lie, lie_submodule.coe_smul, subtype.coe_mk],
  end, }

/-- Given a nilpotent Lie subalgebra `H ⊆ L` together with `χ₁ χ₂ : H → R`, there is a natural
`R`-bilinear product of root vectors and weight vectors, compatible with the actions of `H`. -/
def root_space_weight_space_product (χ₁ χ₂ χ₃ : H → R) (hχ : χ₁ + χ₂ = χ₃) :
  (root_space H χ₁) ⊗[R] (weight_space M χ₂) →ₗ⁅R,H⁆ weight_space M χ₃ :=
lift_lie R H (root_space H χ₁) (weight_space M χ₂) (weight_space M χ₃)
{ to_linear_map := root_space_weight_space_product_aux R L H M hχ,
  map_lie' := λ x y, by ext m; rw [root_space_weight_space_product_aux,
    lie_hom.lie_apply, lie_submodule.coe_sub, linear_map.coe_mk,
    linear_map.coe_mk, subtype.coe_mk, subtype.coe_mk, lie_submodule.coe_bracket,
    lie_submodule.coe_bracket, subtype.coe_mk, lie_subalgebra.coe_bracket_of_module,
    lie_subalgebra.coe_bracket_of_module, lie_submodule.coe_bracket,
    lie_subalgebra.coe_bracket_of_module, lie_lie], }

@[simp] lemma coe_root_space_weight_space_product_tmul
  (χ₁ χ₂ χ₃ : H → R) (hχ : χ₁ + χ₂ = χ₃) (x : root_space H χ₁) (m : weight_space M χ₂) :
  (root_space_weight_space_product R L H M χ₁ χ₂ χ₃ hχ (x ⊗ₜ m) : M) = ⁅(x : L), (m : M)⁆ :=
by simp only [root_space_weight_space_product, root_space_weight_space_product_aux,
  lift_apply, lie_module_hom.coe_to_linear_map,
  coe_lift_lie_eq_lift_coe, submodule.coe_mk, linear_map.coe_mk, lie_module_hom.coe_mk]

/-- Given a nilpotent Lie subalgebra `H ⊆ L` together with `χ₁ χ₂ : H → R`, there is a natural
`R`-bilinear product of root vectors, compatible with the actions of `H`. -/
def root_space_product (χ₁ χ₂ χ₃ : H → R) (hχ : χ₁ + χ₂ = χ₃) :
  (root_space H χ₁) ⊗[R] (root_space H χ₂) →ₗ⁅R,H⁆ root_space H χ₃ :=
root_space_weight_space_product R L H L χ₁ χ₂ χ₃ hχ

@[simp] lemma root_space_product_def :
  root_space_product R L H = root_space_weight_space_product R L H L :=
rfl

lemma root_space_product_tmul
  (χ₁ χ₂ χ₃ : H → R) (hχ : χ₁ + χ₂ = χ₃) (x : root_space H χ₁) (y : root_space H χ₂) :
  (root_space_product R L H χ₁ χ₂ χ₃ hχ (x ⊗ₜ y) : L) = ⁅(x : L), (y : L)⁆ :=
by simp only [root_space_product_def, coe_root_space_weight_space_product_tmul]

/-- Given a nilpotent Lie subalgebra `H ⊆ L`, the root space of the zero map `0 : H → R` is a Lie
subalgebra of `L`. -/
def zero_root_subalgebra : lie_subalgebra R L :=
{ lie_mem' := λ x y hx hy, by
  { let xy : (root_space H 0) ⊗[R] (root_space H 0) := ⟨x, hx⟩ ⊗ₜ ⟨y, hy⟩,
    suffices : (root_space_product R L H 0 0 0 (add_zero 0) xy : L) ∈ root_space H 0,
    { rwa [root_space_product_tmul, subtype.coe_mk, subtype.coe_mk] at this, },
    exact (root_space_product R L H 0 0 0 (add_zero 0) xy).property, },
  .. (root_space H 0 : submodule R L) }

@[simp] lemma coe_zero_root_subalgebra :
  (zero_root_subalgebra R L H : submodule R L) = root_space H 0 :=
rfl

lemma mem_zero_root_subalgebra (x : L) :
  x ∈ zero_root_subalgebra R L H ↔ ∀ (y : H), ∃ (k : ℕ), ((to_endomorphism R H L y)^k) x = 0 :=
by simp only [zero_root_subalgebra, mem_weight_space, mem_pre_weight_space, pi.zero_apply, sub_zero,
  set_like.mem_coe, zero_smul, lie_submodule.mem_coe_submodule, submodule.mem_carrier,
  lie_subalgebra.mem_mk_iff]

lemma to_lie_submodule_le_root_space_zero : H.to_lie_submodule ≤ root_space H 0 :=
begin
  intros x hx,
  simp only [lie_subalgebra.mem_to_lie_submodule] at hx,
  simp only [mem_weight_space, mem_pre_weight_space, pi.zero_apply, sub_zero, zero_smul],
  intros y,
  unfreezingI { obtain ⟨k, hk⟩ := (infer_instance : is_nilpotent R H) },
  use k,
  let f : module.End R H := to_endomorphism R H H y,
  let g : module.End R L := to_endomorphism R H L y,
  have hfg : g.comp (H : submodule R L).subtype = (H : submodule R L).subtype.comp f,
  { ext z, simp only [to_endomorphism_apply_apply, submodule.subtype_apply,
      lie_subalgebra.coe_bracket_of_module, lie_subalgebra.coe_bracket, function.comp_app,
      linear_map.coe_comp], },
  change (g^k).comp (H : submodule R L).subtype ⟨x, hx⟩ = 0,
  rw linear_map.commute_pow_left_of_commute hfg k,
  have h := iterate_to_endomorphism_mem_lower_central_series R H H y ⟨x, hx⟩ k,
  rw [hk, lie_submodule.mem_bot] at h,
  simp only [submodule.subtype_apply, function.comp_app, linear_map.pow_apply, linear_map.coe_comp,
    submodule.coe_eq_zero],
  exact h,
end

lemma le_zero_root_subalgebra : H ≤ zero_root_subalgebra R L H :=
begin
  rw [← lie_subalgebra.coe_submodule_le_coe_submodule, ← H.coe_to_lie_submodule,
    coe_zero_root_subalgebra, lie_submodule.coe_submodule_le_coe_submodule],
  exact to_lie_submodule_le_root_space_zero R L H,
end

@[simp] lemma zero_root_subalgebra_normalizer_eq_self :
  (zero_root_subalgebra R L H).normalizer = zero_root_subalgebra R L H :=
begin
  refine le_antisymm _ (lie_subalgebra.le_normalizer _),
  intros x hx,
  rw lie_subalgebra.mem_normalizer_iff at hx,
  rw mem_zero_root_subalgebra,
  rintros ⟨y, hy⟩,
  specialize hx y (le_zero_root_subalgebra R L H hy),
  rw mem_zero_root_subalgebra at hx,
  obtain ⟨k, hk⟩ := hx ⟨y, hy⟩,
  rw [← lie_skew, linear_map.map_neg, neg_eq_zero] at hk,
  use k + 1,
  rw [linear_map.iterate_succ, linear_map.coe_comp, function.comp_app, to_endomorphism_apply_apply,
    lie_subalgebra.coe_bracket_of_module, submodule.coe_mk, hk],
end

/-- In finite dimensions over a field (and possibly more generally) Engel's theorem shows that
the converse of this is also true, i.e.,
`zero_root_subalgebra R L H = H ↔ lie_subalgebra.is_cartan_subalgebra H`. -/
lemma zero_root_subalgebra_is_cartan_of_eq (h : zero_root_subalgebra R L H = H) :
  lie_subalgebra.is_cartan_subalgebra H :=
{ nilpotent        := infer_instance,
  self_normalizing := by { rw ← h, exact zero_root_subalgebra_normalizer_eq_self R L H, } }

end lie_algebra

namespace lie_module

open lie_algebra

variables {R L H}

/-- A priori, weight spaces are Lie submodules over the Lie subalgebra `H` used to define them.
However they are naturally Lie submodules over the (in general larger) Lie subalgebra
`zero_root_subalgebra R L H`. Even though it is often the case that
`zero_root_subalgebra R L H = H`, it is likely to be useful to have the flexibility not to have
to invoke this equality (as well as to work more generally). -/
def weight_space' (χ : H → R) : lie_submodule R (zero_root_subalgebra R L H) M :=
{ lie_mem := λ x m hm, by
  { have hx : (x : L) ∈ root_space H 0,
    { rw [← lie_submodule.mem_coe_submodule, ← coe_zero_root_subalgebra], exact x.property, },
    rw ← zero_add χ,
    exact lie_mem_weight_space_of_mem_weight_space hx hm, },
  .. (weight_space M χ : submodule R M) }

@[simp] lemma coe_weight_space' (χ : H → R) :
  (weight_space' M χ : submodule R M) = weight_space M χ :=
rfl

end lie_module

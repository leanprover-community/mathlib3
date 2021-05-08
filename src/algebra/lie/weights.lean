/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.lie.nilpotent
import algebra.lie.tensor_product
import algebra.lie.character
import linear_algebra.eigenspace

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
  * `lie_module.weight`
  * `lie_algebra.root_space`
  * `lie_algebra.root`

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

@[simp] lemma mem_pre_weight_space (χ : L → R) (m : M) :
  m ∈ pre_weight_space M χ ↔ ∀ x, ∃ (k : ℕ), ((to_endomorphism R L M x - (χ x) • 1)^k) m = 0 :=
by simp [pre_weight_space, -linear_map.pow_apply]

/-- See also `bourbaki1975b` Chapter VII §1.1, Proposition 2 (ii). -/
private lemma weight_vector_multiplication (M₁ : Type w₁) (M₂ : Type w₂) (M₃ : Type w₃)
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
  have h_comm_square : F.comp ↑g = (g : M₁ ⊗[R] M₂ →ₗ[R] M₃).comp (f₁ + f₂),
  { ext m₁ m₂, simp only [← g.map_lie x (m₁ ⊗ₜ m₂), add_smul, tensor_product.sub_tmul,
      tensor_product.tmul_sub, tensor_product.smul_tmul, lie_tmul_right, tensor_product.tmul_smul,
      to_endomorphism_apply_apply, tensor_product.mk_apply, lie_module_hom.map_smul,
      linear_map.one_apply, lie_module_hom.coe_to_linear_map, linear_map.compr₂_apply, pi.add_apply,
      linear_map.smul_apply, function.comp_app, linear_map.coe_comp, linear_map.rtensor_tmul,
      lie_module_hom.map_add, linear_map.add_apply, lie_module_hom.map_sub, linear_map.sub_apply,
      linear_map.ltensor_tmul], abel, },
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
  { ext m₁ m₂,
    simp only [smul_comm (χ₁ x) (χ₂ x), linear_map.rtensor_smul, to_endomorphism_apply_apply,
      tensor_product.mk_apply, linear_map.mul_apply, linear_map.one_apply, linear_map.ltensor_sub,
      linear_map.compr₂_apply, linear_map.smul_apply, linear_map.ltensor_smul,
      linear_map.rtensor_tmul, linear_map.map_sub, linear_map.map_smul, linear_map.rtensor_sub,
      linear_map.sub_apply, linear_map.ltensor_tmul], },
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

variables {M}

lemma lie_mem_pre_weight_space_of_mem_pre_weight_space {χ₁ χ₂ : L → R} {x : L} {m : M}
  (hx : x ∈ pre_weight_space L χ₁) (hm : m ∈ pre_weight_space M χ₂) :
  ⁅x, m⁆ ∈ pre_weight_space M (χ₁ + χ₂) :=
begin
  apply weight_vector_multiplication L M M (to_module_hom R L M) χ₁ χ₂,
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

@[simp] lemma coe_weight_space_of_top [lie_algebra.is_nilpotent R L] (χ : L → R) :
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
structure weight :=
(to_character : lie_character R H)
(weight_space_ne_bot : weight_space M to_character ≠ ⊥)

instance : has_coe (weight H M) (module.dual R H) := ⟨λ w, (w.to_character : H →ₗ[R] R)⟩

/-- see Note [function coercion] -/
instance : has_coe_to_fun (weight H M) := ⟨_, weight.to_character⟩

/-- The zero character is a weight for a non-trivial nilpotent Lie module. -/
instance [nontrivial M] [lie_algebra.is_nilpotent R L] [is_nilpotent R L M] :
  inhabited $ weight (⊤ : lie_subalgebra R L) M :=
⟨{ to_character        := 0,
   weight_space_ne_bot := by
   { rw [lie_hom.coe_zero, zero_weight_space_eq_top_of_nilpotent], exact top_ne_bot, }, }⟩

end lie_module

namespace lie_algebra

/-- Given a nilpotent Lie subalgebra `H ⊆ L`, the root space of a map `χ : H → R` is the weight
space of `L` regarded as a module of `H` via the adjoint action. -/
abbreviation root_space (χ : H → R) : lie_submodule R H L := lie_module.weight_space L χ

@[simp] lemma zero_root_space_eq_top_of_nilpotent [h : is_nilpotent R L] :
  root_space (⊤ : lie_subalgebra R L) 0 = ⊤ :=
lie_module.zero_weight_space_eq_top_of_nilpotent L

/-- A root of a Lie algebra `L` with respect to a nilpotent subalgebra `H ⊆ L` is a weight of `L`,
regarded as a module of `H` via the adjoint action. -/
abbreviation root := lie_module.weight H L

end lie_algebra

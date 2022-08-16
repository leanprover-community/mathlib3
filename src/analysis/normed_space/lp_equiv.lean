/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import analysis.normed_space.lp_space
import analysis.normed_space.pi_Lp
import topology.continuous_function.bounded

/-!
# Equivalences among $$L^p$$ spaces

In this file we collect a variety of equivalences among various $$L^p$$ spaces.  In particular,
when `α` is a `fintype`, given `E : α → Type u` and `p : ℝ≥0∞`, there is a natural linear isometric
equivalence `lp_pi_Lpₗᵢ : lp E p ≃ₗᵢ pi_Lp p E`.

We keep this as a separate file so that the various $$L^p$$ space files don't import the others.

## TODO

* Equivalence between `lp` and `measure_theory.Lp`, for `f : α → E` (i.e., functions rather than
  pi-types) and the counting measure on `α`

-/

open_locale ennreal

section lp_pi_Lp

variables {α : Type*} {E : α → Type*} [Π i, normed_add_comm_group (E i)] (p : ℝ≥0∞)
/-- When `α` is `finite`, every `f : pre_lp E p` satisfies `mem_ℓp f p`. -/
lemma mem_ℓp.all [finite α] (f : Π i, E i) : mem_ℓp f p :=
begin
  rcases p.trichotomy with (rfl | rfl | h),
  { exact mem_ℓp_zero_iff.mpr {i : α | f i ≠ 0}.to_finite, },
  { exact mem_ℓp_infty_iff.mpr (set.finite.bdd_above (set.range (λ (i : α), ∥f i∥)).to_finite) },
  { casesI nonempty_fintype α, exact mem_ℓp_gen ⟨finset.univ.sum _, has_sum_fintype _⟩ }
end

variables [fintype α]

/-- The canonical `equiv` between `lp E p ≃ pi_Lp p E` when `E : α → Type u` with `[fintype α]`. -/
def equiv.lp_pi_Lp : lp E p ≃ pi_Lp p E :=
{ to_fun := λ f, f,
  inv_fun := λ f, ⟨f, mem_ℓp.all p f⟩,
  left_inv := λ f, lp.ext $ funext $ λ x, rfl,
  right_inv := λ f, funext $ λ x, rfl }

lemma equiv_lp_pi_Lp_norm (f : lp E p) : ∥equiv.lp_pi_Lp p f∥ = ∥f∥ :=
begin
  unfreezingI { rcases p.trichotomy with (rfl | rfl | h) },
  { rw [pi_Lp.norm_eq_card, lp.norm_eq_card_dsupport], refl },
  { rw [pi_Lp.norm_eq_csupr, lp.norm_eq_csupr], refl },
  { rw [pi_Lp.norm_eq_sum h, lp.norm_eq_tsum_rpow h, tsum_fintype], refl },
end

/-- The canonical `add_equiv` between `lp E p` and `pi_Lp p E` when `E : α → Type u` with
`[fintype α]` and `[fact (1 ≤ p)]`. -/
def add_equiv.lp_pi_Lp [fact (1 ≤ p)] : lp E p ≃+ pi_Lp p E :=
{ map_add' := λ f g, rfl,
  .. (equiv.lp_pi_Lp p) }

section equivₗᵢ
variables {𝕜 : Type*} [nontrivially_normed_field 𝕜] [Π i, normed_space 𝕜 (E i)]

/-- The canonical `add_equiv` between `lp E p` and `pi_Lp p E` when `E : α → Type u` with
`[fintype α]` and `[fact (1 ≤ p)]`. -/
noncomputable def lp_pi_Lpₗᵢ [fact (1 ≤ p)] : lp E p ≃ₗᵢ[𝕜] pi_Lp p E :=
{ map_smul' := λ k f, rfl,
  norm_map' := equiv_lp_pi_Lp_norm p,
  .. (add_equiv.lp_pi_Lp p) }

end equivₗᵢ

end lp_pi_Lp

section lp_bcf

open_locale bounded_continuous_function
open bounded_continuous_function

variables (α E 𝕜 : Type*) [topological_space α] [discrete_topology α]

/-- The canonical map between `lp (λ (_ : α), E) ∞` and `α →ᵇ E` as an `add_equiv`. -/
noncomputable def add_equiv.lp_bcf [normed_add_comm_group E] :
  lp (λ (_ : α), E) ∞ ≃+ (α →ᵇ E) :=
{ to_fun := λ f, of_normed_add_comm_group_discrete f (∥f∥) $ le_csupr (mem_ℓp_infty_iff.mp f.prop),
  inv_fun := λ f, ⟨f, f.bdd_above_range_norm_comp⟩,
  left_inv := λ f, lp.ext rfl,
  right_inv := λ f, ext $ λ x, rfl,
  map_add' := λ f g, ext $ λ x, rfl }

/-- The canonical map between `lp (λ (_ : α), E) ∞` and `α →ᵇ E` as a `linear_isometry_equiv`. -/
noncomputable def equivₗᵢ.lp_bcf [normed_add_comm_group E] [nontrivially_normed_field 𝕜]
  [normed_space 𝕜 E] : lp (λ (_ : α), E) ∞ ≃ₗᵢ[𝕜] (α →ᵇ E) :=
{ map_smul' := λ k f, rfl,
  norm_map' := λ f, by { simp only [norm_eq_supr_norm, lp.norm_eq_csupr], refl },
  .. add_equiv.lp_bcf α E }

/-- The canonical map between `lp (λ (_ : α), E) ∞` and `α →ᵇ E` as a `ring_equiv`. -/
noncomputable def ring_equiv.lp_bcf [non_unital_normed_ring E] :
  lp (λ (_ : α), E) ∞ ≃+* (α →ᵇ E) :=
{ map_mul' := λ f g, ext $ λ x, rfl, .. add_equiv.lp_bcf α E }

-- the `norm_one_class E` shouldn't really be necessary, but currently it is for
-- `one_mem_ℓp_infty` to get the `ring` instance on `lp`.
/-- The canonical map between `lp (λ (_ : α), E) ∞` and `α →ᵇ E` as an `alg_equiv`. -/
noncomputable def alg_equiv.lp_bcf [normed_ring E] [norm_one_class E] [nontrivially_normed_field 𝕜]
  [normed_algebra 𝕜 E] :
  lp (λ (_ : α), E) ∞ ≃ₐ[𝕜] (α →ᵇ E) :=
{ commutes' := λ k, rfl, .. ring_equiv.lp_bcf α E }

end lp_bcf

/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import analysis.normed_space.lp_space
import analysis.normed_space.pi_Lp
import topology.continuous_function.bounded

/-!
# Equivalences among $L^p$ spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we collect a variety of equivalences among various $L^p$ spaces.  In particular,
when `α` is a `fintype`, given `E : α → Type u` and `p : ℝ≥0∞`, there is a natural linear isometric
equivalence `lp_pi_Lpₗᵢ : lp E p ≃ₗᵢ pi_Lp p E`. In addition, when `α` is a discrete topological
space, the bounded continuous functions `α →ᵇ β` correspond exactly to `lp (λ _, β) ∞`. Here there
can be more structure, including ring and algebra structures, and we implement these equivalences
accordingly as well.

We keep this as a separate file so that the various $L^p$ space files don't import the others.

Recall that `pi_Lp` is just a type synonym for `Π i, E i` but given a different metric and norm
structure, although the topological, uniform and bornological structures coincide definitionally.
These structures are only defined on `pi_Lp` for `fintype α`, so there are no issues of convergence
to consider.

While `pre_lp` is also a type synonym for `Π i, E i`, it allows for infinite index types. On this
type there is a predicate `mem_ℓp` which says that the relevant `p`-norm is finite and `lp E p` is
the subtype of `pre_lp` satisfying `mem_ℓp`.

## TODO

* Equivalence between `lp` and `measure_theory.Lp`, for `f : α → E` (i.e., functions rather than
  pi-types) and the counting measure on `α`

-/

open_locale ennreal

section lp_pi_Lp

variables {α : Type*} {E : α → Type*} [Π i, normed_add_comm_group (E i)] {p : ℝ≥0∞}

/-- When `α` is `finite`, every `f : pre_lp E p` satisfies `mem_ℓp f p`. -/
lemma mem_ℓp.all [finite α] (f : Π i, E i) : mem_ℓp f p :=
begin
  rcases p.trichotomy with (rfl | rfl | h),
  { exact mem_ℓp_zero_iff.mpr {i : α | f i ≠ 0}.to_finite, },
  { exact mem_ℓp_infty_iff.mpr (set.finite.bdd_above (set.range (λ (i : α), ‖f i‖)).to_finite) },
  { casesI nonempty_fintype α, exact mem_ℓp_gen ⟨finset.univ.sum _, has_sum_fintype _⟩ }
end

variables [fintype α]

/-- The canonical `equiv` between `lp E p ≃ pi_Lp p E` when `E : α → Type u` with `[fintype α]`. -/
def equiv.lp_pi_Lp : lp E p ≃ pi_Lp p E :=
{ to_fun := λ f, f,
  inv_fun := λ f, ⟨f, mem_ℓp.all f⟩,
  left_inv := λ f, lp.ext $ funext $ λ x, rfl,
  right_inv := λ f, funext $ λ x, rfl }

lemma coe_equiv_lp_pi_Lp (f : lp E p) : equiv.lp_pi_Lp f = f := rfl
lemma coe_equiv_lp_pi_Lp_symm (f : pi_Lp p E) : (equiv.lp_pi_Lp.symm f : Π i, E i) = f :=  rfl

lemma equiv_lp_pi_Lp_norm (f : lp E p) : ‖equiv.lp_pi_Lp f‖ = ‖f‖ :=
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
  .. equiv.lp_pi_Lp }

lemma coe_add_equiv_lp_pi_Lp [fact (1 ≤ p)] (f : lp E p) :
  add_equiv.lp_pi_Lp f = f := rfl
lemma coe_add_equiv_lp_pi_Lp_symm [fact (1 ≤ p)] (f : pi_Lp p E) :
  (add_equiv.lp_pi_Lp.symm f : Π i, E i) = f :=  rfl

section equivₗᵢ
variables (𝕜 : Type*) [nontrivially_normed_field 𝕜] [Π i, normed_space 𝕜 (E i)]

/-- The canonical `linear_isometry_equiv` between `lp E p` and `pi_Lp p E` when `E : α → Type u`
with `[fintype α]` and `[fact (1 ≤ p)]`. -/
noncomputable def lp_pi_Lpₗᵢ [fact (1 ≤ p)] : lp E p ≃ₗᵢ[𝕜] pi_Lp p E :=
{ map_smul' := λ k f, rfl,
  norm_map' := equiv_lp_pi_Lp_norm,
  .. add_equiv.lp_pi_Lp }

variables {𝕜}

lemma coe_lp_pi_Lpₗᵢ [fact (1 ≤ p)] (f : lp E p) :
  lp_pi_Lpₗᵢ 𝕜 f = f := rfl
lemma coe_lp_pi_Lpₗᵢ_symm [fact (1 ≤ p)] (f : pi_Lp p E) :
  ((lp_pi_Lpₗᵢ 𝕜).symm f : Π i, E i) = f :=  rfl

end equivₗᵢ

end lp_pi_Lp

section lp_bcf

open_locale bounded_continuous_function
open bounded_continuous_function

-- note: `R` and `A` are explicit because otherwise Lean has elaboration problems
variables {α E : Type*} (R A 𝕜 : Type*) [topological_space α] [discrete_topology α]
variables [normed_ring A] [norm_one_class A] [nontrivially_normed_field 𝕜] [normed_algebra 𝕜 A]
variables [normed_add_comm_group E] [normed_space 𝕜 E] [non_unital_normed_ring R]


section normed_add_comm_group

/-- The canonical map between `lp (λ (_ : α), E) ∞` and `α →ᵇ E` as an `add_equiv`. -/
noncomputable def add_equiv.lp_bcf :
  lp (λ (_ : α), E) ∞ ≃+ (α →ᵇ E) :=
{ to_fun := λ f, of_normed_add_comm_group_discrete f (‖f‖) $ le_csupr (mem_ℓp_infty_iff.mp f.prop),
  inv_fun := λ f, ⟨f, f.bdd_above_range_norm_comp⟩,
  left_inv := λ f, lp.ext rfl,
  right_inv := λ f, ext $ λ x, rfl,
  map_add' := λ f g, ext $ λ x, rfl }

lemma coe_add_equiv_lp_bcf (f : lp (λ (_ : α), E) ∞) :
  (add_equiv.lp_bcf f : α → E) = f := rfl
lemma coe_add_equiv_lp_bcf_symm (f : α →ᵇ E) : (add_equiv.lp_bcf.symm f : α → E) = f := rfl

/-- The canonical map between `lp (λ (_ : α), E) ∞` and `α →ᵇ E` as a `linear_isometry_equiv`. -/
noncomputable def lp_bcfₗᵢ : lp (λ (_ : α), E) ∞ ≃ₗᵢ[𝕜] (α →ᵇ E) :=
{ map_smul' := λ k f, rfl,
  norm_map' := λ f, by { simp only [norm_eq_supr_norm, lp.norm_eq_csupr], refl },
  .. add_equiv.lp_bcf }

variables {𝕜}

lemma coe_lp_bcfₗᵢ (f : lp (λ (_ : α), E) ∞) : (lp_bcfₗᵢ 𝕜 f : α → E) = f := rfl
lemma coe_lp_bcfₗᵢ_symm (f : α →ᵇ E) : ((lp_bcfₗᵢ 𝕜).symm f : α → E) = f :=  rfl

end normed_add_comm_group

section ring_algebra

/-- The canonical map between `lp (λ (_ : α), R) ∞` and `α →ᵇ R` as a `ring_equiv`. -/
noncomputable def ring_equiv.lp_bcf : lp (λ (_ : α), R) ∞ ≃+* (α →ᵇ R) :=
{ map_mul' := λ f g, ext $ λ x, rfl, .. @add_equiv.lp_bcf _ R _ _ _ }

variables {R}
lemma coe_ring_equiv_lp_bcf (f : lp (λ (_ : α), R) ∞) :
  (ring_equiv.lp_bcf R f : α → R) = f := rfl
lemma coe_ring_equiv_lp_bcf_symm (f : α →ᵇ R) :
  ((ring_equiv.lp_bcf R).symm f : α → R) = f := rfl

variables (α) -- even `α` needs to be explicit here for elaboration

-- the `norm_one_class A` shouldn't really be necessary, but currently it is for
-- `one_mem_ℓp_infty` to get the `ring` instance on `lp`.
/-- The canonical map between `lp (λ (_ : α), A) ∞` and `α →ᵇ A` as an `alg_equiv`. -/
noncomputable def alg_equiv.lp_bcf : lp (λ (_ : α), A) ∞ ≃ₐ[𝕜] (α →ᵇ A) :=
{ commutes' := λ k, rfl, .. ring_equiv.lp_bcf A }

variables {α A 𝕜}
lemma coe_alg_equiv_lp_bcf (f : lp (λ (_ : α), A) ∞) :
  (alg_equiv.lp_bcf α A 𝕜 f : α → A) = f := rfl
lemma coe_alg_equiv_lp_bcf_symm (f : α →ᵇ A) :
  ((alg_equiv.lp_bcf α A 𝕜).symm f : α → A) = f := rfl

end ring_algebra

end lp_bcf

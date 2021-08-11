/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä and Heather Macbeth
-/
import tactic
import topology.algebra.weak_dual_topology
import analysis.normed_space.dual
import analysis.normed_space.operator_norm

noncomputable theory
open filter
open_locale topological_space

section weak_star_topology_for_duals_of_normed_spaces

/-!
### Weak star topology on duals of normed spaces
In this section, we prove properties about the weak-* topology on duals of normed spaces.
We prove in particular that the canonical mapping `dual 𝕜 E → weak_dual 𝕜 E` is continuous,
i.e., that the weak-* topology is coarser (not necessarily strictly) than the topology given
by the dual-norm (i.e. the operator-norm).
-/

open normed_space

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
variables {E : Type*} [normed_group E] [normed_space 𝕜 E]

/-- For normed spaces `E`, there is a canonical map `dual 𝕜 E ≃ₗ[𝕜] weak_dual 𝕜 E`. -/
def normed_space.dual.to_weak_dual : dual 𝕜 E ≃ₗ[𝕜] weak_dual 𝕜 E :=
linear_equiv.refl 𝕜 (E →L[𝕜] 𝕜)

/-- For normed spaces `E`, there is a canonical map `weak_dual 𝕜 E → dual 𝕜 E`. -/
def weak_dual.to_original_dual : weak_dual 𝕜 E → dual 𝕜 E := id

@[simp] lemma weak_dual.coe_to_fun_eq_original_coe_to_fun (x' : dual 𝕜 E) :
  (x'.to_weak_dual : E → 𝕜) = x' := rfl

lemma to_weak_dual_injective :
  function.injective (λ (x' : dual 𝕜 E), x'.to_weak_dual) := λ _ _ , id

lemma to_original_dual_injective :
  function.injective (λ (x' : weak_dual 𝕜 E), x'.to_original_dual) := λ _ _ , id

-- Q: Are the following simp-lemmas useful?

@[simp] lemma to_weak_dual_to_original_dual (x' : weak_dual 𝕜 E) :
  (x'.to_original_dual).to_weak_dual = x' := rfl

@[simp] lemma to_original_dual_to_weak_dual (x' : dual 𝕜 E) :
  (x'.to_weak_dual).to_original_dual = x' := rfl

@[simp] lemma to_weak_dual_inj_iff (x' y' : dual 𝕜 E) :
  x'.to_weak_dual = y'.to_weak_dual ↔ x' = y' := iff.rfl

@[simp] lemma to_original_dual_inj_iff (x' y' : weak_dual 𝕜 E) :
  x'.to_original_dual = y'.to_original_dual ↔ x' = y' := iff.rfl

/-- The linear equivalence between `dual 𝕜 E` and `weak_dual 𝕜 E` for a normed space `E`. -/
def linequiv_to_weak_dual : dual 𝕜 E ≃ₗ[𝕜] weak_dual 𝕜 E :=
{ to_fun := (λ (x' : dual 𝕜 E), x'.to_weak_dual),
  map_add' := by { intros x' y', refl, },
  map_smul' := by { intros c x', refl, },
  inv_fun := (λ (x' : weak_dual 𝕜 E), x'.to_original_dual),
  left_inv := to_original_dual_to_weak_dual,
  right_inv := to_weak_dual_to_original_dual, }

@[simp]
lemma linequiv_to_weak_dual_apply (x' : dual 𝕜 E) :
  linequiv_to_weak_dual x' = x'.to_weak_dual := rfl

@[simp]
lemma equiv_to_weak_dual_symm_apply (x' : weak_dual 𝕜 E) :
  linequiv_to_weak_dual.symm x' = x'.to_original_dual := rfl

-- TODO: The only reason to separate this from `evaluate_dual_at` is to get access to the proofs
-- of `map_add'` and `map_smul'`. Surely there is a syntax to avoid this unnecessary intermediate
-- step... right?
def normed_space.evaluate_dual_at' (z : E) : (dual 𝕜 E) →ₗ[𝕜] 𝕜 :=
{ to_fun := (λ (x' : dual 𝕜 E), x' z),
  map_add' := by simp only [forall_const, eq_self_iff_true, continuous_linear_map.add_apply],
  map_smul' := by simp only [forall_const, eq_self_iff_true, pi.smul_apply,
                             continuous_linear_map.coe_smul'], }

/-
TODO: Is there a way to make the following dot notation work?
(And the same for `evaluate_dual_at`?)

variables (w : E)
#check w
#check normed_space.evaluate_dual_at' w
#check w.evaluate_dual_at' -- fails
-/

def normed_space.evaluate_dual_at (z : E) : (dual 𝕜 E) →L[𝕜] 𝕜 :=
{ to_fun := (λ (x' : dual 𝕜 E), x' z),
  map_add' := (normed_space.evaluate_dual_at' z).map_add,
  map_smul' := (normed_space.evaluate_dual_at' z).map_smul,
  cont := begin
    apply @continuous_of_linear_of_bound 𝕜 (dual 𝕜 E) 𝕜 _ infer_instance _ _ _
      (λ (x' : dual 𝕜 E), x' z) (normed_space.evaluate_dual_at' z).map_add
      (normed_space.evaluate_dual_at' z).map_smul (∥ z ∥),
    intros x',
    have key := continuous_linear_map.le_op_norm x' z,
    rwa mul_comm at key,
  end, }

theorem to_weak_dual_continuous :
  continuous (λ (x' : dual 𝕜 E), x'.to_weak_dual) :=
begin
  apply continuous_induced_rng,
  apply continuous_pi_iff.mpr,
  intros z,
  exact (inclusion_in_double_dual 𝕜 E z).continuous,
end

def normed_space.dual.continuous_linear_map_to_weak_dual : dual 𝕜 E →L[𝕜] weak_dual 𝕜 E :=
{ to_fun := (λ (x' : dual 𝕜 E), x'.to_weak_dual),
  map_add' := (@linequiv_to_weak_dual 𝕜 _ E _ _).map_add',
  map_smul' := (@linequiv_to_weak_dual 𝕜 _ E _ _).map_smul',
  cont := to_weak_dual_continuous, }

-- This is a relatively straightforward statement of the fact that the weak-star topology is
-- coarser than the dual-norm topology, without abusing definitional equality.
/-- The weak-star topology is coarser than the dual-norm topology: all weak-star open sets are
    norm-topology open. -/
lemma open_set_of_weak_dual_open_set (s : set (dual 𝕜 E))
  (s_weak_dual_open : is_open (linequiv_to_weak_dual '' s)) : is_open s :=
begin
  have eq : (linequiv_to_weak_dual)⁻¹' (linequiv_to_weak_dual '' s) = s,
  { ext x',
    simp only [set.mem_preimage, linequiv_to_weak_dual_apply, set.mem_image, to_weak_dual_inj_iff,
               exists_eq_right], },
  rw ←eq,
  apply continuous_def.mp to_weak_dual_continuous _ s_weak_dual_open,
end

-- TODO: The proof below may be abusing definitional equality... And it looks like it needs golf.
private lemma linequiv_to_weak_dual_image (s : set (dual 𝕜 E)) :
  (linequiv_to_weak_dual '' s) = s :=
begin
  ext x',
  split,
  { intros hx',
    rcases hx' with ⟨y', hy', h_eq⟩,
    rwa ←h_eq, },
  { intros hx',
    use x',
    exact ⟨ hx', by refl ⟩, },
end

-- TODO: The proof and even the statement below may be abusing definitional equality...
-- But I don't think this can be stated using `≤` on topologies without such abuse.
/-- The weak-star topology is coarser than the dual-norm topology. -/
theorem dual_norm_topology_le_weak_dual_topology :
  (by apply_instance : topological_space (dual 𝕜 E)) ≤ weak_dual.topology 𝕜 E :=
begin
  intros U hU,
  apply open_set_of_weak_dual_open_set U,
  rwa linequiv_to_weak_dual_image,
end

end weak_star_topology_for_duals_of_normed_spaces

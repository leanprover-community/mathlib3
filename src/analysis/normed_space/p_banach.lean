import analysis.normed_space.lp_space
import analysis.normed_space.banach
import analysis.mean_inequalities_pow

/-!
# p-Banach spaces
A `p`-Banach space is just like an ordinary Banach space,
except that the axiom `∥c • v∥ = ∥c∥ * ∥v∥` is replaced by `∥c • v∥ = ∥c∥^p * ∥v∥`.
In other words, a `p`-Banach space is a complete topological vector space
whose topology is induced by a `p`-norm.
In this file, we define `p`-normed spaces, called `normed_space'`,
and we prove that every `p`-normed space is also `p'`-normed, for `0 < p' ≤ p`.
-/

noncomputable theory

open_locale nnreal

section

structure has_p_norm (V : Type*) (p : ℝ)
  [add_comm_group V] [module ℝ V] [uniform_space V] extends has_norm V :=
(norm_smul : ∀ (α : ℝ) (v : V), ∥α • v∥ = |α|^p • ∥v∥)
(triangle : ∀ (v w : V), ∥v+w∥ ≤ ∥v∥ + ∥w∥)
(uniformity : uniformity V = ⨅ (ε : ℝ) (H : ε > 0),
  filter.principal {p : V × V | ∥p.fst - p.snd∥ < ε})

variables (V : Type*) (p : ℝ) [add_comm_group V] [module ℝ V] [uniform_space V]

def has_p_norm.semi_normed_group [fact (0 < p)] (h : has_p_norm V p) : seminormed_add_comm_group V :=
{ to_uniform_space := by apply_instance,
  uniformity_dist := h.uniformity,
  to_add_comm_group := by apply_instance,
  .. @seminormed_add_comm_group.of_core V _ h.to_has_norm $
    have hp0 : p ≠ 0 := (fact.out _ : 0 < p).ne',
    { norm_zero := by simpa only [zero_smul, abs_zero, real.zero_rpow hp0] using h.norm_smul 0 0,
      triangle := h.triangle,
      norm_neg := λ v, by simpa only [neg_smul, one_smul, abs_neg, abs_one, real.one_rpow]
                            using h.norm_smul (-1) v } }

structure p_banach : Prop :=
(exists_p_norm : nonempty (has_p_norm V p))
[topological_add_group : topological_add_group V]
[continuous_smul : has_continuous_smul ℝ V]
[complete : complete_space V]
[separated : separated_space V]

end

section lp

open lp ennreal nnreal
open_locale nnreal ennreal

/- Although we restrict to `p ≤ 1`, it would be better to work with `p : ℝ≥0∞` rather than `p : ℝ≥0` because there is no coercion from `{x : ℝ≥0∞ // x ≤ 1}` to `{x : ℝ≥0 // x ≤ 1}`, for which the `simp` lemma `one_le_coe_iff` is needed. -/
variables {p : ℝ≥0} --[hp : fact (p ≤ 1)]




@[reducible]
def E : ℕ → Type* := λ n, ℝ
/-First, three basic instances to access `lp E p`-/
instance normed_add_comm_group_En : Π n : ℕ, normed_add_comm_group (E n) := infer_instance
instance normed_space_En : Π n : ℕ, normed_space ℝ (E n) := infer_instance
instance complete_space_En : Π n : ℕ, complete_space (E n) := infer_instance


/-Then, one instance to make the following lemmas type-check; and five lemmas corresponding to the relevant fields of `p_banach`-/

-- instance : metric_space (lp E p) := sorry --When `1 ≤ p`, this is a consequence of the ℓ^p(E) being a `normed_group`, but this is false when `p ≤ 1`.

-- lemma top_add_group_p_le_one : topological_add_group (lp E p) := sorry--would follow from a `normed_group` (→ `metric_space`) instance on `lp E p`

-- lemma cont_smul_p_le_one : has_continuous_smul ℝ (lp E p) := sorry

-- lemma complete_p_le_one : complete_space (lp E p ) := sorry

-- lemma separated_p_le_one : separated_space (lp E p) := infer_instance --sorry--would follow from a `normed_group` (→ `metric_space`) instance on `lp E p`

section

local attribute [-instance] lp.has_norm lp.normed_add_comm_group

local attribute [instance] non_standard_norm_lp non_standard_normed_group_lp

lemma p_norm_lp : has_p_norm (lp E p) p :=
{ norm := λ x, ∥x∥,
  norm_smul := _,
  triangle := _,
  uniformity := rfl }

--the following theorem should really be a `def`
theorem lp_N_is_pBanach : p_banach (lp E p) p :=
{ exists_p_norm := ⟨p_norm_lp⟩,
  topological_add_group := by apply_instance,
  continuous_smul := _,
  complete := by apply_instance,
  separated := by apply_instance }

end

section

variables (F : Type*) [uniform_space F] [add_comm_group F] [module ℝ F] [i : p_banach F p]
variables (p) (p' : ℝ≥0) [fact (p' ≤ p)] [fact (0 < (p:ℝ))]

include p i

def exponentiate_norm.has_p_norm : has_p_norm F p' :=
{ norm_smul := _,
  triangle := begin
    letI : seminormed_add_comm_group F :=
      (exponentiate_norm.seminormed_add_comm_group (sorry : 0 < p'/p) (sorry : p'/p ≤ 1) F
      (has_p_norm.semi_normed_group F p i.exists_p_norm.some)),
    exact norm_add_le
  end,
  uniformity := begin
    letI : seminormed_add_comm_group F :=
      (exponentiate_norm.seminormed_add_comm_group (sorry : 0 < p'/p) (sorry : p'/p ≤ 1) F
      (has_p_norm.semi_normed_group F p i.exists_p_norm.some)),
    exact pseudo_metric_space.uniformity_dist,
  end,
  .. (exponentiate_norm.seminormed_add_comm_group (sorry : 0 < p'/p) (sorry : p'/p ≤ 1) F
      (has_p_norm.semi_normed_group F p i.exists_p_norm.some)).to_has_norm }

def exponentiate_norm.p_banach : p_banach F p' :=
{ exists_p_norm := ⟨@exponentiate_norm.has_p_norm p F (by apply_instance) (by apply_instance)
    (by apply_instance) i p' (by apply_instance) (by apply_instance)⟩,
  topological_add_group := _,
  continuous_smul := _,
  complete := _,
  separated := begin
    letI : seminormed_add_comm_group F :=
      (exponentiate_norm.seminormed_add_comm_group (sorry : 0 < p'/p) (sorry : p'/p ≤ 1) F
      (has_p_norm.semi_normed_group F p i.exists_p_norm.some)),
    apply @metric_space.to_separated F,
  end }


end

-- begin
--   have := has_norm.norm,
--   rotate,
--   use lp E p,
--   apply_instance,
--   use this;
--   sorry,
-- end


end lp

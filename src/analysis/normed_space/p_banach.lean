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

variables {p : ℝ≥0} [hp : fact (p ≤ 1)]


/- We introduce the ℓ^q-space ℓ^q(T) for testing purposes.-/
variables {q q' : ℝ≥0∞} [fact (1 ≤ q)] {T : ℕ → Type*}
  [Π i, normed_add_comm_group (T i)]
  [Π i, normed_space ℝ (T i)]
  [Π i, complete_space (T i)]

example : uniform_space (lp T q) := infer_instance --needs 1≤ q, no completeness and no normed space structure

example : topological_add_group (lp T q) := infer_instance --needs 1≤ q, no completeness and no normed space structure

-- example : metric_space (lp T q) := infer_instance --needs 1≤ q, no completeness and no normed space structure

example : separated_space (lp T q) := infer_instance--needs 1≤ q, no completeness and no normed space structure

example : has_continuous_smul ℝ (lp T q) := infer_instance  --needs 1 ≤ q, no completeness and no normed space structure

example : complete_space (lp T q) := infer_instance --needs 1 ≤ q, and completeness of every (F n)
/-The true example-/


-- [add_comm_group V] [module ℝ V] [uniform_space V] extends has_norm V
@[derive [add_comm_group, module ℝ]]
def copy_normed_grp (E : Type*) (p : ℝ≥0∞) [add_comm_group E] [module ℝ E] [has_norm E] : Type* := E

def p_norm_on_copy (E : Type*) (p : ℝ≥0∞) [add_comm_group E] [module ℝ E] [has_norm E] : has_norm (copy_normed_grp E p) := { norm := λ x, ∥ (id x : E) ∥ ^ (p.to_real)}

instance (E : Type*) (p : ℝ≥0∞) [normed_add_comm_group E] [normed_space ℝ E] : uniform_space (copy_normed_grp E p) := (by apply_instance : uniform_space E)

def pBanach_on_copy (E : Type*) (p : ℝ≥0∞) [normed_add_comm_group E] [normed_space ℝ E] : has_p_norm (copy_normed_grp E p) p.to_real :=
{ norm_smul := _,
  triangle := _,
  uniformity := _,
  .. p_norm_on_copy E p }


@[reducible]
def E : ℕ → Type* := λ n, ℝ
/-First, three basic instances to access `lp E p`-/
instance normed_add_comm_group_En : Π n : ℕ, normed_add_comm_group (E n) := infer_instance
instance normed_space_En : Π n : ℕ, normed_space ℝ (E n) := infer_instance
instance complete_space_En : Π n : ℕ, complete_space (E n) := infer_instance


/-Then, one instance to make the following lemmas type-check; and five lemmas corresponding to the relevant fields of `p_banach`-/

instance : metric_space (lp E p) := sorry --When `1 ≤ p`, this is a consequence of the ℓ^p(E) being a `normed_group`, but this is false when `p ≤ 1`.

lemma top_add_group_p_le_one : topological_add_group (lp E p) := sorry--would follow from a `normed_group` (→ `metric_space`) instance on `lp E p`

lemma cont_smul_p_le_one : has_continuous_smul ℝ (lp E p) := sorry

lemma complete_p_le_one : complete_space (lp E p ) := sorry

lemma separated_p_le_one : separated_space (lp E p) := infer_instance --sorry--would follow from a `normed_group` (→ `metric_space`) instance on `lp E p`

lemma p_norm_lp : has_p_norm (lp E p) p :=
begin
  have := has_norm.norm,
  rotate,
  use lp E p,
  apply_instance,
  use this;
  sorry,
end

--the following theorem should really be a `def`
theorem lp_N_is_pBanach : p_banach (lp E p) p :=
{ exists_p_norm := ⟨p_norm_lp⟩,
  topological_add_group := top_add_group_p_le_one,
  continuous_smul := cont_smul_p_le_one,
  complete := complete_p_le_one,
  separated := separated_p_le_one}

end lp

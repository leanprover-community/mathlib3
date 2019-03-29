/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow

The space of bounded linear maps

Define the set of bounded linear maps between normed spaces and show basic facts about it. In
particular

(*) define a set L(E,F) of bounded linear maps between k normed spaces,
(*) show that L(E,F) is a vector subspace of E → F,
(*) define the 'operator norm' on L(E,F) and show that it induces the structure of a normed space
    on L(E,F).
-/
import algebra.module
import analysis.normed_space.bounded_linear_maps
import topology.metric_space.lipschitz

variable  {k : Type*}
variables {E : Type*} {F : Type*} {G : Type*}

section op_norm

variable  [normed_field k]
variables [normed_space k E] [normed_space k F] [normed_space k G]

open bounded_linear_map

variables (c : k) {x : E}
variables (f g : bounded_linear_map k E F) (h : bounded_linear_map k F G)

noncomputable def op_norm  := real.Inf { c | c ≥ 0 ∧ ∀ x, ∥f x∥ ≤ c * ∥x∥ }

noncomputable instance : has_norm (bounded_linear_map k E F) := ⟨op_norm⟩

-- so that invocations of real.Inf_le make sense: the set of
-- bounds is nonempty and bounded below.
lemma bounds_nonempty {f : bounded_linear_map k E F} :
  ∃ c, c ∈ { c | c ≥ 0 ∧ ∀ x, ∥f x∥ ≤ c * ∥x∥ } :=
  let ⟨M, hMp, hMb⟩ := f.has_pos_bound in ⟨M, le_of_lt hMp, hMb⟩
lemma bounds_bdd_below {f : bounded_linear_map k E F} :
  bdd_below { c | c ≥ 0 ∧ ∀ x, ∥f x∥ ≤ c * ∥x∥ } :=
  ⟨0, λ _ ⟨hn, _⟩, hn⟩

lemma op_norm_nonneg : ∥f∥ ≥ 0 :=
  real.lb_le_Inf _ bounds_nonempty (λ _ ⟨hx, _⟩, hx)

lemma le_op_norm : ∥f x∥ ≤ ∥f∥ * ∥x∥ :=
  or.elim (eq_or_lt_of_le (norm_nonneg x))
  (λ heq, by rw [←heq, mul_zero,
    (norm_eq_zero _).1 heq.symm, map_zero, norm_zero])
  (λ hlt, le_mul_of_div_le hlt
    ((real.le_Inf _ bounds_nonempty bounds_bdd_below).2
    (λ c ⟨_, hc⟩, div_le_of_le_mul hlt (by rw mul_comm; exact hc _))))

lemma ratio_le_op_norm : ∥f x∥ / ∥x∥ ≤ ∥f∥ :=
  (or.elim (lt_or_eq_of_le (norm_nonneg _))
  (λ hlt, div_le_of_le_mul hlt (by rw mul_comm; exact le_op_norm _))
  (λ heq, by rw [←heq, div_zero]; exact op_norm_nonneg _))

/-- the image of the unit ball under a bounded linear map is bounded. -/
lemma unit_le_op_norm : ∥x∥ ≤ 1 → ∥f x∥ ≤ ∥f∥ :=
  λ hx, by rw [←(mul_one ∥f∥)];
  calc _ ≤ (op_norm f) * ∥x∥ : le_op_norm _
  ...    ≤ _ : mul_le_mul_of_nonneg_left hx (op_norm_nonneg _)

lemma op_norm_eq_zero : ∥f∥ = 0 ↔ f = 0 :=
  ⟨λ hn, bounded_linear_map.ext (λ x, (norm_le_zero_iff _).1
    (calc _ ≤ ∥f∥ * ∥x∥ : le_op_norm _
     ...     = _ : by rw [hn, zero_mul])),
  λ hf, le_antisymm (real.Inf_le _ bounds_bdd_below
    ⟨ge_of_eq rfl, λ _, le_of_eq (by rw [zero_mul, hf]; exact norm_zero)⟩)
    (op_norm_nonneg _)⟩

lemma op_norm_triangle : ∥f + g∥ ≤ ∥f∥ + ∥g∥ :=
  real.Inf_le _ bounds_bdd_below
  ⟨add_nonneg (op_norm_nonneg _) (op_norm_nonneg _), λ x, by rw add_mul;
    calc _ ≤ ∥f x∥ + ∥g x∥ : norm_triangle _ _
    ...    ≤ _ : add_le_add (le_op_norm _) (le_op_norm _)⟩

lemma op_norm_smul : ∥c • f∥ = ∥c∥ * ∥f∥ :=
  le_antisymm
    (real.Inf_le _ bounds_bdd_below
      ⟨mul_nonneg (norm_nonneg _) (op_norm_nonneg _),
      λ _, by erw [norm_smul, mul_assoc]; exact
      mul_le_mul_of_nonneg_left (le_op_norm _) (norm_nonneg _)⟩)
    (real.lb_le_Inf _ bounds_nonempty (λ _ ⟨hn, hc⟩,
      (or.elim (lt_or_eq_of_le (norm_nonneg c))
        (λ hlt, by rw mul_comm; exact
          mul_le_of_le_div hlt (real.Inf_le _ bounds_bdd_below
          ⟨div_nonneg hn hlt, λ _,
            (by rw div_mul_eq_mul_div; exact le_div_of_mul_le hlt
            (by rw [ mul_comm, ←norm_smul ]; exact hc _))⟩))
        (λ heq, by rw [←heq, zero_mul]; exact hn))))

/-- bounded linear maps themselves form a normed space w/ the op norm -/
noncomputable instance : normed_space k (bounded_linear_map k E F) :=
  normed_space.of_core _ _ ⟨op_norm_eq_zero, op_norm_smul, op_norm_triangle⟩

/-- operator norm is submultiplicative. -/
lemma op_norm_comp_le : ∥comp h f∥ ≤ ∥h∥ * ∥f∥ :=
  (real.Inf_le _
  bounds_bdd_below ⟨mul_nonneg (op_norm_nonneg _) (op_norm_nonneg _),
  λ x, by rw mul_assoc; calc _ ≤ ∥h∥ * ∥f x∥: le_op_norm _
  ... ≤ _ : mul_le_mul_of_nonneg_left (le_op_norm _) (op_norm_nonneg _)⟩)

/-- bounded linear maps are lipschitz continuous. -/
theorem lipschitz : lipschitz_with ∥f∥ f :=
  ⟨op_norm_nonneg _, λ x y, by rw [ dist_eq_norm, dist_eq_norm, ←map_sub];
  exact le_op_norm _⟩

end op_norm

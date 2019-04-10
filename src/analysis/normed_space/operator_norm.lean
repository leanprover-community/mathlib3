/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo

The space of bounded linear maps

Define the set of bounded linear maps between normed spaces and show basic facts about it. In
particular

(*) show that bounded linear maps are a vector subspace of E → F,
(*) define the operator norm and show that it induces the structure of a normed space
    on bounded linear maps.
-/
import algebra.module
import analysis.normed_space.bounded_linear_maps
import topology.metric_space.lipschitz

variables {k : Type*}
variables {E : Type*} {F : Type*} {G : Type*}

variables [normed_field k]
variables [normed_space k E] [normed_space k F] [normed_space k G]

noncomputable theory
set_option class.instance_max_depth 50

def bounded_linear_map : subspace k (E → F) :=
{ carrier := {f : E → F | is_bounded_linear_map k f},
  zero := is_bounded_linear_map.zero,
  add := λ _ _, is_bounded_linear_map.add,
  smul := λ _ _, is_bounded_linear_map.smul _ }

namespace bounded_linear_map

notation β ` →L[`:25 α `] ` γ := @bounded_linear_map α β γ _ _ _

/-- Coerce bounded linear maps to functions. -/
instance to_fun : has_coe_to_fun $ E →L[k] F :=
{F :=  λ _, (E → F), coe := (λ f, f.val)}

@[extensionality] theorem ext {f g : E →L[k] F} (h : ∀ x, f x = g x) : f = g :=
set_coe.ext $ funext h

theorem ext_iff {f g : E →L[k] F} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, by rintro; rw h, ext⟩

variables (c : k) (f g: E →L[k] F) (u v: E)

def to_linear_map : linear_map _ E F :=
{to_fun := f.val, ..f.property}

-- make some straightforward lemmas available to `simp`.
@[simp] lemma map_zero : f (0 : E) = 0 := (to_linear_map _).map_zero
@[simp] lemma map_add  : f (u + v) = f u + f v := (to_linear_map _).map_add _ _
@[simp] lemma map_sub  : f (u - v) = f u - f v := (to_linear_map _).map_sub _ _
@[simp] lemma map_smul : f (c • u) = c • f u := (to_linear_map _).map_smul _ _
@[simp] lemma map_neg  : f (-u) = - (f u) := (to_linear_map _).map_neg _

@[simp] lemma coe_zero : (0 : E →L[k] F) = 0 := rfl

@[simp] lemma zero_apply : (0 : E →L[k] F) u = 0 := rfl
@[simp] lemma smul_apply : (c • f) u = c • (f u) := rfl
@[simp] lemma neg_apply  : (-f) u = - (f u) := rfl

@[simp] lemma zero_smul : (0 : k) • f = 0  := by ext; simp
@[simp] lemma one_smul  : (1 : k) • f = f  := by ext; simp

/-- Composition of bounded linear maps. -/
def comp (g : F →L[k] G) (f : E →L[k] F) : E →L[k] G :=
⟨_, is_bounded_linear_map.comp g.property f.property⟩

end bounded_linear_map

section op_norm
open lattice set bounded_linear_map

variables (c : k) (f g : E →L[k] F) (h : F →L[k] G) (x : E)

/-- The operator norm of a bounded linear map is the inf of all its bounds. -/
def op_norm := real.Inf { c | c ≥ 0 ∧ ∀ x, ∥f x∥ ≤ c * ∥x∥ }
instance has_op_norm: has_norm (E →L[k] F) := ⟨op_norm⟩

-- So that invocations of real.Inf_le make sense: we show that the set of
-- bounds is nonempty and bounded below.
lemma bounds_nonempty {f : E →L[k] F} :
  ∃ c, c ∈ { c | c ≥ 0 ∧ ∀ x, ∥f x∥ ≤ c * ∥x∥ } :=
  let ⟨M, hMp, hMb⟩ := f.property.bound in ⟨M, le_of_lt hMp, hMb⟩

lemma bounds_bdd_below {f : E →L[k] F} :
  bdd_below { c | c ≥ 0 ∧ ∀ x, ∥f x∥ ≤ c * ∥x∥ } :=
  ⟨0, λ _ ⟨hn, _⟩, hn⟩

lemma op_norm_nonneg : 0 ≤ ∥f∥ :=
  real.lb_le_Inf _ bounds_nonempty (λ _ ⟨hx, _⟩, hx)

/-- This is the fundamental property of the operator norm: ∥f x∥ ≤ ∥f∥ * ∥x∥. -/
theorem le_op_norm : ∥f x∥ ≤ ∥f∥ * ∥x∥ :=
  classical.by_cases
    (λ heq : x = 0, by rw heq; simp)
    (λ hne, have hlt : 0 < ∥x∥, from (norm_pos_iff _).2 hne,
      le_mul_of_div_le hlt ((real.le_Inf _ bounds_nonempty bounds_bdd_below).2
      (λ c ⟨_, hc⟩, div_le_of_le_mul hlt (by rw mul_comm; exact hc _))))

lemma ratio_le_op_norm : ∥f x∥ / ∥x∥ ≤ ∥f∥ :=
  (or.elim (lt_or_eq_of_le (norm_nonneg _))
  (λ hlt, div_le_of_le_mul hlt (by rw mul_comm; exact le_op_norm _ _))
  (λ heq, by rw [←heq, div_zero]; exact op_norm_nonneg _))

/-- The image of the unit ball under a bounded linear map is bounded. -/
lemma unit_le_op_norm : ∥x∥ ≤ 1 → ∥f x∥ ≤ ∥f∥ :=
  λ hx, by rw [←(mul_one ∥f∥)];
  calc _ ≤ ∥f∥ * ∥x∥ : le_op_norm _ _
  ...    ≤ _ : mul_le_mul_of_nonneg_left hx (op_norm_nonneg _)

/-- If one controls the norm of every A x, then one controls the norm of A. -/
lemma bound_le_op_norm {M : ℝ} (hMp: 0 ≤ M) (hM : ∀ x, ∥f x∥ ≤ M * ∥x∥) :
  ∥f∥ ≤ M := real.Inf_le _ bounds_bdd_below ⟨hMp, hM⟩

/-- The operator norm satisfies the triangle inequality. -/
theorem op_norm_triangle : ∥f + g∥ ≤ ∥f∥ + ∥g∥ :=
  real.Inf_le _ bounds_bdd_below
  ⟨add_nonneg (op_norm_nonneg _) (op_norm_nonneg _),
    λ x, by rw add_mul;
    calc _ ≤ ∥f x∥ + ∥g x∥ : norm_triangle _ _
    ...    ≤ _ : add_le_add (le_op_norm _ _) (le_op_norm _ _)⟩

/-- An operator is zero iff its norm vanishes. -/
theorem op_norm_zero_iff : ∥f∥ = 0 ↔ f = 0 :=
iff.intro
  (λ hn, bounded_linear_map.ext (λ x, (norm_le_zero_iff _).1
    (calc _ ≤ ∥f∥ * ∥x∥ : le_op_norm _ _
     ...     = _ : by rw [hn, zero_mul])))
  (λ hf, le_antisymm (real.Inf_le _ bounds_bdd_below
    ⟨ge_of_eq rfl, λ _, le_of_eq (by rw [zero_mul, hf]; exact norm_zero)⟩)
    (op_norm_nonneg _))

/-- The operator norm is homogeneous. -/
lemma op_norm_smul : ∥c • f∥ = ∥c∥ * ∥f∥ :=
  le_antisymm
    (real.Inf_le _ bounds_bdd_below
      ⟨mul_nonneg (norm_nonneg _) (op_norm_nonneg _),
      λ _, by erw [norm_smul, mul_assoc]; exact
      mul_le_mul_of_nonneg_left (le_op_norm _ _) (norm_nonneg _)⟩)
    (real.lb_le_Inf _ bounds_nonempty (λ _ ⟨hn, hc⟩,
      (or.elim (lt_or_eq_of_le (norm_nonneg c))
        (λ hlt, by rw mul_comm; exact
          mul_le_of_le_div hlt (real.Inf_le _ bounds_bdd_below
          ⟨div_nonneg hn hlt, λ _,
            (by rw div_mul_eq_mul_div; exact le_div_of_mul_le hlt
            (by rw [ mul_comm, ←norm_smul ]; exact hc _))⟩))
        (λ heq, by rw [←heq, zero_mul]; exact hn))))

/-- Bounded linear maps themselves form a normed space with respect to
    the operator norm. -/
noncomputable instance bounded_linear_map.to_normed_space :
  normed_space k (E →L[k] F) :=
  normed_space.of_core _ _
  ⟨op_norm_zero_iff, op_norm_smul, op_norm_triangle⟩

/-- The operator norm is submultiplicative. -/
lemma op_norm_comp_le : ∥comp h f∥ ≤ ∥h∥ * ∥f∥ :=
  (real.Inf_le _ bounds_bdd_below
  ⟨mul_nonneg (op_norm_nonneg _) (op_norm_nonneg _),
  λ x, by rw mul_assoc; calc _ ≤ ∥h∥ * ∥f x∥: le_op_norm _ _
  ... ≤ _ : mul_le_mul_of_nonneg_left
            (le_op_norm _ _) (op_norm_nonneg _)⟩)

/-- bounded linear maps are lipschitz continuous. -/
theorem lipschitz : lipschitz_with ∥f∥ f :=
  ⟨op_norm_nonneg _, λ x y, by rw [dist_eq_norm, dist_eq_norm, ←map_sub];
  exact le_op_norm _ _⟩

end op_norm

/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import algebra.module.ulift
import order.liminf_limsup
import topology.algebra.uniform_group
import topology.metric_space.algebra
import topology.metric_space.isometry
import topology.sequences

/-!
# Normed (semi)groups

In this file we define 10 classes:

* `has_norm`, `has_nnnorm`: auxiliary classes endowing a type `α` with a function `norm : α → ℝ`
  (notation: `∥x∥`) and `nnnorm : α → ℝ≥0` (notation: `∥x∥₊`), respectively;
* `seminormed_..._group`: A seminormed (additive) (commutative) group is an (additive) (commutative)
  group with a norm and a compatible pseudometric space structure:
  `∀ x y, dist x y = ∥x / y∥` or `∀ x y, dist x y = ∥x - y∥`, depending on the group operation.
* `normed_..._group`: A normed (additive) (commutative) group is an (additive) (commutative) group
  with a norm and a compatible metric space structure.

We also prove basic properties of (semi)normed groups and provide some instances.

## Notes

The current convention `dist x y = ∥x - y∥` means that the distance is invariant under right
addition, but actions in mathlib are usually from the left. This means we might want to change it to
`dist x y = ∥-x + y∥`.

The normed group hierarchy would lend itself well to a mixin design (that is, having
`seminormed_group` and `seminormed_add_group` not extend `group` and `add_group`), but we choose not
to for performance concerns.

## Tags

normed group
-/

variables {𝓕 𝕜 α ι E F G : Type*}

open filter function metric
open_locale topological_space big_operators nnreal ennreal uniformity pointwise

/-- Auxiliary class, endowing a type `E` with a function `norm : E → ℝ` with notation `∥x∥`. This
class is designed to be extended in more interesting classes specifying the properties of the norm.
-/
@[notation_class] class has_norm (E : Type*) := (norm : E → ℝ)

/-- Auxiliary class, endowing a type `α` with a function `nnnorm : α → ℝ≥0` with notation `∥x∥₊`. -/
@[notation_class] class has_nnnorm (E : Type*) := (nnnorm : E → ℝ≥0)

export has_norm (norm)
export has_nnnorm (nnnorm)

notation `∥` e `∥` := norm e
notation `∥` e `∥₊` := nnnorm e

/-- A seminormed group is an additive group endowed with a norm for which `dist x y = ∥x - y∥`
defines a pseudometric space structure. -/
class seminormed_add_group (E : Type*) extends has_norm E, add_group E, pseudo_metric_space E :=
(dist := λ x y, ∥x - y∥)
(dist_eq : ∀ x y, dist x y = ∥x - y∥ . obviously)

/-- A seminormed group is a group endowed with a norm for which `dist x y = ∥x / y∥` defines a
pseudometric space structure. -/
@[to_additive]
class seminormed_group (E : Type*) extends has_norm E, group E, pseudo_metric_space E :=
(dist := λ x y, ∥x / y∥)
(dist_eq : ∀ x y, dist x y = ∥x / y∥ . obviously)

/-- A normed group is an additive group endowed with a norm for which `dist x y = ∥x - y∥` defines a
metric space structure. -/
class normed_add_group (E : Type*) extends has_norm E, add_group E, metric_space E :=
(dist := λ x y, ∥x - y∥)
(dist_eq : ∀ x y, dist x y = ∥x - y∥ . obviously)

/-- A normed group is a group endowed with a norm for which `dist x y = ∥x / y∥` defines a metric
space structure. -/
@[to_additive]
class normed_group (E : Type*) extends has_norm E, group E, metric_space E :=
(dist := λ x y, ∥x / y∥)
(dist_eq : ∀ x y, dist x y = ∥x / y∥ . obviously)

/-- A seminormed group is an additive group endowed with a norm for which `dist x y = ∥x - y∥`
defines a pseudometric space structure. -/
class seminormed_add_comm_group (E : Type*)
  extends has_norm E, add_comm_group E, pseudo_metric_space E :=
(dist := λ x y, ∥x - y∥)
(dist_eq : ∀ x y, dist x y = ∥x - y∥ . obviously)

/-- A seminormed group is a group endowed with a norm for which `dist x y = ∥x / y∥`
defines a pseudometric space structure. -/
@[to_additive]
class seminormed_comm_group (E : Type*)
  extends has_norm E, comm_group E, pseudo_metric_space E :=
(dist := λ x y, ∥x / y∥)
(dist_eq : ∀ x y, dist x y = ∥x / y∥ . obviously)

/-- A normed group is an additive group endowed with a norm for which `dist x y = ∥x - y∥` defines a
metric space structure. -/
class normed_add_comm_group (E : Type*) extends has_norm E, add_comm_group E, metric_space E :=
(dist := λ x y, ∥x - y∥)
(dist_eq : ∀ x y, dist x y = ∥x - y∥ . obviously)

/-- A normed group is a group endowed with a norm for which `dist x y = ∥x / y∥` defines a metric
space structure. -/
@[to_additive]
class normed_comm_group (E : Type*) extends has_norm E, comm_group E, metric_space E :=
(dist := λ x y, ∥x / y∥)
(dist_eq : ∀ x y, dist x y = ∥x / y∥ . obviously)

@[priority 100, to_additive] -- See note [lower instance priority]
instance normed_group.to_seminormed_group [normed_group E] : seminormed_group E :=
{ ..‹normed_group E› }

@[priority 100, to_additive] -- See note [lower instance priority]
instance normed_comm_group.to_seminormed_comm_group [normed_comm_group E] :
  seminormed_comm_group E :=
{ ..‹normed_comm_group E› }

@[priority 100, to_additive] -- See note [lower instance priority]
instance seminormed_comm_group.to_seminormed_group [seminormed_comm_group E] : seminormed_group E :=
{ ..‹seminormed_comm_group E› }

@[priority 100, to_additive] -- See note [lower instance priority]
instance normed_comm_group.to_normed_group [normed_comm_group E] : normed_group E :=
{ ..‹normed_comm_group E› }

/-- Construct a seminormed group from a multiplication-invariant distance. -/
@[to_additive "Construct a seminormed group from a translation-invariant distance."]
def seminormed_group.of_mul_dist [has_norm E] [group E] [pseudo_metric_space E]
  (h₁ : ∀ x : E, ∥x∥ = dist x 1) (h₂ : ∀ x y z : E, dist x y ≤ dist (x * z) (y * z)) :
  seminormed_group E :=
{ dist_eq := λ x y, begin
    rw h₁, apply le_antisymm,
    { simpa only [div_eq_mul_inv, ← mul_right_inv y] using h₂ _ _ _ },
    { simpa only [div_mul_cancel', one_mul] using h₂ (x/y) 1 y }
  end }

/-- Construct a seminormed group from a multiplication-invariant pseudodistance. -/
@[to_additive "Construct a seminormed group from a translation-invariant pseudodistance."]
def seminormed_group.of_mul_dist' [has_norm E] [group E] [pseudo_metric_space E]
  (h₁ : ∀ x : E, ∥x∥ = dist x 1) (h₂ : ∀ x y z : E, dist (x * z) (y * z) ≤ dist x y) :
  seminormed_group E :=
{ dist_eq := λ x y, begin
    rw h₁, apply le_antisymm,
    { simpa only [div_mul_cancel', one_mul] using h₂ (x/y) 1 y },
    { simpa only [div_eq_mul_inv, ← mul_right_inv y] using h₂ _ _ _ }
  end }

/-- Construct a seminormed group from a multiplication-invariant pseudodistance. -/
@[to_additive "Construct a seminormed group from a translation-invariant pseudodistance."]
def seminormed_comm_group.of_mul_dist [has_norm E] [comm_group E] [pseudo_metric_space E]
  (h₁ : ∀ x : E, ∥x∥ = dist x 1) (h₂ : ∀ x y z : E, dist x y ≤ dist (x * z) (y * z)) :
  seminormed_comm_group E :=
{ ..seminormed_group.of_mul_dist h₁ h₂ }

/-- Construct a seminormed group from a multiplication-invariant pseudodistance. -/
@[to_additive "Construct a seminormed group from a translation-invariant pseudodistance."]
def seminormed_comm_group.of_mul_dist' [has_norm E] [comm_group E] [pseudo_metric_space E]
  (h₁ : ∀ x : E, ∥x∥ = dist x 1) (h₂ : ∀ x y z : E, dist (x * z) (y * z) ≤ dist x y) :
  seminormed_comm_group E :=
{ ..seminormed_group.of_mul_dist' h₁ h₂ }

/-- Construct a normed group from a multiplication-invariant distance. -/
@[to_additive "Construct a normed group from a translation-invariant distance."]
def normed_group.of_mul_dist [has_norm E] [group E] [metric_space E]
  (h₁ : ∀ x : E, ∥x∥ = dist x 1) (h₂ : ∀ x y z : E, dist x y ≤ dist (x * z) (y * z)) :
  normed_group E :=
{ ..seminormed_group.of_mul_dist h₁ h₂ }

/-- Construct a normed group from a multiplication-invariant pseudodistance. -/
@[to_additive "Construct a normed group from a translation-invariant pseudodistance."]
def normed_group.of_mul_dist' [has_norm E] [group E] [metric_space E]
  (h₁ : ∀ x : E, ∥x∥ = dist x 1) (h₂ : ∀ x y z : E, dist (x * z) (y * z) ≤ dist x y) :
  normed_group E :=
{ ..seminormed_group.of_mul_dist' h₁ h₂ }

/-- Construct a normed group from a multiplication-invariant pseudodistance. -/
@[to_additive "Construct a normed group from a translation-invariant pseudodistance."]
def normed_comm_group.of_mul_dist [has_norm E] [comm_group E] [metric_space E]
  (h₁ : ∀ x : E, ∥x∥ = dist x 1) (h₂ : ∀ x y z : E, dist x y ≤ dist (x * z) (y * z)) :
  normed_comm_group E :=
{ ..normed_group.of_mul_dist h₁ h₂ }

/-- Construct a normed group from a multiplication-invariant pseudodistance. -/
@[to_additive "Construct a normed group from a translation-invariant pseudodistance."]
def normed_comm_group.of_mul_dist' [has_norm E] [comm_group E] [metric_space E]
  (h₁ : ∀ x : E, ∥x∥ = dist x 1) (h₂ : ∀ x y z : E, dist (x * z) (y * z) ≤ dist x y) :
  normed_comm_group E :=
{ ..normed_group.of_mul_dist' h₁ h₂ }

set_option old_structure_cmd true

/-- A seminormed group can be built from a seminorm that satisfies algebraic properties. This is
formalised in this structure. -/
structure seminormed_add_group.core (E : Type*) [add_group E] [has_norm E] : Prop :=
(norm_zero : ∥(0 : E)∥ = 0)
(triangle : ∀ x y : E, ∥x + y∥ ≤ ∥x∥ + ∥y∥)
(norm_neg : ∀ x : E, ∥-x∥ = ∥x∥)

/-- A seminormed group can be built from a seminorm that satisfies algebraic properties. This is
formalised in this structure. -/
@[to_additive]
structure seminormed_group.core (E : Type*) [group E] [has_norm E] : Prop :=
(norm_one : ∥(1 : E)∥ = 0)
(triangle : ∀ x y : E, ∥x * y∥ ≤ ∥x∥ + ∥y∥)
(norm_inv : ∀ x : E, ∥x⁻¹∥ = ∥x∥)

/-- A normed group can be built from a norm that satisfies algebraic properties. This is
formalised in this structure. -/
structure normed_add_group.core (E : Type*) [add_group E] [has_norm E]
  extends seminormed_add_group.core E : Prop :=
(eq_zero_of_norm : ∀ x : E, ∥x∥ = 0 → x = 0)

/-- A normed group can be built from a norm that satisfies algebraic properties. This is
formalised in this structure. -/
@[to_additive]
structure normed_group.core (E : Type*) [group E] [has_norm E]
  extends seminormed_group.core E : Prop :=
(eq_one_of_norm : ∀ x : E, ∥x∥ = 0 → x = 1)

/-- Constructing a seminormed group from core properties of a seminorm, i.e., registering the
pseudodistance and the pseudometric space structure from the seminorm properties. Note that in most
cases this instance creates bad definitional equalities (e.g., it does not take into account
a possibly existing `uniform_space` instance on `E`). -/
@[to_additive "Constructing a seminormed group from core properties of a seminorm, i.e., registering
the pseudodistance and the pseudometric space structure from the seminorm properties. Note that in
most cases this instance creates bad definitional equalities (e.g., it does not take into account
a possibly existing `uniform_space` instance on `E`)"]
def seminormed_group.of_core (E : Type*) [group E] [has_norm E] (C : seminormed_group.core E) :
  seminormed_group E :=
{ dist := λ x y, ∥x / y∥,
  dist_self := λ x, by simp [C.norm_one],
  dist_triangle := λ x y z,
    calc ∥x / z∥ = ∥x / y * (y / z)∥ : by rw div_mul_div_cancel'
            ... ≤ ∥x / y∥ + ∥y / z∥  : C.triangle _ _,
  dist_comm := λ x y,
    calc ∥x / y∥ = ∥(y / x)⁻¹∥ : by simp
             ... = ∥y / x∥ : C.norm_inv _ }

/-- Constructing a seminormed group from core properties of a seminorm, i.e., registering the
pseudodistance and the pseudometric space structure from the seminorm properties. Note that in most
cases this instance creates bad definitional equalities (e.g., it does not take into account
a possibly existing `uniform_space` instance on `E`). -/
@[to_additive "Constructing a seminormed group from core properties of a seminorm, i.e., registering
the pseudodistance and the pseudometric space structure from the seminorm properties. Note that in
most cases this instance creates bad definitional equalities (e.g., it does not take into account
a possibly existing `uniform_space` instance on `E`)"]
def seminormed_comm_group.of_core (E : Type*) [comm_group E] [has_norm E]
  (C : seminormed_group.core E) : seminormed_comm_group E :=
{ ..seminormed_group.of_core _ C }

/-- Constructing a normed group from core properties of a norm, i.e., registering the distance and
the metric space structure from the norm properties. -/
@[to_additive "Constructing a normed group from core properties of a norm, i.e., registering the
distance and the metric space structure from the norm properties."]
def normed_group.of_core (E : Type*) [group E] [has_norm E] (C : normed_group.core E) :
  normed_group E :=
{ eq_of_dist_eq_zero := λ x y h, div_eq_one.1 $ C.eq_one_of_norm _ h,
  ..seminormed_group.of_core E C.to_core }

/-- Constructing a normed group from core properties of a norm, i.e., registering the distance and
the metric space structure from the norm properties. -/
@[to_additive "Constructing a normed group from core properties of a norm, i.e., registering the
distance and the metric space structure from the norm properties."]
def normed_comm_group.of_core (E : Type*) [comm_group E] [has_norm E] (C : normed_group.core E) :
  normed_comm_group E :=
{ ..normed_group.of_core E C }

instance : normed_add_comm_group punit :=
{ norm := function.const _ 0,
  dist_eq := λ _ _, rfl, }

@[simp] lemma punit.norm_eq_zero (r : punit) : ∥r∥ = 0 := rfl

noncomputable instance : normed_add_comm_group ℝ :=
{ norm := λ x, |x|,
  dist_eq := assume x y, rfl }

@[simp] lemma real.norm_eq_abs (r : ℝ) : ∥r∥ = |r| := rfl

section seminormed_group
variables [seminormed_group E] [seminormed_group F] [seminormed_group G] {s : set E}
  {a a₁ a₂ b b₁ b₂ : E} {r r₁ r₂ : ℝ}

@[to_additive]
lemma dist_eq_norm_div (a b : E) : dist a b = ∥a / b∥ := seminormed_group.dist_eq _ _

@[to_additive]
lemma dist_eq_norm_div' (a b : E) : dist a b = ∥b / a∥ := by rw [dist_comm, dist_eq_norm_div]

alias dist_eq_norm_sub ← dist_eq_norm
alias dist_eq_norm_sub' ← dist_eq_norm'

@[simp, to_additive] lemma dist_one_right (a : E) : dist a 1 = ∥a∥ :=
by rw [dist_eq_norm_div, div_one]

@[simp, to_additive] lemma dist_one_left : dist (1 : E) = norm :=
funext $ λ a, by rw [dist_comm, dist_one_right]

@[to_additive]
lemma isometry.norm_map_of_map_one {f : E → F} (hi : isometry f) (h₁ : f 1 = 1) (x : E) :
  ∥f x∥ = ∥x∥ :=
by rw [←dist_one_right, ←h₁, hi.dist_eq, dist_one_right]

@[to_additive tendsto_norm_cocompact_at_top]
lemma tendsto_norm_cocompact_at_top' [proper_space E] : tendsto norm (cocompact E) at_top :=
by simpa only [dist_one_right] using tendsto_dist_right_cocompact_at_top (1 : E)

@[to_additive] lemma norm_div_rev (a b : E) : ∥a / b∥ = ∥b / a∥ :=
by simpa only [dist_eq_norm_div] using dist_comm a b

@[simp, to_additive norm_neg]
lemma norm_inv' (a : E) : ∥a⁻¹∥ = ∥a∥ := by simpa using norm_div_rev 1 a

@[simp, to_additive] lemma dist_mul_right (a₁ a₂ b : E) : dist (a₁ * b) (a₂ * b) = dist a₁ a₂ :=
by simp [dist_eq_norm_div]

@[simp, to_additive] lemma dist_div_right (a₁ a₂ b : E) : dist (a₁ / b) (a₂ / b) = dist a₁ a₂ :=
by simpa only [div_eq_mul_inv] using dist_mul_right _ _ _

/-- In a (semi)normed group, inversion `x ↦ x⁻¹` tends to infinity at infinity. TODO: use
`bornology.cobounded` instead of `filter.comap has_norm.norm filter.at_top`. -/
@[to_additive "In a (semi)normed group, negation `x ↦ -x` tends to infinity at infinity. TODO: use
`bornology.cobounded` instead of `filter.comap has_norm.norm filter.at_top`."]
lemma filter.tendsto_inv_cobounded :
  tendsto (has_inv.inv : E → E) (comap norm at_top) (comap norm at_top) :=
by simpa only [norm_inv', tendsto_comap_iff, (∘)] using tendsto_comap

/-- **Triangle inequality** for the norm. -/
@[to_additive norm_add_le "**Triangle inequality** for the norm."]
lemma norm_mul_le' (a b : E) : ∥a * b∥ ≤ ∥a∥ + ∥b∥ :=
by simpa [dist_eq_norm_div] using dist_triangle a 1 b⁻¹

@[to_additive] lemma norm_mul_le_of_le (h₁ : ∥a₁∥ ≤ r₁) (h₂ : ∥a₂∥ ≤ r₂) : ∥a₁ * a₂∥ ≤ r₁ + r₂ :=
(norm_mul_le' a₁ a₂).trans $ add_le_add h₁ h₂

@[to_additive norm_add₃_le] lemma norm_mul₃_le (a b c : E) : ∥a * b * c∥ ≤ ∥a∥ + ∥b∥ + ∥c∥ :=
norm_mul_le_of_le (norm_mul_le' _ _) le_rfl

@[simp, to_additive norm_nonneg] lemma norm_nonneg' (a : E) : 0 ≤ ∥a∥ :=
by { rw[←dist_one_right], exact dist_nonneg }

section
open tactic tactic.positivity

--TODO: Support multiplicative norms
/-- Extension for the `positivity` tactic: norms are nonnegative. -/
@[positivity]
meta def _root_.tactic.positivity_norm : expr → tactic strictness
| `(∥%%a∥) := nonnegative <$> mk_app ``norm_nonneg [a]
| _ := failed

end

@[simp, to_additive norm_zero] lemma norm_one' : ∥(1 : E)∥ = 0 := by rw [←dist_one_right, dist_self]

@[to_additive] lemma ne_one_of_norm_ne_zero : ∥a∥ ≠ 0 → a ≠ 1 :=
mt $ by { rintro rfl, exact norm_one' }

@[nontriviality, to_additive norm_of_subsingleton]
lemma norm_of_subsingleton' [subsingleton E] (a : E) : ∥a∥ = 0 :=
by rw [subsingleton.elim a 1, norm_one']

attribute [nontriviality] norm_of_subsingleton

@[to_additive] lemma norm_div_le (a b : E) : ∥a / b∥ ≤ ∥a∥ + ∥b∥ :=
by simpa [dist_eq_norm_div] using dist_triangle a 1 b

@[to_additive] lemma norm_div_le_of_le {r₁ r₂ : ℝ} (H₁ : ∥a₁∥ ≤ r₁) (H₂ : ∥a₂∥ ≤ r₂) :
  ∥a₁ / a₂∥ ≤ r₁ + r₂ :=
(norm_div_le a₁ a₂).trans $ add_le_add H₁ H₂

@[to_additive] lemma dist_le_norm_mul_norm (a b : E) : dist a b ≤ ∥a∥ + ∥b∥ :=
by { rw dist_eq_norm_div, apply norm_div_le }

@[to_additive abs_norm_sub_norm_le] lemma abs_norm_sub_norm_le' (a b : E) : |∥a∥ - ∥b∥| ≤ ∥a / b∥ :=
by simpa [dist_eq_norm_div] using abs_dist_sub_le a b 1

@[to_additive norm_sub_norm_le] lemma norm_sub_norm_le' (a b : E) : ∥a∥ - ∥b∥ ≤ ∥a / b∥ :=
(le_abs_self _).trans (abs_norm_sub_norm_le' a b)

@[to_additive dist_norm_norm_le] lemma dist_norm_norm_le' (a b : E) : dist ∥a∥ ∥b∥ ≤ ∥a / b∥ :=
abs_norm_sub_norm_le' a b

@[to_additive] lemma norm_le_norm_add_norm_div' (u v : E) : ∥u∥ ≤ ∥v∥ + ∥u / v∥ :=
by { rw add_comm, refine (norm_mul_le' _ _).trans_eq' _, rw div_mul_cancel' }

@[to_additive] lemma norm_le_norm_add_norm_div (u v : E) : ∥v∥ ≤ ∥u∥ + ∥u / v∥ :=
by { rw norm_div_rev, exact norm_le_norm_add_norm_div' v u }

alias norm_le_norm_add_norm_sub' ← norm_le_insert'
alias norm_le_norm_add_norm_sub ← norm_le_insert

@[to_additive] lemma norm_le_mul_norm_add (u v : E) : ∥u∥ ≤ ∥u * v∥ + ∥v∥ :=
calc ∥u∥ = ∥u * v / v∥ : by rw mul_div_cancel''
... ≤ ∥u * v∥ + ∥v∥ : norm_div_le _ _

@[to_additive ball_eq] lemma ball_eq' (y : E) (ε : ℝ) : ball y ε = {x | ∥x / y∥ < ε} :=
set.ext $ λ a, by simp [dist_eq_norm_div]

@[to_additive] lemma ball_one_eq (r : ℝ) : ball (1 : E) r = {x | ∥x∥ < r} :=
set.ext $ assume a, by simp

@[to_additive mem_ball_iff_norm] lemma mem_ball_iff_norm'' : b ∈ ball a r ↔ ∥b / a∥ < r :=
by rw [mem_ball, dist_eq_norm_div]

@[to_additive mem_ball_iff_norm'] lemma mem_ball_iff_norm''' : b ∈ ball a r ↔ ∥a / b∥ < r :=
by rw [mem_ball', dist_eq_norm_div]

@[simp, to_additive] lemma mem_ball_one_iff : a ∈ ball (1 : E) r ↔ ∥a∥ < r :=
by rw [mem_ball, dist_one_right]

@[to_additive mem_closed_ball_iff_norm]
lemma mem_closed_ball_iff_norm'' : b ∈ closed_ball a r ↔ ∥b / a∥ ≤ r :=
by rw [mem_closed_ball, dist_eq_norm_div]

@[simp, to_additive] lemma mem_closed_ball_one_iff : a ∈ closed_ball (1 : E) r ↔ ∥a∥ ≤ r :=
by rw [mem_closed_ball, dist_one_right]

@[to_additive mem_closed_ball_iff_norm']
lemma mem_closed_ball_iff_norm''' : b ∈ closed_ball a r ↔ ∥a / b∥ ≤ r :=
by rw [mem_closed_ball', dist_eq_norm_div]

@[to_additive norm_le_of_mem_closed_ball]
lemma norm_le_of_mem_closed_ball' (h : b ∈ closed_ball a r) : ∥b∥ ≤ ∥a∥ + r :=
(norm_le_norm_add_norm_div' _ _).trans $ add_le_add_left (by rwa ←dist_eq_norm_div) _

@[to_additive norm_le_norm_add_const_of_dist_le]
lemma norm_le_norm_add_const_of_dist_le' : dist a b ≤ r → ∥a∥ ≤ ∥b∥ + r :=
norm_le_of_mem_closed_ball'

@[to_additive norm_lt_of_mem_ball]
lemma norm_lt_of_mem_ball' (h : b ∈ ball a r) : ∥b∥ < ∥a∥ + r :=
(norm_le_norm_add_norm_div' _ _).trans_lt $ add_lt_add_left (by rwa ←dist_eq_norm_div) _

@[to_additive bounded_iff_forall_norm_le]
lemma bounded_iff_forall_norm_le' : bounded s ↔ ∃ C, ∀ x ∈ s, ∥x∥ ≤ C :=
by simpa only [set.subset_def, mem_closed_ball_one_iff] using bounded_iff_subset_ball (1 : E)

@[simp, to_additive mem_sphere_iff_norm]
lemma mem_sphere_iff_norm' : b ∈ sphere a r ↔ ∥b / a∥ = r := by simp [dist_eq_norm_div]

@[simp, to_additive] lemma mem_sphere_one_iff_norm : a ∈ sphere (1 : E) r ↔ ∥a∥ = r :=
by simp [dist_eq_norm_div]

@[simp, to_additive norm_eq_of_mem_sphere]
lemma norm_eq_of_mem_sphere' (x : sphere (1:E) r) : ∥(x : E)∥ = r := mem_sphere_one_iff_norm.mp x.2

@[to_additive] lemma ne_one_of_mem_sphere (hr : r ≠ 0) (x : sphere (1 : E) r) : (x : E) ≠ 1 :=
ne_one_of_norm_ne_zero $ by rwa norm_eq_of_mem_sphere' x

@[to_additive ne_zero_of_mem_unit_sphere]
lemma ne_one_of_mem_unit_sphere (x : sphere (1 : E) 1) : (x:E) ≠ 1 :=
ne_one_of_mem_sphere one_ne_zero _

namespace isometric
-- TODO This material is superseded by similar constructions such as
-- `affine_isometry_equiv.const_vadd`; deduplicate

/-- Multiplication `y ↦ y * x` as an `isometry`. -/
@[to_additive "Addition `y ↦ y + x` as an `isometry`"]
protected def mul_right (x : E) : E ≃ᵢ E :=
{ isometry_to_fun := isometry.of_dist_eq $ λ y z, dist_mul_right _ _ _,
  .. equiv.mul_right x }

@[simp, to_additive]
lemma mul_right_to_equiv (x : E) : (isometric.mul_right x).to_equiv = equiv.mul_right x := rfl

@[simp, to_additive]
lemma coe_mul_right (x : E) : (isometric.mul_right x : E → E) = λ y, y * x := rfl

@[to_additive] lemma mul_right_apply (x y : E) : (isometric.mul_right x : E → E) y = y * x := rfl

@[simp, to_additive]
lemma mul_right_symm (x : E) : (isometric.mul_right x).symm = isometric.mul_right x⁻¹ :=
ext $ λ y, rfl

end isometric

@[to_additive] lemma normed_comm_group.tendsto_nhds_one {f : α → E} {l : filter α} :
  tendsto f l (𝓝 1) ↔ ∀ ε > 0, ∀ᶠ x in l, ∥ f x ∥ < ε :=
metric.tendsto_nhds.trans $ by simp only [dist_one_right]

@[to_additive] lemma normed_comm_group.tendsto_nhds_nhds {f : E → F} {x : E} {y : F} :
  tendsto f (𝓝 x) (𝓝 y) ↔ ∀ ε > 0, ∃ δ > 0, ∀ x', ∥x' / x∥ < δ → ∥f x' / y∥ < ε :=
by simp_rw [metric.tendsto_nhds_nhds, dist_eq_norm_div]

@[to_additive] lemma normed_comm_group.cauchy_seq_iff [nonempty α] [semilattice_sup α] {u : α → E} :
  cauchy_seq u ↔ ∀ ε > 0, ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n → ∥u m / u n∥ < ε :=
by simp [metric.cauchy_seq_iff, dist_eq_norm_div]

@[to_additive] lemma normed_comm_group.nhds_basis_norm_lt (x : E) :
  (𝓝 x).has_basis (λ ε : ℝ, 0 < ε) (λ ε, {y | ∥y / x∥ < ε}) :=
by { simp_rw ← ball_eq', exact metric.nhds_basis_ball }

@[to_additive] lemma normed_comm_group.nhds_one_basis_norm_lt :
  (𝓝 (1 : E)).has_basis (λ ε : ℝ, 0 < ε) (λ ε, {y | ∥y∥ < ε}) :=
by { convert normed_comm_group.nhds_basis_norm_lt (1 : E), simp }

@[to_additive] lemma normed_comm_group.uniformity_basis_dist :
  (𝓤 E).has_basis (λ ε : ℝ, 0 < ε) (λ ε, {p : E × E | ∥p.fst / p.snd∥ < ε}) :=
by { convert metric.uniformity_basis_dist, simp [dist_eq_norm_div] }

open finset

/-- A homomorphism `f` of seminormed groups is Lipschitz, if there exists a constant `C` such that
for all `x`, one has `∥f x∥ ≤ C * ∥x∥`. The analogous condition for a linear map of
(semi)normed spaces is in `normed_space.operator_norm`. -/
@[to_additive "A homomorphism `f` of seminormed groups is Lipschitz, if there exists a constant `C`
such that for all `x`, one has `∥f x∥ ≤ C * ∥x∥`. The analogous condition for a linear map of
(semi)normed spaces is in `normed_space.operator_norm`."]
lemma monoid_hom_class.lipschitz_of_bound [monoid_hom_class 𝓕 E F] (f : 𝓕) (C : ℝ)
  (h : ∀ x, ∥f x∥ ≤ C * ∥x∥) : lipschitz_with (real.to_nnreal C) f :=
lipschitz_with.of_dist_le' $ λ x y, by simpa only [dist_eq_norm_div, map_div] using h (x / y)

@[to_additive] lemma lipschitz_on_with_iff_norm_div_le {f : E → F} {C : ℝ≥0} :
  lipschitz_on_with C f s ↔ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∥f x / f y∥ ≤ C * ∥x / y∥ :=
by simp only [lipschitz_on_with_iff_dist_le_mul, dist_eq_norm_div]

alias lipschitz_on_with_iff_norm_div_le ↔ lipschitz_on_with.norm_div_le _

attribute [to_additive] lipschitz_on_with.norm_div_le

@[to_additive] lemma lipschitz_on_with.norm_div_le_of_le {f : E → F} {C : ℝ≥0}
  (h : lipschitz_on_with C f s) (ha : a ∈ s) (hb : b ∈ s) (hr : ∥a / b∥ ≤ r) :
  ∥f a / f b∥ ≤ C * r :=
(h.norm_div_le ha hb).trans $ mul_le_mul_of_nonneg_left hr C.2

@[to_additive] lemma lipschitz_with_iff_norm_div_le {f : E → F} {C : ℝ≥0} :
  lipschitz_with C f ↔ ∀ x y, ∥f x / f y∥ ≤ C * ∥x / y∥ :=
by simp only [lipschitz_with_iff_dist_le_mul, dist_eq_norm_div]

alias lipschitz_with_iff_norm_div_le ↔ lipschitz_with.norm_div_le _

attribute [to_additive] lipschitz_with.norm_div_le

@[to_additive] lemma lipschitz_with.norm_div_le_of_le {f : E → F} {C : ℝ≥0} (h : lipschitz_with C f)
  (hr : ∥a / b∥ ≤ r) : ∥f a / f b∥ ≤ C * r :=
(h.norm_div_le _ _).trans $ mul_le_mul_of_nonneg_left hr C.2

/-- A homomorphism `f` of seminormed groups is continuous, if there exists a constant `C` such that
for all `x`, one has `∥f x∥ ≤ C * ∥x∥`. -/
@[to_additive "A homomorphism `f` of seminormed groups is continuous, if there exists a constant `C`
such that for all `x`, one has `∥f x∥ ≤ C * ∥x∥`"]
lemma monoid_hom_class.continuous_of_bound [monoid_hom_class 𝓕 E F] (f : 𝓕) (C : ℝ)
  (h : ∀ x, ∥f x∥ ≤ C * ∥x∥) : continuous f :=
(monoid_hom_class.lipschitz_of_bound f C h).continuous

@[to_additive] lemma monoid_hom_class.uniform_continuous_of_bound [monoid_hom_class 𝓕 E F]
  (f : 𝓕) (C : ℝ) (h : ∀x, ∥f x∥ ≤ C * ∥x∥) : uniform_continuous f :=
(monoid_hom_class.lipschitz_of_bound f C h).uniform_continuous

@[to_additive is_compact.exists_bound_of_continuous_on]
lemma is_compact.exists_bound_of_continuous_on' [topological_space α] {s : set α}
  (hs : is_compact s) {f : α → E} (hf : continuous_on f s) :
  ∃ C, ∀ x ∈ s, ∥f x∥ ≤ C :=
(bounded_iff_forall_norm_le'.1 (hs.image_of_continuous_on hf).bounded).imp $ λ C hC x hx,
  hC _ $ set.mem_image_of_mem _ hx

@[to_additive] lemma monoid_hom_class.isometry_iff_norm [monoid_hom_class 𝓕 E F] (f : 𝓕) :
  isometry f ↔ ∀ x, ∥f x∥ = ∥x∥ :=
begin
  simp only [isometry_iff_dist_eq, dist_eq_norm_div, ←map_div],
  refine ⟨λ h x, _, λ h x y, h _⟩,
  simpa using h x 1,
end

alias monoid_hom_class.isometry_iff_norm ↔ _ monoid_hom_class.isometry_of_norm

attribute [to_additive] monoid_hom_class.isometry_of_norm

section nnnorm

@[priority 100, to_additive] -- See note [lower instance priority]
instance seminormed_group.to_has_nnnorm : has_nnnorm E := ⟨λ a, ⟨∥a∥, norm_nonneg' a⟩⟩

@[simp, norm_cast, to_additive coe_nnnorm] lemma coe_nnnorm' (a : E) : (∥a∥₊ : ℝ) = ∥a∥ := rfl

@[simp, to_additive coe_comp_nnnorm]
lemma coe_comp_nnnorm' : (coe : ℝ≥0 → ℝ) ∘ (nnnorm : E → ℝ≥0) = norm := rfl

@[to_additive norm_to_nnreal]
lemma norm_to_nnreal' : ∥a∥.to_nnreal = ∥a∥₊ := @real.to_nnreal_coe ∥a∥₊

@[to_additive]
lemma nndist_eq_nnnorm_div (a b : E) : nndist a b = ∥a / b∥₊ := nnreal.eq $ dist_eq_norm_div _ _

alias nndist_eq_nnnorm_sub ← nndist_eq_nnnorm

@[simp, to_additive nnnorm_zero] lemma nnnorm_one' : ∥(1 : E)∥₊ = 0 := nnreal.eq norm_one'

@[to_additive] lemma ne_one_of_nnnorm_ne_zero {a : E} : ∥a∥₊ ≠ 0 → a ≠ 1 :=
mt $ by { rintro rfl, exact nnnorm_one' }

@[to_additive nnnorm_add_le]
lemma nnnorm_mul_le' (a b : E) : ∥a * b∥₊ ≤ ∥a∥₊ + ∥b∥₊ := nnreal.coe_le_coe.1 $ norm_mul_le' a b

@[simp, to_additive nnnorm_neg] lemma nnnorm_inv' (a : E) : ∥a⁻¹∥₊ = ∥a∥₊ := nnreal.eq $ norm_inv' a

@[to_additive nndist_nnnorm_nnnorm_le]
lemma nndist_nnnorm_nnnorm_le' (a b : E) : nndist ∥a∥₊ ∥b∥₊ ≤ ∥a / b∥₊ :=
nnreal.coe_le_coe.1 $ dist_norm_norm_le' a b

@[to_additive] lemma nnnorm_le_nnnorm_add_nnnorm_div (a b : E) : ∥b∥₊ ≤ ∥a∥₊ + ∥a / b∥₊ :=
norm_le_norm_add_norm_div _ _

@[to_additive] lemma nnnorm_le_nnnorm_add_nnnorm_div' (a b : E) : ∥a∥₊ ≤ ∥b∥₊ + ∥a / b∥₊ :=
norm_le_norm_add_norm_div' _ _

alias nnnorm_le_nnnorm_add_nnnorm_sub' ← nnnorm_le_insert'
alias nnnorm_le_nnnorm_add_nnnorm_sub ← nnnorm_le_insert

@[to_additive]
lemma nnnorm_le_mul_nnnorm_add (a b : E) : ∥a∥₊ ≤ ∥a * b∥₊ + ∥b∥₊ := norm_le_mul_norm_add _ _

@[to_additive of_real_norm_eq_coe_nnnorm]
lemma of_real_norm_eq_coe_nnnorm' (a : E) : ennreal.of_real ∥a∥ = ∥a∥₊ :=
ennreal.of_real_eq_coe_nnreal _

@[to_additive] lemma edist_eq_coe_nnnorm_div (a b : E) : edist a b = ∥a / b∥₊ :=
by rw [edist_dist, dist_eq_norm_div, of_real_norm_eq_coe_nnnorm']

@[to_additive edist_eq_coe_nnnorm] lemma edist_eq_coe_nnnorm' (x : E) : edist x 1 = (∥x∥₊ : ℝ≥0∞) :=
by rw [edist_eq_coe_nnnorm_div, div_one]

@[to_additive]
lemma mem_emetric_ball_one_iff {r : ℝ≥0∞} : a ∈ emetric.ball (1 : E) r ↔ ↑∥a∥₊ < r :=
by rw [emetric.mem_ball, edist_eq_coe_nnnorm']

@[simp, to_additive] lemma edist_mul_right (a₁ a₂ b : E) : edist (a₁ * b) (a₂ * b) = edist a₁ a₂ :=
by simp [edist_dist]

@[simp, to_additive] lemma edist_div_right (a₁ a₂ b : E) : edist (a₁ / b) (a₂ / b) = edist a₁ a₂ :=
by simpa only [div_eq_mul_inv] using edist_mul_right _ _ _

@[to_additive] lemma monoid_hom_class.lipschitz_of_bound_nnnorm [monoid_hom_class 𝓕 E F] (f : 𝓕)
  (C : ℝ≥0) (h : ∀ x, ∥f x∥₊ ≤ C * ∥x∥₊) : lipschitz_with C f :=
@real.to_nnreal_coe C ▸ monoid_hom_class.lipschitz_of_bound f C h

@[to_additive] lemma monoid_hom_class.antilipschitz_of_bound [monoid_hom_class 𝓕 E F] (f : 𝓕)
  {K : ℝ≥0} (h : ∀ x, ∥x∥ ≤ K * ∥f x∥) :
  antilipschitz_with K f :=
antilipschitz_with.of_le_mul_dist $ λ x y, by simpa only [dist_eq_norm_div, map_div] using h (x / y)

@[to_additive] lemma monoid_hom_class.bound_of_antilipschitz [monoid_hom_class 𝓕 E F] (f : 𝓕)
  {K : ℝ≥0} (h : antilipschitz_with K f) (x) : ∥x∥ ≤ K * ∥f x∥ :=
by simpa only [dist_one_right, map_one] using h.le_mul_dist x 1

end nnnorm

@[to_additive] lemma tendsto_iff_norm_tendsto_one {f : α → E} {a : filter α} {b : E} :
  tendsto f a (𝓝 b) ↔ tendsto (λ e, ∥f e / b∥) a (𝓝 0) :=
by { convert tendsto_iff_dist_tendsto_zero, simp [dist_eq_norm_div] }

@[to_additive] lemma tendsto_one_iff_norm_tendsto_one {f : α → E} {a : filter α} :
  tendsto f a (𝓝 1) ↔ tendsto (λ e, ∥f e∥) a (𝓝 0) :=
by { rw tendsto_iff_norm_tendsto_one, simp only [div_one] }

@[to_additive] lemma comap_norm_nhds_one : comap norm (𝓝 0) = 𝓝 (1 : E) :=
by simpa only [dist_one_right] using nhds_comap_dist (1 : E)

/-- Special case of the sandwich theorem: if the norm of `f` is eventually bounded by a real
function `a` which tends to `0`, then `f` tends to `1`. In this pair of lemmas (`squeeze_one_norm'`
and `squeeze_one_norm`), following a convention of similar lemmas in `topology.metric_space.basic`
and `topology.algebra.order`, the `'` version is phrased using "eventually" and the non-`'` version
is phrased absolutely. -/
@[to_additive "Special case of the sandwich theorem: if the norm of `f` is eventually bounded by a
real function `a` which tends to `0`, then `f` tends to `1`. In this pair of lemmas
(`squeeze_zero_norm'` and `squeeze_zero_norm`), following a convention of similar lemmas in
`topology.metric_space.basic` and `topology.algebra.order`, the `'` version is phrased using
\"eventually\" and the non-`'` version is phrased absolutely."]
lemma squeeze_one_norm' {f : α → E} {a : α → ℝ} {t₀ : filter α} (h : ∀ᶠ n in t₀, ∥f n∥ ≤ a n)
  (h' : tendsto a t₀ (𝓝 0)) : tendsto f t₀ (𝓝 1) :=
tendsto_one_iff_norm_tendsto_one.2 $ squeeze_zero' (eventually_of_forall $ λ n, norm_nonneg' _) h h'

/-- Special case of the sandwich theorem: if the norm of `f` is bounded by a real function `a` which
tends to `0`, then `f` tends to `1`. -/
@[to_additive "Special case of the sandwich theorem: if the norm of `f` is bounded by a real
function `a` which tends to `0`, then `f` tends to `0`."]
lemma squeeze_one_norm {f : α → E} {a : α → ℝ} {t₀ : filter α} (h : ∀ n, ∥f n∥ ≤ a n) :
  tendsto a t₀ (𝓝 0) → tendsto f t₀ (𝓝 1) :=
squeeze_one_norm' $ eventually_of_forall h

@[to_additive] lemma tendsto_norm_div_self (x : E) : tendsto (λ a, ∥a / x∥) (𝓝 x) (𝓝 0) :=
by simpa [dist_eq_norm_div] using
  tendsto_id.dist (tendsto_const_nhds : tendsto (λ a, (x:E)) (𝓝 x) _)

@[to_additive tendsto_norm]lemma tendsto_norm' {x : E} : tendsto (λ a, ∥a∥) (𝓝 x) (𝓝 ∥x∥) :=
by simpa using tendsto_id.dist (tendsto_const_nhds : tendsto (λ a, (1:E)) _ _)

@[to_additive] lemma tendsto_norm_one : tendsto (λ a : E, ∥a∥) (𝓝 1) (𝓝 0) :=
by simpa using tendsto_norm_div_self (1:E)

@[continuity, to_additive continuous_norm] lemma continuous_norm' : continuous (λ a : E, ∥a∥) :=
by simpa using continuous_id.dist (continuous_const : continuous (λ a, (1:E)))

@[continuity, to_additive continuous_nnnorm]
lemma continuous_nnnorm' : continuous (λ (a : E), ∥a∥₊) :=
continuous_subtype_mk _ continuous_norm'

@[to_additive] lemma lipschitz_with_one_norm : lipschitz_with 1 (norm : E → ℝ) :=
by simpa only [dist_one_left] using lipschitz_with.dist_right (1 : E)

@[to_additive] lemma lipschitz_with_one_nnnorm : lipschitz_with 1 (has_nnnorm.nnnorm : E → ℝ≥0) :=
lipschitz_with_one_norm

@[to_additive uniform_continuous_norm]
lemma uniform_continuous_norm' : uniform_continuous (norm : E → ℝ) :=
lipschitz_with_one_norm.uniform_continuous

@[to_additive uniform_continuous_nnnorm]
lemma uniform_continuous_nnnorm' : uniform_continuous (λ (a : E), ∥a∥₊) :=
uniform_continuous_subtype_mk uniform_continuous_norm' _

/-- A helper lemma used to prove that the (scalar or usual) product of a function that tends to one
and a bounded function tends to one. This lemma is formulated for any binary operation
`op : E → F → G` with an estimate `∥op x y∥ ≤ A * ∥x∥ * ∥y∥` for some constant A instead of
multiplication so that it can be applied to `(*)`, `flip (*)`, `(•)`, and `flip (•)`. -/
@[to_additive "A helper lemma used to prove that the (scalar or usual) product of a function that
tends to zero and a bounded function tends to zero. This lemma is formulated for any binary
operation `op : E → F → G` with an estimate `∥op x y∥ ≤ A * ∥x∥ * ∥y∥` for some constant A instead
of multiplication so that it can be applied to `(*)`, `flip (*)`, `(•)`, and `flip (•)`."]
lemma filter.tendsto.op_one_is_bounded_under_le' {f : α → E} {g : α → F} {l : filter α}
  (hf : tendsto f l (𝓝 1)) (hg : is_bounded_under (≤) l (norm ∘ g)) (op : E → F → G)
  (h_op : ∃ A, ∀ x y, ∥op x y∥ ≤ A * ∥x∥ * ∥y∥) :
  tendsto (λ x, op (f x) (g x)) l (𝓝 1) :=
begin
  cases h_op with A h_op,
  rcases hg with ⟨C, hC⟩, rw eventually_map at hC,
  rw normed_comm_group.tendsto_nhds_one at hf ⊢,
  intros ε ε₀,
  rcases exists_pos_mul_lt ε₀ (A * C) with ⟨δ, δ₀, hδ⟩,
  filter_upwards [hf δ δ₀, hC] with i hf hg,
  refine (h_op _ _).trans_lt _,
  cases le_total A 0 with hA hA,
  { exact (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hA $ norm_nonneg' _) $
      norm_nonneg' _).trans_lt ε₀ },
  calc A * ∥f i∥ * ∥g i∥ ≤ A * δ * C :
    mul_le_mul (mul_le_mul_of_nonneg_left hf.le hA) hg (norm_nonneg' _) (mul_nonneg hA δ₀.le)
  ... = A * C * δ : mul_right_comm _ _ _
  ... < ε : hδ,
end

/-- A helper lemma used to prove that the (scalar or usual) product of a function that tends to one
and a bounded function tends to one. This lemma is formulated for any binary operation
`op : E → F → G` with an estimate `∥op x y∥ ≤ ∥x∥ * ∥y∥` instead of multiplication so that it
can be applied to `(*)`, `flip (*)`, `(•)`, and `flip (•)`. -/
@[to_additive "A helper lemma used to prove that the (scalar or usual) product of a function that
tends to zero and a bounded function tends to zero. This lemma is formulated for any binary
operation `op : E → F → G` with an estimate `∥op x y∥ ≤ ∥x∥ * ∥y∥` instead of multiplication so that
it can be applied to `(*)`, `flip (*)`, `(•)`, and `flip (•)`."]
lemma filter.tendsto.op_one_is_bounded_under_le {f : α → E} {g : α → F} {l : filter α}
  (hf : tendsto f l (𝓝 1)) (hg : is_bounded_under (≤) l (norm ∘ g)) (op : E → F → G)
  (h_op : ∀ x y, ∥op x y∥ ≤ ∥x∥ * ∥y∥) :
  tendsto (λ x, op (f x) (g x)) l (𝓝 1) :=
hf.op_one_is_bounded_under_le' hg op ⟨1, λ x y, (one_mul (∥x∥)).symm ▸ h_op x y⟩

section
variables {l : filter α} {f : α → E}

@[to_additive filter.tendsto.norm] lemma filter.tendsto.norm' (h : tendsto f l (𝓝 a)) :
  tendsto (λ x, ∥f x∥) l (𝓝 ∥a∥) :=
tendsto_norm'.comp h

@[to_additive filter.tendsto.nnnorm] lemma filter.tendsto.nnnorm' (h : tendsto f l (𝓝 a)) :
  tendsto (λ x, ∥f x∥₊) l (𝓝 (∥a∥₊)) :=
tendsto.comp continuous_nnnorm'.continuous_at h

end

section
variables [topological_space α] {f : α → E}

@[to_additive continuous.norm] lemma continuous.norm' : continuous f → continuous (λ x, ∥f x∥) :=
continuous_norm'.comp

@[to_additive continuous.nnnorm]
lemma continuous.nnnorm' : continuous f → continuous (λ x, ∥f x∥₊) := continuous_nnnorm'.comp

@[to_additive continuous_at.norm]
lemma continuous_at.norm' {a : α} (h : continuous_at f a) : continuous_at (λ x, ∥f x∥) a := h.norm'

@[to_additive continuous_at.nnnorm]
lemma continuous_at.nnnorm' {a : α} (h : continuous_at f a) : continuous_at (λ x, ∥f x∥₊) a :=
h.nnnorm'

@[to_additive continuous_within_at.norm]
lemma continuous_within_at.norm' {s : set α} {a : α} (h : continuous_within_at f s a) :
  continuous_within_at (λ x, ∥f x∥) s a :=
h.norm'

@[to_additive continuous_within_at.nnnorm]
lemma continuous_within_at.nnnorm' {s : set α} {a : α} (h : continuous_within_at f s a) :
  continuous_within_at (λ x, ∥f x∥₊) s a :=
h.nnnorm'

@[to_additive continuous_on.norm]
lemma continuous_on.norm' {s : set α} (h : continuous_on f s) : continuous_on (λ x, ∥f x∥) s :=
λ x hx, (h x hx).norm'

@[to_additive continuous_on.nnnorm]
lemma continuous_on.nnnorm' {s : set α} (h : continuous_on f s) : continuous_on (λ x, ∥f x∥₊) s :=
λ x hx, (h x hx).nnnorm'

end

/-- If `∥y∥ → ∞`, then we can assume `y ≠ x` for any fixed `x`. -/
@[to_additive eventually_ne_of_tendsto_norm_at_top "If `∥y∥→∞`, then we can assume `y≠x` for any
fixed `x`"]
lemma eventually_ne_of_tendsto_norm_at_top' {l : filter α} {f : α → E}
  (h : tendsto (λ y, ∥f y∥) l at_top) (x : E) :
  ∀ᶠ y in l, f y ≠ x :=
(h.eventually_ne_at_top _).mono $ λ x, ne_of_apply_ne norm

@[to_additive] lemma seminormed_comm_group.mem_closure_iff :
  a ∈ closure s ↔ ∀ ε, 0 < ε → ∃ b ∈ s, ∥a / b∥ < ε :=
by simp [metric.mem_closure_iff, dist_eq_norm_div]

@[to_additive norm_le_zero_iff'] lemma norm_le_zero_iff''' [t0_space E] {a : E} : ∥a∥ ≤ 0 ↔ a = 1 :=
begin
  letI : normed_group E :=
    { to_metric_space := metric.of_t0_pseudo_metric_space E, ..‹seminormed_group E› },
  rw [←dist_one_right, dist_le_zero],
end

@[to_additive norm_eq_zero'] lemma norm_eq_zero''' [t0_space E] {a : E} : ∥a∥ = 0 ↔ a = 1 :=
(norm_nonneg' a).le_iff_eq.symm.trans norm_le_zero_iff'''

@[to_additive norm_pos_iff'] lemma norm_pos_iff''' [t0_space E] {a : E} : 0 < ∥a∥ ↔ a ≠ 1 :=
by rw [← not_le, norm_le_zero_iff''']

end seminormed_group

section induced

/-- A group homomorphism from a `group` to a `seminormed_group` induces a `seminormed_group`
structure on the domain. -/
@[reducible, -- See note [reducible non-instances]
to_additive "A group homomorphism from an `add_group` to a `seminormed_add_group` induces a
`seminormed_add_group` structure on the domain."]
def seminormed_group.induced [group E] [seminormed_group F] (f : E →* F) : seminormed_group E :=
{ norm := λ x, ∥f x∥,
  dist_eq := λ x y, by simpa only [monoid_hom.map_div, ←dist_eq_norm_div],
  ..pseudo_metric_space.induced f _ }

/-- A group homomorphism from a `comm_group` to a `seminormed_group` induces a
`seminormed_comm_group` structure on the domain. -/
@[reducible, -- See note [reducible non-instances]
to_additive "A group homomorphism from an `add_comm_group` to a `seminormed_add_group` induces a
`seminormed_add_comm_group` structure on the domain."]
def seminormed_comm_group.induced [comm_group E] [seminormed_group F] (f : E →* F) :
  seminormed_comm_group E :=
{ ..seminormed_group.induced f }

/-- An injective group homomorphism from a `group` to a `normed_group` induces a `normed_group`
structure on the domain. -/
@[reducible,  -- See note [reducible non-instances].
to_additive "An injective group homomorphism from an `add_group` to a `normed_add_group` induces a
`normed_add_group` structure on the domain."]
def normed_group.induced [group E] [normed_group F] (f : E →* F) (h : injective f) :
  normed_group E :=
{ ..seminormed_group.induced f, ..metric_space.induced f h _ }

/-- An injective group homomorphism from an `comm_group` to a `normed_group` induces a
`normed_comm_group` structure on the domain. -/
@[reducible,  -- See note [reducible non-instances].
to_additive "An injective group homomorphism from an `comm_group` to a `normed_comm_group` induces a
`normed_comm_group` structure on the domain."]
def normed_comm_group.induced [comm_group E] [normed_group F] (f : E →* F) (h : injective f) :
  normed_comm_group E :=
{ ..seminormed_group.induced f, ..metric_space.induced f h _ }

end induced

section seminormed_comm_group
variables [seminormed_comm_group E] [seminormed_comm_group F] {a a₁ a₂ b b₁ b₂ : E} {r r₁ r₂ : ℝ}

@[simp, to_additive] lemma dist_mul_left (a b₁ b₂ : E) : dist (a * b₁) (a * b₂) = dist b₁ b₂ :=
by simp [dist_eq_norm_div]

@[to_additive] lemma dist_inv (x y : E) : dist x⁻¹ y = dist x y⁻¹ :=
by simp_rw [dist_eq_norm_div, ←norm_inv' (x⁻¹ / y), inv_div, div_inv_eq_mul, mul_comm]

@[simp, to_additive] lemma dist_inv_inv (a b : E) : dist a⁻¹ b⁻¹ = dist a b :=
by rw [dist_inv, inv_inv]

@[simp, to_additive] lemma dist_div_left (a b₁ b₂ : E) : dist (a / b₁) (a / b₂) = dist b₁ b₂ :=
by simp only [div_eq_mul_inv, dist_mul_left, dist_inv_inv]

@[simp, to_additive] lemma dist_self_mul_right (a b : E) : dist a (a * b) = ∥b∥ :=
by rw [←dist_one_left, ←dist_mul_left a 1 b, mul_one]

@[simp, to_additive] lemma dist_self_mul_left (a b : E) : dist (a * b) a = ∥b∥ :=
by rw [dist_comm, dist_self_mul_right]

@[simp, to_additive] lemma dist_self_div_right (a b : E) : dist a (a / b) = ∥b∥ :=
by rw [div_eq_mul_inv, dist_self_mul_right, norm_inv']

@[simp, to_additive] lemma dist_self_div_left (a b : E) : dist (a / b) a = ∥b∥ :=
by rw [dist_comm, dist_self_div_right]

@[to_additive] lemma dist_mul_mul_le (a₁ a₂ b₁ b₂ : E) :
  dist (a₁ * a₂) (b₁ * b₂) ≤ dist a₁ b₁ + dist a₂ b₂ :=
by simpa only [dist_mul_left, dist_mul_right] using dist_triangle (a₁ * a₂) (b₁ * a₂) (b₁ * b₂)

@[to_additive] lemma dist_mul_mul_le_of_le (h₁ : dist a₁ b₁ ≤ r₁) (h₂ : dist a₂ b₂ ≤ r₂) :
  dist (a₁ * a₂) (b₁ * b₂) ≤ r₁ + r₂ :=
(dist_mul_mul_le a₁ a₂ b₁ b₂).trans $ add_le_add h₁ h₂

@[to_additive] lemma dist_div_div_le (a₁ a₂ b₁ b₂ : E) :
  dist (a₁ / a₂) (b₁ / b₂) ≤ dist a₁ b₁ + dist a₂ b₂ :=
by simpa only [div_eq_mul_inv, dist_inv_inv] using dist_mul_mul_le a₁ a₂⁻¹ b₁ b₂⁻¹

@[to_additive] lemma dist_div_div_le_of_le (h₁ : dist a₁ b₁ ≤ r₁) (h₂ : dist a₂ b₂ ≤ r₂) :
  dist (a₁ / a₂) (b₁ / b₂) ≤ r₁ + r₂ :=
(dist_div_div_le a₁ a₂ b₁ b₂).trans $ add_le_add h₁ h₂

@[to_additive] lemma abs_dist_sub_le_dist_mul_mul (a₁ a₂ b₁ b₂ : E) :
  |dist a₁ b₁ - dist a₂ b₂| ≤ dist (a₁ * a₂) (b₁ * b₂) :=
by simpa only [dist_mul_left, dist_mul_right, dist_comm b₂]
  using abs_dist_sub_le (a₁ * a₂) (b₁ * b₂) (b₁ * a₂)

lemma norm_sum_le {E} [seminormed_add_comm_group E] (s : finset ι) (f : ι → E) :
  ∥∑ i in s, f i∥ ≤ ∑ i in s, ∥f i∥ :=
s.le_sum_of_subadditive norm norm_zero norm_add_le f

@[to_additive] lemma norm_prod_le (s : finset ι) (f : ι → E) : ∥∏ i in s, f i∥ ≤ ∑ i in s, ∥f i∥ :=
begin
  rw [←multiplicative.of_add_le, finset.of_add_sum],
  refine finset.le_prod_of_submultiplicative (multiplicative.of_add ∘ norm) _ (λ x y, _) _ _,
  { simp only [comp_app, norm_one', of_add_zero] },
  { exact norm_mul_le' _ _ }
end

@[to_additive]
lemma norm_prod_le_of_le (s : finset ι) {f : ι → E} {n : ι → ℝ} (h : ∀ b ∈ s, ∥f b∥ ≤ n b) :
  ∥∏ b in s, f b∥ ≤ ∑ b in s, n b :=
(norm_prod_le s f).trans $ finset.sum_le_sum h

@[to_additive] lemma dist_prod_prod_le_of_le (s : finset ι) {f a : ι → E} {d : ι → ℝ}
  (h : ∀ b ∈ s, dist (f b) (a b) ≤ d b) :
  dist (∏ b in s, f b) (∏ b in s, a b) ≤ ∑ b in s, d b :=
by { simp only [dist_eq_norm_div, ← finset.prod_div_distrib] at *, exact norm_prod_le_of_le s h }

@[to_additive] lemma dist_prod_prod_le (s : finset ι) (f a : ι → E) :
  dist (∏ b in s, f b) (∏ b in s, a b) ≤ ∑ b in s, dist (f b) (a b) :=
dist_prod_prod_le_of_le s $ λ _ _, le_rfl

@[to_additive] lemma mul_mem_ball_iff_norm : a * b ∈ ball a r ↔ ∥b∥ < r :=
by rw [mem_ball_iff_norm'', mul_div_cancel''']

@[to_additive] lemma mul_mem_closed_ball_iff_norm : a * b ∈ closed_ball a r ↔ ∥b∥ ≤ r :=
by rw [mem_closed_ball_iff_norm'', mul_div_cancel''']

@[simp, to_additive] lemma preimage_mul_ball (a b : E) (r : ℝ) :
  ((*) b) ⁻¹' ball a r = ball (a / b) r :=
by { ext c, simp only [dist_eq_norm_div, set.mem_preimage, mem_ball, div_div_eq_mul_div, mul_comm] }

@[simp, to_additive] lemma preimage_mul_closed_ball (a b : E) (r : ℝ) :
  ((*) b) ⁻¹' (closed_ball a r) = closed_ball (a / b) r :=
by { ext c,
  simp only [dist_eq_norm_div, set.mem_preimage, mem_closed_ball, div_div_eq_mul_div, mul_comm] }

@[simp, to_additive] lemma preimage_mul_sphere (a b : E) (r : ℝ) :
  ((*) b) ⁻¹' sphere a r = sphere (a / b) r :=
by { ext c, simp only [set.mem_preimage, mem_sphere_iff_norm', div_div_eq_mul_div, mul_comm] }

namespace isometric

/-- Multiplication `y ↦ x * y` as an `isometry`. -/
@[to_additive "Addition `y ↦ x + y` as an `isometry`"]
protected def mul_left (x : E) : E ≃ᵢ E :=
{ isometry_to_fun := isometry.of_dist_eq $ λ y z, dist_mul_left _ _ _,
  to_equiv := equiv.mul_left x }

@[simp, to_additive] lemma mul_left_to_equiv (x : E) :
  (isometric.mul_left x).to_equiv = equiv.mul_left x := rfl

@[simp, to_additive] lemma coe_mul_left (x : E) : ⇑(isometric.mul_left x) = (*) x := rfl

@[simp, to_additive] lemma mul_left_symm (x : E) :
  (isometric.mul_left x).symm = isometric.mul_left x⁻¹ :=
ext $ λ y, rfl

variables (E)

/-- Inversion `x ↦ x⁻¹` as an `isometry`. -/
@[to_additive "Negation `x ↦ -x` as an `isometry`."] protected def inv : E ≃ᵢ E :=
{ isometry_to_fun := isometry.of_dist_eq $ λ x y, dist_inv_inv _ _,
  to_equiv := equiv.inv E }

variables {E}

@[simp, to_additive] lemma inv_symm : (isometric.inv E).symm = isometric.inv E := rfl
@[simp, to_additive] lemma inv_to_equiv : (isometric.inv E).to_equiv = equiv.inv E := rfl
@[simp, to_additive] lemma coe_inv : ⇑(isometric.inv E) = has_inv.inv := rfl

end isometric

open finset

@[to_additive] lemma controlled_prod_of_mem_closure {s : subgroup E} (hg : a ∈ closure (s : set E))
  {b : ℕ → ℝ} (b_pos : ∀ n, 0 < b n) :
  ∃ v : ℕ → E,
    tendsto (λ n, ∏ i in range (n+1), v i) at_top (𝓝 a) ∧
    (∀ n, v n ∈ s) ∧
    ∥v 0 / a∥ < b 0 ∧
    ∀ n, 0 < n → ∥v n∥ < b n :=
begin
  obtain ⟨u : ℕ → E, u_in : ∀ n, u n ∈ s, lim_u : tendsto u at_top (𝓝 a)⟩ :=
    mem_closure_iff_seq_limit.mp hg,
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, ∀ n ≥ n₀, ∥u n / a∥ < b 0,
  { have : {x | ∥x / a∥ < b 0} ∈ 𝓝 a,
    { simp_rw ← dist_eq_norm_div,
      exact metric.ball_mem_nhds _ (b_pos _) },
    exact filter.tendsto_at_top'.mp lim_u _ this },
  set z : ℕ → E := λ n, u (n + n₀),
  have lim_z : tendsto z at_top (𝓝 a) := lim_u.comp (tendsto_add_at_top_nat n₀),
  have mem_𝓤 : ∀ n, {p : E × E | ∥p.1 / p.2∥ < b (n + 1)} ∈ 𝓤 E :=
  λ n, by simpa [← dist_eq_norm_div] using metric.dist_mem_uniformity (b_pos $ n+1),
  obtain ⟨φ : ℕ → ℕ, φ_extr : strict_mono φ,
          hφ : ∀ n, ∥z (φ $ n + 1) / z (φ n)∥ < b (n + 1)⟩ :=
    lim_z.cauchy_seq.subseq_mem mem_𝓤,
  set w : ℕ → E := z ∘ φ,
  have hw : tendsto w at_top (𝓝 a),
    from lim_z.comp φ_extr.tendsto_at_top,
  set v : ℕ → E := λ i, if i = 0 then w 0 else w i / w (i - 1),
  refine ⟨v, tendsto.congr (finset.eq_prod_range_div' w) hw , _,
          hn₀ _ (n₀.le_add_left _), _⟩,
  { rintro ⟨⟩,
    { change w 0 ∈ s,
      apply u_in },
    { apply s.div_mem ; apply u_in }, },
  { intros l hl,
    obtain ⟨k, rfl⟩ : ∃ k, l = k+1, exact nat.exists_eq_succ_of_ne_zero hl.ne',
    apply hφ }
end

@[to_additive] lemma controlled_prod_of_mem_closure_range {j : E →* F} {b : F}
  (hb : b ∈ closure (j.range : set F)) {f : ℕ → ℝ} (b_pos : ∀ n, 0 < f n) :
  ∃ a : ℕ → E,
    tendsto (λ n, ∏ i in range (n + 1), j (a i)) at_top (𝓝 b) ∧
    ∥j (a 0) / b∥ < f 0 ∧
    ∀ n, 0 < n → ∥j (a n)∥ < f n :=
begin
  obtain ⟨v, sum_v, v_in, hv₀, hv_pos⟩ := controlled_prod_of_mem_closure hb b_pos,
  choose g hg using v_in,
  refine ⟨g, by simpa [← hg] using sum_v, by simpa [hg 0] using hv₀, λ n hn,
          by simpa [hg] using hv_pos n hn⟩,
end

@[to_additive] lemma nndist_mul_mul_le (a₁ a₂ b₁ b₂ : E) :
  nndist (a₁ * a₂) (b₁ * b₂) ≤ nndist a₁ b₁ + nndist a₂ b₂ :=
nnreal.coe_le_coe.1 $ dist_mul_mul_le a₁ a₂ b₁ b₂

@[to_additive]
lemma edist_mul_mul_le (a₁ a₂ b₁ b₂ : E) : edist (a₁ * a₂) (b₁ * b₂) ≤ edist a₁ b₁ + edist a₂ b₂ :=
by { simp only [edist_nndist], norm_cast, apply nndist_mul_mul_le }

@[simp, to_additive] lemma edist_mul_left (a b₁ b₂ : E) : edist (a * b₁) (a * b₂) = edist b₁ b₂ :=
by simp [edist_dist]

@[to_additive]
lemma edist_inv (a b : E) : edist a⁻¹ b = edist a b⁻¹ := by simp_rw [edist_dist, dist_inv]

@[simp, to_additive] lemma edist_inv_inv (x y : E) : edist x⁻¹ y⁻¹ = edist x y :=
by rw [edist_inv, inv_inv]

@[simp, to_additive] lemma edist_div_left (a b₁ b₂ : E) : edist (a / b₁) (a / b₂) = edist b₁ b₂ :=
by simp only [div_eq_mul_inv, edist_mul_left, edist_inv_inv]

@[to_additive] lemma nnnorm_prod_le (s : finset ι) (f : ι → E) :
  ∥∏ a in s, f a∥₊ ≤ ∑ a in s, ∥f a∥₊ :=
nnreal.coe_le_coe.1 $ by { push_cast, exact norm_prod_le _ _ }

@[to_additive]
lemma nnnorm_prod_le_of_le (s : finset ι) {f : ι → E} {n : ι → ℝ≥0} (h : ∀ b ∈ s, ∥f b∥₊ ≤ n b) :
  ∥∏ b in s, f b∥₊ ≤ ∑ b in s, n b :=
(norm_prod_le_of_le s h).trans_eq nnreal.coe_sum.symm

namespace lipschitz_with
variables [pseudo_emetric_space α] {K Kf Kg : ℝ≥0} {f g : α → E}

@[to_additive] lemma inv (hf : lipschitz_with K f) : lipschitz_with K (λ x, (f x)⁻¹) :=
λ x y, (edist_inv_inv _ _).trans_le $ hf x y

@[to_additive add] lemma mul' (hf : lipschitz_with Kf f) (hg : lipschitz_with Kg g) :
  lipschitz_with (Kf + Kg) (λ x, f x * g x) :=
λ x y, calc
  edist (f x * g x) (f y * g y) ≤ edist (f x) (f y) + edist (g x) (g y) : edist_mul_mul_le _ _ _ _
... ≤ Kf * edist x y + Kg * edist x y : add_le_add (hf x y) (hg x y)
... = (Kf + Kg) * edist x y : (add_mul _ _ _).symm

@[to_additive] lemma div (hf : lipschitz_with Kf f) (hg : lipschitz_with Kg g) :
  lipschitz_with (Kf + Kg) (λ x, f x / g x) :=
by simpa only [div_eq_mul_inv] using hf.mul' hg.inv

end lipschitz_with

namespace antilipschitz_with
variables [pseudo_emetric_space α] {K Kf Kg : ℝ≥0} {f g : α → E}

@[to_additive] lemma mul_lipschitz_with (hf : antilipschitz_with Kf f) (hg : lipschitz_with Kg g)
  (hK : Kg < Kf⁻¹) : antilipschitz_with (Kf⁻¹ - Kg)⁻¹ (λ x, f x * g x) :=
begin
  letI : pseudo_metric_space α := pseudo_emetric_space.to_pseudo_metric_space hf.edist_ne_top,
  refine antilipschitz_with.of_le_mul_dist (λ x y, _),
  rw [nnreal.coe_inv, ← div_eq_inv_mul],
  rw le_div_iff (nnreal.coe_pos.2 $ tsub_pos_iff_lt.2 hK),
  rw [mul_comm, nnreal.coe_sub hK.le, sub_mul],
  calc ↑Kf⁻¹ * dist x y - Kg * dist x y ≤ dist (f x) (f y) - dist (g x) (g y) :
    sub_le_sub (hf.mul_le_dist x y) (hg.dist_le_mul x y)
  ... ≤ _ : le_trans (le_abs_self _) (abs_dist_sub_le_dist_mul_mul _ _ _ _),
end

@[to_additive] lemma mul_div_lipschitz_with (hf : antilipschitz_with Kf f)
  (hg : lipschitz_with Kg (g / f)) (hK : Kg < Kf⁻¹) : antilipschitz_with (Kf⁻¹ - Kg)⁻¹ g :=
by simpa only [pi.div_apply, mul_div_cancel'_right] using hf.mul_lipschitz_with hg hK

@[to_additive] lemma le_mul_norm_div {f : E → F} (hf : antilipschitz_with K f) (x y : E) :
  ∥x / y∥ ≤ K * ∥f x / f y∥ :=
by simp [← dist_eq_norm_div, hf.le_mul_dist x y]

end antilipschitz_with

@[priority 100, to_additive] -- See note [lower instance priority]
instance seminormed_comm_group.to_has_lipschitz_mul : has_lipschitz_mul E :=
⟨⟨1 + 1, lipschitz_with.prod_fst.mul' lipschitz_with.prod_snd⟩⟩

/-- A seminormed group is a uniform group, i.e., multiplication and division are uniformly
continuous. -/
@[priority 100, to_additive "A seminormed group is a uniform additive group, i.e., addition and
subtraction are uniformly continuous."] -- See note [lower instance priority]
instance seminormed_comm_group.to_uniform_group : uniform_group E :=
⟨(lipschitz_with.prod_fst.div lipschitz_with.prod_snd).uniform_continuous⟩

 -- short-circuit type class inference
@[priority 100, to_additive] -- See note [lower instance priority]
instance seminormed_comm_group.to_topological_group : topological_group E := infer_instance

@[to_additive] lemma cauchy_seq_prod_of_eventually_eq {u v : ℕ → E} {N : ℕ}
  (huv : ∀ n ≥ N, u n = v n) (hv : cauchy_seq (λ n, ∏ k in range (n+1), v k)) :
  cauchy_seq (λ n, ∏ k in range (n + 1), u k) :=
begin
  let d : ℕ → E := λ n, ∏ k in range (n + 1), (u k / v k),
  rw show (λ n, ∏ k in range (n + 1), u k) = d * (λ n, ∏ k in range (n + 1), v k),
    by { ext n, simp [d] },
  suffices : ∀ n ≥ N, d n = d N,
  { exact (tendsto_at_top_of_eventually_const this).cauchy_seq.mul hv },
  intros n hn,
  dsimp [d],
  rw eventually_constant_prod _ hn,
  intros m hm,
  simp [huv m hm],
end

end seminormed_comm_group

section normed_group
variables [normed_group E] [normed_group F] {a b : E}

@[simp, to_additive norm_eq_zero] lemma norm_eq_zero'' : ∥a∥ = 0 ↔ a = 1 := norm_eq_zero'''

@[to_additive norm_ne_zero_iff] lemma norm_ne_zero_iff' : ∥a∥ ≠ 0 ↔ a ≠ 1 := norm_eq_zero''.not

@[simp, to_additive norm_pos_iff] lemma norm_pos_iff'' : 0 < ∥a∥ ↔ a ≠ 1 := norm_pos_iff'''

@[simp, to_additive norm_le_zero_iff]
lemma norm_le_zero_iff'' : ∥a∥ ≤ 0 ↔ a = 1 := norm_le_zero_iff'''

@[to_additive]
lemma norm_div_eq_zero_iff : ∥a / b∥ = 0 ↔ a = b := by rw [norm_eq_zero'', div_eq_one]

@[to_additive] lemma norm_div_pos_iff : 0 < ∥a / b∥ ↔ a ≠ b :=
by { rw [(norm_nonneg' _).lt_iff_ne, ne_comm], exact norm_div_eq_zero_iff.not }

@[to_additive] lemma eq_of_norm_div_le_zero (h : ∥a / b∥ ≤ 0) : a = b :=
by rwa [←div_eq_one, ← norm_le_zero_iff'']

alias norm_div_eq_zero_iff ↔ eq_of_norm_div_eq_zero _

attribute [to_additive] eq_of_norm_div_eq_zero

@[simp, to_additive nnnorm_eq_zero] lemma nnnorm_eq_zero' : ∥a∥₊ = 0 ↔ a = 1 :=
by rw [← nnreal.coe_eq_zero, coe_nnnorm', norm_eq_zero'']

@[to_additive nnnorm_ne_zero_iff]
lemma nnnorm_ne_zero_iff' : ∥a∥₊ ≠ 0 ↔ a ≠ 1 := nnnorm_eq_zero'.not

@[to_additive]
lemma tendsto_norm_div_self_punctured_nhds (a : E) : tendsto (λ x, ∥x / a∥) (𝓝[≠] a) (𝓝[>] 0) :=
(tendsto_norm_div_self a).inf $ tendsto_principal_principal.2 $ λ x hx, norm_pos_iff''.2 $
  div_ne_one.2 hx

@[to_additive] lemma tendsto_norm_nhds_within_one : tendsto (norm : E → ℝ) (𝓝[≠] 1) (𝓝[>] 0) :=
tendsto_norm_one.inf $ tendsto_principal_principal.2 $ λ x, norm_pos_iff''.2

end normed_group

section normed_add_group
variables [normed_add_group E] [topological_space α] {f : α → E}

/-! Some relations with `has_compact_support` -/

lemma has_compact_support_norm_iff : has_compact_support (λ x, ∥f x∥) ↔ has_compact_support f :=
has_compact_support_comp_left $ λ x, norm_eq_zero

alias has_compact_support_norm_iff ↔ _ has_compact_support.norm

lemma continuous.bounded_above_of_compact_support (hf : continuous f) (h : has_compact_support f) :
  ∃ C, ∀ x, ∥f x∥ ≤ C :=
by simpa [bdd_above_def] using hf.norm.bdd_above_range_of_has_compact_support h.norm

end normed_add_group

/-! ### `ulift` -/

namespace ulift
section has_norm
variables [has_norm E]

instance : has_norm (ulift E) := ⟨λ x, ∥x.down∥⟩

lemma norm_def (x : ulift E) : ∥x∥ = ∥x.down∥ := rfl
@[simp] lemma norm_up (x : E) : ∥ulift.up x∥ = ∥x∥ := rfl
@[simp] lemma norm_down (x : ulift E) : ∥x.down∥ = ∥x∥ := rfl

end has_norm

section has_nnnorm
variables [has_nnnorm E]

instance : has_nnnorm (ulift E) := ⟨λ x, ∥x.down∥₊⟩

lemma nnnorm_def (x : ulift E) : ∥x∥₊ = ∥x.down∥₊ := rfl
@[simp] lemma nnnorm_up (x : E) : ∥ulift.up x∥₊ = ∥x∥₊ := rfl
@[simp] lemma nnnorm_down (x : ulift E) : ∥x.down∥₊ = ∥x∥₊ := rfl

end has_nnnorm

@[to_additive] instance seminormed_group [seminormed_group E] : seminormed_group (ulift E) :=
seminormed_group.induced ⟨ulift.down, rfl, λ _ _, rfl⟩

@[to_additive]
instance seminormed_comm_group [seminormed_comm_group E] : seminormed_comm_group (ulift E) :=
seminormed_comm_group.induced ⟨ulift.down, rfl, λ _ _, rfl⟩

@[to_additive] instance normed_group [normed_group E] : normed_group (ulift E) :=
normed_group.induced ⟨ulift.down, rfl, λ _ _, rfl⟩ down_injective

@[to_additive]
instance normed_comm_group [normed_comm_group E] : normed_comm_group (ulift E) :=
normed_comm_group.induced ⟨ulift.down, rfl, λ _ _, rfl⟩ down_injective

end ulift

/-! ### `additive`, `multiplicative` -/

section additive_multiplicative

open additive multiplicative

section has_norm
variables [has_norm E]

instance : has_norm (additive E) := ‹has_norm E›
instance : has_norm (multiplicative E) := ‹has_norm E›

@[simp] lemma norm_to_mul (x) : ∥(to_mul x : E)∥ = ∥x∥ := rfl
@[simp] lemma norm_of_mul (x : E) : ∥of_mul x∥ = ∥x∥ := rfl
@[simp] lemma norm_to_add (x) : ∥(to_add x : E)∥ = ∥x∥ := rfl
@[simp] lemma norm_of_add (x : E) : ∥of_add x∥ = ∥x∥ := rfl

end has_norm

section has_nnnorm
variables [has_nnnorm E]

instance : has_nnnorm (additive E) := ‹has_nnnorm E›
instance : has_nnnorm (multiplicative E) := ‹has_nnnorm E›

@[simp] lemma nnnorm_to_mul (x) : ∥(to_mul x : E)∥₊ = ∥x∥₊ := rfl
@[simp] lemma nnnorm_of_mul (x : E) : ∥of_mul x∥₊ = ∥x∥₊ := rfl
@[simp] lemma nnnorm_to_add (x) : ∥(to_add x : E)∥₊ = ∥x∥₊ := rfl
@[simp] lemma nnnorm_of_add (x : E) : ∥of_add x∥₊ = ∥x∥₊ := rfl

end has_nnnorm

instance [seminormed_group E] : seminormed_add_group (additive E) :=
{ dist_eq := dist_eq_norm_div }

instance [seminormed_add_group E] : seminormed_group (multiplicative E) :=
{ dist_eq := dist_eq_norm_sub }

instance [seminormed_comm_group E] : seminormed_add_comm_group (additive E) :=
{ ..additive.seminormed_add_group }

instance [seminormed_add_comm_group E] : seminormed_comm_group (multiplicative E) :=
{ ..multiplicative.seminormed_group }

instance [normed_group E] : normed_add_group (additive E) :=
{ ..additive.seminormed_add_group }

instance [normed_add_group E] : normed_group (multiplicative E) :=
{ ..multiplicative.seminormed_group }

instance [normed_comm_group E] : normed_add_comm_group (additive E) :=
{ ..additive.seminormed_add_group }

instance [normed_add_comm_group E] : normed_comm_group (multiplicative E) :=
{ ..multiplicative.seminormed_group }

end additive_multiplicative

/-! ### Order dual -/

section order_dual

open order_dual

section has_norm
variables [has_norm E]

instance : has_norm Eᵒᵈ := ‹has_norm E›

@[simp] lemma norm_to_dual (x : E) : ∥to_dual x∥ = ∥x∥ := rfl
@[simp] lemma norm_of_dual (x : Eᵒᵈ) : ∥of_dual x∥ = ∥x∥ := rfl

end has_norm

section has_nnnorm
variables [has_nnnorm E]

instance : has_nnnorm Eᵒᵈ := ‹has_nnnorm E›

@[simp] lemma nnnorm_to_dual (x : E) : ∥to_dual x∥₊ = ∥x∥₊ := rfl
@[simp] lemma nnnorm_of_dual (x : Eᵒᵈ) : ∥of_dual x∥₊ = ∥x∥₊ := rfl

end has_nnnorm

@[priority 100, to_additive] -- See note [lower instance priority]
instance [seminormed_group E] : seminormed_group Eᵒᵈ := ‹seminormed_group E›

@[priority 100, to_additive] -- See note [lower instance priority]
instance [seminormed_comm_group E] : seminormed_comm_group Eᵒᵈ := ‹seminormed_comm_group E›

@[priority 100, to_additive] -- See note [lower instance priority]
instance [normed_group E] : normed_group Eᵒᵈ := ‹normed_group E›

@[priority 100, to_additive] -- See note [lower instance priority]
instance [normed_comm_group E] : normed_comm_group Eᵒᵈ := ‹normed_comm_group E›

end order_dual

/-! ### Binary product of normed groups -/

section has_norm
variables [has_norm E] [has_norm F] {x : E × F} {r : ℝ}

noncomputable instance : has_norm (E × F) := ⟨λ x, max ∥x.1∥ ∥x.2∥⟩

lemma prod.norm_def (x : E × F) : ∥x∥ = (max ∥x.1∥ ∥x.2∥) := rfl
lemma norm_fst_le (x : E × F) : ∥x.1∥ ≤ ∥x∥ := le_max_left _ _
lemma norm_snd_le (x : E × F) : ∥x.2∥ ≤ ∥x∥ := le_max_right _ _

lemma norm_prod_le_iff : ∥x∥ ≤ r ↔ ∥x.1∥ ≤ r ∧ ∥x.2∥ ≤ r := max_le_iff

end has_norm

section seminormed_group
variables [seminormed_group E] [seminormed_group F]

/-- Product of seminormed groups, using the sup norm. -/
@[to_additive "Product of seminormed groups, using the sup norm."]
noncomputable instance : seminormed_group (E × F) :=
⟨λ x y, by simp only [prod.norm_def, prod.dist_eq, dist_eq_norm_div, prod.fst_div, prod.snd_div]⟩

@[to_additive prod.nnnorm_def']
lemma prod.nnorm_def (x : E × F) : ∥x∥₊ = (max ∥x.1∥₊ ∥x.2∥₊) := rfl

end seminormed_group

/-- Product of seminormed groups, using the sup norm. -/
@[to_additive "Product of seminormed groups, using the sup norm."]
noncomputable instance [seminormed_comm_group E] [seminormed_comm_group F] :
  seminormed_comm_group (E × F) :=
{ ..prod.seminormed_group }

/-- Product of normed groups, using the sup norm. -/
@[to_additive "Product of normed groups, using the sup norm."]
noncomputable instance [normed_group E] [normed_group F] : normed_group (E × F) :=
{ ..prod.seminormed_group }

/-- Product of normed groups, using the sup norm. -/
@[to_additive "Product of normed groups, using the sup norm."]
noncomputable instance [normed_comm_group E] [normed_comm_group F] : normed_comm_group (E × F) :=
{ ..prod.seminormed_group }


/-! ### Finite product of normed groups -/

section pi
variables {π : ι → Type*} [fintype ι]

section seminormed_group
variables [Π i, seminormed_group (π i)] [seminormed_group E] (f : Π i, π i) {x : Π i, π i} {r : ℝ}

/-- Finite product of seminormed groups, using the sup norm. -/
@[to_additive "Finite product of seminormed groups, using the sup norm."]
noncomputable instance : seminormed_group (Π i, π i) :=
{ norm := λ f, ↑(finset.univ.sup (λ b, ∥f b∥₊)),
  dist_eq := λ x y,
    congr_arg (coe : ℝ≥0 → ℝ) $ congr_arg (finset.sup finset.univ) $ funext $ λ a,
    show nndist (x a) (y a) = ∥x a / y a∥₊, from nndist_eq_nnnorm_div (x a) (y a) }

@[to_additive pi.norm_def] lemma pi.norm_def' : ∥f∥ = ↑(finset.univ.sup (λ b, ∥f b∥₊)) := rfl
@[to_additive pi.nnnorm_def] lemma pi.nnnorm_def' : ∥f∥₊ = finset.univ.sup (λ b, ∥f b∥₊) :=
subtype.eta _ _

/-- The seminorm of an element in a product space is `≤ r` if and only if the norm of each
component is. -/
@[to_additive pi_norm_le_iff "The seminorm of an element in a product space is `≤ r` if and only if
the norm of each component is."]
lemma pi_norm_le_iff' (hr : 0 ≤ r) : ∥x∥ ≤ r ↔ ∀ i, ∥x i∥ ≤ r :=
by simp only [←dist_one_right, dist_pi_le_iff hr, pi.one_apply]

@[to_additive pi_nnnorm_le_iff]
lemma pi_nnnorm_le_iff' {r : ℝ≥0} : ∥x∥₊ ≤ r ↔ ∀ i, ∥x i∥₊ ≤ r := pi_norm_le_iff' r.coe_nonneg

/-- The seminorm of an element in a product space is `< r` if and only if the norm of each
component is. -/
@[to_additive pi_norm_lt_iff "The seminorm of an element in a product space is `< r` if and only if
the norm of each component is."]
lemma pi_norm_lt_iff' (hr : 0 < r) : ∥x∥ < r ↔ ∀ i, ∥x i∥ < r :=
by simp only [←dist_one_right, dist_pi_lt_iff hr, pi.one_apply]

@[to_additive pi_nnnorm_lt_iff]
lemma pi_nnnorm_lt_iff' {r : ℝ≥0} (hr : 0 < r) : ∥x∥₊ < r ↔ ∀ i, ∥x i∥₊ < r := pi_norm_lt_iff' hr

@[to_additive norm_le_pi_norm]
lemma norm_le_pi_norm' (i : ι) : ∥f i∥ ≤ ∥f∥ := (pi_norm_le_iff' $ norm_nonneg' _).1 le_rfl i

@[to_additive nnnorm_le_pi_nnnorm]
lemma nnnorm_le_pi_nnnorm' (i : ι) : ∥f i∥₊ ≤ ∥f∥₊ := norm_le_pi_norm' _ i

@[simp, to_additive pi_norm_const]
lemma pi_norm_const' [nonempty ι] (a : E) : ∥(λ i : ι, a)∥ = ∥a∥ :=
by simpa only [←dist_one_right] using dist_pi_const a 1

@[simp, to_additive pi_nnnorm_const]
lemma pi_nnnorm_const' [nonempty ι] (a : E) : ∥(λ i : ι, a)∥₊ = ∥a∥₊ := nnreal.eq $ pi_norm_const' a

/-- The $L^1$ norm is less than the $L^\infty$ norm scaled by the cardinality. -/
@[to_additive pi.sum_norm_apply_le_norm "The $L^1$ norm is less than the $L^\\infty$ norm scaled by
the cardinality."]
lemma pi.sum_norm_apply_le_norm' : ∑ i, ∥f i∥ ≤ fintype.card ι • ∥f∥ :=
finset.sum_le_card_nsmul _ _ _ $ λ i hi, norm_le_pi_norm' _ i

/-- The $L^1$ norm is less than the $L^\infty$ norm scaled by the cardinality. -/
@[to_additive pi.sum_nnnorm_apply_le_nnnorm "The $L^1$ norm is less than the $L^\\infty$ norm scaled
by the cardinality."]
lemma pi.sum_nnnorm_apply_le_nnnorm' : ∑ i, ∥f i∥₊ ≤ fintype.card ι • ∥f∥₊ :=
nnreal.coe_sum.trans_le $ pi.sum_norm_apply_le_norm' _

end seminormed_group

/-- Finite product of seminormed groups, using the sup norm. -/
@[to_additive "Finite product of seminormed groups, using the sup norm."]
noncomputable instance pi.seminormed_comm_group [Π i, seminormed_comm_group (π i)] :
  seminormed_comm_group (Π i, π i) :=
{ ..pi.seminormed_group }

/-- Finite product of normed groups, using the sup norm. -/
@[to_additive "Finite product of seminormed groups, using the sup norm."]
noncomputable instance pi.normed_group [Π i, normed_group (π i)] : normed_group (Π i, π i) :=
{ ..pi.seminormed_group }

/-- Finite product of normed groups, using the sup norm. -/
@[to_additive "Finite product of seminormed groups, using the sup norm."]
noncomputable instance pi.normed_comm_group [Π i, normed_comm_group (π i)] :
  normed_comm_group (Π i, π i) :=
{ ..pi.seminormed_group }

end pi

/-! ### Subgroups of normed groups -/

namespace subgroup
section seminormed_group
variables [seminormed_group E] {s : subgroup E}

/-- A subgroup of a seminormed group is also a seminormed group,
with the restriction of the norm. -/
@[to_additive "A subgroup of a seminormed group is also a seminormed group,
with the restriction of the norm."]
instance seminormed_group : seminormed_group s := seminormed_group.induced s.subtype

/-- If `x` is an element of a subgroup `s` of a seminormed group `E`, its norm in `s` is equal to
its norm in `E`. -/
@[simp, to_additive "If `x` is an element of a subgroup `s` of a seminormed group `E`, its norm in
`s` is equal to its norm in `E`."]
lemma coe_norm (x : s) : ∥x∥ = ∥(x : E)∥ := rfl

/-- If `x` is an element of a subgroup `s` of a seminormed group `E`, its norm in `s` is equal to
its norm in `E`.

This is a reversed version of the `simp` lemma `subgroup.coe_norm` for use by `norm_cast`. -/
@[norm_cast, to_additive "If `x` is an element of a subgroup `s` of a seminormed group `E`, its norm
in `s` is equal to its norm in `E`.

This is a reversed version of the `simp` lemma `add_subgroup.coe_norm` for use by `norm_cast`."]
lemma norm_coe {s : subgroup E} (x : s) : ∥(x : E)∥ = ∥x∥ := rfl

end seminormed_group

@[to_additive] instance seminormed_comm_group [seminormed_comm_group E] {s : subgroup E} :
  seminormed_comm_group s :=
seminormed_comm_group.induced s.subtype

@[to_additive] instance normed_group [normed_group E] {s : subgroup E} : normed_group s :=
normed_group.induced s.subtype subtype.coe_injective

@[to_additive]
instance normed_comm_group [normed_comm_group E] {s : subgroup E} : normed_comm_group s :=
normed_comm_group.induced s.subtype subtype.coe_injective

end subgroup

/-! ### Submodules of normed groups -/

namespace submodule

/-- A submodule of a seminormed group is also a seminormed group, with the restriction of the norm.
-/
-- See note [implicit instance arguments]
instance seminormed_add_comm_group {_ : ring 𝕜} [seminormed_add_comm_group E] {_ : module 𝕜 E}
  (s : submodule 𝕜 E) :
  seminormed_add_comm_group s :=
seminormed_add_comm_group.induced s.subtype.to_add_monoid_hom

/-- If `x` is an element of a submodule `s` of a normed group `E`, its norm in `s` is equal to its
norm in `E`. -/
-- See note [implicit instance arguments].
@[simp] lemma coe_norm {_ : ring 𝕜} [seminormed_add_comm_group E] {_ : module 𝕜 E}
  {s : submodule 𝕜 E} (x : s) :
  ∥x∥ = ∥(x : E)∥ := rfl

/-- If `x` is an element of a submodule `s` of a normed group `E`, its norm in `E` is equal to its
norm in `s`.

This is a reversed version of the `simp` lemma `submodule.coe_norm` for use by `norm_cast`. -/
-- See note [implicit instance arguments].
@[norm_cast] lemma norm_coe {_ : ring 𝕜} [seminormed_add_comm_group E] {_ : module 𝕜 E}
  {s : submodule 𝕜 E} (x : s) :
  ∥(x : E)∥ = ∥x∥ := rfl

/-- A submodule of a normed group is also a normed group, with the restriction of the norm. -/
-- See note [implicit instance arguments].
instance submodule.normed_add_comm_group {_ : ring 𝕜} [normed_add_comm_group E] {_ : module 𝕜 E}
  (s : submodule 𝕜 E) : normed_add_comm_group s :=
{ ..submodule.seminormed_add_comm_group s }


end submodule

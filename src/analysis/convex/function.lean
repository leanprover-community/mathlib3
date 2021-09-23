/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, François Dupuis
-/
import analysis.convex.combination
import data.real.basic
import algebra.module.ordered

/-!
# Convex and concave functions

This file defines convex and concave functions in vector spaces and proves the finite Jensen
inequality. The integral version can be found in `analysis.convex.integral`.

A function `f : E → β` is `convex_on` a set `s` if `s` is itself a convex set, and for any two
points `x y ∈ s`, the segment joining `(x, f x)` to `(y, f y)` is above the graph of `f`.
Equivalently, `convex_on 𝕜 f s` means that the epigraph `{p : E × β | p.1 ∈ s ∧ f p.1 ≤ p.2}` is
a convex set.

## Main declarations

* `convex_on 𝕜 s f`: The function `f` is convex on `s` with scalars `𝕜`.
* `concave_on 𝕜 s f`: The function `f` is concave on `s` with scalars `𝕜`.
* `convex_on.map_center_mass_le` `convex_on.map_sum_le`: Convex Jensen's inequality.
-/

open finset linear_map set
open_locale big_operators classical convex pointwise

variables {𝕜 E F ι ι' β : Type*} [add_comm_group E] [module ℝ E] [add_comm_group F] [module ℝ F]
  [ordered_add_comm_monoid β] [module ℝ β] {s : set E}

/-- Convexity of functions -/
def convex_on (s : set E) (f : E → β) : Prop :=
  convex ℝ s ∧
  ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    f (a • x + b • y) ≤ a • f x + b • f y

/-- Concavity of functions -/
def concave_on (s : set E) (f : E → β) : Prop :=
  convex ℝ s ∧
  ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    a • f x + b • f y ≤ f (a • x + b • y)

section
variables [ordered_smul ℝ β]

/-- A function `f` is concave iff `-f` is convex. -/
@[simp] lemma neg_convex_on_iff {γ : Type*} [ordered_add_comm_group γ] [module ℝ γ]
  (s : set E) (f : E → γ) : convex_on s (-f) ↔ concave_on s f :=
begin
  split,
  { rintros ⟨hconv, h⟩,
    refine ⟨hconv, _⟩,
    intros x y xs ys a b ha hb hab,
    specialize h xs ys ha hb hab,
    simp [neg_apply, neg_le, add_comm] at h,
    exact h },
  { rintros ⟨hconv, h⟩,
    refine ⟨hconv, _⟩,
    intros x y xs ys a b ha hb hab,
    specialize h xs ys ha hb hab,
    simp [neg_apply, neg_le, add_comm, h] }
end

/-- A function `f` is concave iff `-f` is convex. -/
@[simp] lemma neg_concave_on_iff {γ : Type*} [ordered_add_comm_group γ] [module ℝ γ]
  (s : set E) (f : E → γ) : concave_on s (-f) ↔ convex_on s f:=
by rw [← neg_convex_on_iff s (-f), neg_neg f]

end

lemma convex_on_id {s : set ℝ} (hs : convex ℝ s) : convex_on s id := ⟨hs, by { intros, refl }⟩

lemma concave_on_id {s : set ℝ} (hs : convex ℝ s) : concave_on s id := ⟨hs, by { intros, refl }⟩

lemma convex_on_const (c : β) (hs : convex ℝ s) : convex_on s (λ x:E, c) :=
⟨hs, by { intros, simp only [← add_smul, *, one_smul] }⟩

lemma concave_on_const (c : β) (hs : convex ℝ s) : concave_on s (λ x:E, c) :=
@convex_on_const _ (order_dual β) _ _ _ _ _ c hs

lemma convex_on_iff_div {f : E → β} :
  convex_on s f ↔ convex ℝ s ∧ ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → 0 < a + b
  → f ((a/(a+b)) • x + (b/(a+b)) • y) ≤ (a/(a+b)) • f x + (b/(a+b)) • f y :=
and_congr iff.rfl
⟨begin
  intros h x y hx hy a b ha hb hab,
  apply h hx hy (div_nonneg ha $ le_of_lt hab) (div_nonneg hb $ le_of_lt hab),
  rw [←add_div],
  exact div_self (ne_of_gt hab)
end,
begin
  intros h x y hx hy a b ha hb hab,
  simpa [hab, zero_lt_one] using h hx hy ha hb,
end⟩

lemma concave_on_iff_div {f : E → β} :
  concave_on s f ↔ convex ℝ s ∧ ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → 0 < a + b
  → (a/(a+b)) • f x + (b/(a+b)) • f y ≤ f ((a/(a+b)) • x + (b/(a+b)) • y) :=
@convex_on_iff_div _ (order_dual β) _ _ _ _ _ _

/-- For a function on a convex set in a linear ordered space, in order to prove that it is convex
it suffices to verify the inequality `f (a • x + b • y) ≤ a • f x + b • f y` only for `x < y`
and positive `a`, `b`. The main use case is `E = ℝ` however one can apply it, e.g., to `ℝ^n` with
lexicographic order. -/
lemma linear_order.convex_on_of_lt {f : E → β} [linear_order E] (hs : convex ℝ s)
  (hf : ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → x < y → ∀ ⦃a b : ℝ⦄, 0 < a → 0 < b → a + b = 1 →
    f (a • x + b • y) ≤ a • f x + b • f y) : convex_on s f :=
begin
  use hs,
  intros x y hx hy a b ha hb hab,
  wlog hxy : x<=y using [x y a b, y x b a],
  { exact le_total _ _ },
  { cases eq_or_lt_of_le hxy with hxy hxy,
      by { subst y, rw [← add_smul, ← add_smul, hab, one_smul, one_smul] },
    cases eq_or_lt_of_le ha with ha ha,
      by { subst a, rw [zero_add] at hab, subst b, simp },
    cases eq_or_lt_of_le hb with hb hb,
      by { subst b, rw [add_zero] at hab, subst a, simp },
    exact hf hx hy hxy ha hb hab }
end

/-- For a function on a convex set in a linear ordered space, in order to prove that it is concave
it suffices to verify the inequality `a • f x + b • f y ≤ f (a • x + b • y)` only for `x < y`
and positive `a`, `b`. The main use case is `E = ℝ` however one can apply it, e.g., to `ℝ^n` with
lexicographic order. -/
lemma linear_order.concave_on_of_lt {f : E → β} [linear_order E] (hs : convex ℝ s)
  (hf : ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → x < y → ∀ ⦃a b : ℝ⦄, 0 < a → 0 < b → a + b = 1 →
     a • f x + b • f y ≤ f (a • x + b • y)) : concave_on s f :=
@linear_order.convex_on_of_lt _ (order_dual β) _ _ _ _ _ f _ hs hf

/-- For a function `f` defined on a convex subset `D` of `ℝ`, if for any three points `x < y < z`
the slope of the secant line of `f` on `[x, y]` is less than or equal to the slope
of the secant line of `f` on `[x, z]`, then `f` is convex on `D`. This way of proving convexity
of a function is used in the proof of convexity of a function with a monotone derivative. -/
lemma convex_on_real_of_slope_mono_adjacent {s : set ℝ} (hs : convex ℝ s) {f : ℝ → ℝ}
  (hf : ∀ {x y z : ℝ}, x ∈ s → z ∈ s → x < y → y < z →
    (f y - f x) / (y - x) ≤ (f z - f y) / (z - y)) :
  convex_on s f :=
linear_order.convex_on_of_lt hs
begin
  assume x z hx hz hxz a b ha hb hab,
  let y := a * x + b * z,
  have hxy : x < y,
  { rw [← one_mul x, ← hab, add_mul],
    exact add_lt_add_left ((mul_lt_mul_left hb).2 hxz) _ },
  have hyz : y < z,
  { rw [← one_mul z, ← hab, add_mul],
    exact add_lt_add_right ((mul_lt_mul_left ha).2 hxz) _ },
  have : (f y - f x) * (z - y) ≤ (f z - f y) * (y - x),
    from (div_le_div_iff (sub_pos.2 hxy) (sub_pos.2 hyz)).1 (hf hx hz hxy hyz),
  have A : z - y + (y - x) = z - x, by abel,
  have B : 0 < z - x, from sub_pos.2 (lt_trans hxy hyz),
  rw [sub_mul, sub_mul, sub_le_iff_le_add', ← add_sub_assoc, le_sub_iff_add_le, ← mul_add, A,
    ← le_div_iff B, add_div, mul_div_assoc, mul_div_assoc,
    mul_comm (f x), mul_comm (f z)] at this,
  rw [eq_comm, ← sub_eq_iff_eq_add] at hab; subst a,
  convert this; symmetry; simp only [div_eq_iff (ne_of_gt B), y]; ring
end

/-- For a function `f` defined on a subset `D` of `ℝ`, if `f` is convex on `D`, then for any three
points `x < y < z`, the slope of the secant line of `f` on `[x, y]` is less than or equal to the
slope of the secant line of `f` on `[x, z]`. -/
lemma convex_on.slope_mono_adjacent {s : set ℝ} {f : ℝ → ℝ} (hf : convex_on s f)
  {x y z : ℝ} (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y) (hyz : y < z) :
  (f y - f x) / (y - x) ≤ (f z - f y) / (z - y) :=
begin
  have h₁ : 0 < y - x := by linarith,
  have h₂ : 0 < z - y := by linarith,
  have h₃ : 0 < z - x := by linarith,
  suffices : f y / (y - x) + f y / (z - y) ≤ f x / (y - x) + f z / (z - y),
    by { ring_nf at this ⊢, linarith },
  set a := (z - y) / (z - x),
  set b := (y - x) / (z - x),
  have heqz : a • x + b • z = y, by { field_simp, rw div_eq_iff; [ring, linarith], },
  have key, from
    hf.2 hx hz
      (show 0 ≤ a, by apply div_nonneg; linarith)
      (show 0 ≤ b, by apply div_nonneg; linarith)
      (show a + b = 1, by { field_simp, rw div_eq_iff; [ring, linarith], }),
  rw heqz at key,
  replace key := mul_le_mul_of_nonneg_left key (le_of_lt h₃),
  field_simp [ne_of_gt h₁, ne_of_gt h₂, ne_of_gt h₃, mul_comm (z - x) _] at key ⊢,
  rw div_le_div_right,
  { linarith, },
  { nlinarith, },
end

/-- For a function `f` defined on a convex subset `D` of `ℝ`, `f` is convex on `D` iff, for any
three points `x < y < z` the slope of the secant line of `f` on `[x, y]` is less than or equal to
the slope,of the secant line of `f` on `[x, z]`. -/
lemma convex_on_real_iff_slope_mono_adjacent {s : set ℝ} (hs : convex ℝ s) {f : ℝ → ℝ} :
  convex_on s f ↔
  (∀ {x y z : ℝ}, x ∈ s → z ∈ s → x < y → y < z →
    (f y - f x) / (y - x) ≤ (f z - f y) / (z - y)) :=
⟨convex_on.slope_mono_adjacent, convex_on_real_of_slope_mono_adjacent hs⟩

/-- For a function `f` defined on a convex subset `D` of `ℝ`, if for any three points `x < y < z`
the slope of the secant line of `f` on `[x, y]` is greater than or equal to the slope
of the secant line of `f` on `[x, z]`, then `f` is concave on `D`. -/
lemma concave_on_real_of_slope_mono_adjacent {s : set ℝ} (hs : convex ℝ s) {f : ℝ → ℝ}
  (hf : ∀ {x y z : ℝ}, x ∈ s → z ∈ s → x < y → y < z →
    (f z - f y) / (z - y) ≤ (f y - f x) / (y - x)) : concave_on s f :=
begin
  rw [←neg_convex_on_iff],
  apply convex_on_real_of_slope_mono_adjacent hs,
  intros x y z xs zs xy yz,
  rw [←neg_le_neg_iff, ←neg_div, ←neg_div, neg_sub, neg_sub],
  simp only [hf xs zs xy yz, neg_sub_neg, pi.neg_apply],
end

/-- For a function `f` defined on a subset `D` of `ℝ`, if `f` is concave on `D`, then for any three
points `x < y < z`, the slope of the secant line of `f` on `[x, y]` is greater than or equal to the
slope of the secant line of `f` on `[x, z]`. -/
lemma concave_on.slope_mono_adjacent {s : set ℝ} {f : ℝ → ℝ} (hf : concave_on s f)
  {x y z : ℝ} (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y) (hyz : y < z) :
  (f z - f y) / (z - y) ≤ (f y - f x) / (y - x) :=
begin
  rw [←neg_le_neg_iff, ←neg_div, ←neg_div, neg_sub, neg_sub],
  rw [←neg_sub_neg (f y), ←neg_sub_neg (f z)],
  simp_rw [←pi.neg_apply],
  rw [←neg_convex_on_iff] at hf,
  apply convex_on.slope_mono_adjacent hf; assumption,
end

/-- For a function `f` defined on a convex subset `D` of `ℝ`, `f` is concave on `D` iff for any
three points `x < y < z` the slope of the secant line of `f` on `[x, y]` is greater than or equal to
the slope of the secant line of `f` on `[x, z]`. -/
lemma concave_on_real_iff_slope_mono_adjacent {s : set ℝ} (hs : convex ℝ s) {f : ℝ → ℝ} :
  concave_on s f ↔
  (∀ {x y z : ℝ}, x ∈ s → z ∈ s → x < y → y < z →
    (f z - f y) / (z - y) ≤ (f y - f x) / (y - x)) :=
⟨concave_on.slope_mono_adjacent, concave_on_real_of_slope_mono_adjacent hs⟩

lemma convex_on.subset {f : E → β} {t : set E} (h_convex_on : convex_on t f)
  (h_subset : s ⊆ t) (h_convex : convex ℝ s) : convex_on s f :=
begin
  apply and.intro h_convex,
  intros x y hx hy,
  exact h_convex_on.2 (h_subset hx) (h_subset hy),
end

lemma concave_on.subset {f : E → β} {t : set E} (h_concave_on : concave_on t f)
  (h_subset : s ⊆ t) (h_convex : convex ℝ s) : concave_on s f :=
@convex_on.subset _ (order_dual β) _ _ _ _ _ f t h_concave_on h_subset h_convex

lemma convex_on.add {f g : E → β} (hf : convex_on s f) (hg : convex_on s g) :
  convex_on s (λx, f x + g x) :=
begin
  apply and.intro hf.1,
  intros x y hx hy a b ha hb hab,
  calc
    f (a • x + b • y) + g (a • x + b • y) ≤ (a • f x + b • f y) + (a • g x + b • g y)
      : add_le_add (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)
    ... = a • f x + a • g x + b • f y + b • g y : by abel
    ... = a • (f x + g x) + b • (f y + g y) : by simp [smul_add, add_assoc]
end

lemma concave_on.add {f g : E → β} (hf : concave_on s f) (hg : concave_on s g) :
  concave_on s (λx, f x + g x) :=
@convex_on.add _ (order_dual β) _ _ _ _ _ f g hf hg

lemma convex_on.smul [ordered_smul ℝ β] {f : E → β} {c : ℝ} (hc : 0 ≤ c)
  (hf : convex_on s f) : convex_on s (λx, c • f x) :=
begin
  apply and.intro hf.1,
  intros x y hx hy a b ha hb hab,
  calc
    c • f (a • x + b • y) ≤ c • (a • f x + b • f y)
      : smul_le_smul_of_nonneg (hf.2 hx hy ha hb hab) hc
    ... = a • (c • f x) + b • (c • f y) : by simp only [smul_add, smul_comm c]
end

lemma concave_on.smul [ordered_smul ℝ β] {f : E → β} {c : ℝ} (hc : 0 ≤ c)
  (hf : concave_on s f) : concave_on s (λx, c • f x) :=
@convex_on.smul _ (order_dual β) _ _ _ _ _ _ f c hc hf

section linear_order
section monoid

variables {γ : Type*} [linear_ordered_add_comm_monoid γ] [module ℝ γ] [ordered_smul ℝ γ]
  {f g : E → γ}

/-- The pointwise maximum of convex functions is convex. -/
lemma convex_on.sup (hf : convex_on s f) (hg : convex_on s g) :
  convex_on s (f ⊔ g) :=
begin
   refine ⟨hf.left, λ x y hx hy a b ha hb hab, sup_le _ _⟩,
   { calc f (a • x + b • y) ≤ a • f x + b • f y : hf.right hx hy ha hb hab
      ...                   ≤ a • (f x ⊔ g x) + b • (f y ⊔ g y) : add_le_add
      (smul_le_smul_of_nonneg le_sup_left ha)
      (smul_le_smul_of_nonneg le_sup_left hb) },
   { calc g (a • x + b • y) ≤ a • g x + b • g y : hg.right hx hy ha hb hab
      ...                   ≤ a • (f x ⊔ g x) + b • (f y ⊔ g y) : add_le_add
      (smul_le_smul_of_nonneg le_sup_right ha)
      (smul_le_smul_of_nonneg le_sup_right hb) }
end

/-- The pointwise minimum of concave functions is concave. -/
lemma concave_on.inf (hf : concave_on s f) (hg : concave_on s g) :
  concave_on s (f ⊓ g) :=
@convex_on.sup _ _ _ _ (order_dual γ) _ _ _ _ _ hf hg

/-- A convex function on a segment is upper-bounded by the max of its endpoints. -/
lemma convex_on.le_on_segment' (hf : convex_on s f) {x y : E} {a b : ℝ}
  (hx : x ∈ s) (hy : y ∈ s) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
  f (a • x + b • y) ≤ max (f x) (f y) :=
calc
  f (a • x + b • y) ≤ a • f x + b • f y : hf.2 hx hy ha hb hab
  ... ≤ a • max (f x) (f y) + b • max (f x) (f y) :
    add_le_add (smul_le_smul_of_nonneg (le_max_left _ _) ha)
      (smul_le_smul_of_nonneg (le_max_right _ _) hb)
  ... = max (f x) (f y) : by rw [←add_smul, hab, one_smul]

/-- A concave function on a segment is lower-bounded by the min of its endpoints. -/
lemma concave_on.le_on_segment' (hf : concave_on s f) {x y : E} {a b : ℝ}
  (hx : x ∈ s) (hy : y ∈ s) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
  min (f x) (f y) ≤ f (a • x + b • y) :=
@convex_on.le_on_segment' _ _ _ _ (order_dual γ) _ _ _ f hf x y a b hx hy ha hb hab

/-- A convex function on a segment is upper-bounded by the max of its endpoints. -/
lemma convex_on.le_on_segment (hf : convex_on s f) {x y z : E}
  (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ [x -[ℝ] y]) :
  f z ≤ max (f x) (f y) :=
let ⟨a, b, ha, hb, hab, hz⟩ := hz in hz ▸ hf.le_on_segment' hx hy ha hb hab

/-- A concave function on a segment is lower-bounded by the min of its endpoints. -/
lemma concave_on.le_on_segment {f : E → γ} (hf : concave_on s f) {x y z : E}
  (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ [x -[ℝ] y]) :
    min (f x) (f y) ≤ f z :=
@convex_on.le_on_segment _ _ _ _ (order_dual γ) _ _ _ f hf x y z hx hy hz

end monoid

variables {γ : Type*} [linear_ordered_cancel_add_comm_monoid γ] [module ℝ γ] [ordered_smul ℝ γ]
  {f : E → γ}

-- could be shown without contradiction but yeah
lemma convex_on.le_left_of_right_le' (hf : convex_on s f) {x y : E} {a b : ℝ}
  (hx : x ∈ s) (hy : y ∈ s) (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1)
  (hxy : f y ≤ f (a • x + b • y)) :
  f (a • x + b • y) ≤ f x :=
begin
  apply le_of_not_lt (λ h, lt_irrefl (f (a • x + b • y)) _),
  calc
    f (a • x + b • y)
        ≤ a • f x + b • f y : hf.2 hx hy ha.le hb hab
    ... < a • f (a • x + b • y) + b • f (a • x + b • y)
        : add_lt_add_of_lt_of_le (smul_lt_smul_of_pos h ha) (smul_le_smul_of_nonneg hxy hb)
    ... = f (a • x + b • y) : by rw [←add_smul, hab, one_smul],
end

lemma concave_on.left_le_of_le_right' (hf : concave_on s f) {x y : E} {a b : ℝ}
  (hx : x ∈ s) (hy : y ∈ s) (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1)
  (hxy : f (a • x + b • y) ≤ f y) :
  f x ≤ f (a • x + b • y) :=
@convex_on.le_left_of_right_le' _ _ _ _ (order_dual γ) _ _ _ f hf x y a b hx hy ha hb hab hxy

lemma convex_on.le_right_of_left_le' (hf : convex_on s f) {x y : E} {a b : ℝ}
  (hx : x ∈ s) (hy : y ∈ s) (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1)
  (hxy : f x ≤ f (a • x + b • y)) :
  f (a • x + b • y) ≤ f y :=
begin
  rw add_comm at ⊢ hab hxy,
  exact hf.le_left_of_right_le' hy hx hb ha hab hxy,
end

lemma concave_on.le_right_of_left_le' (hf : concave_on s f) {x y : E} {a b : ℝ}
  (hx : x ∈ s) (hy : y ∈ s) (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1)
  (hxy : f (a • x + b • y) ≤ f x) :
  f y ≤ f (a • x + b • y) :=
@convex_on.le_right_of_left_le' _ _ _ _ (order_dual γ) _ _ _ f hf x y a b hx hy ha hb hab hxy

lemma convex_on.le_left_of_right_le (hf : convex_on s f) {x y z : E} (hx : x ∈ s)
  (hy : y ∈ s) (hz : z ∈ open_segment ℝ x y) (hyz : f y ≤ f z) :
  f z ≤ f x :=
begin
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz,
  exact hf.le_left_of_right_le' hx hy ha hb.le hab hyz,
end

lemma concave_on.left_le_of_le_right (hf : concave_on s f) {x y z : E} (hx : x ∈ s)
  (hy : y ∈ s) (hz : z ∈ open_segment ℝ x y) (hyz : f z ≤ f y) :
  f x ≤ f z :=
@convex_on.le_left_of_right_le _ _ _ _ (order_dual γ) _ _ _ f hf x y z hx hy hz hyz

lemma convex_on.le_right_of_left_le (hf : convex_on s f) {x y z : E} (hx : x ∈ s)
  (hy : y ∈ s) (hz : z ∈ open_segment ℝ x y) (hxz : f x ≤ f z) :
  f z ≤ f y :=
begin
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz,
  exact hf.le_right_of_left_le' hx hy ha.le hb hab hxz,
end

lemma concave_on.le_right_of_left_le (hf : concave_on s f) {x y z : E} (hx : x ∈ s)
  (hy : y ∈ s) (hz : z ∈ open_segment ℝ x y) (hxz : f z ≤ f x) :
  f y ≤ f z :=
@convex_on.le_right_of_left_le _ _ _ _ (order_dual γ) _ _ _ f hf x y z hx hy hz hxz

end linear_order

lemma convex_on.convex_le [ordered_smul ℝ β] {f : E → β} (hf : convex_on s f) (r : β) :
  convex ℝ {x ∈ s | f x ≤ r} :=
λ x y hx hy a b ha hb hab,
begin
  refine ⟨hf.1 hx.1 hy.1 ha hb hab, _⟩,
  calc
    f (a • x + b • y) ≤ a • (f x) + b • (f y) : hf.2 hx.1 hy.1 ha hb hab
                  ... ≤ a • r + b • r         : add_le_add (smul_le_smul_of_nonneg hx.2 ha)
                                                  (smul_le_smul_of_nonneg hy.2 hb)
                  ... ≤ r                     : by simp [←add_smul, hab]
end

lemma concave_on.concave_le [ordered_smul ℝ β] {f : E → β} (hf : concave_on s f) (r : β) :
  convex ℝ {x ∈ s | r ≤ f x} :=
@convex_on.convex_le _ (order_dual β) _ _ _ _ _ _ f hf r

lemma convex_on.convex_lt {γ : Type*} [ordered_cancel_add_comm_monoid γ]
  [module ℝ γ] [ordered_smul ℝ γ]
  {f : E → γ} (hf : convex_on s f) (r : γ) : convex ℝ {x ∈ s | f x < r} :=
begin
  intros a b as bs xa xb hxa hxb hxaxb,
  refine ⟨hf.1 as.1 bs.1 hxa hxb hxaxb, _⟩,
  by_cases H : xa = 0,
  { have H' : xb = 1 := by rwa [H, zero_add] at hxaxb,
    rw [H, H', zero_smul, one_smul, zero_add],
    exact bs.2 },
  { calc
      f (xa • a + xb • b) ≤ xa • (f a) + xb • (f b) : hf.2 as.1 bs.1 hxa hxb hxaxb
                      ... < xa • r + xb • (f b)     : (add_lt_add_iff_right (xb • (f b))).mpr
                                                        (smul_lt_smul_of_pos as.2
                                                          (lt_of_le_of_ne hxa (ne.symm H)))
                      ... ≤ xa • r + xb • r         : (add_le_add_iff_left (xa • r)).mpr
                                                        (smul_le_smul_of_nonneg bs.2.le hxb)
                      ... = r                       : by simp only [←add_smul, hxaxb, one_smul] }
end

lemma concave_on.convex_lt {γ : Type*} [ordered_cancel_add_comm_monoid γ]
  [module ℝ γ] [ordered_smul ℝ γ]
  {f : E → γ} (hf : concave_on s f) (r : γ) : convex ℝ {x ∈ s | r < f x} :=
@convex_on.convex_lt _ _ _ _ (order_dual γ) _ _ _ f hf r

lemma convex_on.convex_epigraph {γ : Type*} [ordered_add_comm_group γ]
  [module ℝ γ] [ordered_smul ℝ γ]
  {f : E → γ} (hf : convex_on s f) :
  convex ℝ {p : E × γ | p.1 ∈ s ∧ f p.1 ≤ p.2} :=
begin
  rintros ⟨x, r⟩ ⟨y, t⟩ ⟨hx, hr⟩ ⟨hy, ht⟩ a b ha hb hab,
  refine ⟨hf.1 hx hy ha hb hab, _⟩,
  calc f (a • x + b • y) ≤ a • f x + b • f y : hf.2 hx hy ha hb hab
  ... ≤ a • r + b • t : add_le_add (smul_le_smul_of_nonneg hr ha)
                            (smul_le_smul_of_nonneg ht hb)
end

lemma concave_on.convex_hypograph {γ : Type*} [ordered_add_comm_group γ]
  [module ℝ γ] [ordered_smul ℝ γ]
  {f : E → γ} (hf : concave_on s f) :
  convex ℝ {p : E × γ | p.1 ∈ s ∧ p.2 ≤ f p.1} :=
@convex_on.convex_epigraph _ _ _ _ (order_dual γ) _ _ _ f hf

lemma convex_on_iff_convex_epigraph {γ : Type*} [ordered_add_comm_group γ]
  [module ℝ γ] [ordered_smul ℝ γ]
  {f : E → γ} :
  convex_on s f ↔ convex ℝ {p : E × γ | p.1 ∈ s ∧ f p.1 ≤ p.2} :=
begin
  refine ⟨convex_on.convex_epigraph, λ h, ⟨_, _⟩⟩,
  { assume x y hx hy a b ha hb hab,
    exact (@h (x, f x) (y, f y) ⟨hx, le_refl _⟩ ⟨hy, le_refl _⟩ a b ha hb hab).1 },
  { assume x y hx hy a b ha hb hab,
    exact (@h (x, f x) (y, f y) ⟨hx, le_refl _⟩ ⟨hy, le_refl _⟩ a b ha hb hab).2 }
end

lemma concave_on_iff_convex_hypograph {γ : Type*} [ordered_add_comm_group γ]
  [module ℝ γ] [ordered_smul ℝ γ]
  {f : E → γ} :
  concave_on s f ↔ convex ℝ {p : E × γ | p.1 ∈ s ∧ p.2 ≤ f p.1} :=
@convex_on_iff_convex_epigraph _ _ _ _ (order_dual γ) _ _ _ f

/- A linear map is convex. -/
lemma linear_map.convex_on (f : E →ₗ[ℝ] β) {s : set E} (hs : convex ℝ s) : convex_on s f :=
⟨hs, λ _ _ _ _ _ _ _ _ _, by rw [f.map_add, f.map_smul, f.map_smul]⟩

/- A linear map is concave. -/
lemma linear_map.concave_on (f : E →ₗ[ℝ] β) {s : set E} (hs : convex ℝ s) : concave_on s f :=
⟨hs, λ _ _ _ _ _ _ _ _ _, by rw [f.map_add, f.map_smul, f.map_smul]⟩

/-- If a function is convex on `s`, it remains convex when precomposed by an affine map. -/
lemma convex_on.comp_affine_map {f : F → β} (g : E →ᵃ[ℝ] F) {s : set F}
  (hf : convex_on s f) : convex_on (g ⁻¹' s) (f ∘ g) :=
begin
  refine ⟨hf.1.affine_preimage  _,_⟩,
  intros x y xs ys a b ha hb hab,
  calc
    (f ∘ g) (a • x + b • y) = f (g (a • x + b • y))         : rfl
                       ...  = f (a • (g x) + b • (g y))     : by rw [convex.combo_affine_apply hab]
                       ...  ≤ a • f (g x) + b • f (g y)     : hf.2 xs ys ha hb hab
                       ...  = a • (f ∘ g) x + b • (f ∘ g) y : rfl
end

/-- If a function is concave on `s`, it remains concave when precomposed by an affine map. -/
lemma concave_on.comp_affine_map {f : F → β} (g : E →ᵃ[ℝ] F) {s : set F}
  (hf : concave_on s f) : concave_on (g ⁻¹' s) (f ∘ g) :=
@convex_on.comp_affine_map _ _ (order_dual β) _ _ _ _ _ _ f g s hf

/-- If `g` is convex on `s`, so is `(g ∘ f)` on `f ⁻¹' s` for a linear `f`. -/
lemma convex_on.comp_linear_map {g : F → β} {s : set F} (hg : convex_on s g) (f : E →ₗ[ℝ] F) :
  convex_on (f ⁻¹' s) (g ∘ f) :=
hg.comp_affine_map f.to_affine_map

/-- If `g` is concave on `s`, so is `(g ∘ f)` on `f ⁻¹' s` for a linear `f`. -/
lemma concave_on.comp_linear_map {g : F → β} {s : set F} (hg : concave_on s g) (f : E →ₗ[ℝ] F) :
  concave_on (f ⁻¹' s) (g ∘ f) :=
hg.comp_affine_map f.to_affine_map

/-- If a function is convex on `s`, it remains convex after a translation. -/
lemma convex_on.translate_right {f : E → β} {s : set E} {a : E} (hf : convex_on s f) :
  convex_on ((λ z, a + z) ⁻¹' s) (f ∘ (λ z, a + z)) :=
hf.comp_affine_map $ affine_map.const ℝ E a +ᵥ affine_map.id ℝ E

/-- If a function is concave on `s`, it remains concave after a translation. -/
lemma concave_on.translate_right {f : E → β} {s : set E} {a : E} (hf : concave_on s f) :
  concave_on ((λ z, a + z) ⁻¹' s) (f ∘ (λ z, a + z)) :=
hf.comp_affine_map $ affine_map.const ℝ E a +ᵥ affine_map.id ℝ E

/-- If a function is convex on `s`, it remains convex after a translation. -/
lemma convex_on.translate_left {f : E → β} {s : set E} {a : E} (hf : convex_on s f) :
  convex_on ((λ z, a + z) ⁻¹' s) (f ∘ (λ z, z + a)) :=
by simpa only [add_comm] using hf.translate_right

/-- If a function is concave on `s`, it remains concave after a translation. -/
lemma concave_on.translate_left {f : E → β} {s : set E} {a : E} (hf : concave_on s f) :
  concave_on ((λ z, a + z) ⁻¹' s) (f ∘ (λ z, z + a)) :=
by simpa only [add_comm] using hf.translate_right

/-! ### Jensen's inequality -/

variables {i j : ι} {c : ℝ} {t : finset ι} {w : ι → ℝ} {z : ι → E}

/-- Convex **Jensen's inequality**, `finset.center_mass` version. -/
lemma convex_on.map_center_mass_le {f : E → ℝ} (hf : convex_on s f)
  (h₀ : ∀ i ∈ t, 0 ≤ w i) (hpos : 0 < ∑ i in t, w i)
  (hmem : ∀ i ∈ t, z i ∈ s) : f (t.center_mass w z) ≤ t.center_mass w (f ∘ z) :=
begin
  have hmem' : ∀ i ∈ t, (z i, (f ∘ z) i) ∈ {p : E × ℝ | p.1 ∈ s ∧ f p.1 ≤ p.2},
    from λ i hi, ⟨hmem i hi, le_rfl⟩,
  convert (hf.convex_epigraph.center_mass_mem h₀ hpos hmem').2;
    simp only [center_mass, function.comp, prod.smul_fst, prod.fst_sum, prod.smul_snd, prod.snd_sum]
end

/-- Convex **Jensen's inequality**, `finset.sum` version. -/
lemma convex_on.map_sum_le {f : E → ℝ} (hf : convex_on s f)
  (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i in t, w i = 1)
  (hmem : ∀ i ∈ t, z i ∈ s) : f (∑ i in t, w i • z i) ≤ ∑ i in t, w i * (f (z i)) :=
by simpa only [center_mass, h₁, inv_one, one_smul]
  using hf.map_center_mass_le h₀ (h₁.symm ▸ zero_lt_one) hmem

/-! ### Maximal principle -/

/-- If a function `f` is convex on `s` takes value `y` at the center of mass of some points
`z i ∈ s`, then for some `i` we have `y ≤ f (z i)`. -/
lemma convex_on.exists_ge_of_center_mass {f : E → ℝ} (h : convex_on s f)
  (hw₀ : ∀ i ∈ t, 0 ≤ w i) (hws : 0 < ∑ i in t, w i) (hz : ∀ i ∈ t, z i ∈ s) :
  ∃ i ∈ t, f (t.center_mass w z) ≤ f (z i) :=
begin
  set y := t.center_mass w z,
  have : f y ≤ t.center_mass w (f ∘ z) := h.map_center_mass_le hw₀ hws hz,
  rw ← sum_filter_ne_zero at hws,
  rw [← finset.center_mass_filter_ne_zero (f ∘ z), center_mass, smul_eq_mul,
    ← div_eq_inv_mul, le_div_iff hws, mul_sum] at this,
  replace : ∃ i ∈ t.filter (λ i, w i ≠ 0), f y * w i ≤ w i • (f ∘ z) i :=
    exists_le_of_sum_le (nonempty_of_sum_ne_zero (ne_of_gt hws)) this,
  rcases this with ⟨i, hi, H⟩,
  rw [mem_filter] at hi,
  use [i, hi.1],
  simp only [smul_eq_mul, mul_comm (w i)] at H,
  refine (mul_le_mul_right _).1 H,
  exact lt_of_le_of_ne (hw₀ i hi.1) hi.2.symm
end

/-- Maximum principle for convex functions. If a function `f` is convex on the convex hull of `s`,
then `f` can't have a maximum on `convex_hull s` outside of `s`. -/
lemma convex_on.exists_ge_of_mem_convex_hull {f : E → ℝ} (hf : convex_on (convex_hull ℝ s) f)
  {x} (hx : x ∈ convex_hull ℝ s) : ∃ y ∈ s, f x ≤ f y :=
begin
  rw _root_.convex_hull_eq at hx,
  rcases hx with ⟨α, t, w, z, hw₀, hw₁, hz, rfl⟩,
  rcases hf.exists_ge_of_center_mass hw₀ (hw₁.symm ▸ zero_lt_one)
    (λ i hi, subset_convex_hull ℝ s (hz i hi)) with ⟨i, hit, Hi⟩,
  exact ⟨z i, hz i hit, Hi⟩
end

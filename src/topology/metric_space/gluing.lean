/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Gluing metric spaces
Authors: Sébastien Gouëzel
-/
import topology.metric_space.isometry
import topology.metric_space.premetric_space

/-!
# Metric space gluing

Gluing two metric spaces along a common subset. Formally, we are given

```
     Φ
  γ ---> α
  |
  |Ψ
  v
  β
```
where `hΦ : isometry Φ` and `hΨ : isometry Ψ`.
We want to complete the square by a space `glue_space hΦ hΨ` and two isometries
`to_glue_l hΦ hΨ` and `to_glue_r hΦ hΨ` that make the square commute.
We start by defining a predistance on the disjoint union `α ⊕ β`, for which
points `Φ p` and `Ψ p` are at distance 0. The (quotient) metric space associated
to this predistance is the desired space.

This is an instance of a more general construction, where `Φ` and `Ψ` do not have to be isometries,
but the distances in the image almost coincide, up to `2ε` say. Then one can almost glue the two
spaces so that the images of a point under `Φ` and `Ψ` are ε-close. If `ε > 0`, this yields a
metric space structure on `α ⊕ β`, without the need to take a quotient. In particular, when
`α` and `β` are inhabited, this gives a natural metric space structure on `α ⊕ β`, where the basepoints
are at distance 1, say, and the distances between other points are obtained by going through the
two basepoints.

We also define the inductive limit of metric spaces. Given
```
     f 0        f 1        f 2        f 3
X 0 -----> X 1 -----> X 2 -----> X 3 -----> ...
```
where the `X n` are metric spaces and `f n` isometric embeddings, we define the inductive
limit of the `X n`, also known as the increasing union of the `X n` in this context, if we
identify `X n` and `X (n+1)` through `f n`. This is a metric space in which all `X n` embed
isometrically and in a way compatible with `f n`.

-/

noncomputable theory

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

open function set premetric

namespace metric
section approx_gluing

variables [metric_space α] [metric_space β]
          {Φ : γ → α} {Ψ : γ → β} {ε : ℝ}
open sum (inl inr)

/-- Define a predistance on α ⊕ β, for which Φ p and Ψ p are at distance ε -/
def glue_dist (Φ : γ → α) (Ψ : γ → β) (ε : ℝ) : α ⊕ β → α ⊕ β → ℝ
| (inl x) (inl y) := dist x y
| (inr x) (inr y) := dist x y
| (inl x) (inr y) := infi (λp, dist x (Φ p) + dist y (Ψ p)) + ε
| (inr x) (inl y) := infi (λp, dist y (Φ p) + dist x (Ψ p)) + ε

private lemma glue_dist_self (Φ : γ → α) (Ψ : γ → β) (ε : ℝ) : ∀x, glue_dist Φ Ψ ε x x = 0
| (inl x) := dist_self _
| (inr x) := dist_self _

lemma glue_dist_glued_points [nonempty γ] (Φ : γ → α) (Ψ : γ → β) (ε : ℝ) (p : γ) :
  glue_dist Φ Ψ ε (inl (Φ p)) (inr (Ψ p)) = ε :=
begin
  have : infi (λq, dist (Φ p) (Φ q) + dist (Ψ p) (Ψ q)) = 0,
  { have A : ∀q, 0 ≤ dist (Φ p) (Φ q) + dist (Ψ p) (Ψ q) :=
      λq, by rw ← add_zero (0 : ℝ); exact add_le_add dist_nonneg dist_nonneg,
    refine le_antisymm _ (le_cinfi A),
    have : 0 = dist (Φ p) (Φ p) + dist (Ψ p) (Ψ p), by simp,
    rw this,
    exact cinfi_le ⟨0, forall_range_iff.2 A⟩ p },
  rw [glue_dist, this, zero_add]
end

private lemma glue_dist_comm (Φ : γ → α) (Ψ : γ → β) (ε : ℝ) :
  ∀x y, glue_dist Φ Ψ ε x y = glue_dist Φ Ψ ε y x
| (inl x) (inl y) := dist_comm _ _
| (inr x) (inr y) := dist_comm _ _
| (inl x) (inr y) := rfl
| (inr x) (inl y) := rfl

variable [nonempty γ]

private lemma glue_dist_triangle (Φ : γ → α) (Ψ : γ → β) (ε : ℝ)
  (H : ∀p q, abs (dist (Φ p) (Φ q) - dist (Ψ p) (Ψ q)) ≤ 2 * ε) :
  ∀x y z, glue_dist Φ Ψ ε x z ≤ glue_dist Φ Ψ ε x y + glue_dist Φ Ψ ε y z
| (inl x) (inl y) (inl z) := dist_triangle _ _ _
| (inr x) (inr y) (inr z) := dist_triangle _ _ _
| (inr x) (inl y) (inl z) := begin
    have B : ∀a b, bdd_below (range (λ (p : γ), dist a (Φ p) + dist b (Ψ p))) :=
      λa b, ⟨0, forall_range_iff.2 (λp, add_nonneg dist_nonneg dist_nonneg)⟩,
    unfold glue_dist,
    have : infi (λp, dist z (Φ p) + dist x (Ψ p)) ≤ infi (λp, dist y (Φ p) + dist x (Ψ p)) + dist y z,
    { have : infi (λp, dist y (Φ p) + dist x (Ψ p)) + dist y z =
            infi ((λt, t + dist y z) ∘ (λp, dist y (Φ p) + dist x (Ψ p))),
      { refine map_cinfi_of_continuous_at_of_monotone (continuous_at_id.add continuous_at_const) _
          (B _ _),
        intros x y hx, simpa },
      rw [this, comp],
      refine cinfi_le_cinfi (B _ _) (λp, _),
      calc
        dist z (Φ p) + dist x (Ψ p) ≤ (dist y z + dist y (Φ p)) + dist x (Ψ p) :
          add_le_add (dist_triangle_left _ _ _) (le_refl _)
        ... = dist y (Φ p) + dist x (Ψ p) + dist y z : by ring },
    linarith
  end
| (inr x) (inr y) (inl z) := begin
    have B : ∀a b, bdd_below (range (λ (p : γ), dist a (Φ p) + dist b (Ψ p))) :=
      λa b, ⟨0, forall_range_iff.2 (λp, add_nonneg dist_nonneg dist_nonneg)⟩,
    unfold glue_dist,
    have : infi (λp, dist z (Φ p) + dist x (Ψ p)) ≤ dist x y + infi (λp, dist z (Φ p) + dist y (Ψ p)),
    { have : dist x y + infi (λp, dist z (Φ p) + dist y (Ψ p)) =
            infi ((λt, dist x y + t) ∘ (λp, dist z (Φ p) + dist y (Ψ p))),
      { refine map_cinfi_of_continuous_at_of_monotone (continuous_at_const.add continuous_at_id) _
          (B _ _),
        intros x y hx, simpa },
      rw [this, comp],
      refine cinfi_le_cinfi (B _ _) (λp, _),
      calc
        dist z (Φ p) + dist x (Ψ p) ≤ dist z (Φ p) + (dist x y + dist y (Ψ p)) :
          add_le_add (le_refl _) (dist_triangle _ _ _)
        ... = dist x y + (dist z (Φ p) + dist y (Ψ p)) : by ring },
    linarith
  end
| (inl x) (inl y) (inr z) := begin
    have B : ∀a b, bdd_below (range (λ (p : γ), dist a (Φ p) + dist b (Ψ p))) :=
      λa b, ⟨0, forall_range_iff.2 (λp, add_nonneg dist_nonneg dist_nonneg)⟩,
    unfold glue_dist,
    have : infi (λp, dist x (Φ p) + dist z (Ψ p)) ≤ dist x y + infi (λp, dist y (Φ p) + dist z (Ψ p)),
    { have : dist x y + infi (λp, dist y (Φ p) + dist z (Ψ p)) =
            infi ((λt, dist x y + t) ∘ (λp, dist y (Φ p) + dist z (Ψ p))),
      { refine map_cinfi_of_continuous_at_of_monotone (continuous_at_const.add continuous_at_id) _
          (B _ _),
        intros x y hx, simpa },
      rw [this, comp],
      refine cinfi_le_cinfi (B _ _) (λp, _),
      calc
        dist x (Φ p) + dist z (Ψ p) ≤ (dist x y + dist y (Φ p)) + dist z (Ψ p) :
          add_le_add (dist_triangle _ _ _) (le_refl _)
        ... = dist x y + (dist y (Φ p) + dist z (Ψ p)) : by ring },
    linarith
  end
| (inl x) (inr y) (inr z) := begin
    have B : ∀a b, bdd_below (range (λ (p : γ), dist a (Φ p) + dist b (Ψ p))) :=
      λa b, ⟨0, forall_range_iff.2 (λp, add_nonneg dist_nonneg dist_nonneg)⟩,
    unfold glue_dist,
    have : infi (λp, dist x (Φ p) + dist z (Ψ p)) ≤ infi (λp, dist x (Φ p) + dist y (Ψ p)) + dist y z,
    { have : infi (λp, dist x (Φ p) + dist y (Ψ p)) + dist y z =
            infi ((λt, t + dist y z) ∘ (λp, dist x (Φ p) + dist y (Ψ p))),
      { refine map_cinfi_of_continuous_at_of_monotone (continuous_at_id.add continuous_at_const) _
          (B _ _),
        intros x y hx, simpa },
      rw [this, comp],
      refine cinfi_le_cinfi (B _ _) (λp, _),
      calc
        dist x (Φ p) + dist z (Ψ p) ≤ dist x (Φ p) + (dist y z + dist y (Ψ p)) :
          add_le_add (le_refl _) (dist_triangle_left _ _ _)
        ... = dist x (Φ p) + dist y (Ψ p) + dist y z : by ring },
    linarith
  end
| (inl x) (inr y) (inl z) := real.le_of_forall_epsilon_le $ λδ δpos, begin
    have : ∃a ∈ range (λp, dist x (Φ p) + dist y (Ψ p)), a < infi (λp, dist x (Φ p) + dist y (Ψ p)) + δ/2 :=
      exists_lt_of_cInf_lt (range_nonempty _) (by rw [infi]; linarith),
    rcases this with ⟨a, arange, ha⟩,
    rcases mem_range.1 arange with ⟨p, pa⟩,
    rw ← pa at ha,
    have : ∃b ∈ range (λp, dist z (Φ p) + dist y (Ψ p)), b < infi (λp, dist z (Φ p) + dist y (Ψ p)) + δ/2 :=
      exists_lt_of_cInf_lt (range_nonempty _) (by rw [infi]; linarith),
    rcases this with ⟨b, brange, hb⟩,
    rcases mem_range.1 brange with ⟨q, qb⟩,
    rw ← qb at hb,
    have : dist (Φ p) (Φ q) ≤ dist (Ψ p) (Ψ q) + 2 * ε,
      { have := le_trans (le_abs_self _) (H p q), by linarith },
    calc dist x z ≤ dist x (Φ p) + dist (Φ p) (Φ q) + dist (Φ q) z : dist_triangle4 _ _ _ _
      ... ≤ dist x (Φ p) + dist (Ψ p) (Ψ q) + dist z (Φ q) + 2 * ε : by rw [dist_comm z]; linarith
      ... ≤ dist x (Φ p) + (dist y (Ψ p) + dist y (Ψ q)) + dist z (Φ q) + 2 * ε :
        add_le_add (add_le_add (add_le_add (le_refl _) (dist_triangle_left _ _ _)) (le_refl _)) (le_refl _)
      ... ≤ (infi (λp, dist x (Φ p) + dist y (Ψ p)) + ε) + (infi (λp, dist z (Φ p) + dist y (Ψ p)) + ε) + δ :
        by linarith
  end
| (inr x) (inl y) (inr z) := real.le_of_forall_epsilon_le $ λδ δpos, begin
    have : ∃a ∈ range (λp, dist y (Φ p) + dist x (Ψ p)), a < infi (λp, dist y (Φ p) + dist x (Ψ p)) + δ/2 :=
      exists_lt_of_cInf_lt (range_nonempty _) (by rw [infi]; linarith),
    rcases this with ⟨a, arange, ha⟩,
    rcases mem_range.1 arange with ⟨p, pa⟩,
    rw ← pa at ha,
    have : ∃b ∈ range (λp, dist y (Φ p) + dist z (Ψ p)), b < infi (λp, dist y (Φ p) + dist z (Ψ p)) + δ/2 :=
      exists_lt_of_cInf_lt (range_nonempty _) (by rw [infi]; linarith),
    rcases this with ⟨b, brange, hb⟩,
    rcases mem_range.1 brange with ⟨q, qb⟩,
    rw ← qb at hb,
    have : dist (Ψ p) (Ψ q) ≤ dist (Φ p) (Φ q) + 2 * ε,
      { have := le_trans (neg_le_abs_self _) (H p q), by linarith },
    calc dist x z ≤ dist x (Ψ p) + dist (Ψ p) (Ψ q) + dist (Ψ q) z : dist_triangle4 _ _ _ _
      ... ≤ dist x (Ψ p) + dist (Φ p) (Φ q) + dist z (Ψ q) + 2 * ε : by rw [dist_comm z]; linarith
      ... ≤ dist x (Ψ p) + (dist y (Φ p) + dist y (Φ q)) + dist z (Ψ q) + 2 * ε :
        add_le_add (add_le_add (add_le_add (le_refl _) (dist_triangle_left _ _ _)) (le_refl _)) (le_refl _)
      ... ≤ (infi (λp, dist y (Φ p) + dist x (Ψ p)) + ε) + (infi (λp, dist y (Φ p) + dist z (Ψ p)) + ε) + δ :
        by linarith
  end

private lemma glue_eq_of_dist_eq_zero (Φ : γ → α) (Ψ : γ → β) (ε : ℝ) (ε0 : 0 < ε) :
  ∀p q : α ⊕ β, glue_dist Φ Ψ ε p q = 0 → p = q
| (inl x) (inl y) h := by rw eq_of_dist_eq_zero h
| (inl x) (inr y) h := begin
    have : 0 ≤ infi (λp, dist x (Φ p) + dist y (Ψ p)) :=
      le_cinfi (λp, by simpa using add_le_add (@dist_nonneg _ _ x _) (@dist_nonneg _ _ y _)),
    have : 0 + ε ≤ glue_dist Φ Ψ ε (inl x) (inr y) := add_le_add this (le_refl ε),
    exfalso,
    linarith
  end
| (inr x) (inl y) h := begin
    have : 0 ≤ infi (λp, dist y (Φ p) + dist x (Ψ p)) :=
      le_cinfi (λp, by simpa [add_comm]
                         using add_le_add (@dist_nonneg _ _ x _) (@dist_nonneg _ _ y _)),
    have : 0 + ε ≤ glue_dist Φ Ψ ε (inr x) (inl y) := add_le_add this (le_refl ε),
    exfalso,
    linarith
  end
| (inr x) (inr y) h := by rw eq_of_dist_eq_zero h

/-- Given two maps Φ and Ψ intro metric spaces α and β such that the distances between Φ p and Φ q,
and between Ψ p and Ψ q, coincide up to 2 ε where ε > 0, one can almost glue the two spaces α
and β along the images of Φ and Ψ, so that Φ p and Ψ p are at distance ε. -/
def glue_metric_approx (Φ : γ → α) (Ψ : γ → β) (ε : ℝ) (ε0 : 0 < ε)
  (H : ∀p q, abs (dist (Φ p) (Φ q) - dist (Ψ p) (Ψ q)) ≤ 2 * ε) : metric_space (α ⊕ β) :=
{ dist               := glue_dist Φ Ψ ε,
  dist_self          := glue_dist_self Φ Ψ ε,
  dist_comm          := glue_dist_comm Φ Ψ ε,
  dist_triangle      := glue_dist_triangle Φ Ψ ε H,
  eq_of_dist_eq_zero := glue_eq_of_dist_eq_zero Φ Ψ ε ε0 }

end approx_gluing

section sum
/- A particular case of the previous construction is when one uses basepoints in α and β and one
glues only along the basepoints, putting them at distance 1. We give a direct definition of
the distance, without infi, as it is easier to use in applications, and show that it is equal to
the gluing distance defined above to take advantage of the lemmas we have already proved. -/

variables [metric_space α] [metric_space β] [inhabited α] [inhabited β]
open sum (inl inr)

/- Distance on a disjoint union. There are many (noncanonical) ways to put a distance compatible
with each factor.
If the two spaces are bounded, one can say for instance that each point in the first is at distance
`diam α + diam β + 1` of each point in the second.
Instead, we choose a construction that works for unbounded spaces, but requires basepoints.
We embed isometrically each factor, set the basepoints at distance 1,
arbitrarily, and say that the distance from `a` to `b` is the sum of the distances of `a` and `b` to
their respective basepoints, plus the distance 1 between the basepoints.
Since there is an arbitrary choice in this construction, it is not an instance by default. -/

def sum.dist : α ⊕ β → α ⊕ β → ℝ
| (inl a) (inl a') := dist a a'
| (inr b) (inr b') := dist b b'
| (inl a) (inr b)  := dist a (default α) + 1 + dist (default β) b
| (inr b) (inl a)  := dist b (default β) + 1 + dist (default α) a

lemma sum.dist_eq_glue_dist {p q : α ⊕ β} :
  sum.dist p q = glue_dist (λ_ : unit, default α) (λ_ : unit, default β) 1 p q :=
by cases p; cases q; refl <|> simp [sum.dist, glue_dist, dist_comm, add_comm, add_left_comm]

private lemma sum.dist_comm (x y : α ⊕ β) : sum.dist x y = sum.dist y x :=
by cases x; cases y; simp only [sum.dist, dist_comm, add_comm, add_left_comm]

lemma sum.one_dist_le {x : α} {y : β} : 1 ≤ sum.dist (inl x) (inr y) :=
le_trans (le_add_of_nonneg_right dist_nonneg) $
add_le_add_right (le_add_of_nonneg_left dist_nonneg) _

lemma sum.one_dist_le' {x : α} {y : β} : 1 ≤ sum.dist (inr y) (inl x) :=
by rw sum.dist_comm; exact sum.one_dist_le

private lemma sum.mem_uniformity (s : set ((α ⊕ β) × (α ⊕ β))) :
  s ∈ (@uniformity (α ⊕ β) _).sets ↔ ∃ ε > 0, ∀ a b, sum.dist a b < ε → (a, b) ∈ s :=
begin
  split,
  { rintro ⟨hsα, hsβ⟩,
    rcases mem_uniformity_dist.1 hsα with ⟨εα, εα0, hα⟩,
    rcases mem_uniformity_dist.1 hsβ with ⟨εβ, εβ0, hβ⟩,
    refine ⟨min (min εα εβ) 1, lt_min (lt_min εα0 εβ0) zero_lt_one, _⟩,
    rintro (a|a) (b|b) h,
    { exact hα (lt_of_lt_of_le h (le_trans (min_le_left _ _) (min_le_left _ _))) },
    { cases not_le_of_lt (lt_of_lt_of_le h (min_le_right _ _)) sum.one_dist_le },
    { cases not_le_of_lt (lt_of_lt_of_le h (min_le_right _ _)) sum.one_dist_le' },
    { exact hβ (lt_of_lt_of_le h (le_trans (min_le_left _ _) (min_le_right _ _))) } },
  { rintro ⟨ε, ε0, H⟩,
    split; rw [filter.mem_map, mem_uniformity_dist];
      exact ⟨ε, ε0, λ x y h, H _ _ (by exact h)⟩ }
end

/-- The distance on the disjoint union indeed defines a metric space. All the distance properties follow from our
choice of the distance. The harder work is to show that the uniform structure defined by the distance coincides
with the disjoint union uniform structure. -/
def metric_space_sum : metric_space (α ⊕ β) :=
{ dist               := sum.dist,
  dist_self          := λx, by cases x; simp only [sum.dist, dist_self],
  dist_comm          := sum.dist_comm,
  dist_triangle      := λp q r,
    by simp only [dist, sum.dist_eq_glue_dist]; exact glue_dist_triangle _ _ _ (by simp; norm_num) _ _ _,
  eq_of_dist_eq_zero := λp q,
    by simp only [dist, sum.dist_eq_glue_dist]; exact glue_eq_of_dist_eq_zero _ _ _ zero_lt_one _ _,
  to_uniform_space   := sum.uniform_space,
  uniformity_dist    := uniformity_dist_of_mem_uniformity _ _ sum.mem_uniformity }

local attribute [instance] metric_space_sum

lemma sum.dist_eq {x y : α ⊕ β} : dist x y = sum.dist x y := rfl

/-- The left injection of a space in a disjoint union in an isometry -/
lemma isometry_on_inl : isometry (sum.inl : α → (α ⊕ β)) :=
isometry_emetric_iff_metric.2 $ λx y, rfl

/-- The right injection of a space in a disjoint union in an isometry -/
lemma isometry_on_inr : isometry (sum.inr : β → (α ⊕ β)) :=
isometry_emetric_iff_metric.2 $ λx y, rfl

end sum

section gluing
/- Exact gluing of two metric spaces along isometric subsets. -/

variables [nonempty γ] [metric_space γ] [metric_space α] [metric_space β]
          {Φ : γ → α} {Ψ : γ → β} {ε : ℝ}
open sum (inl inr)
local attribute [instance] premetric.dist_setoid

def glue_premetric (hΦ : isometry Φ) (hΨ : isometry Ψ) : premetric_space (α ⊕ β) :=
{ dist          := glue_dist Φ Ψ 0,
  dist_self     := glue_dist_self Φ Ψ 0,
  dist_comm     := glue_dist_comm Φ Ψ 0,
  dist_triangle := glue_dist_triangle Φ Ψ 0 $ λp q, by rw [hΦ.dist_eq, hΨ.dist_eq]; simp }

def glue_space (hΦ : isometry Φ) (hΨ : isometry Ψ) : Type* :=
@metric_quot _ (glue_premetric hΦ hΨ)

instance metric_space_glue_space (hΦ : isometry Φ) (hΨ : isometry Ψ) :
  metric_space (glue_space hΦ hΨ) :=
@premetric.metric_space_quot _ (glue_premetric hΦ hΨ)

def to_glue_l (hΦ : isometry Φ) (hΨ : isometry Ψ) (x : α) : glue_space hΦ hΨ :=
by letI : premetric_space (α ⊕ β) := glue_premetric hΦ hΨ; exact ⟦inl x⟧

def to_glue_r (hΦ : isometry Φ) (hΨ : isometry Ψ) (y : β) : glue_space hΦ hΨ :=
by letI : premetric_space (α ⊕ β) := glue_premetric hΦ hΨ; exact ⟦inr y⟧

instance inhabited_left (hΦ : isometry Φ) (hΨ : isometry Ψ) [inhabited α] :
  inhabited (glue_space hΦ hΨ) :=
⟨to_glue_l _ _ (default _)⟩

instance inhabited_right (hΦ : isometry Φ) (hΨ : isometry Ψ) [inhabited β] :
  inhabited (glue_space hΦ hΨ) :=
⟨to_glue_r _ _ (default _)⟩

lemma to_glue_commute (hΦ : isometry Φ) (hΨ : isometry Ψ) :
  (to_glue_l hΦ hΨ) ∘ Φ = (to_glue_r hΦ hΨ) ∘ Ψ :=
begin
  letI : premetric_space (α ⊕ β) := glue_premetric hΦ hΨ,
  funext,
  simp only [comp, to_glue_l, to_glue_r, quotient.eq],
  exact glue_dist_glued_points Φ Ψ 0 x
end

lemma to_glue_l_isometry (hΦ : isometry Φ) (hΨ : isometry Ψ) : isometry (to_glue_l hΦ hΨ) :=
isometry_emetric_iff_metric.2 $ λ_ _, rfl

lemma to_glue_r_isometry (hΦ : isometry Φ) (hΨ : isometry Ψ) : isometry (to_glue_r hΦ hΨ) :=
isometry_emetric_iff_metric.2 $ λ_ _, rfl

end gluing --section

section inductive_limit
/- In this section, we define the inductive limit of
     f 0        f 1        f 2        f 3
X 0 -----> X 1 -----> X 2 -----> X 3 -----> ...
where the X n are metric spaces and f n isometric embeddings. We do it by defining a premetric
space structure on Σn, X n, where the predistance dist x y is obtained by pushing x and y in a
common X k using composition by the f n, and taking the distance there. This does not depend on
the choice of k as the f n are isometries. The metric space associated to this premetric space
is the desired inductive limit.-/
open nat

variables {X : ℕ → Type u} [∀n, metric_space (X n)] {f : Πn, X n → X (n+1)}

/-- Predistance on the disjoint union Σn, X n. -/
def inductive_limit_dist (f : Πn, X n → X (n+1)) (x y : Σn, X n) : ℝ :=
dist (le_rec_on (le_max_left  x.1 y.1) f x.2 : X (max x.1 y.1))
     (le_rec_on (le_max_right x.1 y.1) f y.2 : X (max x.1 y.1))

/-- The predistance on the disjoint union Σn, X n can be computed in any X k for large enough k.-/
lemma inductive_limit_dist_eq_dist (I : ∀n, isometry (f n))
  (x y : Σn, X n) (m : ℕ) : ∀hx : x.1 ≤ m, ∀hy : y.1 ≤ m,
  inductive_limit_dist f x y = dist (le_rec_on hx f x.2 : X m) (le_rec_on hy f y.2 : X m) :=
begin
  induction m with m hm,
  { assume hx hy,
    have A : max x.1 y.1 = 0, { rw [le_zero_iff_eq.1 hx, le_zero_iff_eq.1 hy], simp },
    unfold inductive_limit_dist,
    congr; simp only [A] },
  { assume hx hy,
    by_cases h : max x.1 y.1 = m.succ,
    { unfold inductive_limit_dist,
      congr; simp only [h] },
    { have : max x.1 y.1 ≤ succ m := by simp [hx, hy],
      have : max x.1 y.1 ≤ m := by simpa [h] using of_le_succ this,
      have xm : x.1 ≤ m := le_trans (le_max_left _ _) this,
      have ym : y.1 ≤ m := le_trans (le_max_right _ _) this,
      rw [le_rec_on_succ xm, le_rec_on_succ ym, (I m).dist_eq],
      exact hm xm ym }}
end

/-- Premetric space structure on Σn, X n.-/
def inductive_premetric (I : ∀n, isometry (f n)) :
  premetric_space (Σn, X n) :=
{ dist          := inductive_limit_dist f,
  dist_self     := λx, by simp [dist, inductive_limit_dist],
  dist_comm     := λx y, begin
    let m := max x.1 y.1,
    have hx : x.1 ≤ m := le_max_left _ _,
    have hy : y.1 ≤ m := le_max_right _ _,
    unfold dist,
    rw [inductive_limit_dist_eq_dist I x y m hx hy, inductive_limit_dist_eq_dist I y x m hy hx,
        dist_comm]
  end,
  dist_triangle := λx y z, begin
    let m := max (max x.1 y.1) z.1,
    have hx : x.1 ≤ m := le_trans (le_max_left _ _) (le_max_left _ _),
    have hy : y.1 ≤ m := le_trans (le_max_right _ _) (le_max_left _ _),
    have hz : z.1 ≤ m := le_max_right _ _,
    calc inductive_limit_dist f x z
      = dist (le_rec_on hx f x.2 : X m) (le_rec_on hz f z.2 : X m) :
        inductive_limit_dist_eq_dist I x z m hx hz
      ... ≤ dist (le_rec_on hx f x.2 : X m) (le_rec_on hy f y.2 : X m)
          + dist (le_rec_on hy f y.2 : X m) (le_rec_on hz f z.2 : X m) :
        dist_triangle _ _ _
      ... = inductive_limit_dist f x y + inductive_limit_dist f y z :
         by rw [inductive_limit_dist_eq_dist I x y m hx hy,
                inductive_limit_dist_eq_dist I y z m hy hz]
  end }

local attribute [instance] inductive_premetric premetric.dist_setoid

/-- The type giving the inductive limit in a metric space context. -/
def inductive_limit (I : ∀n, isometry (f n)) : Type* :=
@metric_quot _ (inductive_premetric I)

/-- Metric space structure on the inductive limit. -/
instance metric_space_inductive_limit (I : ∀n, isometry (f n)) :
  metric_space (inductive_limit I) :=
@premetric.metric_space_quot _ (inductive_premetric I)

/-- Mapping each `X n` to the inductive limit. -/
def to_inductive_limit (I : ∀n, isometry (f n)) (n : ℕ) (x : X n) : metric.inductive_limit I :=
by letI : premetric_space (Σn, X n) := inductive_premetric I; exact ⟦sigma.mk n x⟧

instance (I : ∀ n, isometry (f n)) [inhabited (X 0)] : inhabited (inductive_limit I) :=
⟨to_inductive_limit _ 0 (default _)⟩

/-- The map `to_inductive_limit n` mapping `X n` to the inductive limit is an isometry. -/
lemma to_inductive_limit_isometry (I : ∀n, isometry (f n)) (n : ℕ) :
  isometry (to_inductive_limit I n) := isometry_emetric_iff_metric.2 $ λx y,
begin
  change inductive_limit_dist f ⟨n, x⟩ ⟨n, y⟩ = dist x y,
  rw [inductive_limit_dist_eq_dist I ⟨n, x⟩ ⟨n, y⟩ n (le_refl n) (le_refl n),
      le_rec_on_self, le_rec_on_self]
end

/-- The maps `to_inductive_limit n` are compatible with the maps `f n`. -/
lemma to_inductive_limit_commute (I : ∀n, isometry (f n)) (n : ℕ) :
  (to_inductive_limit I n.succ) ∘ (f n) = to_inductive_limit I n :=
begin
  funext,
  simp only [comp, to_inductive_limit, quotient.eq],
  show inductive_limit_dist f ⟨n.succ, f n x⟩ ⟨n, x⟩ = 0,
  { rw [inductive_limit_dist_eq_dist I ⟨n.succ, f n x⟩ ⟨n, x⟩ n.succ,
        le_rec_on_self, le_rec_on_succ, le_rec_on_self, dist_self],
    exact le_refl _,
    exact le_refl _,
    exact le_succ _ }
end

end inductive_limit --section
end metric --namespace

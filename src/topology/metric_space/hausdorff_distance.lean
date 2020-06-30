/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sébastien Gouëzel
-/
import topology.metric_space.isometry
import topology.instances.ennreal

/-!
# Hausdorff distance

The Hausdorff distance on subsets of a metric (or emetric) space.

Given two subsets `s` and `t` of a metric space, their Hausdorff distance is the smallest `d`
such that any point `s` is within `d` of a point in `t`, and conversely. This quantity
is often infinite (think of `s` bounded and `t` unbounded), and therefore better
expressed in the setting of emetric spaces.

## Main definitions

This files introduces:
* `inf_edist x s`, the infimum edistance of a point `x` to a set `s` in an emetric space
* `Hausdorff_edist s t`, the Hausdorff edistance of two sets in an emetric space
* Versions of these notions on metric spaces, called respectively `inf_dist` and
`Hausdorff_dist`.
-/
noncomputable theory
open_locale classical
universes u v w

open classical set function topological_space filter

namespace emetric

section inf_edist
open_locale ennreal
variables {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] {x y : α} {s t : set α} {Φ : α → β}

/-- The minimal edistance of a point to a set -/
def inf_edist (x : α) (s : set α) : ennreal := Inf ((edist x) '' s)

@[simp] lemma inf_edist_empty : inf_edist x ∅ = ∞ :=
by unfold inf_edist; simp

/-- The edist to a union is the minimum of the edists -/
@[simp] lemma inf_edist_union : inf_edist x (s ∪ t) = inf_edist x s ⊓ inf_edist x t :=
by simp [inf_edist, image_union, Inf_union]

/-- The edist to a singleton is the edistance to the single point of this singleton -/
@[simp] lemma inf_edist_singleton : inf_edist x {y} = edist x y :=
by simp [inf_edist]

/-- The edist to a set is bounded above by the edist to any of its points -/
lemma inf_edist_le_edist_of_mem (h : y ∈ s) : inf_edist x s ≤ edist x y :=
Inf_le ((mem_image _ _ _).2 ⟨y, h, by refl⟩)

/-- If a point `x` belongs to `s`, then its edist to `s` vanishes -/
lemma inf_edist_zero_of_mem (h : x ∈ s) : inf_edist x s = 0 :=
le_zero_iff_eq.1 $ @edist_self _ _ x ▸ inf_edist_le_edist_of_mem h

/-- The edist is monotonous with respect to inclusion -/
lemma inf_edist_le_inf_edist_of_subset (h : s ⊆ t) : inf_edist x t ≤ inf_edist x s :=
Inf_le_Inf (image_subset _ h)

/-- If the edist to a set is `< r`, there exists a point in the set at edistance `< r` -/
lemma exists_edist_lt_of_inf_edist_lt {r : ennreal} (h : inf_edist x s < r) :
  ∃y∈s, edist x y < r :=
let ⟨t, ⟨ht, tr⟩⟩ :=  Inf_lt_iff.1 h in
let ⟨y, ⟨ys, hy⟩⟩ := (mem_image _ _ _).1 ht in
⟨y, ys, by rwa ← hy at tr⟩

/-- The edist of `x` to `s` is bounded by the sum of the edist of `y` to `s` and
the edist from `x` to `y` -/
lemma inf_edist_le_inf_edist_add_edist : inf_edist x s ≤ inf_edist y s + edist x y :=
begin
  have : ∀z ∈ s, Inf (edist x '' s) ≤ edist y z + edist x y := λz hz, calc
    Inf (edist x '' s) ≤ edist x z :
      Inf_le ((mem_image _ _ _).2 ⟨z, hz, by refl⟩)
    ... ≤ edist x y + edist y z : edist_triangle _ _ _
    ... = edist y z + edist x y : add_comm _ _,
  have : (λz, z + edist x y) (Inf (edist y '' s)) = Inf ((λz, z + edist x y) '' (edist y '' s)),
  { refine map_Inf_of_continuous_at_of_monotone _ _ (by simp),
    { exact continuous_at_id.add continuous_at_const },
    { assume a b h, simp, apply add_le_add_right' h }},
  simp only [inf_edist] at this,
  rw [inf_edist, inf_edist, this, ← image_comp],
  simpa only [and_imp, function.comp_app, le_Inf_iff, exists_imp_distrib, ball_image_iff]
end

/-- The edist to a set depends continuously on the point -/
lemma continuous_inf_edist : continuous (λx, inf_edist x s) :=
continuous_of_le_add_edist 1 (by simp) $
  by simp only [one_mul, inf_edist_le_inf_edist_add_edist, forall_2_true_iff]

/-- The edist to a set and to its closure coincide -/
lemma inf_edist_closure : inf_edist x (closure s) = inf_edist x s :=
begin
  refine le_antisymm (inf_edist_le_inf_edist_of_subset subset_closure) _,
  refine ennreal.le_of_forall_epsilon_le (λε εpos h, _),
  have εpos' : (0 : ennreal) < ε := by simpa,
  have : inf_edist x (closure s) < inf_edist x (closure s) + ε/2 :=
    ennreal.lt_add_right h (ennreal.half_pos εpos'),
  rcases exists_edist_lt_of_inf_edist_lt this with ⟨y, ycs, hy⟩,
  -- y : α,  ycs : y ∈ closure s,  hy : edist x y < inf_edist x (closure s) + ↑ε / 2
  rcases emetric.mem_closure_iff.1 ycs (ε/2) (ennreal.half_pos εpos') with ⟨z, zs, dyz⟩,
  -- z : α,  zs : z ∈ s,  dyz : edist y z < ↑ε / 2
  calc inf_edist x s ≤ edist x z : inf_edist_le_edist_of_mem zs
        ... ≤ edist x y + edist y z : edist_triangle _ _ _
        ... ≤ (inf_edist x (closure s) + ε / 2) + (ε/2) : add_le_add (le_of_lt hy) (le_of_lt dyz)
        ... = inf_edist x (closure s) + ↑ε : by rw [add_assoc, ennreal.add_halves]
end

/-- A point belongs to the closure of `s` iff its infimum edistance to this set vanishes -/
lemma mem_closure_iff_inf_edist_zero : x ∈ closure s ↔ inf_edist x s = 0 :=
⟨λh, by rw ← inf_edist_closure; exact inf_edist_zero_of_mem h,
λh, emetric.mem_closure_iff.2 $ λε εpos, exists_edist_lt_of_inf_edist_lt (by rwa h)⟩

/-- Given a closed set `s`, a point belongs to `s` iff its infimum edistance to this set vanishes -/
lemma mem_iff_ind_edist_zero_of_closed (h : is_closed s) : x ∈ s ↔ inf_edist x s = 0 :=
begin
  convert ← mem_closure_iff_inf_edist_zero,
  exact h.closure_eq
end

/-- The infimum edistance is invariant under isometries -/
lemma inf_edist_image (hΦ : isometry Φ) :
  inf_edist (Φ x) (Φ '' t) = inf_edist x t :=
begin
  simp only [inf_edist],
  apply congr_arg,
  ext b, split,
  { assume hb,
    rcases (mem_image _ _ _).1 hb with ⟨y, ⟨hy, hy'⟩⟩,
    rcases (mem_image _ _ _).1 hy with ⟨z, ⟨hz, hz'⟩⟩,
    rw [← hy', ← hz', hΦ x z],
    exact mem_image_of_mem _ hz },
  { assume hb,
    rcases (mem_image _ _ _).1 hb with ⟨y, ⟨hy, hy'⟩⟩,
    rw [← hy', ← hΦ x y],
    exact mem_image_of_mem _ (mem_image_of_mem _ hy) }
end

end inf_edist --section

/-- The Hausdorff edistance between two sets is the smallest `r` such that each set
is contained in the `r`-neighborhood of the other one -/
def Hausdorff_edist {α : Type u} [emetric_space α] (s t : set α) : ennreal :=
  Sup ((λx, inf_edist x t) '' s) ⊔ Sup ((λx, inf_edist x s) '' t)

lemma Hausdorff_edist_def {α : Type u} [emetric_space α] (s t : set α) :
  Hausdorff_edist s t = Sup ((λx, inf_edist x t) '' s) ⊔ Sup ((λx, inf_edist x s) '' t) := rfl

attribute [irreducible] Hausdorff_edist

section Hausdorff_edist
open_locale ennreal
variables {α : Type u} {β : Type v} [emetric_space α] [emetric_space β]
          {x y : α} {s t u : set α} {Φ : α → β}

/-- The Hausdorff edistance of a set to itself vanishes -/
@[simp] lemma Hausdorff_edist_self : Hausdorff_edist s s = 0 :=
begin
  erw [Hausdorff_edist_def, sup_idem, ← le_bot_iff],
  apply Sup_le _,
  simp [le_bot_iff, inf_edist_zero_of_mem, le_refl] {contextual := tt},
end

/-- The Haudorff edistances of `s` to `t` and of `t` to `s` coincide -/
lemma Hausdorff_edist_comm : Hausdorff_edist s t = Hausdorff_edist t s :=
by unfold Hausdorff_edist; apply sup_comm

/-- Bounding the Hausdorff edistance by bounding the edistance of any point
in each set to the other set -/
lemma Hausdorff_edist_le_of_inf_edist {r : ennreal}
  (H1 : ∀x ∈ s, inf_edist x t ≤ r) (H2 : ∀x ∈ t, inf_edist x s ≤ r) :
  Hausdorff_edist s t ≤ r :=
begin
  simp only [Hausdorff_edist, -mem_image, set.ball_image_iff, Sup_le_iff, sup_le_iff],
  exact ⟨H1, H2⟩
end

/-- Bounding the Hausdorff edistance by exhibiting, for any point in each set,
another point in the other set at controlled distance -/
lemma Hausdorff_edist_le_of_mem_edist {r : ennreal}
  (H1 : ∀x ∈ s, ∃y ∈ t, edist x y ≤ r) (H2 : ∀x ∈ t, ∃y ∈ s, edist x y ≤ r) :
  Hausdorff_edist s t ≤ r :=
begin
  refine Hausdorff_edist_le_of_inf_edist _ _,
  { assume x xs,
    rcases H1 x xs with ⟨y, yt, hy⟩,
    exact le_trans (inf_edist_le_edist_of_mem yt) hy },
  { assume x xt,
    rcases H2 x xt with ⟨y, ys, hy⟩,
    exact le_trans (inf_edist_le_edist_of_mem ys) hy }
end

/-- The distance to a set is controlled by the Hausdorff distance -/
lemma inf_edist_le_Hausdorff_edist_of_mem (h : x ∈ s) : inf_edist x t ≤ Hausdorff_edist s t :=
begin
  rw Hausdorff_edist_def,
  refine le_trans (le_Sup _) le_sup_left,
  exact mem_image_of_mem _ h
end

/-- If the Hausdorff distance is `<r`, then any point in one of the sets has
a corresponding point at distance `<r` in the other set -/
lemma exists_edist_lt_of_Hausdorff_edist_lt {r : ennreal} (h : x ∈ s) (H : Hausdorff_edist s t < r) :
  ∃y∈t, edist x y < r :=
exists_edist_lt_of_inf_edist_lt $ calc
  inf_edist x t ≤ Sup ((λx, inf_edist x t) '' s) : le_Sup (mem_image_of_mem _ h)
  ... ≤ Sup ((λx, inf_edist x t) '' s) ⊔ Sup ((λx, inf_edist x s) '' t) : le_sup_left
  ... < r : by rwa Hausdorff_edist_def at H

/-- The distance from `x` to `s`or `t` is controlled in terms of the Hausdorff distance
between `s` and `t` -/
lemma inf_edist_le_inf_edist_add_Hausdorff_edist :
  inf_edist x t ≤ inf_edist x s + Hausdorff_edist s t :=
ennreal.le_of_forall_epsilon_le $ λε εpos h, begin
  have εpos' : (0 : ennreal) < ε := by simpa,
  have : inf_edist x s < inf_edist x s + ε/2 :=
    ennreal.lt_add_right (ennreal.add_lt_top.1 h).1 (ennreal.half_pos εpos'),
  rcases exists_edist_lt_of_inf_edist_lt this with ⟨y, ys, dxy⟩,
  -- y : α,  ys : y ∈ s,  dxy : edist x y < inf_edist x s + ↑ε / 2
  have : Hausdorff_edist s t < Hausdorff_edist s t + ε/2 :=
    ennreal.lt_add_right (ennreal.add_lt_top.1 h).2 (ennreal.half_pos εpos'),
  rcases exists_edist_lt_of_Hausdorff_edist_lt ys this with ⟨z, zt, dyz⟩,
  -- z : α,  zt : z ∈ t,  dyz : edist y z < Hausdorff_edist s t + ↑ε / 2
  calc inf_edist x t ≤ edist x z : inf_edist_le_edist_of_mem zt
    ... ≤ edist x y + edist y z : edist_triangle _ _ _
    ... ≤ (inf_edist x s + ε/2) + (Hausdorff_edist s t + ε/2) : add_le_add (le_of_lt dxy) (le_of_lt dyz)
    ... = inf_edist x s + Hausdorff_edist s t + ε : by simp [ennreal.add_halves, add_comm, add_left_comm]
end

/-- The Hausdorff edistance is invariant under eisometries -/
lemma Hausdorff_edist_image (h : isometry Φ) :
  Hausdorff_edist (Φ '' s) (Φ '' t) = Hausdorff_edist s t :=
begin
  unfold Hausdorff_edist,
  congr,
  { ext b,
    split,
    { assume hb,
      rcases (mem_image _ _ _ ).1 hb with ⟨y, ⟨hy, hy'⟩⟩,
      rcases (mem_image _ _ _ ).1 hy with ⟨z, ⟨hz, hz'⟩⟩,
      rw [← hy', ← hz', inf_edist_image h],
      exact mem_image_of_mem _ hz },
    { assume hb,
      rcases (mem_image _ _ _ ).1 hb with ⟨y, ⟨hy, hy'⟩⟩,
      rw [← hy', ← inf_edist_image h],
      exact mem_image_of_mem _ (mem_image_of_mem _ hy) }},
  { ext b,
    split,
    { assume hb,
      rcases (mem_image _ _ _ ).1 hb with ⟨y, ⟨hy, hy'⟩⟩,
      rcases (mem_image _ _ _ ).1 hy with ⟨z, ⟨hz, hz'⟩⟩,
      rw [← hy', ← hz', inf_edist_image h],
      exact mem_image_of_mem _ hz },
    { assume hb,
      rcases (mem_image _ _ _ ).1 hb with ⟨y, ⟨hy, hy'⟩⟩,
      rw [← hy', ← inf_edist_image h],
      exact mem_image_of_mem _ (mem_image_of_mem _ hy) }}
end

/-- The Hausdorff distance is controlled by the diameter of the union -/
lemma Hausdorff_edist_le_ediam (hs : s.nonempty) (ht : t.nonempty) : Hausdorff_edist s t ≤ diam (s ∪ t) :=
begin
  rcases hs with ⟨x, xs⟩,
  rcases ht with ⟨y, yt⟩,
  refine Hausdorff_edist_le_of_mem_edist _ _,
  { exact λz hz, ⟨y, yt, edist_le_diam_of_mem (subset_union_left _ _ hz) (subset_union_right _ _ yt)⟩ },
  { exact λz hz, ⟨x, xs, edist_le_diam_of_mem (subset_union_right _ _ hz) (subset_union_left _ _ xs)⟩ }
end

/-- The Hausdorff distance satisfies the triangular inequality -/
lemma Hausdorff_edist_triangle : Hausdorff_edist s u ≤ Hausdorff_edist s t + Hausdorff_edist t u :=
begin
  rw Hausdorff_edist_def,
  simp only [and_imp, set.mem_image, Sup_le_iff, exists_imp_distrib,
             sup_le_iff, -mem_image, set.ball_image_iff],
  split,
  show ∀x ∈ s, inf_edist x u ≤ Hausdorff_edist s t + Hausdorff_edist t u, from λx xs, calc
    inf_edist x u ≤ inf_edist x t + Hausdorff_edist t u : inf_edist_le_inf_edist_add_Hausdorff_edist
    ... ≤ Hausdorff_edist s t + Hausdorff_edist t u :
      add_le_add_right' (inf_edist_le_Hausdorff_edist_of_mem  xs),
  show ∀x ∈ u, inf_edist x s ≤ Hausdorff_edist s t + Hausdorff_edist t u, from λx xu, calc
    inf_edist x s ≤ inf_edist x t + Hausdorff_edist t s : inf_edist_le_inf_edist_add_Hausdorff_edist
    ... ≤ Hausdorff_edist u t + Hausdorff_edist t s :
      add_le_add_right' (inf_edist_le_Hausdorff_edist_of_mem xu)
    ... = Hausdorff_edist s t + Hausdorff_edist t u : by simp [Hausdorff_edist_comm, add_comm]
end

/-- The Hausdorff edistance between a set and its closure vanishes -/
@[simp, priority 1100]
lemma Hausdorff_edist_self_closure : Hausdorff_edist s (closure s) = 0 :=
begin
  erw ← le_bot_iff,
  simp only [Hausdorff_edist, inf_edist_closure, -le_zero_iff_eq, and_imp,
    set.mem_image, Sup_le_iff, exists_imp_distrib, sup_le_iff,
    set.ball_image_iff, ennreal.bot_eq_zero, -mem_image],
  simp only [inf_edist_zero_of_mem, mem_closure_iff_inf_edist_zero, le_refl, and_self,
             forall_true_iff] {contextual := tt}
end

/-- Replacing a set by its closure does not change the Hausdorff edistance. -/
@[simp] lemma Hausdorff_edist_closure₁ : Hausdorff_edist (closure s) t = Hausdorff_edist s t :=
begin
  refine le_antisymm _ _,
  { calc  _ ≤ Hausdorff_edist (closure s) s + Hausdorff_edist s t : Hausdorff_edist_triangle
    ... = Hausdorff_edist s t : by simp [Hausdorff_edist_comm] },
  { calc _ ≤ Hausdorff_edist s (closure s) + Hausdorff_edist (closure s) t : Hausdorff_edist_triangle
    ... = Hausdorff_edist (closure s) t : by simp }
end

/-- Replacing a set by its closure does not change the Hausdorff edistance. -/
@[simp] lemma Hausdorff_edist_closure₂ : Hausdorff_edist s (closure t) = Hausdorff_edist s t :=
by simp [@Hausdorff_edist_comm _ _ s _]

/-- The Hausdorff edistance between sets or their closures is the same -/
@[simp] lemma Hausdorff_edist_closure : Hausdorff_edist (closure s) (closure t) = Hausdorff_edist s t :=
by simp

/-- Two sets are at zero Hausdorff edistance if and only if they have the same closure -/
lemma Hausdorff_edist_zero_iff_closure_eq_closure : Hausdorff_edist s t = 0 ↔ closure s = closure t :=
⟨begin
  assume h,
  refine subset.antisymm _ _,
  { have : s ⊆ closure t := λx xs, mem_closure_iff_inf_edist_zero.2 $ begin
      erw ← le_bot_iff,
      have := @inf_edist_le_Hausdorff_edist_of_mem _ _ _ _ t xs,
      rwa h at this,
    end,
    by rw ← @closure_closure _ _ t; exact closure_mono this },
  { have : t ⊆ closure s := λx xt, mem_closure_iff_inf_edist_zero.2 $ begin
      erw ← le_bot_iff,
      have := @inf_edist_le_Hausdorff_edist_of_mem _ _ _ _ s xt,
      rw Hausdorff_edist_comm at h,
      rwa h at this,
    end,
    by rw ← @closure_closure _ _ s; exact closure_mono this }
end,
λh, by rw [← Hausdorff_edist_closure, h, Hausdorff_edist_self]⟩

/-- Two closed sets are at zero Hausdorff edistance if and only if they coincide -/
lemma Hausdorff_edist_zero_iff_eq_of_closed (hs : is_closed s) (ht : is_closed t) :
  Hausdorff_edist s t = 0 ↔ s = t :=
by rw [Hausdorff_edist_zero_iff_closure_eq_closure, hs.closure_eq,
       ht.closure_eq]

/-- The Haudorff edistance to the empty set is infinite -/
lemma Hausdorff_edist_empty (ne : s.nonempty) : Hausdorff_edist s ∅ = ∞ :=
begin
  rcases ne with ⟨x, xs⟩,
  have : inf_edist x ∅ ≤ Hausdorff_edist s ∅ := inf_edist_le_Hausdorff_edist_of_mem xs,
  simpa using this,
end

/-- If a set is at finite Hausdorff edistance of a nonempty set, it is nonempty -/
lemma nonempty_of_Hausdorff_edist_ne_top (hs : s.nonempty) (fin : Hausdorff_edist s t ≠ ⊤) :
  t.nonempty :=
t.eq_empty_or_nonempty.elim (λ ht, (fin $ ht.symm ▸ Hausdorff_edist_empty hs).elim) id

lemma empty_or_nonempty_of_Hausdorff_edist_ne_top (fin : Hausdorff_edist s t ≠ ⊤) :
  s = ∅ ∧ t = ∅ ∨ s.nonempty ∧ t.nonempty :=
begin
  cases s.eq_empty_or_nonempty with hs hs,
  { cases t.eq_empty_or_nonempty with ht ht,
    { exact or.inl ⟨hs, ht⟩ },
    { rw Hausdorff_edist_comm at fin,
      exact or.inr ⟨nonempty_of_Hausdorff_edist_ne_top ht fin, ht⟩ } },
  { exact or.inr ⟨hs, nonempty_of_Hausdorff_edist_ne_top hs fin⟩ }
end

end Hausdorff_edist -- section
end emetric --namespace


/-Now, we turn to the same notions in metric spaces. To avoid the difficulties related to
Inf and Sup on ℝ (which is only conditionnally complete), we use the notions in ennreal formulated
in terms of the edistance, and coerce them to ℝ. Then their properties follow readily from the
corresponding properties in ennreal, modulo some tedious rewriting of inequalities from one to the
other -/

namespace metric
section
variables {α : Type u} {β : Type v} [metric_space α] [metric_space β] {s t u : set α} {x y : α} {Φ : α → β}
open emetric

/-- The minimal distance of a point to a set -/
def inf_dist (x : α) (s : set α) : ℝ := ennreal.to_real (inf_edist x s)

/-- the minimal distance is always nonnegative -/
lemma inf_dist_nonneg : 0 ≤ inf_dist x s := by simp [inf_dist]

/-- the minimal distance to the empty set is 0 (if you want to have the more reasonable
value ∞ instead, use `inf_edist`, which takes values in ennreal) -/
@[simp] lemma inf_dist_empty : inf_dist x ∅ = 0 :=
by simp [inf_dist]

/-- In a metric space, the minimal edistance to a nonempty set is finite -/
lemma inf_edist_ne_top (h : s.nonempty) : inf_edist x s ≠ ⊤ :=
begin
  rcases h with ⟨y, hy⟩,
  apply lt_top_iff_ne_top.1,
  calc inf_edist x s ≤ edist x y : inf_edist_le_edist_of_mem hy
       ... < ⊤ : lt_top_iff_ne_top.2 (edist_ne_top _ _)
end

/-- The minimal distance of a point to a set containing it vanishes -/
lemma inf_dist_zero_of_mem (h : x ∈ s) : inf_dist x s = 0 :=
by simp [inf_edist_zero_of_mem h, inf_dist]

/-- The minimal distance to a singleton is the distance to the unique point in this singleton -/
@[simp] lemma inf_dist_singleton : inf_dist x {y} = dist x y :=
by simp [inf_dist, inf_edist, dist_edist]

/-- The minimal distance to a set is bounded by the distance to any point in this set -/
lemma inf_dist_le_dist_of_mem (h : y ∈ s) : inf_dist x s ≤ dist x y :=
begin
  rw [dist_edist, inf_dist, ennreal.to_real_le_to_real (inf_edist_ne_top ⟨_, h⟩) (edist_ne_top _ _)],
  exact inf_edist_le_edist_of_mem h
end

/-- The minimal distance is monotonous with respect to inclusion -/
lemma inf_dist_le_inf_dist_of_subset (h : s ⊆ t) (hs : s.nonempty) :
  inf_dist x t ≤ inf_dist x s :=
begin
  have ht : t.nonempty := hs.mono h,
  rw [inf_dist, inf_dist, ennreal.to_real_le_to_real (inf_edist_ne_top ht) (inf_edist_ne_top hs)],
  exact inf_edist_le_inf_edist_of_subset h
end

/-- If the minimal distance to a set is `<r`, there exists a point in this set at distance `<r` -/
lemma exists_dist_lt_of_inf_dist_lt {r : real} (h : inf_dist x s < r) (hs : s.nonempty) :
  ∃y∈s, dist x y < r :=
begin
  have rpos : 0 < r := lt_of_le_of_lt inf_dist_nonneg h,
  have : inf_edist x s < ennreal.of_real r,
  { rwa [inf_dist, ← ennreal.to_real_of_real (le_of_lt rpos), ennreal.to_real_lt_to_real (inf_edist_ne_top hs)] at h,
    simp },
  rcases exists_edist_lt_of_inf_edist_lt this with ⟨y, ys, hy⟩,
  rw [edist_dist, ennreal.of_real_lt_of_real_iff rpos] at hy,
  exact ⟨y, ys, hy⟩,
end

/-- The minimal distance from `x` to `s` is bounded by the distance from `y` to `s`, modulo
the distance between `x` and `y` -/
lemma inf_dist_le_inf_dist_add_dist : inf_dist x s ≤ inf_dist y s + dist x y :=
begin
  cases s.eq_empty_or_nonempty with hs hs,
  { by simp [hs, dist_nonneg] },
  { rw [inf_dist, inf_dist, dist_edist, ← ennreal.to_real_add (inf_edist_ne_top hs) (edist_ne_top _ _),
        ennreal.to_real_le_to_real (inf_edist_ne_top hs)],
    { apply inf_edist_le_inf_edist_add_edist },
    { simp [ennreal.add_eq_top, inf_edist_ne_top hs, edist_ne_top] }}
end

variable (s)

/-- The minimal distance to a set is Lipschitz in point with constant 1 -/
lemma lipschitz_inf_dist_pt : lipschitz_with 1 (λx, inf_dist x s) :=
lipschitz_with.of_le_add $ λ x y, inf_dist_le_inf_dist_add_dist

/-- The minimal distance to a set is uniformly continuous in point -/
lemma uniform_continuous_inf_dist_pt :
  uniform_continuous (λx, inf_dist x s) :=
(lipschitz_inf_dist_pt s).uniform_continuous

/-- The minimal distance to a set is continuous in point -/
lemma continuous_inf_dist_pt : continuous (λx, inf_dist x s) :=
(uniform_continuous_inf_dist_pt s).continuous

variable {s}

/-- The minimal distance to a set and its closure coincide -/
lemma inf_dist_eq_closure : inf_dist x (closure s) = inf_dist x s :=
by simp [inf_dist, inf_edist_closure]

/-- A point belongs to the closure of `s` iff its infimum distance to this set vanishes -/
lemma mem_closure_iff_inf_dist_zero (h : s.nonempty) : x ∈ closure s ↔ inf_dist x s = 0 :=
by simp [mem_closure_iff_inf_edist_zero, inf_dist, ennreal.to_real_eq_zero_iff, inf_edist_ne_top h]

/-- Given a closed set `s`, a point belongs to `s` iff its infimum distance to this set vanishes -/
lemma mem_iff_inf_dist_zero_of_closed (h : is_closed s) (hs : s.nonempty) :
  x ∈ s ↔ inf_dist x s = 0 :=
begin
  have := @mem_closure_iff_inf_dist_zero _ _ s x hs,
  rwa h.closure_eq at this
end

/-- The infimum distance is invariant under isometries -/
lemma inf_dist_image (hΦ : isometry Φ) :
  inf_dist (Φ x) (Φ '' t) = inf_dist x t :=
by simp [inf_dist, inf_edist_image hΦ]

/-- The Hausdorff distance between two sets is the smallest nonnegative `r` such that each set is
included in the `r`-neighborhood of the other. If there is no such `r`, it is defined to
be `0`, arbitrarily -/
def Hausdorff_dist (s t : set α) : ℝ := ennreal.to_real (Hausdorff_edist s t)

/-- The Hausdorff distance is nonnegative -/
lemma Hausdorff_dist_nonneg : 0 ≤ Hausdorff_dist s t :=
by simp [Hausdorff_dist]

/-- If two sets are nonempty and bounded in a metric space, they are at finite Hausdorff edistance -/
lemma Hausdorff_edist_ne_top_of_nonempty_of_bounded (hs : s.nonempty) (ht : t.nonempty)
  (bs : bounded s) (bt : bounded t) : Hausdorff_edist s t ≠ ⊤ :=
begin
  rcases hs with ⟨cs, hcs⟩,
  rcases ht with ⟨ct, hct⟩,
  rcases (bounded_iff_subset_ball ct).1 bs with ⟨rs, hrs⟩,
  rcases (bounded_iff_subset_ball cs).1 bt with ⟨rt, hrt⟩,
  have : Hausdorff_edist s t ≤ ennreal.of_real (max rs rt),
  { apply Hausdorff_edist_le_of_mem_edist,
    { assume x xs,
      existsi [ct, hct],
      have : dist x ct ≤ max rs rt := le_trans (hrs xs) (le_max_left _ _),
      rwa [edist_dist, ennreal.of_real_le_of_real_iff],
      exact le_trans dist_nonneg this },
    { assume x xt,
      existsi [cs, hcs],
      have : dist x cs ≤ max rs rt := le_trans (hrt xt) (le_max_right _ _),
      rwa [edist_dist, ennreal.of_real_le_of_real_iff],
      exact le_trans dist_nonneg this }},
  exact ennreal.lt_top_iff_ne_top.1 (lt_of_le_of_lt this (by simp [lt_top_iff_ne_top]))
end

/-- The Hausdorff distance between a set and itself is zero -/
@[simp] lemma Hausdorff_dist_self_zero : Hausdorff_dist s s = 0 :=
by simp [Hausdorff_dist]

/-- The Hausdorff distance from `s` to `t` and from `t` to `s` coincide -/
lemma Hausdorff_dist_comm : Hausdorff_dist s t = Hausdorff_dist t s :=
by simp [Hausdorff_dist, Hausdorff_edist_comm]

/-- The Hausdorff distance to the empty set vanishes (if you want to have the more reasonable
value ∞ instead, use `Hausdorff_edist`, which takes values in ennreal) -/
@[simp] lemma Hausdorff_dist_empty : Hausdorff_dist s ∅ = 0 :=
begin
  cases s.eq_empty_or_nonempty with h h,
  { simp [h] },
  { simp [Hausdorff_dist, Hausdorff_edist_empty h] }
end

/-- The Hausdorff distance to the empty set vanishes (if you want to have the more reasonable
value ∞ instead, use `Hausdorff_edist`, which takes values in ennreal) -/
@[simp] lemma Hausdorff_dist_empty' : Hausdorff_dist ∅ s = 0 :=
by simp [Hausdorff_dist_comm]

/-- Bounding the Hausdorff distance by bounding the distance of any point
in each set to the other set -/
lemma Hausdorff_dist_le_of_inf_dist {r : ℝ} (hr : r ≥ 0)
  (H1 : ∀x ∈ s, inf_dist x t ≤ r) (H2 : ∀x ∈ t, inf_dist x s ≤ r) :
  Hausdorff_dist s t ≤ r :=
begin
  by_cases h1 : Hausdorff_edist s t = ⊤,
    by rwa [Hausdorff_dist, h1, ennreal.top_to_real],
  cases s.eq_empty_or_nonempty with hs hs,
    by rwa [hs, Hausdorff_dist_empty'],
  cases t.eq_empty_or_nonempty with ht ht,
    by rwa [ht, Hausdorff_dist_empty],
  have : Hausdorff_edist s t ≤ ennreal.of_real r,
  { apply Hausdorff_edist_le_of_inf_edist _ _,
    { assume x hx,
      have I := H1 x hx,
      rwa [inf_dist, ← ennreal.to_real_of_real hr,
           ennreal.to_real_le_to_real (inf_edist_ne_top ht) ennreal.of_real_ne_top] at I },
    { assume x hx,
      have I := H2 x hx,
      rwa [inf_dist, ← ennreal.to_real_of_real hr,
           ennreal.to_real_le_to_real (inf_edist_ne_top hs) ennreal.of_real_ne_top] at I }},
  rwa [Hausdorff_dist, ← ennreal.to_real_of_real hr,
       ennreal.to_real_le_to_real h1 ennreal.of_real_ne_top]
end

/-- Bounding the Hausdorff distance by exhibiting, for any point in each set,
another point in the other set at controlled distance -/
lemma Hausdorff_dist_le_of_mem_dist {r : ℝ} (hr : 0 ≤ r)
  (H1 : ∀x ∈ s, ∃y ∈ t, dist x y ≤ r) (H2 : ∀x ∈ t, ∃y ∈ s, dist x y ≤ r) :
  Hausdorff_dist s t ≤ r :=
begin
  apply Hausdorff_dist_le_of_inf_dist hr,
  { assume x xs,
    rcases H1 x xs with ⟨y, yt, hy⟩,
    exact le_trans (inf_dist_le_dist_of_mem yt) hy },
  { assume x xt,
    rcases H2 x xt with ⟨y, ys, hy⟩,
    exact le_trans (inf_dist_le_dist_of_mem ys) hy }
end

/-- The Hausdorff distance is controlled by the diameter of the union -/
lemma Hausdorff_dist_le_diam (hs : s.nonempty) (bs : bounded s) (ht : t.nonempty) (bt : bounded t) :
  Hausdorff_dist s t ≤ diam (s ∪ t) :=
begin
  rcases hs with ⟨x, xs⟩,
  rcases ht with ⟨y, yt⟩,
  refine Hausdorff_dist_le_of_mem_dist diam_nonneg _ _,
  { exact  λz hz, ⟨y, yt, dist_le_diam_of_mem (bounded_union.2 ⟨bs, bt⟩)
      (subset_union_left _ _ hz) (subset_union_right _ _ yt)⟩ },
  { exact λz hz, ⟨x, xs, dist_le_diam_of_mem (bounded_union.2 ⟨bs, bt⟩)
      (subset_union_right _ _ hz) (subset_union_left _ _ xs)⟩ }
end

/-- The distance to a set is controlled by the Hausdorff distance -/
lemma inf_dist_le_Hausdorff_dist_of_mem (hx : x ∈ s) (fin : Hausdorff_edist s t ≠ ⊤) :
  inf_dist x t ≤ Hausdorff_dist s t :=
begin
  have ht : t.nonempty := nonempty_of_Hausdorff_edist_ne_top ⟨x, hx⟩ fin,
  rw [Hausdorff_dist, inf_dist, ennreal.to_real_le_to_real (inf_edist_ne_top ht) fin],
  exact inf_edist_le_Hausdorff_edist_of_mem hx
end

/-- If the Hausdorff distance is `<r`, then any point in one of the sets is at distance
`<r` of a point in the other set -/
lemma exists_dist_lt_of_Hausdorff_dist_lt {r : ℝ} (h : x ∈ s) (H : Hausdorff_dist s t < r)
  (fin : Hausdorff_edist s t ≠ ⊤) : ∃y∈t, dist x y < r :=
begin
  have r0 : 0 < r := lt_of_le_of_lt (Hausdorff_dist_nonneg) H,
  have : Hausdorff_edist s t < ennreal.of_real r,
    by rwa [Hausdorff_dist, ← ennreal.to_real_of_real (le_of_lt r0),
            ennreal.to_real_lt_to_real fin (ennreal.of_real_ne_top)] at H,
  rcases exists_edist_lt_of_Hausdorff_edist_lt h this with ⟨y, hy, yr⟩,
  rw [edist_dist, ennreal.of_real_lt_of_real_iff r0] at yr,
  exact ⟨y, hy, yr⟩
end

/-- If the Hausdorff distance is `<r`, then any point in one of the sets is at distance
`<r` of a point in the other set -/
lemma exists_dist_lt_of_Hausdorff_dist_lt' {r : ℝ} (h : y ∈ t) (H : Hausdorff_dist s t < r)
  (fin : Hausdorff_edist s t ≠ ⊤) : ∃x∈s, dist x y < r :=
begin
  rw Hausdorff_dist_comm at H,
  rw Hausdorff_edist_comm at fin,
  simpa [dist_comm] using exists_dist_lt_of_Hausdorff_dist_lt h H fin
end

/-- The infimum distance to `s` and `t` are the same, up to the Hausdorff distance
between `s` and `t` -/
lemma inf_dist_le_inf_dist_add_Hausdorff_dist (fin : Hausdorff_edist s t ≠ ⊤) :
  inf_dist x t ≤ inf_dist x s + Hausdorff_dist s t :=
begin
  rcases empty_or_nonempty_of_Hausdorff_edist_ne_top fin with ⟨hs,ht⟩|⟨hs,ht⟩,
  { simp only [hs, ht, Hausdorff_dist_empty, inf_dist_empty, zero_add] },
  rw [inf_dist, inf_dist, Hausdorff_dist, ← ennreal.to_real_add (inf_edist_ne_top hs) fin,
      ennreal.to_real_le_to_real (inf_edist_ne_top ht)],
  { exact inf_edist_le_inf_edist_add_Hausdorff_edist },
  { exact ennreal.add_ne_top.2 ⟨inf_edist_ne_top hs, fin⟩ }
end

/-- The Hausdorff distance is invariant under isometries -/
lemma Hausdorff_dist_image (h : isometry Φ) :
  Hausdorff_dist (Φ '' s) (Φ '' t) = Hausdorff_dist s t :=
by simp [Hausdorff_dist, Hausdorff_edist_image h]

/-- The Hausdorff distance satisfies the triangular inequality -/
lemma Hausdorff_dist_triangle (fin : Hausdorff_edist s t ≠ ⊤) :
  Hausdorff_dist s u ≤ Hausdorff_dist s t + Hausdorff_dist t u :=
begin
  by_cases Hausdorff_edist s u = ⊤,
  { calc Hausdorff_dist s u = 0 + 0 : by simp [Hausdorff_dist, h]
         ... ≤ Hausdorff_dist s t + Hausdorff_dist t u :
           add_le_add (Hausdorff_dist_nonneg) (Hausdorff_dist_nonneg) },
  { have Dtu : Hausdorff_edist t u < ⊤ := calc
      Hausdorff_edist t u ≤ Hausdorff_edist t s + Hausdorff_edist s u : Hausdorff_edist_triangle
      ... = Hausdorff_edist s t + Hausdorff_edist s u : by simp [Hausdorff_edist_comm]
      ... < ⊤ : by simp  [ennreal.add_lt_top]; simp [ennreal.lt_top_iff_ne_top, h, fin],
    rw [Hausdorff_dist, Hausdorff_dist, Hausdorff_dist,
        ← ennreal.to_real_add fin (lt_top_iff_ne_top.1 Dtu), ennreal.to_real_le_to_real h],
    { exact Hausdorff_edist_triangle },
    { simp [ennreal.add_eq_top, lt_top_iff_ne_top.1 Dtu, fin] }}
end

/-- The Hausdorff distance satisfies the triangular inequality -/
lemma Hausdorff_dist_triangle' (fin : Hausdorff_edist t u ≠ ⊤) :
  Hausdorff_dist s u ≤ Hausdorff_dist s t + Hausdorff_dist t u :=
begin
  rw Hausdorff_edist_comm at fin,
  have I : Hausdorff_dist u s ≤ Hausdorff_dist u t + Hausdorff_dist t s := Hausdorff_dist_triangle fin,
  simpa [add_comm, Hausdorff_dist_comm] using I
end

/-- The Hausdorff distance between a set and its closure vanish -/
@[simp, priority 1100]
lemma Hausdorff_dist_self_closure : Hausdorff_dist s (closure s) = 0 :=
by simp [Hausdorff_dist]

/-- Replacing a set by its closure does not change the Hausdorff distance. -/
@[simp] lemma Hausdorff_dist_closure₁ : Hausdorff_dist (closure s) t = Hausdorff_dist s t :=
by simp [Hausdorff_dist]

/-- Replacing a set by its closure does not change the Hausdorff distance. -/
@[simp] lemma Hausdorff_dist_closure₂ : Hausdorff_dist s (closure t) = Hausdorff_dist s t :=
by simp [Hausdorff_dist]

/-- The Hausdorff distance between two sets and their closures coincide -/
@[simp] lemma Hausdorff_dist_closure : Hausdorff_dist (closure s) (closure t) = Hausdorff_dist s t :=
by simp [Hausdorff_dist]

/-- Two sets are at zero Hausdorff distance if and only if they have the same closures -/
lemma Hausdorff_dist_zero_iff_closure_eq_closure (fin : Hausdorff_edist s t ≠ ⊤) :
  Hausdorff_dist s t = 0 ↔ closure s = closure t :=
by simp [Hausdorff_edist_zero_iff_closure_eq_closure.symm, Hausdorff_dist,
         ennreal.to_real_eq_zero_iff, fin]

/-- Two closed sets are at zero Hausdorff distance if and only if they coincide -/
lemma Hausdorff_dist_zero_iff_eq_of_closed (hs : is_closed s) (ht : is_closed t)
  (fin : Hausdorff_edist s t ≠ ⊤) : Hausdorff_dist s t = 0 ↔ s = t :=
by simp [(Hausdorff_edist_zero_iff_eq_of_closed hs ht).symm, Hausdorff_dist,
         ennreal.to_real_eq_zero_iff, fin]

end --section
end metric --namespace

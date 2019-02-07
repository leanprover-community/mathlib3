/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sébastien Gouëzel
The Hausdorff distance on subsets of a metric (or emetric) space.
Given two subsets `s` and `t` of a metric space, their Hausdorff distance is the smallest `d`
such that any point `s` is within `d` of a point in `t`, and conversely. This quantity
is often infinite (think of `s` bounded and `t` unbounded), and therefore better
expressed in the setting of emetric spaces.
This files introduces:
* `inf_edist x s`, the infimum edistance of a point `x` to a set `s` in an emetric space
* `Hausdorff_edist s t`, the Hausdorff edistance of two sets in an emetric space
* The sets of closed sets, and of nonempty compact sets, become emetric spaces when endowed
with the Hausdorff edistance. They are complete (resp. compact) when the ambient space is
complete (resp. compact). The latter is also second countable when the ambient space is.
* Versions of these notions on metric spaces, called respectively `inf_dist` and
`Hausdorff_dist`.
In particular, in a metric space, the space of nonempty compact subsets inherits a metric space
structure, as the Hausdorff edistance between such sets is finite.
-/

import topology.metric_space.isometry topology.instances.ennreal data.real.cau_seq_filter
       topology.metric_space.lipschitz
noncomputable theory
local attribute [instance, priority 0] classical.prop_decidable
universes u v w

open classical lattice set function topological_space filter

/-- The type of closed subsets of a topological space. -/
def closeds (α : Type u) [topological_space α] := {s : set α // is_closed s}

/-- The space of non-empty compact subsets of a topological space. The
non-emptiness will be useful in metric spaces, as we will be able to put
a distance (and not merely an edistance) on this space. -/
def nonempty_compacts (α : Type u) [topological_space α] := {s : set α // s ≠ ∅ ∧ compact s}

instance nonempty_compacts.to_compact_space (α : Type u) [topological_space α] {p : nonempty_compacts α} :
  compact_space p.val :=
⟨compact_iff_compact_univ.1 p.property.2⟩

instance nonempty_compacts.to_nonempty (α : Type u) [topological_space α] {p : nonempty_compacts α} :
  nonempty p.val :=
nonempty_subtype.2 $ ne_empty_iff_exists_mem.1 p.property.1

/-- Associate to a nonempty compact subset the corresponding closed subset -/
def nonempty_compacts.to_closeds {α : Type u} [topological_space α] [t2_space α]
  (s : nonempty_compacts α) : closeds α :=
⟨s.val, closed_of_compact _ s.property.2⟩


namespace emetric

section inf_edist
local notation `∞` := (⊤ : ennreal)
variables {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] {x y : α} {s t : set α} {Φ : α → β}

/-- The minimal edistance of a point to a set -/
def inf_edist (x : α) (s : set α) : ennreal := Inf ((edist x) '' s)

@[simp] lemma inf_edist_empty : inf_edist x ∅ = ∞ :=
by unfold inf_edist; simp

/-- If a point `x` belongs to `s`, then its edist to `s` vanishes -/
lemma inf_edist_zero_of_mem (h : x ∈ s) : inf_edist x s = 0 :=
begin
  refine le_zero_iff_eq.1 (Inf_le _),
  rw ← @edist_self _ _ x,
  exact mem_image_of_mem _ h,
end

/-- The edist to a union is the minimum of the edists -/
@[simp] lemma inf_edist_union : inf_edist x (s ∪ t) = inf_edist x s ⊓ inf_edist x t :=
by simp [inf_edist, image_union, Inf_union]

/-- The edist to a singleton is the edistance to the single point of this singleton -/
@[simp] lemma inf_edist_singleton : inf_edist x {y} = edist x y :=
by simp [inf_edist]

/-- The edist to a set is bounded above by the edist to any of its points -/
lemma inf_edist_le_edist_of_mem (h : y ∈ s) : inf_edist x s ≤ edist x y :=
Inf_le ((mem_image _ _ _).2 ⟨y, h, by refl⟩)

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
  { refine Inf_of_continuous _ _ (by simp),
    { exact continuous_add continuous_id continuous_const },
    { assume a b h, simp, apply add_le_add_right' h }},
  simp only [inf_edist] at this,
  rw [inf_edist, inf_edist, this, ← image_comp],
  simpa only [and_imp, function.comp_app, lattice.le_Inf_iff, exists_imp_distrib, ball_image_iff]
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
  rcases emetric.mem_closure_iff'.1 ycs (ε/2) (ennreal.half_pos εpos') with ⟨z, zs, dyz⟩,
  -- z : α,  zs : z ∈ s,  dyz : edist y z < ↑ε / 2
  calc inf_edist x s ≤ edist x z : inf_edist_le_edist_of_mem zs
        ... ≤ edist x y + edist y z : edist_triangle _ _ _
        ... ≤ (inf_edist x (closure s) + ε / 2) + (ε/2) : add_le_add' (le_of_lt hy) (le_of_lt dyz)
        ... = inf_edist x (closure s) + ↑ε : by simp [ennreal.add_halves]
end

/-- A point belongs to the closure of `s` iff its infimum edistance to this set vanishes -/
lemma mem_closure_iff_inf_edist_zero : x ∈ closure s ↔ inf_edist x s = 0 :=
⟨λh, by rw ← inf_edist_closure; exact inf_edist_zero_of_mem h,
λh, emetric.mem_closure_iff'.2 $ λε εpos, exists_edist_lt_of_inf_edist_lt (by rwa h)⟩

/-- Given a closed set `s`, a point belongs to `s` iff its infimum edistance to this set vanishes -/
lemma mem_iff_ind_edist_zero_of_closed (h : is_closed s) : x ∈ s ↔ inf_edist x s = 0 :=
begin
  have := @mem_closure_iff_inf_edist_zero _ _ x s,
  rwa closure_eq_iff_is_closed.2 h at this
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

section Hausdorff_edist
local notation `∞` := (⊤ : ennreal)
variables {α : Type u} {β : Type v} [emetric_space α] [emetric_space β]
          {x y : α} {s t u : set α} {Φ : α → β}

/-- The Hausdorff edistance of a set to itself vanishes -/
@[simp] lemma Hausdorff_edist_self : Hausdorff_edist s s = 0 :=
begin
  unfold Hausdorff_edist,
  erw [lattice.sup_idem, ← le_bot_iff],
  apply Sup_le _,
  simp [le_bot_iff, inf_edist_zero_of_mem] {contextual := tt},
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
  simp only [Hausdorff_edist, -mem_image, set.ball_image_iff, lattice.Sup_le_iff, lattice.sup_le_iff],
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
  ... < r : H

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
    ... ≤ (inf_edist x s + ε/2) + (Hausdorff_edist s t + ε/2) : add_le_add' (le_of_lt dxy) (le_of_lt dyz)
    ... = inf_edist x s + Hausdorff_edist s t + ε : by simp [ennreal.add_halves, add_comm]
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
lemma Hausdorff_edist_le_ediam (hs : s ≠ ∅) (ht : t ≠ ∅) : Hausdorff_edist s t ≤ diam (s ∪ t) :=
begin
  rcases ne_empty_iff_exists_mem.1 hs with ⟨x, xs⟩,
  rcases ne_empty_iff_exists_mem.1 ht with ⟨y, yt⟩,
  refine Hausdorff_edist_le_of_mem_edist _ _,
  { exact λz hz, ⟨y, yt, edist_le_diam_of_mem (subset_union_left _ _ hz) (subset_union_right _ _ yt)⟩ },
  { exact λz hz, ⟨x, xs, edist_le_diam_of_mem (subset_union_right _ _ hz) (subset_union_left _ _ xs)⟩ }
end

/-- The Hausdorff distance satisfies the triangular inequality -/
lemma Hausdorff_edist_triangle : Hausdorff_edist s u ≤ Hausdorff_edist s t + Hausdorff_edist t u :=
begin
  change Sup ((λx, inf_edist x u) '' s) ⊔ Sup ((λx, inf_edist x s) '' u) ≤ Hausdorff_edist s t + Hausdorff_edist t u,
  simp only [and_imp, set.mem_image, lattice.Sup_le_iff, exists_imp_distrib,
             lattice.sup_le_iff, -mem_image, set.ball_image_iff],
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
@[simp] lemma Hausdorff_edist_self_closure : Hausdorff_edist s (closure s) = 0 :=
begin
  erw ← le_bot_iff,
  simp only [Hausdorff_edist, inf_edist_closure, -le_zero_iff_eq, and_imp,
    set.mem_image, lattice.Sup_le_iff, exists_imp_distrib, lattice.sup_le_iff,
    set.ball_image_iff, ennreal.bot_eq_zero, -mem_image],
  simp only [inf_edist_zero_of_mem, mem_closure_iff_inf_edist_zero, le_refl, and_self,
             forall_true_iff] {contextual := tt}
end

/-- The Hausdorff edistance between sets or their closures is the same -/
@[simp] lemma Hausdorff_edist_closure : Hausdorff_edist (closure s) (closure t) = Hausdorff_edist s t :=
begin
  refine le_antisymm _ _,
  {calc  _ ≤ Hausdorff_edist (closure s) s + Hausdorff_edist s (closure t) : Hausdorff_edist_triangle
    ... = Hausdorff_edist s (closure t) : by simp [Hausdorff_edist_comm]
    ... ≤ Hausdorff_edist s t + Hausdorff_edist t (closure t) : Hausdorff_edist_triangle
    ... = Hausdorff_edist s t : by simp},
  {calc _ ≤ Hausdorff_edist s (closure s) + Hausdorff_edist (closure s) t : Hausdorff_edist_triangle
    ... = Hausdorff_edist (closure s) t : by simp
    ... ≤ Hausdorff_edist (closure s) (closure t) + Hausdorff_edist (closure t) t :
      Hausdorff_edist_triangle
    ... = Hausdorff_edist (closure s) (closure t) : by simp [Hausdorff_edist_comm] }
end

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
by rw [Hausdorff_edist_zero_iff_closure_eq_closure, closure_eq_iff_is_closed.2 hs,
       closure_eq_iff_is_closed.2 ht]

/-- The Haudorff edistance to the empty set is infinite -/
lemma Hausdorff_edist_empty (ne : s ≠ ∅) : Hausdorff_edist s ∅ = ∞ :=
begin
  rcases exists_mem_of_ne_empty ne with ⟨x, xs⟩,
  have : inf_edist x ∅ ≤ Hausdorff_edist s ∅ := inf_edist_le_Hausdorff_edist_of_mem xs,
  simpa using this,
end

/-- If a set is at finite Hausdorff edistance of a nonempty set, it is nonempty -/
lemma ne_empty_of_Hausdorff_edist_ne_top (hs : s ≠ ∅) (fin : Hausdorff_edist s t ≠ ⊤) : t ≠ ∅ :=
begin
  by_contradiction h,
  simp only [not_not, ne.def] at h,
  rw [h, Hausdorff_edist_empty hs] at fin,
  simpa using fin
end

/-- In emetric spaces, the Hausdorff edistance defines an emetric space structure
on the type of closed subsets -/
instance : emetric_space (closeds α) :=
{ edist               := λs t, Hausdorff_edist s.val t.val,
  edist_self          := λs, Hausdorff_edist_self,
  edist_comm          := λs t, Hausdorff_edist_comm,
  edist_triangle      := λs t u, Hausdorff_edist_triangle,
  eq_of_edist_eq_zero :=
    λs t h, subtype.eq ((Hausdorff_edist_zero_iff_eq_of_closed s.property t.property).1 h) }

/-- The edistance to a closed set depends continuously on the point and the set -/
lemma continuous_inf_edist_Hausdorff_edist :
  continuous (λp : α × (closeds α), inf_edist p.1 (p.2).val) :=
begin
  refine continuous_of_le_add_edist 2 (by simp) _,
  rintros ⟨x, s⟩ ⟨y, t⟩,
  calc inf_edist x (s.val) ≤ inf_edist x (t.val) + Hausdorff_edist (t.val) (s.val) :
    inf_edist_le_inf_edist_add_Hausdorff_edist
  ... ≤ (inf_edist y (t.val) + edist x y) + Hausdorff_edist (t.val) (s.val) :
    add_le_add_right' inf_edist_le_inf_edist_add_edist
  ... = inf_edist y (t.val) + (edist x y + Hausdorff_edist (s.val) (t.val)) :
    by simp [add_comm, Hausdorff_edist_comm]
  ... ≤ inf_edist y (t.val) + (edist (x, s) (y, t) + edist (x, s) (y, t)) :
    add_le_add_left' (add_le_add' (by simp [edist, le_refl]) (by simp [edist, le_refl]))
  ... = inf_edist y (t.val) + 2 * edist (x, s) (y, t) :
    by rw [← mul_two, mul_comm]
end

/-- Subsets of a given closed subset form a closed set -/
lemma is_closed_subsets_of_is_closed (hs : is_closed s) :
  is_closed {t : closeds α | t.val ⊆ s} :=
begin
  refine is_closed_of_closure_subset (λt ht x hx, _),
  -- t : closeds α,  ht : t ∈ closure {t : closeds α | t.val ⊆ s},
  -- x : α,  hx : x ∈ t.val
  -- goal : x ∈ s
  have : x ∈ closure s,
  { refine mem_closure_iff'.2 (λε εpos, _),
    rcases mem_closure_iff'.1 ht ε εpos with ⟨u, hu, Dtu⟩,
    -- u : closeds α,  hu : u ∈ {t : closeds α | t.val ⊆ s},  hu' : edist t u < ε
    rcases exists_edist_lt_of_Hausdorff_edist_lt hx Dtu with ⟨y, hy, Dxy⟩,
    -- y : α,  hy : y ∈ u.val, Dxy : edist x y < ε
    exact ⟨y, hu hy, Dxy⟩ },
  rwa closure_eq_of_is_closed hs at this,
end

/-- By definition, the edistance on `closeds α` is given by the Hausdorff edistance -/
lemma closeds.edist_eq {s t : closeds α} : edist s t = Hausdorff_edist s.val t.val := rfl

/-- In a complete space, the space of closed subsets is complete for the
Hausdorff edistance. -/
instance [complete_space α] : complete_space (closeds α) :=
begin
  /- We will show that, if a sequence of sets `s n` satisfies
     `edist (s n) (s (n+1)) < 2^{-n}`, then it converges. This is enough to guarantee
     completeness, by a standard completeness criterion.
     First, introduce the bounding coefficients `B n = 2^{-n}`, in `ennreal`,
     and prove their basic properties that we will use later -/
  have BR_pos : ∀n:ℕ, (0 : real) < (1/2)^n := by apply pow_pos; norm_num,
  let B : ℕ → ennreal := λn, ennreal.of_real ((1 / 2) ^ n),
  have Bpos : ∀n:ℕ, (0 : ennreal) < B n := by simpa using BR_pos,
  have B_lim: tendsto B at_top (nhds 0),
  { rw ← ennreal.of_real_zero,
    apply ennreal.tendsto_of_real,
    apply tendsto_pow_at_top_nhds_0_of_lt_1,
    norm_num, norm_num },
  have B2_lim : tendsto (λn, 2 * B n) at_top (nhds 0),
  { have : tendsto (λn, 2 * B n) at_top (nhds (2 * 0)) := ennreal.tendsto_mul_right B_lim (by simp),
    simpa using this },
  have Bkk : ∀k, B (k+1) + B (k+1) = B k,
  { assume k,
    simp only [B, (ennreal.of_real_add _ _).symm, BR_pos, le_of_lt],
    apply congr_arg,
    simp only [pow_add, one_div_eq_inv, pow_one],
    ring },
  have IB : ∀m, ∀k≥m, 2 * B k ≤ 2 * B m,
  { assume m k hkm,
    apply canonically_ordered_semiring.mul_le_mul (le_refl _) _,
    exact ennreal.of_real_le_of_real (pow_le_pow_of_le_one (by norm_num) (by norm_num) hkm) },

  /- Consider now a sequence of closed sets `s n` with `edist (s n) (s (n+1)) < B n`.
  We will show that it converges. The limit set is t0 = ⋂n, closure (⋃m≥n, s m).
  We will have to show that a point in `s n` is close to a point in `t0`, and a point
  in `t0` is close to a point in `s n`. The completeness then follows from a
  standard criterion. -/
  refine complete_of_convergent_controlled_sequences _ Bpos (λs hs, _),
  let t0 := ⋂n, closure (⋃m≥n, (s m).val),
  have : is_closed t0 := is_closed_Inter (λ_, is_closed_closure),
  let t : closeds α := ⟨t0, this⟩,
  existsi t,
  have I1 : ∀n:ℕ, ∀x ∈ (s n).val, ∃y ∈ t0, edist x y ≤ 2 * B n,
  { /- This is the main difficulty of the proof. Starting from `x ∈ s n`, we want
       to find a point in `t0` which is close to `x`. Define inductively a sequence of
       points `z m` with `z n = x` and `z m ∈ s m` and `edist (z m) (z (m+1)) ≤ B m`. This is
       possible since the Hausdorff distance between `s m` and `s (m+1)` is at most `B m`.
       This sequence is a Cauchy sequence, therefore converging as the space is complete, to
       a limit which satisfies the required properties. -/
    assume n x hx,
    haveI : nonempty α := ⟨x⟩,
    let z : ℕ → α := λk, nat.rec_on k x (λl z, if l < n then x else
                      epsilon (λy, y ∈ (s (l+1)).val ∧ edist z y < B l)),
    have z_le_n : ∀l≤n, z l = x,
    { assume l hl,
      cases l with m,
      { show z 0 = x, from rfl },
      { have : z (nat.succ m) = ite (m < n) x (epsilon (λ (y : α), y ∈ (s (m + 1)).val ∧ edist (z m) y < B m))
          := rfl,
        rw this,
        simp [nat.lt_of_succ_le hl] }},
    have : z n = x := z_le_n n (le_refl n),
    -- check by induction that the sequence `z m` satisfies the required properties
    have I : ∀m≥n, z m ∈ (s m).val → (z (m+1) ∈ (s (m+1)).val ∧ edist (z m) (z (m+1)) < B m),
    { assume m hm hz,
      have E : ∃y, y ∈ (s (m+1)).val ∧ edist (z m) y < B m,
      { have : Hausdorff_edist (s m).val (s (m+1)).val < B m := hs m m (m+1) (le_refl _) (by simp),
        rcases exists_edist_lt_of_Hausdorff_edist_lt hz this with ⟨y, hy, Dy⟩,
        exact ⟨y, ⟨hy, Dy⟩⟩ },
      have : z (m+1) = ite (m < n) x (epsilon (λ (y : α), y ∈ (s (m + 1)).val ∧ edist (z m) y < B m)) := rfl,
      rw this,
      simp only [not_lt_of_le hm, if_false],
      exact epsilon_spec E },
    have z_in_s : ∀m≥n, z m ∈ (s m).val :=
      nat.le_induction (by rwa ‹z n = x›) (λm hm zm, (I m hm zm).1),
    -- for all `m`, the distance between `z m` and `z (m+1)` is controlled by `B m`:
    -- for `m ≥ n`, this follows from the construction, while for `m < n` all points are `x`.
    have Im_succm : ∀m, edist (z m) (z (m+1)) < B m,
    { assume m,
      by_cases hm : n≤m,
      { exact (I m hm (z_in_s m hm)).2 },
      { rw not_le at hm,
        have Im : z m = x := z_le_n m (le_of_lt hm),
        have Im' : z (m+1) = x := z_le_n (m+1) (nat.succ_le_of_lt hm),
        simp [Im, Im', Bpos] }},
    /- From the distance control between `z m` and `z (m+1)`, we deduce a distance control
    between `z k` and `z l` by summing the geometric series. Except that we are in `ennreal`, so
    we really want to avoid subtraction and we write the computation with a more awkward
    induction -/
    have Iz : ∀k l N, N ≤ k → N ≤ l → edist (z k) (z l) ≤ 2 * B N,
    { have ineq_rec : ∀m, ∀k≥m, B k + edist (z m) (z (k+1)) ≤ 2 * B m,
      { assume m,
        refine nat.le_induction _ (λk km hk, _),
        { calc B m + edist (z m) (z (m+1)) ≤ B m + B m : add_le_add_left' (le_of_lt (Im_succm m))
          ... = 2 * B m : by simp [(mul_two _).symm, mul_comm] },
        { calc B (k + 1) + edist (z m) (z (k + 1 + 1))
          ≤ B (k+1) + (edist (z m) (z (k+1)) + edist (z (k+1)) (z (k+2))) :
            add_le_add_left' (edist_triangle _ _ _)
          ... ≤ B (k+1) + (edist (z m) (z (k+1)) + B (k+1)) :
            add_le_add_left' (add_le_add_left' (le_of_lt (Im_succm (k+1))))
          ... = (B(k+1) + B(k+1)) + edist (z m) (z (k+1)) : by simp [add_comm]
          ... = B k + edist (z m) (z (k+1)) : by rw Bkk
          ... ≤ 2 * B m : hk }},
      have Imk : ∀m, ∀k≥m, edist (z m) (z k) ≤ 2 * B m,
      { assume m k hk,
        by_cases h : m = k,
        { simp [h, le_of_lt (Bpos k)] },
        { have I : m < k := lt_of_le_of_ne hk h,
          have : 0 < k := lt_of_le_of_lt (nat.zero_le _) ‹m < k›,
          let l := nat.pred k,
          have : k = l+1 := (nat.succ_pred_eq_of_pos ‹0 < k›).symm,
          rw this,
          have : m ≤ l := begin rw this at I, apply nat.le_of_lt_succ I end,
          calc edist (z m) (z (l+1)) ≤ B l + edist (z m) (z (l+1)) : le_add_left (le_refl _)
            ... ≤ 2 * B m : ineq_rec m l ‹m ≤ l› }},
      assume k l N hk hl,
      by_cases h : k ≤ l,
      { calc edist (z k) (z l) ≤ 2 * B k : Imk k l h
          ... ≤ 2 * B N : IB N k hk },
      { simp at h,
        calc edist (z k) (z l) = edist (z l) (z k) : edist_comm _ _
          ... ≤ 2 * B l : Imk l k (le_of_lt h)
          ... ≤ 2 * B N : IB N l hl }},
    -- it follows from the previous bound that `z` is a Cauchy sequence
    have : cauchy_seq z :=
      cauchy_seq_iff_le_tendsto_0.2 ⟨λn:ℕ, 2 * B n, ⟨Iz, B2_lim⟩⟩,
    -- therefore, it converges
    rcases cauchy_seq_tendsto_of_complete this with ⟨y, y_lim⟩,
    -- the limit point `y` will be the desired point, in `t0` and close to our initial point `x`.
    -- First, we check it belongs to `t0`.
    have : y ∈ t0 := mem_Inter.2 (λk, mem_closure_of_tendsto (by simp) y_lim
    begin
      simp only [exists_prop, set.mem_Union, filter.mem_at_top_sets, set.mem_preimage_eq, set.preimage_Union],
      exact ⟨max n k, λm hm, ⟨m, ⟨le_trans (le_max_right _ _) hm, z_in_s m (le_trans (le_max_left _ _) hm)⟩⟩⟩,
    end),
    -- Then, we check that `y` is close to `x = z n`. This follows from the fact that `y`
    -- is the limit of `z k`, and the distance between `z n` and `z k` has already been estimated.
    have : edist x y ≤ 2 * B n,
    { refine le_of_tendsto (by simp) (tendsto_edist tendsto_const_nhds y_lim) _,
      simp [‹z n = x›.symm],
      exact ⟨n, λm hm, Iz n m n (le_refl n) hm⟩ },
    -- Conclusion of this argument: the point `y` satisfies the required properties.
    exact ⟨y, ‹y ∈ t0›, ‹edist x y ≤ 2 * B n›⟩ },
  have I2 : ∀n:ℕ, ∀x ∈ t0, ∃y ∈ (s n).val, edist x y ≤ 2 * B n,
  { /- For the (much easier) reverse inequality, we start from a point `x ∈ t0` and we want
        to find a point `y ∈ s n` which is close to `x`.
        `x` belongs to `t0`, the intersection of the closures. In particular, it is well
        approximated by a point `z` in `⋃m≥n, s m`, say in `s m`. Since `s m` and
        `s n` are close, this point is itself well approximated by a point `y` in `s n`,
        as required. -/
    assume n x xt0,
    have : x ∈ closure (⋃m≥n, (s m).val) := by apply mem_Inter.1 xt0 n,
    rcases mem_closure_iff'.1 this (B n) (Bpos n) with ⟨z, hz, Dxz⟩,
    -- z : α,  Dxz : edist x z < B n,
    simp only [exists_prop, set.mem_Union] at hz,
    rcases hz with ⟨m, ⟨m_ge_n, hm⟩⟩,
    -- m : ℕ, m_ge_n : m ≥ n, hm : z ∈ (s m).val
    have : Hausdorff_edist (s m).val (s n).val < B n := hs n m n m_ge_n (le_refl n),
    rcases exists_edist_lt_of_Hausdorff_edist_lt hm this with ⟨y, hy, Dzy⟩,
    -- y : α,  hy : y ∈ (s n).val,  Dzy : edist z y < B n
    exact ⟨y, hy, calc
      edist x y ≤ edist x z + edist z y : edist_triangle _ _ _
            ... ≤ B n + B n : add_le_add' (le_of_lt Dxz) (le_of_lt Dzy)
            ... = 2 * B n : (two_mul _).symm ⟩ },
  -- Deduce from the above inequalities that the distance between `s n` and `t0` is at most `2 B n`.
  have main : ∀n:ℕ, edist (s n) t ≤ 2 * B n := λn, Hausdorff_edist_le_of_mem_edist (I1 n) (I2 n),
  -- from this, the convergence of `s n` to `t0` follows.
  refine (tendsto_at_top _).2 (λε εpos, _),
  have Z := (tendsto_orderable.1 B2_lim).2 ε εpos,
  simp only [filter.mem_at_top_sets, set.mem_set_of_eq] at Z,
  rcases Z with ⟨N, hN⟩,  --  ∀ (b : ℕ), b ≥ N → ε > 2 * B b
  exact ⟨N, λn hn, lt_of_le_of_lt (main n) (hN n hn)⟩
end

/-- In a compact space, the set of closed subsets is compact. -/
instance [compact_space α] : compact_space (closeds α) :=
⟨begin
  /- by completeness, it suffices to show that it is totally bounded,
    i.e., for all ε>0, there is a finite set which is ε-dense.
    start from a set `s` which is ε-dense in α. Then the subsets of `s`
    are finitely many, and ε-dense for the Hausdorff distance. -/
  refine compact_of_totally_bounded_is_closed (emetric.totally_bounded_iff.2 (λε εpos, _)) is_closed_univ,
  rcases dense εpos with ⟨δ, δpos, δlt⟩,
  rcases emetric.totally_bounded_iff.1 (compact_iff_totally_bounded_complete.1 (@compact_univ α _ _ _)).1 δ δpos
    with ⟨s, fs, hs⟩,
  -- s : set α,  fs : finite s,  hs : univ ⊆ ⋃ (y : α) (H : y ∈ s), eball y δ
  -- we first show that any set is well approximated by a subset of `s`.
  have main : ∀ u : set α, ∃v ⊆ s, Hausdorff_edist u v ≤ δ,
  { assume u,
    let v := {x : α | x ∈ s ∧ ∃y∈u, edist x y < δ},
    existsi [v, ((λx hx, hx.1) : v ⊆ s)],
    refine Hausdorff_edist_le_of_mem_edist _ _,
    { assume x hx,
      have : x ∈ ⋃y ∈ s, ball y δ := hs (by simp),
      rcases mem_bUnion_iff.1 this with ⟨y, ⟨ys, dy⟩⟩,
      have : edist y x < δ := by simp at dy; rwa [edist_comm] at dy,
      exact ⟨y, ⟨ys, ⟨x, hx, this⟩⟩, le_of_lt dy⟩ },
    { rintros x ⟨hx1, ⟨y, yu, hy⟩⟩,
      exact ⟨y, yu, le_of_lt hy⟩ }},
  -- introduce the set F of all subsets of `s` (seen as members of `closeds α`).
  -- it is finite
  let F := {f : closeds α | f.val ⊆ s},
  existsi F,
  split,
  { apply @finite_of_finite_image _ _ F (λf, f.val),
    { simp [subtype.val_injective] },
    { refine finite_subset (finite_subsets_of_finite fs) (λb, _),
      simp only [and_imp, set.mem_image, set.mem_set_of_eq, exists_imp_distrib],
      assume x hx hx',
      rwa hx' at hx }},
  -- `F` is ε-dense
  { assume u _,
    rcases main u.val with ⟨t0, t0s, Dut0⟩,
    have : finite t0 := finite_subset fs t0s,
    have : is_closed t0 := closed_of_compact _ (compact_of_finite this),
    let t : closeds α := ⟨t0, this⟩,
    have : t ∈ F := t0s,
    have : edist u t < ε := lt_of_le_of_lt Dut0 δlt,
    apply mem_bUnion_iff.2,
    exact ⟨t, ‹t ∈ F›, this⟩ }
end⟩

/-- In an emetric space, the space of non-empty compact subsets is an emetric space,
where the edistance is the Hausdorff edistance -/
instance nonempty_compacts.emetric_space : emetric_space (nonempty_compacts α) :=
{ edist               := λs t, Hausdorff_edist s.val t.val,
  edist_self          := λs, Hausdorff_edist_self,
  edist_comm          := λs t, Hausdorff_edist_comm,
  edist_triangle      := λs t u, Hausdorff_edist_triangle,
  eq_of_edist_eq_zero := λs t h, subtype.eq $ begin
    have : closure (s.val) = closure (t.val) := Hausdorff_edist_zero_iff_closure_eq_closure.1 h,
    rwa [closure_eq_iff_is_closed.2 (closed_of_compact _ s.property.2),
              closure_eq_iff_is_closed.2 (closed_of_compact _ t.property.2)] at this,
  end }

/-- `nonempty_compacts.to_closeds` is a uniform embedding (as it is an isometry) -/
lemma nonempty_compacts.to_closeds.uniform_embedding :
  uniform_embedding (@nonempty_compacts.to_closeds α _ _) :=
isometry.uniform_embedding $ λx y, rfl

/-- The range of `nonempty_compacts.to_closeds` is closed in a complete space -/
lemma nonempty_compacts.is_closed_in_closeds [complete_space α] :
  is_closed (nonempty_compacts.to_closeds '' (univ : set (nonempty_compacts α))) :=
begin
  have : nonempty_compacts.to_closeds '' univ = {s : closeds α | s.val ≠ ∅ ∧ compact s.val},
  { ext,
    simp only [set.image_univ, set.mem_range, ne.def, set.mem_set_of_eq],
    split,
    { rintros ⟨y, hy⟩,
      have : x.val = y.val := by rcases hy; simp,
      rw this,
      exact y.property },
    { rintros ⟨hx1, hx2⟩,
      existsi (⟨x.val, ⟨hx1, hx2⟩⟩ : nonempty_compacts α),
      apply subtype.eq,
      refl }},
  rw this,
  refine is_closed_of_closure_subset (λs hs, _),
  split,
  { -- take a set set t which is nonempty and at distance at most 1 of s
    rcases mem_closure_iff'.1 hs 1 ennreal.zero_lt_one with ⟨t, ht, Dst⟩,
    rw edist_comm at Dst,
    -- this set t contains a point x
    rcases ne_empty_iff_exists_mem.1 ht.1 with ⟨x, hx⟩,
    -- by the Hausdorff distance control, this point x is at distance at most 1
    -- of a point y in s
    rcases exists_edist_lt_of_Hausdorff_edist_lt hx Dst with ⟨y, hy, _⟩,
    -- this shows that s is not empty
    exact ne_empty_of_mem hy },
  { refine compact_iff_totally_bounded_complete.2 ⟨_, is_complete_of_is_closed s.property⟩,
    refine totally_bounded_iff.2 (λε εpos, _),
    -- we have to show that s is covered by finitely many eballs of radius ε
    -- pick a nonempty compact set t at distance at most ε/2 of s
    rcases mem_closure_iff'.1 hs (ε/2) (ennreal.half_pos εpos) with ⟨t, ht, Dst⟩,
    -- cover this space with finitely many balls of radius ε/2
    rcases totally_bounded_iff.1 (compact_iff_totally_bounded_complete.1 ht.2).1 (ε/2) (ennreal.half_pos εpos)
      with ⟨u, fu, ut⟩,
    refine ⟨u, ⟨fu, λx hx, _⟩⟩,
    -- u : set α,  fu : finite u,  ut : t.val ⊆ ⋃ (y : α) (H : y ∈ u), eball y (ε / 2)
    -- then s is covered by the union of the balls centered at u of radius ε
    rcases exists_edist_lt_of_Hausdorff_edist_lt hx Dst with ⟨z, hz, Dxz⟩,
    rcases mem_bUnion_iff.1 (ut hz) with ⟨y, hy, Dzy⟩,
    have : edist x y < ε := calc
      edist x y ≤ edist x z + edist z y : edist_triangle _ _ _
      ... < ε/2 + ε/2 : ennreal.add_lt_add Dxz Dzy
      ... = ε : ennreal.add_halves _,
    exact mem_bUnion hy this },
end

/-- In a complete space, the space of nonempty compact subsets is complete. This follows
from the same statement for closed subsets -/
instance nonempty_compacts.complete_space [complete_space α] : complete_space (nonempty_compacts α) :=
begin
  apply complete_space_of_is_complete_univ,
  apply (is_complete_image_iff nonempty_compacts.to_closeds.uniform_embedding).1,
  apply is_complete_of_is_closed,
  exact nonempty_compacts.is_closed_in_closeds
end

/-- In a compact space, the space of nonempty compact subsets is compact. This follows from
the same statement for closed subsets -/
instance nonempty_compacts.compact_space [compact_space α] : compact_space (nonempty_compacts α) :=
⟨begin
  rw compact_iff_compact_image_of_embedding nonempty_compacts.to_closeds.uniform_embedding.embedding,
  exact compact_of_closed nonempty_compacts.is_closed_in_closeds
end⟩

/-- In a second countable space, the space of nonempty compact subsets is second countable -/
instance [second_countable_topology α] : second_countable_topology (nonempty_compacts α) :=
begin
  haveI : separable_space (nonempty_compacts α) :=
  begin
    /- To obtain a countable dense subset of `nonempty_compacts α`, start from
    a countable dense subset `s` of α, and then consider all its finite nonempty subsets.
    This set is countable and made of nonempty compact sets. It turns out to be dense:
    by total boundedness, any compact set `t` can be covered by finitely many small balls, and
    approximations in `s` of the centers of these balls give the required finite approximation
    of `t`. -/
    have : separable_space α := by apply_instance,
    rcases this.exists_countable_closure_eq_univ with ⟨s, cs, s_dense⟩,
    let v0 := {t : set α | finite t ∧ t ⊆ s},
    let v : set (nonempty_compacts α) := {t : nonempty_compacts α | t.val ∈ v0},
    refine  ⟨⟨v, ⟨_, _⟩⟩⟩,
    { have : countable (subtype.val '' v),
      { refine countable_subset (λx hx, _) (countable_set_of_finite_subset cs),
        rcases (mem_image _ _ _).1 hx with ⟨y, ⟨hy, yx⟩⟩,
        rw ← yx,
        exact hy },
      apply countable_of_injective_of_countable_image _ this,
      apply inj_on_of_inj_on_of_subset (injective_iff_inj_on_univ.1 subtype.val_injective)
        (subset_univ _) },
    { refine subset.antisymm (subset_univ _) (λt ht, mem_closure_iff'.2 (λε εpos, _)),
      -- t is a compact nonempty set, that we have to approximate uniformly by a a set in `v`.
      rcases dense εpos with ⟨δ, δpos, δlt⟩,
      -- construct a map F associating to a point in α an approximating point in s, up to δ/2.
      have Exy : ∀x, ∃y, y ∈ s ∧ edist x y < δ/2,
      { assume x,
        have : x ∈ closure s := by rw s_dense; exact mem_univ _,
        rcases mem_closure_iff'.1 this (δ/2) (ennreal.half_pos δpos) with ⟨y, ys, hy⟩,
        exact ⟨y, ⟨ys, hy⟩⟩ },
      let F := λx, some (Exy x),
      have Fspec : ∀x, F x ∈ s ∧ edist x (F x) < δ/2 := λx, some_spec (Exy x),

      -- cover `t` with finitely many balls. Their centers form a set `a`
      have : totally_bounded t.val := (compact_iff_totally_bounded_complete.1 t.property.2).1,
      rcases totally_bounded_iff.1 this (δ/2) (ennreal.half_pos δpos) with ⟨a, af, ta⟩,
      -- a : set α,  af : finite a,  ta : t.val ⊆ ⋃ (y : α) (H : y ∈ a), eball y (δ / 2)
      -- replace each center by a nearby approximation in `s`, giving a new set `b`
      let b := F '' a,
      have : finite b := finite_image _ af,
      have tb : ∀x ∈ t.val, ∃y ∈ b, edist x y < δ,
      { assume x hx,
        rcases mem_bUnion_iff.1 (ta hx) with ⟨z, za, Dxz⟩,
        existsi [F z, mem_image_of_mem _ za],
        calc edist x (F z) ≤ edist x z + edist z (F z) : edist_triangle _ _ _
             ... < δ/2 + δ/2 : ennreal.add_lt_add Dxz (Fspec z).2
             ... = δ : ennreal.add_halves _ },
      -- keep only the points in `b` that are close to point in `t`, yielding a new set `c`
      let c := {y ∈ b | ∃x∈t.val, edist x y < δ},
      have : finite c := finite_subset ‹finite b› (λx hx, hx.1),
      -- points in `t` are well approximated by points in `c`
      have tc : ∀x ∈ t.val, ∃y ∈ c, edist x y ≤ δ,
      { assume x hx,
        rcases tb x hx with ⟨y, yv, Dxy⟩,
        have : y ∈ c := by simp [c, -mem_image]; exact ⟨yv, ⟨x, hx, Dxy⟩⟩,
        exact ⟨y, this, le_of_lt Dxy⟩ },
      -- points in `c` are well approximated by points in `t`
      have ct : ∀y ∈ c, ∃x ∈ t.val, edist y x ≤ δ,
      { rintros y ⟨hy1, ⟨x, xt, Dyx⟩⟩,
        have : edist y x ≤ δ := calc
          edist y x = edist x y : edist_comm _ _
          ... ≤ δ : le_of_lt Dyx,
        exact ⟨x, xt, this⟩ },
      -- it follows that their Hausdorff distance is small
      have : Hausdorff_edist t.val c ≤ δ :=
        Hausdorff_edist_le_of_mem_edist tc ct,
      have Dtc : Hausdorff_edist t.val c < ε := lt_of_le_of_lt this δlt,
      -- the set `c` is not empty, as it is well approximated by a nonempty set
      have : c ≠ ∅,
      { by_contradiction h,
        simp only [not_not, ne.def] at h,
        rw [h, Hausdorff_edist_empty t.property.1] at Dtc,
        exact not_top_lt Dtc },
      -- let `d` be the version of `c` in the type `nonempty_compacts α`
      let d : nonempty_compacts α := ⟨c, ⟨‹c ≠ ∅›, compact_of_finite ‹finite c›⟩⟩,
      have : c ⊆ s,
      { assume x hx,
        rcases (mem_image _ _ _).1 hx.1 with ⟨y, ⟨ya, yx⟩⟩,
        rw ← yx,
        exact (Fspec y).1 },
      have : d ∈ v := ⟨‹finite c›, this⟩,
      -- we have proved that `d` is a good approximation of `t` as requested
      exact ⟨d, ‹d ∈ v›, Dtc⟩ },
  end,
  apply second_countable_of_separable,
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
lemma inf_edist_ne_top (h : s ≠ ∅) : inf_edist x s ≠ ⊤ :=
begin
  rcases exists_mem_of_ne_empty h with ⟨y, hy⟩,
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
  rw [dist_edist, inf_dist, ennreal.to_real_le_to_real (inf_edist_ne_top (ne_empty_of_mem h)) (edist_ne_top _ _)],
  exact inf_edist_le_edist_of_mem h
end

/-- The minimal distance is monotonous with respect to inclusion -/
lemma inf_dist_le_inf_dist_of_subset (h : s ⊆ t) (hs : s ≠ ∅) :
  inf_dist x t ≤ inf_dist x s :=
begin
  rcases ne_empty_iff_exists_mem.1 hs with ⟨y, hy⟩,
  have ht : t ≠ ∅ := ne_empty_of_mem (h hy),
  rw [inf_dist, inf_dist, ennreal.to_real_le_to_real (inf_edist_ne_top ht) (inf_edist_ne_top hs)],
  exact inf_edist_le_inf_edist_of_subset h
end

/-- If the minimal distance to a set is `<r`, there exists a point in this set at distance `<r` -/
lemma exists_dist_lt_of_inf_dist_lt {r : real} (h : inf_dist x s < r) (hs : s ≠ ∅) :
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
  by_cases hs : s = ∅,
  { by simp [hs, dist_nonneg] },
  { rw [inf_dist, inf_dist, dist_edist, ← ennreal.to_real_add (inf_edist_ne_top hs) (edist_ne_top _ _),
        ennreal.to_real_le_to_real (inf_edist_ne_top hs)],
    { apply inf_edist_le_inf_edist_add_edist },
    { simp [ennreal.add_eq_top, inf_edist_ne_top hs, edist_ne_top] }}
end

/-- The minimal distance to a set is uniformly continuous -/
lemma uniform_continuous_inf_dist : uniform_continuous (λx, inf_dist x s) :=
uniform_continuous_of_le_add 1 (by simp [inf_dist_le_inf_dist_add_dist])

/-- The minimal distance to a set is continuous -/
lemma continuous_inf_dist : continuous (λx, inf_dist x s) :=
uniform_continuous_inf_dist.continuous

/-- The minimal distance to a set and its closure coincide -/
lemma inf_dist_eq_closure : inf_dist x (closure s) = inf_dist x s :=
by simp [inf_dist, inf_edist_closure]

/-- A point belongs to the closure of `s` iff its infimum distance to this set vanishes -/
lemma mem_closure_iff_inf_dist_zero (h : s ≠ ∅) : x ∈ closure s ↔ inf_dist x s = 0 :=
by simp [mem_closure_iff_inf_edist_zero, inf_dist, ennreal.to_real_eq_zero_iff, inf_edist_ne_top h]

/-- Given a closed set `s`, a point belongs to `s` iff its infimum distance to this set vanishes -/
lemma mem_iff_ind_dist_zero_of_closed (h : is_closed s) (hs : s ≠ ∅) :
  x ∈ s ↔ inf_dist x s = 0 :=
begin
  have := @mem_closure_iff_inf_dist_zero _ _ s x hs,
  rwa closure_eq_iff_is_closed.2 h at this
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
lemma Hausdorff_edist_ne_top_of_ne_empty_of_bounded (hs : s ≠ ∅) (ht : t ≠ ∅)
  (bs : bounded s) (bt : bounded t) : Hausdorff_edist s t ≠ ⊤ :=
begin
  rcases ne_empty_iff_exists_mem.1 hs with ⟨cs, hcs⟩,
  rcases ne_empty_iff_exists_mem.1 ht with ⟨ct, hct⟩,
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
  by_cases h : s = ∅,
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
  by_cases h : (Hausdorff_edist s t = ⊤) ∨ (s = ∅) ∨ (t = ∅),
  { rcases h with h1 | h2 | h3,
    { simpa [Hausdorff_dist, h1] },
    { simpa [h2] },
    { simpa [h3] }},
  { simp only [not_or_distrib] at h,
    have : Hausdorff_edist s t ≤ ennreal.of_real r,
    { apply Hausdorff_edist_le_of_inf_edist _ _,
      { assume x hx,
        have I := H1 x hx,
        rwa [inf_dist, ← ennreal.to_real_of_real hr,
             ennreal.to_real_le_to_real (inf_edist_ne_top h.2.2) ennreal.of_real_ne_top] at I },
      { assume x hx,
        have I := H2 x hx,
        rwa [inf_dist, ← ennreal.to_real_of_real hr,
             ennreal.to_real_le_to_real (inf_edist_ne_top h.2.1) ennreal.of_real_ne_top] at I }},
    rwa [Hausdorff_dist, ← ennreal.to_real_of_real hr,
         ennreal.to_real_le_to_real h.1 ennreal.of_real_ne_top] }
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
lemma Hausdorff_dist_le_diam (hs : s ≠ ∅) (bs : bounded s) (ht : t ≠ ∅) (bt : bounded t) :
  Hausdorff_dist s t ≤ diam (s ∪ t) :=
begin
  rcases ne_empty_iff_exists_mem.1 hs with ⟨x, xs⟩,
  rcases ne_empty_iff_exists_mem.1 ht with ⟨y, yt⟩,
  refine Hausdorff_dist_le_of_mem_dist diam_nonneg _ _,
  { exact  λz hz, ⟨y, yt, dist_le_diam_of_mem (bounded_union.2 ⟨bs, bt⟩) (subset_union_left _ _ hz) (subset_union_right _ _ yt)⟩ },
  { exact λz hz, ⟨x, xs, dist_le_diam_of_mem (bounded_union.2 ⟨bs, bt⟩) (subset_union_right _ _ hz) (subset_union_left _ _ xs)⟩ }
end

/-- The distance to a set is controlled by the Hausdorff distance -/
lemma inf_dist_le_Hausdorff_dist_of_mem (hx : x ∈ s) (fin : Hausdorff_edist s t ≠ ⊤) :
  inf_dist x t ≤ Hausdorff_dist s t :=
begin
  have ht : t ≠ ∅ := ne_empty_of_Hausdorff_edist_ne_top (ne_empty_of_mem hx) fin,
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
  by_cases (s = ∅) ∨ (t = ∅),
  { rcases h with h1 |h2,
    { have : t = ∅,
      { by_contradiction ht,
        rw Hausdorff_edist_comm at fin,
        exact ne_empty_of_Hausdorff_edist_ne_top ht fin h1 },
      simp [‹s = ∅›, ‹t = ∅›] },
    { have : s = ∅,
      { by_contradiction hs,
        exact ne_empty_of_Hausdorff_edist_ne_top hs fin h2 },
      simp [‹s = ∅›, ‹t = ∅›] }},
  { rw not_or_distrib at h,
    rw [inf_dist, inf_dist, Hausdorff_dist, ← ennreal.to_real_add (inf_edist_ne_top h.1) fin,
        ennreal.to_real_le_to_real (inf_edist_ne_top h.2)],
    { exact inf_edist_le_inf_edist_add_Hausdorff_edist },
    { simp [ennreal.add_eq_top, not_or_distrib, fin, inf_edist_ne_top h.1] }}
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
@[simp] lemma Hausdorff_dist_self_closure : Hausdorff_dist s (closure s) = 0 :=
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

/-- `nonempty_compacts α` inherits a metric space structure, as the Hausdorff
edistance between two such sets is finite. -/
instance : metric_space (nonempty_compacts α) :=
emetric_space.to_metric_space $ λx y, Hausdorff_edist_ne_top_of_ne_empty_of_bounded x.2.1 y.2.1
  (bounded_of_compact x.2.2) (bounded_of_compact y.2.2)

/-- The distance on `nonempty_compacts α` is the Hausdorff distance, by construction -/
lemma nonempty_compacts.dist_eq {x y : nonempty_compacts α} :
  dist x y = Hausdorff_dist x.val y.val := rfl

lemma uniform_continuous_inf_dist_Hausdorff_dist :
  uniform_continuous (λp : α × (nonempty_compacts α), inf_dist p.1 (p.2).val) :=
begin
  refine uniform_continuous_of_le_add 2 _,
  rintros ⟨x, s⟩ ⟨y, t⟩,
  calc inf_dist x (s.val) ≤ inf_dist x (t.val) + Hausdorff_dist (t.val) (s.val) :
    inf_dist_le_inf_dist_add_Hausdorff_dist (edist_ne_top t s)
  ... ≤ (inf_dist y (t.val) + dist x y) + Hausdorff_dist (t.val) (s.val) :
    add_le_add_right inf_dist_le_inf_dist_add_dist _
  ... = inf_dist y (t.val) + (dist x y + Hausdorff_dist (s.val) (t.val)) :
    by simp [add_comm, Hausdorff_dist_comm]
  ... ≤ inf_dist y (t.val) + (dist (x, s) (y, t) + dist (x, s) (y, t)) :
    add_le_add_left (add_le_add (by simp [dist, le_refl]) (by simp [dist, nonempty_compacts.dist_eq, le_refl])) _
  ... = inf_dist y (t.val) + 2 * dist (x, s) (y, t) :
    by rw [← mul_two, mul_comm]
end

end --section
end metric --namespace

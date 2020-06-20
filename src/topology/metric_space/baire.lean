/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.specific_limits

/-!
# Baire theorem

In a complete metric space, a countable intersection of dense open subsets is dense.

The good concept underlying the theorem is that of a Gδ set, i.e., a countable intersection
of open sets. Then Baire theorem can also be formulated as the fact that a countable
intersection of dense Gδ sets is a dense Gδ set. We prove Baire theorem, giving several different
formulations that can be handy. We also prove the important consequence that, if the space is
covered by a countable union of closed sets, then the union of their interiors is dense.

The names of the theorems do not contain the string "Baire", but are instead built from the form of
the statement. "Baire" is however in the docstring of all the theorems, to facilitate grep searches.
-/

noncomputable theory
open_locale classical

open filter encodable set

variables {α : Type*} {β : Type*} {γ : Type*}

section is_Gδ
variable [topological_space α]

/-- A Gδ set is a countable intersection of open sets. -/
def is_Gδ (s : set α) : Prop :=
  ∃T : set (set α), (∀t ∈ T, is_open t) ∧ countable T ∧ s = (⋂₀ T)

/-- An open set is a Gδ set. -/
lemma is_open.is_Gδ {s : set α} (h : is_open s) : is_Gδ s :=
⟨{s}, by simp [h], countable_singleton _, (set.sInter_singleton _).symm⟩

lemma is_Gδ_bInter_of_open {ι : Type*} {I : set ι} (hI : countable I) {f : ι → set α}
  (hf : ∀i ∈ I, is_open (f i)) : is_Gδ (⋂i∈I, f i) :=
⟨f '' I, by rwa ball_image_iff, hI.image _, by rw sInter_image⟩

lemma is_Gδ_Inter_of_open {ι : Type*} [encodable ι] {f : ι → set α}
  (hf : ∀i, is_open (f i)) : is_Gδ (⋂i, f i) :=
⟨range f, by rwa forall_range_iff, countable_range _, by rw sInter_range⟩

/-- A countable intersection of Gδ sets is a Gδ set. -/
lemma is_Gδ_sInter {S : set (set α)} (h : ∀s∈S, is_Gδ s) (hS : countable S) : is_Gδ (⋂₀ S) :=
begin
  have : ∀s : set α, ∃T : set (set α), s ∈ S → ((∀t ∈ T, is_open t) ∧ countable T ∧ s = (⋂₀ T)),
  { assume s,
    by_cases hs : s ∈ S,
    { simp [hs], exact h s hs },
    { simp [hs] }},
  choose T hT using this,
  refine ⟨⋃s∈S, T s, λt ht, _, _, _⟩,
  { simp only [exists_prop, set.mem_Union] at ht,
    rcases ht with ⟨s, hs, tTs⟩,
    exact (hT s hs).1 t tTs },
  { exact hS.bUnion (λs hs, (hT s hs).2.1) },
  { exact (sInter_bUnion (λs hs, (hT s hs).2.2)).symm }
end

/-- The union of two Gδ sets is a Gδ set. -/
lemma is_Gδ.union {s t : set α} (hs : is_Gδ s) (ht : is_Gδ t) : is_Gδ (s ∪ t) :=
begin
  rcases hs with ⟨S, Sopen, Scount, sS⟩,
  rcases ht with ⟨T, Topen, Tcount, tT⟩,
  rw [sS, tT, sInter_union_sInter],
  apply is_Gδ_bInter_of_open (countable_prod Scount Tcount),
  rintros ⟨a, b⟩ hab,
  simp only [set.prod_mk_mem_set_prod_eq] at hab,
  have aopen : is_open a := Sopen a hab.1,
  have bopen : is_open b := Topen b hab.2,
  simp [aopen, bopen, is_open_union]
end

end is_Gδ

section Baire_theorem
open metric
variables [metric_space α] [complete_space α]

/-- Baire theorem: a countable intersection of dense open sets is dense. Formulated here when
the source space is ℕ (and subsumed below by `dense_Inter_of_open` working with any
encodable source space). -/
theorem dense_Inter_of_open_nat {f : ℕ → set α} (ho : ∀n, is_open (f n))
  (hd : ∀n, closure (f n) = univ) : closure (⋂n, f n) = univ :=
begin
  let B : ℕ → ℝ := λn, ((1/2)^n : ℝ),
  have Bpos : ∀n, 0 < B n := λn, begin apply pow_pos, by norm_num end,
  /- Translate the density assumption into two functions `center` and `radius` associating
  to any n, x, δ, δpos a center and a positive radius such that
  `closed_ball center radius` is included both in `f n` and in `closed_ball x δ`.
  We can also require `radius ≤ (1/2)^(n+1), to ensure we get a Cauchy sequence later. -/
  have : ∀n x δ, ∃y r, δ > 0 → (r > 0 ∧ r ≤ B (n+1) ∧ closed_ball y r ⊆ (closed_ball x δ) ∩ f n),
  { assume n x δ,
    by_cases δpos : δ > 0,
    { have : x ∈ closure (f n) := by simpa only [(hd n).symm] using mem_univ x,
      rcases metric.mem_closure_iff.1 this (δ/2) (half_pos δpos) with ⟨y, ys, xy⟩,
      rw dist_comm at xy,
      rcases is_open_iff.1 (ho n) y ys with ⟨r, rpos, hr⟩,
      refine ⟨y, min (min (δ/2) (r/2)) (B (n+1)), λ_, ⟨_, _, λz hz, ⟨_, _⟩⟩⟩,
      show 0 < min (min (δ / 2) (r/2)) (B (n+1)),
        from lt_min (lt_min (half_pos δpos) (half_pos rpos)) (Bpos (n+1)),
      show min (min (δ / 2) (r/2)) (B (n+1)) ≤ B (n+1), from min_le_right _ _,
      show z ∈ closed_ball x δ, from calc
        dist z x ≤ dist z y + dist y x : dist_triangle _ _ _
        ... ≤ (min (min (δ / 2) (r/2)) (B (n+1))) + (δ/2) : add_le_add hz (le_of_lt xy)
        ... ≤ δ/2 + δ/2 : add_le_add (le_trans (min_le_left _ _) (min_le_left _ _)) (le_refl _)
        ... = δ : add_halves _,
      show z ∈ f n, from hr (calc
        dist z y ≤ min (min (δ / 2) (r/2)) (B (n+1)) : hz
        ... ≤ r/2 : le_trans (min_le_left _ _) (min_le_right _ _)
        ... < r : half_lt_self rpos) },
    { use [x, 0] }},
  choose center radius H using this,

  refine subset.antisymm (subset_univ _) (λx hx, _),
  refine metric.mem_closure_iff.2 (λε εpos, _),
  /- ε is positive. We have to find a point in the ball of radius ε around x belonging to all `f n`.
  For this, we construct inductively a sequence `F n = (c n, r n)` such that the closed ball
  `closed_ball (c n) (r n)` is included in the previous ball and in `f n`, and such that
  `r n` is small enough to ensure that `c n` is a Cauchy sequence. Then `c n` converges to a
  limit which belongs to all the `f n`. -/
  let F : ℕ → (α × ℝ) := λn, nat.rec_on n (prod.mk x (min (ε/2) 1))
                              (λn p, prod.mk (center n p.1 p.2) (radius n p.1 p.2)),
  let c : ℕ → α := λn, (F n).1,
  let r : ℕ → ℝ := λn, (F n).2,
  have rpos : ∀n, r n > 0,
  { assume n,
    induction n with n hn,
    exact lt_min (half_pos εpos) (zero_lt_one),
    exact (H n (c n) (r n) hn).1 },
  have rB : ∀n, r n ≤ B n,
  { assume n,
    induction n with n hn,
    exact min_le_right _ _,
    exact (H n (c n) (r n) (rpos n)).2.1 },
  have incl : ∀n, closed_ball (c (n+1)) (r (n+1)) ⊆ (closed_ball (c n) (r n)) ∩ (f n) :=
    λn, (H n (c n) (r n) (rpos n)).2.2,
  have cdist : ∀n, dist (c n) (c (n+1)) ≤ B n,
  { assume n,
    rw dist_comm,
    have A : c (n+1) ∈ closed_ball (c (n+1)) (r (n+1)) :=
      mem_closed_ball_self (le_of_lt (rpos (n+1))),
    have I := calc
      closed_ball (c (n+1)) (r (n+1)) ⊆ closed_ball (c n) (r n) :
        subset.trans (incl n) (inter_subset_left _ _)
      ... ⊆ closed_ball (c n) (B n) : closed_ball_subset_closed_ball (rB n),
    exact I A },
  have : cauchy_seq c,
  { refine cauchy_seq_of_le_geometric (1/2) 1 (by norm_num) (λn, _),
    rw one_mul,
    exact cdist n },
  -- as the sequence `c n` is Cauchy in a complete space, it converges to a limit `y`.
  rcases cauchy_seq_tendsto_of_complete this with ⟨y, ylim⟩,
  -- this point `y` will be the desired point. We will check that it belongs to all
  -- `f n` and to `ball x ε`.
  use y,
  simp only [exists_prop, set.mem_Inter],
  have I : ∀n, ∀m ≥ n, closed_ball (c m) (r m) ⊆ closed_ball (c n) (r n),
  { assume n,
    refine nat.le_induction _ (λm hnm h, _),
    { exact subset.refl _ },
    { exact subset.trans (incl m) (subset.trans (inter_subset_left _ _) h) }},
  have yball : ∀n, y ∈ closed_ball (c n) (r n),
  { assume n,
    refine mem_of_closed_of_tendsto (by simp) ylim is_closed_ball _,
    simp only [filter.mem_at_top_sets, nonempty_of_inhabited, set.mem_preimage],
    exact ⟨n, λm hm, I n m hm (mem_closed_ball_self (le_of_lt (rpos m)))⟩ },
  split,
  show ∀n, y ∈ f n,
  { assume n,
    have : closed_ball (c (n+1)) (r (n+1)) ⊆ f n := subset.trans (incl n) (inter_subset_right _ _),
    exact this (yball (n+1)) },
  show dist x y < ε, from calc
    dist x y = dist y x : dist_comm _ _
    ... ≤ r 0 : yball 0
    ... < ε : lt_of_le_of_lt (min_le_left _ _) (half_lt_self εpos)
end

/-- Baire theorem: a countable intersection of dense open sets is dense. Formulated here with ⋂₀. -/
theorem dense_sInter_of_open {S : set (set α)} (ho : ∀s∈S, is_open s) (hS : countable S)
  (hd : ∀s∈S, closure s = univ) : closure (⋂₀S) = univ :=
begin
  cases S.eq_empty_or_nonempty with h h,
  { simp [h] },
  { rcases hS.exists_surjective h with ⟨f, hf⟩,
    have F : ∀n, f n ∈ S := λn, by rw hf; exact mem_range_self _,
    rw [hf, sInter_range],
    exact dense_Inter_of_open_nat (λn, ho _ (F n)) (λn, hd _ (F n)) }
end

/-- Baire theorem: a countable intersection of dense open sets is dense. Formulated here with
an index set which is a countable set in any type. -/
theorem dense_bInter_of_open {S : set β} {f : β → set α} (ho : ∀s∈S, is_open (f s))
  (hS : countable S) (hd : ∀s∈S, closure (f s) = univ) : closure (⋂s∈S, f s) = univ :=
begin
  rw ← sInter_image,
  apply dense_sInter_of_open,
  { rwa ball_image_iff },
  { exact hS.image _ },
  { rwa ball_image_iff }
end

/-- Baire theorem: a countable intersection of dense open sets is dense. Formulated here with
an index set which is an encodable type. -/
theorem dense_Inter_of_open [encodable β] {f : β → set α} (ho : ∀s, is_open (f s))
  (hd : ∀s, closure (f s) = univ) : closure (⋂s, f s) = univ :=
begin
  rw ← sInter_range,
  apply dense_sInter_of_open,
  { rwa forall_range_iff },
  { exact countable_range _ },
  { rwa forall_range_iff }
end

/-- Baire theorem: a countable intersection of dense Gδ sets is dense. Formulated here with ⋂₀. -/
theorem dense_sInter_of_Gδ {S : set (set α)} (ho : ∀s∈S, is_Gδ s) (hS : countable S)
  (hd : ∀s∈S, closure s = univ) : closure (⋂₀S) = univ :=
begin
  -- the result follows from the result for a countable intersection of dense open sets,
  -- by rewriting each set as a countable intersection of open sets, which are of course dense.
  have : ∀s : set α, ∃T : set (set α), s ∈ S → ((∀t ∈ T, is_open t) ∧ countable T ∧ s = (⋂₀ T)),
  { assume s,
    by_cases hs : s ∈ S,
    { simp [hs], exact ho s hs },
    { simp [hs] }},
  choose T hT using this,
  have : ⋂₀ S = ⋂₀ (⋃s∈S, T s) := (sInter_bUnion (λs hs, (hT s hs).2.2)).symm,
  rw this,
  refine dense_sInter_of_open (λt ht, _) (hS.bUnion (λs hs, (hT s hs).2.1)) (λt ht, _),
  show is_open t,
  { simp only [exists_prop, set.mem_Union] at ht,
    rcases ht with ⟨s, hs, tTs⟩,
    exact (hT s hs).1 t tTs },
  show closure t = univ,
  { simp only [exists_prop, set.mem_Union] at ht,
    rcases ht with ⟨s, hs, tTs⟩,
    apply subset.antisymm (subset_univ _),
    rw ← (hd s hs),
    apply closure_mono,
    have := sInter_subset_of_mem tTs,
    rwa ← (hT s hs).2.2 at this }
end

/-- Baire theorem: a countable intersection of dense Gδ sets is dense. Formulated here with
an index set which is a countable set in any type. -/
theorem dense_bInter_of_Gδ {S : set β} {f : β → set α} (ho : ∀s∈S, is_Gδ (f s))
  (hS : countable S) (hd : ∀s∈S, closure (f s) = univ) : closure (⋂s∈S, f s) = univ :=
begin
  rw ← sInter_image,
  apply dense_sInter_of_Gδ,
  { rwa ball_image_iff },
  { exact hS.image _ },
  { rwa ball_image_iff }
end

/-- Baire theorem: a countable intersection of dense Gδ sets is dense. Formulated here with
an index set which is an encodable type. -/
theorem dense_Inter_of_Gδ [encodable β] {f : β → set α} (ho : ∀s, is_Gδ (f s))
  (hd : ∀s, closure (f s) = univ) : closure (⋂s, f s) = univ :=
begin
  rw ← sInter_range,
  apply dense_sInter_of_Gδ,
  { rwa forall_range_iff },
  { exact countable_range _ },
  { rwa forall_range_iff }
end

/-- Baire theorem: if countably many closed sets cover the whole space, then their interiors
are dense. Formulated here with an index set which is a countable set in any type. -/
theorem dense_bUnion_interior_of_closed {S : set β} {f : β → set α} (hc : ∀s∈S, is_closed (f s))
  (hS : countable S) (hU : (⋃s∈S, f s) = univ) : closure (⋃s∈S, interior (f s)) = univ :=
begin
  let g := λs, - (frontier (f s)),
  have clos_g : closure (⋂s∈S, g s) = univ,
  { refine dense_bInter_of_open (λs hs, _) hS (λs hs, _),
    show is_open (g s), from is_open_compl_iff.2 is_closed_frontier,
    show closure (g s) = univ,
    { apply subset.antisymm (subset_univ _),
     simp [g, interior_frontier (hc s hs)] }},
  have : (⋂s∈S, g s) ⊆ (⋃s∈S, interior (f s)),
  { assume x hx,
    have : x ∈ ⋃s∈S, f s, { have := mem_univ x, rwa ← hU at this },
    rcases mem_bUnion_iff.1 this with ⟨s, hs, xs⟩,
    have : x ∈ g s := mem_bInter_iff.1 hx s hs,
    have : x ∈ interior (f s),
    { have : x ∈ f s \ (frontier (f s)) := mem_inter xs this,
      simpa [frontier, xs, closure_eq_of_is_closed (hc s hs)] using this },
    exact mem_bUnion_iff.2 ⟨s, ⟨hs, this⟩⟩ },
  have := closure_mono this,
  rw clos_g at this,
  exact subset.antisymm (subset_univ _) this
end

/-- Baire theorem: if countably many closed sets cover the whole space, then their interiors
are dense. Formulated here with ⋃₀. -/
theorem dense_sUnion_interior_of_closed {S : set (set α)} (hc : ∀s∈S, is_closed s)
  (hS : countable S) (hU : (⋃₀ S) = univ) : closure (⋃s∈S, interior s) = univ :=
by rw sUnion_eq_bUnion at hU; exact dense_bUnion_interior_of_closed hc hS hU

/-- Baire theorem: if countably many closed sets cover the whole space, then their interiors
are dense. Formulated here with an index set which is an encodable type. -/
theorem dense_Union_interior_of_closed [encodable β] {f : β → set α} (hc : ∀s, is_closed (f s))
  (hU : (⋃s, f s) = univ) : closure (⋃s, interior (f s)) = univ :=
begin
  rw ← bUnion_univ,
  apply dense_bUnion_interior_of_closed,
  { simp [hc] },
  { apply countable_encodable },
  { rwa ← bUnion_univ at hU }
end

/-- One of the most useful consequences of Baire theorem: if a countable union of closed sets
covers the space, then one of the sets has nonempty interior. -/
theorem nonempty_interior_of_Union_of_closed [nonempty α] [encodable β] {f : β → set α}
  (hc : ∀s, is_closed (f s)) (hU : (⋃s, f s) = univ) : ∃s x ε, 0 < ε ∧ ball x ε ⊆ f s :=
begin
  have : ∃s, (interior (f s)).nonempty,
  { by_contradiction h,
    simp only [not_exists, not_nonempty_iff_eq_empty] at h,
    have := calc ∅ = closure (⋃s, interior (f s)) : by simp [h]
                 ... = univ : dense_Union_interior_of_closed hc hU,
    exact univ_nonempty.ne_empty this.symm },
  rcases this with ⟨s, hs⟩,
  rcases hs with ⟨x, hx⟩,
  rcases mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hx) with ⟨ε, εpos, hε⟩,
  exact ⟨s, x, ε, εpos, hε⟩,
end

end Baire_theorem

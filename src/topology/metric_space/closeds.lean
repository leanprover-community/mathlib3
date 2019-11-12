/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sébastien Gouëzel
The metric and emetric space structure on the types of closed subsets and nonempty compact
subsets of a metric or emetric space

The Hausdorff distance induces an emetric space structure on the type of closed subsets
of an emetric space, called `closeds`. Its completeness, resp. compactness, resp.
second-countability, follow from the corresponding properties of the original space.

In a metric space, the type of nonempty compact subsets (called `nonempty_compacts`) also
inherits a metric space structure from the Hausdorff distance, as the Hausdorff edistance is
always finite in this context.
-/

import topology.metric_space.hausdorff_distance topology.opens
noncomputable theory
open_locale classical
open_locale topological_space

universe u
open classical lattice set function topological_space filter

namespace emetric
section
variables {α : Type u} [emetric_space α] {s : set α}

/-- In emetric spaces, the Hausdorff edistance defines an emetric space structure
on the type of closed subsets -/
instance closeds.emetric_space : emetric_space (closeds α) :=
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

/-- In a complete space, the type of closed subsets is complete for the
Hausdorff edistance. -/
instance closeds.complete_space [complete_space α] : complete_space (closeds α) :=
begin
  /- We will show that, if a sequence of sets `s n` satisfies
  `edist (s n) (s (n+1)) < 2^{-n}`, then it converges. This is enough to guarantee
  completeness, by a standard completeness criterion.
  We use the shorthand `B n = 2^{-n}` in ennreal. -/
  let B : ℕ → ennreal := ennreal.half_pow,
  /- Consider a sequence of closed sets `s n` with `edist (s n) (s (n+1)) < B n`.
  We will show that it converges. The limit set is t0 = ⋂n, closure (⋃m≥n, s m).
  We will have to show that a point in `s n` is close to a point in `t0`, and a point
  in `t0` is close to a point in `s n`. The completeness then follows from a
  standard criterion. -/
  refine complete_of_convergent_controlled_sequences _ ennreal.half_pow_pos (λs hs, _),
  let t0 := ⋂n, closure (⋃m≥n, (s m).val),
  have : is_closed t0 := is_closed_Inter (λ_, is_closed_closure),
  let t : closeds α := ⟨t0, this⟩,
  use t,
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
    have Im_succm : ∀m, edist (z m) (z (m+1)) ≤ B m,
    { assume m,
      by_cases hm : n≤m,
      { exact le_of_lt (I m hm (z_in_s m hm)).2 },
      { rw not_le at hm,
        have Im : z m = x := z_le_n m (le_of_lt hm),
        have Im' : z (m+1) = x := z_le_n (m+1) (nat.succ_le_of_lt hm),
        simp [Im, Im', ennreal.half_pow_pos] }},
    /- From the distance control between `z m` and `z (m+1)`, we deduce a distance control
    between `z k` and `z l` by summing the geometric series. -/
    have Iz : ∀k l N, N ≤ k → N ≤ l → edist (z k) (z l) ≤ 2 * B N :=
      λk l N hk hl, ennreal.edist_le_two_mul_half_pow hk hl Im_succm,
    -- it follows from the previous bound that `z` is a Cauchy sequence
    have : cauchy_seq z := ennreal.cauchy_seq_of_edist_le_half_pow Im_succm,
    -- therefore, it converges
    rcases cauchy_seq_tendsto_of_complete this with ⟨y, y_lim⟩,
    -- the limit point `y` will be the desired point, in `t0` and close to our initial point `x`.
    -- First, we check it belongs to `t0`.
    have : y ∈ t0 := mem_Inter.2 (λk, mem_closure_of_tendsto (by simp) y_lim
    begin
      simp only [exists_prop, set.mem_Union, filter.mem_at_top_sets, set.mem_preimage, set.preimage_Union],
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
    have : x ∈ closure (⋃m≥n, (s m).val), by apply mem_Inter.1 xt0 n,
    rcases mem_closure_iff'.1 this (B n) (ennreal.half_pow_pos n) with ⟨z, hz, Dxz⟩,
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
  have : tendsto (λn, 2 * ennreal.half_pow n) at_top (𝓝 (2 * 0)) :=
    ennreal.tendsto_mul_right ennreal.half_pow_tendsto_zero (by simp),
  rw mul_zero at this,
  have Z := (tendsto_orderable.1 this).2 ε εpos,
  simp only [filter.mem_at_top_sets, set.mem_set_of_eq] at Z,
  rcases Z with ⟨N, hN⟩,  --  ∀ (b : ℕ), b ≥ N → ε > 2 * B b
  exact ⟨N, λn hn, lt_of_le_of_lt (main n) (hN n hn)⟩
end

/-- In a compact space, the type of closed subsets is compact. -/
instance closeds.compact_space [compact_space α] : compact_space (closeds α) :=
⟨begin
  /- by completeness, it suffices to show that it is totally bounded,
    i.e., for all ε>0, there is a finite set which is ε-dense.
    start from a set `s` which is ε-dense in α. Then the subsets of `s`
    are finitely many, and ε-dense for the Hausdorff distance. -/
  refine compact_of_totally_bounded_is_closed (emetric.totally_bounded_iff.2 (λε εpos, _)) is_closed_univ,
  rcases dense εpos with ⟨δ, δpos, δlt⟩,
  rcases emetric.totally_bounded_iff.1 (compact_iff_totally_bounded_complete.1 (@compact_univ α _ _)).1 δ δpos
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
  let F := {f : closeds α | f.val ⊆ s},
  use F,
  split,
  -- `F` is finite
  { apply @finite_of_finite_image _ _ F (λf, f.val),
    { apply set.inj_on_of_injective, simp [subtype.val_injective] },
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

/-- In an emetric space, the type of non-empty compact subsets is an emetric space,
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

/-- In a complete space, the type of nonempty compact subsets is complete. This follows
from the same statement for closed subsets -/
instance nonempty_compacts.complete_space [complete_space α] : complete_space (nonempty_compacts α) :=
begin
  apply complete_space_of_is_complete_univ,
  apply (is_complete_image_iff nonempty_compacts.to_closeds.uniform_embedding).1,
  apply is_complete_of_is_closed,
  exact nonempty_compacts.is_closed_in_closeds
end

/-- In a compact space, the type of nonempty compact subsets is compact. This follows from
the same statement for closed subsets -/
instance nonempty_compacts.compact_space [compact_space α] : compact_space (nonempty_compacts α) :=
⟨begin
  rw compact_iff_compact_image_of_embedding nonempty_compacts.to_closeds.uniform_embedding.embedding,
  exact compact_of_closed nonempty_compacts.is_closed_in_closeds
end⟩

/-- In a second countable space, the type of nonempty compact subsets is second countable -/
instance nonempty_compacts.second_countable_topology [second_countable_topology α] :
  second_countable_topology (nonempty_compacts α) :=
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

end --section
end emetric --namespace

namespace metric
section

variables {α : Type u} [metric_space α]

/-- `nonempty_compacts α` inherits a metric space structure, as the Hausdorff
edistance between two such sets is finite. -/
instance nonempty_compacts.metric_space : metric_space (nonempty_compacts α) :=
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

/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.specific_limits.basic
import topology.G_delta
import topology.sets.compacts

/-!
# Baire theorem

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In a complete metric space, a countable intersection of dense open subsets is dense.

The good concept underlying the theorem is that of a Gδ set, i.e., a countable intersection
of open sets. Then Baire theorem can also be formulated as the fact that a countable
intersection of dense Gδ sets is a dense Gδ set. We prove Baire theorem, giving several different
formulations that can be handy. We also prove the important consequence that, if the space is
covered by a countable union of closed sets, then the union of their interiors is dense.

We also prove that in Baire spaces, the `residual` sets are exactly those containing a dense Gδ set.
-/

noncomputable theory

open_locale classical topology filter ennreal

open filter encodable set topological_space

variables {α : Type*} {β : Type*} {γ : Type*} {ι : Type*}

section Baire_theorem

open emetric ennreal

/-- The property `baire_space α` means that the topological space `α` has the Baire property:
any countable intersection of open dense subsets is dense.
Formulated here when the source space is ℕ (and subsumed below by `dense_Inter_of_open` working
with any encodable source space).-/
class baire_space (α : Type*) [topological_space α] : Prop :=
(baire_property : ∀ f : ℕ → set α, (∀ n, is_open (f n)) → (∀ n, dense (f n)) → dense (⋂n, f n))

/-- Baire theorems asserts that various topological spaces have the Baire property.
Two versions of these theorems are given.
The first states that complete pseudo_emetric spaces are Baire. -/
@[priority 100]
instance baire_category_theorem_emetric_complete [pseudo_emetric_space α] [complete_space α] :
  baire_space α :=
begin
  refine ⟨λ f ho hd, _⟩,
  let B : ℕ → ℝ≥0∞ := λn, 1/2^n,
  have Bpos : ∀n, 0 < B n,
  { intro n,
    simp only [B, one_div, one_mul, ennreal.inv_pos],
    exact pow_ne_top two_ne_top },
  /- Translate the density assumption into two functions `center` and `radius` associating
  to any n, x, δ, δpos a center and a positive radius such that
  `closed_ball center radius` is included both in `f n` and in `closed_ball x δ`.
  We can also require `radius ≤ (1/2)^(n+1)`, to ensure we get a Cauchy sequence later. -/
  have : ∀n x δ, δ ≠ 0 → ∃y r, 0 < r ∧ r ≤ B (n+1) ∧ closed_ball y r ⊆ (closed_ball x δ) ∩ f n,
  { assume n x δ δpos,
    have : x ∈ closure (f n) := hd n x,
    rcases emetric.mem_closure_iff.1 this (δ/2) (ennreal.half_pos δpos) with ⟨y, ys, xy⟩,
    rw edist_comm at xy,
    obtain ⟨r, rpos, hr⟩ : ∃ r > 0, closed_ball y r ⊆ f n :=
      nhds_basis_closed_eball.mem_iff.1 (is_open_iff_mem_nhds.1 (ho n) y ys),
    refine ⟨y, min (min (δ/2) r) (B (n+1)), _, _, λz hz, ⟨_, _⟩⟩,
    show 0 < min (min (δ / 2) r) (B (n+1)),
      from lt_min (lt_min (ennreal.half_pos δpos) rpos) (Bpos (n+1)),
    show min (min (δ / 2) r) (B (n+1)) ≤ B (n+1), from min_le_right _ _,
    show z ∈ closed_ball x δ, from calc
      edist z x ≤ edist z y + edist y x : edist_triangle _ _ _
      ... ≤ (min (min (δ / 2) r) (B (n+1))) + (δ/2) : add_le_add hz (le_of_lt xy)
      ... ≤ δ/2 + δ/2 : add_le_add (le_trans (min_le_left _ _) (min_le_left _ _)) le_rfl
      ... = δ : ennreal.add_halves δ,
    show z ∈ f n, from hr (calc
      edist z y ≤ min (min (δ / 2) r) (B (n+1)) : hz
      ... ≤ r : le_trans (min_le_left _ _) (min_le_right _ _)) },
  choose! center radius Hpos HB Hball using this,
  refine λ x, (mem_closure_iff_nhds_basis nhds_basis_closed_eball).2 (λ ε εpos, _),
  /- `ε` is positive. We have to find a point in the ball of radius `ε` around `x` belonging to all
  `f n`. For this, we construct inductively a sequence `F n = (c n, r n)` such that the closed ball
  `closed_ball (c n) (r n)` is included in the previous ball and in `f n`, and such that
  `r n` is small enough to ensure that `c n` is a Cauchy sequence. Then `c n` converges to a
  limit which belongs to all the `f n`. -/
  let F : ℕ → (α × ℝ≥0∞) := λn, nat.rec_on n (prod.mk x (min ε (B 0)))
                              (λn p, prod.mk (center n p.1 p.2) (radius n p.1 p.2)),
  let c : ℕ → α := λn, (F n).1,
  let r : ℕ → ℝ≥0∞ := λn, (F n).2,
  have rpos : ∀ n, 0 < r n,
  { assume n,
    induction n with n hn,
    exact lt_min εpos (Bpos 0),
    exact Hpos n (c n) (r n) hn.ne' },
  have r0 : ∀ n, r n ≠ 0 := λ n, (rpos n).ne',
  have rB : ∀n, r n ≤ B n,
  { assume n,
    induction n with n hn,
    exact min_le_right _ _,
    exact HB n (c n) (r n) (r0 n) },
  have incl : ∀n, closed_ball (c (n+1)) (r (n+1)) ⊆ (closed_ball (c n) (r n)) ∩ (f n) :=
    λ n, Hball n (c n) (r n) (r0 n),
  have cdist : ∀n, edist (c n) (c (n+1)) ≤ B n,
  { assume n,
    rw edist_comm,
    have A : c (n+1) ∈ closed_ball (c (n+1)) (r (n+1)) := mem_closed_ball_self,
    have I := calc
      closed_ball (c (n+1)) (r (n+1)) ⊆ closed_ball (c n) (r n) :
        subset.trans (incl n) (inter_subset_left _ _)
      ... ⊆ closed_ball (c n) (B n) : closed_ball_subset_closed_ball (rB n),
    exact I A },
  have : cauchy_seq c :=
    cauchy_seq_of_edist_le_geometric_two _ one_ne_top cdist,
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
    refine is_closed_ball.mem_of_tendsto ylim _,
    refine (filter.eventually_ge_at_top n).mono (λ m hm, _),
    exact I n m hm mem_closed_ball_self },
  split,
  show ∀n, y ∈ f n,
  { assume n,
    have : closed_ball (c (n+1)) (r (n+1)) ⊆ f n := subset.trans (incl n) (inter_subset_right _ _),
    exact this (yball (n+1)) },
  show edist y x ≤ ε, from le_trans (yball 0) (min_le_left _ _),
end

/-- The second theorem states that locally compact spaces are Baire. -/
@[priority 100]
instance baire_category_theorem_locally_compact [topological_space α] [t2_space α]
  [locally_compact_space α] :
  baire_space α :=
begin
  constructor,
  intros f ho hd,
  /- To prove that an intersection of open dense subsets is dense, prove that its intersection
  with any open neighbourhood `U` is dense. Define recursively a decreasing sequence `K` of
  compact neighbourhoods: start with some compact neighbourhood inside `U`, then at each step,
  take its interior, intersect with `f n`, then choose a compact neighbourhood inside the
  intersection.-/
  apply dense_iff_inter_open.2,
  intros U U_open U_nonempty,
  rcases exists_positive_compacts_subset U_open U_nonempty with ⟨K₀, hK₀⟩,
  have : ∀ n (K : positive_compacts α), ∃ K' : positive_compacts α, ↑K' ⊆ f n ∩ interior K,
  { refine λ n K, exists_positive_compacts_subset ((ho n).inter is_open_interior) _,
    rw inter_comm,
    exact (hd n).inter_open_nonempty _ is_open_interior K.interior_nonempty },
  choose K_next hK_next,
  let K : ℕ → positive_compacts α := λ n, nat.rec_on n K₀ K_next,
  /- This is a decreasing sequence of positive compacts contained in suitable open sets `f n`.-/
  have hK_decreasing : ∀ (n : ℕ), ↑(K (n + 1)) ⊆ f n ∩ K n,
    from λ n, (hK_next n (K n)).trans $ inter_subset_inter_right _ interior_subset,
  /- Prove that ̀`⋂ n : ℕ, K n` is inside `U ∩ ⋂ n : ℕ, (f n)`. -/
  have hK_subset : (⋂ n, K n : set α) ⊆ U ∩ (⋂ n, f n),
  { intros x hx,
    simp only [mem_inter_iff, mem_Inter] at hx ⊢,
    exact ⟨hK₀ $ hx 0, λ n, (hK_decreasing n (hx (n + 1))).1⟩ },
  /- Prove that `⋂ n : ℕ, K n` is not empty, as an intersection of a decreasing sequence
  of nonempty compact subsets.-/
  have hK_nonempty : (⋂ n, K n : set α).nonempty,
    from is_compact.nonempty_Inter_of_sequence_nonempty_compact_closed _
      (λ n, (hK_decreasing n).trans (inter_subset_right _ _))
      (λ n, (K n).nonempty) (K 0).is_compact (λ n, (K n).is_compact.is_closed),
  exact hK_nonempty.mono hK_subset
end

variables [topological_space α] [baire_space α]

/-- Definition of a Baire space. -/
theorem dense_Inter_of_open_nat {f : ℕ → set α} (ho : ∀ n, is_open (f n)) (hd : ∀ n, dense (f n)) :
  dense (⋂ n, f n) :=
baire_space.baire_property f ho hd

/-- Baire theorem: a countable intersection of dense open sets is dense. Formulated here with ⋂₀. -/
theorem dense_sInter_of_open {S : set (set α)} (ho : ∀s∈S, is_open s) (hS : S.countable)
  (hd : ∀s∈S, dense s) : dense (⋂₀S) :=
begin
  cases S.eq_empty_or_nonempty with h h,
  { simp [h] },
  { rcases hS.exists_eq_range h with ⟨f, hf⟩,
    have F : ∀n, f n ∈ S := λn, by rw hf; exact mem_range_self _,
    rw [hf, sInter_range],
    exact dense_Inter_of_open_nat (λn, ho _ (F n)) (λn, hd _ (F n)) }
end

/-- Baire theorem: a countable intersection of dense open sets is dense. Formulated here with
an index set which is a countable set in any type. -/
theorem dense_bInter_of_open {S : set β} {f : β → set α} (ho : ∀s∈S, is_open (f s))
  (hS : S.countable) (hd : ∀s∈S, dense (f s)) : dense (⋂s∈S, f s) :=
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
  (hd : ∀s, dense (f s)) : dense (⋂s, f s) :=
begin
  rw ← sInter_range,
  apply dense_sInter_of_open,
  { rwa forall_range_iff },
  { exact countable_range _ },
  { rwa forall_range_iff }
end

/-- A set is residual (comeagre) if and only if it includes a dense `Gδ` set. -/
lemma mem_residual {s : set α} :
  s ∈ residual α ↔ ∃ t ⊆ s, is_Gδ t ∧ dense t :=
begin
  split,
  { rw mem_residual_iff,
    rintros ⟨S, hSo, hSd, Sct, Ss⟩,
    refine ⟨_, Ss, ⟨_, λ t ht, hSo _ ht, Sct, rfl⟩, _⟩,
    exact dense_sInter_of_open hSo Sct hSd, },
  rintros ⟨t, ts, ho, hd⟩,
  exact mem_of_superset (residual_of_dense_Gδ ho hd) ts,
end

/-- A property holds on a residual (comeagre) set if and only if it holds on some dense `Gδ` set. -/
lemma eventually_residual {p : α → Prop} :
  (∀ᶠ x in residual α, p x) ↔ ∃ (t : set α), is_Gδ t ∧ dense t ∧ ∀ (x : α), x ∈ t → p x :=
begin
  -- this can probably be improved...
  convert @mem_residual _ _ _ p,
  simp_rw [exists_prop, and_comm ((_ : set α) ⊆ p), and_assoc],
  refl,
end

lemma dense_of_mem_residual {s : set α} (hs : s ∈ residual α) : dense s :=
let ⟨t, hts, _, hd⟩ := mem_residual.1 hs in hd.mono hts

/-- Baire theorem: a countable intersection of dense Gδ sets is dense. Formulated here with ⋂₀. -/
theorem dense_sInter_of_Gδ {S : set (set α)} (ho : ∀s∈S, is_Gδ s) (hS : S.countable)
  (hd : ∀s∈S, dense s) : dense (⋂₀S) :=
dense_of_mem_residual ((countable_sInter_mem hS).mpr
  (λ s hs, residual_of_dense_Gδ (ho _ hs) (hd _ hs)))

/-- Baire theorem: a countable intersection of dense Gδ sets is dense. Formulated here with
an index set which is an encodable type. -/
theorem dense_Inter_of_Gδ [encodable β] {f : β → set α} (ho : ∀s, is_Gδ (f s))
  (hd : ∀s, dense (f s)) : dense (⋂s, f s) :=
begin
  rw ← sInter_range,
  exact dense_sInter_of_Gδ (forall_range_iff.2 ‹_›) (countable_range _) (forall_range_iff.2 ‹_›)
end

/-- Baire theorem: a countable intersection of dense Gδ sets is dense. Formulated here with
an index set which is a countable set in any type. -/
theorem dense_bInter_of_Gδ {S : set β} {f : Π x ∈ S, set α} (ho : ∀s∈S, is_Gδ (f s ‹_›))
  (hS : S.countable) (hd : ∀s∈S, dense (f s ‹_›)) : dense (⋂s∈S, f s ‹_›) :=
begin
  rw bInter_eq_Inter,
  haveI := hS.to_encodable,
  exact dense_Inter_of_Gδ (λ s, ho s s.2) (λ s, hd s s.2)
end

/-- Baire theorem: the intersection of two dense Gδ sets is dense. -/
theorem dense.inter_of_Gδ {s t : set α} (hs : is_Gδ s) (ht : is_Gδ t) (hsc : dense s)
  (htc : dense t) :
  dense (s ∩ t) :=
begin
  rw [inter_eq_Inter],
  apply dense_Inter_of_Gδ; simp [bool.forall_bool, *]
end

/-- If a countable family of closed sets cover a dense `Gδ` set, then the union of their interiors
is dense. Formulated here with `⋃`. -/
lemma is_Gδ.dense_Union_interior_of_closed [encodable ι] {s : set α} (hs : is_Gδ s)
  (hd : dense s) {f : ι → set α} (hc : ∀ i, is_closed (f i)) (hU : s ⊆ ⋃ i, f i) :
  dense (⋃ i, interior (f i)) :=
begin
  let g := λ i, (frontier (f i))ᶜ,
  have hgo : ∀ i, is_open (g i), from λ i, is_closed_frontier.is_open_compl,
  have hgd : dense (⋂ i, g i),
  { refine dense_Inter_of_open hgo (λ i x, _),
    rw [closure_compl, interior_frontier (hc _)],
    exact id },
  refine (hd.inter_of_Gδ hs (is_Gδ_Inter_of_open $ λ i, hgo i) hgd).mono _,
  rintro x ⟨hxs, hxg⟩,
  rw [mem_Inter] at hxg,
  rcases mem_Union.1 (hU hxs) with ⟨i, hi⟩,
  exact mem_Union.2 ⟨i, self_diff_frontier (f i) ▸ ⟨hi, hxg _⟩⟩,
end

/-- If a countable family of closed sets cover a dense `Gδ` set, then the union of their interiors
is dense. Formulated here with a union over a countable set in any type. -/
lemma is_Gδ.dense_bUnion_interior_of_closed {t : set ι} {s : set α} (hs : is_Gδ s)
  (hd : dense s) (ht : t.countable) {f : ι → set α} (hc : ∀ i ∈ t, is_closed (f i))
  (hU : s ⊆ ⋃ i ∈ t, f i) :
  dense (⋃ i ∈ t, interior (f i)) :=
begin
  haveI := ht.to_encodable,
  simp only [bUnion_eq_Union, set_coe.forall'] at *,
  exact hs.dense_Union_interior_of_closed hd hc hU
end

/-- If a countable family of closed sets cover a dense `Gδ` set, then the union of their interiors
is dense. Formulated here with `⋃₀`. -/
lemma is_Gδ.dense_sUnion_interior_of_closed {T : set (set α)} {s : set α} (hs : is_Gδ s)
  (hd : dense s) (hc : T.countable) (hc' : ∀ t ∈ T, is_closed t) (hU : s ⊆ ⋃₀ T) :
  dense (⋃ t ∈ T, interior t) :=
hs.dense_bUnion_interior_of_closed hd hc hc' $ by rwa [← sUnion_eq_bUnion]

/-- Baire theorem: if countably many closed sets cover the whole space, then their interiors
are dense. Formulated here with an index set which is a countable set in any type. -/
theorem dense_bUnion_interior_of_closed {S : set β} {f : β → set α} (hc : ∀s∈S, is_closed (f s))
  (hS : S.countable) (hU : (⋃s∈S, f s) = univ) : dense (⋃s∈S, interior (f s)) :=
is_Gδ_univ.dense_bUnion_interior_of_closed dense_univ hS hc hU.ge

/-- Baire theorem: if countably many closed sets cover the whole space, then their interiors
are dense. Formulated here with `⋃₀`. -/
theorem dense_sUnion_interior_of_closed {S : set (set α)} (hc : ∀s∈S, is_closed s)
  (hS : S.countable) (hU : (⋃₀ S) = univ) : dense (⋃s∈S, interior s) :=
is_Gδ_univ.dense_sUnion_interior_of_closed dense_univ hS hc hU.ge

/-- Baire theorem: if countably many closed sets cover the whole space, then their interiors
are dense. Formulated here with an index set which is an encodable type. -/
theorem dense_Union_interior_of_closed [encodable β] {f : β → set α} (hc : ∀s, is_closed (f s))
  (hU : (⋃s, f s) = univ) : dense (⋃s, interior (f s)) :=
is_Gδ_univ.dense_Union_interior_of_closed dense_univ hc hU.ge

/-- One of the most useful consequences of Baire theorem: if a countable union of closed sets
covers the space, then one of the sets has nonempty interior. -/
theorem nonempty_interior_of_Union_of_closed [nonempty α] [encodable β] {f : β → set α}
  (hc : ∀s, is_closed (f s)) (hU : (⋃s, f s) = univ) :
  ∃s, (interior $ f s).nonempty :=
by simpa using (dense_Union_interior_of_closed hc hU).nonempty

end Baire_theorem

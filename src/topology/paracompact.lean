/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Yury Kudryashov
-/
import topology.subset_properties
import topology.separation
import topology.metric_space.emetric_space
import set_theory.ordinal

/-!
# Paracompact topological spaces

-/

open set filter function
open_locale filter topological_space ennreal

universes u v

/-- A topological space is called paracompact, if every open covering of this space admits
a locally finite refinement. -/
class paracompact_space (X : Type u) [topological_space X] : Prop :=
(locally_finite_refinement :
  ∀ (S : set (set X)) (ho : ∀ s ∈ S, is_open s) (hc : ⋃₀ S = univ),
  ∃ (α : Type u) (t : α → set X) (ho : ∀ a, is_open (t a)) (hc : (⋃ a, t a) = univ),
    locally_finite t ∧ ∀ a, ∃ s ∈ S, t a ⊆ s)

variables {ι X : Type*} [topological_space X]

/-- Any open cover of a paracompact space has a locally finite *precise* refinement, that is,
 one indexed on the same type with each open set contained in the corresponding original one. -/
lemma paracompact_space.precise_refinement [paracompact_space X] (u : ι → set X)
  (uo : ∀ a, is_open (u a)) (uc : (⋃ i, u i) = univ) :
  ∃ v : ι → set X, (∀ a, is_open (v a)) ∧ (⋃ i, v i) = univ ∧ locally_finite v ∧ (∀ a, v a ⊆ u a) :=
begin
  have := paracompact_space.locally_finite_refinement (range u) (forall_range_iff.2 uo) uc,
  simp_rw [exists_range_iff, exists_prop, Union_eq_univ_iff] at this,
  choose α t hto hXt htf ind hind, choose t_inv ht_inv using hXt, choose U hxU hU using htf,
  refine ⟨λ i, ⋃ (a : α) (ha : ind a = i), t a, _, _, _, _⟩,
  { exact λ a, is_open_Union (λ a, is_open_Union $ λ ha, hto a) },
  { simp only [eq_univ_iff_forall, mem_Union],
    exact λ x, ⟨ind (t_inv x), _, rfl, ht_inv _⟩ },
  { refine λ x, ⟨U x, hxU x, ((hU x).image ind).subset _⟩,
    simp only [subset_def, mem_Union, mem_set_of_eq, set.nonempty, mem_inter_eq],
    rintro i ⟨y, ⟨a, rfl, hya⟩, hyU⟩,
    exact mem_image_of_mem _ ⟨y, hya, hyU⟩ },
  { simp only [subset_def, mem_Union],
    rintro i x ⟨a, rfl, hxa⟩,
    exact hind _ hxa }
end

instance paracompact_of_compact [compact_space X] : paracompact_space X :=
begin
  refine ⟨λ S hSo hSu, _⟩,
  rw sUnion_eq_Union at hSu,
  rcases compact_univ.elim_finite_subcover _ (λ s : S, hSo s.1 s.2)  hSu.ge with ⟨T, hT⟩,
  simp only [subset_def, mem_Union, mem_univ, forall_prop_of_true] at hT, choose s hsT hs using hT,
  refine ⟨(T : set S), λ t, t.1.1, λ t, hSo _ t.1.2,
    univ_subset_iff.1 $ λ x hx, mem_Union.2 ⟨⟨s x, hsT x⟩, hs x⟩, locally_finite_of_fintype _,
    λ t, ⟨t.1.1, t.1.2, subset.refl _⟩⟩
end

instance paracompact_of_locally_compact_sigma_compact [locally_compact_space X]
  [sigma_compact_space X] [t2_space X] : paracompact_space X :=
begin
  classical,
  refine ⟨λ S hSo hSc, _⟩,
  -- For technical reasons we prepend two empty sets to the sequence `compact_covering X`
  set K : ℕ → set X := λ n, nat.cases_on n ∅ (λ n, nat.cases_on n ∅ (compact_covering X)),
  -- Now we restate properties of `compact_covering X` for `K`
  have hKc : ∀ n, is_compact (K n),
  { rintro (_|_|n); simp [K, is_compact_compact_covering] },
  have hKsub : ∀ n, K n ⊆ interior (K (n + 1)),
  { rintro (_|_|n); simp [K, compact_covering_subset_interior, nat.lt_succ_self] },
  have hKsub' : ∀ n, K n ≤ K (n + 1),
    from λ n, subset.trans (hKsub n) interior_subset,
  have hKcov : ∀ x, ∃ n, x ∈ K (n + 2) \ K (n + 1),
  { intro x,
    have := Union_eq_univ_iff.1 (Union_compact_covering X) x,
    rcases nat.find_x this with ⟨n, hn, hlt⟩,
    refine ⟨n, hn, _⟩,
    rcases n with (_|n),
    exacts [not_mem_empty _, hlt _ n.lt_succ_self] },
  -- Next we choose a finite covering `T n` of each `K (n + 2) \ interior (K (n + 1))`
  have : ∀ n, ∃ T ⊆ S, finite T ∧ K (n + 2) \ interior (K (n + 1)) ⊆ ⋃₀ T,
  { intro n,
    simp only [sUnion_eq_bUnion],
    apply (compact_diff (hKc (n + 2)) is_open_interior).elim_finite_subcover_image,
    { exact λ s hs, hSo s hs },
    { rw [← sUnion_eq_bUnion, hSc],
      exact subset_univ _ } },
  choose T hTS hTf hTK, haveI := λ n, (hTf n).fintype,
  -- Finally, we take the set of all `t \ K n`, `t ∈ T n`
  refine ⟨Σ n, T n, λ a, a.2 \ K a.1, _, _, _, _⟩,
  { rintro ⟨n, t⟩,
    exact is_open_diff (hSo _ (hTS n t.2)) (hKc _).is_closed },
  { refine Union_eq_univ_iff.2 (λ x, _),
    rcases hKcov x with ⟨n, hn⟩,
    rcases hTK n (diff_subset_diff_right interior_subset hn) with ⟨t, ht, hxt⟩,
    exact ⟨⟨n, t, ht⟩, hxt, λ hx, hn.2 (hKsub' _ hx)⟩ },
  { intro x,
    rcases hKcov x with ⟨n, hn⟩,
    refine ⟨interior (K (n + 3)), mem_nhds_sets is_open_interior (hKsub (n + 2) hn.1), _⟩,
    have : (⋃ k ≤ n + 2, (range $ sigma.mk k) : set (Σ n, T n)).finite,
      from (finite_le_nat _).bUnion (λ k hk, finite_range _),
    apply this.subset, rintro ⟨k, t, ht⟩,
    simp only [mem_Union, mem_set_of_eq, mem_image_eq, subtype.coe_mk],
    rintro ⟨x, ⟨hxt, hxk⟩, hxn⟩,
    refine ⟨k, _, ⟨t, ht⟩, rfl⟩,
    contrapose! hxk with hnk,
    exact monotone_of_monotone_nat hKsub' hnk (interior_subset hxn) },
  { rintro ⟨n, t, ht⟩,
    exact ⟨t, hTS n ht, diff_subset _ _⟩ }
end

open emetric
lemma paracompact_of_emetric {X : Type*} [emetric_space X] : paracompact_space X :=
begin
  have pow_pos : ∀ k : ℕ, (0 : ℝ≥0∞) < 2⁻¹ ^ k,
    from λ k, ennreal.pow_pos (ennreal.inv_pos.2 ennreal.two_ne_top) _,
  have hpow_le : ∀ {m n : ℕ}, m ≤ n → (2⁻¹ : ℝ≥0∞) ^ n ≤ 2⁻¹ ^ m,
    from λ m n h, ennreal.pow_le_pow_of_le_one (ennreal.inv_le_one.2 ennreal.one_lt_two.le) h,
  have h2pow : ∀ n : ℕ, 2 * (2⁻¹ : ℝ≥0∞) ^ (n + 1) = 2⁻¹ ^ n,
    by { intro n, simp [pow_succ, ← mul_assoc, ennreal.mul_inv_cancel] },
  refine ⟨λ S hSo hScov, _⟩,
  simp only [sUnion_eq_univ_iff, set_coe.exists'] at hScov,
  set r : S → S → Prop := well_ordering_rel,
  have wf : well_founded r := is_well_order.wf,
  set ind : X → S := λ x, wf.min {s : S | x ∈ (s : set X)} (hScov x),
  have mem_ind : ∀ x, x ∈ (ind x : set X), from λ x, wf.min_mem _ (hScov x),
  have rel_ind : ∀ {x s}, r s (ind x) → x ∉ (s : set X),
    from λ x s hr hxs, wf.not_lt_min _ (hScov x) hxs hr,
  set D : ℕ → S → set X :=
    λ n, nat.strong_rec_on' n (λ n D' s,
      ⋃ (x : X) (hxs : ind x = s) (hb : ball x (3 * 2⁻¹ ^ n) ⊆ (s : set X))
        (hlt : ∀ (m < n) (s : S), x ∉ D' m ‹_› s), ball x (2⁻¹ ^ n)),
  have Dn : ∀ n s, D n s = ⋃ (x : X) (hxs : ind x = s) (hb : ball x (3 * 2⁻¹ ^ n) ⊆ (s : set X))
    (hlt : ∀ (m < n) (s : S), x ∉ D m s), ball x (2⁻¹ ^ n),
    from λ n s, by { simp only [D], rw nat.strong_rec_on_beta' },
  have memD : ∀ {n s y}, y ∈ D n s ↔ ∃ x (hxs : ind x = s) (hb : ball x (3 * 2⁻¹ ^ n) ⊆ (s : set X))
    (hlt : ∀ (m < n) (s : S), x ∉ D m s), edist y x < 2⁻¹ ^ n,
  { intros n s y, rw [Dn n s], simp only [mem_Union, mem_ball] },
  have Dcov : ∀ x, ∃ (s : S) (n : ℕ), x ∈ D n s,
  { intro x,
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ball x (3 * 2⁻¹ ^ n) ⊆ (ind x : set X),
    { rcases is_open_iff.1 (hSo (ind x) (ind x).2) x (mem_ind x) with ⟨ε, ε0, hε⟩,
      have : 0 < ε / 3 := ennreal.div_pos_iff.2 ⟨ε0.lt.ne', ennreal.coe_ne_top⟩,
      rcases ennreal.exists_inv_two_pow_lt this.ne' with ⟨n, hn⟩,
      refine ⟨n, subset.trans (ball_subset_ball _) hε⟩,
      simpa only [div_eq_mul_inv, mul_comm] using (ennreal.mul_lt_of_lt_div hn).le },
    by_contra h, push_neg at h,
    apply h (ind x) n,
    exact memD.2 ⟨x, rfl, hn, λ _ _ _, h _ _, mem_ball_self (pow_pos _)⟩ },
  have Dopen : ∀ n s, is_open (D n s),
  { intros n s,
    rw Dn,
    iterate 4 { refine is_open_Union (λ _, _) },
    exact is_open_ball },
  have HDS : ∀ n s, D n s ⊆ s,
  { intros n s x,
    rw memD,
    rintro ⟨y, rfl, hsub, -, hyx⟩,
    refine hsub (lt_of_lt_of_le hyx _),
    calc 2⁻¹ ^ n = 1 * 2⁻¹ ^ n : (one_mul _).symm
    ... ≤ 3 * 2⁻¹ ^ n : ennreal.mul_le_mul _ le_rfl,
    -- TODO: use `norm_num`
    have : ((1 : ℕ) : ℝ≥0∞) ≤ (3 : ℕ), from ennreal.coe_nat_le_coe_nat.2 (by norm_num1),
    exact_mod_cast this },
  refine ⟨ℕ × S, λ ns, D ns.1 ns.2, _, _, _, _⟩,
  { exact λ _, Dopen _ _ },
  { refine Union_eq_univ_iff.2 (λ x, _),
    rcases Dcov x with ⟨s, n, h⟩,
    exact ⟨⟨n, s⟩, h⟩ },
  { intro x,
    set s := wf.min {s | ∃ n, x ∈ D n s} (Dcov x),
    rcases wf.min_mem _ (Dcov x) with ⟨n, hn : x ∈ D n s⟩,
    have hs : ∀ s' n', x ∈ D n' s' → ¬r s' s,
    { intros s' n' h, exact wf.not_lt_min _ (Dcov x) ⟨n', h⟩ },
    have : D n s ∈ 𝓝 x, from mem_nhds_sets (Dopen _ _) hn,
    rcases (nhds_basis_uniformity uniformity_basis_edist_inv_two_pow).mem_iff.1 this
      with ⟨k, -, hsub : ball x (2⁻¹ ^ k) ⊆ D n s⟩,
    set B := ball x (2⁻¹ ^ (n + k + 1)),
    refine ⟨B, ball_mem_nhds _ (pow_pos _), _⟩,
    have Hgt : ∀ (i ≥ n + k + 1) (s : S), disjoint (D i s) B,
    { rintros i hi s y ⟨hyi, hyx⟩,
      rcases memD.1 hyi with ⟨z, rfl, hzi, H, hz⟩,
      have : z ∉ ball x (2⁻¹ ^ k), from λ hz, H n (by linarith) s (hsub hz), apply this,
      calc edist z x ≤ edist y z + edist y x : edist_triangle_left _ _ _
      ... < (2⁻¹ ^ i) + (2⁻¹ ^ (n + k + 1)) : ennreal.add_lt_add hz hyx
      ... ≤ (2⁻¹ ^ (k + 1)) + (2⁻¹ ^ (k + 1)) :
        add_le_add (hpow_le $ by linarith) (hpow_le $ by linarith)
      ... = (2⁻¹ ^ k) : by rw [← two_mul, h2pow] },
    have Hle : ∀ i ≤ n + k, set.subsingleton {s | (D i s ∩ B).nonempty},
    { rintros i hi s₁ ⟨y, hyD, hyB⟩ s₂ ⟨z, hzD, hzB⟩,
      apply @eq_of_incomp _ r, rw [← not_or_distrib], intro h,
      wlog h : r s₁ s₂ := h using [s₁ s₂ y z, s₂ s₁ z y],
      rcases memD.1 hyD with ⟨y', rfl, hsuby, -, hdisty⟩,
      rcases memD.1 hzD with ⟨z', rfl, -, -, hdistz⟩,
      suffices : edist z' y' < 3 * 2⁻¹ ^ i, from rel_ind h (hsuby this),
      calc edist z' y' ≤ edist z' x + edist x y' : edist_triangle _ _ _
      ... ≤ (edist z z' + edist z x) + (edist y x + edist y y') :
        add_le_add (edist_triangle_left _ _ _) (edist_triangle_left _ _ _)
      ... < (2⁻¹ ^ i + 2⁻¹ ^ (n + k + 1)) + (2⁻¹ ^ (n + k + 1) + 2⁻¹ ^ i) :
        by apply_rules [ennreal.add_lt_add]
      ... = 2 * (2⁻¹ ^ i + 2⁻¹ ^ (n + k + 1)) : by simp only [two_mul, add_comm]
      ... ≤ 2 * (2⁻¹ ^ i + 2⁻¹ ^ (i + 1)) :
        ennreal.mul_le_mul le_rfl $ add_le_add le_rfl $ hpow_le (add_le_add hi le_rfl)
      ... = 3 * 2⁻¹ ^ i : _,
      rw [mul_add, h2pow, bit1, add_mul, one_mul] },
    have : (⋃ (i ≤ n + k) (s ∈ {s : S | (D i s ∩ B).nonempty}), {(i, s)}).finite,
      from (finite_le_nat _).bUnion (λ i hi, (Hle i hi).finite.bUnion (λ _ _, finite_singleton _)),
    refine this.subset (λ I hI, _), simp only [mem_Union],
    refine ⟨I.1, _, I.2, hI, prod.mk.eta.symm⟩,
    refine not_lt.1 (λ hlt, Hgt I.1 hlt I.2 hI.some_spec) },
  { rintro ⟨n, s⟩,
    exact ⟨s, s.2, HDS _ _⟩ }
end
/-
See Mary Ellen Rudin, A new proof that metric spaces are paracompact.
https://www.ams.org/journals/proc/1969-020-02/S0002-9939-1969-0236876-3/S0002-9939-1969-0236876-3.pdf
-/

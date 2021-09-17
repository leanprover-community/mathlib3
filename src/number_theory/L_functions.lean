/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import number_theory.padics.padic_integers
import topology.continuous_function.compact

/-!
# L-functions

This file defines ... and proves ...

## Main definitions
 * `foo`
 * `bar`

## Implementation notes
TODO (optional)

## References
TODO (optional)

## Tags
L-function, totally disconnected, locally constant, ...
-/

def clopen_sets (H : Type*) [topological_space H] := {s : set H // is_clopen s}

variables (X : Type*)
variables [topological_space X] [compact_space X] [t2_space X] [totally_disconnected_space X]
variables {R : Type*} [normed_group R]
variables (A : Type*) [normed_comm_ring A]

--todo
--instance completeness {R : Type*} [normed_group R] : complete_space C(X, R) := sorry

-- TODO Remove `inclusion`
abbreviation inclusion (R : Type*) [topological_space R] : locally_constant X R → C(X,R) :=
locally_constant.to_continuous_map

-- TODO Remove `inclusion'`
abbreviation inclusion' : locally_constant X A →ₗ[A] C(X, A) :=
locally_constant.to_continuous_map_linear_map A

-- TODO Generalise this. Ideally appeal to corresponding result for compact-open topology
-- (cf #8721) if we can solve the defeq problem on the two topologies: CO and metric.
lemma continuous_const' [nonempty X] : continuous (continuous_map.const : A → C(X,A)) :=
begin
  rw metric.continuous_iff,
  intros a ε hε,
  refine ⟨ε/2, (show 0<ε/2, by linarith), λ b hb, _⟩,
  rw dist_eq_norm at hb ⊢,
  refine lt_of_le_of_lt _ (show ε/2 < ε, by linarith),
  rw continuous_map.norm_eq_supr_norm,
  apply csupr_le,
  intro x,
  apply le_of_lt,
  simp [hb],
end

instance [nonempty X] : has_continuous_smul A C(X, A) :=
⟨begin
  change continuous ((λ p, p.1 * p.2 : C(X,A) × C(X,A) → C(X,A)) ∘
    (λ p, ((continuous_map.const p.fst), p.2) : A × C(X,A) → C(X,A) × C(X,A))),
  have h := continuous_const' X A,
  continuity,
end⟩

noncomputable def char_fn {R : Type*} [topological_space R] [ring R] [topological_ring R]
  (U : clopen_sets X) : locally_constant X R :=
{
  to_fun := λ x, by classical; exact if (x ∈ U.val) then 1 else 0,
  is_locally_constant :=
    begin
      rw is_locally_constant.iff_exists_open, rintros x,
      by_cases x ∈ U.val,
      { refine ⟨U.val, ((U.prop).1), h, _⟩, rintros y hy, simp [h, hy], },
      { rw ←set.mem_compl_iff at h, refine ⟨(U.val)ᶜ, (is_clopen.compl U.prop).1, h, _⟩,
        rintros y hy, rw set.mem_compl_iff at h, rw set.mem_compl_iff at hy, simp [h, hy], },
    end,
}

lemma diff_inter_mem_sUnion {α : Type*} (s : set (set α)) (a y : set α) (h : y ∈ s) :
  (a \ ⋃₀ s) ∩ y = ∅ :=
begin
  rw [set.inter_comm, ← set.inter_diff_assoc, set.diff_eq_empty],
  exact (set.inter_subset_left y a).trans (set.subset_sUnion_of_mem h),
end

lemma clopen_finite_Union {H : Type*} [topological_space H]
  [locally_compact_space H] [t2_space H] [totally_disconnected_space H]
  (s : finset(set H)) (hs : ∀ x ∈ s, is_clopen x) :
  is_clopen ⋃₀ (s : set(set H)) :=
begin
  classical,
  apply finset.induction_on' s,
  { simp, },
  { rintros a S h's hS aS US,
    simp, apply is_clopen.union (hs a h's) US, },
end

lemma clopen_Union_disjoint {H : Type*} [topological_space H]
  [locally_compact_space H] [t2_space H] [totally_disconnected_space H]
  (s : finset(set H)) (hs : ∀ x ∈ s, is_clopen x) :
  ∃ (t : finset (set H)),
  (∀ (x ∈ (t : set (set H))), is_clopen x) ∧
  ⋃₀ (s : set(set H)) = ⋃₀ (t : set(set H)) ∧
  (∀ (x : set H) (hx : x ∈ t), ∃ z ∈ s, x ⊆ z) ∧
  ∀ (x y : set H) (hx : x ∈ t) (hy : y ∈ t) (h : x ≠ y), x ∩ y = ∅ :=
begin
  classical,
  apply finset.induction_on' s,
  { use ∅, simp, },
  { rintros a S h's hS aS ⟨t, clo, union, sub, disj⟩,
    set b := a \ ⋃₀ S with hb,
    use insert b t, split,
    { rintros x hx, simp at hx, cases hx,
      { rw hx, rw hb, apply is_clopen.diff (hs a h's) _,
        apply clopen_finite_Union, rintros y hy, apply hs y (hS hy), },
      { apply clo x hx,  }, },
    split,
    { simp only [finset.coe_insert, set.sUnion_insert], rw hb, rw ←union, rw set.diff_union_self, },
    { split,
      { rintros x hx, simp only [finset.mem_insert] at hx, cases hx,
        { use a, rw hx, rw hb, simp, apply set.diff_subset, },
        { specialize sub x hx, rcases sub with ⟨z, hz, xz⟩,
          refine ⟨z, _, xz⟩, rw finset.mem_insert, right, assumption, }, },
      { rintros x y hx hy ne, rw finset.mem_insert at hx, rw finset.mem_insert at hy,
        have : ∀ y ∈ t, b ∩ y = ∅,
        { rintros y hy, rw hb, rw union,
          apply diff_inter_mem_sUnion, assumption, },
        cases hx,
        { cases hy,
          { rw [hx, hy] at ne, exfalso, simp at ne, assumption, },
          { rw hx, apply this y hy, }, },
        { cases hy,
          { rw set.inter_comm, rw hy, apply this x hx, },
          { apply disj x y hx hy ne, }, }, }, }, },
end

--show that locally compact Hausdorff is tot disc iff zero dim

def h {A : Type*} [normed_ring A] (ε : ℝ) : A → set A := λ (x : A), metric.ball x (ε / 4)

def S {A : Type*} [normed_ring A] (ε : ℝ) : set (set A) := set.range (h ε)

variables {A} (f : C(X, A)) (ε : ℝ) [hε : 0 < ε]

def B : set(set X) := { j : set X | ∃ (U ∈ ((S ε) : set(set A))), j = f ⁻¹' U }

lemma opens : ∀ j ∈ (B X f ε), is_open j :=
begin
  rintros j hj, rw B at hj, rw set.mem_set_of_eq at hj,
  rcases hj with ⟨U, hU, jU⟩, rw jU, apply continuous.is_open_preimage, continuity,
  rw S at hU, rw set.mem_range at hU, cases hU with y hy, rw ←hy, rw h,
  simp, apply metric.is_open_ball,
end

lemma g'' (t : finset(set A))
  (ht : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t) (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i) :
  (set.univ ⊆ set.sUnion (B X f ε)) :=
begin
  rintros x hx, simp, have xt := ht hx, simp at xt,
  rcases xt with ⟨j, hj, jS, fj⟩, use f⁻¹' j, split,
  { use j, split, assumption, refl, }, simp [fj],
end

lemma dense_C_suff (f : C(X, A)) (t : finset(set A))
  (ht : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t) (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i) :
  ∃ (T' : finset (set X)),
    (∀ s ∈ T', is_clopen s ∧ ∃ U ∈ ((S ε) : set(set A)), (set.image f s : set A) ⊆ U) ∧
    ∀ (a : X), ∃! (b : set X) (H : b ∈ T'), a ∈ b :=
begin
  set B : set(set X) := (B X f ε) with hB,
  have f' := @loc_compact_Haus_tot_disc_of_zero_dim X _ _ _ _,
  obtain ⟨C, hC, h⟩ := @loc_compact_Haus_tot_disc_of_zero_dim X _ _ _ _,
  have g'' := g'' X f ε t ht,
  conv at g'' { congr, skip, rw set.sUnion_eq_Union, congr, funext,
    apply_congr classical.some_spec (classical.some_spec
    (topological_space.is_topological_basis.open_eq_sUnion f' (opens X f ε i.val i.prop))), },
  simp at g'', rw set.Union at g'',
  have try : ∃ (V ⊆ {s : set X | is_clopen s}), ((set.univ : set X) ⊆ set.sUnion V) ∧
             ∀ x ∈ V, ∃ U ∈ B, x ⊆ U,
  { refine ⟨ {j : set X | ∃ (U : set X) (hU : U ∈ B),
      j ∈ classical.some (topological_space.is_topological_basis.open_eq_sUnion f'
      (opens X f ε U hU))}, _, _ ⟩,
    intros j hj, simp only [set.mem_set_of_eq, exists_const] at hj, rcases hj with ⟨W, hW, hj⟩,
    obtain ⟨H, H1⟩ := classical.some_spec (topological_space.is_topological_basis.open_eq_sUnion f'
      (opens X f ε W hW)), apply H, apply hj, split,
    { intros x hx, rw set.mem_sUnion,
      have g3 := g'' hx, simp at g3, rcases g3 with ⟨U, hU, a, ha, xa⟩,
      refine ⟨a, _, xa⟩, simp, refine ⟨U, hU, ha⟩, },
      { rintros x hx, simp at hx, rcases hx with ⟨U, hU⟩, use U, cases hU with hU xU, simp [hU],
        obtain ⟨H, H1⟩ := classical.some_spec
        (topological_space.is_topological_basis.open_eq_sUnion f' (opens X f ε U _)),
        rw H1, intros u hu, simp, refine ⟨x, xU, hu⟩, }, },
  rcases try with ⟨V, hV, cover, clopen⟩,
  rw set.sUnion_eq_Union at cover,
  obtain ⟨s', h's⟩ := is_compact.elim_finite_subcover (@compact_univ X _ _) _ _ cover,
  --set s1 := (λ (i : V) (H : i ∈ s'), (i : set X)) with hs1,
  --have fin : set.finite (set.range s1),
  set s1 : (s' : set V) → set X := λ x, (x.1 : set X) with hs1,
  --set s1 := {i : set X | ∃ (j : V) (H : j ∈ s'), (j : set X) = i } with hs1,
  have fin : (set.range s1).finite,
  { apply set.finite_range _, apply finset.subtype.fintype, },
  obtain ⟨s, clo, hs, sub, disj⟩ := clopen_Union_disjoint (set.finite.to_finset fin) _,
  use s,
  { split,
    { rintros w hw, split, {apply clo w hw, },
      { specialize sub w hw, rcases sub with ⟨z, hz, wz⟩, simp at hz,
        rcases hz with ⟨z', h1, h2, h3⟩,
        specialize clopen z' h1, rcases clopen with ⟨U, BU, xU⟩, rw hB at BU, rw _root_.B at BU,
        simp at BU,
        rcases BU with ⟨U', h4, h5⟩, refine ⟨U', h4, _⟩, transitivity (set.image f z),
        { apply set.image_subset _ wz, }, { simp, rw ←h5, rw ←h3, rw hs1, simp [xU], }, }, },
    --constructor,
    { rintros a, have ha := h's (set.mem_univ a), simp at ha, rcases ha with ⟨U, hU, aU⟩,
      have : ∃ j ∈ s, a ∈ j,
      { have ha := h's (set.mem_univ a), simp at hs,
        suffices : a ∈ ⋃₀ (s : set (set X)), simp at this, cases this with j hj, use j, assumption,
        rw ←hs, simp, cases hU with hU s'U, refine ⟨U, hU, s'U, _⟩, rw hs1, simp [aU], },
      rcases this with ⟨j, hj, aj⟩, use j,
      split,
      { simp, refine ⟨hj, aj⟩, },
      { rintros y hy, simp at hy, cases hy with h1 h2, specialize disj j y hj h1,
        by_cases h : j = y, rw h.symm,
        exfalso, specialize disj h, have k := set.mem_inter aj h2,
        rw disj at k, simp at k, assumption, }, }, },
  { rintros x hx, simp at hx, rcases hx with ⟨U, hU, h1, h2⟩,
    suffices : is_clopen U, rw hs1 at h2, simp at h2, rw ←h2, apply this,
    have UC := hV hU, apply set.mem_def.1 UC, },
  { rintros i, have iC := hV i.2, apply topological_space.is_topological_basis.is_open f' iC, },
end

noncomputable def T' (ε : ℝ) (f : C(X, A)) (t : finset(set A))
 (ht : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t) (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i) :
 finset (set X) :=
classical.some (dense_C_suff X ε f t ht)

variables (t : finset(set A))
variables (ht : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t) (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i)

lemma ht1 : ∀ s ∈ T' X ε f t ht, is_clopen s ∧
  ∃ U ∈ ((S ε) : set(set A)), (set.image f s : set A) ⊆ U :=
begin
  rintros s hs,
  apply (classical.some_spec (dense_C_suff X ε f t ht)).1, apply hs,
end

lemma ht3 : ∀ (a : X), ∃! (b : set X) (H : b ∈ T' X ε f t ht), a ∈ b :=
begin
  apply (classical.some_spec (dense_C_suff X ε f t ht)).2,
end

lemma ht5 : ∀ s ∈ (T' X ε f t ht), ∃ U ∈ ((S ε) : set(set A)),  (set.image f s : set A) ⊆ U :=
begin
  rintros s hs,
  suffices : is_clopen s ∧ ∃ U ∈ ((S ε) : set(set A)), (set.image f s : set A) ⊆ U, apply this.2,
  apply (classical.some_spec (dense_C_suff X ε f t ht)).1, apply hs,
end

def c := λ (s : set X) (H : s ∈ (T' X ε f t ht)), (⟨s, (ht1 X f ε t ht s H).1⟩ : clopen_sets X)

noncomputable def c' := λ (s : set X) (H : s ∈ (T' X ε f t ht) ∧ nonempty s), classical.choice (H.2)

noncomputable def c2 (f : C(X, A)) (ε : ℝ) (t : finset(set A))
  (ht : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t) (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i) : X → A :=
λ x, f (c' X f ε t ht (classical.some (exists_of_exists_unique (ht3 X f ε t ht x)) )
begin
  have := (exists_prop.1 (exists_of_exists_unique (classical.some_spec
    (exists_of_exists_unique (ht3 X f ε t ht x))))),
  split,
  refine finset.mem_coe.1 (this).1,
  apply set.nonempty.to_subtype, rw set.nonempty, use x,
  apply this.2,
end).

lemma loc_const : is_locally_constant (c2 X f ε t ht) :=
begin
  have c2 := c2 X f ε t ht, -- this line must be useless because c2 is data and have forgets defns
  have ht1 := ht1 X f ε t ht,
  have ht3 := ht3 X f ε t ht,
  have ht4 : ∀ (a : X), ∃ (b : set X) (H : b ∈ (T' X ε f t ht)), a ∈ b,
   { rintros a, apply exists_of_exists_unique, simpa using ht3 a },
--  show is_locally_constant c2,
  rw is_locally_constant.iff_exists_open, rintros x, specialize ht4 x,
      rcases ht4 with ⟨U, hU, xU⟩, use U, split, {specialize ht1 U hU, apply (ht1.1).1, },
      use xU, rintros x' x'U, rw _root_.c2, simp, apply congr_arg,
      have : classical.some (exists_of_exists_unique (ht3 x)) = classical.some
        (exists_of_exists_unique (ht3 x')),
      { congr, ext y, simp, rintros hy, split,
        { rintros xy, specialize ht3 x, simp at ht3,
          cases ht3 with b hb, simp at hb, cases hb with hb hby, have hbU := hby U hU xU,
          have hby := hby y hy xy, rw hby, rw ←hbU, apply x'U, },
          { rintros xy, specialize ht3 x', simp at ht3,
            cases ht3 with b hb, simp at hb, cases hb with hb hby, have hbU := hby U hU x'U,
            have hby := hby y hy xy, rw hby, rw ←hbU, apply xU, }, },
      congr',
      repeat { ext y, simp, rintros hy, split,
      { rintros xy, specialize ht3 x', simp at ht3,
        cases ht3 with b hb, simp at hb, cases hb with hb hby, have hbU := hby U hU x'U,
        have hby := hby y hy xy, rw hby, rw ←hbU, apply xU, },
        { rintros xy, specialize ht3 x, simp at ht3,
          cases ht3 with b hb, simp at hb, cases hb with hb hby, have hbU := hby U hU xU,
          have hby := hby y hy xy, rw hby, rw ←hbU, apply x'U, }, },
      simp, ext y, revert y,
      rw ← set.ext_iff, symmetry,
      { congr, ext y, simp, rintros hy, split,
        { rintros xy, specialize ht3 x, simp at ht3,
          cases ht3 with b hb, simp at hb, cases hb with hb hby, have hbU := hby U hU xU,
          have hby := hby y hy xy, rw hby, rw ←hbU, apply x'U, },
        { rintros xy, specialize ht3 x', simp at ht3,
          cases ht3 with b hb, simp at hb, cases hb with hb hby, have hbU := hby U hU x'U,
          have hby := hby y hy xy, rw hby, rw ←hbU, apply xU, }, },
end

theorem tp_dense [nonempty X] (hε : 0 < ε) (f : C(X, A)) (t : finset(set A))
 (ht : set.univ ⊆ ⨆ (i : set A) (H : i ∈ t) (H : i ∈ ((S ε) : set(set A))), f ⁻¹' i) :
  ∃ (b : C(X, A)) (H_1 : b ∈ set.range (inclusion X A)), dist f b < ε :=
begin
  have ht1 := ht1 X f ε t ht, --have ht5 := ht1.2,
  have ht3 := ht3 X f ε t ht,
  have ht4 : ∀ (a : X), ∃ (b : set X) (H : b ∈ (T' X ε f t ht)), a ∈ b,
   { rintros a, apply exists_of_exists_unique, specialize ht3 a, convert ht3, simp, },
   have loc_const := loc_const X f ε t ht,
   refine ⟨inclusion X A ⟨(c2 X f ε t ht), loc_const⟩, _, _⟩, { simp, },
/-     set b : locally_constant X A :=
      (∑ s in T', if H : s ∈ T' then ((f (c' s H)) • (char_fn X (c s H))) else 0) with hb, -/
    { have : dist f (inclusion X A ⟨(c2 X f ε t ht), loc_const⟩) ≤ (ε/2),
      { rw [dist_eq_norm, continuous_map.norm_eq_supr_norm],
        refine cSup_le _ _,
        { rw set.range_nonempty_iff_nonempty, assumption, },
        { rintros m hm, rw set.mem_range at hm, cases hm with y hy, rw ←hy, have ht3 := ht3 y,
          rcases ht3 with ⟨w, wT, hw⟩,
          obtain ⟨w1, w2⟩ := exists_prop.1 (exists_of_exists_unique wT),
          have : (inclusion X A ⟨(c2 X f ε t ht), loc_const⟩) y =
                 f (c' X f ε t ht w ⟨w1, ⟨⟨y, w2⟩⟩⟩),
          { change c2 X f ε t ht y = _, rw c2, simp, apply congr_arg,
            congr' 2, swap, congr, swap 3, congr,
            repeat { apply hw, refine classical.some_spec (exists_of_exists_unique (ht3 y)), }, },
          convert_to ∥(f y) - ((inclusion X A ⟨(c2 X f ε t ht), loc_const⟩) y)∥ ≤ ε/2,
          { simp only [continuous_map.coe_sub, pi.sub_apply], },
          rw this, --obtain ⟨U, hU, wU⟩ := (ht1 w w1).2, --have yU := wU w2, simp at yU,
          --rw S at ht5, rw set.mem_range at ht5, cases ht5 with z hz,
          have ht5 := (ht1 w w1).2, rcases ht5 with ⟨U, hU, wU⟩,
          --rw h at hz, simp only [continuous_map.to_fun_eq_coe] at hz,
          rw S at hU, rw set.mem_range at hU, cases hU with z hz,
          have tired' : f (c' X f ε t ht w ⟨w1, ⟨⟨y, w2⟩⟩⟩) ∈ set.image f w,
          { simp,
            refine ⟨(c' X f ε t ht w ⟨w1, ⟨⟨y, w2⟩⟩⟩), _, _⟩, { simp, }, refl, },
          have tired := wU tired',
          have tS' : f y ∈ set.image f w, { simp, refine ⟨y, w2, _⟩, refl, },
          have tS := wU tS',
          rw h at hz, rw hz.symm at tired, rw mem_ball_iff_norm at tired, rw hz.symm at tS,
          --have sub : f y - f ↑(c' w w1) = (f y - z) - (f ↑(c' w w1) - z),
          rw mem_ball_iff_norm at tS,
          conv_lhs { rw sub_eq_sub_add_sub _ _ z, },
          have : ε/2 = ε/4 + ε/4, { rw div_add_div_same, linarith, }, rw this,
          apply norm_add_le_of_le _ (le_of_lt tS),
          apply le_of_lt, rw ←norm_neg _, simp [tired], }, },
    rw le_iff_lt_or_eq at this, cases this, transitivity (ε/2), assumption, exact half_lt_self hε,
    { rw this, exact half_lt_self hε, }, },
end

theorem dense_C [nonempty X] : @dense (C(X, A)) _ (set.range (inclusion X A)) :=
begin
  rintros f,
  rw metric.mem_closure_iff,
  rintros ε hε,
  set h := λ (x : A), (metric.ball x (ε/4)) with h',
  set S := set.range h with hS,
  have g : (⋃₀ S) = set.univ,
  { rw set.sUnion_eq_univ_iff, rintros, refine ⟨metric.ball a (ε/4), _, _⟩, rw hS, rw set.mem_range,
    use a, simp, apply div_pos hε zero_lt_four, },
  set preh := set.preimage f (⋃₀ S) with preh',
  have g' : preh = set.univ,
  { rw preh', rw g, exact set.preimage_univ, },
  rw preh' at g',
  rw set.preimage_sUnion at g',
  rw set.subset.antisymm_iff at g',
  obtain ⟨t, ht⟩ := is_compact.elim_finite_subcover _ _ _ g'.2,
  { exact tp_dense X ε hε f t ht, },
  { exact compact_univ, },
  { rintros i, apply is_open_Union, rintros hi, apply continuous.is_open_preimage _,
    { rw [hS, h'] at hi, simp at hi, cases hi with y hy,
      suffices : is_open (metric.ball y (ε/4)),
      { rw hy at this, assumption, },
      refine @metric.is_open_ball A _ y (ε/4), },
    exact continuous_map.continuous f, },
-- working with clopen sets makes life easy
end
--end of density section

instance union : semilattice_inf_bot (clopen_sets X) :=
begin
  constructor,
  swap 5, use ⟨∅, is_clopen_empty⟩,
  swap 5, rintros a b, refine (a.val ⊆ b.val),
  swap 8, rintros a b, refine ⟨a.val ∩ b.val, is_clopen.inter a.prop b.prop⟩,
  { rintros a, apply set.empty_subset, },
  { rintros a b, apply set.inter_subset_left, },
  { rintros a b, apply set.inter_subset_right, },
  { rintros a b c ab ac, apply set.subset_inter_iff.2 ⟨ab, ac⟩, },
  { rintros a, apply set.subset.refl, },
  { rintros a b c ab ac, apply set.subset.trans ab ac, },
  { rintros a b ab ba, apply subtype.eq, apply set.subset.antisymm ab ba, },
end

instance : lattice (clopen_sets X) :=
begin
  refine subtype.lattice _ _,
  { rintros x y, apply is_clopen.union, },
  { rintros x y, apply is_clopen.inter, },
end

structure  distribution {R : Type*} [add_monoid R] :=
(phi : clopen_sets X → R)
(count_add ⦃f : ℕ → clopen_sets X⦄ :
  (∀ (S T : clopen_sets X), S ⊓ T = ⊥ →
  phi(S ⊔ T) = phi S + phi T))

structure distribution' :=
(phi : linear_map A (locally_constant X A) A)

variables (v : valuation A nnreal) (A)

def measures := {φ : distribution X // ∀ S : clopen_sets X, ∃ K : ℝ, (v (φ.phi S) : ℝ) ≤ K }

def measures' :=
  {φ : distribution' X //
    ∃ K : ℝ, ∀ f : (locally_constant X A), ∥φ.phi f∥ ≤ K * ∥inclusion X A f∥ }

def measures'' :=
  {φ : distribution' X //
    ∃ K : ℝ, 0 < K ∧ ∀ f : (locally_constant X A), ∥φ.phi f∥ ≤ K * ∥inclusion X A f∥ }

noncomputable instance : normed_group (locally_constant X A) :=
normed_group.induced
  locally_constant.to_continuous_map_add_monoid_hom
  locally_constant.to_continuous_map_injective

lemma integral_cont (φ : measures'' X A) : continuous (φ.1).phi :=
begin
  /-suffices : ∀ (b : locally_constant X A) (ε : ℝ), ε > 0 → (∃ (δ : ℝ) (H : δ > 0),
      ∀ (a : locally_constant X A), dist a b < δ → dist ((φ.val.phi) a) ((φ.val.phi) b) < ε),-/
  rw metric.continuous_iff, rintros b ε hε,
  obtain ⟨K, hKpos, hK⟩ := φ.prop,
  refine ⟨ε/K, div_pos hε hKpos, _⟩,
  rintros a dab, rw dist_eq_norm,
  rw ←linear_map.map_sub,
  specialize hK (a - b), apply lt_of_le_of_lt hK _, rw mul_comm, rw ←lt_div_iff hKpos,
  convert dab,
  change ∥inclusion X A (a - b)∥ = dist (inclusion' X A a) (inclusion' X A b),
  rw [dist_eq_norm, ← linear_map.map_sub],
  refl,
end

lemma di [nonempty X] : dense_inducing (inclusion X A) := ⟨⟨rfl⟩, dense_C X⟩

lemma uni_ind [nonempty X] : uniform_inducing (inclusion X A) := ⟨rfl⟩

lemma uni_cont (φ : measures'' X A) : uniform_continuous ⇑(φ.val.phi) :=
begin
  refine metric.uniform_continuous_iff.mpr _,
  rintros ε hε,
  obtain ⟨K, hKpos, hK⟩ := φ.prop,
  refine ⟨ε/K, div_pos hε hKpos, _⟩,
  rintros a b dab, rw dist_eq_norm,
  rw ←linear_map.map_sub,
  specialize hK (a - b), apply lt_of_le_of_lt hK _, rw mul_comm, rw ←lt_div_iff hKpos,
  convert dab,
  change ∥inclusion X A (a - b)∥ = dist (inclusion' X A a) (inclusion' X A b),
  rw [dist_eq_norm, ← linear_map.map_sub],
  refl,
end

lemma cont [complete_space A] [nonempty X] (φ : measures'' X A) :
  continuous ((di X A).extend (φ.val.phi)) :=
begin
  refine uniform_continuous.continuous _,
  refine uniform_continuous_uniformly_extend _ (dense_inducing.dense (di X A)) _,
  { apply uni_ind, },
  { apply uni_cont, },
end

noncomputable def integral [nonempty X] (φ : measures'' X A) [complete_space A] :
  continuous_linear_map A C(X, A) A :=
begin
  have cont := cont X A φ,
  have di := di X A,
  split,
  swap,
  { split, swap 3,
    { --X nonempty needed here, for the topo space on loc const to exist
      apply dense_inducing.extend di (φ.1).phi, },
    { refine dense_range.induction_on₂ (dense_inducing.dense di) _ _,
      { exact is_closed_eq (cont.comp continuous_add)
        ((cont.comp continuous_fst).add (cont.comp continuous_snd)) },
      { rintros a b,
        change di.extend (φ.val.phi) (inclusion' X A a + inclusion' X A b) =
  di.extend (φ.val.phi) (inclusion X A a) + di.extend (φ.val.phi) (inclusion X A b),
        rw ← linear_map.map_add,
        change di.extend (φ.val.phi) ((inclusion X A) (a + b)) =
  di.extend (φ.val.phi) (inclusion X A a) + di.extend (φ.val.phi) (inclusion X A b),
        repeat { rw dense_inducing.extend_eq di (integral_cont X A φ), },
        { simp only [linear_map.map_add], }, }, },
    { rintros m, refine (λ b, dense_range.induction_on (dense_inducing.dense di) b _ _),
      { exact is_closed_eq (cont.comp (continuous_const.smul continuous_id))
        ((continuous_const.smul continuous_id).comp cont) },
      { rintros a,
        change di.extend (φ.val.phi) (m • inclusion' X A a) =
        m • di.extend (φ.val.phi) (inclusion X A a),
        rw ← linear_map.map_smul,
        change di.extend (φ.val.phi) ((inclusion X A) (m • a)) =
        m • di.extend (φ.val.phi) (inclusion X A a),
        repeat { rw dense_inducing.extend_eq di (integral_cont X A φ), },
        simp only [linear_map.map_smul], }, }, },
  simp only [auto_param_eq], assumption,
end

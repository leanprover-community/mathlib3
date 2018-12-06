/-
Copyright (c) 2018 Rohan Mitta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Mitta, Patrick Massot, Alistair Tucker
-/
--When exercise/lemma/prop numbers are quoted here, the material comes from 
--"Metric Spaces and Topology" by Sutherland

import analysis.metric_space data.real.cau_seq_filter

noncomputable theory
local attribute [instance] classical.prop_decidable 

variables {α : Type*} {β : Type*} [metric_space α]
open filter

private lemma one_div_succ {n : ℕ} : (1 : ℝ) / (nat.succ n) > 0 :=
one_div_pos_of_pos (iff.mpr nat.cast_pos (nat.zero_lt_succ n))

--Exercise 6.26 (as setup for prop 17.6)
theorem lim_sequence_of_mem_closure {Y : set α} {a : α} (H : a ∈ closure Y) :
∃ (f : ℕ → α) (H1 : ∀ (n : ℕ), f n ∈ Y), filter.tendsto f at_top (nhds a)  := 
begin
  let ε := λ (n : ℕ), (1 : ℝ) / (n + 1),
  have g : Π (n : ℕ), {b : α // ∃ (h : b ∈ Y), dist a b < ε n},
    intro n,
    apply classical.indefinite_description,
    apply iff.mp mem_closure_iff' H,
    exact one_div_succ,
  constructor,
  constructor,
    intro n,
    cases (g n).property with h1 h2,
    exact h1,
  apply iff.mpr tendsto_iff_dist_tendsto_zero,
  apply squeeze_zero,
      intro n,
      exact dist_nonneg,
    intro n,
    show dist (g n).val a ≤ ε n,
    rewrite dist_comm,
    cases (g n).property with h1 h2,
    exact le_of_lt h2,
  exact sequentially_complete.tendsto_div,
end

def metric_space.seq_tendsto (u : ℕ → α) (a : α) : Prop :=
∀ ε > 0, ∃ (N : ℕ), ∀ {n}, n ≥ N → dist (u n) a < ε

lemma metric_space.unique_limit_seq (u : ℕ → α) (a b : α)  
  (Ha : metric_space.seq_tendsto u a) (Hb : metric_space.seq_tendsto u b) : a = b := 
tendsto_nhds_unique at_top_ne_bot (iff.mpr (tendsto_at_top_metric u) Ha) (iff.mpr (tendsto_at_top_metric u) Hb)

lemma metric_space.cauchy_of_convergent (u : ℕ → α) (H : ∃ (a : α), metric_space.seq_tendsto u a) : 
  cauchy_seq u := 
begin
  rw cauchy_seq_metric,
  cases H with a Ha,
  intros ε Hε,
  unfold metric_space.seq_tendsto at Ha,
  cases Ha (ε / 2) (div_pos Hε (by norm_num)) with N HN,
  existsi N,
  intros n m Hn Hm,
  have dist_n := HN Hn, rw dist_comm at dist_n,
  have := add_lt_add (HN Hm) (dist_n), 
  rw [← two_mul (ε / 2), mul_div_cancel' ε two_ne_zero] at this, 
  exact (lt_of_le_of_lt (dist_triangle (u m) a (u n)) this),
end

lemma subtype.seq_cauchy {Y : set α} (u : ℕ → α) (H1 : ∀ (n : ℕ), u n ∈ Y) :
  cauchy_seq u ↔ cauchy_seq (λ (n : ℕ), (⟨u n, H1 n⟩ : Y)) := 
by rw cauchy_seq_metric; rw cauchy_seq_metric; refl


lemma subtype.seq_tendsto {Y : set α} (u : ℕ → α) (H1 : ∀ (n : ℕ), u n ∈ Y) {a : α} (H2 : a ∈ Y) :
  metric_space.seq_tendsto u a ↔ metric_space.seq_tendsto (λ (n : ℕ), (⟨u n, H1 n⟩ : Y)) ⟨a, H2⟩ := by refl


--Proposition 17.6
theorem closed_of_complete_subspace_of_metric (Y : set α) [complete_space Y] :
is_closed Y := 
begin
  rw ← closure_eq_iff_is_closed, 
  apply set.eq_of_subset_of_subset,
  { intros x Hx,
    rcases lim_sequence_of_mem_closure Hx with ⟨sequence, Hxn, Hsequence⟩,
    rw tendsto_at_top_metric at Hsequence,
    have Ha := cauchy_seq_tendsto_of_complete  
      ((subtype.seq_cauchy sequence Hxn).1 (metric_space.cauchy_of_convergent sequence ⟨x, Hsequence⟩)), 
    cases Ha with a Ha,
    rw tendsto_at_top_metric at Ha,
    change metric_space.seq_tendsto (λ (n : ℕ), (⟨sequence n, Hxn n⟩ : Y)) a at Ha,
    cases a with a ha,
    rw ← subtype.seq_tendsto at Ha,
    change metric_space.seq_tendsto sequence x at Hsequence,
    change metric_space.seq_tendsto sequence a at Ha,
    have H4 := metric_space.unique_limit_seq sequence x a Hsequence Ha,
    rw H4, exact ha },
  exact subset_closure,
end

--Lemma for following lemma   
--Showing the filter definition of complete is equivalent to the sequences defintion for a metric space
lemma complete_iff_seq_complete :
  complete_space α ↔ ( ∀ (f : ℕ → α), cauchy (filter.map f at_top) → (∃ (a : α), tendsto f at_top (nhds a))) :=
begin 
  split, intros H f Hf,
    exact (@complete_space.complete _ _ H _ Hf),
  intro H,
  split,
  intros filt Hfilt,
  rw cauchy_of_metric at Hfilt,

  have this1 : ∀ n, 0 < (↑(n + 1) : ℝ) := by intro n; rw ← nat.cast_zero; rw (@nat.cast_lt ℝ _ 0 (n+1)); exact zero_lt_iff_ne_zero.2 (nat.succ_ne_zero n),

  have this2 := λ (n : ℕ), (@div_pos ℝ _ 1 (n+1) (@zero_lt_one ℝ _) (this1 n)),
    have this3 := λ n, (Hfilt.2 ((1 : ℝ)/(n+1 : ℕ))) (this2 n),
    have this4 := classical.axiom_of_choice (this3),

    cases this4 with f Hf, dsimp at f, dsimp at Hf,
    cases (classical.axiom_of_choice Hf) with Hf1 Hf2,
    dsimp at Hf1, dsimp at Hf2,
    
    have H3 : ∀ n, (f n) ≠ ∅,
      intro n,
      by_contradiction,
      rw not_not at a,
      have H2 := Hf1 n,
      rw a at H2,
      have H1 := empty_in_sets_eq_bot.1 H2,
      cc,

    have H4 : ∀ n, nonempty (f n),
    intro n, 
    cases set.exists_mem_of_ne_empty (H3 n) with x Hx,
    constructor,
    exact ⟨x, Hx⟩,  

    have seq_prop_better : ∀ (n : ℕ), ∃ (S : set α), (∀ (m : ℕ), m ≤ n → (S ⊆ (f m))) ∧ S ∈ filt.sets,
      intro n, induction n with N HN,
      existsi (f 0),
      exact ⟨λ n Hn, by rw (le_zero_iff_eq.1 Hn); exact (set.subset.refl (f 0)), Hf1 0⟩,
      cases HN with S0 HS0,
      existsi S0 ∩ (f (N+1)),
      refine ⟨_,inter_mem_sets HS0.2 (Hf1 (N+1))⟩,
      intro n,
      by_cases (n ≤ N),
      exact λ _ x Hx, (HS0.1 n h) Hx.1,
      rw not_le at h,
      intro Hn,

      rw (le_antisymm Hn (nat.succ_le_of_lt h)),
      intros x Hx, exact Hx.2,

    have seq_prop2 := classical.axiom_of_choice seq_prop_better, dsimp at seq_prop2,
    cases seq_prop2 with seqsets Hseqsets,
    
    have Hnonempty : ∀ n, nonempty (seqsets n),
      intro n,
        have Hnotempty : seqsets n ≠ ∅,
        by_contradiction,
        rw not_not at a,
        have := Hseqsets n,
        rw a at this,
        have := empty_in_sets_eq_bot.1 this.2,
        cc,
      cases set.exists_mem_of_ne_empty Hnotempty,  
      constructor, exact ⟨w,h⟩,
    have seq := λ (n : ℕ), classical.choice (Hnonempty n),

    have FGI : cauchy (map (λ (n : ℕ), (seq n).val) at_top),
      rw cauchy_of_metric,
      apply and.intro (map_ne_bot at_top_ne_bot),
      intros ε Hε,
      existsi (f (int.nat_abs (ceil ((1:ℝ)/ε)))),
      have Hnext : f (int.nat_abs ⌈1 / ε⌉) ∈ (map (λ (n : ℕ), (seq n).val) at_top).sets,
        rw mem_map,
        rw mem_at_top_sets,
        existsi (int.nat_abs ⌈1 / ε⌉),
        intros m Hm,
        exact (Hseqsets m).1 (int.nat_abs ⌈1 / ε⌉) Hm (seq m).property,        
      existsi Hnext,      
      intros x y Hx Hy,
      
      have exciting := Hf2 (int.nat_abs ⌈1 / ε⌉) x y Hx Hy,
       have Hnext3 : 1/ε > 0,
            apply (mul_lt_mul_right Hε).1,
            rw one_div_eq_inv, rw zero_mul,
            rw inv_mul_cancel (ne.symm (ne_of_lt Hε)),
            exact zero_lt_one,
      have Hnext2 : ceil (1/ε) ≥ 0,
          exact le_of_lt (ceil_pos.2 Hnext3),
      have Hnext : 1 / (↑(int.nat_abs ⌈1 / ε⌉) + 1) < ε,
        
        rw [← int.cast_coe_nat (int.nat_abs _), int.nat_abs_of_nonneg Hnext2],
        have Hfornext4 := lt_add_one (↑⌈1 / ε⌉ : ℝ),
          
        have Hnext4 : (1 : ℝ) / (↑⌈1 / ε⌉ + 1) < 1 / (↑⌈1 / ε⌉),
          exact one_div_lt_one_div_of_lt (int.cast_lt.2 (ceil_pos.2 Hnext3)) Hfornext4,
        apply lt_of_lt_of_le Hnext4,
        have Hnext5 := le_ceil (1/ε),
        have Hnext6 := one_div_le_one_div_of_le Hnext3 Hnext5,
        apply le_trans Hnext6,
        simp,
        exact lt_trans exciting Hnext,
        exact ⟨0⟩, 

  have := H (λ n, (seq n).1) FGI,
  cases this with a Ha,
  existsi a,
  unfold tendsto at Ha,
  intros S HS,

  rcases mem_nhds_sets_iff.1 HS with ⟨S1, HS1, H2S1⟩,
  rcases is_open_metric.1 H2S1.1 a H2S1.2 with ⟨ε, Hε, Hballε⟩,

  have Hepover2 : ε/2 > 0 := div_pos Hε (by norm_num),
  cases (tendsto_at_top_metric (λ (n : ℕ), (seq n).val)).1 Ha (ε/2) Hepover2 with N1 HN1,
  
  let N := max N1 (int.nat_abs ⌈2 / ε⌉),

  have HS3 : f N ⊆ ball a ε,
    intros x Hx,
    rw mem_ball,
    dsimp at HN1,
    have distance1 := Hf2 N x (seq N).val Hx ((Hseqsets N).1 N (le_refl N) (seq N).property),
    have lt_εover2 : 1 / (↑N + 1) < ε / 2,
      have le_somth := le_max_right N1 (int.nat_abs ⌈2 / ε⌉),
      have twoovereplt : 2 / ε < ↑(nat.succ N),
        apply lt_of_le_of_lt (le_ceil (2/ε)),
        have N_ge_ceil : int.nat_abs ⌈2 / ε⌉ ≤ N, 
        exact le_max_right _ _,
        have N_ge_ceil2 : ((int.nat_abs ⌈2 / ε⌉) : ℝ) ≤ ↑N := nat.cast_le.2 N_ge_ceil,
        have zero_le_ceiltwooverep : (0 : ℤ) ≤ ⌈2 / ε⌉,
        have zero_lt_twooverep : 0 < 2/ε,
        have := div_div_eq_mul_div 1 2 ε,
        simp at this,
        rw ← this at Hepover2,
        exact inv_pos'.1 Hepover2,
        apply int.cast_le.1,
        refine le_of_lt (lt_of_lt_of_le zero_lt_twooverep _),
        exact le_ceil _,

        have := int.nat_abs_of_nonneg zero_le_ceiltwooverep,
        change (((int.nat_abs ⌈2 / ε⌉) : ℤ) : ℝ) ≤ _ at N_ge_ceil2,
        rw this at N_ge_ceil2,
        refine lt_of_le_of_lt N_ge_ceil2 _,
        simp [zero_lt_one],

      have := (inv_lt_inv  (nat.cast_lt.2 (nat.zero_lt_succ N) : (0 : ℝ) < _) 
        (div_pos (by norm_num) Hε : (2 : ℝ)/ε > 0)).2 twoovereplt,
      rw inv_eq_one_div at this, rw inv_eq_one_div at this,
      rw div_div_eq_mul_div at this, rw one_mul at this,
      exact this,

    have distance2 := HN1 _ (le_max_left N1 (int.nat_abs ⌈2 / ε⌉)),
    have distance3 := dist_triangle x (seq N).val a,
    have distance4 := add_lt_add (lt_trans distance1 lt_εover2) distance2,
    have distance5 := lt_of_le_of_lt distance3 distance4,
    rw add_halves at distance5, exact distance5,
  
  apply mem_sets_of_superset (Hf1 N),
  exact set.subset.trans (set.subset.trans HS3 Hballε) HS1,
end

--Proposition 17.7
theorem complete_of_closed_subspace_of_complete [complete_space α] 
(Y : set α) (HY : is_closed Y) : complete_space Y := 
begin
  rw complete_iff_seq_complete,
  intros f Hf,
  rw complete_iff_seq_complete at _inst_2,
  have : cauchy_seq f := Hf,
  have this2 : f = (λ (n : ℕ), (⟨(f n).val, (f n).property⟩ : Y)),
  { simp },
  rw this2 at this,
  cases _inst_2 (λ n, (f n).val) ((subtype.seq_cauchy _ _).2 this) with a Ha,
  have H2 : a ∈ Y,  
  { apply mem_of_closed_of_tendsto at_top_ne_bot Ha HY,
  rw mem_at_top_sets, existsi 0, exact λ n _, (f n).property },
  existsi (⟨a, H2⟩ : Y),
  have H3 := subtype.seq_tendsto (λ n, (f n).val) (λ n, (f n).property) H2,
  simp at H3,
  rw tendsto_at_top_metric,
  apply H3.1,
  exact (tendsto_at_top_metric (λ (n : ℕ), (f n).val)).1 Ha
end

def subseq {α : Type*} (f : ℕ → α) (u : ℕ → α) := ∃ (map : ℕ → ℕ), u = f ∘ map ∧ tendsto map at_top at_top

--Prop 17.10
theorem convergent_of_cauchy_of_subseq_convergent {f : ℕ → α} (H : cauchy (filter.map f at_top))
 {sub : ℕ → α} (H1 : subseq sub f) {x : α} (H2 : metric_space.seq_tendsto sub x) : metric_space.seq_tendsto f x :=
begin
  cases H1 with map Hmap,
  rw Hmap.1, unfold tendsto at Hmap, unfold metric_space.seq_tendsto, 
  rw ← tendsto_at_top_metric,
  unfold metric_space.seq_tendsto at H2,
  rw ← tendsto_at_top_metric at H2, exact tendsto.comp tendsto_id (tendsto.comp Hmap.2 H2),
end

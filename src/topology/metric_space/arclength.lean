import analysis.bounded_variation

open_locale ennreal big_operators
noncomputable theory

variables {α E : Type*} [linear_order α] [pseudo_emetric_space E] (f : α → E) {a b c : α}

def arclength (a b : α) : ℝ≥0∞ := evariation_on f (set.Icc a b)

lemma arclength_eq_supr (hab : a ≤ b) : arclength f a b =
  ⨆ (p : ℕ × {u : ℕ → α // monotone u ∧ (∀ i, u i ∈ set.Icc a b) ∧ u 0 = a ∧ a < u 1}),
    ∑ i in finset.range p.1.succ, edist (f $ p.2.1 (i+1)) (f $ p.2.1 i) :=
    /- using coercion `p.2 : ℕ → α` makes things a lot slower, strangely -/
begin
  refine le_antisymm (supr_le _)
    (supr_le $ λ p, le_supr_of_le ⟨p.1.succ, p.2.1, p.2.2.1, p.2.2.2.1⟩ le_rfl),
  rintro ⟨n, u, hu, huab⟩,
  by_cases h : ∀ m ≤ n, u m = a,
  { convert zero_le _, refine finset.sum_eq_zero (λ m hm, _),
    rw finset.mem_range at hm,
    simp only [subtype.coe_mk, h _ hm.le, h _ hm, edist_self] },
  push_neg at h,
  obtain ⟨m, ⟨hmn, hma⟩, hmin⟩ := nat.well_founded_lt.wf.has_min _ h,
  cases m,
  { refine le_supr_of_le ⟨n, _, monotone_nat_of_le_succ $ λ k, _, λ k, _, _⟩ _,
    { apply nat.rec, exacts [a, λ k _, u k] },
    { cases k, exacts [(huab 0).1, hu k.le_succ] },
    { cases k, exacts [set.left_mem_Icc.2 hab, huab k] },
    { exact ⟨rfl, (huab 0).1.lt_of_ne' hma⟩ },
    { rw [finset.sum_range_succ'], exact self_le_add_right _ _ } },
  have : ∀ k ≤ m, u k = a,
  { intros k hk, contrapose! hmin,
    exact ⟨_, ⟨hk.trans (m.le_succ.trans hmn), hmin⟩, hk.trans_lt m.lt_succ_self⟩ },
  refine le_supr_of_le ⟨(n - m).pred, λ k, u (m + k), hu.comp $ λ _ _ h, add_le_add_left h _,
    λ k, huab _, this m le_rfl, (huab _).1.lt_of_ne' hma⟩ _,
  dsimp only [subtype.coe_mk],
  conv_lhs { rw [← nat.sub_add_cancel (m.le_succ.trans hmn), add_comm, finset.sum_range_add] },
  simp_rw [add_assoc, nat.succ_pred_eq_of_pos (nat.sub_pos_of_lt hmn)],
  convert (zero_add _).le,
  refine finset.sum_eq_zero (λ k hk, _),
  rw finset.mem_range at hk,
  rw [this _ hk.le, this _ hk, edist_self],
end

lemma edist_le_arclength (hab : a ≤ b) : edist (f a) (f b) ≤ arclength f a b :=
evariation_on.edist_le f (set.left_mem_Icc.2 hab) (set.right_mem_Icc.2 hab)

lemma arclength_eq_zero (hab : b ≤ a) : arclength f a b = 0 :=
evariation_on.subsingleton f $
  λ x hx y hy, (hx.2.trans $ hab.trans hy.1).antisymm (hy.2.trans $ hab.trans hx.1)

lemma arclength_self (a : α) : arclength f a a = 0 := arclength_eq_zero f le_rfl

lemma arclength_anti (c : α) : antitone (λ x, arclength f x c) :=
λ a b hab, evariation_on.mono f $ λ x h, ⟨hab.trans h.1, h.2⟩

lemma arclength_mono (a : α) : monotone (arclength f a) :=
λ b c hbc, evariation_on.mono f $ λ x h, ⟨h.1, h.2.trans hbc⟩

lemma arclength_add (hab : a ≤ b) (hbc : b ≤ c) :
  arclength f a b + arclength f b c = arclength f a c :=
begin
  simp_rw arclength,
  convert evariation_on.Icc_add_Icc f hab hbc (set.mem_univ _); rw set.univ_inter,
end

lemma arclength_sum {n : ℕ} {u : ℕ → α} (hu : monotone u) :
  (finset.range n).sum (λ i, arclength f (u i) (u (i + 1))) = arclength f (u 0) (u n) :=
begin
  induction n with n ih,
  { rw [finset.sum_range_zero, arclength_self] },
  { rw [finset.sum_range_succ, ih, arclength_add f (hu $ zero_le n) (hu n.le_succ)] },
end

lemma arclength_sub₀ (hba : b ≤ a) : arclength f a b = arclength f a c - arclength f b c :=
by { rw [arclength_eq_zero f hba, eq_comm], exact tsub_eq_zero_of_le (arclength_anti f c hba) }

lemma arclength_sub' {a b c : α} (hbc : b ≤ c) (hac : arclength f b c ≠ ⊤) :
  arclength f a b = arclength f a c - arclength f b c :=
(le_total a b).elim
  (λ hab, ennreal.eq_sub_of_add_eq hac $ arclength_add f hab hbc)
  (arclength_sub₀ f)

lemma arclength_sub {a b c : α} (hbc : b ≤ c) (hac : arclength f a c ≠ ⊤) :
  arclength f a b = arclength f a c - arclength f b c :=
(le_total a b).elim
  (λ hab, arclength_sub' f hbc $ ne_top_of_le_ne_top hac $ arclength_anti f c hab)
  (arclength_sub₀ f)

open order_dual
lemma arclength_comp_of_dual (a b : α) :
   arclength (f ∘ of_dual) (to_dual b) (to_dual a) = arclength f a b :=
begin
  rw arclength,
  convert evariation_on.comp_of_dual f (set.Icc a b) using 2,
  ext, apply and_comm,
end

lemma arclength'_eq (b : α) :
  (λ x, arclength f x b) = arclength (f ∘ of_dual) (to_dual b) ∘ to_dual :=
funext $ λ a, (arclength_comp_of_dual f a b).symm

lemma arclength_proj_Icc {a b : α} (h : a ≤ b) :
  arclength (set.Icc_extend h (f ∘ coe)) a b = arclength f a b :=
evariation_on.eq_of_eq_on $ λ x, set.Icc_extend_of_mem h _

variables [topological_space α] [order_topology α] (hab : a < b)
  (hrect : arclength f a b ≠ ⊤) /- f is rectifiable on [a,b] -/

lemma continuous_on_Iic_arclength (h : b ≤ a) : continuous_on (arclength f a) (set.Iic b) :=
continuous_on_const.congr $ λ x hx, arclength_eq_zero f (trans hx h)

lemma continuous_on_Ici_arclength (h : b ≤ a) : continuous_on (λ x, arclength f x b) (set.Ici a) :=
continuous_on_const.congr $ λ x hx, arclength_eq_zero f (trans h hx)

include hab hrect

theorem continuous_right_self_arclength
  (hcont : continuous_within_at f (set.Ico a b) a) /- f is right continuous at a -/ :
  filter.tendsto (arclength f a) (nhds_within a (set.Ici a)) (nhds 0) :=
begin
  replace hcont := hcont.mono_of_mem (mem_nhds_within.2 ⟨_, is_open_Iio, hab, λ x, and.symm⟩),
  rw [ennreal.tendsto_nhds_zero],
  intros ε hε,
  by_cases hlab : arclength f a b = 0,
  { rw eventually_nhds_within_iff,
    refine filter.eventually_of_mem (Iio_mem_nhds hab) (λ x hb ha, _),
    exact ((arclength_mono f a $ le_of_lt hb).trans_eq hlab).trans (zero_le ε) },
  have hε2 : 0 < ε / 2 := ennreal.half_pos (ne_of_gt hε),
  rw arclength_eq_supr f hab.le at hrect hlab,
  obtain ⟨⟨n, u, hu, hmem, hea, hal⟩, hl⟩ := lt_supr_iff.1 (ennreal.sub_lt_self hrect hlab hε2.ne'),
  simp_rw [← arclength_eq_supr f hab.le, edist_comm] at hl,
  obtain ⟨c, hc, hcb⟩ := (mem_nhds_within_Ici_iff_exists_mem_Ioc_Ico_subset hab).1
    ((emetric.nhds_basis_eball.tendsto_right_iff).1 hcont _ hε2),
  apply (mem_nhds_within_Ici_iff_exists_mem_Ioc_Ico_subset hab).2,
  by_cases ∀ x, ¬ x ∈ set.Ioo a c,
  { refine ⟨c, hc, λ x hx, _⟩,
    obtain rfl | hxa := eq_or_ne a x,
    exacts [(arclength_self f a).trans_le (zero_le ε), (h x ⟨hx.1.lt_of_ne hxa, hx.2⟩).elim] },
  push_neg at h, obtain ⟨d, hd⟩ := h,
  let e := min (u 1) d,
  have hae : a < e := lt_min hal hd.1,
  have hec : e < c := (min_le_right _ d).trans_lt hd.2,
  refine ⟨e, ⟨hae, hec.le.trans hc.2⟩, λ x hx, (arclength_mono f a hx.2.le).trans _⟩,
  obtain rfl | hε := eq_or_ne ε ⊤, { exact le_top },
  have : ε / 2 ≠ ⊤ := λ h, (ennreal.div_eq_top.1 h).elim (λ h, two_ne_zero h.2) (λ h, hε h.1),
  /- extract div_ne_top ? -/
  by_contra' hac, apply (eq.refl $ arclength f a b).not_lt,
  calc  arclength f a b
      ≤ arclength f a b - ε/2 + ε/2 : tsub_le_iff_right.1 le_rfl
  ... < (∑ i in finset.range (n + 1), edist (f $ u i) (f $ u $ i+1)) + ε/2 :
        by { rw ennreal.add_lt_add_iff_right this, exact hl }
  ... ≤ (∑ i in finset.range n, edist (f $ u $ i+1) (f $ u $ i+1+1)) +
          (edist (f e) (f a) + edist (f e) (f $ u 1)) + ε/2 :
        add_le_add_right (by { rw [finset.sum_range_succ', hea],
          apply add_le_add_left (edist_triangle_left _ _ _) }) _
  ... ≤ (∑ i in finset.range n, arclength f (u $ i+1) (u $ i+1+1)) +
          (ε/2 + arclength f e (u 1)) + ε/2 :
        add_le_add_right
          (add_le_add (finset.sum_le_sum $ λ i _, edist_le_arclength f $ hu (i+1).le_succ) $
            add_le_add (le_of_lt $ hcb ⟨hae.le, hec⟩) $ edist_le_arclength f $ min_le_left _ d) _
  ... = _ + (ε + arclength f e (u 1)) : by rw [add_assoc, add_right_comm, ennreal.add_halves]
  ... ≤ _ + arclength f (u 0) (u 1) : by { rw [hea, ← arclength_add f hae.le $ min_le_left _ d],
          exact add_le_add_left (add_le_add_right hac.le _) _ }
  ... = ∑ i in finset.range (n + 1), arclength f (u i) (u $ i+1) : by rw finset.sum_range_succ'
  ... = arclength f (u 0) (u $ n+1) : arclength_sum f hu
  ... ≤ arclength f a b : by { rw hea, exact arclength_mono f a (hmem _).2 },
end

omit hrect

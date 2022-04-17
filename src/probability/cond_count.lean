import probability.conditional

noncomputable theory

open_locale probability_theory

open measure_theory measurable_space

namespace probability_theory

variables {α : Type*} [measurable_space α]

def cond_count (s : set α) : measure α := measure.count[|s]

-- move
lemma measure.count_empty : measure.count (∅ : set α) = 0 :=
by rw [measure.count_apply measurable_set.empty, tsum_empty]

variable [measurable_singleton_class α]

lemma measure.count_eq_zero {s : set α} (hs : s.finite) (hsc : measure.count s = 0) :
  s = ∅ :=
begin
  rw measure.count_apply_finite _ hs at hsc,
  simpa using hsc,
end

@[simp] lemma measure.count_eq_zero_iff {s : set α} (hs : s.finite) :
  measure.count s = 0 ↔ s = ∅ :=
⟨measure.count_eq_zero hs, λ h, h.symm ▸ measure.count_empty⟩

lemma measure.count_singleton (a : α) : measure.count ({a} : set α) = 1 :=
begin
  rw [measure.count_apply_finite ({a} : set α) (set.finite_singleton _), set.finite.to_finset],
  simp,
end

---------------------------------------------------------------------

lemma cond_count_is_probability_measure {s : set α} (hs : s.finite) (hs' : s.nonempty) :
  is_probability_measure (cond_count s) :=
{ measure_univ :=
  begin
    rw [cond_count, cond_apply _ hs.measurable_set, set.inter_univ, ennreal.inv_mul_cancel],
    { exact λ h, hs'.ne_empty $ measure.count_eq_zero hs h },
    { exact (measure.count_apply_lt_top.2 hs).ne }
  end }

lemma cond_prob_singleton (a : α) (t : set α) [decidable (a ∈ t)] :
  cond_count {a} t = if a ∈ t then 1 else 0 :=
begin
  rw [cond_count, cond_apply _ (measurable_set_singleton a), measure.count_singleton,
    ennreal.inv_one, one_mul],
  split_ifs,
  { rw [(by simpa : ({a} : set α) ∩ t = {a}), measure.count_singleton] },
  { rw [(by simpa : ({a} : set α) ∩ t = ∅), measure.count_empty] },
end

@[simp] lemma cond_count_empty_meas : (cond_count ∅ : measure α) = 0 :=
by { ext x, simp [cond_count] }

variables {s t u : set α}

@[simp] lemma cond_count_empty : cond_count s ∅ = 0 :=
by { ext x, simp [cond_count] }

lemma cond_count_cond (hs : s.finite) (hs' : s.nonempty) :
  cond_count s s = 1 :=
begin
  rw [cond_count, cond_apply _ hs.measurable_set, set.inter_self, ennreal.inv_mul_cancel],
  { exact λ h, hs'.ne_empty $ measure.count_eq_zero hs h },
  { exact (measure.count_apply_lt_top.2 hs).ne }
end

lemma cond_count_eq_one_of (hs : s.finite) (hs' : s.nonempty) (ht : s ⊆ t) :
  cond_count s t = 1 :=
begin
  haveI := cond_count_is_probability_measure hs hs',
  refine eq_of_le_of_not_lt prob_le_one _,
  rw [not_lt, ← cond_count_cond hs hs'],
  exact measure_mono ht,
end

lemma pred_true_of_cond_count_eq_one (hs : s.finite) (hs' : s.nonempty)
  (h : cond_count s t = 1) : s ⊆ t :=
begin
  rw [cond_count, cond_apply _ hs.measurable_set, mul_comm] at h,
  replace h := ennreal.eq_inv_of_mul_eq_one h,
  rw [inv_inv, measure.count_apply_finite _ hs,
    measure.count_apply_finite _ (hs.inter_of_left _), nat.cast_inj] at h,
  suffices : s ∩ t = s,
  { exact this ▸ λ x hx, hx.2 },
  rw ← @set.finite.to_finset_inj _ _ _ (hs.inter_of_left _) hs,
  exact finset.eq_of_subset_of_card_le
    (set.finite.to_finset_mono.2 (s.inter_subset_left t)) h.symm.le
end

lemma cond_count_eq_zero_iff (hs : s.finite) (hs' : s.nonempty) :
  cond_count s t = 0 ↔ s ∩ t = ∅ :=
by simp [cond_count, cond_apply _ hs.measurable_set, measure.count_apply_eq_top,
    set.not_infinite.2 hs, measure.count_apply_finite _ (hs.inter_of_left _)]

lemma cond_count_univ (hs : s.finite) (hs' : s.nonempty) :
  cond_count s set.univ = 1 :=
cond_count_eq_one_of hs hs' s.subset_univ

lemma cond_count_inter (hs : s.finite) (hs' : s.nonempty) :
  cond_count s (t ∩ u) = cond_count (s ∩ t) u * cond_count s t :=
begin
  by_cases hst : s ∩ t = ∅,
  { rw [hst, cond_count_empty_meas, measure.coe_zero, pi.zero_apply, zero_mul,
      cond_count_eq_zero_iff hs hs', ← set.inter_assoc, hst, set.empty_inter] },
  rw [cond_count, cond_count, cond_apply _ hs.measurable_set, cond_apply _ hs.measurable_set,
    cond_apply _ (hs.inter_of_left _).measurable_set,
    mul_comm _ (measure.count (s ∩ t)), ← mul_assoc, mul_comm _ (measure.count (s ∩ t)),
    ← mul_assoc, ennreal.mul_inv_cancel, one_mul, mul_comm, set.inter_assoc],
  { rwa ← measure.count_eq_zero_iff (hs.inter_of_left _) at hst },
  { exact (measure.count_apply_lt_top.2 $ hs.inter_of_left _).ne }
end

lemma cond_count_inter' (hs : s.finite) (hs' : s.nonempty) :
  cond_count s (t ∩ u) = cond_count (s ∩ u) t * cond_count s u :=
begin
  rw ← set.inter_comm,
  exact cond_count_inter hs hs',
end

lemma cond_count_union (hs : s.finite) (hs' : s.nonempty) (htu : disjoint t u) :
  cond_count s (t ∪ u) = cond_count s t + cond_count s u :=
begin
  rw [cond_count, cond_apply _ hs.measurable_set, cond_apply _ hs.measurable_set,
    cond_apply _ hs.measurable_set, set.inter_union_distrib_left, measure_union, mul_add],
  exacts [htu.mono inf_le_right inf_le_right, (hs.inter_of_left _).measurable_set],
end

lemma cond_count_compl (hs : s.finite) (hs' : s.nonempty) :
  cond_count s t + cond_count s tᶜ = 1 :=
begin
  rw [← cond_count_union hs hs' disjoint_compl_right, set.union_compl_self,
    (cond_count_is_probability_measure hs hs').measure_univ],
end

lemma Prob_disjoint_union {α : Type*} [decidable_eq α] (s t : finset α) (h₁ : disjoint s t)
  (P : α → Prop) [decidable_pred P] :
  Prob (s ∪ t) P =
    Prob s P * (s.card / (s ∪ t).card) + Prob t P * (t.card / (s ∪ t).card) :=
begin
  rcases s.eq_empty_or_nonempty with (rfl | hs),
  { rcases t.eq_empty_or_nonempty with (rfl | ht),
    { simp [Prob] },
    { rw [empty_union, card_empty, nat.cast_zero, zero_div, mul_zero, zero_add, div_self, mul_one],
      rw [← card_pos, nat.pos_iff_ne_zero] at ht,
      norm_cast at * } },
  { rcases t.eq_empty_or_nonempty with (rfl | ht),
    { rw [union_empty, card_empty, nat.cast_zero, zero_div, mul_zero, add_zero, div_self, mul_one],
      rw [←card_pos, nat.pos_iff_ne_zero] at hs,
      norm_cast at * },
    { rw [←card_pos, nat.pos_iff_ne_zero] at hs ht,
      rw [Prob, Prob, Prob, filter_union, card_disjoint_union h₁,
        card_disjoint_union (disjoint_filter_filter h₁), nat.cast_add, nat.cast_add, add_div,
        div_mul_div_cancel, div_mul_div_cancel];
      norm_cast at * } },
end

lemma conditional {α : Type*} (s : finset α) (P Q : α → Prop)
  [decidable_eq α] [decidable_pred P] [decidable_pred Q] :
  Prob s P = Prob (filter Q s) P * Prob s Q + Prob (filter (λ a, ¬Q a) s) P * Prob s (λ a, ¬Q a) :=
begin
  have : Prob s P = Prob s (λ x, P x ∧ Q x) + Prob s (λ x, P x ∧ ¬ Q x),
    rw [Prob, Prob, Prob, ← add_div],
    congr' 1,
    norm_cast,
    rw [← filter_filter, ← filter_filter, ← card_union_eq, filter_union_filter_neg_eq],
    rw [disjoint_iff_inter_eq_empty, filter_inter_filter_neg_eq],
  rw this,
  rw Prob_and,
  rw Prob_and,
end

end probability_theory

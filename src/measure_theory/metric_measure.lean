import topology.metric_space.metric_separated
import measure_theory.borel_space

open_locale nnreal ennreal topological_space big_operators

open emetric set function filter

noncomputable theory

namespace measure_theory

namespace outer_measure

variables {ι X Y : Type*} [emetric_space X] [emetric_space Y]

def is_metric (m : outer_measure X) : Prop :=
∀ (s t : set X), is_metric_separated s t → m (s ∪ t) = m s + m t

namespace is_metric

variables {m : outer_measure X}

lemma finset_Union_of_pairwise_separated (hm : is_metric m) {I : finset ι} {s : ι → set X}
  (hI : ∀ (i ∈ I) (j ∈ I), i ≠ j → is_metric_separated (s i) (s j)) :
  m (⋃ i ∈ I, s i) = ∑ i in I, m (s i) :=
begin
  classical,
  induction I using finset.induction_on with i I hiI ihI hI, { simp },
  simp only [finset.mem_insert] at hI,
  rw [finset.set_bUnion_insert, hm, ihI, finset.sum_insert hiI],
  exacts [λ i hi j hj hij, (hI i (or.inr hi) j (or.inr hj) hij),
    is_metric_separated.finset_Union_right
      (λ j hj, hI i (or.inl rfl) j (or.inr hj) (ne_of_mem_of_not_mem hj hiI).symm)]
end

lemma borel_le_caratheodory {m : outer_measure X} (hm : is_metric m) :
  borel X ≤ m.caratheodory :=
begin
  rw [borel_eq_generate_from_is_closed],
  refine measurable_space.generate_from_le (λ t ht, m.is_caratheodory_iff_le.2 $ λ s, _),
  set S : ℕ → set X := λ n, {x ∈ s | (↑n)⁻¹ ≤ inf_edist x t},
  have n0 : ∀ {n : ℕ}, (n⁻¹ : ℝ≥0∞) ≠ 0, from λ n, ennreal.inv_ne_zero.2 ennreal.coe_nat_ne_top,
  have Ssep : ∀ n, is_metric_separated (S n) t,
    from λ n, ⟨n⁻¹, n0, λ x hx y hy, hx.2.trans $ inf_edist_le_edist_of_mem hy⟩,
  have Ssep' : ∀ n, is_metric_separated (S n) (s ∩ t),
    from λ n, (Ssep n).mono subset.rfl (inter_subset_right _ _),
  have S_sub : ∀ n, S n ⊆ s \ t,
    from λ n, subset_inter (inter_subset_left _ _) (Ssep n).subset_compl_right,
  have hSs : ∀ n, m (s ∩ t) + m (S n) ≤ m s, from λ n,
  calc m (s ∩ t) + m (S n) = m (s ∩ t ∪ S n) :
    eq.symm $ hm _ _ $ (Ssep' n).symm
  ... ≤ m (s ∩ t ∪ s \ t)  : by { mono*, exact le_rfl }
  ... = m s : by rw [inter_union_diff],
  have Union_S : (⋃ n, S n) = s \ t,
  { refine subset.antisymm (Union_subset S_sub) _,
    rintro x ⟨hxs, hxt⟩,
    rw mem_iff_ind_edist_zero_of_closed ht at hxt,
    rcases ennreal.exists_inv_nat_lt hxt with ⟨n, hn⟩,
    exact mem_Union.2 ⟨n, hxs, hn.le⟩ },
  /- Now we have `∀ n, m (s ∩ t) + m (S n) ≤ m s` and we need to prove
  `m (s ∩ t) + m (⋃ n, S n) ≤ m s`. We can't pass to the limit because
  `m` is only an outer measure. -/
  by_cases htop : m (s \ t) = ∞,
  { rw [htop, ennreal.add_top, ← htop],
    exact m.mono (diff_subset _ _) },
  suffices : m (s \ t) ≤ ⨆ n, m (S n),
  calc m (s ∩ t) + m (s \ t) ≤ m (s ∩ t) + ⨆ n, m (S n) :
    add_le_add le_rfl this
  ... = ⨆ n, m (s ∩ t) + m (S n) : ennreal.add_supr
  ... ≤ m s : supr_le hSs,
  rw [← Union_S, m.Union_nat_of_monotone_of_tsum_ne_top], refl',
  { exact λ n x hx, ⟨hx.1, le_trans (ennreal.inv_le_inv.2 $
      ennreal.coe_nat_le_coe_nat.2 n.le_succ) hx.2⟩ },
  { rw [← tsum_even_add_odd ennreal.summable ennreal.summable, ennreal.add_ne_top],
    suffices : ∀ a, (∑' (k : ℕ), m (S (2 * k + 1 + a) \ S (2 * k + a))) ≠ ∞,
      from ⟨by simpa using this 0, by simpa using this 1⟩,
    refine λ r, ne_top_of_le_ne_top htop _,
    rw [← Union_S, ennreal.tsum_eq_supr_nat, supr_le_iff],
    intro n,
    rw [← hm.finset_Union_of_pairwise_separated],
    { exact m.mono (Union_subset $ λ i, Union_subset $ λ hi x hx, mem_Union.2 ⟨_, hx.1⟩) },
    suffices : ∀ i  j, i < j → is_metric_separated (S (2 * i + 1 + r)) (s \ S (2 * j + r)),
      from λ i _ j _ hij, hij.lt_or_lt.elim
        (λ h, (this i j h).mono (inter_subset_left _ _) (λ x hx, ⟨hx.1.1, hx.2⟩))
        (λ h, (this j i h).symm.mono  (λ x hx, ⟨hx.1.1, hx.2⟩) (inter_subset_left _ _)),
    intros i j hj,
    have A : ((↑(2 * j + r))⁻¹ : ℝ≥0∞) < (↑(2 * i + 1 + r))⁻¹,
      by { rw [ennreal.inv_lt_inv, ennreal.coe_nat_lt_coe_nat], linarith },
    refine ⟨(↑(2 * i + 1 + r))⁻¹ - (↑(2 * j + r))⁻¹, by simpa using A, λ x hx y hy, _⟩,
    have : inf_edist y t < (↑(2 * j + r))⁻¹, from not_le.1 (λ hle, hy.2 ⟨hy.1, hle⟩),
    rcases exists_edist_lt_of_inf_edist_lt this with ⟨z, hzt, hyz⟩,
    have hxz : (↑(2 * i + 1 + r))⁻¹ ≤ edist x z, from le_inf_edist.1 hx.2 _ hzt,
    apply ennreal.le_of_add_le_add_right (hyz.trans_le le_top),
    refine le_trans _ (edist_triangle _ _ _),
    refine (add_le_add le_rfl hyz.le).trans (eq.trans_le _ hxz),
    rw [ennreal.sub_add_cancel_of_le A.le] }
end

lemma le_caratheodory [measurable_space X] [borel_space X]
  {m : outer_measure X} (hm : is_metric m) :
  ‹_› ≤ m.caratheodory :=
by { rw @borel_space.measurable_eq X _ _, exact hm.borel_le_caratheodory }

end is_metric

def mk_metric'.pre (m : set X → ℝ≥0∞) (hm : m ∅ = 0) (r : ℝ≥0∞) :
  outer_measure X :=
outer_measure.of_function (λ s, ⨅ (h : diam s ≤ r), m s) (by simpa)

def mk_metric' (m : set X → ℝ≥0∞) (hm : m ∅ = 0) :
  outer_measure X :=
⨆ r > (0 : ℝ≥0∞), mk_metric'.pre m hm r

def mk_metric (m : ℝ≥0∞ → ℝ≥0∞) (hm : m 0 = 0) : outer_measure X :=
mk_metric' (λ s, m (diam s)) $ by rwa diam_empty

namespace mk_metric'

lemma mono_pre (m : set X → ℝ≥0∞) (hm : m ∅ = 0) {r r' : ℝ≥0∞} (h : r ≤ r') :
  pre m hm r' ≤ pre m hm r :=
begin
  refine le_of_function.2 (λ s, (of_function_le s).trans _),
  exact infi_le_infi2 (λ hr, ⟨hr.trans h, le_rfl⟩)
end

lemma tendsto_pre (m : set X → ℝ≥0∞) (hm : m ∅ = 0) (s : set X) :
  tendsto (λ r, pre m hm r s) (𝓝[Ioi 0] 0) (𝓝 $ mk_metric' m hm s) :=
begin
  rw [← map_coe_Ioi_at_bot, tendsto_map'_iff],
  simp only [mk_metric', outer_measure.supr_apply, supr_subtype'],
  exact tendsto_at_bot_supr (λ r r' hr, mono_pre _ _ hr _)
end

end mk_metric'

lemma mk_metric'_is_metric (m : set X → ℝ≥0∞) (hm : m ∅ = 0) :
  (mk_metric' m hm).is_metric :=
begin
  rintros s t ⟨r, r0, hr⟩,
  refine tendsto_nhds_unique_of_eventually_eq
    (mk_metric'.tendsto_pre _ _ _)
    ((mk_metric'.tendsto_pre _ _ _).add (mk_metric'.tendsto_pre _ _ _)) _,
  rw [← pos_iff_ne_zero] at r0,
  filter_upwards [Ioo_mem_nhds_within_Ioi ⟨le_rfl, r0⟩],
  rintro ε ⟨ε0, εr⟩,
  refine of_function_union_of_separated _,
  rintro u ⟨x, hxs, hxu⟩ ⟨y, hyt, hyu⟩,
  have : ε < diam u, from εr.trans_le ((hr x hxs y hyt).trans $ edist_le_diam_of_mem hxu hyu),
  simp [this.not_le]
end

lemma isomety_map_mk_metric (m : ℝ≥0∞ → ℝ≥0∞) (hm : m 0 = 0) {f : X → Y} (hf : isometry f) :
  map f (mk_metric m hm) = mk_metric m hm :=
begin
  
end

end outer_measure

#check outer_measure.to_measure

end measure_theory

import topology.metric_space.metric_separated
import measure_theory.borel_space

open_locale nnreal ennreal topological_space big_operators

open emetric set function filter

noncomputable theory

variables {ι X Y : Type*} [emetric_space X] [emetric_space Y]

namespace measure_theory

namespace outer_measure

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

/-- If `m` is a metric outer measure, then every Borel measurable set `t` is Caratheodory
measurable: for any (not necessarily measurable) set `s` we have `m (s ∩ t) + m (s \ t) = m s`. -/
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
  suffices : m (⋃ n, S n) ≤ ⨆ n, m (S n),
  calc m (s ∩ t) + m (s \ t) = m (s ∩ t) + m (⋃ n, S n) :
    by rw Union_S
  ... ≤ m (s ∩ t) + ⨆ n, m (S n) :
    add_le_add le_rfl this
  ... = ⨆ n, m (s ∩ t) + m (S n) : ennreal.add_supr
  ... ≤ m s : supr_le hSs,
  /- It suffices to show that `∑' k, m (S (k + 1) \ S k) ≠ ∞`. Indeed, if we have this,
  then for all `N` we have `m (⋃ n, S n) ≤ m (S N) + ∑' k, m (S (N + k + 1) \ S (N + k))`
  and the second term tends to zero, see `outer_measure.Union_nat_of_monotone_of_tsum_ne_top`
  for details. -/
  refine (m.Union_nat_of_monotone_of_tsum_ne_top _ _).le,
  { exact λ n x hx, ⟨hx.1, le_trans (ennreal.inv_le_inv.2 $
      ennreal.coe_nat_le_coe_nat.2 n.le_succ) hx.2⟩ },
  /- While the sets `S (k + 1) \ S k` are not pairwise metric separated, the sets in each
  subsequence `S (2 * k + 1) \ S (2 * k)` and `S (2 * k + 2) \ S (2 * k)` are metric separated,
  so `m` is additive on each of those sequences. -/
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

/-- Auxiliary definition for `outer_measure.mk_metric'`: given a function on sets
`m : set X → ℝ≥0∞`, returns the maximal outer measure `μ` such that `μ s ≤ m s`
for any set `s` of diamenter at most `r`.-/
def mk_metric'.pre (m : set X → ℝ≥0∞) (hm : m ∅ = 0) (r : ℝ≥0∞) :
  outer_measure X :=
induced_outer_measure (λ s (hs : diam s ≤ r), m s) (by { rw diam_empty, exact zero_le r }) hm

def mk_metric' (m : set X → ℝ≥0∞) (hm : m ∅ = 0) :
  outer_measure X :=
⨆ r > 0, mk_metric'.pre m hm r

def mk_metric (m : ℝ≥0∞ → ℝ≥0∞) (hm : m 0 = 0) : outer_measure X :=
mk_metric' (λ s, m (diam s)) $ by rwa diam_empty

namespace mk_metric'

variables {m : set X → ℝ≥0∞} {hm : m ∅ = 0} {r : ℝ≥0∞} {μ : outer_measure X} {s : set X}

lemma le_pre : μ ≤ pre m hm r ↔ ∀ s, diam s ≤ r → μ s ≤ m s :=
by simp only [pre, le_induced_outer_measure]

lemma pre_le (hs : diam s ≤ r) : pre m hm r s ≤ m s :=
(of_function_le _).trans $ infi_le _ hs

lemma mono_pre (m : set X → ℝ≥0∞) (hm : m ∅ = 0) {r r' : ℝ≥0∞} (h : r ≤ r') :
  pre m hm r' ≤ pre m hm r :=
le_pre.2 $ λ s hs, pre_le (hs.trans h)

lemma mono_pre_nat (m : set X → ℝ≥0∞) (hm : m ∅ = 0) :
  monotone (λ k : ℕ, pre m hm k⁻¹) :=
λ k l h, le_pre.2 $ λ s hs, pre_le (hs.trans $ by simpa)

lemma tendsto_pre (m : set X → ℝ≥0∞) (hm : m ∅ = 0) (s : set X) :
  tendsto (λ r, pre m hm r s) (𝓝[Ioi 0] 0) (𝓝 $ mk_metric' m hm s) :=
begin
  rw [← map_coe_Ioi_at_bot, tendsto_map'_iff],
  simp only [mk_metric', outer_measure.supr_apply, supr_subtype'],
  exact tendsto_at_bot_supr (λ r r' hr, _)
end

lemma tendsto_pre_nat (m : set X → ℝ≥0∞) (hm : m ∅ = 0) (s : set X) :
  tendsto (λ n : ℕ, pre m hm n⁻¹ s) at_top (𝓝 $ mk_metric' m hm s) :=
begin
  refine (tendsto_pre m hm s).comp (tendsto_inf.2 ⟨ennreal.tendsto_inv_nat_nhds_zero, _⟩),
  refine tendsto_principal.2 (eventually_of_forall $ λ n, _),
  simp
end

lemma eq_supr_nat (m : set X → ℝ≥0∞) (hm : m ∅ = 0) :
  mk_metric' m hm = ⨆ n : ℕ, mk_metric'.pre m hm n⁻¹ :=
begin
  ext1 s,
  rw supr_apply,
  refine tendsto_nhds_unique (mk_metric'.tendsto_pre_nat m hm s)
    (tendsto_at_top_supr $ λ k l hkl, mk_metric'.mono_pre_nat m hm hkl s)
end

lemma trim_pre [measurable_space X] [opens_measurable_space X]
  (m : ℝ≥0∞ → ℝ≥0∞) {hm : m (diam (∅ : set X)) = 0} (r : ℝ≥0∞) :
  (pre (λ s : set X, m (diam s)) hm r).trim =
    pre (λ s, m (diam s)) hm r :=
begin
  refine le_antisymm (le_pre.2 $ λ s hs, _) (le_trim _),
  rw trim_eq_infi,
  refine (infi_le_of_le (closure s) $ infi_le_of_le subset_closure $
    infi_le_of_le measurable_set_closure ((pre_le _).trans_eq _)),
  { rwa diam_closure },
  { rw diam_closure }
end

end mk_metric'

/-- An outer measure constructed using `outer_measure.mk_metric'` is a metric outer measure. -/
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
  exact infi_eq_top.2 (λ h, (this.not_le h).elim)
end

lemma mk_metric_mono_smul {m₁ m₂ : ℝ≥0∞ → ℝ≥0∞} (hm₁ : m₁ 0 = 0) (hm₂ : m₂ 0 = 0)
  {c : ℝ≥0∞} (hc : c ≠ ⊤) (h0 : c ≠ 0) (hle : m₁ ≤ᶠ[𝓝[Ioi 0] 0] c • m₂) :
  (mk_metric m₁ hm₁ : outer_measure X) ≤ c • mk_metric m₂ hm₂ :=
begin
  rcases (mem_nhds_within_Ioi_iff_exists_Ioo_subset' ennreal.zero_lt_one).1 hle with ⟨r, hr0, hr⟩,
  replace hr : ∀ r', r' < r → m₁ r' ≤ c • m₂ r',
    from λ r' hr', (zero_le r').eq_or_lt.elim (λ h, h ▸ by simp [hm₁, hm₂]) (λ h, hr ⟨h, hr'⟩),
  refine λ s, le_of_tendsto_of_tendsto (mk_metric'.tendsto_pre _ _ s)
    (ennreal.tendsto.const_mul (mk_metric'.tendsto_pre _ _ s) (or.inr hc))
    (mem_sets_of_superset (Ioo_mem_nhds_within_Ioi ⟨le_rfl, hr0⟩) (λ r' hr', _)),
  simp only [mem_set_of_eq, mk_metric'.pre, induced_outer_measure],
  rw [← smul_apply, smul_of_function hc],
  refine le_of_function.2 (λ t, (of_function_le _).trans _) _,
  simp only [smul_eq_mul, pi.smul_apply, extend, infi_eq_if],
  split_ifs with ht ht,
  { exact hr _ (ht.trans_lt hr'.2) },
  { simp [h0] }
end

lemma mk_metric_mono {m₁ m₂ : ℝ≥0∞ → ℝ≥0∞} (hm₁ : m₁ 0 = 0) (hm₂ : m₂ 0 = 0)
  (hle : m₁ ≤ᶠ[𝓝[Ioi 0] 0] m₂) :
  (mk_metric m₁ hm₁ : outer_measure X) ≤ mk_metric m₂ hm₂ :=
by { convert mk_metric_mono_smul hm₁ hm₂ ennreal.one_ne_top ennreal.zero_lt_one.ne' _; simp * }

lemma isometry_comap_mk_metric (m : ℝ≥0∞ → ℝ≥0∞) (hm : m 0 = 0)
  {f : X → Y} (hf : isometry f) (H : monotone m ∨ surjective f) :
  comap f (mk_metric m hm) = mk_metric m hm :=
begin
  simp only [mk_metric, mk_metric', mk_metric'.pre, induced_outer_measure, comap_supr],
  refine supr_congr id surjective_id (λ ε, supr_congr id surjective_id $ λ hε, _),
  rw comap_of_function _ (H.imp (λ h_mono, _) id),
  { congr' with s : 1,
    apply extend_congr; try { intros }; simp only [hf.ediam_image, id] },
  { exact λ s t hst, infi_le_infi2 (λ ht, ⟨(diam_mono hst).trans ht, h_mono (diam_mono hst)⟩) }
end

lemma isometry_map_mk_metric (m : ℝ≥0∞ → ℝ≥0∞) (hm : m 0 = 0)
  {f : X → Y} (hf : isometry f) (H : monotone m ∨ surjective f) :
  map f (mk_metric m hm) = restrict (range f) (mk_metric m hm) :=
by rw [← isometry_comap_mk_metric _ _ hf H, map_comap]

lemma isometric_comap_mk_metric (m : ℝ≥0∞ → ℝ≥0∞) (hm : m 0 = 0) (f : X ≃ᵢ Y) :
  comap f (mk_metric m hm) = mk_metric m hm :=
isometry_comap_mk_metric _ _ f.isometry (or.inr f.surjective)

lemma isometric_map_mk_metric (m : ℝ≥0∞ → ℝ≥0∞) (hm : m 0 = 0) (f : X ≃ᵢ Y) :
  map f (mk_metric m hm) = mk_metric m hm :=
by rw [← isometric_comap_mk_metric _ _ f, map_comap_of_surjective f.surjective]

lemma trim_mk_metric [measurable_space X] [borel_space X] (m : ℝ≥0∞ → ℝ≥0∞) (hm : m 0 = 0) :
  (mk_metric m hm : outer_measure X).trim = mk_metric m hm :=
by simp only [mk_metric, mk_metric'.eq_supr_nat, trim_supr, mk_metric'.trim_pre]

end outer_measure

namespace measure

variables [measurable_space X] [borel_space X]

def mk_metric' (m : set X → ℝ≥0∞) (hm : m ∅ = 0) : measure X :=
(outer_measure.mk_metric' m hm).to_measure (outer_measure.mk_metric'_is_metric _ _).le_caratheodory

def mk_metric (m : ℝ≥0∞ → ℝ≥0∞) (hm : m 0 = 0) : measure X :=
mk_metric' (λ s, m (diam s)) (by rwa diam_empty)

@[simp] lemma mk_metric'_to_outer_measure (m : set X → ℝ≥0∞) (hm : m ∅ = 0) :
  (mk_metric' m hm).to_outer_measure = (outer_measure.mk_metric' m hm).trim :=
rfl

@[simp] lemma mk_metric_to_outer_measure (m : ℝ≥0∞ → ℝ≥0∞) (hm : m 0 = 0) :
  (mk_metric m hm : measure X).to_outer_measure = outer_measure.mk_metric m hm :=
outer_measure.trim_mk_metric m hm

end measure

end measure_theory

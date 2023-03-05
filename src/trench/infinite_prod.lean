import algebra.order.complete_field
import analysis.specific_limits.basic
import trench.prod_le_sum
import to_mathlib.algebra.big_operators.basic
import to_mathlib.algebra.big_operators.order
import to_mathlib.algebra.hom.units
import to_mathlib.algebra.order.field.basic
import to_mathlib.data.finset.image
import to_mathlib.topology.algebra.order.monotone_convergence
import to_mathlib.topology.algebra.infinite_sum
import to_mathlib.topology.finset

noncomputable theory
open finset filter function classical
open_locale topology classical big_operators nnreal filter

variables {α : Type*} {β : Type*} {γ : Type*} {R K E : Type*}

section
variables [comm_monoid α] [topological_space α]
  [comm_semiring R] [topological_space R] [no_zero_divisors R] [nontrivial R]
  [field K] [topological_space K] [has_continuous_mul K] [has_continuous_inv₀ K]
  [conditionally_complete_linear_ordered_field E] [topological_space E] [has_continuous_mul E]
  -- [has_continuous_inv₀ E]

structure has_prod (f : β → α) (a : α) : Prop :=
(finite_not_unit : {b | ¬ is_unit (f b)}.finite)
(tendsto_units : ∃ x : αˣ, tendsto
  (λ s : finset β, ∏ b in (s.filter (λ i, is_unit (f i))), f b) at_top (𝓝 x))
(prod_eq : a = tendsto_units.some * ∏ b in finite_not_unit.to_finset, f b)

lemma has_prod_of_tendsto_of_finite [t2_space α] {f : β → α} {x : α}
  (h : tendsto (λ s : finset β, ∏ b in (s.filter (λ i, is_unit (f i))), f b) at_top (𝓝 x))
  (hx : is_unit x) (hs : {b | ¬ is_unit (f b)}.finite) :
  has_prod f (x * hs.to_finset.prod f) :=
begin
  refine ⟨hs, ⟨hx.unit, h⟩, _⟩,
  generalize_proofs H,
  rw tendsto_nhds_unique (Exists.some_spec H) h
end

lemma has_prod_of_tendsto_of_ne_zero [t2_space K] {f : β → K} {x : K}
  (h : tendsto (λ s : finset β, ∏ b in s.filter (λ i, f i ≠ 0), f b) at_top (𝓝 x))
  (hx : x ≠ 0) (hs : {b | f b = 0}.finite) :
  has_prod f (x * hs.to_finset.prod f) :=
begin
  simp_rw ←is_unit_iff_ne_zero at h hx,
  convert has_prod_of_tendsto_of_finite h hx (hs.subset _);
  simp [is_unit_iff_ne_zero]
end

lemma has_prod_of_tendsto_of_forall_is_unit [t2_space α] {f : β → α} {x : α}
  (h : tendsto (λ s : finset β, ∏ b in (s.filter (λ i, is_unit (f i))), f b) at_top (𝓝 x))
  (hx : is_unit x) (hs : ∀ b, is_unit (f b)) :
  has_prod f x :=
begin
  have : {b | ¬ is_unit (f b)} = ∅ := set.subset_empty_iff.mp (λ x hx, hx (hs _)),
  convert has_prod_of_tendsto_of_finite h hx (set.finite_empty.subset this.le),
  simp [this]
end

lemma has_prod_is_empty [t2_space α] [h : is_empty β] (f : β → α) :
  has_prod f 1 :=
begin
  refine has_prod_of_tendsto_of_forall_is_unit _ is_unit_one (λ x, h.elim x),
  have : ∀ (s : finset β), ∏ i in s, f i = 1,
  { intro s,
    suffices : s = ∅,
    { simp [this] },
    ext x,
    exact h.elim x },
  simp [this]
end

lemma has_prod_unique [t2_space α] [unique β] (f : β → α) :
  has_prod f (f default) :=
begin
  by_cases hf : is_unit (f default),
  { refine has_prod_of_tendsto_of_forall_is_unit _ hf _,
    { rw order_top.at_top_eq,
      simp only [prod_filter, tendsto_pure_left, hf, top_eq_univ, fintype.univ_of_subsingleton,
                 is_unit.unit_spec, prod_singleton, if_true, mem_nhds_iff, exists_prop,
                 forall_exists_index, and_imp],
      intros s t hst _ hm,
      exact hst hm },
    { intro b,
      simpa [subsingleton.elim b default] using hf } },
  { convert has_prod_of_tendsto_of_finite _ is_unit_one
      (set.finite_univ.subset (set.subset_univ _)),
    { simp [hf, filter_singleton],},
    { apply_instance },
    { have : ∀ (s : finset β), ∏ i in (s.filter (λ i, is_unit (f i))), f i = 1,
      { intro s,
        suffices : s.filter (λ i, is_unit (f i)) = ∅,
        { simp [this] },
        ext x,
        simp [hf, subsingleton.elim x default] },
      simp [this, tendsto_const_nhds] },
    { apply_instance } }
end


lemma has_prod_ratio {f : β → K} {a : K} (hf : has_prod f a) :
  tendsto (λ sb : finset β × β, (
      ∏ b in ((insert sb.2 sb.1).filter (λ i, is_unit (f i))), f b) /
      ∏ b in (sb.1.filter (λ i, is_unit (f i))), f b)
    (at_top.comap prod.fst) (𝓝 1) :=
begin
  obtain ⟨x, hx⟩ := hf.tendsto_units,
  rw ←div_self x.ne_zero,
  simp_rw div_eq_mul_inv,
  refine tendsto.mul _ ((tendsto_inv₀ x.ne_zero).comp _),
  { intros U hU,
    specialize hx hU,
    simp only [filter.mem_map, mem_comap, mem_at_top_sets, ge_iff_le, le_eq_subset,
               exists_prop] at hx ⊢,
    obtain ⟨s, hs⟩ := hx,
    simp only [set.mem_preimage] at hs,
    set s' : set (finset β) := (λ t, s ∪ t) '' set.univ with hs',
    refine ⟨s', ⟨s, _⟩, _⟩,
    { simp only [hs', set.image_univ, set.mem_range],
      intros t ht,
      refine ⟨t \ s, _⟩,
      simp [ht] },
    simp only [hs', set.image_univ],
    rintro ⟨t, b⟩,
    simp only [set.mem_preimage, set.mem_range, forall_exists_index],
    rintro x rfl,
    refine hs _ _,
    exact (subset_union_left _ _).trans (subset_insert _ _) },
  { refine (hx.comp tendsto_comap).congr _,
    simp }
end

lemma has_prod_ratio' {f : β → K} {a : K} (hf : has_prod f a) :
  tendsto (λ sb : finset β × finset β, (
      ∏ b in ((sb.1 ∪ sb.2).filter (λ i, is_unit (f i))), f b) /
      ∏ b in (sb.1.filter (λ i, is_unit (f i))), f b)
    at_top (𝓝 1) :=
begin
  obtain ⟨x, hx⟩ := hf.tendsto_units,
  rw ←div_self x.ne_zero,
  simp_rw div_eq_mul_inv,
  refine tendsto.mul _ ((tendsto_inv₀ x.ne_zero).comp _),
  { intros U hU,
    specialize hx hU,
    simp only [filter.mem_map, mem_at_top_sets, ge_iff_le, le_eq_subset, set.mem_preimage,
               prod.forall, prod.exists, prod.mk_le_mk, and_imp] at hx ⊢,
    obtain ⟨s, hs⟩ := hx,
    exact ⟨s, ∅, λ s' t' hs' ht', hs _ (hs'.trans (subset_union_left _ _))⟩ },
  { rw ←prod_at_top_at_top_eq,
    exact (hx.comp tendsto_fst) }
end

lemma has_prod.inv [t2_space K] {f : β → K} {x : K} (hf : has_prod f x) :
  has_prod (λ b, (f b)⁻¹) x⁻¹ :=
begin
  obtain ⟨h, ⟨x, h'⟩, h''⟩ := hf,
  simp only [←is_unit_inv_iff] at h { single_pass := tt},
  rw [←inv_inj, mul_inv_rev, mul_comm, ←prod_inv_distrib] at h'',
  convert has_prod_of_tendsto_of_finite _ x.is_unit.inv h,
  { convert h'',
    { generalize_proofs H,
      ext,
      exact tendsto_nhds_unique h' (Exists.some_spec H) },
    { simp } },
  { refine ((tendsto_inv₀ (units.ne_zero _)).comp h').congr _,
    intro,
    simp }
end

lemma has_prod_inv_iff [t2_space K] {f : β → K} {x : K} :
  has_prod f x⁻¹ ↔ has_prod (λ b, (f b)⁻¹) x :=
begin
  split;
  intro h;
  simpa using h.inv
end

def converges_prod (f : β → α) : Prop := ∃ (a : α), has_prod f a

lemma converges_prod_of_tendsto_of_subset_finite {f : β → α} {x : α} {s : set β}
  (h : tendsto (λ s : finset β, ∏ b in (s.filter (λ i, is_unit (f i))), f b) at_top (𝓝 x))
  (hx : is_unit x) (hs' : s.finite) (hs : {b | ¬ is_unit (f b)} ⊆ s) :
  converges_prod f :=
⟨_, hs'.subset hs, ⟨hx.unit, h⟩, rfl⟩

lemma converges_prod_of_tendsto_of_ne_zero_of_subset_finite {f : β → K} {x : K} {s : set β}
  (h : tendsto (λ s : finset β, ∏ b in (s.filter (λ i, f i ≠ 0)), f b) at_top (𝓝 x))
  (hx : x ≠ 0) (hs' : s.finite) (hs : {b | f b = 0} ⊆ s) :
  converges_prod f :=
begin
  simp_rw ←is_unit_iff_ne_zero at h hx,
  refine converges_prod_of_tendsto_of_subset_finite h hx hs' (subset_trans _ hs),
  simp [is_unit_iff_ne_zero],
end

lemma has_prod_zero_iff_converges_prod_and_exists_zero {f : β → R} :
  has_prod f 0 ↔ converges_prod f ∧ ∃ i, f i = 0 :=
begin
  split,
  { intro h,
    have := h.prod_eq,
    simp only [zero_eq_mul, false_or, prod_eq_zero_iff, units.ne_zero, set.finite.mem_to_finset,
               set.mem_set_of_eq, exists_prop] at this,
    obtain ⟨i, -, hi⟩ := this,
    exact ⟨⟨_, h⟩, i, hi⟩ },
  { rintro ⟨⟨a, hf⟩, i, h⟩,
    refine ⟨hf.finite_not_unit, hf.tendsto_units, _⟩,
    simp only [prod_eq_zero_iff, zero_eq_mul, units.ne_zero, set.finite.mem_to_finset,
               set.mem_set_of_eq, exists_prop, false_or],
    use i,
    simp [h] }
end

lemma function.injective.converges_prod_iff [t2_space α] {f : β → α} {g : γ → β} (hg : injective g)
  (hf : ∀ x ∉ set.range g, f x = 1) :
  converges_prod (f ∘ g) ↔ converges_prod f :=
begin
  have :
    filter.map (λ (s : finset γ), ∏ (i : γ) in s,
      (set.mul_indicator (set_of {i | is_unit (f i)}) f) (g i)) at_top =
    filter.map (λ (s : finset β), ∏ (i : β) in s,
      set.mul_indicator (set_of {i | is_unit (f i)}) f i) at_top,
  { refine injective.map_at_top_finset_prod_eq hg _,
    intros b hb,
    simp [hf _ hb] },
  split,
  { rintro ⟨a, h, ⟨y, h'⟩, h''⟩,
    rw tendsto at h',
    simp_rw [prod_mul_indicator_eq_prod_filter] at this,
    refine converges_prod_of_tendsto_of_subset_finite (h'.trans' this.ge) y.is_unit (h.image g) _,
    intros b hb,
    by_cases hbg : b ∈ set.range g,
    { obtain ⟨c, rfl⟩ := hbg,
      refine ⟨c, _⟩,
      simpa using hb },
    { simpa [hf _ hbg] using hb } },
  { rintro ⟨a, h, ⟨y, h'⟩, h''⟩,
    rw tendsto at h',
    simp_rw [prod_mul_indicator_eq_prod_filter] at this,
    refine converges_prod_of_tendsto_of_subset_finite (h'.trans' this.le) y.is_unit
      (h.preimage (hg.inj_on _)) _,
    intro,
    simp }
end

lemma converges_prod_subtype_iff_of_mul_support_subset [t2_space α] {f : β → α} {s : set β}
  (hf : mul_support f ⊆ s) :
  converges_prod (f ∘ coe : s → α) ↔ converges_prod f :=
subtype.coe_injective.converges_prod_iff $ by simpa using mul_support_subset_iff'.1 hf

lemma converges_prod_iff_mul_indicator [t2_space α] {f : β → α} {s : set β} :
  converges_prod (f ∘ coe : s → α) ↔ converges_prod (s.mul_indicator f) :=
begin
  rw [← set.mul_indicator_range_comp, subtype.range_coe],
  exact converges_prod_subtype_iff_of_mul_support_subset set.mul_support_mul_indicator_subset
end

lemma converges_prod_fintype [fintype β] (f : β → α) :
  converges_prod f :=
begin
  have : ∃ x : αˣ, tendsto
    (λ s : finset β, ∏ b in (s.filter (λ i, is_unit (f i))), f b) at_top (𝓝 x),
  { refine ⟨is_unit.unit (is_unit_prod_filter univ f), _⟩,
    simp [order_top.at_top_eq, tendsto_pure_left, mem_of_mem_nhds] { contextual := tt } },
  exact ⟨_, set.finite_univ.subset (set.subset_univ _), this, rfl⟩
end

@[simp] lemma converges_prod_subsingleton [subsingleton β] (f : β → α) :
  converges_prod f :=
begin
  casesI is_empty_or_nonempty β,
  { haveI : fintype β := fintype.of_is_empty,
    exact converges_prod_fintype _ },
  { inhabit β,
    haveI : fintype β := fintype.of_subsingleton default,
    exact converges_prod_fintype _ }
end

lemma converges_prod_inv_iff [t2_space K] {f : β → K} :
  converges_prod (λ b, (f b)⁻¹) ↔ converges_prod f :=
begin
  split; rintro ⟨x, h⟩;
  refine ⟨x⁻¹, _⟩;
  simpa using h.inv
end

lemma converges_prod.vanishing {f : β → K} (hf : converges_prod f) ⦃e : set K⦄
  (he : e ∈ 𝓝 (1 : K)) : ∃ s : finset β, ∀ t, disjoint t s → ∏ k in t, f k ∈ e :=
begin
  rcases hf with ⟨x, hf⟩,
  have := has_prod_ratio hf,
  have h := has_prod_ratio' hf he,
  simp only [filter.mem_map, mem_comap, mem_at_top_sets, ge_iff_le, le_eq_subset, exists_prop,
             set.preimage_subset_iff, set.mem_preimage, prod.forall] at h,
  simp only [prod.exists, prod.mk_le_mk, le_eq_subset, and_imp] at h,
  obtain ⟨s, t, h⟩ := h,
  refine ⟨s ∪ t ∪ hf.finite_not_unit.to_finset, λ u hdisj, _⟩,
  specialize h (s ∪ (t ∪ hf.finite_not_unit.to_finset)) (t ∪ u)
    (subset_union_left _ _) (subset_union_left _ _),
  simp_rw [union_assoc s, union_left_comm, ←union_assoc t, union_idempotent t, ←union_assoc s] at h,
  rw [filter_union, prod_union (disjoint_filter_filter hdisj.symm), is_unit.mul_div_cancel_left] at
    h,
  { suffices : ∀ b ∈ u, is_unit (f b),
    { rwa (filter_eq_self _).mpr this at h },
    intros b hb,
    have : {b} ≤ u := by simp only [hb, le_eq_subset, singleton_subset_iff],
    specialize hdisj this,
    simp only [union_assoc, le_eq_subset, singleton_subset_iff, mem_union, set.finite.mem_to_finset,
               set.mem_set_of_eq, bot_eq_empty, not_mem_empty] at hdisj,
    contrapose! hdisj,
    simp [hdisj] },
  { exact is_unit_prod_filter _ _ },
end

/-- The sequence of the factors in a convergent infinite product always tends to 1. -/
lemma converges_prod.tendsto_cofinite_one {f : β → K} (hf : converges_prod f) :
  tendsto f cofinite (𝓝 1) :=
begin
  intros e he,
  rw [filter.mem_map],
  rcases hf.vanishing he with ⟨s, hs⟩,
  refine s.eventually_cofinite_nmem.mono (λ x hx, _),
  simpa using hs {x} (disjoint_singleton_left.2 hx)
end

/-- The sequence of the factors `aₙ` in a convergent infinite product of
`1 + aₙ` always tends to 0. -/
lemma converges_prod.tendsto_cofinite_zero [has_continuous_add K]
  {f : β → K} (hf : converges_prod (λ b, 1 + f b)) :
  tendsto f cofinite (𝓝 0) :=
begin
  rw ←neg_add_self (1 : K),
  refine (hf.tendsto_cofinite_one.const_add (-1)).congr _,
  simp
end

-- TODO: specialize to `conditionally_complete_linear_ordered_field E`
/-- A product `∏ (1 + aₙ)` with positive terms `aₙ` is convergent iff the series `∑ aₙ` converges. -/
lemma converges_prod_one_add_iff_summable {f : β → ℝ} (hf : ∀ b, 0 ≤ f b) :
  converges_prod (λ b, 1 + f b) ↔ summable f :=
begin
  nontriviality β,
  have hu : ∀ b, is_unit (1 + f b),
  { intro b,
    simp [is_unit_iff_ne_zero, add_eq_zero_iff_neg_eq, (neg_one_lt_zero.trans_le (hf b)).ne] },
  have hs : ∀ s : finset β, (s.filter (λ b, is_unit (1 + f b))) = s,
  { intro,
    rw (filter_eq_self _).mpr _,
    intros b hb,
    exact hu b },
  suffices : bdd_above (set.range (λ s, ∏ a in s, (1 + f a))) ↔
    bdd_above (set.range (λ s, ∑ a in s, f a)),
  { split; intro h,
    -- the `is_lub_csupr` is where the proof is specialized to condtionally complete lattices
    { refine ⟨_, has_sum_of_is_lub_of_nonneg _ hf (is_lub_csupr (this.mp _))⟩,
      obtain ⟨x, h⟩ := h,
      obtain ⟨y, hy⟩ := h.tendsto_units,
      refine is_lub.bdd_above (is_lub_of_tendsto_at_top _ _ : is_lub _ x),
      { exact monotone_prod_of_one_le' (λ x, le_add_of_nonneg_right (hf _)) },
      { convert hy,
        { simp [hs] },
        { rw h.prod_eq,
          have he : h.finite_not_unit.to_finset = ∅,
          { ext x,
            simp [hu] },
          simp only [he, filter_congr_decidable, prod_empty, mul_one],
          refine tendsto_nhds_unique _ hy,
          generalize_proofs H,
          exact Exists.some_spec H } } },
    { have hb := (this.mpr
        (is_lub_of_tendsto_at_top (finset.sum_mono_set_of_nonneg hf) h.some_spec).bdd_above),
      have hunit : is_unit (⨆ (i : finset β), (λ (s : finset β), ∏ (a : β) in s, (1 + f a)) i),
      { rw is_unit_iff_ne_zero,
        refine ne_of_gt (lt_cSup_of_lt hb ⟨∅, _⟩ zero_lt_one),
        simp },
      refine converges_prod_of_tendsto_of_subset_finite _ hunit set.finite_empty
        (λ b hb, hb (hu b)),
      simp_rw [prod_filter, hu, if_true],
      exact tendsto_at_top_is_lub (monotone_prod_of_one_le' (λ x, le_add_of_nonneg_right (hf _)))
        (is_lub_csupr hb) } },
  split; intro h,
  { simp only [bdd_above_iff_exists_ge (1 : ℝ), set.mem_range, forall_exists_index,
      forall_apply_eq_imp_iff'] at h ⊢,
    obtain ⟨x, hx, hy⟩ := h,
    exact ⟨x, hx, λ s, (hy s).trans' (sum_le_prod_one_add_of_nonneg _ (λ _ _, hf _))⟩ },
  { have : summable f := ⟨_, has_sum_of_is_lub_of_nonneg _ hf (is_lub_csupr h)⟩,
    simp only [bdd_above_iff_exists_ge (0 : ℝ), set.mem_range, forall_exists_index,
      forall_apply_eq_imp_iff'] at h,
    simp only [bdd_above_iff_exists_ge (2 : ℝ), set.mem_range, forall_exists_index,
      forall_apply_eq_imp_iff'],
    obtain ⟨x, hx, hy⟩ := h,
    have hball : (set.Ioo (-1 : ℝ) 2⁻¹) ∈ 𝓝 (0 : ℝ),
    { exact Ioo_mem_nhds neg_one_lt_zero (inv_pos.mpr zero_lt_two) },
    obtain ⟨s, hs⟩ := this.vanishing hball,
    refine ⟨2 * ∏ b in s, (1 + f b), _, _⟩,
    { simp only [le_mul_iff_one_le_right, zero_lt_bit0, zero_lt_one],
      refine one_le_prod₀ (λ b hb, _),
      simp [hf b] },
    { intro t,
      rw ←sdiff_union_inter t s,
      rw prod_union (disjoint_sdiff_inter t s),
      refine mul_le_mul _ _ (zero_le_one.trans (one_le_prod₀ _)) zero_le_two,
      { refine (prod_one_add_le_one_add_sum_sum_pow _ _).trans _,
        { simp [hf] },
        -- `has_sum_geometric_two` is specialized to `ℝ`
        refine ge_of_tendsto has_sum_geometric_two _,
        rw eventually_at_top,
        refine ⟨range ((t \ s).card + 1), λ u hu, _⟩,
        refine (sum_le_sum_of_subset_of_nonneg hu _).trans (sum_le_sum _),
        { intros,
          exact pow_nonneg (sum_nonneg (λ _ _, hf _)) _ },
        { intros,
          refine pow_le_pow_of_le_left (sum_nonneg (λ _ _, hf _)) _ _,
          simpa using (hs (t \ s) disjoint_sdiff.symm).right.le } },
      { rw ←prod_sdiff (inter_subset_right t s),
        refine le_mul_of_one_le_of_le_of_nonneg _ le_rfl (zero_le_one.trans _);
        refine one_le_prod₀ _;
        simp [hf] },
      { simp [hf] } } }
end

-- should be factored out to be like `summable.add_compl`
lemma converges_prod_of_converges_prod_cofinite_subset {f : β → ℝ} (s : set β)
  (hs : sᶜ.finite) (h : converges_prod (λ x : s, f x)) :
  converges_prod f :=
begin
  classical,
  obtain ⟨x, h, ⟨y, h'⟩, h''⟩ := h,
  set t : set β := {b : β | is_unit (f b) ∧ b ∉ s} with ht,
  have htf : t.finite := hs.subset (λ _ h, h.right),
  refine converges_prod_of_tendsto_of_subset_finite _ (y.is_unit.mul
    (is_unit_prod htf.to_finset _ _)) (hs.union (h.image coe)) _,
  { exact f },
  { simp only [←prod_filter_mul_prod_filter_not _ (∈ s)] { single_pass := tt },
    refine tendsto.mul _ _,
    { convert tendsto_finset_map_subtype_at_top (∈ s)
        (λ t : finset β, ∏ b in t.filter (λ i, is_unit (f i)), f b) (𝓝 y) _ using 1,
      { simp [function.comp, filter_filter, and_comm] },
      { simpa [finset.filter_map, finset.prod_map] using h' } },
    { simp_rw prod_filter_mul_prod_filter_not,
      convert tendsto_finset_map_subtype_at_top (∉ s)
        (λ t : finset β, ∏ b in t.filter (λ i, is_unit (f i)), f b) (𝓝 _) _ using 1,
      { simp [function.comp, filter_filter, and_comm] },
      { haveI : fintype (sᶜ : set β) := hs.fintype,
        suffices : htf.to_finset.prod f =
          (λ t : finset (sᶜ : set β), ∏ b in (t.map (embedding.subtype (∉ s))).filter
            (λ i,  is_unit (f i)), f b) ⊤,
        { rw this,
          exact order_top.tendsto_at_top_nhds _ },
        refine prod_congr _ (λ _ _, rfl),
        ext,
        simp [and_comm] } } },
    { simp {contextual := tt} },
    { intro,
      simp [or.comm, classical.em] { contextual := tt } },
end

lemma converges_prod.converges_prod_subtype_of_one_le {f : β → ℝ} (h : converges_prod f)
  (p : β → Prop) (hf : ∀ b, is_unit (f b) → 1 ≤ f b) :
  converges_prod (λ b : subtype p, f b) :=
begin
  have hmap :
  (λ (s : finset (subtype p)), ∏ (b : subtype p) in filter (λ (i : subtype p),
      is_unit (f i)) s, f b) =
    λ s : finset (subtype p), ∏ b : β in filter (λ i : β, is_unit (f i))
      (s.map (embedding.subtype _)), f b,
  { ext,
    rw [←prod_subtype_map_embedding, filter_map],
    congr,
    exact λ _ _, rfl },
  have key : monotone (λ s : finset (subtype p), ∏ b in s.filter (λ i, is_unit (f i)), f b),
  { intros s t hst,
    refine prod_le_prod_of_subset_of_one_le₀ (monotone_filter_left _ hst) (prod_nonneg _) _,
    { simp only [mem_filter, and_imp, subtype.forall, subtype.coe_mk],
      exact λ _ _ _ hb, zero_le_one.trans (hf _ hb) },
    { simp only [mem_filter, not_and, and_imp, subtype.forall, subtype.coe_mk],
      exact λ _ _ _ hb _, hf _ hb } },
  obtain ⟨x, hx, ⟨x', hx'⟩, hx''⟩ := id h,
  rcases tendsto_of_monotone key with (hy|⟨y, hy⟩),
  { rw hmap at hy,
    have := tendsto_finset_map_subtype_at_top p ((λ s, finset.prod s f) ∘ finset.filter _)
      at_top hy,
    refine absurd (tendsto_at_top_mono _ this) (not_tendsto_at_top_of_tendsto_nhds hx'),
    intro s,
    refine prod_le_prod_of_subset_of_one_le₀ (monotone_filter_left _ (filter_subset _ _))
      (prod_nonneg _) _,
    { simp only [mem_filter, and_imp, subtype.forall, subtype.coe_mk],
      exact λ _ _ _ hb, zero_le_one.trans (hf _ hb) },
    { simp only [mem_filter, not_and, and_imp, subtype.forall, subtype.coe_mk],
      exact λ _ _ hb _, hf _ hb } },
  { refine converges_prod_of_tendsto_of_subset_finite hy _
      (hx.preimage (subtype.coe_injective.inj_on _)) _,
    { rw is_unit_iff_ne_zero,
      refine (zero_lt_one.trans_le (ge_of_tendsto' hy (λ s, one_le_prod₀ _))).ne',
      simp only [mem_filter, not_and, and_imp, subtype.forall, subtype.coe_mk],
      exact λ _ _ _ hb, hf _ hb  },
    { simp } }
end

lemma converges_prod.converges_prod_subtype_of_bounded_of_antitone {f : β → ℝ}
  (h : converges_prod f) (p : β → Prop) (hp : ∀ b, p b → (1 / 2) < f b)
  (hf' : antitone (λ s : finset (subtype p), ∏ b in s.filter (λ i, is_unit (f i)), f b)) :
  converges_prod (λ b : subtype p, f b) :=
begin
  have hmap :
  (λ (s : finset (subtype p)), ∏ (b : subtype p) in filter (λ (i : subtype p),
      is_unit (f i)) s, f b) =
    λ s : finset (subtype p), ∏ b : β in filter (λ i : β, is_unit (f i))
      (s.map (embedding.subtype _)), f b,
  { ext,
    rw [←prod_subtype_map_embedding, filter_map],
    congr,
    exact λ _ _, rfl },
  obtain ⟨x, hx, ⟨x', hx'⟩, hx''⟩ := id h,
  rcases tendsto_of_antitone hf' with (hy|⟨y, hy⟩),
  { rw hmap at hy,
    have h0 : tendsto (λ s : finset (subtype p), (0 : ℝ)) at_top (𝓝 0) := tendsto_const_nhds,
    refine absurd (tendsto_at_bot_mono _ hy)
      (not_tendsto_at_bot_of_tendsto_nhds h0),
    intro,
    refine prod_nonneg (λ b, _),
    simp only [mem_filter, finset.mem_map, embedding.coe_subtype, exists_prop, subtype.exists,
               subtype.coe_mk, exists_and_distrib_right, exists_eq_right, and_imp,
               forall_exists_index],
    exact λ hb _ _, (hp _ hb).le.trans' (div_nonneg zero_le_one zero_le_two) },
  refine converges_prod_of_tendsto_of_subset_finite hy _
    (hx.preimage (subtype.coe_injective.inj_on _)) _,
  { rw is_unit_iff_ne_zero,
    rintro rfl,
    refine x'.is_unit.ne_zero _,
    refine tendsto_nhds_unique hx' _,
    rw tendsto_at_top_nhds at hy ⊢,
    have : set.Ioo (1 / 2 : ℝ) 2 ∈ (𝓝 (1 : ℝ)),
    { exact Ioo_mem_nhds one_half_lt_one one_lt_two },
    obtain ⟨s, hs⟩ := h.vanishing this,
    set ps : ℝ := ∏ b in (s.subtype p).filter (λ i, is_unit (f i)), f b with hps,
    have pspos : 0 < ps,
    { refine prod_pos _,
      simp only [mem_filter, mem_subtype, and_imp, subtype.forall, subtype.coe_mk],
      exact λ _ hb _ _, (hp _ hb).trans' (div_pos zero_lt_one zero_lt_two) },
    obtain ⟨t, ht⟩ := hy (metric.ball 0 (ps / 2)) _ metric.is_open_ball,
    swap,
    { simp [half_pos pspos] },
    specialize ht (t ∪ s.subtype p) (subset_union_left _ _),
    rw [←sdiff_union_self_eq_union, filter_union,
        prod_union (disjoint_filter_filter sdiff_disjoint), ←hps] at ht,
    specialize hs (((t \ s.subtype p).map (embedding.subtype _)).filter (λ i, is_unit (f i))) _,
    { intros u htu hsu x hx,
      specialize htu hx,
      simp only [mem_filter, finset.mem_map, mem_sdiff, mem_subtype, embedding.coe_subtype,
                  exists_prop, subtype.exists, subtype.coe_mk, exists_and_distrib_right,
                  exists_eq_right] at htu,
      rcases htu with ⟨⟨_, htu⟩, _⟩,
      exact absurd (hsu hx) htu },
    replace hs : (1 / 2 : ℝ) < ∏ b in (t \ s.subtype p).filter (λ i, is_unit (f i)), f b,
    { simp only [finset.prod_map, embedding.coe_subtype, one_div, set.mem_Ioo] at hs,
      rw ←inv_eq_one_div,
      refine hs.left.trans_le (le_of_eq _),
      rw [←prod_subtype_map_embedding, filter_map],
      { congr },
      { exact λ _ _, rfl } },
    simp only [mem_ball_zero_iff, real.norm_eq_abs, abs_lt] at ht,
    have : ps / 2 < ps / 2,
    { calc ps / 2 = (1 / 2) * ps : by rw [div_eq_mul_one_div, mul_comm]
      ...   < (∏ b in (t \ s.subtype p).filter (λ i, is_unit (f i)), f b) * ps :
        (mul_lt_mul_right pspos).mpr hs
      ...   < ps / 2 : ht.right },
    exact absurd this (lt_irrefl _) },
  { simp }
end

/-- A product `∏ (1 - aₙ)` with positive terms `aₙ` is convergent iff the series `∑ aₙ` converges. -/
lemma converges_prod_one_sub_iff_summable {f : β → ℝ} (hf : ∀ b, 0 ≤ f b) :
  converges_prod (λ b, 1 - f b) ↔ summable f :=
begin
  have h2 : (2⁻¹ : ℝ) < 1 := by norm_num,
  have hapos : ∀ a : (f ⁻¹' set.Ioo (-2⁻¹) 2⁻¹ : set β), 0 < 1 - f a :=
    λ a, sub_pos_of_lt (a.prop.right.trans h2),
  have hapos' : ∀ a : (f ⁻¹' set.Ioo (-2⁻¹) 2⁻¹ : set β), 0 < 1 + f a :=
    λ a, add_pos_of_pos_of_nonneg zero_lt_one (hf _),
  have hapos2' : ∀ a : (f ⁻¹' set.Ioo (-2⁻¹) 2⁻¹ : set β), 0 < 1 + 2 * f a :=
    λ a, add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg zero_le_two (hf _)),
  have hrearr : ∀ g : β → ℝ, (λ s : finset (f ⁻¹' set.Ioo (-2⁻¹) 2⁻¹ : set β),
      ∏ b in s.filter (λ i, is_unit (g i)), g b) =
      ((λ s : finset (f ⁻¹' set.Ioo (-2⁻¹) 2⁻¹ : set β),
        ∏ b in s, (g b)) ∘ finset.filter (λ i, is_unit (g i))),
  { intro g,
    funext,
    simp only [function.comp] },
  have hmono : monotone (λ s : finset (f ⁻¹' set.Ioo (-2⁻¹) 2⁻¹ : set β),
    ∏ b in s.filter (λ i, is_unit (1 + f i)), (1 + f b)),
  { simp_rw hrearr (λ i, 1 + f i),
    refine monotone.comp (monotone_prod_of_one_le' _) (monotone_filter_left _),
    simp [hf] },
  have hanti : antitone (λ s : finset (f ⁻¹' set.Ioo (-2⁻¹) 2⁻¹ : set β),
    ∏ b in s.filter (λ i, is_unit (1 - f i)), (1 - f b)),
  { simp_rw hrearr (λ i, 1 - f i),
    refine antitone.comp_monotone (antitone_prod_of_le_one' _ (λ _, (hapos _).le))
      (monotone_filter_left _),
    simp [hf] },
  clear hrearr,
  by_cases hlim : tendsto f cofinite (𝓝 0),
  { rw tendsto_nhds at hlim,
    specialize hlim (set.Ioo (-2⁻¹ : ℝ) 2⁻¹) is_open_Ioo _,
    { simp },
    split,
    { intros hs,
      rw ←converges_prod_one_add_iff_summable hf,
      refine converges_prod_of_converges_prod_cofinite_subset _ hlim _,
      have npos : ∀ t : finset (f ⁻¹' set.Ioo (-2⁻¹) 2⁻¹ : set β),
        (0 : ℝ) < ∏ b in t.filter (λ i, is_unit (1 - f i)), (1 - f b),
      { intro,
        refine prod_pos _,
        simp only [set.mem_preimage, set.mem_Ioo, mem_filter, sub_pos, and_imp,
                    set_coe.forall, subtype.coe_mk],
        intros _ hb _ _,
        exact hb.right.trans h2 },
      rcases tendsto_of_monotone hmono with (hy|⟨y, hy⟩),
      { obtain ⟨_, -, ⟨x', hx'⟩, -⟩ := hs.converges_prod_subtype_of_bounded_of_antitone
          (∈ f ⁻¹' set.Ioo (-2⁻¹) 2⁻¹) _ hanti,
        { rw tendsto_at_top_at_top_iff_of_monotone hmono at hy,
          obtain ⟨t, ht⟩ := hy (x'⁻¹ + 1),
          refine absurd (lt_add_of_le_of_pos _ zero_lt_one) ht.not_lt,
          have key : (∏ b in t.filter (λ i, is_unit (1 - f i)), (1 - f b))⁻¹ ≤ x'⁻¹,
          { rw inv_le_inv,
            { exact hanti.le_of_tendsto hx' t },
            { exact npos t },
            { refine lt_of_le_of_ne _ x'.is_unit.ne_zero.symm,
              refine ge_of_tendsto' hx' (λ s, prod_nonneg _),
              simp only [set.mem_preimage, set.mem_Ioo, filter_congr_decidable, mem_filter,
                         sub_nonneg, and_imp, subtype.forall, subtype.coe_mk],
              exact λ _ hb _ _, hb.right.le.trans h2.le } },
          refine key.trans' _,
          simp only [is_unit_iff_ne_zero] at npos ⊢,
          clear ht key,
          induction t using finset.cons_induction_on with a t ha IH,
          { simp },
          { simp only [ha, filter_insert, (hapos a).ne', (hapos' a).ne', cons_eq_insert,
                      if_true, prod_insert, mem_filter, false_and, not_false_iff, mul_inv_rev,
                      ne.def],
            rw mul_comm,
            exact mul_le_mul IH (one_add_le_inv_one_sub_of_lt_one (a.prop.right.trans h2))
              (hapos' a).le (inv_nonneg_of_nonneg (npos _).le) } },
        { simp only [set.mem_preimage, set.mem_Ioo, one_div, and_imp],
          intros b hb hb',
          rw [lt_sub_comm, inv_eq_one_div, sub_half, ←inv_eq_one_div],
          exact hb' } },
      simp_rw is_unit_iff_ne_zero at hy hmono,
      refine converges_prod_of_tendsto_of_ne_zero_of_subset_finite hy _ set.finite_empty _,
      { rintro rfl,
        have hbdd := (is_lub_of_tendsto_at_top hmono hy),
        refine absurd _ (zero_lt_one : (0 : ℝ) < 1).not_le,
        rw ←hbdd.csupr_eq,
        refine le_csupr_of_le hbdd.bdd_above ∅ _,
        simp },
      { intro b,
        simp only [set.mem_set_of_eq, set.mem_empty_iff_false, is_unit_iff_ne_zero, not_not],
        intro H,
        simpa [zero_lt_one.not_le] using H.le.trans (hf b) } },
    { intros hs,
      refine converges_prod_of_converges_prod_cofinite_subset _ hlim _,
      replace hs : summable (λ i, 2 * f i),
      { simp_rw ←smul_eq_mul,
        exact hs.const_smul _ },
      rw ←converges_prod_one_add_iff_summable at hs, swap,
      { exact λ _, mul_nonneg zero_le_two (hf _) },
      rcases tendsto_of_antitone hanti with (hy|⟨y, hy⟩),
      { rw tendsto_at_top_at_bot_iff_of_antitone hanti at hy,
        obtain ⟨t, ht⟩ := hy (-1 : ℝ),
        simp only at ht,
        refine absurd (neg_one_lt_zero.trans_le _) ht.not_lt,
        exact prod_nonneg (λ _ _, (hapos _).le) },
      simp_rw is_unit_iff_ne_zero at hy hmono,
      refine converges_prod_of_tendsto_of_ne_zero_of_subset_finite hy _ set.finite_empty _,
      { obtain ⟨_, -, ⟨x', hx'⟩, -⟩ := hs.converges_prod_subtype_of_one_le
            (∈ f ⁻¹' set.Ioo (-2⁻¹) 2⁻¹) _, swap,
        { intros,
          simpa using hf _ },
        have xpos : (0 : ℝ) < x',
        { refine lt_of_le_of_ne (ge_of_tendsto' hx' (λ t, _)) x'.ne_zero.symm,
          exact prod_nonneg (λ b _, add_nonneg zero_le_one (mul_nonneg zero_le_two (hf _))) },
        refine ((inv_pos_of_pos xpos).trans_le _).ne',
        refine le_of_tendsto_of_tendsto' ((real.tendsto_inv xpos.ne').comp hx') hy (λ t, _),
        simp only [is_unit_iff_ne_zero],
        induction t using finset.cons_induction_on with a t ha IH,
        { simp only [comp_app, filter_true_of_mem, not_mem_empty, is_empty.forall_iff,
                     implies_true_iff, prod_empty, inv_one] },
        { suffices : (∏ x in filter (λ i, (1 + 2 * f (↑i : β)) ≠ 0) t, (1 + 2 * f (x : β)))⁻¹ *
            (1 + 2 * f a)⁻¹ ≤
            (1 - f a) * ∏ x in filter (λ i, (1 - f (↑i : β)) ≠ 0) t, (1 - f (x : β)),
          { simpa [ha, filter_insert, (hapos a).ne', (hapos2' a).ne'] using this },
          rw mul_comm,
          refine mul_le_mul _ IH (inv_nonneg_of_nonneg (prod_nonneg (λ _ _, (hapos2' _).le)))
            (hapos _).le,
          refine inv_one_add_two_mul_le_one_sub_of_nonneg_of_le_half (hf _) _,
          rw ←inv_eq_one_div,
          exact a.prop.right.le } },
      { rintro ⟨b, hb⟩,
        simp only [set.mem_preimage, set.mem_Ioo] at hb,
        simp only [is_unit_iff_ne_zero, not_not, set.mem_set_of_eq, subtype.coe_mk,
                   set.mem_empty_iff_false, sub_eq_zero],
        intro H,
        exact hb.right.not_le (H.le.trans' (inv_lt_one one_lt_two).le) } } },
  { split; intro h,
    { rw ←sub_self (1 : ℝ) at hlim,
      refine absurd ((h.tendsto_cofinite_one.const_sub _).congr _) hlim,
      simp },
    { exact absurd h.tendsto_cofinite_zero hlim } }
end

end

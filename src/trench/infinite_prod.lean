import analysis.specific_limits.basic
import topology.algebra.infinite_sum
import trench.prod_le_sum
import to_mathlib.algebra.hom.units

noncomputable theory
open finset filter function classical
open_locale topology classical big_operators nnreal filter

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

section
variables [comm_monoid α] [topological_space α]

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

lemma has_prod_of_tendsto_of_forall_is_unit [t2_space α] {f : β → α} {x : α}
  (h : tendsto (λ s : finset β, ∏ b in (s.filter (λ i, is_unit (f i))), f b) at_top (𝓝 x))
  (hx : is_unit x) (hs : ∀ b, is_unit (f b)) :
  has_prod f x :=
begin
  have : {b | ¬ is_unit (f b)} = ∅ := set.subset_empty_iff.mp (λ x hx, hx (hs _)),
  convert has_prod_of_tendsto_of_finite h hx (set.finite_empty.subset this.le),
  simp [this]
end

def converges_prod (f : β → α) : Prop := ∃ (a : α), has_prod f a

lemma converges_prod_of_tendsto_of_subset_finite {f : β → α} {x : α} {s : set β}
  (h : tendsto (λ s : finset β, ∏ b in (s.filter (λ i, is_unit (f i))), f b) at_top (𝓝 x))
  (hx : is_unit x) (hs' : s.finite) (hs : {b | ¬ is_unit (f b)} ⊆ s) :
  converges_prod f :=
⟨_, hs'.subset hs, ⟨hx.unit, h⟩, rfl⟩

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

lemma has_prod_zero_iff_converges_prod_and_exists_zero {f : β → ℝ} :
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

lemma has_prod_ratio {f : β → ℝ} {a : ℝ} (hf : has_prod f a) :
  tendsto (λ sb : finset β × β, (
      ∏ b in ((insert sb.2 sb.1).filter (λ i, is_unit (f i))), f b) /
      ∏ b in (sb.1.filter (λ i, is_unit (f i))), f b)
    (at_top.comap prod.fst) (𝓝 1) :=
begin
  obtain ⟨x, hx⟩ := hf.tendsto_units,
  rw ←div_self x.ne_zero,
  simp_rw div_eq_mul_inv,
  refine tendsto.mul _ ((real.tendsto_inv x.ne_zero).comp _),
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

lemma has_prod_ratio' {f : β → ℝ} {a : ℝ} (hf : has_prod f a) :
  tendsto (λ sb : finset β × finset β, (
      ∏ b in ((sb.1 ∪ sb.2).filter (λ i, is_unit (f i))), f b) /
      ∏ b in (sb.1.filter (λ i, is_unit (f i))), f b)
    at_top (𝓝 1) :=
begin
  obtain ⟨x, hx⟩ := hf.tendsto_units,
  rw ←div_self x.ne_zero,
  simp_rw div_eq_mul_inv,
  refine tendsto.mul _ ((real.tendsto_inv x.ne_zero).comp _),
  { intros U hU,
    specialize hx hU,
    simp only [filter.mem_map, mem_at_top_sets, ge_iff_le, le_eq_subset, set.mem_preimage,
               prod.forall, prod.exists, prod.mk_le_mk, and_imp] at hx ⊢,
    obtain ⟨s, hs⟩ := hx,
    exact ⟨s, ∅, λ s' t' hs' ht', hs _ (hs'.trans (subset_union_left _ _))⟩ },
  { rw ←prod_at_top_at_top_eq,
    exact (hx.comp tendsto_fst) }
end

@[to_additive]
def prod_induction [comm_monoid γ] {C : γ → Prop} (s : finset β) (f : β → γ) (h1 : C 1)
  (hmul : ∀ (a ∈ s) b, C b → C (f a * b)) : C (s.prod f) :=
begin
  induction s using finset.cons_induction_on with a s ha IH,
  { exact h1 },
  { rw prod_cons ha,
    refine hmul _ (mem_cons_self _ _) _ (IH _),
    intros a ha,
    exact hmul _ (mem_cons.mpr (or.inr ha)) }
end

@[to_additive]
lemma is_unit_prod [comm_monoid γ] (s : finset β) (f : β → γ) (hs : ∀ b ∈ s, is_unit (f b)) :
  is_unit (s.prod f) :=
prod_induction _ _ is_unit_one (λ a ha b hb, (hs _ ha).mul hb)

attribute [to_additive] is_unit.decidable

@[to_additive]
lemma is_unit_prod_filter [comm_monoid γ] (s : finset β) (f : β → γ) :
  is_unit ((s.filter (λ b, is_unit (f b))).prod f) :=
is_unit_prod _ _ (by simp)

lemma is_unit.inf [monoid γ] [linear_order γ] {x y : γ} (hx : is_unit x) (hy : is_unit y) :
  is_unit (x ⊓ y) :=
begin
  cases le_total x y with h;
  simp [h, hx, hy]
end

lemma is_unit.sup [monoid γ] [linear_order γ] {x y : γ} (hx : is_unit x) (hy : is_unit y) :
  is_unit (x ⊔ y) :=
@is_unit.inf γᵒᵈ _ _ _ _  hx hy

-- lemma is_unit_supr [monoid γ] [conditionally_complete_lattice γ] {f : β → γ}
--   (hf : ∀ i, is_unit (f i)) :
--   is_unit (⨆ i, f i) :=
-- begin
--   refine (is_unit.mem_submonoid_iff (⨆ (i : β), f i)).mp _,
-- end

lemma converges_prod_fintype [fintype β] (f : β → α) :
  converges_prod f :=
begin
  have : ∃ x : αˣ, tendsto
    (λ s : finset β, ∏ b in (s.filter (λ i, is_unit (f i))), f b) at_top (𝓝 x),
  { refine ⟨is_unit.unit (is_unit_prod_filter univ f), _⟩,
    simp [order_top.at_top_eq, tendsto_pure_left, mem_of_mem_nhds] { contextual := tt } },
  exact ⟨_, set.finite_univ.subset (set.subset_univ _), this, rfl⟩
end

lemma summable_fintype [add_comm_monoid γ] [topological_space γ] [fintype β] (f : β → γ) :
  summable f :=
begin
  refine ⟨univ.sum f, _⟩,
  simp [has_sum, order_top.at_top_eq, tendsto_pure_left, mem_of_mem_nhds] { contextual := tt }
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

@[simp] lemma summable_subsingleton [add_comm_monoid γ] [topological_space γ] [subsingleton β]
  (f : β → γ) : summable f :=
begin
  casesI is_empty_or_nonempty β,
  { haveI : fintype β := fintype.of_is_empty,
    exact summable_fintype _ },
  { inhabit β,
    haveI : fintype β := fintype.of_subsingleton default,
    exact summable_fintype _ }
end

lemma converges_prod.vanishing {f : β → ℝ} (hf : converges_prod f) ⦃e : set ℝ⦄
  (he : e ∈ 𝓝 (1 : ℝ)) : ∃ s : finset β, ∀ t, disjoint t s → ∏ k in t, f k ∈ e :=
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
lemma converges_prod.tendsto_cofinite_one {f : β → ℝ} (hf : converges_prod f) :
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
lemma converges_prod.tendsto_cofinite_zero {f : β → ℝ} (hf : converges_prod (λ b, 1 + f b)) :
  tendsto f cofinite (𝓝 0) :=
begin
  rw ←neg_add_self (1 : ℝ),
  refine (hf.tendsto_cofinite_one.const_add (-1)).congr _,
  simp
end

@[to_additive sum_le_sum_of_subset_of_nonpos]
lemma prod_le_prod_of_subset_of_le_one' [ordered_comm_monoid γ] {s t : finset β} {f : β → γ}
  (h : s ⊆ t) (hf : ∀ i ∈ t, i ∉ s → f i ≤ 1) :
  ∏ i in t, f i ≤ ∏ i in s, f i :=
by classical;
calc ∏ i in t, f i = ∏ i in t \ s ∪ s, f i    : by rw [sdiff_union_of_subset h]
  ... = (∏ i in t \ s, f i) * (∏ i in s, f i) : (prod_union sdiff_disjoint)
  ... ≤ ∏ i in s, f i                         : mul_le_of_le_one_left' $
    prod_le_one' $ by simpa only [mem_sdiff, and_imp]

lemma prod_anti_set_of_le_one [ordered_comm_monoid γ] {f : β → γ} (hf : ∀ b, f b ≤ 1) :
  antitone (λ s, ∏ b in s, f b) :=
λ _ _ hst, prod_le_prod_of_subset_of_le_one' hst (λ _ _ _, hf _)

lemma one_le_prod₀ [ordered_comm_semiring γ] {s : finset β} {f : β → γ}
  (h : ∀i ∈ s, 1 ≤ f i) : 1 ≤ (∏ i in s, f i) :=
prod_induction _ _ le_rfl (λ x hx y hy,
  le_mul_of_le_mul_of_nonneg_left (by simpa using h _ hx) hy (zero_le_one.trans (h _ hx)))

lemma prod_le_one₀ [ordered_comm_semiring γ] {s : finset β} {f : β → γ}
  (h : ∀i ∈ s, f i ≤ 1) (h' : ∀i ∈ s, 0 ≤ f i) : ∏ i in s, f i ≤ 1 :=
begin
  induction s using finset.cons_induction_on with a s ha IH,
  { simp },
  simp only [ha, cons_eq_insert, prod_insert, not_false_iff],
  refine mul_le_one (h _ (mem_cons_self _ _)) (prod_nonneg _) (IH _ _);
  { intros,
    apply h' <|> apply h,
    simp [*] }
end

lemma monotone_prod_of_one_le' [ordered_comm_semiring γ] {f : β → γ} (hf : ∀ b, 1 ≤ f b) :
  monotone (λ s, ∏ b in s, f b) :=
begin
  intros s t hst,
  simp only [←prod_sdiff hst],
  refine le_mul_of_one_le_left (zero_le_one.trans _) _;
  exact one_le_prod₀ (λ _ _, hf _)
end

lemma antitone_prod_of_le_one' [ordered_comm_semiring γ] {f : β → γ} (hf : ∀ b, f b ≤ 1)
  (hf' : ∀ b, 0 ≤ f b) :
  antitone (λ s, ∏ b in s, f b) :=
begin
  intros s t hst,
  simp only [←prod_sdiff hst],
  refine mul_le_of_le_one_left (prod_nonneg (λ _ _, hf' _)) _,
  refine prod_le_one₀ (λ _ _, hf _) (λ _ _, hf' _)
end

lemma sum_le_prod_one_add_of_nonneg [linear_ordered_comm_semiring γ]
  (s : finset β) {f : β → γ} (hf : ∀ b ∈ s, 0 ≤ f b) :
  ∑ i in s, f i ≤ ∏ (a : β) in s, (1 + f a) :=
begin
  induction s using finset.cons_induction_on with a s ha IH,
  { simp },
  simp only [ha, add_mul, cons_eq_insert, sum_insert, not_false_iff, prod_insert, one_mul],
  rw [add_comm],
  refine add_le_add (IH (λ b hb, hf _ (mem_cons.mpr (or.inr hb)))) _,
  refine le_mul_of_one_le_right (hf _ (mem_cons_self _ _)) (one_le_prod₀ (λ b hb, _)),
  simp [hf _ (mem_cons.mpr (or.inr hb))]
end

lemma prod_le_prod_of_nonneg [ordered_comm_semiring γ] (s : finset β) {f g : β → γ}
  (h : ∀ b ∈ s, f b ≤ g b) (h' : ∀ b ∈ s, 0 ≤ f b) :
  ∏ i in s, f i ≤ ∏ i in s, g i :=
begin
  induction s using finset.cons_induction_on with a s ha IH,
  { simp },
  simp only [ha, cons_eq_insert, prod_insert, not_false_iff],
  refine mul_le_mul (h _ (mem_cons_self _ _)) (IH _ _) (prod_nonneg _) ((h' _ _).trans (h _ _)),
  { intros b hb,
    exact h _ (mem_cons.mpr (or.inr hb)) },
  { intros b hb,
    exact h' _ (mem_cons.mpr (or.inr hb)) },
  { intros b hb,
    exact h' _ (mem_cons.mpr (or.inr hb)) },
  { simp },
  { simp }
end

/-- A product `∏ (1 + aₙ)` with positive terms `aₙ` is convergent iff the series `∑ aₙ` converges. -/
lemma converges_prod_one_add_iff_summable {f : β → ℝ} (hf : ∀ b, 0 ≤ f b) :
  converges_prod (λ b, 1 + f b) ↔ summable f :=
begin
  nontriviality β,
  have hu : ∀ b, is_unit (1 + f b),
  { intro b,
    simp [is_unit_iff_ne_zero, add_eq_zero_iff_neg_eq,
          (neg_one_lt_zero.trans_le (hf b)).ne] },
  have hs : ∀ s : finset β, (s.filter (λ b, is_unit (1 + f b))) = s,
  { intro,
    rw (filter_eq_self _).mpr _,
    intros b hb,
    exact hu b },
  suffices : bdd_above (set.range (λ s, ∏ a in s, (1 + f a))) ↔
    bdd_above (set.range (λ s, ∑ a in s, f a)),
  { split; intro h,
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
        refine ge_of_tendsto has_sum_geometric_two _,
        rw eventually_at_top,
        refine ⟨range ((t \ s).card + 1), λ u hu, _⟩,
        refine (sum_le_sum_of_subset_of_nonneg hu _).trans (sum_le_sum _),
        { intros,
          exact pow_nonneg (sum_nonneg (λ _ _, hf _)) _ },
        { intros,
          refine pow_le_pow_of_le_left (sum_nonneg (λ _ _, hf _)) _ _,
          simpa using (hs (t \ s) disjoint_sdiff.symm).right.le
        } },
      { rw ←prod_sdiff (inter_subset_right t s),
        refine le_mul_of_one_le_of_le_of_nonneg _ le_rfl (zero_le_one.trans _);
        refine one_le_prod₀ _;
        simp [hf] },
      { simp [hf] } } }
end

@[simp] lemma is_unit_inv_iff [division_monoid β] {x : β} :
  is_unit x⁻¹ ↔ is_unit x :=
⟨λ h, by simpa using h.inv, λ h, h.inv⟩

lemma has_prod.inv {f : β → ℝ} {x : ℝ} (hf : has_prod f x) :
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
  { refine ((real.tendsto_inv (units.ne_zero _)).comp h').congr _,
    intro,
    simp }
end

lemma has_prod_inv_iff {f : β → ℝ} {x : ℝ} :
  has_prod f x⁻¹ ↔ has_prod (λ b, (f b)⁻¹) x :=
begin
  split;
  intro h;
  simpa using h.inv
end

lemma converges_prod_inv_iff {f : β → ℝ} :
  converges_prod (λ b, (f b)⁻¹) ↔ converges_prod f :=
begin
  split; rintro ⟨x, h⟩;
  refine ⟨x⁻¹, _⟩;
  simpa using h.inv
end

@[to_additive]
lemma prod_coe_sort_set [comm_monoid γ] (s : set β) (t : finset s) (f : β → γ) :
  ∏ (i : s) in t, f i = ∏ (i : β) in (t.map (embedding.subtype _)).filter (∈ s), f i :=
begin
  refine prod_bij (λ x _, x) _ (λ _ _, rfl) (λ _ _ _ _, subtype.ext) _,
  { rintro ⟨b, hb⟩,
    simp only [hb, subtype.coe_mk, mem_filter, finset.mem_map, embedding.coe_subtype, exists_prop,
               subtype.exists, exists_and_distrib_right, exists_eq_right, exists_true_left,
              and_true, imp_self] },
  { simp only [filter_true_of_mem, finset.mem_map, embedding.coe_subtype, exists_prop,
               subtype.exists, subtype.coe_mk, exists_and_distrib_right, exists_eq_right,
               forall_exists_index, implies_true_iff, set_coe.exists, exists_eq_right']
               {contextual := tt} }
end

lemma finset.monotone_map (f : β ↪ γ) :
  monotone (finset.map f) :=
λ _ _ h, map_subset_map.mpr h

@[simp] lemma finset.map_subtype_subtype (p : β → Prop) (s : finset (subtype p)) :
  finset.subtype p (s.map (embedding.subtype p)) = s :=
begin
  ext x,
  simp only [x.prop, mem_subtype, finset.mem_map, embedding.coe_subtype, exists_prop,
             subtype.exists, subtype.coe_mk, exists_and_distrib_right, exists_eq_right,
             subtype.coe_eta, exists_true_left],
end

lemma finset.subtype_map_gc (p : β → Prop) :
  galois_connection (finset.map (embedding.subtype p)) (finset.subtype p) :=
begin
  classical,
  intros s t,
  split; intro h,
  { exact (subtype_mono h).trans' (finset.map_subtype_subtype _ _).ge },
  { refine (finset.monotone_map _ h).trans _,
    simp }
end

lemma tendsto_finset_map_subtype_at_top (p : β → Prop) (f : finset β → ℝ) (F : filter ℝ)
  (h : tendsto (λ t : finset (subtype p), f (t.map (embedding.subtype p))) at_top F) :
  tendsto (f ∘ finset.filter p) at_top F :=
begin
  rw tendsto_at_top' at h ⊢,
  intros t ht,
  obtain ⟨u, hu⟩ := h t ht,
  refine ⟨u.map (embedding.subtype p), λ v hv, _⟩,
  simpa only [subtype_map] using hu (v.subtype p) _,
  rwa [ge_iff_le, ←(finset.subtype_map_gc _)]
end

-- lemma has_prod_of_has_prod_subtype_of_support_subset {f : β → α} {a : α} {s : set β}
--   (hf : mul_support f ⊆ s) (h : has_prod (f ∘ coe : s → α) a) :
--   has_sum (f ∘ coe : s → α) a ↔ has_sum f a :=
-- subtype.coe_injective.has_sum_iff $ by simpa using support_subset_iff'.1 hf

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

-- /-- A product `∏ (1 - aₙ)` with positive terms `aₙ` is convergent iff the series `∑ aₙ` converges. -/
-- lemma converges_prod_one_sub_iff_summable {f : β → ℝ} (hf : ∀ b, 0 ≤ f b) :
--   converges_prod (λ b, 1 - f b) ↔ summable f :=
-- begin
--   by_cases hlim : tendsto f cofinite (𝓝 0),
--   { rw tendsto_nhds at hlim,
--     specialize hlim (set.Ioo (-2⁻¹ : ℝ) 2⁻¹) is_open_Ioo _,
--     { simp },
--     -- simp at hlim,
--     split,
--     { sorry },
--     { intros hs,
--       refine converges_prod_of_converges_prod_cofinite_subset _ hlim _,
--     },
--   },
--   { split; intro h,
--     { rw ←sub_self (1 : ℝ) at hlim,
--       refine absurd ((h.tendsto_cofinite_one.const_sub _).congr _) hlim,
--       simp },
--     { exact absurd h.tendsto_cofinite_zero hlim } }
-- end


end

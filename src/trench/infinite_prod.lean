import algebra.order.complete_field
import analysis.specific_limits.basic
import trench.prod_le_sum
import to_mathlib.algebra.big_operators.basic
import to_mathlib.algebra.big_operators.order
import to_mathlib.algebra.group_with_zero.units.basic
import to_mathlib.algebra.order.field.basic
import to_mathlib.data.finset.image
import to_mathlib.topology.algebra.constructions
import to_mathlib.topology.algebra.group_with_zero
import to_mathlib.topology.algebra.order.monotone_convergence
import to_mathlib.topology.algebra.infinite_sum
import to_mathlib.topology.finset

noncomputable theory
open finset filter function classical
open_locale topology classical big_operators nnreal filter

variables {α : Type*} {β : Type*} {γ : Type*} {R M₀ G₀ K E : Type*}

section
variables [comm_monoid α] [topological_space α]
  -- [comm_semiring R] [topological_space R] [no_zero_divisors R] [nontrivial R]
  [comm_monoid_with_zero M₀] [no_zero_divisors M₀] [topological_space M₀]
  [comm_group_with_zero G₀] [topological_space G₀]
  [field K] [topological_space K] [has_continuous_mul K] [has_continuous_inv₀ K]
  [conditionally_complete_linear_ordered_field E] [topological_space E] [has_continuous_mul E]
  -- [has_continuous_inv₀ E]

structure has_prod (f : β → α) (a : α) : Prop :=
(finite_not_unit : {b | ¬ is_unit (f b)}.finite)
(tendsto_units : ∃ x : αˣ, tendsto
  (λ s : finset β, ∏ b in s, surj_units (f b)) at_top (𝓝 x))
(prod_eq : a = tendsto_units.some * ∏ b in finite_not_unit.to_finset, f b)

lemma has_prod_of_tendsto_of_finite [t2_space α] {f : β → α} {x : αˣ}
  (h : tendsto (λ s : finset β, ∏ b in s, surj_units (f b)) at_top (𝓝 x))
  (hs : {b | ¬ is_unit (f b)}.finite) :
  has_prod f (x * hs.to_finset.prod f) :=
begin
  refine ⟨hs, ⟨_, h⟩, _⟩,
  generalize_proofs H,
  rw [tendsto_nhds_unique (Exists.some_spec H) h]
end

lemma has_prod_of_tendsto_of_ne_zero [has_continuous_inv₀ G₀] [t2_space G₀] {f : β → G₀} {x : G₀}
  (h : tendsto (λ s : finset β, ∏ b in s.filter (λ i, f i ≠ 0), f b) at_top (𝓝 x))
  (hx : x ≠ 0) (hs : {b | f b = 0}.finite) :
  has_prod f (x * hs.to_finset.prod f) :=
begin
  have hx' : x = units.mk0 _ hx := rfl,
  rw hx' at h ⊢,
  suffices : tendsto (λ s : finset β, ∏ b in s, surj_units (f b)) at_top (𝓝 (units.mk0 _ hx)),
  { convert has_prod_of_tendsto_of_finite this (hs.subset _);
    simp [is_unit_iff_ne_zero] },
  simp_rw is_unit_iff_ne_zero at h,
  have : ∀ m : finset β, ∏ b in m.filter (λ i, f i ≠ 0), f b = ∏ b in m, surj_units (f b),
  { intro,
    rw prod_filter,
    refine prod_congr rfl (λ b _, _),
    split_ifs with hb hb,
    { simp [surj_units_apply_eq_mk0_apply hb] },
    { simp only [not_not] at hb,
      simp [hb], } },
  simp_rw this at h, clear this,
  have h' := h.inv₀ hx,
  rw tendsto_at_top_nhds at h h' ⊢,
  intros U hU hU',
  obtain ⟨V, hV, hV'⟩ := hU',
  rw is_open_prod_iff at hV,
  specialize hV x (mul_opposite.op x⁻¹) _,
  { simpa [surj_units_apply_eq_mk0_apply hx, ←hV'] using hU, },
  obtain ⟨s, t, hs, ht, hxs, hxt, hst⟩ := hV,
  obtain ⟨N, hN⟩ := h s hxs hs,
  obtain ⟨M, hM⟩ := h' (mul_opposite.op ⁻¹' t) hxt
    (mul_opposite.continuous_op.is_open_preimage _ ht),
  refine ⟨N ∪ M, λ u hu, _⟩,
  specialize hN u ((finset.subset_union_left _ _).trans hu),
  specialize hM u ((finset.subset_union_right _ _).trans hu),
  rw ←hV',
  refine hst _,
  simp only [set.mem_preimage, units.embed_product_apply, units.coe_prod, units.coe_inv,
            mul_opposite.op_inv, set.prod_mk_mem_set_prod_eq],
  exact ⟨hN, hM⟩
end

lemma has_prod_of_tendsto_of_forall_is_unit [t2_space α] {f : β → α} {x : αˣ}
  (h : tendsto (λ s : finset β, ∏ b in s, surj_units (f b)) at_top (𝓝 x))
  (hs : ∀ b, is_unit (f b)) :
  has_prod f x :=
begin
  have : {b | ¬ is_unit (f b)} = ∅ := set.subset_empty_iff.mp (λ x hx, hx (hs _)),
  convert has_prod_of_tendsto_of_finite h (set.finite_empty.subset this.le),
  simp [this]
end

lemma has_prod_is_empty [t2_space α] [h : is_empty β] (f : β → α) :
  has_prod f 1 :=
begin
  suffices : tendsto (λ s : finset β, ∏ b in s, surj_units (f b)) at_top (𝓝 1),
  { exact has_prod_of_tendsto_of_forall_is_unit this (λ x, h.elim x) },
  have : ∀ (s : finset β), ∏ i in s, surj_units (f i) = 1,
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
  suffices : tendsto (λ s : finset β, ∏ b in s, surj_units (f b)) at_top
    (𝓝 (surj_units (f default))),
  { convert has_prod_of_tendsto_of_finite this (set.finite_univ.subset (set.subset_univ _)),
    by_cases hf : is_unit (f default),
    { simp [hf, filter_singleton, surj_units_apply_is_unit hf] },
    { simp [hf, filter_singleton, surj_units_apply_not_is_unit hf] } },
  rw [order_top.at_top_eq, tendsto_pure_left],
  intros s hs,
  simpa using mem_of_mem_nhds hs
end

lemma has_prod_ratio [has_continuous_mul α] {f : β → α} {a : α} (hf : has_prod f a) :
  tendsto (λ sb : finset β × β, (
      ∏ b in (insert sb.2 sb.1), surj_units (f b)) /
      ∏ b in sb.1, surj_units (f b))
    (at_top.comap prod.fst) (𝓝 1) :=
begin
  obtain ⟨x, hx⟩ := hf.tendsto_units,
  simp_rw div_eq_mul_inv,
  rw ←mul_inv_self x,
  refine tendsto.mul _ ((tendsto_inv _).comp _),
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

lemma has_prod_ratio' [has_continuous_mul α] {f : β → α} {a : α} (hf : has_prod f a) :
  tendsto (λ sb : finset β × finset β, (
      ∏ b in (sb.1 ∪ sb.2), surj_units (f b)) /
      ∏ b in sb.1, surj_units (f b))
    at_top (𝓝 1) :=
begin
  obtain ⟨x, hx⟩ := hf.tendsto_units,
  rw ←mul_inv_self x,
  simp_rw div_eq_mul_inv,
  refine tendsto.mul _ ((tendsto_inv _).comp _),
  { intros U hU,
    specialize hx hU,
    simp only [filter.mem_map, mem_at_top_sets, ge_iff_le, le_eq_subset, set.mem_preimage,
               prod.forall, prod.exists, prod.mk_le_mk, and_imp] at hx ⊢,
    obtain ⟨s, hs⟩ := hx,
    exact ⟨s, ∅, λ s' t' hs' ht', hs _ (hs'.trans (subset_union_left _ _))⟩ },
  { rw ←prod_at_top_at_top_eq,
    exact (hx.comp tendsto_fst) }
end

lemma has_prod.inv [has_continuous_mul G₀] [t2_space G₀] {f : β → G₀} {x : G₀} (hf : has_prod f x) :
  has_prod (λ b, (f b)⁻¹) x⁻¹ :=
begin
  obtain ⟨h, ⟨x, h'⟩, h''⟩ := hf,
  simp only [←is_unit_inv_iff] at h { single_pass := tt },
  rw [←inv_inj, mul_inv_rev, mul_comm, ←prod_inv_distrib] at h'',
  convert has_prod_of_tendsto_of_finite (h'.inv.congr _) h,
  { convert h'',
    { generalize_proofs H,
      simp [tendsto_nhds_unique h' (Exists.some_spec H)] },
    { simp } },
  { intro,
    simp }
end

lemma has_prod_inv_iff [has_continuous_mul G₀] [t2_space G₀] {f : β → G₀} {x : G₀}  :
  has_prod f x⁻¹ ↔ has_prod (λ b, (f b)⁻¹) x :=
begin
  split;
  intro h;
  simpa using h.inv
end

def converges_prod (f : β → α) : Prop := ∃ (a : α), has_prod f a

lemma converges_prod_of_tendsto_of_subset_finite {f : β → α} {x : αˣ} {s : set β}
  (h : tendsto (λ s : finset β, ∏ b in s, surj_units (f b)) at_top (𝓝 x))
  (hs' : s.finite) (hs : {b | ¬ is_unit (f b)} ⊆ s) :
  converges_prod f :=
⟨_, hs'.subset hs, ⟨_, h⟩, rfl⟩

lemma converges_prod_of_tendsto_of_ne_zero_of_subset_finite
  [has_continuous_mul G₀] [has_continuous_inv₀ G₀] [t2_space G₀] {f : β → G₀} {x : G₀} {s : set β}
  (h : tendsto (λ s : finset β, ∏ b in (s.filter (λ i, f i ≠ 0)), f b) at_top (𝓝 x))
  (hx : x ≠ 0) (hs' : s.finite) (hs : {b | f b = 0} ⊆ s) :
  converges_prod f :=
begin
  suffices : tendsto (λ s : finset β, ∏ b in s, surj_units (f b)) at_top (𝓝 (units.mk0 _ hx)),
  { refine converges_prod_of_tendsto_of_subset_finite this hs' (subset_trans _ hs),
    simp [is_unit_iff_ne_zero] },
  simp_rw is_unit_iff_ne_zero at h hx,
  have : ∀ m : finset β, ∏ b in m.filter (λ i, f i ≠ 0), f b = ∏ b in m, surj_units (f b),
  { intro,
    rw prod_filter,
    refine prod_congr rfl (λ b _, _),
    split_ifs with hb hb,
    { simp [surj_units_apply_eq_mk0_apply hb] },
    { simp only [not_not] at hb,
      simp [hb], } },
  simp_rw this at h, clear this,
  have h' := h.inv₀ hx,
  rw tendsto_at_top_nhds at h h' ⊢,
  intros U hU hU',
  obtain ⟨V, hV, hV'⟩ := hU',
  rw is_open_prod_iff at hV,
  specialize hV x (mul_opposite.op x⁻¹) _,
  { simpa [surj_units_apply_eq_mk0_apply hx, ←hV'] using hU, },
  obtain ⟨s, t, hs, ht, hxs, hxt, hst⟩ := hV,
  obtain ⟨N, hN⟩ := h s hxs hs,
  obtain ⟨M, hM⟩ := h' (mul_opposite.op ⁻¹' t) hxt
    (mul_opposite.continuous_op.is_open_preimage _ ht),
  refine ⟨N ∪ M, λ u hu, _⟩,
  specialize hN u ((finset.subset_union_left _ _).trans hu),
  specialize hM u ((finset.subset_union_right _ _).trans hu),
  rw ←hV',
  refine hst _,
  simp only [set.mem_preimage, units.embed_product_apply, units.coe_prod, units.coe_inv,
            mul_opposite.op_inv, set.prod_mk_mem_set_prod_eq],
  exact ⟨hN, hM⟩
end

lemma converges_prod_fintype [fintype β] (f : β → α) :
  converges_prod f :=
begin
  have : ∃ x : αˣ, tendsto
    (λ s : finset β, ∏ b in s, surj_units (f b)) at_top (𝓝 x),
  { refine ⟨∏ b, surj_units (f b), _⟩,
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

lemma has_prod_zero_iff_converges_prod_and_exists_zero' [nontrivial M₀] {f : β → M₀} :
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

lemma has_prod_zero_iff_converges_prod_and_exists_zero [nonempty β] {f : β → M₀} :
  has_prod f 0 ↔ converges_prod f ∧ ∃ i, f i = 0 :=
begin
  casesI subsingleton_or_nontrivial M₀,
  { simp only [eq_iff_true_of_subsingleton, exists_const, and_true],
    split,
    { intro h,
      exact ⟨_, h⟩ },
    { rintro ⟨x, hx⟩,
      rw subsingleton.elim 0 x,
      exact hx } },
  { exact has_prod_zero_iff_converges_prod_and_exists_zero' }
end

lemma function.injective.converges_prod_iff [t2_space α] {f : β → α} {g : γ → β} (hg : injective g)
  (hf : ∀ x ∉ set.range g, f x = 1) :
  converges_prod (f ∘ g) ↔ converges_prod f :=
begin
  have :
    filter.map (λ (s : finset γ), ∏ (i : γ) in s, surj_units (f (g i))) at_top =
    filter.map (λ (s : finset β), ∏ (i : β) in s, surj_units (f i)) at_top,
  { convert injective.map_at_top_finset_prod_eq hg _,
    { funext,
      refl },
    intros b hb,
    simp [hf _ hb] },
  split,
  { rintro ⟨a, h, ⟨y, h'⟩, h''⟩,
    rw tendsto at h',
    refine converges_prod_of_tendsto_of_subset_finite (h'.trans' this.ge) (h.image g) _,
    intros b hb,
    by_cases hbg : b ∈ set.range g,
    { obtain ⟨c, rfl⟩ := hbg,
      refine ⟨c, _⟩,
      simpa using hb },
    { simpa [hf _ hbg] using hb } },
  { rintro ⟨a, h, ⟨y, h'⟩, h''⟩,
    rw tendsto at h',
    refine converges_prod_of_tendsto_of_subset_finite (h'.trans' this.le)
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

lemma converges_prod_inv_iff [has_continuous_mul G₀] [t2_space G₀] {f : β → G₀} :
  converges_prod (λ b, (f b)⁻¹) ↔ converges_prod f :=
begin
  split; rintro ⟨x, h⟩;
  refine ⟨x⁻¹, _⟩;
  simpa using h.inv
end

lemma converges_prod.vanishing [has_continuous_mul α] {f : β → α} (hf : converges_prod f) ⦃e : set α⦄
  (he : e ∈ 𝓝 (1 : α)) : ∃ s : finset β, ∀ t, disjoint t s → ∏ k in t, f k ∈ e :=
begin
  rcases hf with ⟨x, hf⟩,
  have := has_prod_ratio hf,
  have he' : e ∈ map (coe : αˣ → α) (𝓝 1) := units.continuous_coe.tendsto _ he,
  have h := has_prod_ratio' hf he',
  simp only [filter.mem_map, mem_comap, mem_at_top_sets, ge_iff_le, le_eq_subset, exists_prop,
             set.preimage_subset_iff, set.mem_preimage, prod.forall] at h,
  simp only [prod.exists, prod.mk_le_mk, le_eq_subset, and_imp] at h,
  obtain ⟨s, t, h⟩ := h,
  refine ⟨s ∪ t ∪ hf.finite_not_unit.to_finset, λ u hdisj, _⟩,
  specialize h (s ∪ (t ∪ hf.finite_not_unit.to_finset)) (t ∪ u)
    (subset_union_left _ _) (subset_union_left _ _),
  simp_rw [union_assoc s, union_left_comm, ←union_assoc t, union_idempotent t, ←union_assoc s] at h,
  rw [prod_union hdisj.symm, mul_div_cancel'''] at h,
  suffices : ∀ b ∈ u, is_unit (f b),
  { simp only [units.coe_prod] at h,
    convert h using 1,
    refine prod_congr rfl _,
    intros b hb,
    rw [coe_surj_units_apply_is_unit (this _ hb)] },
  intros b hb,
  have : {b} ≤ u := by simp only [hb, le_eq_subset, singleton_subset_iff],
  specialize hdisj this,
  simp only [union_assoc, le_eq_subset, singleton_subset_iff, mem_union, set.finite.mem_to_finset,
              set.mem_set_of_eq, bot_eq_empty, not_mem_empty] at hdisj,
  contrapose! hdisj,
  simp [hdisj]
end

/-- The sequence of the factors in a convergent infinite product always tends to 1. -/
lemma converges_prod.tendsto_cofinite_one [has_continuous_mul α]
  {f : β → α} (hf : converges_prod f) :
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
lemma converges_prod.tendsto_cofinite_zero [comm_ring R] [topological_space R]
  [has_continuous_add R] [has_continuous_mul R]
  {f : β → R} (hf : converges_prod (λ b, 1 + f b)) :
  tendsto f cofinite (𝓝 0) :=
begin
  rw ←neg_add_self (1 : R),
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
      { convert (units.continuous_coe.tendsto _).comp hy,
        { ext,
          simp only [comp_app, units.coe_prod],
          refine prod_congr rfl (λ i hi, _),
          rw [coe_surj_units_apply_ne_zero],
          exact (zero_lt_one.trans_le (le_add_of_nonneg_right (hf i))).ne' },
        { rw h.prod_eq,
          have he : h.finite_not_unit.to_finset = ∅,
          { ext x,
            simp [hu] },
          simp only [he, filter_congr_decidable, prod_empty, mul_one, ←units.ext_iff],
          generalize_proofs H,
          refine tendsto_nhds_unique _ hy,
          exact Exists.some_spec H } } },
    { have hb := (this.mpr
        (is_lub_of_tendsto_at_top (finset.sum_mono_set_of_nonneg hf) h.some_spec).bdd_above),
      replace hb : bdd_above (set.range
        (λ (s : finset β), ∏ b in (s.filter (λ i, 1 + f i ≠ 0)), (1 + f b))),
      { convert hb,
        ext,
        refine prod_congr _ (λ _ _, rfl),
        rw filter_eq_self,
        intro i,
        simp [(zero_lt_one.trans_le (le_add_of_nonneg_right (hf i))).ne'] },
      have hunit : (⨆ (i : finset β), (λ (s : finset β), ∏ (a : β) in (s.filter (λ i, 1 + f i ≠ 0)),
        (1 + f a)) i) ≠ 0,
      { refine ne_of_gt (lt_cSup_of_lt hb ⟨∅, _⟩ zero_lt_one),
        simp },
      refine converges_prod_of_tendsto_of_ne_zero_of_subset_finite
        (tendsto_at_top_is_lub _ (is_lub_csupr hb)) hunit set.finite_empty _,
      { refine (monotone_prod_of_one_le' _).comp (monotone_filter_left _),
        simp [hf] },
      { intro i,
        simp [(zero_lt_one.trans_le (le_add_of_nonneg_right (hf i))).ne'] } } },
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
lemma converges_prod_of_converges_prod_cofinite_subset [has_continuous_mul α]
  {f : β → α} (s : set β) (hs : sᶜ.finite) (h : converges_prod (λ x : s, f x)) :
  converges_prod f :=
begin
  classical,
  obtain ⟨x, h, ⟨y, h'⟩, h''⟩ := h,
  set t : set β := {b : β | is_unit (f b) ∧ b ∉ s} with ht,
  have htf : t.finite := hs.subset (λ _ h, h.right),
  refine converges_prod_of_tendsto_of_subset_finite _ (hs.union (h.image coe)) _,
  { exact y * ∏ i in htf.to_finset, surj_units (f i) },
  { simp only [←prod_filter_mul_prod_filter_not _ (∈ s)] { single_pass := tt },
    refine tendsto.mul _ _,
    { refine tendsto_finset_map_subtype_at_top (∈ s)
        (λ t : finset β, ∏ b in t, surj_units (f b)) (𝓝 y) _,
      simpa using h' },
    { simp_rw prod_filter_mul_prod_filter_not,
      refine tendsto_finset_map_subtype_at_top (∉ s)
        (λ t : finset β, ∏ b in t, surj_units (f b)) (𝓝 _) _,
      haveI : fintype (sᶜ : set β) := hs.fintype,
      suffices : ∏ (x : β) in htf.to_finset, surj_units (f x) =
        (λ t : finset (sᶜ : set β), ∏ b in t.map (embedding.subtype (∉ s)), surj_units (f b)) ⊤,
      { rw this,
        exact order_top.tendsto_at_top_nhds _ },
      simp only [top_eq_univ, finset.prod_map, embedding.coe_subtype],
      rw ←prod_filter_mul_prod_filter_not univ (λ b : (sᶜ : set β), is_unit (f b)),
      rw ←mul_one (∏ (x : β) in htf.to_finset, surj_units (f x)),
      congr' 1,
      { refine prod_bij _ _ _ _ _,
        { refine λ b hb, ⟨b, _⟩,
          simp only [set.finite.mem_to_finset, set.mem_set_of_eq] at hb,
          exact hb.right },
        { simp { contextual := tt } },
        { simp },
        { simp },
        { simp only [set.finite.mem_to_finset, set.mem_set_of_eq, mem_filter, mem_univ, true_and,
                     set_coe.forall, subtype.coe_mk, subtype.mk_eq_mk, exists_prop,
                     exists_eq_right', set.mem_compl_iff],
          exact λ _ h h', ⟨h', h⟩ } },
      { rw prod_eq_one,
        simp [surj_units_apply_not_is_unit] { contextual := tt } } } },
    { intro,
      simp [or.comm, classical.em] { contextual := tt } },
end

instance {K : Type*} [linear_ordered_field K] : no_max_order Kˣ :=
begin
  constructor,
  intro x,
  obtain ⟨y, hy⟩ := exists_gt (max (x : K) 1),
  refine ⟨units.mk0 _ ((zero_lt_one.trans_le (le_max_right _ _)).trans hy).ne',
          units.coe_lt_coe.mp (hy.trans_le' (le_max_left _ _))⟩
end

lemma converges_prod.converges_prod_subtype_of_one_le {f : β → ℝ} (h : converges_prod f)
  (p : β → Prop) (hf : ∀ b, is_unit (f b) → 1 ≤ f b) :
  converges_prod (λ b : subtype p, f b) :=
begin
  have hmap :
  (λ (s : finset (subtype p)), ∏ (b : subtype p) in s, (surj_units (f b) : ℝ)) =
    λ s : finset (subtype p), ∏ b : β in (s.map (embedding.subtype _)), surj_units (f b),
  { ext,
    rw [←prod_subtype_map_embedding],
    exact λ _ _, rfl },
  have key : monotone (λ s : finset (subtype p), ∏ b in s, (surj_units (f b) : ℝ)),
  { intros s t hst,
    refine prod_le_prod_of_subset_of_one_le₀ hst (prod_nonneg _) _,
    { rintro ⟨i, hi⟩ _,
      by_cases hu : is_unit (f i),
      { simp [surj_units_apply_is_unit hu, zero_le_one.trans (hf _ hu)], },
      { simp [surj_units_apply_not_is_unit hu] } },
    { rintro ⟨i, hi⟩ _,
      by_cases hu : is_unit (f i),
      { simp [surj_units_apply_is_unit hu, hf _ hu], },
      { simp [surj_units_apply_not_is_unit hu] } } },
  obtain ⟨x, hx, ⟨x', hx'⟩, hx''⟩ := id h,
  have hxc := (units.continuous_coe.tendsto _).comp hx',
  rcases tendsto_of_monotone key with (hy|⟨y, hy⟩),
  { rw hmap at hy,
    have := tendsto_finset_map_subtype_at_top p (λ s, ∏ b : β in s, (surj_units (f b) : ℝ))
      at_top hy,
    refine absurd (tendsto_at_top_mono _ this) (not_tendsto_at_top_of_tendsto_nhds hxc),
    intro s,
    simp only [comp_app, filter_congr_decidable, units.coe_prod],
    refine prod_le_prod_of_subset_of_one_le₀ (filter_subset p s)
      (prod_nonneg _) _,
    { intro i,
      by_cases hu : is_unit (f i),
      { simp [surj_units_apply_is_unit hu, zero_le_one.trans (hf _ hu)], },
      { simp [surj_units_apply_not_is_unit hu] } },
    { rintro i _,
      by_cases hu : is_unit (f i),
      { simp [surj_units_apply_is_unit hu, hf _ hu], },
      { simp [surj_units_apply_not_is_unit hu] } } },
  { suffices : tendsto (λ (s : finset (subtype p)), ∏ (b : subtype p) in s, surj_units (f ↑b))
      at_top (𝓝 (surj_units y)),
    { refine converges_prod_of_tendsto_of_subset_finite this
        (hx.preimage (subtype.coe_injective.inj_on _)) _,
      simp },
    refine (tendsto.comp _ hy).congr _,
    { exact λ i, surj_units i },
    { simp only [comp_app],
      intro s,
      rw ←prod_surj_units s (λ b, ((surj_units (f b)) : ℝ)),
      { simp_rw surj_units_apply_coe_units },
      { simp } },
    { rcases eq_or_ne y 0 with rfl|hy',
      { refine absurd ((is_lub_of_tendsto_at_top key hy).left _) zero_lt_one.not_le,
        use ∅,
        simp },
      exact tendsto_surj_units_of_ne_zero _ hy' } },
end

lemma converges_prod.converges_prod_subtype_of_bounded_of_antitone {f : β → ℝ}
  (h : converges_prod f) (p : β → Prop) (hp : ∀ b, p b → (1 / 2) < f b)
  (hf' : antitone (λ s : finset (subtype p), ∏ b in s, (surj_units (f b) : ℝ))) :
  converges_prod (λ b : subtype p, f b) :=
begin
  have hmap :
  (λ (s : finset (subtype p)), ∏ (b : subtype p) in s, (surj_units (f b) : ℝ)) =
    λ s : finset (subtype p), ∏ b : β in (s.map (embedding.subtype _)), surj_units (f b),
  { ext,
    rw [←prod_subtype_map_embedding],
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
    intros hb,
    have : 0 < f b := ((hp _ hb).trans' (half_pos zero_lt_one)),
    rw surj_units_apply_is_unit (is_unit_iff_ne_zero.mpr this.ne'),
    simp [this.le] },
  suffices hy' : tendsto (λ (s : finset (subtype p)),
    ∏ (b : subtype p) in s, surj_units (f b)) at_top (𝓝 (surj_units y)),
  { refine converges_prod_of_tendsto_of_subset_finite hy'
      (hx.preimage (subtype.coe_injective.inj_on _)) _,
    simp },
  refine ((tendsto_surj_units_of_ne_zero _ _).comp hy).congr _,
  { simp only [comp_app],
    intro s,
    rw ←prod_surj_units s (λ b, ((surj_units (f b)) : ℝ)),
    { simp_rw surj_units_apply_coe_units },
    { simp } },
  rintro rfl,
  refine x'.is_unit.ne_zero _,
  refine tendsto_nhds_unique ((units.continuous_coe.tendsto _).comp hx') _,
  rw tendsto_at_top_nhds at hy ⊢,
  have : set.Ioo (1 / 2 : ℝ) 2 ∈ (𝓝 (1 : ℝ)),
  { exact Ioo_mem_nhds one_half_lt_one one_lt_two },
  obtain ⟨s, hs⟩ := h.vanishing this,
  set ps : ℝ := ∏ b in (s.subtype p), (surj_units (f b) : ℝ) with hps,
  have pspos : 0 < ps,
  { refine prod_pos _,
    rintro ⟨b, hb⟩,
    have : 0 < f b := ((hp _ hb).trans' (half_pos zero_lt_one)),
    simp only [surj_units_apply_is_unit (is_unit_iff_ne_zero.mpr this.ne'), this,
               subtype.coe_mk, is_unit.unit_spec, implies_true_iff] },
  obtain ⟨t, ht⟩ := hy (metric.ball 0 (ps / 2)) _ metric.is_open_ball,
  swap,
  { simp [half_pos pspos] },
  specialize ht (t ∪ s.subtype p) (subset_union_left _ _),
  rw [←sdiff_union_self_eq_union, prod_union, ←hps] at ht, swap,
  { exact disjoint_sdiff_self_left },
  specialize hs (((t \ s.subtype p).map (embedding.subtype _))) _,
  { intros u htu hsu x hx,
    specialize htu hx,
    simp only [mem_filter, finset.mem_map, mem_sdiff, mem_subtype, embedding.coe_subtype,
                exists_prop, subtype.exists, subtype.coe_mk, exists_and_distrib_right,
                exists_eq_right] at htu,
    exact absurd (hsu hx) htu.right },
  replace hs : (1 / 2 : ℝ) < ∏ b in (t \ s.subtype p), surj_units (f b),
  { simp only [finset.prod_map, embedding.coe_subtype, one_div, set.mem_Ioo] at hs,
    rw ←inv_eq_one_div,
    refine hs.left.trans_le (le_of_eq _),
    refine prod_congr rfl _,
    rintro ⟨b, hb⟩,
    have : 0 < f b := ((hp _ hb).trans' (half_pos zero_lt_one)),
    simp only [surj_units_apply_is_unit (is_unit_iff_ne_zero.mpr this.ne'), subtype.coe_mk,
               is_unit.unit_spec, eq_self_iff_true, implies_true_iff] },
  simp only [mem_ball_zero_iff, real.norm_eq_abs, abs_lt] at ht,
  have : ps / 2 < ps / 2,
  { calc ps / 2 = (1 / 2) * ps : by rw [div_eq_mul_one_div, mul_comm]
    ...   < (∏ b in (t \ s.subtype p), surj_units (f b)) * ps :
      (mul_lt_mul_right pspos).mpr hs
    ...   < ps / 2 : ht.right },
  exact absurd this (lt_irrefl _) ,
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
  have hmono : monotone (λ s : finset (f ⁻¹' set.Ioo (-2⁻¹) 2⁻¹ : set β),
    ∏ b in s, (surj_units (1 + f b) : ℝ)),
  { refine monotone_prod_of_one_le' (λ b, _),
    have : 1 ≤ 1 + f b,
    { simp [hf] },
    rw coe_surj_units_apply_ne_zero (zero_lt_one.trans_le this).ne',
    exact this },
  have hanti : antitone (λ s : finset (f ⁻¹' set.Ioo (-2⁻¹) 2⁻¹ : set β),
    ∏ b in s, (surj_units (1 - f b) : ℝ)),
  { refine antitone_prod_of_le_one' (λ b, _) (λ b, coe_surj_units_nonneg (hapos b).le),
    rw coe_surj_units_apply_ne_zero,
    { simp [hf] },
    { rw [ne.def, sub_eq_zero],
      exact (b.prop.right.trans h2).ne' } },
  by_cases hlim : tendsto f cofinite (𝓝 0),
  { rw tendsto_nhds at hlim,
    specialize hlim (set.Ioo (-2⁻¹ : ℝ) 2⁻¹) is_open_Ioo _,
    { simp },
    split,
    { intros hs,
      rw ←converges_prod_one_add_iff_summable hf,
      refine converges_prod_of_converges_prod_cofinite_subset _ hlim _,
      have npos : ∀ t : finset (f ⁻¹' set.Ioo (-2⁻¹) 2⁻¹ : set β),
        (0 : ℝ) < ∏ b in t, surj_units (1 - f b),
      { intro,
        exact prod_pos (λ i hi, coe_surj_units_pos (hapos i)) },
      rcases tendsto_of_monotone hmono with (hy|⟨y, hy⟩),
      { obtain ⟨_, -, ⟨x', hx'⟩, -⟩ := hs.converges_prod_subtype_of_bounded_of_antitone
          (∈ f ⁻¹' set.Ioo (-2⁻¹) 2⁻¹) _ hanti,
        { rw tendsto_at_top_at_top_iff_of_monotone hmono at hy,
          obtain ⟨t, ht⟩ := hy (x'⁻¹ + 1),
          refine absurd (lt_add_of_le_of_pos _ zero_lt_one) ht.not_lt,
          have key : (∏ b in t, (surj_units (1 - f b) : ℝ))⁻¹ ≤ x'⁻¹,
          { rw inv_le_inv,
            { refine hanti.le_of_tendsto (((units.continuous_coe.tendsto _).comp hx').congr _) t,
              intro,
              simpa },
            { exact npos t },
            { refine lt_of_le_of_ne _ x'.is_unit.ne_zero.symm,
              refine ge_of_tendsto' ((units.continuous_coe.tendsto _).comp hx') _,
              simp only [comp_app, units.coe_prod],
              exact λ s, prod_nonneg (λ i hi, coe_surj_units_nonneg (hapos i).le) } },
          refine key.trans' _,
          simp only [is_unit_iff_ne_zero] at npos ⊢,
          clear ht key,
          induction t using finset.cons_induction_on with a t ha IH,
          { simp },
          { simp only [ha, filter_insert, (hapos a).ne', (hapos' a).ne', cons_eq_insert,
                      if_true, prod_insert, mem_filter, false_and, not_false_iff, mul_inv_rev,
                      ne.def],
            rw [coe_surj_units_apply_ne_zero (hapos' a).ne',
                coe_surj_units_apply_ne_zero (hapos a).ne', mul_comm],
            exact mul_le_mul IH (one_add_le_inv_one_sub_of_lt_one (a.prop.right.trans h2))
              (hapos' a).le (inv_nonneg_of_nonneg (npos _).le) } },
        { simp only [set.mem_preimage, set.mem_Ioo, one_div, and_imp],
          intros b hb hb',
          rw [lt_sub_comm, inv_eq_one_div, sub_half, ←inv_eq_one_div],
          exact hb' } },
      refine converges_prod_of_tendsto_of_ne_zero_of_subset_finite (hy.congr _) _
        set.finite_empty _,
      { intro s,
        refine prod_bij _ _ _ _ _,
        { exact λ i _, i },
        { simp only [mem_filter],
          intros i hi,
          exact ⟨hi, (hapos' i).ne'⟩ },
        { intros i hi,
          rw [coe_surj_units_apply_ne_zero ((hapos' i).ne')] },
        { exact λ _ _ _ _ h, h },
        { simp only [mem_filter],
          rintro b ⟨hb, hb'⟩,
          exact ⟨b, hb, rfl⟩ } },
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
        refine prod_nonneg (λ i hi, coe_surj_units_nonneg (hapos i).le) },
      refine converges_prod_of_tendsto_of_ne_zero_of_subset_finite (hy.congr _)
        _ set.finite_empty _,
      { intro s,
        refine prod_bij _ _ _ _ _,
        { exact λ i _, i },
        { simp only [mem_filter],
          intros i hi,
          exact ⟨hi, (hapos i).ne'⟩ },
        { intros i hi,
          rw [coe_surj_units_apply_ne_zero ((hapos i).ne')] },
        { exact λ _ _ _ _ h, h },
        { simp only [mem_filter],
          rintro b ⟨hb, hb'⟩,
          exact ⟨b, hb, rfl⟩ } },
      { obtain ⟨_, -, ⟨x', hx'⟩, -⟩ := hs.converges_prod_subtype_of_one_le
            (∈ f ⁻¹' set.Ioo (-2⁻¹) 2⁻¹) _, swap,
        { intros,
          simpa using hf _ },
        have xpos : (0 : ℝ) < x',
        { refine lt_of_le_of_ne (ge_of_tendsto' ((units.continuous_coe.tendsto _).comp hx')
            (λ t, _)) x'.ne_zero.symm,
          simp only [comp_app, units.coe_prod],
          refine prod_nonneg (λ b hb, coe_surj_units_nonneg (hapos2' b).le) },
        refine ((inv_pos_of_pos xpos).trans_le _).ne',
        refine le_of_tendsto_of_tendsto'
          (((units.continuous_coe.tendsto _).comp hx').inv₀ xpos.ne') hy (λ t, _),
        simp only [comp_app, units.coe_prod],
        induction t using finset.cons_induction_on with a t ha IH,
        { simp only [comp_app, prod_empty, units.coe_one, inv_one] },
        { suffices : (∏ x in t, (surj_units (1 + 2 * f (x : β)) : ℝ))⁻¹ * (1 + 2 * f a)⁻¹ ≤
            (1 - f a) * ∏ x in t, surj_units (1 - f (x : β)),
          { simpa [ha, surj_units_apply_is_unit (is_unit_iff_ne_zero.mpr (hapos a).ne'),
                   surj_units_apply_is_unit (is_unit_iff_ne_zero.mpr (hapos2' a).ne')] using this },
          rw mul_comm,
          refine mul_le_mul _ IH (inv_nonneg_of_nonneg (prod_nonneg _))
            (hapos _).le,
          { refine inv_one_add_two_mul_le_one_sub_of_nonneg_of_le_half (hf _) _,
            rw ←inv_eq_one_div,
            exact a.prop.right.le },
          { exact λ b hb, coe_surj_units_nonneg (hapos2' b).le } } },
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

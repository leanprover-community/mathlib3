import analysis.specific_limits.basic
import topology.algebra.infinite_sum
import trench.prod_le_sum
import to_mathlib.algebra.hom.units
import to_mathlib.topology.algebra.order.monotone_convergence

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

-- lemma exists_tendsto_finer_filter_of_tendsto {f g : β → α} {x : α}
--   (h : tendsto (λ s, ∏ i in s, f i) at_top (𝓝 x)) :
--   ∃ y, tendsto ((λ s, ∏ i in s, f i) ∘ finset.filter (λ i, is_unit (g i))) at_top (𝓝 y) :=
-- begin
--   by_cases hf : {x | is_unit (g x)}.finite,
--   { refine ⟨hf.to_finset.prod f, _⟩,
--     rw tendsto_at_top',
--     intros s hs,
--     refine ⟨hf.to_finset, λ t ht, _⟩,
--     have hs' : hf.to_finset.prod f ∈ s,
--     { rw mem_nhds_iff at hs,
--       obtain ⟨s, hs, _, hs'⟩ := hs,
--       exact hs hs' },
--     simp only [comp_app],
--     convert hs',
--     ext,
--     simp only [mem_filter, set.finite.mem_to_finset, set.mem_set_of_eq, and_iff_right_iff_imp],
--     intros ha,
--     refine ht _,
--     simp [ha] },
--   { refine ⟨x, _⟩,
--     rw tendsto_at_top_nhds at h ⊢,
--     refine h.comp _,
--     refine (finset.monotone_filter_left _).tendsto_at_top_at_top (λ t, _),
--     obtain ⟨b, hb, htb⟩ := set.infinite.exists_not_mem_finset hf t,
--     refine ⟨t.cons _ htb, _⟩,
--     -- simp at hf,
--     -- contrapose! hf,
--     -- obtain ⟨s, hs⟩ := hf,
--     -- simp at hs,
--     -- refine set.finite.of_finset s _,
--   },
--   -- have : (at_top : _root_.filter (finset β)) ≤
--   -- rw tendsto_at_top' at h,
--   -- simp_rw tendsto_at_top',


-- end
-- #exit

-- -- #exit

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

lemma prod_le_prod_of_subset_of_one_le₀ [ordered_comm_semiring γ] {f : β → γ} {s t : finset β}
  (h : s ⊆ t) (hs : 0 ≤ ∏ b in s, f b) (hf : ∀ b ∈ t, b ∉ s → 1 ≤ f b) :
  ∏ b in s, f b ≤ ∏ b in t, f b :=
calc (∏ i in s, f i) ≤ (∏ i in t \ s, f i) * (∏ i in s, f i) :
    le_mul_of_one_le_left hs $ one_le_prod₀ $ by simpa only [mem_sdiff, and_imp]
  ... = ∏ i in t \ s ∪ s, f i : (prod_union sdiff_disjoint).symm
  ... = ∏ i in t, f i         : by rw [sdiff_union_of_subset h]

lemma prod_le_prod_of_subset_of_le_one₀ [ordered_comm_semiring γ] {s t : finset β} {f : β → γ}
  (h : s ⊆ t) (ht : ∀ i ∈ t, 0 ≤ f i) (hf : ∀ i ∈ t, i ∉ s → f i ≤ 1) :
  ∏ i in t, f i ≤ ∏ i in s, f i :=
by classical;
calc ∏ i in t, f i = ∏ i in t \ s ∪ s, f i    : by rw [sdiff_union_of_subset h]
  ... = (∏ i in t \ s, f i) * (∏ i in s, f i) : (prod_union sdiff_disjoint)
  ... ≤ ∏ i in s, f i                         : by
    { refine mul_le_of_le_one_left (prod_nonneg $ λ _ hb, ht _ (h hb)) (prod_le_one _ _),
      { simp [ht] { contextual := tt} },
      { simpa using hf } }

lemma prod_le_one₀ [ordered_comm_semiring γ] {s : finset β} {f : β → γ}
  (h : ∀i ∈ s, f i ≤ 1) (h' : ∀i ∈ s, 0 ≤ f i) : ∏ i in s, f i ≤ 1 :=
begin
  rw ←prod_empty,
  refine prod_le_prod_of_subset_of_le_one₀ (empty_subset _) h' (λ _ hb _, h _ hb)
end

lemma monotone_prod_of_one_le' [ordered_comm_semiring γ] {f : β → γ} (hf : ∀ b, 1 ≤ f b) :
  monotone (λ s, ∏ b in s, f b) :=
λ _ _ h, prod_le_prod_of_subset_of_one_le₀ h
  (prod_nonneg (λ b _, zero_le_one.trans (hf _))) (λ b _ _, hf b)

lemma antitone_prod_of_le_one' [ordered_comm_semiring γ] {f : β → γ} (hf : ∀ b, f b ≤ 1)
  (hf' : ∀ b, 0 ≤ f b) :
  antitone (λ s, ∏ b in s, f b) :=
λ _ _ h, prod_le_prod_of_subset_of_le_one₀ h (λ _ _, hf' _) (λ _ _ _, hf _)

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

lemma finset.subtype_map_gci (p : β → Prop) :
  galois_coinsertion (finset.map (embedding.subtype p)) (finset.subtype p) :=
(finset.subtype_map_gc _).to_galois_coinsertion $ by simp

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

lemma tendsto_union_map_subtype_at_top (p : β → Prop) :
  tendsto (λ (pq : finset (subtype p) × finset (subtype (λ i, ¬ p i))),
    (pq.1.map (embedding.subtype _)) ∪ (pq.2.map (embedding.subtype _))) at_top at_top :=
begin
  intro,
  simp only [mem_at_top_sets, ge_iff_le, le_eq_subset, filter.mem_map, set.mem_preimage,
             prod.forall, prod.exists, prod.mk_le_mk, and_imp, forall_exists_index],
  intros s hs,
  refine ⟨s.subtype p, s.subtype _, λ t u ht hu, hs _ _⟩,
  classical,
  rw [←filter_union_filter_neg_eq p s, ←subtype_map, ←subtype_map],
  exact union_subset_union (finset.monotone_map _ ht) (finset.monotone_map _ hu)
end

lemma tendsto_prod_mk_subtype_at_top (p : β → Prop) :
  tendsto (λ s : finset β, (s.subtype p, s.subtype (λ i, ¬ p i))) at_top at_top :=
begin
  intro,
  simp only [mem_at_top_sets, ge_iff_le, prod.forall, prod.exists, prod.mk_le_mk, le_eq_subset,
             and_imp, filter.mem_map, set.mem_preimage, forall_exists_index],
  intros t u htu,
  refine ⟨t.map (embedding.subtype _) ∪ u.map (embedding.subtype _), λ s hs, htu _ _ _ _⟩,
  { rw ←finset.map_subtype_subtype _ t,
    exact subtype_mono (union_subset_left hs) },
  { rw ←finset.map_subtype_subtype _ u,
    convert subtype_mono (union_subset_right hs) }
end

-- lemma finset.at_top_subtype_prod (p : β → Prop) :
--   (at_top : _root_.filter (finset (subtype p) × finset (subtype (λ i, ¬ p i)))).map
--     (λ pq, (pq.1.map (embedding.subtype _)) ∪ (pq.2.map (embedding.subtype _))) =
--   (at_top : _root_.filter (finset β)) :=
-- begin
--   refine le_antisymm _ _,
-- end

-- #exit

lemma finset.disjoint_map_subtype_of_not {p q : β → Prop}
  (s : finset (subtype p)) (t : finset (subtype q)) (h : ∀ (b : subtype p), b ∈ s → ¬ q b) :
  disjoint (s.map (embedding.subtype _)) (t.map (embedding.subtype _)) :=
begin
  intros u hs ht x hx,
  have hp := hs hx,
  have hq := ht hx,
  simp only [finset.mem_map, embedding.coe_subtype, exists_prop, subtype.exists, subtype.coe_mk,
             exists_and_distrib_right, exists_eq_right] at hp hq,
  rcases hp with ⟨_, hp⟩,
  rcases hq with ⟨hq, -⟩,
  exact absurd hq (h _ hp)
end

lemma finset.disjoint_map_subtype (p : β → Prop)
  {s : finset (subtype p)} {t : finset (subtype (λ b, ¬ p b))} :
  disjoint (s.map (embedding.subtype _)) (t.map (embedding.subtype _)) :=
finset.disjoint_map_subtype_of_not _ _ (λ b _, by simp [b.prop])

-- lemma tendsto_prod_pos {f : β → ℝ} (hf : ∀ b, 0 ≤ f b) (hf' : ∀ b, f b ≤ 1 / 2)
--   (hf'' : tendsto f cofinite (𝓝 0)) :
--   ∃ (y : ℝ) (hy : 0 < y), tendsto (λ s : finset β, s.prod (λ b, 1 - f b)) at_top (𝓝 y) :=
-- begin
--   have hmono : antitone (λ s : finset β, s.prod (λ b, 1 - f b)) := sorry,
--   rcases (tendsto_of_antitone hmono) with hy|⟨y, hy⟩,
--   { rw tendsto_at_top_at_bot at hy,
--     obtain ⟨s, hs⟩ := hy 0,
--     specialize hs s le_rfl,
--     have : ∏ b in s, (1 - f b) = 0,
--     { refine le_antisymm hs (prod_nonneg (λ b _, _)),
--       rw sub_nonneg,
--       refine (hf' b).trans _,
--       norm_num },
--     rw prod_eq_zero_iff at this,
--     obtain ⟨b, hb, hb'⟩ := this,
--     rw sub_eq_zero at hb',
--     specialize hf' b,
--     norm_num [←hb'] at hf' b, },
--   { refine ⟨y, _, hy⟩,
--     contrapose! hy,
--     intro H,
--     -- rw tendsto_at_top_nhds at H,
--     have : (set.Ioo (y - 1) (-y⁻¹)) ∈ (𝓝 (0 : ℝ)),
--     sorry,
--     -- specialize H (set.Ioo (y - 1) (-y⁻¹)) _ is_open_Ioo,
--     -- sorry,
--     specialize hf'' this,
--     simp at hf'',
--     -- { simp [hy.trans_lt zero_lt_one] },
--     obtain ⟨s, hs⟩ := H,
--     rw summable_of_nonneg_of_le,


--   },
-- end
-- #exit

-- #exit
-- lemma exists_tendsto_prod_at_top_nhds [semilattice_sup β] [semilattice_sup γ] [nonempty β]
--   [nonempty γ] {f : β → ℝ} {g : γ → ℝ} {x : ℝ}
--   (h : tendsto (λ xy : β × γ, f xy.1 * g xy.2) (at_top ×ᶠ at_top) (𝓝 x)) :
--   ∃ (y z : ℝ), y * z = x ∧ tendsto f at_top (𝓝 y) ∧ tendsto g at_top (𝓝 z) :=
-- begin
--   rw prod_at_top_at_top_eq at h,
--   have fmono : monotone f := sorry,
--   have gmono : monotone g := sorry,
--   rcases (tendsto_of_monotone fmono) with hf|⟨y, hf⟩;
--   rcases (tendsto_of_monotone gmono) with hg|⟨z, hg⟩,
--   { refine absurd h (not_tendsto_nhds_of_tendsto_at_top _ _),
--     rw tendsto_at_top at hf hg ⊢,
--     intros b,
--     specialize hf (max b 1),
--     specialize hg (max b 1),
--     rw eventually_at_top at hf hg ⊢,
--     obtain ⟨y, hy⟩ := hf,
--     obtain ⟨z, hz⟩ := hg,
--     refine ⟨(y, z), _⟩,
--     rintro ⟨c, d⟩ ⟨hc, hd⟩,
--     exact le_mul_of_one_le_of_le_of_nonneg (le_of_max_le_right (hy _ hc))
--       (le_of_max_le_left (hz _ hd)) (zero_le_one.trans (le_of_max_le_right (hz _ hd))) },
--   { rcases lt_trichotomy 0 z with zpos|rfl|zneg,
--     { refine absurd h (not_tendsto_nhds_of_tendsto_at_top _ _),
--       rw ←prod_at_top_at_top_eq,
--       exact tendsto.at_top_mul zpos (hf.comp tendsto_fst) (hg.comp tendsto_snd) },
--     { sorry },
--     { refine absurd h (not_tendsto_nhds_of_tendsto_at_bot _ _),
--       rw ←prod_at_top_at_top_eq,
--       exact tendsto.at_top_mul_neg zneg (hf.comp tendsto_fst) (hg.comp tendsto_snd) }, },
--   { rcases lt_trichotomy 0 y with ypos|rfl|yneg,
--     { refine absurd h (not_tendsto_nhds_of_tendsto_at_top _ _),
--       rw ←prod_at_top_at_top_eq,
--       exact (tendsto.at_top_mul ypos (hg.comp tendsto_snd) (hf.comp tendsto_fst)).congr
--         (λ _, mul_comm _ _) },
--     { sorry },
--     { refine absurd h (not_tendsto_nhds_of_tendsto_at_bot _ _),
--       rw ←prod_at_top_at_top_eq,
--       exact (tendsto.at_top_mul_neg yneg (hg.comp tendsto_snd) (hf.comp tendsto_fst)).congr
--         (λ _, mul_comm _ _) } },
--   { refine ⟨_, _, _, hf, hg⟩,
--     have := (tendsto.prod_map hf hg),
--     rw tendsto_at_top at h,

--   },
--   -- by_cases hy : ∃ y, y ≠ 0 ∧ tendsto f at_top (𝓝 y),
--   -- { obtain ⟨y, hne, hy⟩ := hy,
--   --   -- refine ⟨y, x * y⁻¹, mul_div_cancel' _ hne, hy, _⟩,
--   --   -- rw tendsto_prod_iff at h,

--   -- },
-- end

-- #exit

-- lemma converges_prod.converges_prod_subset {f : β → ℝ} (h : converges_prod f) (s : set β)
--   (hf : monotone (λ s : finset β, (s.filter (λ i, is_unit (f i))).prod f) ∨
--         antitone (λ s : finset β, (s.filter (λ i, is_unit (f i))).prod f)) :
--   converges_prod (f ∘ coe : s → ℝ) :=
-- begin
--   obtain ⟨x, hx, ⟨x', hx'⟩, hx''⟩ := h,
--   have : tendsto (λ (tt : finset s × finset (sᶜ : set β)),
--     (∏ (b : s) in filter (λ (i : s), is_unit (f i)) tt.1, f b) *
--     (∏ (b : (sᶜ : set β)) in filter (λ (i : (sᶜ : set β)), is_unit (f i)) tt.2, f b))
--     (at_top ×ᶠ at_top) (𝓝 x'),
--   { rw prod_at_top_at_top_eq,
--     refine (hx'.comp (tendsto_union_map_subtype_at_top _)).congr _,
--     rintro ⟨p, q⟩,
--     simp only [comp_app, filter_congr_decidable, filter_union, filter_map],
--     rw [prod_union (finset.disjoint_map_subtype _), prod_subtype_map_embedding (λ _ _, rfl),
--         prod_subtype_map_embedding (λ _ _, rfl)],
--     congr },
--   -- simp only [←prod_filter_mul_prod_filter_not _ (∈ s)] at hx' { single_pass := tt },
--   -- have : ∀ (p : β → Prop) (t : finset β), (t.filter (λ i, is_unit (f i))).filter p =
--   --   (t.filter p).filter (λ i, is_unit (f i)),
--   -- { sorry },
--   -- rw ←prod_at_top_at_top_eq at hx',
--   -- simp_rw [this, this (λ b, b ∉ s)] at hx',
--   rw converges_prod_iff_mul_indicator,
--   cases hf,
--   { have hf' : monotone (λ t : finset β, (t.filter (λ i, is_unit (s.mul_indicator f i))).prod
--       (s.mul_indicator f)),
--     { sorry },
--     obtain ⟨y, hy⟩ := (tendsto_of_monotone hf').resolve_left _,
--     {

--       -- ideally, have this outside of the case, but unification doesn't work
--       refine converges_prod_of_tendsto_of_subset_finite hy _ (hx.inter_of_left s) _,
--       { refine tendsto_pos_ },
--       {  },
--     },
--     {  },
--   },
--   {  },
--   swap,
--   -- convert (or.resolve_left (tendsto_of_monotone _) _).some_spec,
-- end

-- #exit

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
    have := tendsto_finset_map_subtype_at_top p ((λ s, finset.prod s f) ∘ finset.filter _) at_top hy,
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

lemma finset.filter_sdiff_distrib (s t : finset β) (p : β → Prop) [decidable_pred p] :
  finset.filter p (s \ t) = s.filter p \ t.filter p :=
begin
  ext,
  simp only [mem_filter, mem_sdiff, not_and],
  tauto
end

lemma finset.map_sdiff_distrib (s t : finset β) (f : β ↪ γ) :
  finset.map f (s \ t) = s.map f \ t.map f :=
begin
  ext y,
  simp only [finset.mem_map, mem_sdiff, exists_prop, not_exists, not_and, and.comm, and.left_comm],
  split,
  { rintro ⟨x, hs, ht, rfl⟩,
    refine ⟨λ z hz, _, ⟨_, hs, rfl⟩⟩,
    rw f.apply_eq_iff_eq,
    rintro rfl,
    exact ht hz },
  { rintro ⟨H, x, hs, rfl⟩,
    refine ⟨_, hs, λ ht, _, rfl⟩,
    exact H _ ht (congr_arg _ rfl) }
end

lemma converges_prod.converges_prod_subtype_of_bounded_of_antitone {f : β → ℝ} (h : converges_prod f)
  (p : β → Prop) (hp : ∀ b, p b → (1 / 2) < f b)
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

lemma one_add_le_inv_one_sub_of_lt_one {x : ℝ} (hx : x < 1) :
  1 + x ≤ (1 - x)⁻¹ :=
begin
  have : 0 < 1 - x,
  { rwa [lt_sub_iff_add_lt, zero_add] },
  refine le_of_mul_le_mul_left _ this,
  rw mul_inv_cancel this.ne',
  ring_nf,
  rw [add_le_iff_nonpos_left, neg_nonpos],
  exact sq_nonneg x
end

lemma inv_one_add_two_mul_le_one_sub_of_nonneg_of_le_half {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) :
  (1 + 2 * x)⁻¹ ≤ 1 - x :=
begin
  have : 0 < 1 + 2 * x,
  { refine add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg two_pos.le hx) },
  refine le_of_mul_le_mul_left _ this,
  rw mul_inv_cancel this.ne',
  ring_nf,
  simp only [add_mul, neg_mul, one_mul, le_add_iff_nonneg_left, le_neg_add_iff_add_le, add_zero],
  refine mul_le_of_le_one_left hx _,
  refine (mul_le_mul_of_nonneg_left hx' zero_le_two).trans _,
  simp
end

/-- A product `∏ (1 - aₙ)` with positive terms `aₙ` is convergent iff the series `∑ aₙ` converges. -/
lemma converges_prod_one_sub_iff_summable {f : β → ℝ} (hf : ∀ b, 0 ≤ f b) :
  converges_prod (λ b, 1 - f b) ↔ summable f :=
begin
  have h2 : (2⁻¹ : ℝ) < 1 := by norm_num,
  have hapos : ∀ a : (f ⁻¹' set.Ioo (-2⁻¹) 2⁻¹ : set β), 0 < 1 - f a :=
    λ a, sub_pos_of_lt (a.prop.right.trans h2),
  have haunit : ∀ a : (f ⁻¹' set.Ioo (-2⁻¹) 2⁻¹ : set β), is_unit (1 - f a) :=
    λ a, is_unit_iff_ne_zero.mpr (hapos a).ne',
  have hapos' : ∀ a : (f ⁻¹' set.Ioo (-2⁻¹) 2⁻¹ : set β), 0 < 1 + f a :=
    λ a, add_pos_of_pos_of_nonneg zero_lt_one (hf _),
  have haunit' : ∀ a : (f ⁻¹' set.Ioo (-2⁻¹) 2⁻¹ : set β), is_unit (1 + f a) :=
    λ a, is_unit_iff_ne_zero.mpr (hapos' a).ne',
  have hapos2' : ∀ a : (f ⁻¹' set.Ioo (-2⁻¹) 2⁻¹ : set β), 0 < 1 + (2 • f) a :=
    λ a, add_pos_of_pos_of_nonneg zero_lt_one (smul_nonneg zero_le_two (hf _)),
  have haunit2' : ∀ a : (f ⁻¹' set.Ioo (-2⁻¹) 2⁻¹ : set β), is_unit (1 + 2 * f a) :=
    λ a, is_unit_iff_ne_zero.mpr $ by simpa using (hapos2' a).ne',
  have hmono : monotone (λ s : finset (f ⁻¹' set.Ioo (-2⁻¹) 2⁻¹ : set β),
    ∏ b in s.filter (λ i, is_unit (1 + f i)), (1 + f b)),
  { change (monotone ((λ s : finset (f ⁻¹' set.Ioo (-2⁻¹) 2⁻¹ : set β), ∏ b in s, (1 + f b)) ∘
      finset.filter _)),
    refine monotone.comp (monotone_prod_of_one_le' _) (monotone_filter_left _),
    simp [hf] },
  have hanti : antitone (λ s : finset (f ⁻¹' set.Ioo (-2⁻¹) 2⁻¹ : set β),
    ∏ b in s.filter (λ i, is_unit (1 - f i)), (1 - f b)),
  { change (antitone ((λ s : finset (f ⁻¹' set.Ioo (-2⁻¹) 2⁻¹ : set β), ∏ b in s, (1 - f b)) ∘
      finset.filter _)),
    refine antitone.comp_monotone (antitone_prod_of_le_one' _ (λ _, (hapos _).le))
      (monotone_filter_left _),
    simp [hf] },
  have npos : ∀ t : finset (f ⁻¹' set.Ioo (-2⁻¹) 2⁻¹ : set β),
    (0 : ℝ) < ∏ b in t.filter (λ i, is_unit (1 - f i)), (1 - f b),
  { intro,
    refine prod_pos _,
    simp only [set.mem_preimage, set.mem_Ioo, mem_filter, sub_pos, and_imp,
                set_coe.forall, subtype.coe_mk],
    intros _ hb _ _,
    exact hb.right.trans h2 },
  have ppos : ∀ t : finset (f ⁻¹' set.Ioo (-2⁻¹) 2⁻¹ : set β),
    (0 : ℝ) < ∏ b in t.filter (λ i, is_unit (1 + f i)), (1 + f b),
  { intro,
    refine zero_lt_one.trans_le (one_le_prod₀ _),
    simp only [le_add_iff_nonneg_right],
    exact λ _ _, hf _ },
  by_cases hlim : tendsto f cofinite (𝓝 0),
  { rw tendsto_nhds at hlim,
    specialize hlim (set.Ioo (-2⁻¹ : ℝ) 2⁻¹) is_open_Ioo _,
    { simp },
    split,
    { intros hs,
      rw ←converges_prod_one_add_iff_summable hf,
      refine converges_prod_of_converges_prod_cofinite_subset _ hlim _,
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
          simp only,
          clear ht key,
          induction t using finset.cons_induction_on with a t ha IH,
          { simp },
          { simp only [ha, filter_insert, haunit a, haunit' a, cons_eq_insert, if_true, prod_insert,
                       mem_filter, false_and, not_false_iff, mul_inv_rev],
            rw mul_comm,
            exact mul_le_mul IH (one_add_le_inv_one_sub_of_lt_one (a.prop.right.trans h2))
              (hapos' a).le (inv_nonneg_of_nonneg (npos _).le) } },
        { simp only [set.mem_preimage, set.mem_Ioo, one_div, and_imp],
          intros b hb hb',
          rw [lt_sub_comm, inv_eq_one_div, sub_half, ←inv_eq_one_div],
          exact hb' } },
      refine converges_prod_of_tendsto_of_subset_finite hy _ set.finite_empty _,
      { rw is_unit_iff_ne_zero,
        contrapose! hy,
        subst hy,
        intro hy,
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
      replace hs : summable (2 • f) := hs.const_smul _,
      rw ←converges_prod_one_add_iff_summable at hs, swap,
      { exact λ _, smul_nonneg zero_le_two (hf _) },
      rcases tendsto_of_antitone hanti with (hy|⟨y, hy⟩),
      { rw tendsto_at_top_at_bot_iff_of_antitone hanti at hy,
        obtain ⟨t, ht⟩ := hy (-1 : ℝ),
        simp only at ht,
        refine absurd (neg_one_lt_zero.trans_le _) ht.not_lt,
        exact prod_nonneg (λ _ _, (hapos _).le) },
      refine converges_prod_of_tendsto_of_subset_finite hy _ set.finite_empty _,
      { rw is_unit_iff_ne_zero,
        obtain ⟨_, -, ⟨x', hx'⟩, -⟩ := hs.converges_prod_subtype_of_one_le
            (∈ f ⁻¹' set.Ioo (-2⁻¹) 2⁻¹) _, swap,
        { intros,
          simpa using hf _ },
        have xpos : (0 : ℝ) < x',
        { refine lt_of_le_of_ne (ge_of_tendsto' hx' (λ t, _)) x'.ne_zero.symm,
          exact prod_nonneg (λ b _, add_nonneg zero_le_one (smul_nonneg zero_le_two (hf _))) },
        refine ((inv_pos_of_pos xpos).trans_le _).ne',
        refine le_of_tendsto_of_tendsto' ((real.tendsto_inv xpos.ne').comp hx') hy (λ t, _),
        simp only,
        induction t using finset.cons_induction_on with a t ha IH,
        { simp only [comp_app, filter_true_of_mem, not_mem_empty, is_empty.forall_iff,
                     implies_true_iff, prod_empty, inv_one] },
        { suffices : (∏ x in filter (λ i, is_unit (1 + (2 • f) ↑i)) t, (1 + (2 • f) ↑x))⁻¹ *
            (1 + 2 * f a)⁻¹ ≤ (1 - f a) * ∏ x in filter (λ i, is_unit (1 - f ↑i)) t, (1 - f ↑x),
          { simpa [ha, filter_insert, haunit a, haunit2' a] using this },
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

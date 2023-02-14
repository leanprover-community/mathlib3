import topology.algebra.infinite_sum

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

def converges_prod (f : β → α) : Prop := ∃ (a : α), has_prod f a

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

-- lemma converges_prod.tendsto_nhds_one {f : ℕ → ℝ} (hf : converges_prod f) :
--   tendsto f at_top (𝓝 1) :=
-- begin
--   obtain ⟨x, hf⟩ := hf,
--   have := has_prod_ratio hf,
--   refine (this.comp _).congr' _,
--   { exact λ b, (hf.finite_not_unit.to_finset, b) },
--   { rw eventually_eq,
--     refine hf.finite_not_unit.subset _,
--     intro s,
--     contrapose!,
--     have : filter (λ i : β, is_unit (f i)) hf.finite_not_unit.to_finset = ∅,
--     { ext,
--       simp },
--     simp [filter_insert, this] { contextual := tt } },
--   { simp only [tendsto_comap_iff, tendsto_at_top, eventually_cofinite, le_eq_subset,
--                set.finite.subset_to_finset],
--     intro s,
--     simp,
--     -- {x : β | ¬↑s ⊆ {b : β | ¬is_unit (f b)}}.finite
--     sorry -- this is false for infinite β, because the condition doesn't need x here
--     },
-- end
#exit


#exit

variables {f : β → α} {a : α}

lemma has_prod.is_unit (h : has_prod f a) : is_unit a := h.left
lemma has_prod.eventually_is_unit (h : has_prod f a) :
  ∀ᶠ b in cofinite, is_unit (f b) :=
h.right.left
lemma has_prod.tendsto (h : has_prod f a) :
  tendsto (λs:finset β, ∏ b in s, f b) at_top (𝓝 a) :=
h.right.right

end

section comm_group

variables [comm_group_with_zero α] [topological_space α]
variables {f : β → α} {a : α}

lemma has_prod.ne_zero (h : has_prod f a) : a ≠ 0 := h.is_unit.ne_zero

lemma has_prod.eventually_ne_zero (h : has_prod f a) :
  ∀ᶠ b in cofinite, f b ≠ 0 :=
h.eventually_is_unit.mono (λ _, is_unit.ne_zero)

end comm_group

section
variables [comm_monoid α] [topological_space α]

def converges (f : β → α) : Prop := ∃ a, has_prod f a
def converges_absolutely [has_add α] [has_abs α] (f : β → α) : Prop :=
  ∃ a, has_prod (λ b, 1 + |f b|) a

variables {f : β → α} {a : α}

-- lemma converges_iff_summable_log :
--   converges f ↔ summable (λ i, real.log (f i))

lemma converges_absolutely.converges [has_add α] [has_abs α] (h : converges_absolutely f) :
  converges f :=
begin
  obtain ⟨a, h⟩ := h,

end

-- lemma has_prod.is_unit (h : has_prod f a) : is_unit a := h.left
-- lemma has_prod.eventually_is_unit (h : has_prod f a) :
--   ∀ᶠ b in cofinite, is_unit (f b) :=
-- h.right.left
-- lemma has_prod.tendsto (h : has_prod f a) :
--   tendsto (λs:finset β, ∏ b in s, f b) at_top (𝓝 a) :=
-- h.right.right

end

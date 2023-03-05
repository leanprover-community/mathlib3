import topology.continuous_on
import topology.algebra.group_with_zero

variables {M M₀ G₀ : Type*} [monoid M] [monoid_with_zero M₀] [group_with_zero G₀]

noncomputable
def surj_units (x : M) [decidable (is_unit x)] : Mˣ := if h : is_unit x then h.unit else 1

lemma surj_units_apply_is_unit {x : M} [decidable (is_unit x)] (hx : is_unit x) :
  surj_units x = hx.unit :=
dif_pos hx

lemma surj_units_apply_not_is_unit {x : M} [decidable (is_unit x)] (hx : ¬ is_unit x) :
  surj_units x = 1 :=
dif_neg hx

@[simp] lemma coe_surj_units_apply_eq_iff {x : M} [decidable (is_unit (x : M))] :
  (surj_units x : M) = x ↔ is_unit x :=
begin
  by_cases h : is_unit x,
  { simp [surj_units_apply_is_unit h, h] },
  { simp only [surj_units_apply_not_is_unit h, h, units.coe_one, iff_false],
    contrapose! h,
    simp [←h] }
end

@[simp] lemma surj_units_apply_coe_units (x : Mˣ) [decidable (is_unit (x : M))] :
  surj_units (x : M) = x :=
by simp only [surj_units_apply_is_unit x.is_unit, is_unit.unit_of_coe_units]

lemma surj_units_apply_eq_mk0_apply {x : G₀} [decidable (is_unit x)] (hx : x ≠ 0) :
  surj_units x = units.mk0 _ hx :=
begin
  ext,
  simp [is_unit_iff_ne_zero, hx]
end

@[simp] lemma surj_units_apply_zero [decidable (is_unit (0 : M₀))] :
  surj_units (0 : M₀) = 1 :=
begin
  nontriviality M₀,
  exact surj_units_apply_not_is_unit not_is_unit_zero
end

variables {α : Type*} {β : Type*} {f : α → β}
open finset filter function classical
open_locale topology classical big_operators filter

instance [has_zero α] [has_mul α] [has_inv α] [topological_space α] [has_continuous_inv₀ α] :
  has_continuous_inv₀ αᵐᵒᵖ :=
⟨λ x hx, begin
  refine (mul_opposite.continuous_op.continuous_at).comp
    (mul_opposite.continuous_unop.continuous_at.inv₀ _),
  simp [hx]
end⟩

example {G₀ : Type*} [comm_group_with_zero G₀] [topological_space G₀]
  [has_continuous_inv₀ G₀]
  {f : β → G₀} {x : G₀} (hx : x ≠ 0)
  (h : tendsto (λ s : finset β, ∏ b in s.filter (λ i, f i ≠ 0), f b) at_top (𝓝 x)) :
  tendsto (λ s : finset β, ∏ b in s, surj_units (f b)) at_top (𝓝 (surj_units x)) :=
begin
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

lemma continuous_on_surj_units [topological_space G₀] [has_continuous_inv₀ G₀] :
  continuous_on (λ x : G₀, surj_units x) ({x : G₀ | is_unit x}) :=
begin
  intros x hx U,
  simp only [filter.mem_map, nhds_induced],
  simp only [units.embed_product_apply, units.coe_inv, mul_opposite.op_inv, mem_comap, exists_prop,
             forall_exists_index, and_imp, mem_nhds_prod_iff],
  intros V s hs t ht hst hVU,
  rw [surj_units_apply_is_unit hx, is_unit.unit_spec] at hs ht,
  refine mem_of_superset _ (set.preimage_mono hVU),
  rw set.preimage_preimage,
  rw [←mul_opposite.op_inv] at ht,
  have hne : mul_opposite.op x ≠ 0,
  { simpa [is_unit_iff_ne_zero] using hx },
  have ht' := (mul_opposite.continuous_op.tendsto _).inv₀ hne ht,
  rw filter.mem_map at ht',
  rw [nhds_within, mem_inf_iff_superset],
  refine ⟨_, inter_mem hs ht', _, mem_principal_self _, _⟩,
  intros y,
  simp only [set.mem_inter_iff, set.mem_preimage, set.mem_set_of_eq, units.embed_product_apply,
             units.coe_inv, mul_opposite.op_inv, and_imp],
  intros hxs hxt hy,
  simp_rw [surj_units_apply_is_unit hy, is_unit.unit_spec],
  refine hst _,
  simp [hxs, hxt]
end

example {G₀ : Type*} [comm_group_with_zero G₀] [topological_space G₀]
  [has_continuous_inv₀ G₀] [t1_space G₀]
  {f : β → G₀} {x : G₀} (hx : x ≠ 0)
  (h : tendsto (λ s : finset β, ∏ b in s.filter (λ i, f i ≠ 0), f b) at_top (𝓝 x)) :
  tendsto (λ s : finset β, ∏ b in s, surj_units (f b)) at_top (𝓝 (surj_units x)) :=
begin
  have : ∀ m : finset β, ∏ b in m.filter (λ i, f i ≠ 0), f b = ∏ b in m, surj_units (f b),
  { intro,
    rw prod_filter,
    refine prod_congr rfl (λ b _, _),
    split_ifs with hb hb,
    { simp [surj_units_apply_eq_mk0_apply hb] },
    { simp only [not_not] at hb,
      simp [hb] } },
  simp_rw this at h, clear this,
  have key : tendsto id (𝓝 x) (𝓝[set_of is_unit] x),
  { intro,
    simp only [nhds_within, mem_inf_iff_superset, mem_principal, exists_prop, map_id,
              forall_exists_index, and_imp],
    intros V hV W hW hVW,
    refine mem_of_superset _ hVW,
    refine inter_mem hV (mem_of_superset _ hW),
    have : set_of (is_unit : G₀ → Prop) = set.univ \ {0},
    { ext,
      simp [is_unit_iff_ne_zero] },
    rw [this, mem_nhds_iff],
    -- here is where I use that G₀ is T1
    refine ⟨_, subset_refl _, is_open_univ.sdiff is_closed_singleton, _⟩,
    simp [hx] },
  refine ((continuous_on_surj_units _ _).tendsto.comp (tendsto.comp key h)).congr _,
  { simp [←units.coe_prod, surj_units_apply_coe_units] },
  { simp [is_unit_iff_ne_zero, hx] }
end

import measure_theory.group.measure measure_theory.measure.lebesgue topology.basic
import analysis.normed_space.pointwise measure_theory.measure.haar



open add_monoid_hom measure_theory measure_theory.measure metric nnreal set
open_locale pointwise

section prereq


variables {G : Type*} [topological_space G] [group G] [topological_group G]

/-- Given a compact set `K` inside an open set `U`, there is a open neighborhood `V` of `1`
  such that `V * K ⊆ U`. -/
@[to_additive "Given a compact set `K` inside an open set `U`, there is a open neighborhood `V` of
`0` such that `V + K ⊆ U`."]
lemma compact_open_separated_mul_left {K U : set G} (hK : is_compact K) (hU : is_open U)
  (hKU : K ⊆ U) : ∃ V : set G, is_open V ∧ (1 : G) ∈ V ∧ V * K ⊆ U :=
begin
  let W : G → set G := λ x, (λ y, y * x) ⁻¹' U,
  have h1W : ∀ x, is_open (W x) := λ x, hU.preimage (continuous_mul_right x),
  have h2W : ∀ x ∈ K, (1 : G) ∈ W x := λ x hx, by simp only [mem_preimage, one_mul, hKU hx],
  choose V hV using λ x : K, exists_open_nhds_one_mul_subset ((h1W x).mem_nhds (h2W x.1 x.2)),
  let X : K → set G := λ x, (λ y, y * (x : G)⁻¹) ⁻¹' (V x),
  obtain ⟨t, ht⟩ : ∃ t : finset ↥K, K ⊆ ⋃ i ∈ t, X i,
  { refine hK.elim_finite_subcover X (λ x, (hV x).1.preimage (continuous_mul_right x⁻¹)) _,
    intros x hx, rw [mem_Union], use ⟨x, hx⟩, rw [mem_preimage], convert (hV _).2.1,
    simp only [mul_right_inv, subtype.coe_mk] },
  refine ⟨⋂ x ∈ t, V x, is_open_bInter (finite_mem_finset _) (λ x hx, (hV x).1), _, _⟩,
  { simp only [mem_Inter], intros x hx, exact (hV x).2.1 },
  rintro _ ⟨x, y, hx, hy, rfl⟩, simp only [mem_Inter] at hx,
  have := ht hy, simp only [mem_Union, mem_preimage] at this, rcases this with ⟨z, h1z, h2z⟩,
  have : x * (y * (z : G)⁻¹) ∈ W z := (hV z).2.2 (mul_mem_mul (hx z h1z) h2z),
  rw [mem_preimage] at this, convert this using 1, simp only [mul_assoc, inv_mul_cancel_right]
end

end prereq


variables (α : Type*) [group α] [topological_space α] [topological_group α] [t2_space α]
  [locally_compact_space α] [measurable_space α] [opens_measurable_space α] [borel_space α]
  [topological_space.second_countable_topology α] {μ : measure α} [is_haar_measure μ]


@[to_additive]
theorem steinhaus_theorem_mul (E : set α) (hE : measurable_set E) (hEpos : 0 < μ E)
  (hEtop : μ E ≠ ⊤) : ∃ (U : set α) , U ∈ nhds (1 : α) ∧ U ⊆ E / E :=
begin
  have hK := measurable_set.exists_lt_is_compact_of_ne_top hE hEtop hEpos,
  rcases hK with ⟨K, hKE, hK, hKpos⟩,
  have hKtop : μ K ≠ ⊤,
  { apply ne_top_of_le_ne_top hEtop,
    apply measure_mono hKE },
  have h2 : μ K ≠ 0,
  { exact ne_of_gt hKpos },
  have hU := set.exists_is_open_lt_add K hKtop h2,
  rcases hU with ⟨U, hUK, hU, hμUK⟩,
  have hV := compact_open_separated_mul_left hK hU hUK,
  rcases hV with ⟨V, hV, hVzero, hVKU⟩,
  have hv : ∀ (v : α), v ∈ V → ¬ disjoint ({v}* K) K,
  { intros v hv hKv,
    have hKvsub : {v} * K ∪ K ⊆ U,
    { apply set.union_subset _ hUK,
      apply subset_trans _ hVKU,
      apply set.mul_subset_mul _ (set.subset.refl K),
      simp only [set.singleton_subset_iff, hv] },
    replace hKvsub := @measure_mono _ _ μ _ _ hKvsub,
    have hcontr := lt_of_le_of_lt hKvsub hμUK,
    rw measure_union hKv (is_compact.measurable_set hK) at hcontr,
    have hKtranslate : μ ({v} * K) = μ K,
    { simp only [singleton_mul, image_mul_left, measure_preimage_mul] },
    rw [hKtranslate, lt_self_iff_false] at hcontr,
    assumption },
    use V,
    split,
    { exact is_open.mem_nhds hV hVzero },
    { intros v hvV,
      specialize hv v hvV,
      rw set.not_disjoint_iff at hv,
      rcases hv with ⟨x, hxK, hxvK⟩,
      rw set.mem_div,
      refine ⟨x, v⁻¹ * x, _, _, _⟩,
      { apply hKE hxvK },
      { apply hKE,
        simp only [singleton_mul, image_mul_left, mem_preimage] at hxK,
        exact hxK },
        simp only [div_eq_iff_eq_mul, ← mul_assoc, mul_right_inv, one_mul] }
end


/-!
# Cauchy's Functional Equation
-/

theorem cauchy_rational (f : ℝ →+ ℝ) :
  is_linear_map ℚ f := by exact ⟨map_add f, λ c x, add_monoid_hom.map_rat_cast_smul f ℝ ℝ c x⟩


lemma prereq_1 (f : ℝ → ℝ) :
  ∃ (r : ℝ), 0 < measure_space.volume (f⁻¹' (ball 0 r)) :=
begin
  have : measure_space.volume (f⁻¹' set.univ) = ⊤,
  simp only [set.preimage_univ, real.volume_univ],
  by_contra hf,
  push_neg at hf,
  simp at hf,
  have huniv := @measurable_set.univ ℝ (borel ℝ),
  have hrat : (⋃ (q : ℚ), ball (0 : ℝ) q) = set.univ,
  { ext,
    split,
    { simp only [set.mem_univ, implies_true_iff]},
    { intro hx,
      simp only [set.mem_Union, mem_ball_zero_iff],
      exact exists_rat_gt _}},
  rw ← hrat at this,
  simp at this,
  have htop : ⊤ ≤ ∑' (i : ℚ), measure_space.volume ((λ (q : ℚ), f ⁻¹' ball 0 ↑q) i),
  rw ← this,
  apply measure_Union_le (λ q : ℚ, f⁻¹' (ball (0 : ℝ) q)),
  simp only [hf, tsum_zero, nonpos_iff_eq_zero, ennreal.top_ne_zero] at htop,
  exact htop,
end

lemma prereq (f : ℝ →+ ℝ) (h : @measurable ℝ ℝ (real.measurable_space) (borel ℝ) f) :
  ∃ (C δ : ℝ), 0 < C ∧ 0 < δ ∧ ∀ (x : ℝ), x ∈ ball (0 : ℝ) δ → ∥f x∥ ≤ C :=
begin
  cases (prereq_1 f) with r hr,
  have hrm : measurable_set (f⁻¹' (ball 0 r)),
  { apply h,
    exact measurable_set_ball },
  -- error with instances
  -- rcases (steinhaus_theorem_add ℝ (f⁻¹' (ball 0 r)) hrm hr _) with ⟨U, hU0, hUr⟩,
  sorry,
  -- refine ⟨(2 * r), δ, _, hδ.1, λ x hx, _⟩,
  -- { sorry },
  -- { replace hx := set.mem_of_subset_of_mem hδ.2 hx,
  --   rw set.mem_vsub at hx,
  --   rcases hx with ⟨a, b, ha, hb, hab⟩,
  --   rw ← hab,
  --   simp only [vsub_eq_sub, map_sub],
  --   calc ∥f a - f b∥ ≤ ∥ f a ∥ + ∥ f b ∥ : norm_sub_le (f a) (f b)
  --     ... ≤ 2 * r : by linarith [(mem_ball_zero_iff).mp (set.mem_preimage.mp ha),
  --     (mem_ball_zero_iff).mp (set.mem_preimage.mp hb)]}
end

lemma prereq2 (f : ℝ →+ ℝ)
  (h : @measurable ℝ ℝ (borel ℝ) (borel ℝ) f) : continuous_at f 0 :=
begin
  rw continuous_at_iff,
  intros ε hε,
  simp only [gt_iff_lt, dist_zero_right, _root_.map_zero, exists_prop],
  have h1 := prereq f h,
  rcases h1 with ⟨C, δ, h1⟩,
  cases (exists_nat_gt (C / ε)) with n hn,
  use δ/n,
  split,
  { apply div_pos h1.2.1 (lt_trans (div_pos h1.1 hε) hn) },
  { intros x hxδ,
    have h2 : f (n • x) = n • f x, { exact map_nsmul f x n },
    have hnpos : 0 < (n : ℝ) := (lt_trans (div_pos h1.1 hε) hn),
    simp only [nsmul_eq_mul] at h2,
    simp only [mul_comm, ← div_eq_iff (ne.symm (ne_of_lt hnpos))] at h2,
    rw ← h2,
    replace hxδ : ∥ x * n ∥ < δ,
    { simp only [norm_mul, real.norm_coe_nat, ← lt_div_iff hnpos, hxδ], },
    norm_num,
    simp only [mem_ball_zero_iff] at h1,
    apply lt_of_le_of_lt (div_le_div (le_of_lt h1.1) (h1.2.2 (x * n) hxδ) hnpos (le_of_eq rfl)) _,
    simp only [div_lt_iff hnpos, mul_comm ε _, ← div_lt_iff hε, hn] }
end


lemma continuous_of_measurable (μ : measure ℝ) [is_add_haar_measure μ] (f : ℝ →+ ℝ)
  (h : @measurable ℝ ℝ (borel ℝ) (borel ℝ) f) : continuous f :=
  by exact uniform_continuous.continuous
    (uniform_continuous_of_continuous_at_zero f (prereq2 f h))

lemma real_eq_forall_pos_lt {a b : ℝ} : (∀ (ε : ℝ), 0 < ε → ∥ a - b ∥ < ε) → a = b :=
begin
  intro h,
  contrapose h,
  push_neg,
  use ∥ a - b ∥ / 2,
  split,
  { rw lt_div_iff (show 0 < (2 : ℝ), by norm_num),
    norm_num [sub_eq_zero, h] },
  { rw div_le_iff (show 0 < (2 : ℝ), by norm_num),
    simp only [mul_two, le_add_iff_nonneg_left, norm_nonneg] }
end

lemma is_linear_rat (f : ℝ →+ ℝ) : ∀ (q : ℚ), f q = f 1 * q :=
begin
  intro q,
  suffices h1 : f ((q : ℝ) • 1) = (q : ℝ) • f 1,
  { convert h1 using 1,
    { simp only [algebra.id.smul_eq_mul, mul_one], },
    { simp only [mul_comm, algebra.id.smul_eq_mul] }},
  { rw map_rat_cast_smul f ℝ ℝ q 1 }
end

lemma is_linear_of_continuous (f : ℝ →+ ℝ) (h : continuous f) : ∀ (x : ℝ), f x  = f 1 * x :=
begin
  have h1 := is_linear_rat f,
  intro x,
  apply real_eq_forall_pos_lt,
  by_contra hf,
  push_neg at hf,
  rcases hf with ⟨ε, hε, hf⟩,
  rw continuous_iff at h,
  specialize h x (ε/2) (by linarith [hε]),
  rcases h with ⟨δ, hδ, h⟩,
  by_cases hf1 : f 1 = 0,
  { simp only [hf1, zero_mul] at h1,
    simp only [hf1, zero_mul, sub_zero] at hf,
    cases (exists_rat_near x hδ) with q hq,
    specialize h q _,
    { simp only [dist_eq_norm', real.norm_eq_abs, hq] },
    simp only [h1, dist_zero_left] at h,
    linarith },
  { have hq : ∃ (q : ℚ), | x - ↑q | < min δ (ε / 2 / ∥f 1∥),
    apply exists_rat_near,
    { apply lt_min hδ,
      apply mul_pos,
      { linarith },
      { simp only [_root_.inv_pos, norm_pos_iff, ne.def, hf1, not_false_iff] }},
    cases hq with q hq,
    specialize h ↑q _,
    { simp only [dist_eq_norm', real.norm_eq_abs],
      apply lt_of_lt_of_le hq (min_le_left δ _) },
    rw [dist_eq_norm', h1] at h,
    suffices h2 : ∥ f x - f 1 * x ∥ < ε, by linarith [hf, h2],
    have h3 : ∥ f x - f 1 * q ∥ + ∥ f 1 * q - f 1 * x ∥ < ε,
    { have h4 : ∥ f 1 * q - f 1 * x ∥ < ε / 2,
      { replace hf1 : 0 < ∥ f 1 ∥ := by simpa [norm_pos_iff, ne.def],
        simp only [←mul_sub, norm_mul, mul_comm (∥f 1∥) _, ← lt_div_iff hf1],
        rw [← dist_eq_norm, dist_eq_norm', real.norm_eq_abs],
        apply lt_of_lt_of_le hq (min_le_right δ _) },
      linarith },
    apply lt_of_le_of_lt _ h3,
    apply le_trans _ (norm_add_le _ _),
    apply le_of_eq,
    congr,
    abel }
end

/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import measure_theory.lebesgue_measure
import group_theory.subgroup
import analysis.convex.basic
import measure_theory.haar_measure
import tactic

open measure_theory
variables {n : ℕ}
noncomputable theory

lemma trans_inv (v : fin n → ℝ) (S : set (fin n → ℝ)) (hS : measurable_set S) :
volume S = volume ((+ (-v)) '' S) :=
begin
  simp only [set.image_add_left, add_comm],
  set K : topological_space.positive_compacts (fin n → ℝ) := { val := ({x | ∀ n, x n ∈ set.Icc (0 : ℝ) 1} : set (fin n → ℝ)),
      property := begin sorry end },
  suffices : volume = measure.add_haar_measure K,
  { rw [this],
    simp only [set.image_add_right, neg_neg],
    simp_rw add_comm,
    rw [measure.is_add_left_invariant_add_haar_measure K v hS], },
  sorry,
end

/-- Blichfeldt's Principle --/
-- def L (n : ℕ) : add_subgroup (fin n → ℝ) := set.range (monoid_hom.comp {to_fun := (coe : ℤ → ℝ),
-- map_one' := int.cast_one, map_mul' := int.cast_mul})

-- instance : is_add_group_hom ((∘) (coe : ℤ → ℝ) : (fin n → ℤ) → (fin n → ℝ)) :=
-- { map_add := λ x y, by ext;
--   exact int.cast_add (x x_1) (y x_1), }
-- instance : is_add_subgroup (L n) := is_add_group_hom.range_add_subgroup ((∘) coe)
/- this can be generalized any range of a morphism is a subgroup -/

/- TODO decide wether to include measurablity in defn of a fundamental domain-/

structure fundamental_domain (L : add_subgroup (fin n → ℝ)) := /- this is _just_ a coset right? -/
  (F : set (fin n → ℝ))
  (hF : measurable_set F)
  (disjoint : ∀ (l : fin n → ℝ) (hl : l ∈ L) (h : l ≠ 0), disjoint ((+ l) '' F) F)
  (covers : ∀ (x : fin n → ℝ), ∃ (l : fin n → ℝ) (hl : l ∈ L), l + x ∈ F)

-- def cube_fund : fundamental_domain (L n) :=
-- { F := {v : fin n → ℝ | ∀ m : fin n, 0 ≤ v m ∧ v m < 1},
--   disjoint := λ l hl h x ⟨⟨a, ha, hx₁⟩, hx₂⟩, false.elim (h (begin
--     ext m, specialize ha m, specialize hx₂ m,
--     simp only [hx₁.symm, int.cast_zero, pi.add_apply, pi.zero_apply,
--       eq_self_iff_true, ne.def, zero_add] at ha hx₂ ⊢,
--     rcases hl with ⟨w, hw⟩,
--     rw ← hw at *,
--     dsimp,
--     have wlt : (↑(w m): ℝ) < 1 := by linarith,
--     have ltw : (-1 : ℝ) < w m := by linarith,
--     norm_cast,
--     have : w m < 1 := by exact_mod_cast wlt,
--     have : (-1 : ℤ) < w m := by exact_mod_cast ltw,
--     linarith,
--   end)),
--   covers := λ x, ⟨-(coe ∘ floor ∘ x), ⟨is_add_subgroup.neg_mem (set.mem_range_self (floor ∘ x)),
--   begin
--     intro,
--     simp only [int.cast_zero, pi.add_apply, pi.zero_apply, pi.neg_apply,
--       function.comp_app, zero_add, neg_add_lt_iff_lt_add],
--     split,
--     { linarith [floor_le (x m)], },
--     { linarith [lt_floor_add_one (x m)], }
--   end⟩⟩}

-- lemma cube_fund_volume : volume (cube_fund.F : set (fin n → ℝ)) = 1 :=
-- begin
--   dsimp [cube_fund],
--   rw volume_pi,
--   sorry,
-- end


lemma fundamental_domain.exists_unique {L : add_subgroup (fin n → ℝ)} (F : fundamental_domain L)
  (x : fin n → ℝ) : ∃! (p : L), x ∈ (+ (p : fin n → ℝ)) '' F.F :=
exists_unique_of_exists_of_unique
begin
  simp only [exists_prop, set.mem_preimage, set.image_add_right, exists_unique_iff_exists],
  obtain ⟨l, hl, lh⟩ := F.covers x,
  use -l,
  exact L.neg_mem hl,
  simpa [hl, add_comm] using lh,
end
begin
  rintro ⟨y₁_val, y₁_property⟩ ⟨y₂_val, y₂_property⟩ ⟨a, ha, rfl⟩ ⟨c, hc, h⟩,
  simp only [subtype.mk_eq_mk, add_subgroup.coe_mk] at *,
  rw [← sub_eq_iff_eq_add, add_sub_assoc] at h,
  have := F.disjoint (y₁_val - y₂_val) (L.sub_mem y₁_property y₂_property),
  contrapose! this,
  rw sub_ne_zero,
  simp only [this, true_and, neg_sub, not_false_iff, set.image_add_right, ne.def],
  intro hd,
  apply hd ⟨_, hc⟩,
  simpa [h],
end

/- TODO do I want to use this instance instead -/
-- instance {F : fundamental_domain $ L n} (hF : measurable_set F.F) :
--   measurable_space F.F := subtype.measurable_space

instance subtype.measure_space {V : Type*} [measure_space V] {p : set V} :
measure_space (subtype p) :=
{ volume := measure.comap subtype.val volume,
  ..subtype.measurable_space }

lemma volume_subtype_univ {V : Type*} [measure_space V] {p : set V} (hmp : measurable_set p) :
  @volume _ subtype.measure_space (set.univ : set (subtype p)) = volume p :=
begin
  dsimp [measure_space.volume],
  rw [measure.comap_apply _ subtype.val_injective, set.image_univ],
  congr,
  exact subtype.range_val,
  begin
    intros x hx,
    exact measurable_set.subtype_image hmp hx,
  end,
  exact measurable_set.univ,
end

/-instance {F : fundamental_domain $ L n} : measure_space F.F :=
{ measurable_set := λ s, measure_space.to_measurable_space.measurable_set (subtype.val '' s),
  measurable_set_empty := by rw [set.image_empty];
                          exact measure_space.to_measurable_space.is_measurable_empty,
  measurable_set_compl := λ S h, begin
    have : subtype.val '' (-S) = -(subtype.val '' S) ∩ F.F :=
    begin
      ext,
      simp only [not_exists, set.mem_image, set.mem_inter_eq, exists_and_distrib_right,
      exists_eq_right, subtype.exists,
 set.mem_compl_eq], /- TODO is this a logic lemma now ? -/
      split; intro; cases a,
      split,
      intro,
      exact a_h,
      exact a_w,
      exact Exists.intro a_right (a_left a_right),
    end,
    rw this,
    apply measurable_set.inter,
    exact measurable_space.is_measurable_compl _ _ h,
    exact hF,
  end,
  is_measurable_Union := λ f a, begin
    rw set.image_Union,
    exact measure_space.to_measurable_space.is_measurable_Union (λ (i : ℕ), subtype.val '' f i) a,
  end,
  μ := { measure_of := λ S, begin let l := (subtype.val '' S), exact _inst_1.μ.measure_of l, end,
  empty := _,
  mono := _,
  Union_nat := _,
  m_Union := sorry,
  trimmed := _ }
  }-/

lemma exists_diff_lattice_of_volume_le_volume (L : add_subgroup (fin n → ℝ)) [encodable L]
  {S : set (fin n → ℝ)} (hS : measurable_set S) (F : fundamental_domain L)
  (h : volume F.F < volume S) :
∃ (x y : fin n → ℝ) (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y), x - y ∈ L :=
begin
  suffices : ∃ (p₁ p₂ : L) (hne : p₁ ≠ p₂),
    (((+ ↑p₁) '' S ∩ F.F) ∩ ((+ ↑p₂) '' S ∩ F.F)).nonempty,
  begin
    rcases this with ⟨p₁, p₂, hne, u, ⟨⟨q₁, ⟨hS₁, ht₁⟩⟩, hu⟩, ⟨⟨q₂, ⟨hS₂, ht₂⟩⟩, hu⟩⟩,
    use [u - p₁, u - p₂],
    split,
    { rwa [← ht₁, add_sub_cancel], },
    split,
    { rwa [← ht₂, add_sub_cancel], },
    rw (by abel : u - p₁ - (u - p₂) = p₂ - p₁),
    split,
    { intro a,
      apply hne,
      rw sub_right_inj at a,
      exact subtype.eq a, },
    exact L.sub_mem p₂.mem p₁.mem,
  end,
  rw ← volume_subtype_univ F.hF at h,
  have := exists_nonempty_inter_of_measure_univ_lt_tsum_measure subtype.measure_space.volume
    (_ : (∀ p : L, measurable_set (λ a, ((+ ↑p) '' S) a.val : set F.F))) _,
  { rcases this with ⟨i, j, hij, t, ht⟩,
    use [i, j, hij, t],
    simp only [and_true, set.mem_inter_eq, set.mem_preimage, subtype.coe_prop],
    exact ht, },
  { intros,
    suffices : measurable_set (λ (a : ↥(F.F)), S ↑a),
    { simp only [set.image_add_right],
      refine measurable_set_preimage _ hS,
      refine measurable.add_const _ (-↑p),
      exact measurable_subtype_coe, },
    exact ⟨S, ⟨hS, rfl⟩⟩, },
  convert h,
  have : (∑' (i : L), volume ((+ (i : fin n → ℝ)) '' S ∩ F.F)) = volume S,
  { rw (_ : ∑' (i : L), volume ((+ ↑i) '' S ∩ F.F) =
        ∑' (i : L), volume ((+ (-↑i)) '' ((+ ↑i) '' S ∩ F.F))),
    { conv in (_ '' (_ ∩ _)) {
        rw [← set.image_inter (add_left_injective _), ← set.image_comp],
        simp only [add_neg_cancel_right, function.comp_app, set.image_id',
          comp_add_right, add_zero, add_right_neg, set.image_add_right, neg_neg],
        rw set.inter_comm, },
      rw ← measure_Union _ _,
      { congr,
        rw [← set.Union_inter, set.inter_eq_self_of_subset_right],
        convert set.subset_univ _,
        rw set.eq_univ_iff_forall,
        intros,
        rw set.mem_Union,
        rcases F.covers x with ⟨w, t, h_1_h⟩,
        use ⟨w, t⟩,
        rw [set.mem_preimage, subtype.coe_mk, add_comm],
        assumption, },
      { apply_instance, },
      { intros x y hxy,
        suffices : (disjoint on λ (i : ↥(L)), (λ (_x : fin n → ℝ), _x + -↑i) '' F.F) x y,
        { simp only [comp_add_right, add_zero, add_right_neg,
            set.image_add_right, neg_neg, set.image_id'] at this ⊢,
          rintros z ⟨⟨hzx, hzS⟩, ⟨hzy, hzS⟩⟩,
          apply this,
          simp only [set.mem_preimage, set.mem_inter_eq, set.inf_eq_inter],
          exact ⟨hzx, hzy⟩, },
        rintros t ⟨htx, hty⟩,
        simp only [set.mem_empty_eq, set.mem_preimage, set.bot_eq_empty,
          set.image_add_right, neg_neg] at htx hty ⊢,
        apply hxy,
        suffices : -x = -y, by simpa using this,
        apply exists_unique.unique (F.exists_unique t) _ _; simpa, },
    { intro l,
      apply measurable_set.inter _ hS,
      refine measurable_set_preimage _ F.hF,
      exact measurable_add_const ↑l, }, },
    { congr,
      ext1 l,
      rw [trans_inv (↑ l) _ _],
      apply measurable_set.inter _ F.hF, -- TODO is this a dup goal?
      simp only [set.image_add_right],
      refine measurable_set_preimage _ hS,
      exact measurable_add_const (-↑l), }, },
  convert this,
  ext1 l,
  simp only [set.image_add_right],
  dsimp only [subtype.measure_space],
  rw measure.comap_apply _ subtype.val_injective _ _ _,
  { congr,
    ext1 v,
    simp only [set.mem_preimage, set.mem_image, set.mem_inter_eq, exists_and_distrib_right,
      exists_eq_right, subtype.exists, subtype.coe_mk, subtype.val_eq_coe],
    cases l, cases h, cases h_h, cases h_w,
    simp only [set.image_add_right, add_subgroup.coe_mk, option.mem_def,
      ennreal.some_eq_coe, add_subgroup.coe_mk],
    split; { intros a, cases a, split; assumption, }, },
  { intros X hX,
    convert measurable_set.subtype_image F.hF hX, },
  { refine measurable_set_preimage _ hS,
    refine measurable.add_const _ (-↑l),
    exact measurable_subtype_coe, },
end

-- how to apply to the usual lattice
    -- exact set.countable.to_encodable (set.countable_range (function.comp coe)),

open ennreal
lemma exists_nonzero_lattice_of_two_dim_le_volume (L : add_subgroup (fin n → ℝ)) [encodable L]
  (F : fundamental_domain L) (S : set (fin n → ℝ)) (hS : measurable_set S)
  (h : volume F.F * 2 ^ n < volume S) (symmetric : ∀ x ∈ S, -x ∈ S) (convex : convex S) :
∃ (x : L) (h : x ≠ 0), ↑x ∈ S :=
begin
  have mhalf : measurable_set ((1/2 : ℝ) • S),
  { convert measurable_const_smul (2 : ℝ) hS,
    ext x,
    simp only [one_div, set.mem_preimage],
    exact mem_inv_smul_set_iff two_ne_zero S x, },
  have : volume ((1/2 : ℝ) • S) * 2^n = volume S,
  {
    suffices : volume ((1/2 : ℝ) • S) = (1 / 2)^n * volume S,
    { rw [this, mul_comm _ (volume S), mul_assoc, ← mul_pow, one_div,
        ennreal.inv_mul_cancel two_ne_zero two_ne_top, one_pow, mul_one], },

    sorry, -- rescaling measures
  },
  have h2 : volume F.F < volume ((1/2 : ℝ) • S),
  { rw ← ennreal.mul_lt_mul_right (pow_ne_zero n two_ne_zero') (pow_ne_top two_ne_top),
    convert h, },

  have : (1/2 : ℝ) • S + (1/2 : ℝ) • S = S,
  { ext,
    split; intro h,
    { rcases h with ⟨v₁, v₂, ⟨v₁₁, h₁₂, rfl⟩, ⟨v₂₁, h₂₂, rfl⟩, rfl⟩,
      have := convex h₁₂ h₂₂ (le_of_lt one_half_pos) (le_of_lt one_half_pos) (by linarith),
      rw [← inv_eq_one_div] at this,
      suffices hv : ∀ v : fin n → ℝ, v = (2⁻¹:ℝ) • (2 * v),
      { convert this;
        exact one_div 2, },
      intro,
      suffices : v = ((2⁻¹:ℝ) * 2) • v,
      { conv_lhs { rw this, },
        exact mul_assoc _ _ _, },
      norm_num, },
    { use [(1/2 : ℝ) • x, (1/2 : ℝ) • x],
      simp only [and_self_left],
      split,
      { exact set.smul_mem_smul_set h, },
      { rw ← add_smul,
        norm_num, }, }, },
  rw ← this,
  suffices : ∃ (x y : fin n → ℝ) (hx : x ∈ (1/2 : ℝ) • S) (hy : y ∈ (1/2 : ℝ) • S) (hne : x ≠ y),
    x - y ∈ L,
  { rcases this with ⟨x, y, hx, hy, hne, hsub⟩,
    use ⟨x - y, hsub⟩,
    split,
    { apply subtype.ne_of_val_ne,
      simp [sub_eq_zero, hne], },
    have : ∀ t ∈ (1/2 : ℝ) • S, -t ∈ (1/2 : ℝ) • S,
    { intros t ht,
      rcases ht with ⟨v, hv, rfl⟩,
      rw ← smul_neg,
      exact set.smul_mem_smul_set (symmetric _ hv), },
    use [x, -y, hx, this _ hy],
    refl, },
  { exact exists_diff_lattice_of_volume_le_volume L mhalf F h2, }
end

#lint

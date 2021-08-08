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

-- TODO change fin n to iota
open measure_theory
variables {n : ℕ}
noncomputable theory
section floris
/-
from floris
-/

open measure_theory measure_theory.measure topological_space set
#check real.map_volume_add_left
def is_add_left_invariant_real_volume : is_add_left_invariant (volume : measure ℝ) :=
by simp [← map_add_left_eq_self, real.map_volume_add_left]
def is_add_left_invariant_pi_volume (ι : Type*) [fintype ι] :
is_add_left_invariant (volume : measure (ι → ℝ)) :=
begin
  simp only [←map_add_left_eq_self],
  intro v,
  refine (pi_eq_generate_from (λ i, real.borel_eq_generate_from_Ioo_rat.symm)
    (λ i, real.is_pi_system_Ioo_rat) (λ i, real.finite_spanning_sets_in_Ioo_rat _)
    _).symm,
  intros s hS,
  simp only [exists_prop, mem_Union, mem_singleton_iff] at hS,
  choose a b H using hS,
  obtain rfl : s = λ i, Ioo (a i) (b i), from funext (λ i, (H i).2), replace H := λ i, (H i).1,
  simp only [real.volume_Ioo] at *,
  rw [map_apply, volume_pi],
  rw (_ : has_add.add v ⁻¹' set.pi set.univ (λ (i : ι), Ioo ↑(a i) ↑(b i))
    = set.pi set.univ (λ (i : ι), Ioo (↑(a i) - v i) (↑(b i) - v i))),
  rw pi_pi,
  have : ∀ (i : ι), measure_space.volume (Ioo (↑(a i) - v i) (↑(b i) - v i))
    = measure_space.volume (Ioo (↑(a i) : ℝ) (↑(b i))),
  { intro i,
    simp only [real.volume_Ioo],
    congr' 1,
    abel, },
  simp only [real.volume_Ioo] at this,
  simp [this],
  { exact (λ i, measurable_set_Ioo), },
  { ext,
    simp [sub_lt_iff_lt_add', lt_sub_iff_add_lt'], },
  { refine measurable_const_add v, },
  { rw measurable_set_pi (finite_univ.countable : (univ : set ι).countable),
    left,
    intros i hi,
    exact measurable_set_Ioo, },
end

def Icc01 : positive_compacts ℝ :=
⟨Icc 0 1, is_compact_Icc, by simp_rw [interior_Icc, nonempty_Ioo, zero_lt_one]⟩

def unit_cube (ι) [fintype ι] : positive_compacts (ι → ℝ) :=
⟨Icc 0 1, begin
  simp_rw [← pi_univ_Icc, pi.zero_apply, pi.one_apply],
  exact is_compact_univ_pi (λ i, is_compact_Icc),
end,
begin
  simp_rw [← pi_univ_Icc, pi.zero_apply, pi.one_apply],
  have : pi univ (λ i : ι, interior (Icc 0 1)) ⊆ interior (pi univ (λ i : ι, Icc (0 : ℝ) 1)),
  -- TODO weird dot notation fail?
  { rw subset_interior_iff_subset_of_open,
    { exact pi_mono (λ i hi, interior_subset), },
    { rw [interior_Icc],
      exact is_open_set_pi finite_univ (λ i hi, is_open_Ioo), }, },-- TODO general lemma?
  have ok : (pi univ (λ i : ι, interior (Icc (0 : ℝ) 1))).nonempty,
  { rw [interior_Icc, univ_pi_nonempty_iff],
    exact (λ i, nonempty_Ioo.mpr zero_lt_one) },
  exact nonempty.mono this ok,
end⟩

lemma haar_measure_eq_lebesgue_measure : add_haar_measure Icc01 = volume :=
begin
  convert (add_haar_measure_unique _ Icc01).symm,
  { simp [Icc01] },
  { apply_instance },
  { exact is_add_left_invariant_real_volume }
end

lemma pi_haar_measure_eq_lebesgue_measure (ι) [fintype ι] :
add_haar_measure (unit_cube ι) = volume :=
begin
  convert (add_haar_measure_unique _ (unit_cube ι)).symm,
  { rw [unit_cube],
    suffices : measure_space.volume (Icc (0 : ι → ℝ) 1) = 1,
    { rw [this, one_smul], },
    simp_rw [← pi_univ_Icc, pi.zero_apply, pi.one_apply],
    rw [volume_pi_pi, real.volume_Icc, sub_zero, ennreal.of_real_one, finset.prod_const_one],
    exact (λ i, measurable_set_Icc), },
  { apply_instance },
  { exact is_add_left_invariant_pi_volume ι }
end
end floris


/-- In the space `ι → ℝ`, Hausdorff measure coincides exactly with Lebesgue measure. -/
-- theorem hausdorff_measure_pi_real {ι : Type*} [fintype ι] [nonempty ι] :
--   (μH[fintype.card ι] : measure (ι → ℝ)) = volume :=
-- begin
--   classical,
--   -- it suffices to check that the two measures coincide on products of rational intervals
--   refine (pi_eq_generate_from (λ i, real.borel_eq_generate_from_Ioo_rat.symm)
--     (λ i, real.is_pi_system_Ioo_rat) (λ i, real.finite_spanning_sets_in_Ioo_rat _)
--     _).symm,
--   simp only [mem_Union, mem_singleton_iff],
--   -- fix such a product `s` of rational intervals, of the form `Π (a i, b i)`.
--   intros s hs,
--   choose a b H using hs,
--   obtain rfl : s = λ i, Ioo (a i) (b i), from funext (λ i, (H i).2), replace H := λ i, (H i).1,
--   apply le_antisymm _,
--   -- first check that `volume s ≤ μH s`
--   { have Hle : volume ≤ (μH[fintype.card ι] : measure (ι → ℝ)),
--     { refine le_hausdorff_measure _ _ ∞ ennreal.coe_lt_top (λ s h₁ h₂, _),
--       rw [ennreal.rpow_nat_cast],
--       exact real.volume_pi_le_diam_pow s },
--     rw [← volume_pi_pi (λ i, Ioo (a i : ℝ) (b i)) (λ i, measurable_set_Ioo)],
--     exact measure.le_iff'.1 Hle _ },
--   /- For the other inequality `μH s ≤ volume s`, we use a covering of `s` by sets of small diameter
--   `1/n`, namely cubes with left-most point of the form `a i + f i / n` with `f i` ranging between
--   `0` and `⌈(b i - a i) * n⌉`. Their number is asymptotic to `n^d * Π (b i - a i)`. -/
--   have Hpos' : 0 < fintype.card ι := fintype.card_pos_iff.2 ‹nonempty ι›,
--   have Hpos : 0 < (fintype.card ι : ℝ), by simp only [Hpos', nat.cast_pos],
--   have I : ∀ i, 0 ≤ (b i : ℝ) - a i := λ i, by simpa only [sub_nonneg, rat.cast_le] using (H i).le,
--   let γ := λ (n : ℕ), (Π (i : ι), fin ⌈((b i : ℝ) - a i) * n⌉₊),
--   haveI : ∀ n, encodable (γ n) := λ n, (fintype_pi ι (λ (i : ι), fin _)).out,
--   let t : Π (n : ℕ), γ n → set (ι → ℝ) :=
--     λ n f, set.pi univ (λ i, Icc (a i + f i / n) (a i + (f i + 1) / n)),
--   have A : tendsto (λ (n : ℕ), 1/(n : ℝ≥0∞)) at_top (𝓝 0),
--     by simp only [one_div, ennreal.tendsto_inv_nat_nhds_zero],
--   have B : ∀ᶠ n in at_top, ∀ (i : γ n), diam (t n i) ≤ 1 / n,
--   { apply eventually_at_top.2 ⟨1, λ n hn, _⟩,
--     assume f,
--     apply diam_pi_le_of_le (λ b, _),
--     simp only [real.ediam_Icc, add_div, ennreal.of_real_div_of_pos (nat.cast_pos.mpr hn), le_refl,
--       add_sub_add_left_eq_sub, add_sub_cancel', ennreal.of_real_one, ennreal.of_real_coe_nat] },
--   have C : ∀ᶠ n in at_top, set.pi univ (λ (i : ι), Ioo (a i : ℝ) (b i)) ⊆ ⋃ (i : γ n), t n i,
--   { apply eventually_at_top.2 ⟨1, λ n hn, _⟩,
--     have npos : (0 : ℝ) < n := nat.cast_pos.2 hn,
--     assume x hx,
--     simp only [mem_Ioo, mem_univ_pi] at hx,
--     simp only [mem_Union, mem_Ioo, mem_univ_pi, coe_coe],
--     let f : γ n := λ i, ⟨⌊(x i - a i) * n⌋₊,
--     begin
--       apply nat_floor_lt_nat_ceil_of_lt_of_pos,
--       { refine (mul_lt_mul_right npos).2 _,
--         simp only [(hx i).right, sub_lt_sub_iff_right] },
--       { refine mul_pos _ npos,
--         simpa only [rat.cast_lt, sub_pos] using H i }
--     end⟩,
--     refine ⟨f, λ i, ⟨_, _⟩⟩,
--     { calc (a i : ℝ) + ⌊(x i - a i) * n⌋₊ / n
--       ≤ (a i : ℝ) + ((x i - a i) * n) / n :
--           begin
--             refine add_le_add le_rfl ((div_le_div_right npos).2 _),
--             exact nat_floor_le (mul_nonneg (sub_nonneg.2 (hx i).1.le) npos.le),
--           end
--       ... = x i : by field_simp [npos.ne'] },
--     { calc x i
--       = (a i : ℝ) + ((x i - a i) * n) / n : by field_simp [npos.ne']
--       ... ≤ (a i : ℝ) + (⌊(x i - a i) * n⌋₊ + 1) / n :
--         add_le_add le_rfl ((div_le_div_right npos).2 (lt_nat_floor_add_one _).le) } },
--   calc μH[fintype.card ι] (set.pi univ (λ (i : ι), Ioo (a i : ℝ) (b i)))
--     ≤ liminf at_top (λ (n : ℕ), ∑' (i : γ n), diam (t n i) ^ ↑(fintype.card ι)) :
--       hausdorff_measure_le Hpos (set.pi univ (λ i, Ioo (a i : ℝ) (b i)))
--         (λ (n : ℕ), 1/(n : ℝ≥0∞)) A t B C
--   ... ≤ liminf at_top (λ (n : ℕ), ∑' (i : γ n), (1/n) ^ (fintype.card ι)) :
--     begin
--       refine liminf_le_liminf _ (by is_bounded_default),
--       filter_upwards [B],
--       assume n hn,
--       apply ennreal.tsum_le_tsum (λ i, _),
--       simp only [← ennreal.rpow_nat_cast],
--       exact ennreal.rpow_le_rpow (hn i) Hpos.le,
--     end
--   ... = liminf at_top (λ (n : ℕ), ∏ (i : ι), (⌈((b i : ℝ) - a i) * n⌉₊ : ℝ≥0∞) / n) :
--   begin
--     congr' 1,
--     ext1 n,
--     simp only [tsum_fintype, finset.card_univ, nat.cast_prod, one_div, fintype.card_fin,
--       finset.sum_const, nsmul_eq_mul, fintype.card_pi],
--     simp_rw [← finset.card_univ, ← finset.prod_const, ← finset.prod_mul_distrib],
--     refl,
--   end
--   ... = ∏ (i : ι), volume (Ioo (a i : ℝ) (b i)) :
--   begin
--     simp only [real.volume_Ioo],
--     apply tendsto.liminf_eq,
--     refine ennreal.tendsto_finset_prod_of_ne_top _ (λ i hi, _) (λ i hi, _),
--     { apply tendsto.congr' _ ((ennreal.continuous_of_real.tendsto _).comp
--         ((tendsto_nat_ceil_mul_div_at_top (I i)).comp tendsto_coe_nat_at_top_at_top)),
--       apply eventually_at_top.2 ⟨1, λ n hn, _⟩,
--       simp only [ennreal.of_real_div_of_pos (nat.cast_pos.mpr hn), comp_app,
--         ennreal.of_real_coe_nat] },
--     { simp only [ennreal.of_real_ne_top, ne.def, not_false_iff] }
--   end
-- end


lemma trans_inv (v : fin n → ℝ) (S : set (fin n → ℝ)) (hS : measurable_set S) :
volume S = volume ((+ (-v)) '' S) :=
begin
  simp only [set.image_add_left, add_comm],
  suffices : volume = measure.add_haar_measure (unit_cube _),
  { rw [this],
    simp only [set.image_add_right, neg_neg],
    simp_rw add_comm,
    rw [measure.is_add_left_invariant_add_haar_measure (unit_cube _) v hS], },
  rw pi_haar_measure_eq_lebesgue_measure,
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

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
def L (ι : Type*) : add_subgroup (ι → ℝ) := add_monoid_hom.range { to_fun := λ (f : ι → ℤ), (↑f : ι → ℝ),
  map_zero' := rfl,
  map_add' := assume x y, begin ext, rw [pi.add_apply], exact int.cast_add (x x_1) (y x_1), end }

/- this can be generalized any range of a morphism is a subgroup -/

/- TODO decide wether to include measurablity in defn of a fundamental domain-/

structure fundamental_domain {ι : Type*} (L : add_subgroup (ι → ℝ)) := /- this is _just_ a coset right? -/
  (F : set (ι → ℝ))
  (hF : measurable_set F)
  (disjoint : ∀ (l : ι → ℝ) (hl : l ∈ L) (h : l ≠ 0), disjoint ((+ l) '' F) F)
  (covers : ∀ (x : ι → ℝ), ∃ (l : ι → ℝ) (hl : l ∈ L), l + x ∈ F)

-- def cube_fund (ι : Type*) [fintype ι] : fundamental_domain (L ι) :=
-- { F := (unit_cube ι).val,
--   hF := begin simp [unit_cube], sorry end,
--   disjoint := λ l hl h x ⟨⟨a, ha, hx₁⟩, hx₂⟩, false.elim (h (begin
--     ext m, simp [unit_cube] at ha, specialize ha m, specialize hx₂ m,
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
#check measure.map
-- how to apply to the usual lattice
    -- exact set.countable.to_encodable (set.countable_range (function.comp coe)),
open measure_theory measure_theory.measure topological_space set
lemma smul_Ioo {a b r : ℝ} (hr : 0 < r) : r • Ioo a b = Ioo (r • a) (r • b) :=
begin
  ext,
  simp [mem_smul_set],
  split,
  { rintro ⟨ᾰ_w, ⟨ᾰ_h_left_left, ᾰ_h_left_right⟩, rfl⟩, split,
    exact (mul_lt_mul_left hr).mpr ᾰ_h_left_left, exact (mul_lt_mul_left hr).mpr ᾰ_h_left_right, },
  { rintro ⟨ᾰ_left, ᾰ_right⟩, use x / r, split, split, exact (lt_div_iff' hr).mpr ᾰ_left,
    exact (div_lt_iff' hr).mpr ᾰ_right, rw mul_div_cancel', exact ne_of_gt hr, }
end

lemma preimage_smul {α β : Type*} [field α] {a : α} (ha : a ≠ 0) [mul_action α β] {t : set β} :
(λ x, a • x) ⁻¹' t = a⁻¹ • t :=
begin
  ext,
  simp, split, work_on_goal 0 { intros ᾰ, fsplit, work_on_goal 1 { split, { assumption } } }, work_on_goal 1 { rintro ⟨ᾰ_w, ᾰ_h_left, rfl⟩, },
  { rw ← mul_smul,
    rw inv_mul_cancel ha,
    rw one_smul, },
  { rw ← mul_smul,
    rw mul_inv_cancel ha,
    rwa one_smul, },
end

lemma smul_pi (ι : Type*) {r : ℝ} (t : ι → set ℝ) :
r • pi (univ : set ι) t = pi (univ : set ι) (λ (i : ι), r • t i) :=
begin
  ext x,
  simp [mem_smul_set],
  split; intro h,
  { rcases h with ⟨h_w, h_h_left, rfl⟩,
    simp,
    intro i,
    use h_w i,
    split,
    exact h_h_left i,
    left,
    refl, },
  { use (λ i, classical.some (h i)), -- TODO is choice necessary?
    split,
    intro i,
    have := classical.some_spec (h i),
    exact this.left,
    ext i,
    have := classical.some_spec (h i),
    exact this.right, }
end

lemma rescale (ι : Type*) [fintype ι] {r : ℝ} (hr : 0 < r) :
measure.comap ((•) r) (volume : measure (ι → ℝ)) =
(ennreal.of_real r) ^ (fintype.card ι) • (volume : measure (ι → ℝ)) :=
begin
  have hrzero : ennreal.of_real r ≠ 0,
  { intro h,
    rw ennreal.of_real_eq_zero at h,
    linarith, },
  have hrtop : ennreal.of_real r ≠ ⊤, from ennreal.of_real_ne_top,
  suffices : (1 / ennreal.of_real r) ^ (fintype.card ι) •
    measure.comap ((•) r) (volume : measure (ι → ℝ)) = (volume : measure (ι → ℝ)),
  { conv_rhs { rw ← this, },
    simp only [one_div],
    rw [smul_smul, ← mul_pow, ennreal.mul_inv_cancel hrzero hrtop],
    simp only [one_pow, one_smul], },
  refine (pi_eq_generate_from (λ i, real.borel_eq_generate_from_Ioo_rat.symm)
    (λ i, real.is_pi_system_Ioo_rat) (λ i, real.finite_spanning_sets_in_Ioo_rat _)
    _).symm,
  intros s hS,
  simp only [exists_prop, mem_Union, mem_singleton_iff] at hS,
  choose a b H using hS,
  obtain rfl : s = λ i, Ioo (a i) (b i), from funext (λ i, (H i).2), replace H := λ i, (H i).1,
  simp only [real.volume_Ioo, one_div, algebra.id.smul_eq_mul, real.volume_Ioo, coe_smul,
    pi.smul_apply] at *,
  rw comap_apply,
  simp only [image_smul],
  rw smul_pi ι,
  conv in (r • _)
  { rw smul_Ioo hr, },
  erw pi_pi,
  simp only [algebra.id.smul_eq_mul, real.volume_Ioo],
  simp_rw [← mul_sub r],
  simp_rw ennreal.of_real_mul (hr.le),
  rw finset.prod_mul_distrib,
  simp only [finset.prod_const],
  rw [fintype.card, ← mul_assoc, ← mul_pow, ennreal.inv_mul_cancel hrzero hrtop, one_pow, one_mul],
  { intro i,
    exact measurable_set_Ioo, },
  { exact smul_left_injective (ι → ℝ) (ne_of_gt hr), },
  { intros S hS,
    rw [image_smul, ← inv_inv' r, ← preimage_smul (ne_of_gt (inv_pos.mpr hr))],
    apply measurable_set_preimage _ hS,
    rw measurable_const_smul_iff' (ne_of_gt (inv_pos.mpr hr)),
    exact measurable_id',
    apply_instance, },
  { exact measurable_set.univ_pi_fintype (λ i, measurable_set_Ioo), },
end

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
    have := rescale (fin n) (half_pos zero_lt_one),
    simp only [one_div, fintype.card_fin] at this,
    simp only [one_div],
    rw ← ennreal.of_real_inv_of_pos (by norm_num : 0 < (2 : ℝ)) at this,
    simp only [zero_le_one, of_real_one, of_real_bit0] at this,
    rw [← measure.smul_apply, ← this, comap_apply _ _ _ _ hS],
    simp,
    { exact smul_left_injective _ (by norm_num), },
    { intros S hS,
      rw [image_smul, ← preimage_smul _],
      apply measurable_set_preimage _ hS,
      rw measurable_const_smul_iff' _,
      exact measurable_id',
      apply_instance,
      apply_instance,
      exact two_ne_zero,
      exact two_ne_zero, },
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
      suffices : v = ((2⁻¹ : ℝ) * 2) • v,
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

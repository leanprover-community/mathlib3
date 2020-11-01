import measure_theory.lebesgue_measure
import group_theory.subgroup
import analysis.convex.basic
import tactic.equiv_rw

open measure_theory
variables {n : ℕ}
noncomputable theory
open_locale classical
local notation `doₐ` binders ` ←ₐ ` m ` ; ` t:(scoped p, m >>=ₐ p) := t

local notation `ret` := measure.dirac
--instance : measure_space ℝ := by apply_instance

lemma as {a : Type*} : a ≃ (fin 1 → a) := (equiv.fun_unique (fin 1) a).symm
def combine {n : ℕ} (a : fin n → ℝ) (b : ℝ) : (fin (n + 1) → ℝ)
| ⟨0, h⟩ := b
| ⟨n + 1, h⟩ := a ⟨n, (add_lt_add_iff_right 1).mp h⟩


noncomputable def finmap_measure : Π (n : ℕ) (h : 0 < n), measure (fin n → ℝ)
| 0 h := by exfalso; exact nat.not_succ_le_zero 0 h
| 1 _ := measure.of_measurable (λ a ha, volume ((λ x, a (λ _, x)) : set ℝ))  volume_empty
begin intros, simp at *,
  sorry,
end
| (k + 2) h := doₐ x ←ₐ (measure_space.μ : measure ℝ) ;
              doₐ xs ←ₐ (finmap_measure (k + 1) (nat.succ_pos k));
              ret (combine xs x)


variables [measure_space (fin n → ℝ)]
  (trans_inv : ∀ (v : fin n → ℝ) (S : set (fin n → ℝ)), volume S = volume ((+ v) '' S))

/-- Blichfeldt's Principle --/

def L (n : ℕ) : set (fin n → ℝ) := set.range ((∘) (coe : ℤ → ℝ))

instance : is_add_group_hom ((∘) (coe : ℤ → ℝ) : (fin n → ℤ) → (fin n → ℝ)) := { map_add := λ x y, by ext;
  exact int.cast_add (x x_1) (y x_1), }
instance : is_add_subgroup (L n) := is_add_group_hom.range_add_subgroup ((∘) coe)
/- this can be generalized any range of a morphism is a subgroup -/

/- TODO decide wether to include measurablity in defn of a fundamental domain-/

structure fundamental_domain (L : set (fin n → ℝ)) [is_add_subgroup L] := /- this is _just_ a coset right? -/
  (F : set (fin n → ℝ))
  (disjoint : ∀ (l : fin n → ℝ) (hl : l ∈ L) (h : l ≠ 0), disjoint ((+ l) '' F) F)
  (covers : ∀ (x : fin n → ℝ), ∃ (l : fin n → ℝ) (hl : l ∈ L), l + x ∈ F)

def cube_fund : fundamental_domain (L n) :=
{ F := {v : fin n → ℝ | ∀ m : fin n, 0 ≤ v m ∧ v m < 1},
  disjoint := λ l hl h x ⟨⟨a, ha, hx₁⟩, hx₂⟩, false.elim (h (begin
    ext m, specialize ha m, specialize hx₂ m,
    simp only [hx₁.symm, int.cast_zero, pi.add_apply, pi.zero_apply,
      eq_self_iff_true, ne.def, zero_add] at ha hx₂ ⊢,
    rcases hl with ⟨w, hw⟩,
    rw ← hw at *,
    dsimp,
    have wlt : (↑(w m): ℝ) < 1 := by linarith,
    have ltw : (-1 : ℝ) < w m := by linarith,
    norm_cast,
    have : w m < 1 := by exact_mod_cast wlt,
    have : (-1 : ℤ) < w m := by exact_mod_cast ltw,
    linarith,
  end)),
  covers := λ x, ⟨-(coe ∘ floor ∘ x), ⟨is_add_subgroup.neg_mem (set.mem_range_self (floor ∘ x)), begin
    intro,
    simp only [int.cast_zero, pi.add_apply, pi.zero_apply, pi.neg_apply,
      function.comp_app, zero_add, neg_add_lt_iff_lt_add],
    split,
    { linarith [floor_le (x m)], },
    { linarith [lt_floor_add_one (x m)], }
  end⟩⟩}

lemma cube_fund_volume : volume (cube_fund.F : set (fin n → ℝ)) = 1 :=
begin
  sorry,
end


-- not needed but nice
lemma fundamental_domain.exists_unique (F : fundamental_domain (L n)) (x : fin n → ℝ) :
  ∃! (p : fin n →  ℝ) (hp : p ∈ L n), x ∈ (+ p) '' F.F :=
begin
  apply exists_unique_of_exists_of_unique,
  simp,
  have := F.covers x,
  simp at this,
  convert this,
  ext,
  sorry,
  sorry,
end

/- TODO do I want to use this instance instead -/
instance {F : fundamental_domain $ L n} (hF : is_measurable F.F) :
  measurable_space F.F := subtype.measurable_space

instance subtype.measure_space {V : Type*} [measure_space V] {p : set V} (hmp : is_measurable p) : measure_space (subtype p) :=
{ μ := measure.of_measurable
  (λ x hx, volume (subtype.val '' x))
  (by rw [set.image_empty, volume_empty])
  (λ x hx hp, begin
    have : pairwise (disjoint on λ (i : ℕ), subtype.val '' x i) := /- TODO this is a lemma surely -/
    begin
      intros a b hab y hy,
      rcases hy with ⟨⟨Y, hY, as⟩, R, hR, rfl⟩,
      specialize hp a b hab,
      rw [subtype.val_injective as] at *,
      exact hp (set.mem_sep hY hR),
    end,

    rw set.image_Union,
    convert volume_Union this (λ i, is_measurable_subtype_image hmp (hx i)),
  end),
  ..subtype.measurable_space }

lemma volume_subtype_univ  {V : Type*} [measure_space V] {p : set V} (hmp : is_measurable p) :
  @volume _ (subtype.measure_space hmp) (set.univ : set (subtype p)) = volume p :=
begin
  dsimp [volume, measure_space.μ],
  rw measure.of_measurable_apply,
  simp only [set.image_univ, subtype.val_range],
  refl,
  exact is_measurable.univ,
end

/-instance {F : fundamental_domain $ L n} (hF : measure_space.to_measurable_space.is_measurable F.F) : measure_space F.F :=
{ is_measurable := λ s, measure_space.to_measurable_space.is_measurable (subtype.val '' s),
  is_measurable_empty := by rw [set.image_empty];
                          exact measure_space.to_measurable_space.is_measurable_empty,
  is_measurable_compl := λ S h, begin
    have : subtype.val '' (-S) = -(subtype.val '' S) ∩ F.F :=
    begin
      ext,
      simp only [not_exists, set.mem_image, set.mem_inter_eq, exists_and_distrib_right, exists_eq_right, subtype.exists,
 set.mem_compl_eq], /- TODO is this a logic lemma now ? -/
      split; intro; cases a,
      split,
      intro,
      exact a_h,
      exact a_w,
      exact Exists.intro a_right (a_left a_right),
    end,
    rw this,
    apply is_measurable.inter,
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

include trans_inv
lemma exists_diff_lattice_of_one_le_volume (S : set (fin n → ℝ)) (hS : is_measurable S)
  (F : fundamental_domain (L n)) (h : volume F.F < volume S) (hF : is_measurable F.F) :
  ∃ (x ∈ S) (y ∈ S) (hne : x ≠ y), (x - y) ∈ L n :=
begin
  suffices : ∃ (p₁ p₂ : L n) (hne : p₁ ≠ p₂),
    (((+ ↑p₁) '' S ∩ F.F) ∩ ((+ ↑p₂) '' S ∩ F.F)).nonempty,
  begin
    rcases this with ⟨p₁, p₂, hne, u, ⟨⟨q₁, ⟨hS₁, ht₁⟩⟩, hu⟩, ⟨⟨q₂, ⟨hS₂, ht₂⟩⟩, hu⟩⟩,
    use u - p₁,
    split,
    { rwa [← ht₁, add_sub_cancel],},
    use u - p₂,
    split,
    { rwa [← ht₂, add_sub_cancel],},
    rw (by abel : u - p₁ - (u - p₂) = p₂ - p₁),
    split,
    { intro, apply hne,
    rw sub_right_inj at a,
    exact subtype.eq a,},
    exact is_add_subgroup.sub_mem (L n) _ _ (subtype.mem p₂) (subtype.mem p₁),
  end,
  rw ← volume_subtype_univ at h,
  swap,
  sorry, -- TODO same typeclass issue as below

  let s := λ p : L n, (λ a, ((+ ↑p) '' S) a.1 : set ↥F.F),
  have := @exists_nonempty_inter_of_volume_univ_lt_tsum_volume (F.F) (subtype.measure_space (begin
    convert hF, sorry, end) : measure_space F.F) (L n) s _ _,
  {
    rcases this with ⟨i, j, hij, t, ht⟩,
    use [i, j, hij, t],
    simp only [subtype.val_prop', and_true, set.mem_image, set.mem_inter_eq],
    exact ht,
  },
  {
    intros,
    dsimp [s],
    suffices : is_measurable
      (λ (a : ↥(F.F)), (S) ↑a),
      { sorry,},
    exact ⟨S, ⟨hS, rfl⟩⟩
  },
  convert h,
  have : (∑' (i : L n), volume ((+ ↑i) '' S ∩ F.F)) = volume S :=
  begin
    rw (_ : (∑' (i : L n), volume ((+ ↑i) '' S ∩ F.F)) = ∑' (i : L n), volume ((+ (-↑i)) '' ((+ ↑i) '' S ∩ F.F))),
    rw ←volume_Union _ _,
    {
      congr,
      conv_lhs{
        congr,
        funext,
        rw ← set.image_inter (add_left_injective _),
        rw ← set.image_comp,
        simp [add_neg_cancel_right, function.comp_app, set.image_id'],
        rw set.inter_comm,
      },
      rw ← set.Union_inter,
      rw set.inter_eq_self_of_subset_right,
      convert set.subset_univ _,
      rw set.eq_univ_iff_forall,
      intros,
      rw set.mem_Union,
      rcases F.covers x with ⟨w, t, h_1_h⟩,
      use ⟨w, t⟩,
      rw [set.mem_image, subtype.coe_mk],
      use w + x,
      use h_1_h,
      exact add_sub_cancel' w x,
    },
    exact set.countable.to_encodable (set.countable_range (function.comp coe)),
    {
      intros x y hxy,
      suffices : (disjoint on λ (i : ↥(L n)), (λ (_x : fin n → ℝ), _x + -↑i) '' F.F) x y,
      {
        sorry,
      },
      intros t ht,
      have := F.disjoint (x-y) (is_add_subgroup.sub_mem (L n) _ _ (subtype.mem _) (subtype.mem _)) _,
      {
        sorry,

      },
      {
        intro, apply hxy,
        rw sub_eq_zero at a,
        exact subtype.eq a,
      },
    },
    {
      intro,
      suffices : is_measurable (S ∩ F.F),
      sorry, /- need assumption -/
      exact is_measurable.inter hS hF,
    },
    {congr,
    ext1,
    rw [trans_inv (-↑ x) _],},
  end,
  convert this,
  ext1,
  dsimp [s],
  dsimp [volume],
  refl,

end

lemma exists_nonzero_lattice_of_two_dim_le_volume (S : set (fin n → ℝ)) (h : 2^n < volume S)
  (symmetric : ∀ x ∈ S, -x ∈ S) (convex : convex S) :
  ∃ (x : L n) (h : x ≠ 0), ↑x ∈ S :=
begin
  let halfS : set (fin n → ℝ) := {v | 2 * v ∈ S},
  have : 2^n * volume halfS = volume S := begin
    sorry,
  end,
  have h2 : 1 < volume halfS := sorry,

  let C : set (fin n → ℝ) := { v | ∃ (v₁ v₂ : fin n → ℝ) (hv₁ : v₁ ∈ halfS) (hv₂ : v₂ ∈ halfS), v₁ + v₂ = v},
  have : C = S :=
  begin
    ext,
    split; intro h,
    { rcases h with ⟨v₁, v₂, h₁, h₂, rfl⟩,
      have := convex h₁ h₂ (le_of_lt one_half_pos) (le_of_lt one_half_pos) (by linarith),
      rw [one_div_eq_inv] at this,
      suffices hv : ∀ v : fin n → ℝ, v = (2⁻¹:ℝ) • (2 * v),
      { convert this,
        all_goals {exact hv _}, },
      intro,
      suffices : v = ((2⁻¹:ℝ) * 2) • v,
      { conv_lhs { rw this, },
        exact mul_assoc _ _ _, },
      norm_num, },
    { use [(2⁻¹ : ℝ) • x, (2⁻¹ : ℝ) • x],
      simp only [exists_prop, and_self_left, set.mem_set_of_eq],
      split,
      { convert h, ext,
        change 2 * (2⁻¹ * x x_1) = x x_1,
        norm_num, },
      { rw ← add_smul,
        norm_num, }, },
  end,
  rw ← this,
  suffices : ∃ (x : fin n → ℝ) (hx : x ∈ halfS) (y : fin n → ℝ) (hy : y ∈ halfS) (hne : x ≠ y), x - y ∈ L n,
  {
    rcases this with ⟨x, hx, y, hy, hne, hsub⟩,
    use ⟨x - y, hsub⟩,
    split,
    {
      intro, /- TODO this should be easier -/
      apply hne,
      rw subtype.ext at a,
      change x - y = 0 at a,
      rwa sub_eq_zero at a,
    },
    have : ∀ t ∈ halfS, -t ∈ halfS :=
    begin
      intros t ht,
      simp only [mul_neg_eq_neg_mul_symm, set.mem_set_of_eq],
      exact symmetric _ ht,
    end,
    use [x, -y, hx, this _ hy],
    refl,
  },
  {
    exact exists_diff_lattice_of_one_le_volume trans_inv halfS sorry cube_fund (by rw cube_fund_volume; exact h2) sorry,
  }
end

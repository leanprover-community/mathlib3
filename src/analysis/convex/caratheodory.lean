/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/
import analysis.convex.basic
import linear_algebra.finite_dimensional

universes u

open set finset
open_locale big_operators

lemma set.subset_subset_Union
  {E : Type*} {A : set E} {ι : Sort*} {f : ι → set E} (i : ι) (h : A ⊆ f i) : A ⊆ ⋃ (i : ι), f i :=
begin
  transitivity,
  exact h,
  exact subset_Union f i,
end

section
variables {β : Type*}

lemma filter_ne [decidable_eq β] (s : finset β) (b : β) :
  s.filter (λ a, b ≠ a) = s.erase b :=
by { ext, simp only [mem_filter, mem_erase, ne.def], cc, }

lemma filter_ne' [decidable_eq β] (s : finset β) (b : β) :
  s.filter (λ a, a ≠ b) = s.erase b :=
trans (filter_congr (λ _ _, ⟨ne.symm, ne.symm⟩)) (filter_ne s b)
end

open set finite_dimensional

variables {E : Type u} [decidable_eq E] [add_comm_group E] [vector_space ℝ E] [finite_dimensional ℝ E]

-- move this
@[simp] lemma finset.finite_to_set_to_finset {α : Type*} (s : finset α) :
  (finite_to_set s).to_finset = s :=
by { ext, rw [finite.mem_to_finset, mem_coe] }

-- a basic fact about convex hulls of finsets.
lemma convex_coefficients (t : finset E) (x : E) :
  x ∈ convex_hull (↑t : set E) ↔
    ∃ f : E → ℝ, (∀ y, 0 ≤ f y) ∧ (∑ e in t, f e = 1) ∧ (∑ e in t, f e • e = x) :=
begin
  rw finset.convex_hull_eq t,
  simp only [exists_prop, mem_coe, mem_set_of_eq],
  fsplit,
  { rintro ⟨w, w_nonneg, w_sum_one, w_center⟩,
    let w' : E → ℝ := λ z, if z ∈ t then w z else 0,
    refine ⟨w', _, _, _⟩,
    { intro y, dsimp [w'], split_ifs with h h,
      { exact w_nonneg y h },
      { refl }, },
    { rw [← w_sum_one, sum_congr rfl], intros x hx, exact if_pos hx, },
    { rw [← w_center, center_mass_eq_of_sum_1 t id w_sum_one, sum_congr rfl],
      intros x hx, simp only [w', if_pos hx, id] }, },
  { rintro ⟨w, w_nonneg, w_sum_one, w_center⟩,
    refine ⟨w, (λ e _, w_nonneg e), w_sum_one, _⟩,
    rwa center_mass_eq_of_sum_1 t id w_sum_one }
end

-- a lemma about finset
@[simp]
lemma coe_mem {α : Type*} {E : finset α} (x : (↑E : set α)) : ↑x ∈ E := x.2
@[simp]
lemma mk_coe {α : Type*} {E : finset α} (x : (↑E : set α)) {h} : (⟨↑x, h⟩ : (↑E : set α)) = x :=
by { apply subtype.eq, refl, }

-- a basic fact about linear algebra!
lemma exists_nontrivial_relation_of_dim_lt_card {t : finset E} (h : findim ℝ E < t.card) :
  ∃ f : E → ℝ, ∑ e in t, f e • e = 0 ∧ ∃ x ∈ t, f x ≠ 0 :=
begin
  have := mt finset_card_le_findim_of_linear_independent (by { simpa using h }),
  rw linear_dependent_iff at this,
  obtain ⟨s, g, sum, z, zm, nonzero⟩ := this,
  -- Now we have to extend `g` to all of `t`, then to all of `E`.
  let f : E → ℝ := λ x, if h : x ∈ t then if (⟨x, h⟩ : (↑t : set E)) ∈ s then g ⟨x, h⟩ else 0 else 0,
  -- and finally clean up the mess caused by the extension.
  refine ⟨f, _, _⟩,
  { dsimp [f],
    convert sum using 1,
    fapply sum_bij_ne_zero,
    { intros, exact ⟨a, H⟩, },
    { intros, dsimp,
      rw [dif_pos h₁] at h₂,
      by_contradiction w,
      rw [if_neg w] at h₂,
      simpa using h₂, },
    { intros _ _ _ _ _ _, exact subtype.mk.inj, },
    { intros, dsimp,
      use b,
      have h₁ : ↑b ∈ t := by simp,
      use h₁,
      rw [dif_pos h₁, if_pos],
      { fsplit; simp; assumption, },
      { simpa, } },
    { intros a h₁, dsimp, rw [dif_pos h₁], intro h₂,
      split_ifs with h₃,
      { refl, },
      { rw [if_neg h₃, zero_smul, eq_self_iff_true, not_true] at h₂, contradiction, }, }, },
  { refine ⟨z, z.2, _⟩, dsimp only [f], erw [dif_pos z.2, if_pos]; rwa [subtype.coe_eta] },
end

lemma exists_nontrivial_relation_sum_zero_of_dim_succ_lt_card
  {t : finset E} (h : findim ℝ E + 1 < t.card) :
  ∃ f : E → ℝ, ∑ e in t, f e • e = 0 ∧ ∑ e in t, f e = 0 ∧ ∃ x ∈ t, f x ≠ 0 :=
begin
  -- pick an element x₀ ∈ t,
  have card_pos : 0 < t.card := lt_trans (nat.succ_pos _) h,
  obtain ⟨x₀, m⟩ := (finset.card_pos.1 card_pos).bex,
  -- apply the previous lemma to the other xᵢ - x₀,
  let shift : E ↪ E := ⟨λ x, x - x₀, add_left_injective (-x₀)⟩,
  let t' := (t.erase x₀).map shift,
  have h' : findim ℝ E < t'.card,
  { simp only [t', card_map, finset.card_erase_of_mem m],
    exact nat.lt_pred_iff.mpr h, },
  -- to obtain a function `g`
  obtain ⟨g, gsum, x₁, x₁_mem, nz⟩ := exists_nontrivial_relation_of_dim_lt_card h',
  -- and then obtain `f` by translating back by `x₀`,
  -- and setting the value of `f` at `x₀` to ensure `∑ e in t, f e = 0`.
  let f : E → ℝ := λ z, if z = x₀ then - ∑ z in (t.erase x₀), g (z - x₀) else g (z - x₀),
  refine ⟨f, _ ,_ ,_⟩,
  { simp [f],
    conv_lhs { apply_congr, skip, rw [ite_smul], },
    rw [finset.sum_ite],
    conv { congr, congr, apply_congr, simp [filter_eq', m], },
    conv { congr, congr, skip, apply_congr, simp [filter_ne'], },
    rw [sum_singleton, neg_smul, add_comm, ←sub_eq_add_neg, sum_smul, ←sum_sub_distrib],
    simp [←smul_sub],
    change (∑ (x : E) in t.erase x₀, (λ e, g e • e) (shift x)) = 0,
    rw ←sum_map _ shift,
    exact gsum, },
  { rw [← insert_erase m, sum_insert (not_mem_erase x₀ t)],
    dsimp [f],
    rw [if_pos rfl],
    conv_lhs { congr, skip, apply_congr, skip, rw if_neg (show x ≠ x₀, from (mem_erase.mp H).1), },
    exact neg_add_self _, },
  { refine ⟨x₁ + x₀, _, _⟩,
    { rw mem_map at x₁_mem,
      rcases x₁_mem with ⟨x₁, x₁_mem, rfl⟩,
      rw mem_erase at x₁_mem,
      simp only [x₁_mem, sub_add_cancel, function.embedding.coe_fn_mk], },
    { simp only [f],
      split_ifs with hx₀ hx₀,
      { sorry },
      { simpa using nz, } } },
end

lemma exists_pos_of_sum_zero_of_exists_nonzero {F : Type*} [decidable_eq F] {t : finset F}
  (f : F → ℝ) (h₁ : ∑ e in t, f e = 0) (h₂ : ∃ x ∈ t, f x ≠ 0) :
  ∃ x ∈ t, 0 < f x :=
begin
  contrapose! h₁,
  obtain ⟨x, m, x_nz⟩ : ∃ x ∈ t, f x ≠ 0 := h₂,
  apply ne_of_lt,
  calc ∑ e in t, f e < ∑ e in t, 0 : by { apply sum_lt_sum h₁ ⟨x, m, lt_of_le_of_ne (h₁ x m) x_nz⟩ }
                 ... = 0           : by rw [sum_const, nsmul_zero],
end

lemma exists_relation_sum_zero_pos_coefficient {t : finset E} (h : findim ℝ E + 1 < t.card) :
  ∃ f : E → ℝ, ∑ e in t, f e • e = 0 ∧ ∑ e in t, f e = 0 ∧ ∃ x ∈ t, 0 < f x :=
begin
  obtain ⟨f, sum, total, nonzero⟩ := exists_nontrivial_relation_sum_zero_of_dim_succ_lt_card h,
  exact ⟨f, sum, total, exists_pos_of_sum_zero_of_exists_nonzero f total nonzero⟩,
end

namespace caratheodory

-- All the sorries here are very doable!
lemma mem_convex_hull_erase {t : finset E} (h : findim ℝ E + 1 < t.card) {x : E} (m : x ∈ convex_hull (↑t : set E)) :
  ∃ (y : (↑t : set E)), x ∈ convex_hull (↑(t.erase y) : set E) :=
begin
  obtain ⟨f, fpos, fsum, rfl⟩ := (convex_coefficients _ _).1 m, clear m,
  obtain ⟨g, gcombo, gsum, gpos⟩ := exists_relation_sum_zero_pos_coefficient h, clear h,
  let s := t.filter (λ z : E, 0 < g z),
  have : s.nonempty,
  { obtain ⟨x, hx, hgx⟩ : ∃ x ∈ t, 0 < g x := gpos,
    refine ⟨x, mem_filter.mpr ⟨hx, hgx⟩⟩, },
  obtain ⟨i₀, mem, w⟩ := s.exists_min_image (λ z, f z / g z) this,
  have hg : 0 < g i₀ := by { rw mem_filter at mem, exact mem.2 },
  have hi₀ : i₀ ∈ t := filter_subset _ mem,
  let k : E → ℝ := λ z, f z - (f i₀ / g i₀) * g z,
  have hk : k i₀ = 0 := by field_simp [k, ne_of_gt hg],
  have ksum : ∑ e in t.erase i₀, k e = 1,
  { calc ∑ e in t.erase i₀, k e = ∑ e in t, k e :
      by conv_rhs { rw [← insert_erase hi₀, sum_insert (not_mem_erase i₀ t), hk, zero_add], }
    ... = ∑ e in t, (f e - f i₀ / g i₀ * g e) : rfl
    ... = 1 : by rw [sum_sub_distrib, fsum, ← mul_sum, gsum, mul_zero, sub_zero] },
  refine ⟨⟨i₀, hi₀⟩, _⟩,
  { rw finset.convex_hull_eq,
    refine ⟨k, _, ksum, _⟩,
    { simp only [and_imp, sub_nonneg, mem_erase, ne.def, subtype.coe_mk],
      intros e hei₀ het,
      by_cases hes : e ∈ s,
      { have hge : 0 < g e := by { rw mem_filter at hes, exact hes.2 },
        rw ← le_div_iff hge,
        exact w _ hes, },
      { calc _ ≤ 0   : mul_nonpos_of_nonneg_of_nonpos _ _ -- prove two goals below
           ... ≤ f e : fpos e,
        { apply div_nonneg_of_nonneg_of_pos (fpos _) hg },
        { simpa [mem_filter, het] using hes }, } },
    { simp only [subtype.coe_mk, center_mass_eq_of_sum_1 _ id ksum, id],
      sorry }, },
end

lemma step (t : finset E) (h : findim ℝ E + 1 < t.card) :
  convex_hull (↑t : set E) = ⋃ (x : (↑t : set E)), convex_hull ↑(t.erase x) :=
begin
  apply set.subset.antisymm,
  { intros x m',
    obtain ⟨y, m⟩ := mem_convex_hull_erase h m',
    exact mem_Union.2 ⟨y, m⟩, },
  { convert Union_subset _,
    intro x,
    apply convex_hull_mono, simp, }
end

lemma shrink' (t : finset E) (k : ℕ) (h : t.card = findim ℝ E + 1 + k) :
  convex_hull (↑t : set E) ⊆
    ⋃ (t' : finset E) (w : t' ⊆ t) (b : t'.card ≤ findim ℝ E + 1), convex_hull ↑t' :=
begin
  induction k with k ih generalizing t,
  { apply subset_subset_Union t,
    apply subset_subset_Union (set.subset.refl _),
    exact subset_subset_Union (le_of_eq h) (subset.refl _), },
  rw step _ (by { rw h, simp, } : findim ℝ E + 1 < t.card),
  apply Union_subset,
  intro i,
  transitivity,
  { apply ih,
    rw [card_erase_of_mem, h, nat.pred_succ],
    exact i.2, },
  { apply Union_subset_Union,
    intro t',
    apply Union_subset_Union_const,
    exact λ h, set.subset.trans h (erase_subset _ _), }
end

lemma shrink (t : finset E) :
  convex_hull (↑t : set E) ⊆
    ⋃ (t' : finset E) (w : t' ⊆ t) (b : t'.card ≤ findim ℝ E + 1), convex_hull ↑t' :=
begin
  by_cases h : t.card ≤ findim ℝ E + 1,
  { apply subset_subset_Union t,
    apply subset_subset_Union (set.subset.refl _),
    exact subset_subset_Union h (set.subset.refl _), },
  simp at h,
  obtain ⟨k, w⟩ := le_iff_exists_add.mp (le_of_lt h), clear h,
  exact shrink' _ _ w,
end


end caratheodory

lemma caratheodory_le (s : set E) :
  convex_hull s ⊆ ⋃ (t : finset E) (w : ↑t ⊆ s) (b : t.card ≤ findim ℝ E + 1), convex_hull ↑t :=
begin
  -- First we replace `convex_hull s` with the union of the convex hulls of finite subsets.
  rw convex_hull_eq_union_convex_hull_finite_subsets,
  -- And prove the inclusion for each of those
  apply Union_subset,
  intro r,
  apply Union_subset,
  intro h,
  -- Second, for each convex hull of a finite subset, we shrink it
  transitivity,
  { apply caratheodory.shrink, },
  { -- After that it's just shuffling everything around.
    apply Union_subset,
    intro r',
    apply Union_subset,
    intro h',
    apply Union_subset,
    intro b',
    apply subset_subset_Union r',
    apply subset_subset_Union,
    exact subset.trans h' h,
    apply subset_Union _ b', },
end

/--
Carathéodory's convexity theorem.

The convex hull of a set `s` in ℝᵈ is the union of the convex hulls of the (d+1)-tuples in `s`.
-/
theorem caratheodory (s : set E) :
  convex_hull s = ⋃ (t : finset E) (w : ↑t ⊆ s) (b : t.card ≤ findim ℝ E + 1), convex_hull ↑t :=
begin
  apply set.subset.antisymm,
  apply caratheodory_le,
  convert Union_subset _,
  intro t,
  convert Union_subset _,
  intro ss,
  convert Union_subset _,
  intro b,
  exact convex_hull_mono ss,
end

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

Extended non-negative reals

TODO: base ennreal on nnreal!
-/
import algebra.ordered_group analysis.nnreal analysis.limits data.real.ennreal
noncomputable theory
open classical set lattice filter
local attribute [instance] prop_decidable
variables {α : Type*} {β : Type*}

local notation `∞` := ennreal.infinity

namespace ennreal
variables {a b c d : ennreal} {r p q : ℝ}

section topological_space
open topological_space

instance : topological_space ennreal :=
topological_space.generate_from {s | ∃a, s = {b | a < b} ∨ s = {b | b < a}}

instance : orderable_topology ennreal := ⟨rfl⟩

instance : t2_space ennreal := by apply_instance

instance : second_countable_topology ennreal :=
⟨⟨⋃q ≥ (0:ℚ), {{a : ennreal | a < of_real q}, {a : ennreal | of_real ↑q < a}},
  countable_bUnion (countable_encodable _) $ assume a ha, countable_insert (countable_singleton _),
  le_antisymm
    (generate_from_le $ λ s h, begin
      rcases h with ⟨a, hs | hs⟩;
      [ rw show s = ⋃q∈{q:ℚ | 0 ≤ q ∧ a < of_real q}, {b | of_real q < b},
           from set.ext (assume b, by simp [hs, @ennreal.lt_iff_exists_rat_btwn a b, and_assoc]),
        rw show s = ⋃q∈{q:ℚ | 0 ≤ q ∧ of_real q < a}, {b | b < of_real q},
           from set.ext (assume b, by simp [hs, @ennreal.lt_iff_exists_rat_btwn b a, and_comm, and_assoc])];
      { apply is_open_Union, intro q,
        apply is_open_Union, intro hq,
        exact generate_open.basic _ (mem_bUnion hq.1 $ by simp) }
    end)
    (generate_from_le $ by simp [or_imp_distrib, is_open_lt', is_open_gt'] {contextual := tt})⟩⟩

lemma continuous_of_real : continuous of_real :=
have ∀x:ennreal, is_open {a : ℝ | x < of_real a},
  from forall_ennreal.mpr ⟨assume r hr,
    by simp [of_real_lt_of_real_iff_cases]; exact is_open_and (is_open_lt' 0) (is_open_lt' r),
    by simp⟩,
have ∀x:ennreal, is_open {a : ℝ | of_real a < x},
  from forall_ennreal.mpr ⟨assume r hr,
    by simp [of_real_lt_of_real_iff_cases]; exact is_open_and is_open_const (is_open_gt' r),
    by simp [is_open_const]⟩,
continuous_generated_from $ begin simp [or_imp_distrib, *] {contextual := tt} end

lemma tendsto_of_real : tendsto of_real (nhds r) (nhds (of_real r)) :=
continuous_iff_tendsto.mp continuous_of_real r

lemma tendsto_of_ennreal (hr : 0 ≤ r) : tendsto of_ennreal (nhds (of_real r)) (nhds r) :=
tendsto_orderable_unbounded (no_top _) (no_bot _) $
assume l u hl hu,
by_cases
  (assume hr : r = 0,
    have hl : l < 0, by rw [hr] at hl; exact hl,
    have hu : 0 < u, by rw [hr] at hu; exact hu,
    have nhds (of_real r) = (⨅l (h₂ : 0 < l), principal {x | x < l}),
      from calc nhds (of_real r) = nhds ⊥ : by simp [hr]; refl
        ... = (⨅u (h₂ : 0 < u), principal {x | x < u}) : nhds_bot_orderable,
    have {x | x < of_real u} ∈ (nhds (of_real r)).sets,
      by rw [this];
      from mem_infi_sets (of_real u) (mem_infi_sets (by simp *) (subset.refl _)),
    ((nhds (of_real r)).sets_of_superset this $ forall_ennreal.mpr $
        by simp [le_of_lt, hu, hl] {contextual := tt}; exact assume p hp _, lt_of_lt_of_le hl hp))
  (assume hr_ne : r ≠ 0,
    have hu0 : 0 < u, from lt_of_le_of_lt hr hu,
    have hu_nn: 0 ≤ u, from le_of_lt hu0,
    have hr' : 0 < r, from lt_of_le_of_ne hr hr_ne.symm,
    have hl' : ∃l, l < of_real r, from ⟨0, by simp [hr, hr']⟩,
    have hu' : ∃u, of_real r < u, from ⟨of_real u, by simp [hr, hu_nn, hu]⟩,
    begin
      rw [mem_nhds_unbounded hu' hl'],
      existsi (of_real l), existsi (of_real u),
      simp [*, of_real_lt_of_real_iff_cases, forall_ennreal] {contextual := tt}
    end)

lemma nhds_of_real_eq_map_of_real_nhds {r : ℝ} (hr : 0 ≤ r) :
  nhds (of_real r) = (nhds r).map of_real :=
have h₁ : {x | x < ∞} ∈ (nhds (of_real r)).sets,
  from mem_nhds_sets (is_open_gt' ∞) of_real_lt_infty,
have h₂ : {x | x < ∞} ∈ ((nhds r).map of_real).sets,
  from mem_map.mpr $ univ_mem_sets' $ assume a, of_real_lt_infty,
have h : ∀x<∞, ∀y<∞, of_ennreal x = of_ennreal y → x = y,
  by simp [forall_ennreal] {contextual:=tt},
le_antisymm
  (by_cases
    (assume (hr : r = 0) s (hs : {x | of_real x ∈ s} ∈ (nhds r).sets),
      have hs : {x | of_real x ∈ s} ∈ (nhds (0:ℝ)).sets, from hr ▸ hs,
      let ⟨l, u, hl, hu, h⟩ := (mem_nhds_unbounded (no_top 0) (no_bot 0)).mp hs in
      have nhds (of_real r) = nhds ⊥, by simp [hr]; refl,
      begin
        rw [this, nhds_bot_orderable],
        apply mem_infi_sets (of_real u) _,
        apply mem_infi_sets (zero_lt_of_real_iff.mpr hu) _,
        simp [set.subset_def],
        intro x, rw [lt_iff_exists_of_real],
        simp [le_of_lt hu] {contextual := tt},
        exact assume p hp _ hpu, h _ (lt_of_lt_of_le hl hp) hpu
      end)
    (assume : r ≠ 0,
      have hr' : 0 < r, from lt_of_le_of_ne hr this.symm,
      have h' : map (of_ennreal ∘ of_real) (nhds r) = map id (nhds r),
        from map_cong $ (nhds r).sets_of_superset (mem_nhds_sets (is_open_lt' 0) hr') $
          assume r hr, by simp [le_of_lt hr, (∘)],
      le_of_map_le_map_inj' h₁ h₂ h $ le_trans (tendsto_of_ennreal hr) $ by simp [h']))
  tendsto_of_real

lemma nhds_of_real_eq_map_of_real_nhds_nonneg {r : ℝ} (hr : 0 ≤ r) :
  nhds (of_real r) = (nhds r ⊓ principal {x | 0 ≤ x}).map of_real :=
by rw [nhds_of_real_eq_map_of_real_nhds hr];
from by_cases
  (assume : r = 0,
    le_antisymm
      (assume s (hs : {a | of_real a ∈ s} ∈ (nhds r ⊓ principal {x | 0 ≤ x}).sets),
        let ⟨t₁, ht₁, t₂, ht₂, ht⟩ := mem_inf_sets.mp hs in
        show {a | of_real a ∈ s} ∈ (nhds r).sets,
          from (nhds r).sets_of_superset ht₁ $ assume a ha,
          match le_total 0 a with
          | or.inl h := have a ∈ t₂, from ht₂ h, ht ⟨ha, this⟩
          | or.inr h :=
            have r ∈ t₁ ∩ t₂, from ⟨mem_of_nhds ht₁, ht₂ (le_of_eq ‹r = 0›.symm)⟩,
            have of_real 0 ∈ s, from ‹r = 0› ▸ ht this,
            by simp [of_real_of_nonpos h]; assumption
          end)
      (map_mono inf_le_left))
  (assume : r ≠ 0,
    have 0 < r, from lt_of_le_of_ne hr this.symm,
    have nhds r ⊓ principal {x : ℝ | 0 ≤ x} = nhds r,
      from inf_of_le_left $ le_principal_iff.mpr $ le_mem_nhds this,
    by simp [*])

instance : topological_add_monoid ennreal :=
have hinf : ∀a, tendsto (λ(p : ennreal × ennreal), p.1 + p.2) ((nhds ∞).prod (nhds a)) (nhds ⊤),
begin
  intro a,
  rw [nhds_top_orderable],
  apply tendsto_infi.2 _, intro b,
  apply tendsto_infi.2 _, intro hb,
  apply tendsto_principal.2 _,
  revert b,
  simp [forall_ennreal],
  exact assume r hr, mem_prod_iff.mpr ⟨
    {a | of_real r < a}, mem_nhds_sets (is_open_lt' _) of_real_lt_infty,
    univ, univ_mem_sets, assume ⟨c, d⟩ ⟨hc, _⟩, lt_of_lt_of_le hc $ le_add_right $ le_refl _⟩
end,
have h : ∀{p r : ℝ}, 0 ≤ p → 0 ≤ r → tendsto (λp:ennreal×ennreal, p.1 + p.2)
    ((nhds (of_real r)).prod (nhds (of_real p))) (nhds (of_real (r + p))),
  from assume p r hp hr,
  begin
    rw [nhds_of_real_eq_map_of_real_nhds_nonneg hp, nhds_of_real_eq_map_of_real_nhds_nonneg hr,
      prod_map_map_eq, ←prod_inf_prod, prod_principal_principal, ←nhds_prod_eq],
    exact tendsto_map' (tendsto_cong
      (tendsto_le_left inf_le_left $ tendsto_add'.comp tendsto_of_real)
      (mem_inf_sets_of_right $ mem_principal_sets.mpr $ by simp [subset_def, (∘)] {contextual:=tt}))
  end,
have ∀{a₁ a₂ : ennreal}, tendsto (λp:ennreal×ennreal, p.1 + p.2) (nhds (a₁, a₂)) (nhds (a₁ + a₂)),
  from forall_ennreal.mpr ⟨assume r hr, forall_ennreal.mpr
    ⟨assume p hp, by simp [*, nhds_prod_eq]; exact h _ _,
      begin
        rw [nhds_prod_eq, prod_comm],
        apply tendsto_map' _,
        simp [(∘)],
        exact hinf _
      end⟩,
    by simp [nhds_prod_eq]; exact hinf⟩,
⟨continuous_iff_tendsto.mpr $ assume ⟨a₁, a₂⟩, this⟩

protected lemma tendsto_mul : ∀{a b : ennreal}, b ≠ 0 → tendsto ((*) a) (nhds b) (nhds (a * b)) :=
forall_ennreal.mpr $ and.intro
  (assume p hp, forall_ennreal.mpr $ and.intro
    (assume r hr hr0,
      have r ≠ 0, from assume h, by simp [h] at hr0; contradiction,
      have 0 < r, from lt_of_le_of_ne hr this.symm,
      have tendsto (λr, of_real (p * r)) (nhds r ⊓ principal {x : ℝ | 0 ≤ x}) (nhds (of_real (p * r))),
        from tendsto.comp (tendsto_mul tendsto_const_nhds $ tendsto_id' inf_le_left) tendsto_of_real,
      begin
        rw [nhds_of_real_eq_map_of_real_nhds_nonneg hr, of_real_mul_of_real hp hr],
        apply tendsto_map' (tendsto_cong this $ mem_inf_sets_of_right $ mem_principal_sets.mpr _),
        simp [subset_def, (∘), hp] {contextual := tt}
      end)
    (assume _, by_cases
      (assume : p = 0,
        tendsto_cong tendsto_const_nhds $
        (nhds ∞).sets_of_superset (mem_nhds_sets (is_open_lt' _) (@of_real_lt_infty 1)) $
        by simp [this])
      (assume p0 : p ≠ 0,
        have p_pos : 0 < p, from lt_of_le_of_ne hp p0.symm,
        suffices tendsto ((*) (of_real p)) (nhds ⊤) (nhds ⊤), { simpa [hp, p0] },
        by rw [nhds_top_orderable];
        from (tendsto_infi.2 $ assume l, tendsto_infi.2 $ assume hl,
          let ⟨q, hq, hlq, _⟩ := ennreal.lt_iff_exists_of_real.mp hl in
          tendsto_infi' (of_real (q / p)) $ tendsto_infi' of_real_lt_infty $ tendsto_principal_principal.2 $
          forall_ennreal.mpr $ and.intro
            begin
              have : ∀r:ℝ, 0 < r → q / p < r → q < p * r ∧ 0 < p * r,
                from assume r r_pos qpr,
                have q < p * r,
                  from calc q = (q / p) * p : by rw [div_mul_cancel _ (ne_of_gt p_pos)]
                    ... < r * p : mul_lt_mul_of_pos_right qpr p_pos
                    ... = p * r : mul_comm _ _,
                ⟨this, mul_pos p_pos r_pos⟩,
              simp [hlq, hp, of_real_lt_of_real_iff_cases, this] {contextual := tt}
            end
            begin simp [hp, p0]; exact hl end))))
  begin
    assume b hb0,
    have : 0 < b, from lt_of_le_of_ne ennreal.zero_le hb0.symm,
    suffices : tendsto ((*) ∞) (nhds b) (nhds ∞), { simpa [hb0] },
    apply (tendsto_cong tendsto_const_nhds $
      (nhds b).sets_of_superset (mem_nhds_sets (is_open_lt' _) this) _),
    { assume c hc,
      have : c ≠ 0, from assume h, by simp [h] at hc; contradiction,
      simp [this] }
  end

lemma supr_of_real {s : set ℝ} {a : ℝ} (h : is_lub s a) : (⨆a∈s, of_real a) = of_real a :=
suffices Sup (of_real '' s) = of_real a, by simpa [Sup_image],
is_lub_iff_Sup_eq.mp $ is_lub_of_is_lub_of_tendsto
  (assume x _ y _, of_real_le_of_real) h (ne_empty_of_is_lub h)
  (tendsto.comp (tendsto_id' inf_le_left) tendsto_of_real)

lemma infi_of_real {s : set ℝ} {a : ℝ} (h : is_glb s a) : (⨅a∈s, of_real a) = of_real a :=
suffices Inf (of_real '' s) = of_real a, by simpa [Inf_image],
is_glb_iff_Inf_eq.mp $ is_glb_of_is_glb_of_tendsto
  (assume x _ y _, of_real_le_of_real) h (ne_empty_of_is_glb h)
  (tendsto.comp (tendsto_id' inf_le_left) tendsto_of_real)

lemma Inf_add {s : set ennreal} : Inf s + a = ⨅b∈s, b + a :=
by_cases
  (assume : s = ∅, by simp [this, ennreal.top_eq_infty])
  (assume : s ≠ ∅,
    have Inf ((λb, b + a) '' s) = Inf s + a,
      from is_glb_iff_Inf_eq.mp $ is_glb_of_is_glb_of_tendsto
        (assume x _ y _ h, add_le_add' h (le_refl _))
        is_glb_Inf
        this
        (tendsto_add (tendsto_id' inf_le_left) tendsto_const_nhds),
    by simp [Inf_image, -add_comm] at this; exact this.symm)

lemma Sup_add {s : set ennreal} (hs : s ≠ ∅) : Sup s + a = ⨆b∈s, b + a :=
have Sup ((λb, b + a) '' s) = Sup s + a,
  from is_lub_iff_Sup_eq.mp $ is_lub_of_is_lub_of_tendsto
    (assume x _ y _ h, add_le_add' h (le_refl _))
    is_lub_Sup
    hs
    (tendsto_add (tendsto_id' inf_le_left) tendsto_const_nhds),
by simp [Sup_image, -add_comm] at this; exact this.symm

lemma supr_add {ι : Sort*} {s : ι → ennreal} [h : nonempty ι] : supr s + a = ⨆b, s b + a :=
let ⟨x⟩ := h in
calc supr s + a = Sup (range s) + a : by simp [Sup_range]
  ... = (⨆b∈range s, b + a) : Sup_add $ ne_empty_iff_exists_mem.mpr ⟨s x, x, rfl⟩
  ... = _ : by simp [supr_range, -mem_range]

lemma add_supr {ι : Sort*} {s : ι → ennreal} [h : nonempty ι] : a + supr s = ⨆b, a + s b :=
by rw [add_comm, supr_add]; simp

lemma infi_add {ι : Sort*} {s : ι → ennreal} {a : ennreal} : infi s + a = ⨅b, s b + a :=
calc infi s + a = Inf (range s) + a : by simp [Inf_range]
  ... = (⨅b∈range s, b + a) : Inf_add
  ... = _ : by simp [infi_range, -mem_range]

lemma add_infi {ι : Sort*} {s : ι → ennreal} {a : ennreal} : a + infi s = ⨅b, a + s b :=
by rw [add_comm, infi_add]; simp

lemma infi_add_infi {ι : Sort*} {f g : ι → ennreal} (h : ∀i j, ∃k, f k + g k ≤ f i + g j) :
  infi f + infi g = (⨅a, f a + g a) :=
suffices (⨅a, f a + g a) ≤ infi f + infi g,
  from le_antisymm (le_infi $ assume a, add_le_add' (infi_le _ _) (infi_le _ _)) this,
calc (⨅a, f a + g a) ≤ (⨅ a a', f a + g a') :
    le_infi $ assume a, le_infi $ assume a',
      let ⟨k, h⟩ := h a a' in infi_le_of_le k h
  ... ≤ infi f + infi g :
    by simp [add_infi, infi_add, -add_comm, -le_infi_iff]

lemma infi_sum {α : Type*} {ι : Sort*} {f : ι → α → ennreal} {s : finset α} [inhabited ι]
  (h : ∀(t : finset α) (i j : ι), ∃k, ∀a∈t, f k a ≤ f i a ∧ f k a ≤ f j a) :
  (⨅i, s.sum (f i)) = s.sum (λa, ⨅i, f i a) :=
finset.induction_on s (by simp) $ assume a s ha ih,
  have ∀ (i j : ι), ∃ (k : ι), f k a + s.sum (f k) ≤ f i a + s.sum (f j),
    from assume i j,
    let ⟨k, hk⟩ := h (insert a s) i j in
    ⟨k, add_le_add' (hk a (finset.mem_insert_self _ _)).left $ finset.sum_le_sum' $
      assume a ha, (hk _ $ finset.mem_insert_of_mem ha).right⟩,
  by simp [ha, ih.symm, infi_add_infi this]

lemma supr_add_supr {ι : Sort*} [nonempty ι]
  {f g : ι → ennreal} (h : ∀i j, ∃k, f i + g j ≤ f k + g k) :
  supr f + supr g = (⨆ a, f a + g a) :=
begin
  refine le_antisymm _ (supr_le $ λ a, add_le_add' (le_supr _ _) (le_supr _ _)),
  simpa [add_supr, supr_add] using
    λ i j, show f i + g j ≤ ⨆ a, f a + g a, from
    let ⟨k, hk⟩ := h i j in le_supr_of_le k hk,
end

protected lemma tendsto_of_real_sub (hr : 0 ≤ r) :
  tendsto (λb, of_real r - b) (nhds b) (nhds (of_real r - b)) :=
by_cases
  (assume h : of_real r < b,
    suffices tendsto (λb, of_real r - b) (nhds b) (nhds ⊥),
      by simpa [le_of_lt h],
    by rw [nhds_bot_orderable];
    from (tendsto_infi.2 $ assume p, tendsto_infi.2 $ assume hp : 0 < p, tendsto_principal.2 $
      (nhds b).sets_of_superset (mem_nhds_sets (is_open_lt' (of_real r)) h) $
        by simp [forall_ennreal, hr, le_of_lt, hp] {contextual := tt}))
  (assume h : ¬ of_real r < b,
    let ⟨p, hp, hpr, eq⟩ := (le_of_real_iff hr).mp $ not_lt.1 h in
    have tendsto (λb, of_real ((r - b))) (nhds p ⊓ principal {x | 0 ≤ x}) (nhds (of_real (r - p))),
      from tendsto.comp (tendsto_sub tendsto_const_nhds (tendsto_id' inf_le_left)) tendsto_of_real,
    have tendsto (λb, of_real r - b) (map of_real (nhds p ⊓ principal {x | 0 ≤ x}))
      (nhds (of_real (r - p))),
      from tendsto_map' $ tendsto_cong this $ mem_inf_sets_of_right $
        by simp [(∘), -sub_eq_add_neg] {contextual:=tt},
    by simp at this; simp [eq, hr, hp, hpr, nhds_of_real_eq_map_of_real_nhds_nonneg, this])

lemma sub_supr {ι : Sort*} [hι : nonempty ι] {b : ι → ennreal} (hr : a < ∞) :
  a - (⨆i, b i) = (⨅i, a - b i) :=
let ⟨i⟩ := hι in
let ⟨r, hr, eq, _⟩ := lt_iff_exists_of_real.mp hr in
have Inf ((λb, of_real r - b) '' range b) = of_real r - (⨆i, b i),
  from is_glb_iff_Inf_eq.mp $ is_glb_of_is_lub_of_tendsto
    (assume x _ y _, sub_le_sub (le_refl _))
    is_lub_supr
    (ne_empty_of_mem ⟨i, rfl⟩)
    (tendsto.comp (tendsto_id' inf_le_left) (ennreal.tendsto_of_real_sub hr)),
by rw [eq, ←this]; simp [Inf_image, infi_range, -mem_range]

lemma sub_infi {ι : Sort*} {b : ι → ennreal} : a - (⨅i, b i) = (⨆i, a - b i) :=
eq_of_forall_ge_iff $ λ c, begin
  rw [ennreal.sub_le_iff_le_add, add_comm, infi_add],
  simp [ennreal.sub_le_iff_le_add]
end

end topological_space

section tsum

variables {f g : α → ennreal}

protected lemma is_sum : is_sum f (⨆s:finset α, s.sum f) :=
tendsto_orderable.2
  ⟨assume a' ha',
    let ⟨s, hs⟩ := lt_supr_iff.mp ha' in
    mem_at_top_sets.mpr ⟨s, assume t ht, lt_of_lt_of_le hs $ finset.sum_le_sum_of_subset ht⟩,
  assume a' ha',
    univ_mem_sets' $ assume s,
    have s.sum f ≤ ⨆(s : finset α), s.sum f,
      from le_supr (λ(s : finset α), s.sum f) s,
    lt_of_le_of_lt this ha'⟩

@[simp] protected lemma has_sum : has_sum f := ⟨_, ennreal.is_sum⟩

protected lemma tsum_eq_supr_sum : (∑a, f a) = (⨆s:finset α, s.sum f) :=
tsum_eq_is_sum ennreal.is_sum

protected lemma tsum_sigma {β : α → Type*} (f : Πa, β a → ennreal) :
  (∑p:Σa, β a, f p.1 p.2) = (∑a b, f a b) :=
tsum_sigma (assume b, ennreal.has_sum) ennreal.has_sum

protected lemma tsum_prod {f : α → β → ennreal} : (∑p:α×β, f p.1 p.2) = (∑a, ∑b, f a b) :=
let j : α × β → (Σa:α, β) := λp, sigma.mk p.1 p.2 in
let i : (Σa:α, β) → α × β := λp, (p.1, p.2) in
let f' : (Σa:α, β) → ennreal := λp, f p.1 p.2 in
calc (∑p:α×β, f' (j p)) = (∑p:Σa:α, β, f p.1 p.2) :
    tsum_eq_tsum_of_iso j i (assume ⟨a, b⟩, rfl) (assume ⟨a, b⟩, rfl)
   ... = (∑a, ∑b, f a b) : ennreal.tsum_sigma f

protected lemma tsum_of_real {f : α → ℝ} (h : is_sum f r) (hf : ∀a, 0 ≤ f a) :
  (∑a, of_real (f a)) = of_real r :=
have (λs:finset α, s.sum (of_real ∘ f)) = of_real ∘ (λs:finset α, s.sum f),
  from funext $ assume s, sum_of_real $ assume a _, hf a,
have tendsto (λs:finset α, s.sum (of_real ∘ f)) at_top (nhds (of_real r)),
  by rw [this]; exact h.comp tendsto_of_real,
tsum_eq_is_sum this

protected lemma tsum_comm {f : α → β → ennreal} : (∑a, ∑b, f a b) = (∑b, ∑a, f a b) :=
let f' : α×β → ennreal := λp, f p.1 p.2 in
calc (∑a, ∑b, f a b) = (∑p:α×β, f' p) : ennreal.tsum_prod.symm
  ... = (∑p:β×α, f' (prod.swap p)) :
    (tsum_eq_tsum_of_iso prod.swap (@prod.swap α β) (assume ⟨a, b⟩, rfl) (assume ⟨a, b⟩, rfl)).symm
  ... = (∑b, ∑a, f' (prod.swap (b, a))) : @ennreal.tsum_prod β α (λb a, f' (prod.swap (b, a)))

protected lemma tsum_add : (∑a, f a + g a) = (∑a, f a) + (∑a, g a) :=
tsum_add ennreal.has_sum ennreal.has_sum

protected lemma tsum_le_tsum (h : ∀a, f a ≤ g a) : (∑a, f a) ≤ (∑a, g a) :=
tsum_le_tsum h ennreal.has_sum ennreal.has_sum

protected lemma tsum_eq_supr_nat {f : ℕ → ennreal} :
  (∑i:ℕ, f i) = (⨆i:ℕ, (finset.range i).sum f) :=
calc _ = (⨆s:finset ℕ, s.sum f) : ennreal.tsum_eq_supr_sum
  ... = (⨆i:ℕ, (finset.range i).sum f) : le_antisymm
    (supr_le_supr2 $ assume s,
      let ⟨n, hn⟩ := finset.exists_nat_subset_range s in
      ⟨n, finset.sum_le_sum_of_subset hn⟩)
    (supr_le_supr2 $ assume i, ⟨finset.range i, le_refl _⟩)

protected lemma le_tsum (a : α) : f a ≤ (∑a, f a) :=
calc f a = ({a} : finset α).sum f : by simp
  ... ≤ (⨆s:finset α, s.sum f) : le_supr (λs:finset α, s.sum f) _
  ... = (∑a, f a) : by rw [ennreal.tsum_eq_supr_sum]

protected lemma mul_tsum : (∑i, a * f i) = a * (∑i, f i) :=
if h : ∀i, f i = 0 then by simp [h] else
let ⟨i, (hi : f i ≠ 0)⟩ := classical.not_forall.mp h in
have sum_ne_0 : (∑i, f i) ≠ 0, from ne_of_gt $
  calc 0 < f i : lt_of_le_of_ne ennreal.zero_le hi.symm
    ... ≤ (∑i, f i) : ennreal.le_tsum _,
have tendsto (λs:finset α, s.sum ((*) a ∘ f)) at_top (nhds (a * (∑i, f i))),
  by rw [← show (*) a ∘ (λs:finset α, s.sum f) = λs, s.sum ((*) a ∘ f),
         from funext $ λ s, finset.mul_sum];
  exact (is_sum_tsum ennreal.has_sum).comp (ennreal.tendsto_mul sum_ne_0),
tsum_eq_is_sum this

protected lemma tsum_mul : (∑i, f i * a) = (∑i, f i) * a :=
by simp [mul_comm, ennreal.mul_tsum]

@[simp] lemma tsum_supr_eq {α : Type*} (a : α) {f : α → ennreal} :
  (∑b:α, ⨆ (h : a = b), f b) = f a :=
le_antisymm
  (by rw [ennreal.tsum_eq_supr_sum]; exact supr_le (assume s,
    calc s.sum (λb, ⨆ (h : a = b), f b) ≤ (finset.singleton a).sum (λb, ⨆ (h : a = b), f b) :
        finset.sum_le_sum_of_ne_zero $ assume b _ hb,
          suffices a = b, by simpa using this.symm,
          classical.by_contradiction $ assume h,
            by simpa [h] using hb
      ... = f a : by simp))
  (calc f a ≤ (⨆ (h : a = a), f a) : le_supr (λh:a=a, f a) rfl
    ... ≤ (∑b:α, ⨆ (h : a = b), f b) : ennreal.le_tsum _)

theorem exists_pos_sum_of_encodable {ε : ennreal} (hε : 0 < ε)
  (ι) [encodable ι] : ∃ ε' : ι → ℝ, (∀ i, 0 < ε' i) ∧ (∑ i, of_real (ε' i)) < ε :=
let ⟨a, a0, aε⟩ := dense hε,
    ⟨p, _, e, pε⟩ := lt_iff_exists_of_real.1 aε,
    ⟨ε', ε'0, c, hc, cp⟩ := pos_sum_of_encodable (zero_lt_of_real_iff.1 (e ▸ a0):0<p) ι in
⟨ε', ε'0, by rw ennreal.tsum_of_real hc (λ i, le_of_lt (ε'0 i));
  exact lt_of_le_of_lt (of_real_le_of_real cp) pε⟩

end tsum

section nnreal
-- TODO: use nnreal to define ennreal

instance : has_coe nnreal ennreal := ⟨ennreal.of_real ∘ coe⟩

lemma tendsto_of_real_iff {f : filter α} {m : α → ℝ} {r : ℝ} (hm : ∀a, 0 ≤ m a) (hr : 0 ≤ r) :
  tendsto (λx, of_real (m x)) f (nhds (of_real r)) ↔ tendsto m f (nhds r) :=
iff.intro
  (assume h,
    have tendsto (λ (x : α), of_ennreal (of_real (m x))) f (nhds r), from
      h.comp (tendsto_of_ennreal hr),
    by simpa [hm])
  (assume h, h.comp tendsto_of_real)

lemma tendsto_coe_iff {f : filter α} {m : α → nnreal} {r : nnreal} :
  tendsto (λx, (m x : ennreal)) f (nhds r) ↔ tendsto m f (nhds r) :=
iff.trans (tendsto_of_real_iff (assume a, (m a).2) r.2) nnreal.tendsto_coe

protected lemma is_sum_of_real_iff {f : α → ℝ} {r : ℝ} (hf : ∀a, 0 ≤ f a) (hr : 0 ≤ r) :
  is_sum (λa, of_real (f a)) (of_real r) ↔ is_sum f r :=
by simp [is_sum, sum_of_real, hf];
  exact tendsto_of_real_iff (assume s, finset.zero_le_sum $ assume a ha, hf a) hr

protected lemma is_sum_coe_iff {f : α → nnreal} {r : nnreal} :
  is_sum (λa, (f a : ennreal)) r ↔ is_sum f r :=
iff.trans (ennreal.is_sum_of_real_iff (assume a, (f a).2) r.2) nnreal.is_sum_coe

protected lemma coe_tsum {f : α → nnreal} (h : has_sum f) : ↑(∑a, f a) = (∑a, f a : ennreal) :=
eq.symm (tsum_eq_is_sum $ ennreal.is_sum_coe_iff.2 $ is_sum_tsum h)

@[simp] lemma coe_mul (a b : nnreal) : ↑(a * b) = (a * b : ennreal) :=
(ennreal.of_real_mul_of_real a.2 b.2).symm

@[simp] lemma coe_one : ↑(1 : nnreal) = (1 : ennreal) := rfl

@[simp] lemma coe_eq_coe {n m : nnreal} : (↑n : ennreal) = m ↔ n = m :=
iff.trans (of_real_eq_of_real_of n.2 m.2) (iff.intro subtype.eq $ assume eq, eq ▸ rfl)

end nnreal

end ennreal

lemma has_sum_of_nonneg_of_le {f g : β → ℝ} (hg : ∀b, 0 ≤ g b) (hgf : ∀b, g b ≤ f b) :
  has_sum f → has_sum g
| ⟨r, hfr⟩ :=
  have hf : ∀a, 0 ≤ f a, from assume a, le_trans (hg a) (hgf a),
  have hr : 0 ≤ r, from is_sum_le hf is_sum_zero hfr,
  have is_sum (λa, ennreal.of_real (f a)) (ennreal.of_real r), from
    (ennreal.is_sum_of_real_iff hf hr).2 hfr,
  have (∑b, ennreal.of_real (g b)) ≤ ennreal.of_real r,
  begin
    refine is_sum_le (assume b, _) (is_sum_tsum ennreal.has_sum) this,
    exact ennreal.of_real_le_of_real (hgf _)
  end,
  let ⟨p, hp, hpr, eq⟩ := (ennreal.le_of_real_iff hr).1 this in
  have is_sum g p, from
    (ennreal.is_sum_of_real_iff hg hp).1 (eq ▸ is_sum_tsum ennreal.has_sum),
  has_sum_spec this

lemma nnreal.has_sum_of_le {f g : β → nnreal} (hgf : ∀b, g b ≤ f b) (hf : has_sum f) : has_sum g :=
nnreal.has_sum_coe.1 $ has_sum_of_nonneg_of_le (assume b, (g b).2) hgf $ nnreal.has_sum_coe.2 hf

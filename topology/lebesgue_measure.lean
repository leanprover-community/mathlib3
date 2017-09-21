/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Lebesgue measure on the real line
-/
import topology.outer_measure
noncomputable theory

namespace set

lemma subset.antisymm_iff {α : Type*} {s t : set α} : s = t ↔ (s ⊆ t ∧ t ⊆ s) :=
le_antisymm_iff

end set

open set

section decidable_linear_order
variables {α : Type*} [decidable_linear_order α] {a b a₁ a₂ b₁ b₂ : α}

def Ico (a b : α) := {x | a ≤ x ∧ x < b}
def Iio (a : α) := {x | x < a}

lemma Ico_eq_empty_iff : Ico a b = ∅ ↔ (b ≤ a) :=
by rw [←not_lt_iff];
from iff.intro
  (assume eq h, have a ∈ Ico a b, from ⟨le_refl a, h⟩, by rwa [eq] at this)
  (assume h, eq_empty_of_forall_not_mem $ assume x ⟨h₁, h₂⟩, h $ lt_of_le_of_lt h₁ h₂)

@[simp] lemma Ico_eq_empty : b ≤ a → Ico a b = ∅ := Ico_eq_empty_iff.mpr

lemma Ico_subset_Ico_iff (h₁ : a₁ < b₁) : Ico a₁ b₁ ⊆ Ico a₂ b₂ ↔ (a₂ ≤ a₁ ∧ b₁ ≤ b₂) :=
iff.intro
  (assume h,
    have h' : a₁ ∈ Ico a₂ b₂, from h ⟨le_refl _, h₁⟩,
    have ¬ b₂ < b₁, from assume : b₂ < b₁,
      have b₂ ∈ Ico a₂ b₂, from h ⟨le_of_lt h'.right, this⟩,
      lt_irrefl b₂ this.right,
    ⟨h'.left, not_lt_iff.mp $ this⟩)
  (assume ⟨h₁, h₂⟩ x ⟨hx₁, hx₂⟩, ⟨le_trans h₁ hx₁, lt_of_lt_of_le hx₂ h₂⟩)

lemma Ico_eq_Ico_iff : Ico a₁ b₁ = Ico a₂ b₂ ↔ ((b₁ ≤ a₁ ∧ b₂ ≤ a₂) ∨ (a₁ = a₂ ∧ b₁ = b₂)) :=
begin
  by_cases a₁ < b₁ with h₁; by_cases a₂ < b₂ with h₂,
  { rw [subset.antisymm_iff, Ico_subset_Ico_iff h₁, Ico_subset_Ico_iff h₂],
    simp [iff_def, le_antisymm_iff, or_imp_distrib, not_le_of_gt h₁] {contextual := tt} },
  { have h₂ : b₂ ≤ a₂, from not_lt_iff.mp h₂,
    rw [Ico_eq_empty_iff.mpr h₂, Ico_eq_empty_iff],
    simp [iff_def, h₂, or_imp_distrib] {contextual := tt} },
  { have h₁ : b₁ ≤ a₁, from not_lt_iff.mp h₁,
    rw [Ico_eq_empty_iff.mpr h₁, eq_comm, Ico_eq_empty_iff],
    simp [iff_def, h₁, or_imp_distrib] {contextual := tt}, cc },
  { have h₁ : b₁ ≤ a₁, from not_lt_iff.mp h₁,
    have h₂ : b₂ ≤ a₂, from not_lt_iff.mp h₂,
    rw [Ico_eq_empty_iff.mpr h₁, Ico_eq_empty_iff.mpr h₂],
    simp [iff_def, h₁, h₂] {contextual := tt} }
end

@[simp] lemma Ico_sdiff_Iio_eq {a b c : ℝ} : Ico a b \ Iio c = Ico (max a c) b :=
set.ext $ by simp [Ico, Iio, iff_def, max_le_iff] {contextual:=tt}

@[simp] lemma Ico_inter_Iio_eq {a b c : ℝ} : Ico a b ∩ Iio c = Ico a (min b c) :=
set.ext $ by simp [Ico, Iio, iff_def, lt_min_iff] {contextual:=tt}

end decidable_linear_order

open classical set lattice function filter
open ennreal (of_real)
local attribute [instance] decidable_inhabited prop_decidable

section order_topology
universes u v
variables {α : Type u} {β : Type v} [topological_space α] [topological_space β]
  [decidable_linear_order α] [decidable_linear_order β] [orderable_topology α] [orderable_topology β]

lemma nhds_principal_ne_top_of_is_lub {a : α} {s : set α} (ha : is_lub s a) (hs : s ≠ ∅) :
  nhds a ⊓ principal s ≠ ⊥ :=
let ⟨a', ha'⟩ := exists_mem_of_ne_empty hs in
forall_sets_neq_empty_iff_neq_bot.mp $ assume t ht,
  let ⟨t₁, ht₁, t₂, ht₂, ht⟩ := mem_inf_sets.mp ht in
  let ⟨hu, hl⟩ := mem_nhds_orderable_dest ht₁ in
  by_cases
    (assume h : a = a',
      have a ∈ t₁, from mem_of_nhds ht₁,
      have a ∈ t₂, from ht₂ $ by rwa [h],
      ne_empty_iff_exists_mem.mpr ⟨a, ht ⟨‹a ∈ t₁›, ‹a ∈ t₂›⟩⟩)
    (assume : a ≠ a',
      have a' < a, from lt_of_le_of_ne (ha.left _ ‹a' ∈ s›) this.symm,
      let ⟨l, hl, hlt₁⟩ := hl ⟨a', this⟩ in
      have ∃a'∈s, l < a',
        from classical.by_contradiction $ assume : ¬ ∃a'∈s, l < a',
          have ∀a'∈s, a' ≤ l, from assume a ha, not_lt_iff.mp $ assume ha', this ⟨a, ha, ha'⟩,
          have ¬ l < a, from not_lt_iff.mpr $ ha.right _ this,
          this ‹l < a›,
      let ⟨a', ha', ha'l⟩ := this in
      have a' ∈ t₁, from hlt₁ _ ‹l < a'›  $ ha.left _ ha',
      ne_empty_iff_exists_mem.mpr ⟨a', ht ⟨‹a' ∈ t₁›, ht₂ ‹a' ∈ s› ⟩⟩)

lemma is_lub_of_is_lub_of_tendsto {f : α → β} {s : set α} {a : α} {b : β}
  (hf : ∀x∈s, ∀y∈s, x ≤ y → f x ≤ f y) (ha : is_lub s a) (hs : s ≠ ∅)
  (hb : tendsto f (nhds a ⊓ principal s) (nhds b)) : is_lub (f '' s) b :=
have hnbot : (nhds a ⊓ principal s) ≠ ⊥, from nhds_principal_ne_top_of_is_lub ha hs,
have ∀a'∈s, ¬ b < f a',
  from assume a' ha' h,
  have {x | x < f a'} ∈ (nhds b).sets, from mem_nhds_sets (is_open_gt' _) h,
  let ⟨t₁, ht₁, t₂, ht₂, hs⟩ := mem_inf_sets.mp (hb this) in
  by_cases
    (assume h : a = a',
      have a ∈ t₁ ∩ t₂, from ⟨mem_of_nhds ht₁, ht₂ $ by rwa [h]⟩,
      have f a < f a', from hs this,
      lt_irrefl (f a') $ by rwa [h] at this)
    (assume h : a ≠ a',
      have a' < a, from lt_of_le_of_ne (ha.left _ ha') h.symm,
      have {x | a' < x} ∈ (nhds a).sets, from mem_nhds_sets (is_open_lt' _) this,
      have {x | a' < x} ∩ t₁ ∈ (nhds a).sets, from inter_mem_sets this ht₁,
      have ({x | a' < x} ∩ t₁) ∩ s ∈ (nhds a ⊓ principal s).sets,
        from inter_mem_inf_sets this (subset.refl s),
      let ⟨x, ⟨hx₁, hx₂⟩, hx₃⟩ := inhabited_of_mem_sets hnbot this in
      have hxa' : f x < f a', from hs ⟨hx₂, ht₂ hx₃⟩,
      have ha'x : f a' ≤ f x, from hf _ ha' _ hx₃ $ le_of_lt hx₁,
      lt_irrefl _ (lt_of_le_of_lt ha'x hxa')),
and.intro
  (assume b' ⟨a', ha', h_eq⟩, h_eq ▸ not_lt_iff.mp $ this _ ha')
  (assume b' hb', le_of_tendsto hnbot hb tendsto_const_nhds $
      mem_inf_sets_of_right $ assume x hx, hb' _ $ mem_image_of_mem _ hx)

end order_topology

namespace measure_theory

/- "Lebesgue" lebesgue_length of an interval

Important: if `s` is not a interval [a, b) its value is `∞`. This is important to extend this to the
Lebesgue measure. -/
def lebesgue_length (s : set ℝ) : ennreal := ⨅a b (h₁ : a ≤ b) (h₂ : s = Ico a b), of_real (b - a)

@[simp] lemma lebesgue_length_Ico {a b : ℝ} (h : a ≤ b) :
  lebesgue_length (Ico a b) = of_real (b - a) :=
le_antisymm
  (infi_le_of_le a $ infi_le_of_le b $ infi_le_of_le h $ infi_le_of_le rfl $ le_refl _)
  (le_infi $ assume a', le_infi $ assume b', le_infi $ assume h', le_infi $ assume eq,
    match Ico_eq_Ico_iff.mp eq with
    | or.inl ⟨h₁, h₂⟩ :=
      have a = b, from le_antisymm h h₁,
      have a' = b', from le_antisymm h' h₂,
      by simp *
    | or.inr ⟨h₁, h⟩ := by simp *
    end)

@[simp] lemma lebesgue_length_empty : lebesgue_length ∅ = 0 :=
have ∅ = Ico 0 (0:ℝ),
  from set.ext $ by simp [Ico, not_le_iff],
by rw [this, lebesgue_length_Ico]; simp [le_refl]

lemma le_lebesgue_length {r : ennreal} {s : set ℝ } (h : ∀a b, a ≤ b → s ≠ Ico a b) :
  r ≤ lebesgue_length s :=
le_infi $ assume a, le_infi $ assume b, le_infi $ assume hab, le_infi $ assume heq, (h a b hab heq).elim

lemma lebesgue_length_Ico_le_lebesgue_length_Ico {a₁ b₁ a₂ b₂ : ℝ} (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) :
  lebesgue_length (Ico a₁ b₁) ≤ lebesgue_length (Ico a₂ b₂) :=
by_cases
  (assume : b₁ ≤ a₁, by simp [Ico_eq_empty_iff.mpr this])
  (assume : ¬ b₁ ≤ a₁,
    have h₁ : a₁ ≤ b₁, from le_of_lt $ not_le_iff.mp this,
    have h₂ : a₂ ≤ b₂, from le_trans (le_trans ha h₁) hb,
    have b₁ + a₂ ≤ a₁ + (b₂ - a₂) + a₂,
      from calc b₁ + a₂ ≤ b₂ + a₁ : add_le_add hb ha
        ... = a₁ + (b₂ - a₂) + a₂ : by rw [add_sub, sub_add_cancel, add_comm],
    have b₁ ≤ a₁ + (b₂ - a₂), from le_of_add_le_add_right this,
    by simp [h₁, h₂, -sub_eq_add_neg]; exact this)

lemma lebesgue_length_subadditive {a b : ℝ} {c d : ℕ → ℝ}
  (hab : a ≤ b) (hcd : ∀i, c i ≤ d i) (habcd : Ico a b ⊆ (⋃i, Ico (c i) (d i))) :
  lebesgue_length (Ico a b) ≤ (∑i, lebesgue_length (Ico (c i) (d i))) :=
let
  s := λx, ∑i, lebesgue_length (Ico (c i) (min (d i) x)),
  M := {x : ℝ | a ≤ x ∧ x ≤ b ∧ of_real (x - a) ≤ s x }
in
have a ∈ M, by simp [M, le_refl, hab],
have b ∈ upper_bounds M, by simp [upper_bounds, M] {contextual:=tt},
let ⟨x, hx⟩ := exists_supremum_real ‹a ∈ M› ‹b ∈ upper_bounds M› in
have h' : is_lub ((λx, of_real (x - a)) '' M) (of_real (x - a)),
  from is_lub_of_is_lub_of_tendsto
    (assume x ⟨hx, _, _⟩ y ⟨hy, _, _⟩ h,
      have hx : 0 ≤ x - a, by rw [le_sub_iff_add_le]; simp [hx],
      have hy : 0 ≤ y - a, by rw [le_sub_iff_add_le]; simp [hy],
      by rw [ennreal.of_real_le_of_real_iff hx hy]; from sub_le_sub h (le_refl a))
    hx
    (ne_empty_iff_exists_mem.mpr ⟨a, ‹_›⟩)
    (tendsto_compose (tendsto_sub (tendsto_id' inf_le_left) tendsto_const_nhds) ennreal.tendsto_of_real),
have hax : a ≤ x, from hx.left a ‹a ∈ M›,
have hxb : x ≤ b, from hx.right b ‹b ∈ upper_bounds M›,
have hx_sx : of_real (x - a) ≤ s x,
  from h'.right _ $ assume r ⟨y, hy, eq⟩,
    have ∀i, lebesgue_length (Ico (c i) (min (d i) y)) ≤ lebesgue_length (Ico (c i) (min (d i) x)),
      from assume i,
      lebesgue_length_Ico_le_lebesgue_length_Ico (le_refl _) (inf_le_inf (le_refl _) (hx.left _ hy)),
    eq ▸ le_trans hy.2.2 $ ennreal.tsum_le_tsum this,
have hxM : x ∈ M,
  from ⟨hax, hxb, hx_sx⟩,
have x = b,
  from le_antisymm hxb $ not_lt_iff.mp $ assume hxb : x < b,
  have ∃k, x ∈ Ico (c k) (d k), by simpa using habcd ⟨hxM.left, hxb⟩,
  let ⟨k, hxc, hxd⟩ := this, y := min (d k) b in
  have hxy' : x < y, from lt_min hxd hxb,
  have hxy : x ≤ y, from le_of_lt hxy',
  have of_real (y - a) ≤ s y,
    from calc of_real (y - a) = of_real (x - a) + of_real (y - x) :
      begin
        rw [ennreal.of_real_add_of_real],
        simp,
        repeat { simp [hax, hxy, -sub_eq_add_neg] }
      end
      ... ≤ s x + (∑i, ⨆ h : i = k, of_real (y - x)) :
        add_le_add' hx_sx (le_trans (by simp) (@ennreal.le_tsum _ _ k))
      ... ≤ (∑i, lebesgue_length (Ico (c i) (min (d i) x)) + ⨆ h : i = k, of_real (y - x)) :
        by rw [tsum_add]; simp [ennreal.has_sum]
      ... ≤ s y : ennreal.tsum_le_tsum $ assume i, by_cases
          (assume : i = k,
            have eq₁ : min (d k) y = y, from min_eq_right $ min_le_left _ _,
            have eq₂ : min (d k) x = x, from min_eq_right $ le_of_lt hxd,
            have h : c k ≤ y, from le_min (hcd _) (le_trans hxc $ le_of_lt hxb),
            have eq: y - x + (x - c k) = y - c k, by rw [add_sub, sub_add_cancel],
            by simp [h, hxy, hxc, eq, eq₁, eq₂, this, -sub_eq_add_neg, add_sub_cancel'_right, le_refl])
          (assume h : i ≠ k, by simp [h, ennreal.bot_eq_zero];
            from lebesgue_length_Ico_le_lebesgue_length_Ico (le_refl _) (inf_le_inf (le_refl _) hxy)),
  have ¬ x < y, from not_lt_iff.mpr $ hx.left y ⟨le_trans hax hxy, min_le_right _ _, this⟩,
  this hxy',
have hbM : b ∈ M, from this ▸ hxM,
calc lebesgue_length (Ico a b) ≤ s b : by simp [hab]; exact hbM.right.right
  ... ≤ ∑i, lebesgue_length (Ico (c i) (d i)) : ennreal.tsum_le_tsum $ assume a,
    lebesgue_length_Ico_le_lebesgue_length_Ico (le_refl _) (min_le_left _ _)

def lebesgue_outer : outer_measure ℝ :=
outer_measure.inf lebesgue_length lebesgue_length_empty

lemma lebesgue_outer_Ico {a b : ℝ} (h : a ≤ b) :
  lebesgue_outer.measure_of (Ico a b) = of_real (b - a) :=
le_antisymm
  (let f : ℕ → set ℝ := λi, nat.rec_on i (Ico a b) (λn s, ∅) in
    infi_le_of_le f $ infi_le_of_le (subset_Union f 0) $
    calc (∑i, lebesgue_length (f i)) = ({0} : finset ℕ).sum (λi, lebesgue_length (f i)) :
        tsum_eq_sum $ by intro i; cases i; simp
      ... = lebesgue_length (Ico a b) : by simp; refl
      ... ≤ of_real (b - a) : by simp [h])
  (le_infi $ assume f, le_infi $ assume hf, by_cases
    (assume : ∀i, ∃p:ℝ×ℝ, p.1 ≤ p.2 ∧ f i = Ico p.1 p.2,
      let ⟨cd, hcd⟩ := axiom_of_choice this in
      have hcd₁ : ∀i, (cd i).1 ≤ (cd i).2, from assume i, (hcd i).1,
      have hcd₂ : ∀i, f i = Ico (cd i).1 (cd i).2, from assume i, (hcd i).2,
      calc of_real (b - a) = lebesgue_length (Ico a b) :
          by simp [h]
        ... ≤ (∑i, lebesgue_length (Ico (cd i).1 (cd i).2)) :
          lebesgue_length_subadditive h hcd₁ (by simpa [hcd₂] using hf)
        ... = _ :
          by simp [hcd₂])
    (assume h,
      have ∃i, ∀(c d : ℝ), c ≤ d → f i ≠ Ico c d,
        by simpa [classical.not_forall] using h,
      let ⟨i, hi⟩ := this in
      calc of_real (b - a) ≤ lebesgue_length (f i) : le_lebesgue_length hi
        ... ≤ (∑i, lebesgue_length (f i)) : ennreal.le_tsum))

lemma lebesgue_outer_is_measurable_Iio {c : ℝ} :
  lebesgue_outer.space.is_measurable (Iio c) :=
outer_measure.inf_space_is_measurable $ assume t, by_cases
  (assume : ∃a b, a ≤ b ∧ t = Ico a b,
    let ⟨a, b, hab, ht⟩ := this in
    begin
      cases le_total a c with hac hca; cases le_total b c with hbc hcb;
      simp [*, max_eq_right, max_eq_left, min_eq_left, min_eq_right, le_refl,
        -sub_eq_add_neg, add_sub_cancel'_right, add_sub],
      { show of_real (b + b - a - a) ≤ of_real (b - a),
        rw [ennreal.of_real_of_nonpos],
        { exact zero_le },
        { have : b ≤ a, from le_trans hbc hca,
          have : b + b ≤ a + a, from add_le_add this this,
          have : (b + b) - (a + a) ≤ 0, by simp [sub_le_iff_le_add, -sub_eq_add_neg, this],
          { simp, simp at this, exact this } } }
    end)
  (assume h, by simp at h; from le_lebesgue_length h)

end measure_theory


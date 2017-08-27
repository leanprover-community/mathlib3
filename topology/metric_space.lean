/-
Copyright (c) 2015, 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Metric spaces.

Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl

Many definitions and theorems expected on metric spaces are already introduced on uniform spaces and
topological spaces. For example:
  open and closed sets, compactness, completeness, continuity and uniform continuity
-/
import topology.real
open lattice set filter classical
noncomputable theory

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

lemma exists_subtype {p : α → Prop} {q : subtype p → Prop} :
  (∃x:subtype p, q x) ↔ (∃x, ∃h: p x, q ⟨x, h⟩) :=
⟨assume ⟨⟨x, h⟩, h'⟩, ⟨x, h, h'⟩, assume ⟨x, h, h'⟩, ⟨⟨x, h⟩, h'⟩⟩

class metric_space (α : Type u) extends uniform_space α : Type u :=
(dist : α → α → ℝ)
(dist_self : ∀ x : α, dist x x = 0)
(eq_of_dist_eq_zero : ∀ {x y : α}, dist x y = 0 → x = y)
(dist_comm : ∀ x y : α, dist x y = dist y x)
(dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z)
(uniformity_dist : uniformity = (⨅ ε>0, principal {p:α×α | dist p.1 p.2 < ε}))

variables [metric_space α]

def dist : α → α → ℝ := metric_space.dist

@[simp] lemma dist_self (x : α) : dist x x = 0 := metric_space.dist_self x

lemma eq_of_dist_eq_zero {x y : α} : dist x y = 0 → x = y :=
metric_space.eq_of_dist_eq_zero

lemma dist_comm (x y : α) : dist x y = dist y x := metric_space.dist_comm x y

@[simp] lemma dist_eq_zero_iff {x y : α} : dist x y = 0 ↔ x = y :=
iff.intro eq_of_dist_eq_zero (assume : x = y, this ▸ dist_self _)

@[simp] lemma zero_eq_dist_iff {x y : α} : 0 = dist x y ↔ x = y :=
by rw [eq_comm, dist_eq_zero_iff]

lemma dist_triangle (x y z : α) : dist x z ≤ dist x y + dist y z :=
metric_space.dist_triangle x y z

lemma uniformity_dist : uniformity = (⨅ ε>0, principal {p:α×α | dist p.1 p.2 < ε}) :=
metric_space.uniformity_dist _

lemma uniformity_dist' : uniformity = (⨅ε:{ε:ℝ // ε>0}, principal {p:α×α | dist p.1 p.2 < ε.val}) :=
by simp [infi_subtype]; exact uniformity_dist

lemma dist_nonneg {x y : α} : 0 ≤ dist x y :=
have 2 * dist x y ≥ 0,
  from calc 2 * dist x y = dist x y + dist y x : by rw [dist_comm x y]; simp [bit0, bit1, mul_add]
    ... ≥ 0 : by rw [←(dist_self x)]; apply dist_triangle,
nonneg_of_mul_nonneg_left this two_pos

lemma dist_pos_of_ne {x y : α} (h : x ≠ y) : dist x y > 0 :=
lt_of_le_of_ne dist_nonneg (by simp * at *)

lemma ne_of_dist_pos {x y : α} (h : dist x y > 0) : x ≠ y :=
assume : x = y,
have 0 < (0:real), by simp [this] at h; exact h,
lt_irrefl _ this

lemma eq_of_forall_dist_le {x y : α} (h : ∀ε, ε > 0 → dist x y ≤ ε) : x = y :=
eq_of_dist_eq_zero (eq_of_le_of_forall_le dist_nonneg h)

instance metric_space.to_separated [metric_space α] : separated α :=
set.ext $ assume ⟨x, y⟩,
  begin
    constructor,
    simp [id_rel, separation_rel, uniformity_dist'],
    exact (assume h, eq_of_forall_dist_le $ assume ε hε,
      have (x, y) ∈ {p:α×α| dist p.1 p.2 < ε}, from h _ $ mem_infi_sets ⟨ε, hε⟩ $ subset.refl _,
      le_of_lt this),
    simp [id_rel, separation_rel] {contextual := tt},
    have h : principal {(y, y)} ≤ (@uniformity α _),
    { rw [uniformity_dist],
      exact (le_infi $ assume ε, le_infi $ assume hε, by simp; assumption) },
    exact (assume _ t ht, have {(y, y)} ⊆ t, from h ht, by simp at this; assumption)
  end

/- instantiate reals -/
instance : metric_space ℝ :=
{ real.uniform_space with
  dist := λx y, abs (x - y),
  dist_self := by simp [abs_zero],
  eq_of_dist_eq_zero := by simp [add_eq_iff_eq_add_neg] {contextual := tt},
  dist_comm := assume x y, by rw [abs_sub],
  dist_triangle := assume x y z, abs_sub_le _ _ _,
  uniformity_dist := le_antisymm
    (le_infi $ assume ε, le_infi $ assume hε, le_principal_iff.mpr $ mem_uniformity_real_iff.mpr $
      let ⟨q, hq₁, hq₂⟩ := exists_pos_of_rat hε in
      ⟨q, hq₁, assume r₁ r₂ hr, lt_trans hr hq₂⟩)
    (assume s hs,
      let ⟨q, hq₁, hq₂⟩ := mem_uniformity_real_iff.mp hs in
      mem_infi_sets (of_rat q) $ mem_infi_sets (of_rat_lt_of_rat.mpr hq₁) $
      assume ⟨r₁, r₂⟩, hq₂ r₁ r₂) }

lemma uniform_continuous_dist' : uniform_continuous (λp:α×α, dist p.1 p.2) :=
let i : {ε:ℝ // ε>0} := ⟨1, zero_lt_one⟩ in
have d : ∀p₁ p₂ q₁ q₂:α, dist p₁ q₁ - dist p₂ q₂ ≤ dist p₁ p₂ + dist q₁ q₂,
  from assume p₁ p₂ q₁ q₂,
  have dist p₁ q₁ ≤ (dist p₁ p₂ + dist q₁ q₂) + dist p₂ q₂,
    from calc dist p₁ q₁ ≤ dist p₁ p₂ + dist p₂ q₁ : dist_triangle _ _ _
      ... ≤ dist p₁ p₂ + (dist p₂ q₂ + dist q₂ q₁) : add_le_add_left (dist_triangle _ _ _) _
      ... = _ : by simp [dist_comm],
  sub_le_iff_le_add.mpr this,
have ∀{ε} {p₁ p₂ q₁ q₂ : α},
  ε > 0 → dist p₁ p₂ < ε / 2 ∧ dist q₁ q₂ < ε / 2 → dist (dist p₁ q₁) (dist p₂ q₂) < ε,
  from assume ε p₁ p₂ q₁ q₂ hε ⟨h₁, h₂⟩,
  have d₁ : dist p₁ q₁ - dist p₂ q₂ ≤ dist p₁ p₂ + dist q₁ q₂, from d _ _ _ _,
  have d₂ : dist p₂ q₂ - dist p₁ q₁ ≤ dist p₁ p₂ + dist q₁ q₂,
    by have h := d p₂ p₁ q₂ q₁; simp [dist_comm] at h; simp [dist_comm, h],
  calc dist (dist p₁ q₁) (dist p₂ q₂) ≤ dist p₁ p₂ + dist q₁ q₂ :
    abs_le_of_le_of_neg_le d₁ (by rw [neg_sub]; exact d₂)
    ... < ε / 2 + ε / 2 : add_lt_add h₁ h₂
    ... = (ε + ε) / 2 : by simp [div_add_div_same]
    ... = ε : add_self_div_two ε,
begin
  rw [uniform_continuous, uniformity_prod_eq_prod, uniformity_dist', uniformity_dist],
  simp [prod_infi_left i, prod_infi_right i, prod_principal_principal],
  exact (tendsto_map' $ tendsto_infi $ assume ε, tendsto_infi $ assume hε,
    let ε' : subtype {r : ℝ | r > 0} := ⟨ε / 2, div_pos_of_pos_of_pos hε two_pos⟩ in
    tendsto_infi' ε' $ tendsto_infi' ε' $ tendsto_principal_principal $
    assume ⟨⟨p₁, p₂⟩, ⟨q₁, q₂⟩⟩, by simp; exact this hε),
end

lemma uniform_continuous_dist [uniform_space β] {f g : β → α}
  (hf : uniform_continuous f) (hg : uniform_continuous g) :
  uniform_continuous (λb, dist (f b) (g b)) :=
uniform_continuous_compose (uniform_continuous_prod_mk hf hg) uniform_continuous_dist'

lemma continuous_dist' : continuous (λp:α×α, dist p.1 p.2) :=
continuous_of_uniform uniform_continuous_dist'

lemma continuous_dist [topological_space β] {f g : β → α}
  (hf : continuous f) (hg : continuous g) : continuous (λb, dist (f b) (g b)) :=
continuous_compose (continuous_prod_mk hf hg) continuous_dist'

lemma tendsto_dist {f g : β → α} {x : filter β} {a b : α}
  (hf : tendsto f x (nhds a)) (hg : tendsto g x (nhds b)) :
  tendsto (λx, dist (f x) (g x)) x (nhds (dist a b)) :=
have tendsto (λp:α×α, dist p.1 p.2) (nhds (a, b)) (nhds (dist a b)),
  from continuous_iff_tendsto.mp continuous_dist' (a, b),
tendsto_compose (tendsto_prod_mk hf hg) (by rw [nhds_prod_eq] at this; exact this)

/- instantiate metric space as a topology -/
variables {x y z : α} {ε ε₁ ε₂ : ℝ} {s : set α}

def open_ball (x : α) (ε : ℝ) : set α := {y | dist y x < ε}
def closed_ball (x : α) (ε : ℝ) := {y | dist y x ≤ ε}

theorem open_ball_eq_empty_of_nonpos (hε : ε ≤ 0) : open_ball x ε = ∅ :=
eq_empty_of_forall_not_mem $ assume y hy,
  have dist y x < 0, from lt_of_lt_of_le hy hε,
  lt_irrefl 0 (lt_of_le_of_lt dist_nonneg this)

theorem pos_of_mem_open_ball (hy : y ∈ open_ball x ε) : ε > 0 :=
lt_of_le_of_lt dist_nonneg hy

theorem mem_open_ball (h : ε > 0) : x ∈ open_ball x ε :=
show dist x x < ε, by rewrite dist_self; assumption

theorem is_open_open_ball : is_open (open_ball x ε) :=
is_open_lt (continuous_dist continuous_id continuous_const) continuous_const

theorem is_closed_closed_ball : is_closed (closed_ball x ε) :=
is_closed_le (continuous_dist continuous_id continuous_const) continuous_const

lemma open_ball_subset_open_ball_of_le (h : ε₁ ≤ ε₂) : open_ball x ε₁ ⊆ open_ball x ε₂ :=
assume y, assume ymem, lt_of_lt_of_le ymem h

theorem nhds_eq_metric : nhds x = (⨅ε:{ε:ℝ // ε>0}, principal (open_ball x ε.val)) :=
begin
  rw [nhds_eq_uniformity, uniformity_dist', lift'_infi],
  apply congr_arg, apply funext, intro ε,
  rw [lift'_principal],
  simp [open_ball, dist_comm],
  exact monotone_preimage,
  exact ⟨⟨1, zero_lt_one⟩⟩,
  exact assume a b, rfl
end

theorem mem_nhds_sets_iff_metric : s ∈ (nhds x).sets ↔ ∃ε>0, open_ball x ε ⊆ s :=
begin
  rw [nhds_eq_metric, infi_sets_eq],
  simp [exists_subtype],
  exact assume ⟨x, hx⟩ ⟨y, hy⟩, ⟨⟨min x y, lt_min hx hy⟩,
    begin
      simp,
      constructor,
      exact open_ball_subset_open_ball_of_le (min_le_left _ _),
      exact open_ball_subset_open_ball_of_le (min_le_right _ _)
    end⟩,
  exact ⟨⟨1, zero_lt_one⟩⟩,
end

theorem is_open_metric : is_open s ↔ (∀x∈s, ∃ε>0, open_ball x ε ⊆ s) :=
by simp [is_open_iff_nhds, mem_nhds_sets_iff_metric]

/-
theorem is_closed_metric : is_closed s ↔ (∀x, (∀ε>0, open_ball x ε ∩ s ≠ ∅) → x ∈ s :=
_

theorem uniform_continuous_metric_iff [metric_space β] {f : α → β} :
  uniform_continuous f ↔ (∀ε>0, ∃δ>0, ∀x y:α, dist x y < ε → dist (f x) (f y) < δ) :=
_

theorem continuous_metric_iff [metric_space β] {f : α → β} :
  continuous f ↔ (∀x:α, ∀ε>0, ∃δ>0, ∀y, dist x y < ε → dist (f x) (f y) < δ) :=
_
-/

/-
Copyright (c) 2015, 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Metric spaces.

Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro

We introduce the class of metric spaces, i.e., a topological space
with a distance compatible with the topology. This class extends
`emetric_space` (in which the extended distance can take the value ∞), and
therefore also `uniform_space` and `topological_space`.
-/

import analysis.emetric_space
open lattice set filter classical emetric_space
noncomputable theory

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

/-Design note on metric spaces: we could start from an `emetric_space` and require
that the `edist` is always finite. However, we will often create metric spaces
just by providing the distance. In order for `dist` to be defeq to the expression
one gives at construction time, it is better to store the distance directly
in the structure-/

/- In the next definition, the condition `dist_nonneg` is required, as otherwise
one could for instance have `dist x x = -1` since `nnreal.of_real` sends all nonpositive
reals to `0`.-/
/--Metric spaces, in which the distance `dist` takes real values-/
class metric_space (α : Type u) extends emetric_space α : Type u :=
(dist : α → α → ℝ)
(dist_nonneg : ∀ x y, dist x y ≥ 0)
(edist_dist : ∀ x y, edist x y = ↑(nnreal.of_real (dist x y)))

export metric_space (dist)

/-- Construct a metric space from an `emetric_space` in which the extended
distance is everywhere finite.-/
def metric_space.mk' {α : Type u} [emetric_space α] (edist_ne_top : ∀ x y : α, edist x y ≠ ⊤) :
metric_space α :=
{ dist := λ x y, (edist x y).to_nnreal,
  dist_nonneg := λ x y, nnreal.zero_le_coe,
  edist_dist := assume x y, by simp [ennreal.coe_to_nnreal (edist_ne_top x y)] }

/--Construct a metric space from a distance function which satisfies the usual
distance axioms.-/
structure metric_space.core (α : Type u) :=
(dist : α → α → ℝ)
(dist_self : ∀ x : α, dist x x = 0)
(eq_of_dist_eq_zero : ∀ {x y : α}, dist x y = 0 → x = y)
(dist_comm : ∀ x y : α, dist x y = dist y x)
(dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z)

def metric_space.mk'' {α : Type u} (m : metric_space.core α) : metric_space α :=
have A : ∀ x y : α, m.dist x y ≥ 0 := assume x y,
    have 2 * m.dist x y ≥ 0,
    from calc 2 * m.dist x y = m.dist x y + m.dist y x : by rw [m.dist_comm x y, two_mul]
      ... ≥ 0 : by rw ← m.dist_self x; apply m.dist_triangle,
    nonneg_of_mul_nonneg_left this two_pos,
{ dist := m.dist,
  edist := λ x y, nnreal.of_real (m.dist x y),
  dist_nonneg := A,
  edist_dist := by simp [edist],
  edist_self := by simp [edist, m.dist_self],
  eq_of_edist_eq_zero := assume x y h,
    m.eq_of_dist_eq_zero $ le_antisymm (by simpa using h) (A x y),
  edist_comm := by simp [edist, m.dist_comm],
  edist_triangle := assume x y z, begin
    rw [← ennreal.coe_add, ennreal.coe_le_coe, nnreal.of_real_add_of_real (A x y) (A y z), nnreal.of_real_le_of_real_iff (A x z) $ add_le_add (A x y) (A y z)],
    apply m.dist_triangle x y z
  end }

variables [metric_space α]

/--`nndist` is the version of the distance taking values in nonnegative reals-/
def nndist {α : Type u} [metric_space α] (x y : α) : nnreal := ⟨dist x y, metric_space.dist_nonneg x y⟩

/--Express `nndist` in terms of `edist`-/
@[simp] lemma edist_eq_nndist (x y : α) : (edist x y).to_nnreal = nndist x y :=
by simp [nndist, metric_space.edist_dist, nnreal.of_real, max_eq_left (metric_space.dist_nonneg x y)]

/--Express `edist` in terms of `nndist`-/
@[simp] lemma nndist_eq_edist (x y : α) : ↑(nndist x y) = edist x y :=
by simp [nndist, metric_space.edist_dist, nnreal.of_real, max_eq_left (metric_space.dist_nonneg x y)]

/--In a metric space, the extended distance is always finite-/
lemma edist_ne_top (x y : α) : edist x y ≠ ⊤ :=
by rw [metric_space.edist_dist x y]; apply ennreal.coe_ne_top

/--`nndist x x` vanishes-/
@[simp] lemma nndist_self (x : α) : nndist x x = 0 :=
by rw [← edist_eq_nndist, emetric_space.edist_self x]; simp

/--Express `dist` in terms of `nndist`-/
@[simp] lemma nndist_eq_dist (x y : α) : ↑(nndist x y) = dist x y := rfl

/--Express `nndist` in terms of `dist`-/
@[simp] lemma dist_eq_nndist (x y : α) : nnreal.of_real (dist x y) = nndist x y :=
by rw [← nndist_eq_dist, nnreal.of_real_coe]

/--Deduce the equality of points with the vanishing of the nonnegative distance-/
theorem eq_of_nndist_eq_zero {x y : α} (h: nndist x y = 0) : x = y :=
emetric_space.eq_of_edist_eq_zero (by rw [← nndist_eq_edist, h]; simp)

theorem nndist_comm (x y : α) : nndist x y = nndist y x :=
by rw [← edist_eq_nndist, ← edist_eq_nndist]; simp only [emetric_space.edist_comm x y]

/--Characterize the equality of points with the vanishing of the nonnegative distance-/
@[simp] theorem nndist_eq_zero {x y : α} : nndist x y = 0 ↔ x = y :=
iff.intro eq_of_nndist_eq_zero (assume : x = y, this ▸ nndist_self _)

@[simp] theorem zero_eq_nndist {x y : α} : 0 = nndist x y ↔ x = y :=
iff.intro (assume h, eq_of_nndist_eq_zero (h.symm))
          (assume : x = y, this ▸ (nndist_self _).symm)

/--Triangle inequality for the nonnegative distance-/
theorem nndist_triangle (x y z : α) : nndist x z ≤ nndist x y + nndist y z :=
begin
  have A : edist x z ≤ edist x y + edist y z := emetric_space.edist_triangle x y z,
  rwa [← nndist_eq_edist, ← nndist_eq_edist, ← nndist_eq_edist, ← ennreal.coe_add, ennreal.coe_le_coe] at A
end

theorem nndist_triangle_left (x y z : α) : nndist x y ≤ nndist z x + nndist z y :=
by rw nndist_comm z; apply nndist_triangle

theorem nndist_triangle_right (x y z : α) : nndist x y ≤ nndist x z + nndist y z :=
by rw nndist_comm y; apply nndist_triangle

/--Express `edist` in terms of `dist`-/
@[simp] lemma dist_eq_edist (x y : α) : ↑(nnreal.of_real (dist x y)) = edist x y :=
(metric_space.edist_dist x y).symm

/--Express `dist` in terms `edist`-/
@[simp] lemma edist_eq_dist (x y : α) : ↑((edist x y).to_nnreal) = dist x y :=
by rw [← dist_eq_edist]; simp; rw [nnreal.coe_of_real _ (metric_space.dist_nonneg x y)]

@[simp] theorem dist_self (x : α) : dist x x = 0 :=
by rw [← nndist_eq_dist]; simp

theorem eq_of_dist_eq_zero {x y : α} (h : dist x y = 0) : x = y :=
eq_of_nndist_eq_zero (by rwa [← nndist_eq_dist, nnreal.coe_eq_zero] at h)

theorem dist_comm (x y : α) : dist x y = dist y x :=
by rw [← nndist_eq_dist, ← nndist_eq_dist]; simp only [nndist_comm x y]

@[simp] theorem dist_eq_zero {x y : α} : dist x y = 0 ↔ x = y :=
iff.intro eq_of_dist_eq_zero (assume : x = y, this ▸ dist_self _)

@[simp] theorem zero_eq_dist {x y : α} : 0 = dist x y ↔ x = y :=
by rw [eq_comm, dist_eq_zero]

theorem dist_triangle (x y z : α) : dist x z ≤ dist x y + dist y z :=
begin
  rw [← nndist_eq_dist, ← nndist_eq_dist, ← nndist_eq_dist, ← nnreal.coe_add, ← nnreal.coe_le],
  apply nndist_triangle x y z
end

theorem dist_triangle_left (x y z : α) : dist x y ≤ dist z x + dist z y :=
by rw dist_comm z; apply dist_triangle

theorem dist_triangle_right (x y z : α) : dist x y ≤ dist x z + dist y z :=
by rw dist_comm y; apply dist_triangle

theorem swap_dist : function.swap (@dist α _) = dist :=
by funext x y; exact dist_comm _ _

theorem abs_dist_sub_le (x y z : α) : abs (dist x z - dist y z) ≤ dist x y :=
abs_sub_le_iff.2
 ⟨sub_le_iff_le_add.2 (dist_triangle _ _ _),
  sub_le_iff_le_add.2 (dist_triangle_left _ _ _)⟩

theorem dist_nonneg {x y : α} : 0 ≤ dist x y :=
metric_space.dist_nonneg x y

@[simp] theorem dist_le_zero {x y : α} : dist x y ≤ 0 ↔ x = y :=
by simpa [le_antisymm_iff, dist_nonneg] using @dist_eq_zero _ _ x y

@[simp] theorem dist_pos {x y : α} : 0 < dist x y ↔ x ≠ y :=
by simpa [-dist_le_zero] using not_congr (@dist_le_zero _ _ x y)

/- instantiate metric space as a topology -/
variables {x y z : α} {ε ε₁ ε₂ : ℝ} {s : set α}

/-- `ball x ε` is the set of all points `y` with `dist y x < ε` -/
def ball (x : α) (ε : ℝ) : set α := {y | dist y x < ε}

@[simp] theorem mem_ball : y ∈ ball x ε ↔ dist y x < ε := iff.rfl

theorem mem_ball' : y ∈ ball x ε ↔ dist x y < ε := by rw dist_comm; refl

/-- `closed_ball x ε` is the set of all points `y` with `dist y x ≤ ε` -/
def closed_ball (x : α) (ε : ℝ) := {y | dist y x ≤ ε}

@[simp] theorem mem_closed_ball : y ∈ closed_ball x ε ↔ dist y x ≤ ε := iff.rfl

theorem pos_of_mem_ball (hy : y ∈ ball x ε) : ε > 0 :=
lt_of_le_of_lt dist_nonneg hy

theorem mem_ball_self (h : ε > 0) : x ∈ ball x ε :=
show dist x x < ε, by rw dist_self; assumption

theorem mem_ball_comm : x ∈ ball y ε ↔ y ∈ ball x ε :=
by simp [dist_comm]

theorem ball_subset_ball (h : ε₁ ≤ ε₂) : ball x ε₁ ⊆ ball x ε₂ :=
λ y (yx : _ < ε₁), lt_of_lt_of_le yx h

theorem ball_disjoint (h : ε₁ + ε₂ ≤ dist x y) : ball x ε₁ ∩ ball y ε₂ = ∅ :=
eq_empty_iff_forall_not_mem.2 $ λ z ⟨h₁, h₂⟩,
not_lt_of_le (dist_triangle_left x y z)
  (lt_of_lt_of_le (add_lt_add h₁ h₂) h)

theorem ball_disjoint_same (h : ε ≤ dist x y / 2) : ball x ε ∩ ball y ε = ∅ :=
ball_disjoint $ by rwa [← two_mul, ← le_div_iff' two_pos]

theorem ball_subset (h : dist x y ≤ ε₂ - ε₁) : ball x ε₁ ⊆ ball y ε₂ :=
λ z zx, by rw ← add_sub_cancel'_right ε₁ ε₂; exact
lt_of_le_of_lt (dist_triangle z x y) (add_lt_add_of_lt_of_le zx h)

theorem ball_half_subset (y) (h : y ∈ ball x (ε / 2)) : ball y (ε / 2) ⊆ ball x ε :=
ball_subset $ by rw sub_self_div_two; exact le_of_lt h

theorem exists_ball_subset_ball (h : y ∈ ball x ε) : ∃ ε' > 0, ball y ε' ⊆ ball x ε :=
⟨_, sub_pos.2 h, ball_subset $ by rw sub_sub_self⟩

theorem ball_eq_empty_iff_nonpos : ε ≤ 0 ↔ ball x ε = ∅ :=
(eq_empty_iff_forall_not_mem.trans
⟨λ h, le_of_not_gt $ λ ε0, h _ $ mem_ball_self ε0,
 λ ε0 y h, not_lt_of_le ε0 $ pos_of_mem_ball h⟩).symm

/- characterize the members of the uniformity in distance terms.
This will be used below to show that the uniformity can also be defined
directly using `dist` instead of `edist`.-/
theorem mem_uniformity_dist {s : set (α×α)} :
  s ∈ (@uniformity α _).sets ↔ (∃ε>0, ∀{a b:α}, dist a b < ε → (a, b) ∈ s) :=
have Main : (∃ε>0, ∀a b, edist a b < ε → (a, b) ∈ s) ↔ (∃ε>0, ∀a b, dist a b < ε → (a, b) ∈ s) :=
⟨show (∃ε>0, ∀a b, edist a b < ε → (a, b) ∈ s) → (∃ε>0, ∀a b, dist a b < ε → (a, b) ∈ s),
begin
  rintro ⟨ε, εpos, Hε⟩,
  rcases ε with h,
  { /- ε = ⊤, i.e., all points belong to `s` as the distance is finite.-/
    have A : ∀ a b : α, edist a b < ⊤ := assume a b, lt_top_iff_ne_top.2 (edist_ne_top a b),
    have B : ∀ a b : α, (a, b) ∈ s := assume a b, Hε _ _ (A a b),
    exact ⟨1, zero_lt_one, assume a b _, B a b⟩ },
  { /- ε < ⊤, and we can use the same value of ε as a real parameter-/
    have A : ε > 0 := ennreal.coe_lt_coe.1 εpos,
    have B : ∀ (a b : α), dist a b < ↑ε → (a, b) ∈ s := begin
      assume a b Dab,
      have I : nndist a b < ε := by rwa [← nndist_eq_dist, ← nnreal.coe_lt] at Dab,
      have J : edist a b < ε := by rw [← nndist_eq_edist]; apply ennreal.coe_lt_coe.2 I,
      exact Hε a b J
    end,
    exact ⟨ε, by simpa using A, B⟩ }
end,
show (∃ε>0, ∀a b, dist a b < ε → (a, b) ∈ s) → (∃ε>0, ∀a b, edist a b < ε → (a, b) ∈ s),
begin
  rintro ⟨ε, εpos, Hε⟩,
  have A : ((nnreal.of_real ε) : ennreal) > (0:nnreal) :=
  by apply ennreal.coe_lt_coe.2; simpa using εpos,
  have B : ∀ (a b : α), edist a b < nnreal.of_real ε → (a, b) ∈ s :=
  begin
    assume a b Dab,
    have I : nndist a b < nnreal.of_real ε :=
    by rwa [← nndist_eq_edist, ennreal.coe_lt_coe] at Dab,
    have J : dist a b < ε := begin
      rw [← nndist_eq_dist],
      have K := (nnreal.coe_lt _ _).1 I,
      rwa [nnreal.coe_of_real _ (le_of_lt εpos)] at K
    end,
    exact Hε a b J
  end,
  exact ⟨nnreal.of_real ε, A, B⟩
end⟩,
iff.trans (emetric_space.mem_uniformity_edist) Main

theorem uniformity_dist' : uniformity = (⨅ε:{ε:ℝ // ε>0}, principal {p:α×α | dist p.1 p.2 < ε.val}) :=
have A : ∀s, s ∈ (⨅ε:{ε:ℝ // ε>0}, principal {p:α×α | dist p.1 p.2 < ε.val}).sets ↔ (∃ε>0, ∀{a b:α}, dist a b < ε → (a, b) ∈ s) :=
begin
  assume s,
  rw [infi_sets_eq],
  simp [subset_def],
  exact assume ⟨r, hr⟩ ⟨p, hp⟩, ⟨⟨min r p, lt_min hr hp⟩, by simp [lt_min_iff, (≥)] {contextual := tt}⟩,
  exact ⟨⟨1, zero_lt_one⟩⟩
end,
filter.ext $ assume s, iff.trans (mem_uniformity_dist) ((A s).symm)

theorem uniformity_dist : uniformity = (⨅ ε>0, principal {p:α×α | dist p.1 p.2 < ε}) :=
by have h := @uniformity_dist' α _; simpa [infi_subtype] using h

theorem dist_mem_uniformity {ε:ℝ} (ε0 : 0 < ε) :
  {p:α×α | dist p.1 p.2 < ε} ∈ (@uniformity α _).sets :=
mem_uniformity_dist.2 ⟨ε, ε0, λ a b, id⟩

theorem uniform_continuous_of_metric [metric_space β] {f : α → β} :
  uniform_continuous f ↔ ∀ ε > 0, ∃ δ > 0,
    ∀{a b:α}, dist a b < δ → dist (f a) (f b) < ε :=
uniform_continuous_def.trans
⟨λ H ε ε0, mem_uniformity_dist.1 $ H _ $ dist_mem_uniformity ε0,
 λ H r ru,
  let ⟨ε, ε0, hε⟩ := mem_uniformity_dist.1 ru, ⟨δ, δ0, hδ⟩ := H _ ε0 in
  mem_uniformity_dist.2 ⟨δ, δ0, λ a b h, hε (hδ h)⟩⟩

theorem uniform_embedding_of_metric [metric_space β] {f : α → β} :
  uniform_embedding f ↔ function.injective f ∧ uniform_continuous f ∧
    ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, dist (f a) (f b) < ε → dist a b < δ :=
uniform_embedding_def'.trans $ and_congr iff.rfl $ and_congr iff.rfl
⟨λ H δ δ0, let ⟨t, tu, ht⟩ := H _ (dist_mem_uniformity δ0),
               ⟨ε, ε0, hε⟩ := mem_uniformity_dist.1 tu in
  ⟨ε, ε0, λ a b h, ht _ _ (hε h)⟩,
 λ H s su, let ⟨δ, δ0, hδ⟩ := mem_uniformity_dist.1 su, ⟨ε, ε0, hε⟩ := H _ δ0 in
  ⟨_, dist_mem_uniformity ε0, λ a b h, hδ (hε h)⟩⟩

theorem totally_bounded_of_metric {s : set α} :
  totally_bounded s ↔ ∀ ε > 0, ∃t : set α, finite t ∧ s ⊆ ⋃y∈t, ball y ε :=
⟨λ H ε ε0, H _ (dist_mem_uniformity ε0),
 λ H r ru, let ⟨ε, ε0, hε⟩ := mem_uniformity_dist.1 ru,
               ⟨t, ft, h⟩ := H ε ε0 in
  ⟨t, ft, subset.trans h $ Union_subset_Union $ λ y, Union_subset_Union $ λ yt z, hε⟩⟩

lemma cauchy_of_metric {f : filter α} :
  cauchy f ↔ f ≠ ⊥ ∧ ∀ ε > 0, ∃ t ∈ f.sets, ∀ x y ∈ t, dist x y < ε :=
cauchy_iff.trans $ and_congr iff.rfl
⟨λ H ε ε0, let ⟨t, tf, ts⟩ := H _ (dist_mem_uniformity ε0) in
   ⟨t, tf, λ x y xt yt, @ts (x, y) ⟨xt, yt⟩⟩,
 λ H r ru, let ⟨ε, ε0, hε⟩ := mem_uniformity_dist.1 ru,
               ⟨t, tf, h⟩ := H ε ε0 in
   ⟨t, tf, λ ⟨x, y⟩ ⟨hx, hy⟩, hε (h x y hx hy)⟩⟩

theorem nhds_eq_metric : nhds x = (⨅ε:{ε:ℝ // ε>0}, principal (ball x ε.val)) :=
begin
  rw [nhds_eq_uniformity, uniformity_dist', lift'_infi],
  { apply congr_arg, funext ε,
    rw [lift'_principal],
    { simp [ball, dist_comm] },
    { exact monotone_preimage } },
  { exact ⟨⟨1, zero_lt_one⟩⟩ },
  { intros, refl }
end

theorem mem_nhds_iff_metric : s ∈ (nhds x).sets ↔ ∃ε>0, ball x ε ⊆ s :=
begin
  rw [nhds_eq_metric, infi_sets_eq],
  { simp },
  { intros y z, cases y with y hy, cases z with z hz,
    refine ⟨⟨min y z, lt_min hy hz⟩, _⟩,
    simp [ball_subset_ball, min_le_left, min_le_right, (≥)] },
  { exact ⟨⟨1, zero_lt_one⟩⟩ }
end

theorem is_open_metric : is_open s ↔ ∀x∈s, ∃ε>0, ball x ε ⊆ s :=
by simp [is_open_iff_nhds, mem_nhds_iff_metric]

theorem is_open_ball : is_open (ball x ε) :=
is_open_metric.2 $ λ y, exists_ball_subset_ball

theorem ball_mem_nhds (x : α) {ε : ℝ} (ε0 : 0 < ε) : ball x ε ∈ (nhds x).sets :=
mem_nhds_sets is_open_ball (mem_ball_self ε0)

theorem tendsto_nhds_of_metric [metric_space β] {f : α → β} {a b} :
  tendsto f (nhds a) (nhds b) ↔ ∀ ε > 0,
    ∃ δ > 0, ∀{x:α}, dist x a < δ → dist (f x) b < ε :=
⟨λ H ε ε0, mem_nhds_iff_metric.1 (H (ball_mem_nhds _ ε0)),
 λ H s hs,
  let ⟨ε, ε0, hε⟩ := mem_nhds_iff_metric.1 hs, ⟨δ, δ0, hδ⟩ := H _ ε0 in
  mem_nhds_iff_metric.2 ⟨δ, δ0, λ x h, hε (hδ h)⟩⟩

theorem continuous_of_metric [metric_space β] {f : α → β} :
  continuous f ↔ ∀b (ε > 0), ∃ δ > 0, ∀a,
    dist a b < δ → dist (f a) (f b) < ε :=
continuous_iff_tendsto.trans $ forall_congr $ λ b, tendsto_nhds_of_metric

theorem exists_delta_of_continuous [metric_space β] {f : α → β} {ε:ℝ}
  (hf : continuous f) (hε : ε > 0) (b : α) :
  ∃ δ > 0, ∀a, dist a b ≤ δ → dist (f a) (f b) < ε :=
let ⟨δ, δ_pos, hδ⟩ := continuous_of_metric.1 hf b ε hε in
⟨δ / 2, half_pos δ_pos, assume a ha, hδ a $ lt_of_le_of_lt ha $ div_two_lt_of_pos δ_pos⟩

theorem eq_of_forall_dist_le {x y : α} (h : ∀ε, ε > 0 → dist x y ≤ ε) : x = y :=
eq_of_dist_eq_zero (eq_of_le_of_forall_le_of_dense dist_nonneg h)

/-- Instantiate the reals as a metric space. -/
instance : metric_space ℝ := metric_space.mk''
{ dist               := λx y, abs (x - y),
  dist_self          := by simp [abs_zero],
  eq_of_dist_eq_zero := by simp [add_neg_eq_zero],
  dist_comm          := assume x y, abs_sub _ _,
  dist_triangle      := assume x y z, abs_sub_le _ _ _ }

theorem real.dist_eq (x y : ℝ) : dist x y = abs (x - y) := rfl

theorem real.dist_0_eq_abs (x : ℝ) : dist x 0 = abs x :=
by simp [real.dist_eq]

@[simp] theorem abs_dist {a b : α} : abs (dist a b) = dist a b :=
abs_of_nonneg dist_nonneg

instance : orderable_topology ℝ :=
orderable_topology_of_nhds_abs $ λ x, begin
  simp only [show ∀ r, {b : ℝ | abs (x - b) < r} = ball x r,
    by simp [-sub_eq_add_neg, abs_sub, ball, real.dist_eq]],
  apply le_antisymm,
  { simp [le_infi_iff],
    exact λ ε ε0, mem_nhds_sets (is_open_ball) (mem_ball_self ε0) },
  { intros s h,
    rcases mem_nhds_iff_metric.1 h with ⟨ε, ε0, ss⟩,
    exact mem_infi_sets _ (mem_infi_sets ε0 (mem_principal_sets.2 ss)) },
end

instance prod.metric_space_max [metric_space β] : metric_space (α × β) :=
{ dist := λ x y, max (dist x.1 y.1) (dist x.2 y.2),
  dist_nonneg :=
  assume x y,
    calc 0 ≤ dist (x.1) (y.1) : dist_nonneg
      ...  ≤ max (dist x.1 y.1) (dist x.2 y.2) : le_max_left _ _,
  edist_dist := assume x y, begin
    have I : monotone (nnreal.of_real) := assume x y h, nnreal.of_real_le_of_real h,
    have J : monotone (λ (t:nnreal), (t:ennreal)) := assume x y h, ennreal.coe_le_coe.2 h,
    have A : monotone (λ (a:ℝ), ((nnreal.of_real a) : ennreal)) := monotone_comp I J,
    have B := (max_distrib_of_monotone A).symm,
    unfold edist,
    rw [← dist_eq_edist, ← dist_eq_edist, B]
  end }

theorem uniform_continuous_dist' : uniform_continuous (λp:α×α, dist p.1 p.2) :=
uniform_continuous_of_metric.2 $ λ ε ε0, ⟨ε/2, half_pos ε0,
begin
  suffices,
  { intros p q h, cases p with p₁ p₂, cases q with q₁ q₂,
    cases max_lt_iff.1 h with h₁ h₂, clear h,
    dsimp at h₁ h₂ ⊢,
    rw real.dist_eq,
    refine abs_sub_lt_iff.2 ⟨_, _⟩,
    { revert p₁ p₂ q₁ q₂ h₁ h₂, exact this },
    { apply this; rwa dist_comm } },
  intros p₁ p₂ q₁ q₂ h₁ h₂,
  have := add_lt_add
    (abs_sub_lt_iff.1 (lt_of_le_of_lt (abs_dist_sub_le p₁ q₁ p₂) h₁)).1
    (abs_sub_lt_iff.1 (lt_of_le_of_lt (abs_dist_sub_le p₂ q₂ q₁) h₂)).1,
  rwa [add_halves, dist_comm p₂, sub_add_sub_cancel, dist_comm q₂] at this
end⟩

theorem uniform_continuous_dist [uniform_space β] {f g : β → α}
  (hf : uniform_continuous f) (hg : uniform_continuous g) :
  uniform_continuous (λb, dist (f b) (g b)) :=
(hf.prod_mk hg).comp uniform_continuous_dist'

theorem continuous_dist' : continuous (λp:α×α, dist p.1 p.2) :=
uniform_continuous_dist'.continuous

theorem continuous_dist [topological_space β] {f g : β → α}
  (hf : continuous f) (hg : continuous g) : continuous (λb, dist (f b) (g b)) :=
(hf.prod_mk hg).comp continuous_dist'

theorem tendsto_dist {f g : β → α} {x : filter β} {a b : α}
  (hf : tendsto f x (nhds a)) (hg : tendsto g x (nhds b)) :
  tendsto (λx, dist (f x) (g x)) x (nhds (dist a b)) :=
have tendsto (λp:α×α, dist p.1 p.2) (nhds (a, b)) (nhds (dist a b)),
  from continuous_iff_tendsto.mp continuous_dist' (a, b),
(hf.prod_mk hg).comp (by rw [nhds_prod_eq] at this; exact this)

lemma nhds_comap_dist (a : α) : (nhds (0 : ℝ)).comap (λa', dist a' a) = nhds a :=
have h₁ : ∀ε, (λa', dist a' a) ⁻¹' ball 0 ε ⊆ ball a ε,
  by simp [subset_def, real.dist_0_eq_abs],
have h₂ : tendsto (λa', dist a' a) (nhds a) (nhds (dist a a)),
  from tendsto_dist tendsto_id tendsto_const_nhds,
le_antisymm
  (by simp [h₁, nhds_eq_metric, infi_le_infi, principal_mono,
      -le_principal_iff, -le_infi_iff])
  (by simpa [map_le_iff_le_comap.symm, tendsto] using h₂)

lemma tendsto_iff_dist_tendsto_zero {f : β → α} {x : filter β} {a : α} :
  (tendsto f x (nhds a)) ↔ (tendsto (λb, dist (f b) a) x (nhds 0)) :=
by rw [← nhds_comap_dist a, tendsto_comap_iff]

theorem is_closed_ball : is_closed (closed_ball x ε) :=
is_closed_le (continuous_dist continuous_id continuous_const) continuous_const

def metric_space.replace_uniformity {α} [U : uniform_space α] (m : metric_space α)
  (H : @uniformity _ U = @uniformity _ (emetric_space.to_uniform_space α)) :
  metric_space α :=
{ edist               := m.edist,
  edist_self          := m.edist_self,
  eq_of_edist_eq_zero := m.eq_of_edist_eq_zero,
  edist_comm          := m.edist_comm,
  edist_triangle      := m.edist_triangle,
  to_uniform_space    := U,
  dist                := m.dist,
  dist_nonneg         := m.dist_nonneg,
  edist_dist          := m.edist_dist,
  to_uniform_space    := U,
  uniformity_edist := H.trans (@uniformity_edist α _) }

def metric_space.induced {α β} (f : α → β) (hf : function.injective f)
  (m : metric_space β) : metric_space α :=
{ dist := λ x y, dist (f x) (f y),
  dist_nonneg := assume x y, dist_nonneg,
  edist_dist := assume x y, by simp,
  .. emetric_space.induced f hf (m.to_emetric_space) }

theorem metric_space.induced_uniform_embedding {α β} (f : α → β) (hf : function.injective f)
  (m : metric_space β) :
  by haveI := metric_space.induced f hf m;
     exact uniform_embedding f :=
by let := metric_space.induced f hf m; exactI
uniform_embedding_of_metric.2 ⟨hf, uniform_continuous_comap, λ ε ε0, ⟨ε, ε0, λ a b, id⟩⟩

instance {p : α → Prop} [t : metric_space α] : metric_space (subtype p) :=
metric_space.induced subtype.val (λ x y, subtype.eq) t

theorem subtype.dist_eq {p : α → Prop} [t : metric_space α] (x y : subtype p) :
dist x y = dist x.1 y.1 := rfl

lemma lebesgue_number_lemma_of_metric
  {s : set α} {ι} {c : ι → set α} (hs : compact s)
  (hc₁ : ∀ i, is_open (c i)) (hc₂ : s ⊆ ⋃ i, c i) :
  ∃ δ > 0, ∀ x ∈ s, ∃ i, ball x δ ⊆ c i :=
let ⟨n, en, hn⟩ := lebesgue_number_lemma hs hc₁ hc₂,
    ⟨δ, δ0, hδ⟩ := mem_uniformity_dist.1 en in
⟨δ, δ0, assume x hx, let ⟨i, hi⟩ := hn x hx in
 ⟨i, assume y hy, hi (hδ (mem_ball'.mp hy))⟩⟩

lemma lebesgue_number_lemma_of_metric_sUnion
  {s : set α} {c : set (set α)} (hs : compact s)
  (hc₁ : ∀ t ∈ c, is_open t) (hc₂ : s ⊆ ⋃₀ c) :
  ∃ δ > 0, ∀ x ∈ s, ∃ t ∈ c, ball x δ ⊆ t :=
by rw sUnion_eq_Union at hc₂;
   simpa using lebesgue_number_lemma_of_metric hs (by simpa) hc₂

section pi
open finset lattice
variables {π : β → Type*} [fintype β]

instance metric_space_pi [∀b, metric_space (π b)] : metric_space (Πb, π b) :=
{ dist := (λf g, ((finset.sup univ (λb, nndist (f b) (g b)) : nnreal) : real)),
  dist_nonneg := assume f g, nnreal.zero_le_coe,
  edist_dist := assume x y,
  have A : sup univ (λ (b : β), ((nndist (x b) (y b)) : ennreal)) = ↑(sup univ (λ (b : β), nndist (x b) (y b))) :=
  begin
    refine eq.symm (comp_sup_eq_sup_comp _ _ _),
    exact (assume x y h, ennreal.coe_le_coe.2 h), refl
  end,
  by unfold edist; simp; simp only [(nndist_eq_edist _ _).symm, A] }

end pi

/-
Copyright (c) 2015, 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Metric spaces.

Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro

Many definitions and theorems expected on metric spaces are already introduced on uniform spaces and
topological spaces. For example:
  open and closed sets, compactness, completeness, continuity and uniform continuity
-/
import data.real.nnreal analysis.topology.topological_structures
open lattice set filter classical
noncomputable theory

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

/-- Construct a metric space from a distance function and metric space axioms -/
def metric_space.uniform_space_of_dist
  (dist : α → α → ℝ)
  (dist_self : ∀ x : α, dist x x = 0)
  (dist_comm : ∀ x y : α, dist x y = dist y x)
  (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z) : uniform_space α :=
uniform_space.of_core {
  uniformity := (⨅ ε>0, principal {p:α×α | dist p.1 p.2 < ε}),
  refl       := le_infi $ assume ε, le_infi $
    by simp [set.subset_def, id_rel, dist_self, (>)] {contextual := tt},
  comp       := le_infi $ assume ε, le_infi $ assume h, lift'_le
    (mem_infi_sets (ε / 2) $ mem_infi_sets (div_pos_of_pos_of_pos h two_pos) (subset.refl _)) $
    have ∀ (a b c : α), dist a c < ε / 2 → dist c b < ε / 2 → dist a b < ε,
      from assume a b c hac hcb,
      calc dist a b ≤ dist a c + dist c b : dist_triangle _ _ _
        ... < ε / 2 + ε / 2 : add_lt_add hac hcb
        ... = ε : by rw [div_add_div_same, add_self_div_two],
    by simpa [comp_rel],
  symm       := tendsto_infi.2 $ assume ε, tendsto_infi.2 $ assume h,
    tendsto_infi' ε $ tendsto_infi' h $ tendsto_principal_principal.2 $ by simp [dist_comm] }

/-- The distance function (given an ambient metric space on `α`), which returns
  a nonnegative real number `dist x y` given `x y : α`. -/
class has_dist (α : Type*) := (dist : α → α → ℝ)

export has_dist (dist)

/-- Metric space

Each metric space induces a canonical `uniform_space` and hence a canonical `topological_space`.
This is enforced in the type class definition, by extending the `uniform_space` structure. When
instantiating a `metric_space` structure, the uniformity fields are not necessary, they will be
filled in by default. -/
class metric_space (α : Type u) extends has_dist α : Type u :=
(dist_self : ∀ x : α, dist x x = 0)
(eq_of_dist_eq_zero : ∀ {x y : α}, dist x y = 0 → x = y)
(dist_comm : ∀ x y : α, dist x y = dist y x)
(dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z)
(to_uniform_space : uniform_space α := metric_space.uniform_space_of_dist dist dist_self dist_comm dist_triangle)
(uniformity_dist : uniformity = ⨅ ε>0, principal {p:α×α | dist p.1 p.2 < ε} . control_laws_tac)

theorem uniformity_dist_of_mem_uniformity {U : filter (α × α)} (D : α → α → ℝ)
  (H : ∀ s, s ∈ U.sets ↔ ∃ε>0, ∀{a b:α}, D a b < ε → (a, b) ∈ s) :
  U = ⨅ ε>0, principal {p:α×α | D p.1 p.2 < ε} :=
le_antisymm
  (le_infi $ λ ε, le_infi $ λ ε0, le_principal_iff.2 $ (H _).2 ⟨ε, ε0, λ a b, id⟩)
  (λ r ur, let ⟨ε, ε0, h⟩ := (H _).1 ur in
    mem_infi_sets ε $ mem_infi_sets ε0 $ mem_principal_sets.2 $ λ ⟨a, b⟩, h)

variables [metric_space α]

instance metric_space.to_uniform_space' : uniform_space α :=
metric_space.to_uniform_space α

@[simp] theorem dist_self (x : α) : dist x x = 0 := metric_space.dist_self x

theorem eq_of_dist_eq_zero {x y : α} : dist x y = 0 → x = y :=
metric_space.eq_of_dist_eq_zero

theorem dist_comm (x y : α) : dist x y = dist y x := metric_space.dist_comm x y

@[simp] theorem dist_eq_zero {x y : α} : dist x y = 0 ↔ x = y :=
iff.intro eq_of_dist_eq_zero (assume : x = y, this ▸ dist_self _)

@[simp] theorem zero_eq_dist {x y : α} : 0 = dist x y ↔ x = y :=
by rw [eq_comm, dist_eq_zero]

theorem dist_triangle (x y z : α) : dist x z ≤ dist x y + dist y z :=
metric_space.dist_triangle x y z

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
have 2 * dist x y ≥ 0,
  from calc 2 * dist x y = dist x y + dist y x : by rw [dist_comm x y, two_mul]
    ... ≥ 0 : by rw ← dist_self x; apply dist_triangle,
nonneg_of_mul_nonneg_left this two_pos

@[simp] theorem dist_le_zero {x y : α} : dist x y ≤ 0 ↔ x = y :=
by simpa [le_antisymm_iff, dist_nonneg] using @dist_eq_zero _ _ x y

@[simp] theorem dist_pos {x y : α} : 0 < dist x y ↔ x ≠ y :=
by simpa [-dist_le_zero] using not_congr (@dist_le_zero _ _ x y)


section
variables [metric_space α]

def nndist (a b : α) : nnreal := ⟨dist a b, dist_nonneg⟩

@[simp] lemma nndist_self (a : α) : nndist a a = 0 := (nnreal.coe_eq_zero _).1 (dist_self a)

@[simp] lemma coe_dist (a b : α) : (nndist a b : ℝ) = dist a b := rfl

theorem eq_of_nndist_eq_zero {x y : α} : nndist x y = 0 → x = y :=
by simp [nnreal.eq_iff.symm]

theorem nndist_comm (x y : α) : nndist x y = nndist y x :=
by simpa [nnreal.eq_iff.symm] using dist_comm x y

@[simp] theorem nndist_eq_zero {x y : α} : nndist x y = 0 ↔ x = y :=
by simp [nnreal.eq_iff.symm]

@[simp] theorem zero_eq_nndist {x y : α} : 0 = nndist x y ↔ x = y :=
by simp [nnreal.eq_iff.symm]

theorem nndist_triangle (x y z : α) : nndist x z ≤ nndist x y + nndist y z :=
by simpa [nnreal.coe_le] using dist_triangle x y z

theorem nndist_triangle_left (x y z : α) : nndist x y ≤ nndist z x + nndist z y :=
by simpa [nnreal.coe_le] using dist_triangle_left x y z

theorem nndist_triangle_right (x y z : α) : nndist x y ≤ nndist x z + nndist y z :=
by simpa [nnreal.coe_le] using dist_triangle_right x y z

end

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

theorem uniformity_dist : uniformity = (⨅ ε>0, principal {p:α×α | dist p.1 p.2 < ε}) :=
metric_space.uniformity_dist _

theorem uniformity_dist' : uniformity = (⨅ε:{ε:ℝ // ε>0}, principal {p:α×α | dist p.1 p.2 < ε.val}) :=
by simp [infi_subtype]; exact uniformity_dist

theorem mem_uniformity_dist {s : set (α×α)} :
  s ∈ (@uniformity α _).sets ↔ (∃ε>0, ∀{a b:α}, dist a b < ε → (a, b) ∈ s) :=
begin
  rw [uniformity_dist', infi_sets_eq],
  simp [subset_def],
  exact assume ⟨r, hr⟩ ⟨p, hp⟩, ⟨⟨min r p, lt_min hr hp⟩, by simp [lt_min_iff, (≥)] {contextual := tt}⟩,
  exact ⟨⟨1, zero_lt_one⟩⟩
end

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

instance metric_space.to_separated : separated α :=
separated_def.2 $ λ x y h, eq_of_forall_dist_le $
  λ ε ε0, le_of_lt (h _ (dist_mem_uniformity ε0))

/-- Instantiate the reals as a metric space. -/
instance : metric_space ℝ :=
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

def metric_space.replace_uniformity {α} [U : uniform_space α] (m : metric_space α)
  (H : @uniformity _ U = @uniformity _ (metric_space.to_uniform_space α)) :
  metric_space α :=
{ dist               := @dist _ m.to_has_dist,
  dist_self          := dist_self,
  eq_of_dist_eq_zero := @eq_of_dist_eq_zero _ _,
  dist_comm          := dist_comm,
  dist_triangle      := dist_triangle,
  to_uniform_space   := U,
  uniformity_dist    := H.trans (@uniformity_dist α _) }

def metric_space.induced {α β} (f : α → β) (hf : function.injective f)
  (m : metric_space β) : metric_space α :=
{ dist               := λ x y, dist (f x) (f y),
  dist_self          := λ x, dist_self _,
  eq_of_dist_eq_zero := λ x y h, hf (dist_eq_zero.1 h),
  dist_comm          := λ x y, dist_comm _ _,
  dist_triangle      := λ x y z, dist_triangle _ _ _,
  to_uniform_space   := uniform_space.comap f m.to_uniform_space,
  uniformity_dist    := begin
    apply @uniformity_dist_of_mem_uniformity _ _ (λ x y, dist (f x) (f y)),
    refine λ s, mem_comap_sets.trans _,
    split; intro H,
    { rcases H with ⟨r, ru, rs⟩,
      rcases mem_uniformity_dist.1 ru with ⟨ε, ε0, hε⟩,
      refine ⟨ε, ε0, λ a b h, rs (hε _)⟩, exact h },
    { rcases H with ⟨ε, ε0, hε⟩,
      exact ⟨_, dist_mem_uniformity ε0, λ ⟨a, b⟩, hε⟩ }
  end }

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

instance prod.metric_space_max [metric_space β] : metric_space (α × β) :=
{ dist := λ x y, max (dist x.1 y.1) (dist x.2 y.2),
  dist_self := λ x, by simp,
  eq_of_dist_eq_zero := λ x y h, begin
    cases max_le_iff.1 (le_of_eq h) with h₁ h₂,
    exact prod.ext_iff.2 ⟨dist_le_zero.1 h₁, dist_le_zero.1 h₂⟩
  end,
  dist_comm := λ x y, by simp [dist_comm],
  dist_triangle := λ x y z, max_le
    (le_trans (dist_triangle _ _ _) (add_le_add (le_max_left _ _) (le_max_left _ _)))
    (le_trans (dist_triangle _ _ _) (add_le_add (le_max_right _ _) (le_max_right _ _))),
  uniformity_dist := begin
    refine uniformity_prod.trans _,
    simp [uniformity_dist, comap_infi],
    rw ← infi_inf_eq, congr, funext,
    rw ← infi_inf_eq, congr, funext,
    simp [inf_principal, ext_iff, max_lt_iff]
  end,
  to_uniform_space := prod.uniform_space }

theorem uniform_continuous_dist' : uniform_continuous (λp:α×α, dist p.1 p.2) :=
uniform_continuous_of_metric.2 (λ ε ε0, ⟨ε/2, half_pos ε0,
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
end⟩)

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

section pi
open finset lattice
variables {π : β → Type*} [fintype β] [∀b, metric_space (π b)]

instance has_dist_pi : has_dist (Πb, π b) :=
⟨λf g, ((finset.sup univ (λb, nndist (f b) (g b)) : nnreal) : ℝ)⟩

lemma dist_pi_def (f g : Πb, π b) :
  dist f g = (finset.sup univ (λb, nndist (f b) (g b)) : nnreal) := rfl

instance metric_space_pi : metric_space (Πb, π b) :=
{ dist := dist,
  dist_self := assume f, (nnreal.coe_eq_zero _).2 $ bot_unique $ finset.sup_le $ by simp,
  dist_comm := assume f g, nnreal.eq_iff.2 $ by congr; ext a; exact nndist_comm _ _,
  dist_triangle := assume f g h, show dist f h ≤ (dist f g) + (dist g h), from
    begin
      simp only [dist_pi_def, (nnreal.coe_add _ _).symm, (nnreal.coe_le _ _).symm,
        finset.sup_le_iff],
      assume b hb,
      exact le_trans (nndist_triangle _ (g b) _) (add_le_add (le_sup hb) (le_sup hb))
    end,
  eq_of_dist_eq_zero := assume f g eq0,
    begin
      simp only [dist_pi_def, nnreal.coe_eq_zero, nnreal.bot_eq_zero.symm, eq_bot_iff,
        finset.sup_le_iff] at eq0,
      exact (funext $ assume b, eq_of_nndist_eq_zero $ bot_unique $ eq0 b $ mem_univ b),
    end }

end pi

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

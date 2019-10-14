/-
Copyright (c) 2015, 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Metric spaces.

Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel

Many definitions and theorems expected on metric spaces are already introduced on uniform spaces and
topological spaces. For example:
  open and closed sets, compactness, completeness, continuity and uniform continuity
-/
import data.real.nnreal topology.metric_space.emetric_space topology.algebra.ordered
open lattice set filter classical topological_space
noncomputable theory

open_locale uniformity

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

/-- Construct a uniform structure from a distance function and metric space axioms -/
def uniform_space_of_dist
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
filled in by default. In the same way, each metric space induces an emetric space structure.
It is included in the structure, but filled in by default.

When one instantiates a metric space structure, for instance a product structure,
this makes it possible to use a uniform structure and an edistance that are exactly
the ones for the uniform spaces product and the emetric spaces products, thereby
ensuring that everything in defeq in diamonds.-/
class metric_space (α : Type u) extends has_dist α : Type u :=
(dist_self : ∀ x : α, dist x x = 0)
(eq_of_dist_eq_zero : ∀ {x y : α}, dist x y = 0 → x = y)
(dist_comm : ∀ x y : α, dist x y = dist y x)
(dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z)
(edist : α → α → ennreal := λx y, ennreal.of_real (dist x y))
(edist_dist : ∀ x y : α, edist x y = ennreal.of_real (dist x y) . control_laws_tac)
(to_uniform_space : uniform_space α := uniform_space_of_dist dist dist_self dist_comm dist_triangle)
(uniformity_dist : 𝓤 α = ⨅ ε>0, principal {p:α×α | dist p.1 p.2 < ε} . control_laws_tac)

variables [metric_space α]

instance metric_space.to_uniform_space' : uniform_space α :=
metric_space.to_uniform_space α

instance metric_space.to_has_edist : has_edist α := ⟨metric_space.edist⟩

@[simp] theorem dist_self (x : α) : dist x x = 0 := metric_space.dist_self x

theorem eq_of_dist_eq_zero {x y : α} : dist x y = 0 → x = y :=
metric_space.eq_of_dist_eq_zero

theorem dist_comm (x y : α) : dist x y = dist y x := metric_space.dist_comm x y

theorem edist_dist (x y : α) : edist x y = ennreal.of_real (dist x y) :=
metric_space.edist_dist _ x y

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

lemma dist_triangle4 (x y z w : α) :
  dist x w ≤ dist x y + dist y z + dist z w :=
calc
  dist x w ≤ dist x z + dist z w : dist_triangle x z w
       ... ≤ (dist x y + dist y z) + dist z w : add_le_add_right (metric_space.dist_triangle x y z) _

lemma dist_triangle4_left (x₁ y₁ x₂ y₂ : α) :
  dist x₂ y₂ ≤ dist x₁ y₁ + (dist x₁ x₂ + dist y₁ y₂) :=
by rw [add_left_comm, dist_comm x₁, ← add_assoc]; apply dist_triangle4

lemma dist_triangle4_right (x₁ y₁ x₂ y₂ : α) :
  dist x₁ y₁ ≤ dist x₁ x₂ + dist y₁ y₂ + dist x₂ y₂ :=
by rw [add_right_comm, dist_comm y₁]; apply dist_triangle4

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

@[simp] theorem abs_dist {a b : α} : abs (dist a b) = dist a b :=
abs_of_nonneg dist_nonneg

theorem eq_of_forall_dist_le {x y : α} (h : ∀ε, ε > 0 → dist x y ≤ ε) : x = y :=
eq_of_dist_eq_zero (eq_of_le_of_forall_le_of_dense dist_nonneg h)

def nndist (a b : α) : nnreal := ⟨dist a b, dist_nonneg⟩

/--Express `nndist` in terms of `edist`-/
lemma nndist_edist (x y : α) : nndist x y = (edist x y).to_nnreal :=
by simp [nndist, edist_dist, nnreal.of_real, max_eq_left dist_nonneg, ennreal.of_real]

/--Express `edist` in terms of `nndist`-/
lemma edist_nndist (x y : α) : edist x y = ↑(nndist x y) :=
by { rw [edist_dist, nndist, ennreal.of_real_eq_coe_nnreal] }

/--In a metric space, the extended distance is always finite-/
lemma edist_ne_top (x y : α) : edist x y ≠ ⊤ :=
by rw [edist_dist x y]; apply ennreal.coe_ne_top

/--`nndist x x` vanishes-/
@[simp] lemma nndist_self (a : α) : nndist a a = 0 := (nnreal.coe_eq_zero _).1 (dist_self a)

/--Express `dist` in terms of `nndist`-/
lemma dist_nndist (x y : α) : dist x y = ↑(nndist x y) := rfl

/--Express `nndist` in terms of `dist`-/
lemma nndist_dist (x y : α) : nndist x y = nnreal.of_real (dist x y) :=
by rw [dist_nndist, nnreal.of_real_coe]

/--Deduce the equality of points with the vanishing of the nonnegative distance-/
theorem eq_of_nndist_eq_zero {x y : α} : nndist x y = 0 → x = y :=
by simp only [nnreal.eq_iff.symm, (dist_nndist _ _).symm, imp_self, nnreal.coe_zero, dist_eq_zero]

theorem nndist_comm (x y : α) : nndist x y = nndist y x :=
by simpa [nnreal.eq_iff.symm] using dist_comm x y

/--Characterize the equality of points with the vanishing of the nonnegative distance-/
@[simp] theorem nndist_eq_zero {x y : α} : nndist x y = 0 ↔ x = y :=
by simp only [nnreal.eq_iff.symm, (dist_nndist _ _).symm, imp_self, nnreal.coe_zero, dist_eq_zero]

@[simp] theorem zero_eq_nndist {x y : α} : 0 = nndist x y ↔ x = y :=
by simp only [nnreal.eq_iff.symm, (dist_nndist _ _).symm, imp_self, nnreal.coe_zero, zero_eq_dist]

/--Triangle inequality for the nonnegative distance-/
theorem nndist_triangle (x y z : α) : nndist x z ≤ nndist x y + nndist y z :=
by simpa [nnreal.coe_le] using dist_triangle x y z

theorem nndist_triangle_left (x y z : α) : nndist x y ≤ nndist z x + nndist z y :=
by simpa [nnreal.coe_le] using dist_triangle_left x y z

theorem nndist_triangle_right (x y z : α) : nndist x y ≤ nndist x z + nndist y z :=
by simpa [nnreal.coe_le] using dist_triangle_right x y z

/--Express `dist` in terms of `edist`-/
lemma dist_edist (x y : α) : dist x y = (edist x y).to_real :=
by rw [edist_dist, ennreal.to_real_of_real (dist_nonneg)]

namespace metric

/- instantiate metric space as a topology -/
variables {x y z : α} {ε ε₁ ε₂ : ℝ} {s : set α}

/-- `ball x ε` is the set of all points `y` with `dist y x < ε` -/
def ball (x : α) (ε : ℝ) : set α := {y | dist y x < ε}

@[simp] theorem mem_ball : y ∈ ball x ε ↔ dist y x < ε := iff.rfl

theorem mem_ball' : y ∈ ball x ε ↔ dist x y < ε := by rw dist_comm; refl

/-- `closed_ball x ε` is the set of all points `y` with `dist y x ≤ ε` -/
def closed_ball (x : α) (ε : ℝ) := {y | dist y x ≤ ε}

@[simp] theorem mem_closed_ball : y ∈ closed_ball x ε ↔ dist y x ≤ ε := iff.rfl

theorem ball_subset_closed_ball : ball x ε ⊆ closed_ball x ε :=
assume y, by simp; intros h; apply le_of_lt h

theorem pos_of_mem_ball (hy : y ∈ ball x ε) : ε > 0 :=
lt_of_le_of_lt dist_nonneg hy

theorem mem_ball_self (h : ε > 0) : x ∈ ball x ε :=
show dist x x < ε, by rw dist_self; assumption

theorem mem_closed_ball_self (h : ε ≥ 0) : x ∈ closed_ball x ε :=
show dist x x ≤ ε, by rw dist_self; assumption

theorem mem_ball_comm : x ∈ ball y ε ↔ y ∈ ball x ε :=
by simp [dist_comm]

theorem ball_subset_ball (h : ε₁ ≤ ε₂) : ball x ε₁ ⊆ ball x ε₂ :=
λ y (yx : _ < ε₁), lt_of_lt_of_le yx h

theorem closed_ball_subset_closed_ball {α : Type u} [metric_space α] {ε₁ ε₂ : ℝ} {x : α} (h : ε₁ ≤ ε₂) :
  closed_ball x ε₁ ⊆ closed_ball x ε₂ :=
λ y (yx : _ ≤ ε₁), le_trans yx h

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

theorem uniformity_dist : 𝓤 α = (⨅ ε>0, principal {p:α×α | dist p.1 p.2 < ε}) :=
metric_space.uniformity_dist _

theorem uniformity_dist' : 𝓤 α = (⨅ε:{ε:ℝ // ε>0}, principal {p:α×α | dist p.1 p.2 < ε.val}) :=
by simp [infi_subtype]; exact uniformity_dist

theorem mem_uniformity_dist {s : set (α×α)} :
  s ∈ 𝓤 α ↔ (∃ε>0, ∀{a b:α}, dist a b < ε → (a, b) ∈ s) :=
begin
  rw [uniformity_dist', mem_infi],
  simp [subset_def],
  exact assume ⟨r, hr⟩ ⟨p, hp⟩, ⟨⟨min r p, lt_min hr hp⟩, by simp [lt_min_iff, (≥)] {contextual := tt}⟩,
  exact ⟨⟨1, zero_lt_one⟩⟩
end

theorem dist_mem_uniformity {ε:ℝ} (ε0 : 0 < ε) :
  {p:α×α | dist p.1 p.2 < ε} ∈ 𝓤 α :=
mem_uniformity_dist.2 ⟨ε, ε0, λ a b, id⟩

theorem uniform_continuous_iff [metric_space β] {f : α → β} :
  uniform_continuous f ↔ ∀ ε > 0, ∃ δ > 0,
    ∀{a b:α}, dist a b < δ → dist (f a) (f b) < ε :=
uniform_continuous_def.trans
⟨λ H ε ε0, mem_uniformity_dist.1 $ H _ $ dist_mem_uniformity ε0,
 λ H r ru,
  let ⟨ε, ε0, hε⟩ := mem_uniformity_dist.1 ru, ⟨δ, δ0, hδ⟩ := H _ ε0 in
  mem_uniformity_dist.2 ⟨δ, δ0, λ a b h, hε (hδ h)⟩⟩

theorem uniform_embedding_iff [metric_space β] {f : α → β} :
  uniform_embedding f ↔ function.injective f ∧ uniform_continuous f ∧
    ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, dist (f a) (f b) < ε → dist a b < δ :=
uniform_embedding_def'.trans $ and_congr iff.rfl $ and_congr iff.rfl
⟨λ H δ δ0, let ⟨t, tu, ht⟩ := H _ (dist_mem_uniformity δ0),
               ⟨ε, ε0, hε⟩ := mem_uniformity_dist.1 tu in
  ⟨ε, ε0, λ a b h, ht _ _ (hε h)⟩,
 λ H s su, let ⟨δ, δ0, hδ⟩ := mem_uniformity_dist.1 su, ⟨ε, ε0, hε⟩ := H _ δ0 in
  ⟨_, dist_mem_uniformity ε0, λ a b h, hδ (hε h)⟩⟩

theorem totally_bounded_iff {s : set α} :
  totally_bounded s ↔ ∀ ε > 0, ∃t : set α, finite t ∧ s ⊆ ⋃y∈t, ball y ε :=
⟨λ H ε ε0, H _ (dist_mem_uniformity ε0),
 λ H r ru, let ⟨ε, ε0, hε⟩ := mem_uniformity_dist.1 ru,
               ⟨t, ft, h⟩ := H ε ε0 in
  ⟨t, ft, subset.trans h $ Union_subset_Union $ λ y, Union_subset_Union $ λ yt z, hε⟩⟩

/-- A metric space space is totally bounded if one can reconstruct up to any ε>0 any element of the
space from finitely many data. -/
lemma totally_bounded_of_finite_discretization {α : Type u} [metric_space α] {s : set α}
  (H : ∀ε > (0 : ℝ), ∃ (β : Type u) [fintype β] (F : s → β),
    ∀x y, F x = F y → dist (x:α) y < ε) :
  totally_bounded s :=
begin
  classical, by_cases hs : s = ∅,
  { rw hs, exact totally_bounded_empty },
  rcases exists_mem_of_ne_empty hs with ⟨x0, hx0⟩,
  haveI : inhabited s := ⟨⟨x0, hx0⟩⟩,
  refine totally_bounded_iff.2 (λ ε ε0, _),
  rcases H ε ε0 with ⟨β, fβ, F, hF⟩,
  let Finv := function.inv_fun F,
  refine ⟨range (subtype.val ∘ Finv), finite_range _, λ x xs, _⟩,
  let x' := Finv (F ⟨x, xs⟩),
  have : F x' = F ⟨x, xs⟩ := function.inv_fun_eq ⟨⟨x, xs⟩, rfl⟩,
  simp only [set.mem_Union, set.mem_range],
  exact ⟨_, ⟨F ⟨x, xs⟩, rfl⟩, hF _ _ this.symm⟩
end

protected lemma cauchy_iff {f : filter α} :
  cauchy f ↔ f ≠ ⊥ ∧ ∀ ε > 0, ∃ t ∈ f, ∀ x y ∈ t, dist x y < ε :=
cauchy_iff.trans $ and_congr iff.rfl
⟨λ H ε ε0, let ⟨t, tf, ts⟩ := H _ (dist_mem_uniformity ε0) in
   ⟨t, tf, λ x y xt yt, @ts (x, y) ⟨xt, yt⟩⟩,
 λ H r ru, let ⟨ε, ε0, hε⟩ := mem_uniformity_dist.1 ru,
               ⟨t, tf, h⟩ := H ε ε0 in
   ⟨t, tf, λ ⟨x, y⟩ ⟨hx, hy⟩, hε (h x y hx hy)⟩⟩

theorem nhds_eq : nhds x = (⨅ε:{ε:ℝ // ε>0}, principal (ball x ε.val)) :=
begin
  rw [nhds_eq_uniformity, uniformity_dist', lift'_infi],
  { apply congr_arg, funext ε,
    rw [lift'_principal],
    { simp [ball, dist_comm] },
    { exact monotone_preimage } },
  { exact ⟨⟨1, zero_lt_one⟩⟩ },
  { intros, refl }
end

theorem mem_nhds_iff : s ∈ nhds x ↔ ∃ε>0, ball x ε ⊆ s :=
begin
  rw [nhds_eq, mem_infi],
  { simp },
  { intros y z, cases y with y hy, cases z with z hz,
    refine ⟨⟨min y z, lt_min hy hz⟩, _⟩,
    simp [ball_subset_ball, min_le_left, min_le_right, (≥)] },
  { exact ⟨⟨1, zero_lt_one⟩⟩ }
end

theorem is_open_iff : is_open s ↔ ∀x∈s, ∃ε>0, ball x ε ⊆ s :=
by simp [is_open_iff_nhds, mem_nhds_iff]

theorem is_open_ball : is_open (ball x ε) :=
is_open_iff.2 $ λ y, exists_ball_subset_ball

theorem ball_mem_nhds (x : α) {ε : ℝ} (ε0 : 0 < ε) : ball x ε ∈ nhds x :=
mem_nhds_sets is_open_ball (mem_ball_self ε0)

theorem tendsto_nhds_nhds [metric_space β] {f : α → β} {a b} :
  tendsto f (nhds a) (nhds b) ↔
    ∀ ε > 0, ∃ δ > 0, ∀{x:α}, dist x a < δ → dist (f x) b < ε :=
⟨λ H ε ε0, mem_nhds_iff.1 (H (ball_mem_nhds _ ε0)),
 λ H s hs,
  let ⟨ε, ε0, hε⟩ := mem_nhds_iff.1 hs, ⟨δ, δ0, hδ⟩ := H _ ε0 in
  mem_nhds_iff.2 ⟨δ, δ0, λ x h, hε (hδ h)⟩⟩

theorem continuous_iff [metric_space β] {f : α → β} :
  continuous f ↔
    ∀b (ε > 0), ∃ δ > 0, ∀a, dist a b < δ → dist (f a) (f b) < ε :=
continuous_iff_continuous_at.trans $ forall_congr $ λ b, tendsto_nhds_nhds

theorem exists_delta_of_continuous [metric_space β] {f : α → β} {ε : ℝ}
  (hf : continuous f) (hε : ε > 0) (b : α) :
  ∃ δ > 0, ∀a, dist a b ≤ δ → dist (f a) (f b) < ε :=
let ⟨δ, δ_pos, hδ⟩ := continuous_iff.1 hf b ε hε in
⟨δ / 2, half_pos δ_pos, assume a ha, hδ a $ lt_of_le_of_lt ha $ div_two_lt_of_pos δ_pos⟩

theorem tendsto_nhds {f : filter β} {u : β → α} {a : α} :
  tendsto u f (nhds a) ↔ ∀ ε > 0, ∃ n ∈ f, ∀x ∈ n,  dist (u x) a < ε :=
by simp only [metric.nhds_eq, tendsto_infi, subtype.forall, tendsto_principal, mem_ball];
  exact forall_congr (assume ε, forall_congr (assume hε, exists_sets_subset_iff.symm))

theorem continuous_iff' [topological_space β] {f : β → α} :
  continuous f ↔ ∀a (ε > 0), ∃ n ∈ nhds a, ∀b ∈ n, dist (f b) (f a) < ε :=
continuous_iff_continuous_at.trans $ forall_congr $ λ b, tendsto_nhds

theorem tendsto_at_top [nonempty β] [semilattice_sup β] {u : β → α} {a : α} :
  tendsto u at_top (nhds a) ↔ ∀ε>0, ∃N, ∀n≥N, dist (u n) a < ε :=
by simp only [metric.nhds_eq, tendsto_infi, subtype.forall, tendsto_at_top_principal]; refl

end metric

open metric

instance metric_space.to_separated : separated α :=
separated_def.2 $ λ x y h, eq_of_forall_dist_le $
  λ ε ε0, le_of_lt (h _ (dist_mem_uniformity ε0))

/-Instantiate a metric space as an emetric space. Before we can state the instance,
we need to show that the uniform structure coming from the edistance and the
distance coincide. -/

/-- Expressing the uniformity in terms of `edist` -/
protected lemma metric.mem_uniformity_edist {s : set (α×α)} :
  s ∈ 𝓤 α ↔ (∃ε>0, ∀{a b:α}, edist a b < ε → (a, b) ∈ s) :=
begin
  refine mem_uniformity_dist.trans ⟨_, _⟩; rintro ⟨ε, ε0, Hε⟩,
  { refine ⟨ennreal.of_real ε, _, λ a b, _⟩,
    { rwa [gt, ennreal.of_real_pos] },
    { rw [edist_dist, ennreal.of_real_lt_of_real_iff ε0],
      exact Hε } },
  { rcases ennreal.lt_iff_exists_real_btwn.1 ε0 with ⟨ε', _, ε0', hε⟩,
    rw [ennreal.of_real_pos] at ε0',
    refine ⟨ε', ε0', λ a b h, Hε (lt_trans _ hε)⟩,
    rwa [edist_dist, ennreal.of_real_lt_of_real_iff ε0'] }
end

protected theorem metric.uniformity_edist' : 𝓤 α = (⨅ε:{ε:ennreal // ε>0}, principal {p:α×α | edist p.1 p.2 < ε.val}) :=
begin
  ext s, rw mem_infi,
  { simp [metric.mem_uniformity_edist, subset_def] },
  { rintro ⟨r, hr⟩ ⟨p, hp⟩, use ⟨min r p, lt_min hr hp⟩,
    simp [lt_min_iff, (≥)] {contextual := tt} },
  { exact ⟨⟨1, ennreal.zero_lt_one⟩⟩ }
end

theorem uniformity_edist : 𝓤 α = (⨅ ε>0, principal {p:α×α | edist p.1 p.2 < ε}) :=
by simpa [infi_subtype] using @metric.uniformity_edist' α _

/-- A metric space induces an emetric space -/
instance metric_space.to_emetric_space : emetric_space α :=
{ edist               := edist,
  edist_self          := by simp [edist_dist],
  eq_of_edist_eq_zero := assume x y h, by simpa [edist_dist] using h,
  edist_comm          := by simp only [edist_dist, dist_comm]; simp,
  edist_triangle      := assume x y z, begin
    simp only [edist_dist, (ennreal.of_real_add _ _).symm, dist_nonneg],
    rw ennreal.of_real_le_of_real_iff _,
    { exact dist_triangle _ _ _ },
    { simpa using add_le_add (dist_nonneg : 0 ≤ dist x y) dist_nonneg }
  end,
  uniformity_edist    := uniformity_edist,
  ..‹metric_space α› }

/-- Balls defined using the distance or the edistance coincide -/
lemma metric.emetric_ball {x : α} {ε : ℝ} : emetric.ball x (ennreal.of_real ε) = ball x ε :=
begin
  classical, by_cases h : 0 < ε,
  { ext y, by simp [edist_dist, ennreal.of_real_lt_of_real_iff h] },
  { have h' : ε ≤ 0, by simpa using h,
    have A : ball x ε = ∅, by simpa [ball_eq_empty_iff_nonpos.symm],
    have B : emetric.ball x (ennreal.of_real ε) = ∅,
      by simp [ennreal.of_real_eq_zero.2 h', emetric.ball_eq_empty_iff],
    rwa [A, B] }
end

/-- Closed balls defined using the distance or the edistance coincide -/
lemma metric.emetric_closed_ball {x : α} {ε : ℝ} (h : 0 ≤ ε) :
  emetric.closed_ball x (ennreal.of_real ε) = closed_ball x ε :=
by ext y; simp [edist_dist]; rw ennreal.of_real_le_of_real_iff h

def metric_space.replace_uniformity {α} [U : uniform_space α] (m : metric_space α)
  (H : @uniformity _ U = @uniformity _ (metric_space.to_uniform_space α)) :
  metric_space α :=
{ dist               := @dist _ m.to_has_dist,
  dist_self          := dist_self,
  eq_of_dist_eq_zero := @eq_of_dist_eq_zero _ _,
  dist_comm          := dist_comm,
  dist_triangle      := dist_triangle,
  edist              := edist,
  edist_dist         := edist_dist,
  to_uniform_space   := U,
  uniformity_dist    := H.trans (metric_space.uniformity_dist α) }

/-- One gets a metric space from an emetric space if the edistance
is everywhere finite. We set it up so that the edist and the uniformity are
defeq in the metric space and the emetric space -/

def emetric_space.to_metric_space {α : Type u} [e : emetric_space α] (h : ∀x y: α, edist x y ≠ ⊤) :
  metric_space α :=
let m : metric_space α :=
{ dist               := λx y, ennreal.to_real (edist x y),
  eq_of_dist_eq_zero := λx y hxy, by simpa [dist, ennreal.to_real_eq_zero_iff, h x y] using hxy,
  dist_self          := λx, by simp,
  dist_comm          := λx y, by simp [emetric_space.edist_comm],
  dist_triangle      := λx y z, begin
    rw [← ennreal.to_real_add (h _ _) (h _ _), ennreal.to_real_le_to_real (h _ _)],
    { exact edist_triangle _ _ _ },
    { simp [ennreal.add_eq_top, h] }
  end,
  edist              := λx y, edist x y,
  edist_dist         := λx y, by simp [ennreal.of_real_to_real, h] } in
metric_space.replace_uniformity m (by rw [uniformity_edist, uniformity_edist']; refl)

section real

/-- Instantiate the reals as a metric space. -/
instance real.metric_space : metric_space ℝ :=
{ dist               := λx y, abs (x - y),
  dist_self          := by simp [abs_zero],
  eq_of_dist_eq_zero := by simp [add_neg_eq_zero],
  dist_comm          := assume x y, abs_sub _ _,
  dist_triangle      := assume x y z, abs_sub_le _ _ _ }

theorem real.dist_eq (x y : ℝ) : dist x y = abs (x - y) := rfl

theorem real.dist_0_eq_abs (x : ℝ) : dist x 0 = abs x :=
by simp [real.dist_eq]

instance : orderable_topology ℝ :=
orderable_topology_of_nhds_abs $ λ x, begin
  simp only [show ∀ r, {b : ℝ | abs (x - b) < r} = ball x r,
    by simp [-sub_eq_add_neg, abs_sub, ball, real.dist_eq]],
  apply le_antisymm,
  { simp [le_infi_iff],
    exact λ ε ε0, mem_nhds_sets (is_open_ball) (mem_ball_self ε0) },
  { intros s h,
    rcases mem_nhds_iff.1 h with ⟨ε, ε0, ss⟩,
    exact mem_infi_sets _ (mem_infi_sets ε0 (mem_principal_sets.2 ss)) },
end

lemma closed_ball_Icc {x r : ℝ} : closed_ball x r = Icc (x-r) (x+r) :=
by ext y; rw [mem_closed_ball, dist_comm, real.dist_eq,
  abs_sub_le_iff, mem_Icc, ← sub_le_iff_le_add', sub_le]

lemma squeeze_zero {α} {f g : α → ℝ} {t₀ : filter α} (hf : ∀t, 0 ≤ f t) (hft : ∀t, f t ≤ g t)
  (g0 : tendsto g t₀ (nhds 0)) : tendsto f t₀ (nhds 0) :=
begin
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds) g0;
  simp [*]; exact filter.univ_mem_sets
end

theorem metric.uniformity_eq_comap_nhds_zero :
  𝓤 α = comap (λp:α×α, dist p.1 p.2) (nhds (0 : ℝ)) :=
begin
  simp only [uniformity_dist', nhds_eq, comap_infi, comap_principal],
  congr, funext ε,
  rw [principal_eq_iff_eq],
  ext ⟨a, b⟩,
  simp [real.dist_0_eq_abs]
end

lemma cauchy_seq_iff_tendsto_dist_at_top_0 [inhabited β] [semilattice_sup β] {u : β → α} :
  cauchy_seq u ↔ tendsto (λ (n : β × β), dist (u n.1) (u n.2)) at_top (nhds 0) :=
by rw [cauchy_seq_iff_prod_map, metric.uniformity_eq_comap_nhds_zero, ← map_le_iff_le_comap,
  filter.map_map, tendsto, prod.map_def]

end real

section cauchy_seq
variables [inhabited β] [semilattice_sup β]

/-- In a metric space, Cauchy sequences are characterized by the fact that, eventually,
the distance between its elements is arbitrarily small -/
theorem metric.cauchy_seq_iff {u : β → α} :
  cauchy_seq u ↔ ∀ε>0, ∃N, ∀m n≥N, dist (u m) (u n) < ε :=
begin
  unfold cauchy_seq,
  rw metric.cauchy_iff,
  simp only [true_and, exists_prop, filter.mem_at_top_sets, filter.at_top_ne_bot,
             filter.mem_map, ne.def, filter.map_eq_bot_iff, not_false_iff, set.mem_set_of_eq],
  split,
  { intros H ε εpos,
    rcases H ε εpos with ⟨t, ⟨N, hN⟩, ht⟩,
    exact ⟨N, λm n hm hn, ht _ _ (hN _ hm) (hN _ hn)⟩ },
  { intros H ε εpos,
    rcases H (ε/2) (half_pos εpos) with ⟨N, hN⟩,
    existsi ball (u N) (ε/2),
    split,
    { exact ⟨N, λx hx, hN _ _ hx (le_refl N)⟩ },
    { exact λx y hx hy, calc
        dist x y ≤ dist x (u N) + dist y (u N) : dist_triangle_right _ _ _
        ... < ε/2 + ε/2 : add_lt_add hx hy
        ... = ε : add_halves _ } }
end

/-- A variation around the metric characterization of Cauchy sequences -/
theorem metric.cauchy_seq_iff' {u : β → α} :
  cauchy_seq u ↔ ∀ε>0, ∃N, ∀n≥N, dist (u n) (u N) < ε :=
begin
  rw metric.cauchy_seq_iff,
  split,
  { intros H ε εpos,
    rcases H ε εpos with ⟨N, hN⟩,
    exact ⟨N, λn hn, hN _ _ hn (le_refl N)⟩ },
  { intros H ε εpos,
    rcases H (ε/2) (half_pos εpos) with ⟨N, hN⟩,
    exact ⟨N, λ m n hm hn, calc
       dist (u m) (u n) ≤ dist (u m) (u N) + dist (u n) (u N) : dist_triangle_right _ _ _
                    ... < ε/2 + ε/2 : add_lt_add (hN _ hm) (hN _ hn)
                    ... = ε : add_halves _⟩ }
end

/-- A Cauchy sequence on the natural numbers is bounded. -/
theorem cauchy_seq_bdd {u : ℕ → α} (hu : cauchy_seq u) :
  ∃ R > 0, ∀ m n, dist (u m) (u n) < R :=
begin
  rcases metric.cauchy_seq_iff'.1 hu 1 zero_lt_one with ⟨N, hN⟩,
  suffices : ∃ R > 0, ∀ n, dist (u n) (u N) < R,
  { rcases this with ⟨R, R0, H⟩,
    exact ⟨_, add_pos R0 R0, λ m n,
      lt_of_le_of_lt (dist_triangle_right _ _ _) (add_lt_add (H m) (H n))⟩ },
  let R := finset.sup (finset.range N) (λ n, nndist (u n) (u N)),
  refine ⟨↑R + 1, add_pos_of_nonneg_of_pos R.2 zero_lt_one, λ n, _⟩,
  cases le_or_lt N n,
  { exact lt_of_lt_of_le (hN _ h) (le_add_of_nonneg_left R.2) },
  { have : _ ≤ R := finset.le_sup (finset.mem_range.2 h),
    exact lt_of_le_of_lt this (lt_add_of_pos_right _ zero_lt_one) }
end

/-- Yet another metric characterization of Cauchy sequences on integers. This one is often the
most efficient. -/
lemma cauchy_seq_iff_le_tendsto_0 {s : ℕ → α} : cauchy_seq s ↔ ∃ b : ℕ → ℝ,
  (∀ n, 0 ≤ b n) ∧
  (∀ n m N : ℕ, N ≤ n → N ≤ m → dist (s n) (s m) ≤ b N) ∧
  tendsto b at_top (nhds 0) :=
⟨λ hs, begin
  /- `s` is a Cauchy sequence. The sequence `b` will be constructed by taking
  the supremum of the distances between `s n` and `s m` for `n m ≥ N`.
  First, we prove that all these distances are bounded, as otherwise the Sup
  would not make sense. -/
  let S := λ N, (λ(p : ℕ × ℕ), dist (s p.1) (s p.2)) '' {p | p.1 ≥ N ∧ p.2 ≥ N},
  have hS : ∀ N, ∃ x, ∀ y ∈ S N, y ≤ x,
  { rcases cauchy_seq_bdd hs with ⟨R, R0, hR⟩,
    refine λ N, ⟨R, _⟩, rintro _ ⟨⟨m, n⟩, _, rfl⟩,
    exact le_of_lt (hR m n) },
  have bdd : bdd_above (range (λ(p : ℕ × ℕ), dist (s p.1) (s p.2))),
  { rcases cauchy_seq_bdd hs with ⟨R, R0, hR⟩,
    use R, rintro _ ⟨⟨m, n⟩, rfl⟩, exact le_of_lt (hR m n) },
  -- Prove that it bounds the distances of points in the Cauchy sequence
  have ub : ∀ m n N, N ≤ m → N ≤ n → dist (s m) (s n) ≤ real.Sup (S N) :=
    λ m n N hm hn, real.le_Sup _ (hS N) ⟨⟨_, _⟩, ⟨hm, hn⟩, rfl⟩,
  have S0m : ∀ n, (0:ℝ) ∈ S n := λ n, ⟨⟨n, n⟩, ⟨le_refl _, le_refl _⟩, dist_self _⟩,
  have S0 := λ n, real.le_Sup _ (hS n) (S0m n),
  -- Prove that it tends to `0`, by using the Cauchy property of `s`
  refine ⟨λ N, real.Sup (S N), S0, ub, metric.tendsto_at_top.2 (λ ε ε0, _)⟩,
  refine (metric.cauchy_seq_iff.1 hs (ε/2) (half_pos ε0)).imp (λ N hN n hn, _),
  rw [real.dist_0_eq_abs, abs_of_nonneg (S0 n)],
  refine lt_of_le_of_lt (real.Sup_le_ub _ ⟨_, S0m _⟩ _) (half_lt_self ε0),
  rintro _ ⟨⟨m', n'⟩, ⟨hm', hn'⟩, rfl⟩,
  exact le_of_lt (hN _ _ (le_trans hn hm') (le_trans hn hn'))
  end,
λ ⟨b, _, b_bound, b_lim⟩, metric.cauchy_seq_iff.2 $ λ ε ε0,
  (metric.tendsto_at_top.1 b_lim ε ε0).imp $ λ N hN m n hm hn,
  calc dist (s m) (s n) ≤ b N : b_bound m n N hm hn
                    ... ≤ abs (b N) : le_abs_self _
                    ... = dist (b N) 0 : by rw real.dist_0_eq_abs; refl
                    ... < ε : (hN _ (le_refl N)) ⟩

end cauchy_seq

def metric_space.induced {α β} (f : α → β) (hf : function.injective f)
  (m : metric_space β) : metric_space α :=
{ dist               := λ x y, dist (f x) (f y),
  dist_self          := λ x, dist_self _,
  eq_of_dist_eq_zero := λ x y h, hf (dist_eq_zero.1 h),
  dist_comm          := λ x y, dist_comm _ _,
  dist_triangle      := λ x y z, dist_triangle _ _ _,
  edist              := λ x y, edist (f x) (f y),
  edist_dist         := λ x y, edist_dist _ _,
  to_uniform_space   := uniform_space.comap f m.to_uniform_space,
  uniformity_dist    := begin
    apply @uniformity_dist_of_mem_uniformity _ _ _ _ _ (λ x y, dist (f x) (f y)),
    refine λ s, mem_comap_sets.trans _,
    split; intro H,
    { rcases H with ⟨r, ru, rs⟩,
      rcases mem_uniformity_dist.1 ru with ⟨ε, ε0, hε⟩,
      refine ⟨ε, ε0, λ a b h, rs (hε _)⟩, exact h },
    { rcases H with ⟨ε, ε0, hε⟩,
      exact ⟨_, dist_mem_uniformity ε0, λ ⟨a, b⟩, hε⟩ }
  end }

instance subtype.metric_space {α : Type*} {p : α → Prop} [t : metric_space α] :
  metric_space (subtype p) :=
metric_space.induced subtype.val (λ x y, subtype.eq) t

theorem subtype.dist_eq {p : α → Prop} (x y : subtype p) : dist x y = dist x.1 y.1 := rfl

section nnreal

instance : metric_space nnreal := by unfold nnreal; apply_instance

end nnreal

section prod

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
  edist := λ x y, max (edist x.1 y.1) (edist x.2 y.2),
  edist_dist := assume x y, begin
    have : monotone ennreal.of_real := assume x y h, ennreal.of_real_le_of_real h,
    rw [edist_dist, edist_dist, (max_distrib_of_monotone this).symm]
  end,
  uniformity_dist := begin
    refine uniformity_prod.trans _,
    simp [uniformity_dist, comap_infi],
    rw ← infi_inf_eq, congr, funext,
    rw ← infi_inf_eq, congr, funext,
    simp [inf_principal, ext_iff, max_lt_iff]
  end,
  to_uniform_space := prod.uniform_space }

lemma prod.dist_eq [metric_space β] {x y : α × β} :
  dist x y = max (dist x.1 y.1) (dist x.2 y.2) := rfl

end prod

theorem uniform_continuous_dist' : uniform_continuous (λp:α×α, dist p.1 p.2) :=
metric.uniform_continuous_iff.2 (λ ε ε0, ⟨ε/2, half_pos ε0,
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
uniform_continuous_dist'.comp (hf.prod_mk hg)

theorem continuous_dist' : continuous (λp:α×α, dist p.1 p.2) :=
uniform_continuous_dist'.continuous

theorem continuous_dist [topological_space β] {f g : β → α}
  (hf : continuous f) (hg : continuous g) : continuous (λb, dist (f b) (g b)) :=
continuous_dist'.comp (hf.prod_mk hg)

theorem tendsto_dist {f g : β → α} {x : filter β} {a b : α}
  (hf : tendsto f x (nhds a)) (hg : tendsto g x (nhds b)) :
  tendsto (λx, dist (f x) (g x)) x (nhds (dist a b)) :=
have tendsto (λp:α×α, dist p.1 p.2) (nhds (a, b)) (nhds (dist a b)),
  from continuous_iff_continuous_at.mp continuous_dist' (a, b),
tendsto.comp (by rw [nhds_prod_eq] at this; exact this) (hf.prod_mk hg)

lemma nhds_comap_dist (a : α) : (nhds (0 : ℝ)).comap (λa', dist a' a) = nhds a :=
have h₁ : ∀ε, (λa', dist a' a) ⁻¹' ball 0 ε ⊆ ball a ε,
  by simp [subset_def, real.dist_0_eq_abs],
have h₂ : tendsto (λa', dist a' a) (nhds a) (nhds (dist a a)),
  from tendsto_dist tendsto_id tendsto_const_nhds,
le_antisymm
  (by simp [h₁, nhds_eq, infi_le_infi, principal_mono,
      -le_principal_iff, -le_infi_iff])
  (by simpa [map_le_iff_le_comap.symm, tendsto] using h₂)

lemma tendsto_iff_dist_tendsto_zero {f : β → α} {x : filter β} {a : α} :
  (tendsto f x (nhds a)) ↔ (tendsto (λb, dist (f b) a) x (nhds 0)) :=
by rw [← nhds_comap_dist a, tendsto_comap_iff]

lemma uniform_continuous_nndist' : uniform_continuous (λp:α×α, nndist p.1 p.2) :=
uniform_continuous_subtype_mk uniform_continuous_dist' _

lemma continuous_nndist' : continuous (λp:α×α, nndist p.1 p.2) :=
uniform_continuous_nndist'.continuous

lemma continuous_nndist [topological_space β] {f g : β → α}
  (hf : continuous f) (hg : continuous g) : continuous (λb, nndist (f b) (g b)) :=
continuous_nndist'.comp (hf.prod_mk hg)

lemma tendsto_nndist' (a b :α) :
  tendsto (λp:α×α, nndist p.1 p.2) (filter.prod (nhds a) (nhds b)) (nhds (nndist a b)) :=
by rw [← nhds_prod_eq]; exact continuous_iff_continuous_at.1 continuous_nndist' _

namespace metric
variables {x y z : α} {ε ε₁ ε₂ : ℝ} {s : set α}

theorem is_closed_ball : is_closed (closed_ball x ε) :=
is_closed_le (continuous_dist continuous_id continuous_const) continuous_const

/-- ε-characterization of the closure in metric spaces-/
theorem mem_closure_iff' {α : Type u} [metric_space α] {s : set α} {a : α} :
  a ∈ closure s ↔ ∀ε>0, ∃b ∈ s, dist a b < ε :=
⟨begin
  intros ha ε hε,
  have A : ball a ε ∩ s ≠ ∅ := mem_closure_iff.1 ha _ is_open_ball (mem_ball_self hε),
  cases ne_empty_iff_exists_mem.1 A with b hb,
  simp,
  exact ⟨b, ⟨hb.2, by have B := hb.1; simpa [mem_ball'] using B⟩⟩
end,
begin
  intros H,
  apply mem_closure_iff.2,
  intros o ho ao,
  rcases is_open_iff.1 ho a ao with ⟨ε, ⟨εpos, hε⟩⟩,
  rcases H ε εpos with ⟨b, ⟨bs, bdist⟩⟩,
  have B : b ∈ o ∩ s := ⟨hε (by simpa [dist_comm]), bs⟩,
  apply ne_empty_of_mem B
end⟩

lemma mem_closure_range_iff {α : Type u} [metric_space α] {e : β → α} {a : α} :
  a ∈ closure (range e) ↔ ∀ε>0, ∃ k : β, dist a (e k) < ε :=
iff.intro
( assume ha ε hε,
  let ⟨b, ⟨hb, hab⟩⟩ := metric.mem_closure_iff'.1 ha ε hε in
  let ⟨k, hk⟩ := mem_range.1 hb in
  ⟨k, by { rw hk, exact hab }⟩ )
( assume h, metric.mem_closure_iff'.2 (assume ε hε,
  let ⟨k, hk⟩ := h ε hε in
  ⟨e k, ⟨mem_range.2 ⟨k, rfl⟩, hk⟩⟩) )

lemma mem_closure_range_iff_nat {α : Type u} [metric_space α] {e : β → α} {a : α} :
  a ∈ closure (range e) ↔ ∀n : ℕ, ∃ k : β, dist a (e k) < 1 / ((n : ℝ) + 1) :=
⟨assume ha n, mem_closure_range_iff.1 ha (1 / ((n : ℝ) + 1)) nat.one_div_pos_of_nat,
 assume h, mem_closure_range_iff.2 $ assume ε hε,
  let ⟨n, hn⟩ := exists_nat_one_div_lt hε in
  let ⟨k, hk⟩ := h n  in
  ⟨k, calc dist a (e k) < 1 / ((n : ℝ) + 1) : hk ... < ε : hn⟩⟩

theorem mem_of_closed' {α : Type u} [metric_space α] {s : set α} (hs : is_closed s)
  {a : α} : a ∈ s ↔ ∀ε>0, ∃b ∈ s, dist a b < ε :=
by simpa only [closure_eq_of_is_closed hs] using @mem_closure_iff' _ _ s a

end metric

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
      simp only [dist_pi_def, (nnreal.coe_add _ _).symm, nnreal.coe_le.symm,
        finset.sup_le_iff],
      assume b hb,
      exact le_trans (nndist_triangle _ (g b) _) (add_le_add (le_sup hb) (le_sup hb))
    end,
  eq_of_dist_eq_zero := assume f g eq0,
    begin
      simp only [dist_pi_def, nnreal.coe_eq_zero, nnreal.bot_eq_zero.symm, eq_bot_iff,
        finset.sup_le_iff] at eq0,
      exact (funext $ assume b, eq_of_nndist_eq_zero $ bot_unique $ eq0 b $ mem_univ b),
    end,
  edist := λ f g, finset.sup univ (λb, edist (f b) (g b)),
  edist_dist := assume x y, begin
    have A : sup univ (λ (b : β), ((nndist (x b) (y b)) : ennreal)) = ↑(sup univ (λ (b : β), nndist (x b) (y b))),
    { refine eq.symm (comp_sup_eq_sup_comp _ _ _),
      exact (assume x y h, ennreal.coe_le_coe.2 h), refl },
    simp [dist, edist_nndist, ennreal.of_real, A]
  end,
  to_uniform_space := Pi.uniform_space _,
  uniformity_dist := begin
    -- with simp only on next line, the proof fails for no reason...
    simp [Pi.uniformity, uniformity_dist, comap_infi, comap_infi, gt_iff_lt, preimage_set_of_eq,
          comap_principal],
    rw infi_comm, congr, funext ε,
    rw infi_comm, congr, funext εpos,
    simp only [ext_iff, εpos, dist, principal_eq_iff_eq, prod.forall, mem_Inter, mem_set_of_eq,
               infi_principal_fintype],
    assume a b,
    let ε' : nnreal := ⟨ε, le_of_lt εpos⟩,
    have A : ε' = nnreal.of_real ε, by simp [nnreal.of_real, ε', le_of_lt εpos],
    change (∀ (i : β), dist (a i) (b i) < ε) ↔ (sup univ (λ (i : β), nndist (a i) (b i))) < ε',
    simp only [finset.sup_lt_iff (show ⊥ < ε', from εpos)],
    simp [nndist_dist, A, εpos],
  end }

end pi

section compact

/-- Any compact set in a metric space can be covered by finitely many balls of a given positive
radius -/
lemma finite_cover_balls_of_compact {α : Type u} [metric_space α] {s : set α}
  (hs : compact s) {e : ℝ} (he : e > 0) :
  ∃t ⊆ s, finite t ∧ s ⊆ ⋃x∈t, ball x e :=
begin
  apply compact_elim_finite_subcover_image hs,
  { simp [is_open_ball] },
  { intros x xs,
    simp,
    exact ⟨x, ⟨xs, by simpa⟩⟩ }
end

end compact

section proper_space
open metric

/-- A metric space is proper if all closed balls are compact. -/
class proper_space (α : Type u) [metric_space α] : Prop :=
(compact_ball : ∀x:α, ∀r, compact (closed_ball x r))

/- A compact metric space is proper -/
instance proper_of_compact [compact_space α] : proper_space α :=
⟨assume x r, compact_of_is_closed_subset compact_univ is_closed_ball (subset_univ _)⟩

/-- A proper space is locally compact -/
instance locally_compact_of_proper [proper_space α] :
  locally_compact_space α :=
begin
  apply locally_compact_of_compact_nhds,
  intros x,
  existsi closed_ball x 1,
  split,
  { apply mem_nhds_iff.2,
    existsi (1 : ℝ),
    simp,
    exact ⟨zero_lt_one, ball_subset_closed_ball⟩ },
  { apply proper_space.compact_ball }
end

/-- A proper space is complete -/
instance complete_of_proper [proper_space α] : complete_space α :=
⟨begin
  intros f hf,
  /- We want to show that the Cauchy filter `f` is converging. It suffices to find a closed
  ball (therefore compact by properness) where it is nontrivial. -/
  have A : ∃ t ∈ f, ∀ x y ∈ t, dist x y < 1 := (metric.cauchy_iff.1 hf).2 1 zero_lt_one,
  rcases A with ⟨t, ⟨t_fset, ht⟩⟩,
  rcases inhabited_of_mem_sets hf.1 t_fset with ⟨x, xt⟩,
  have : t ⊆ closed_ball x 1 := by intros y yt; simp [dist_comm]; apply le_of_lt (ht x y xt yt),
  have : closed_ball x 1 ∈ f := f.sets_of_superset t_fset this,
  rcases (compact_iff_totally_bounded_complete.1 (proper_space.compact_ball x 1)).2 f hf (le_principal_iff.2 this)
    with ⟨y, _, hy⟩,
  exact ⟨y, hy⟩
end⟩

/-- A proper metric space is separable, and therefore second countable. Indeed, any ball is
compact, and therefore admits a countable dense subset. Taking a countable union over the balls
centered at a fixed point and with integer radius, one obtains a countable set which is
dense in the whole space. -/
instance second_countable_of_proper [proper_space α] :
  second_countable_topology α :=
begin
  /- We show that the space admits a countable dense subset. The case where the space is empty
  is special, and trivial. -/
  have A : (univ : set α) = ∅ → ∃(s : set α), countable s ∧ closure s = (univ : set α) :=
    assume H, ⟨∅, ⟨by simp, by simp; exact H.symm⟩⟩,
  have B : (univ : set α) ≠ ∅ → ∃(s : set α), countable s ∧ closure s = (univ : set α) :=
  begin
    /- When the space is not empty, we take a point `x` in the space, and then a countable set
    `T r` which is dense in the closed ball `closed_ball x r` for each `r`. Then the set
    `t = ⋃ T n` (where the union is over all integers `n`) is countable, as a countable union
    of countable sets, and dense in the space by construction. -/
    assume non_empty,
    rcases ne_empty_iff_exists_mem.1 non_empty with ⟨x, x_univ⟩,
    choose T a using show ∀ (r:ℝ), ∃ t ⊆ closed_ball x r, (countable (t : set α) ∧ closed_ball x r = closure t),
      from assume r, emetric.countable_closure_of_compact (proper_space.compact_ball _ _),
    let t := (⋃n:ℕ, T (n : ℝ)),
    have T₁ : countable t := by finish [countable_Union],
    have T₂ : closure t ⊆ univ := by simp,
    have T₃ : univ ⊆ closure t :=
    begin
      intros y y_univ,
      rcases exists_nat_gt (dist y x) with ⟨n, n_large⟩,
      have h : y ∈ closed_ball x (n : ℝ) := by simp; apply le_of_lt n_large,
      have h' : closed_ball x (n : ℝ) = closure (T (n : ℝ)) := by finish,
      have : y ∈ closure (T (n : ℝ)) := by rwa h' at h,
      show y ∈ closure t, from mem_of_mem_of_subset this (by apply closure_mono; apply subset_Union (λ(n:ℕ), T (n:ℝ))),
    end,
    exact ⟨t, ⟨T₁, subset.antisymm T₂ T₃⟩⟩
  end,
  haveI : separable_space α := ⟨by_cases A B⟩,
  apply emetric.second_countable_of_separable,
end

end proper_space

namespace metric
section second_countable
open topological_space

/-- A metric space is second countable if, for every ε > 0, there is a countable set which is ε-dense. -/
lemma second_countable_of_almost_dense_set
  (H : ∀ε > (0 : ℝ), ∃ s : set α, countable s ∧ (∀x, ∃y ∈ s, dist x y ≤ ε)) :
  second_countable_topology α :=
begin
  choose T T_dense using H,
  have I1 : ∀n:ℕ, (n:ℝ) + 1 > 0 :=
    λn, lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left (nat.cast_nonneg _)),
  have I : ∀n:ℕ, (n+1 : ℝ)⁻¹ > 0 := λn, inv_pos'.2 (I1 n),
  let t := ⋃n:ℕ, T (n+1)⁻¹ (I n),
  have count_t : countable t := by finish [countable_Union],
  have clos_t : closure t = univ,
  { refine subset.antisymm (subset_univ _) (λx xuniv, mem_closure_iff'.2 (λε εpos, _)),
    rcases exists_nat_gt ε⁻¹ with ⟨n, hn⟩,
    have : ε⁻¹ < n + 1 := lt_of_lt_of_le hn (le_add_of_nonneg_right zero_le_one),
    have nε : ((n:ℝ)+1)⁻¹ < ε := (inv_lt (I1 n) εpos).2 this,
    rcases (T_dense (n+1)⁻¹ (I n)).2 x with ⟨y, yT, Dxy⟩,
    have : y ∈ t := mem_of_mem_of_subset yT (by apply subset_Union (λ (n:ℕ), T (n+1)⁻¹ (I n))),
    exact ⟨y, this, lt_of_le_of_lt Dxy nε⟩ },
  haveI : separable_space α := ⟨⟨t, ⟨count_t, clos_t⟩⟩⟩,
  exact emetric.second_countable_of_separable α
end

/-- A metric space space is second countable if one can reconstruct up to any ε>0 any element of the
space from countably many data. -/
lemma second_countable_of_countable_discretization {α : Type u} [metric_space α]
  (H : ∀ε > (0 : ℝ), ∃ (β : Type u) [encodable β] (F : α → β), ∀x y, F x = F y → dist x y ≤ ε) :
  second_countable_topology α :=
begin
  classical, by_cases hs : (univ : set α) = ∅,
  { haveI : compact_space α := ⟨by rw hs; exact compact_of_finite (set.finite_empty)⟩, by apply_instance },
  rcases exists_mem_of_ne_empty hs with ⟨x0, hx0⟩,
  letI : inhabited α := ⟨x0⟩,
  refine second_countable_of_almost_dense_set (λε ε0, _),
  rcases H ε ε0 with ⟨β, fβ, F, hF⟩,
  let Finv := function.inv_fun F,
  refine ⟨range Finv, ⟨countable_range _, λx, _⟩⟩,
  let x' := Finv (F x),
  have : F x' = F x := function.inv_fun_eq ⟨x, rfl⟩,
  exact ⟨x', mem_range_self _, hF _ _ this.symm⟩
end

end second_countable
end metric

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

namespace metric

/-- Boundedness of a subset of a metric space. We formulate the definition to work
even in the empty space. -/
def bounded (s : set α) : Prop :=
∃C, ∀x y ∈ s, dist x y ≤ C

section bounded
variables {x : α} {s t : set α} {r : ℝ}

@[simp] lemma bounded_empty : bounded (∅ : set α) :=
⟨0, by simp⟩

lemma bounded_iff_mem_bounded : bounded s ↔ ∀ x ∈ s, bounded s :=
⟨λ h _ _, h, λ H, begin
  classical, by_cases s = ∅,
  { subst s, exact ⟨0, by simp⟩ },
  { rcases exists_mem_of_ne_empty h with ⟨x, hx⟩,
    exact H x hx }
end⟩

/-- Subsets of a bounded set are also bounded -/
lemma bounded.subset (incl : s ⊆ t) : bounded t → bounded s :=
Exists.imp $ λ C hC x y hx hy, hC x y (incl hx) (incl hy)

/-- Closed balls are bounded -/
lemma bounded_closed_ball : bounded (closed_ball x r) :=
⟨r + r, λ y z hy hz, begin
  simp only [mem_closed_ball] at *,
  calc dist y z ≤ dist y x + dist z x : dist_triangle_right _ _ _
            ... ≤ r + r : add_le_add hy hz
end⟩

/-- Open balls are bounded -/
lemma bounded_ball : bounded (ball x r) :=
bounded_closed_ball.subset ball_subset_closed_ball

/-- Given a point, a bounded subset is included in some ball around this point -/
lemma bounded_iff_subset_ball (c : α) : bounded s ↔ ∃r, s ⊆ closed_ball c r :=
begin
  split; rintro ⟨C, hC⟩,
  { classical, by_cases s = ∅,
    { subst s, exact ⟨0, by simp⟩ },
    { rcases exists_mem_of_ne_empty h with ⟨x, hx⟩,
      exact ⟨C + dist x c, λ y hy, calc
        dist y c ≤ dist y x + dist x c : dist_triangle _ _ _
            ... ≤ C + dist x c : add_le_add_right (hC y x hy hx) _⟩ } },
  { exact bounded_closed_ball.subset hC }
end

/-- The union of two bounded sets is bounded iff each of the sets is bounded -/
@[simp] lemma bounded_union :
  bounded (s ∪ t) ↔ bounded s ∧ bounded t :=
⟨λh, ⟨h.subset (by simp), h.subset (by simp)⟩,
begin
  rintro ⟨hs, ht⟩,
  refine bounded_iff_mem_bounded.2 (λ x _, _),
  rw bounded_iff_subset_ball x at hs ht ⊢,
  rcases hs with ⟨Cs, hCs⟩, rcases ht with ⟨Ct, hCt⟩,
  exact ⟨max Cs Ct, union_subset
    (subset.trans hCs $ closed_ball_subset_closed_ball $ le_max_left _ _)
    (subset.trans hCt $ closed_ball_subset_closed_ball $ le_max_right _ _)⟩,
end⟩

/-- A finite union of bounded sets is bounded -/
lemma bounded_bUnion {I : set β} {s : β → set α} (H : finite I) :
  bounded (⋃i∈I, s i) ↔ ∀i ∈ I, bounded (s i) :=
finite.induction_on H (by simp) $ λ x I _ _ IH,
by simp [or_imp_distrib, forall_and_distrib, IH]

/-- A compact set is bounded -/
lemma bounded_of_compact {s : set α} (h : compact s) : bounded s :=
-- We cover the compact set by finitely many balls of radius 1,
-- and then argue that a finite union of bounded sets is bounded
let ⟨t, ht, fint, subs⟩ := finite_cover_balls_of_compact h zero_lt_one in
bounded.subset subs $ (bounded_bUnion fint).2 $ λ i hi, bounded_ball

/-- A finite set is bounded -/
lemma bounded_of_finite {s : set α} (h : finite s) : bounded s :=
bounded_of_compact $ compact_of_finite h

/-- A singleton is bounded -/
lemma bounded_singleton {x : α} : bounded ({x} : set α) :=
bounded_of_finite $ finite_singleton _

/-- Characterization of the boundedness of the range of a function -/
lemma bounded_range_iff {f : β → α} : bounded (range f) ↔ ∃C, ∀x y, dist (f x) (f y) ≤ C :=
exists_congr $ λ C, ⟨
  λ H x y, H _ _ ⟨x, rfl⟩ ⟨y, rfl⟩,
  by rintro H _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact H x y⟩

/-- In a compact space, all sets are bounded -/
lemma bounded_of_compact_space [compact_space α] : bounded s :=
(bounded_of_compact compact_univ).subset (subset_univ _)

/-- In a proper space, a set is compact if and only if it is closed and bounded -/
lemma compact_iff_closed_bounded [proper_space α] :
  compact s ↔ is_closed s ∧ bounded s :=
⟨λ h, ⟨closed_of_compact _ h, bounded_of_compact h⟩, begin
  rintro ⟨hc, hb⟩,
  classical, by_cases s = ∅, {simp [h, compact_empty]},
  rcases exists_mem_of_ne_empty h with ⟨x, hx⟩,
  rcases (bounded_iff_subset_ball x).1 hb with ⟨r, hr⟩,
  exact compact_of_is_closed_subset (proper_space.compact_ball x r) hc hr
end⟩

end bounded

section diam
variables {s : set α} {x y : α}

/-- The diameter of a set in a metric space. To get controllable behavior even when the diameter
should be infinite, we express it in terms of the emetric.diameter -/
def diam (s : set α) : ℝ := ennreal.to_real (emetric.diam s)

/-- The diameter of a set is always nonnegative -/
lemma diam_nonneg : 0 ≤ diam s :=
by simp [diam]

/-- The empty set has zero diameter -/
@[simp] lemma diam_empty : diam (∅ : set α) = 0 :=
by simp [diam]

/-- A singleton has zero diameter -/
@[simp] lemma diam_singleton : diam ({x} : set α) = 0 :=
by simp [diam]

/-- Characterize the boundedness of a set in terms of the finiteness of its emetric.diameter. -/
lemma bounded_iff_diam_ne_top : bounded s ↔ emetric.diam s ≠ ⊤ :=
begin
  classical, by_cases hs : s = ∅,
  { simp [hs] },
  { rcases ne_empty_iff_exists_mem.1 hs with ⟨x, hx⟩,
    split,
    { assume bs,
      rcases (bounded_iff_subset_ball x).1 bs with ⟨r, hr⟩,
      have r0 : 0 ≤ r := by simpa [closed_ball] using hr hx,
      have : emetric.diam s < ⊤ := calc
        emetric.diam s ≤ emetric.diam (emetric.closed_ball x (ennreal.of_real r)) :
          by rw emetric_closed_ball r0; exact emetric.diam_mono hr
        ... ≤ 2 * (ennreal.of_real r) : emetric.diam_closed_ball
        ... < ⊤ : begin apply ennreal.lt_top_iff_ne_top.2, simp [ennreal.mul_eq_top], end,
      exact ennreal.lt_top_iff_ne_top.1 this },
    { assume ds,
      have : s ⊆ closed_ball x (ennreal.to_real (emetric.diam s)),
      { rw [← emetric_closed_ball ennreal.to_real_nonneg, ennreal.of_real_to_real ds],
        exact λy hy, emetric.edist_le_diam_of_mem hy hx },
      exact bounded.subset this (bounded_closed_ball) }}
end

/-- An unbounded set has zero diameter. If you would prefer to get the value ∞, use `emetric.diam`.
This lemma makes it possible to avoid side conditions in some situations -/
lemma diam_eq_zero_of_unbounded (h : ¬(bounded s)) : diam s = 0 :=
begin
  simp only [bounded_iff_diam_ne_top, not_not, ne.def] at h,
  simp [diam, h]
end

/-- If `s ⊆ t`, then the diameter of `s` is bounded by that of `t`, provided `t` is bounded. -/
lemma diam_mono {s t : set α} (h : s ⊆ t) (ht : bounded t) : diam s ≤ diam t :=
begin
  unfold diam,
  rw ennreal.to_real_le_to_real (bounded_iff_diam_ne_top.1 (bounded.subset h ht)) (bounded_iff_diam_ne_top.1 ht),
  exact emetric.diam_mono h
end

/-- The distance between two points in a set is controlled by the diameter of the set. -/
lemma dist_le_diam_of_mem (h : bounded s) (hx : x ∈ s) (hy : y ∈ s) : dist x y ≤ diam s :=
begin
  rw [diam, dist_edist],
  rw ennreal.to_real_le_to_real (edist_ne_top _ _) (bounded_iff_diam_ne_top.1 h),
  exact emetric.edist_le_diam_of_mem hx hy
end

/-- If the distance between any two points in a set is bounded by some constant, this constant
bounds the diameter. -/
lemma diam_le_of_forall_dist_le {d : real} (hd : d ≥ 0) (h : ∀x y ∈ s, dist x y ≤ d) : diam s ≤ d :=
begin
  have I : emetric.diam s ≤ ennreal.of_real d,
  { refine emetric.diam_le_of_forall_edist_le (λx y hx hy, _),
    rw [edist_dist],
    exact ennreal.of_real_le_of_real (h x y hx hy) },
  have A : emetric.diam s ≠ ⊤ :=
    ennreal.lt_top_iff_ne_top.1 (lt_of_le_of_lt I (ennreal.lt_top_iff_ne_top.2 (by simp))),
  rw [← ennreal.to_real_of_real hd, diam, ennreal.to_real_le_to_real A],
  { exact I },
  { simp }
end

/-- The diameter of a union is controlled by the sum of the diameters, and the distance between
any two points in each of the sets. This lemma is true without any side condition, since it is
obviously true if `s ∪ t` is unbounded. -/
lemma diam_union {t : set α} (xs : x ∈ s) (yt : y ∈ t) : diam (s ∪ t) ≤ diam s + dist x y + diam t :=
have I1 : ¬(bounded (s ∪ t)) → diam (s ∪ t) ≤ diam s + dist x y + diam t := λh, calc
  diam (s ∪ t) = 0 + 0 + 0 : by simp [diam_eq_zero_of_unbounded h]
  ... ≤ diam s + dist x y + diam t : add_le_add (add_le_add diam_nonneg dist_nonneg) diam_nonneg,
have I2 : (bounded (s ∪ t)) → diam (s ∪ t) ≤ diam s + dist x y + diam t := λh,
begin
  have : bounded s := bounded.subset (subset_union_left _ _) h,
  have : bounded t := bounded.subset (subset_union_right _ _) h,
  have A : ∀a ∈ s, ∀b ∈ t, dist a b ≤ diam s + dist x y + diam t := λa ha b hb, calc
    dist a b ≤ dist a x + dist x y + dist y b : dist_triangle4 _ _ _ _
    ... ≤ diam s + dist x y + diam t :
      add_le_add (add_le_add (dist_le_diam_of_mem ‹bounded s› ha xs) (le_refl _)) (dist_le_diam_of_mem ‹bounded t› yt hb),
  have B : ∀a b ∈ s ∪ t, dist a b ≤ diam s + dist x y + diam t := λa b ha hb,
  begin
    cases (mem_union _ _ _).1 ha with h'a h'a; cases (mem_union _ _ _).1 hb with h'b h'b,
    { calc dist a b ≤ diam s : dist_le_diam_of_mem ‹bounded s› h'a h'b
           ... = diam s + (0 + 0) : by simp
           ... ≤ diam s + (dist x y + diam t) : add_le_add (le_refl _) (add_le_add dist_nonneg diam_nonneg)
           ... = diam s + dist x y + diam t : by simp only [add_comm, eq_self_iff_true, add_left_comm] },
    { exact A a h'a b h'b },
    { have Z := A b h'b a h'a, rwa [dist_comm] at Z },
    { calc dist a b ≤ diam t : dist_le_diam_of_mem ‹bounded t› h'a h'b
           ... = (0 + 0) + diam t : by simp
           ... ≤ (diam s + dist x y) + diam t : add_le_add (add_le_add diam_nonneg dist_nonneg) (le_refl _) }
  end,
  have C : 0 ≤ diam s + dist x y + diam t := calc
    0 = 0 + 0 + 0 : by simp
    ... ≤ diam s + dist x y + diam t : add_le_add (add_le_add diam_nonneg dist_nonneg) diam_nonneg,
  exact diam_le_of_forall_dist_le C B
end,
classical.by_cases I2 I1

/-- If two sets intersect, the diameter of the union is bounded by the sum of the diameters. -/
lemma diam_union' {t : set α} (h : s ∩ t ≠ ∅) : diam (s ∪ t) ≤ diam s + diam t :=
begin
  rcases ne_empty_iff_exists_mem.1 h with ⟨x, ⟨xs, xt⟩⟩,
  simpa using diam_union xs xt
end

/-- The diameter of a closed ball of radius `r` is at most `2 r`. -/
lemma diam_closed_ball {r : ℝ} (h : r ≥ 0) : diam (closed_ball x r) ≤ 2 * r :=
diam_le_of_forall_dist_le (mul_nonneg (by norm_num) h) $ λa b ha hb, calc
  dist a b ≤ dist a x + dist b x : dist_triangle_right _ _ _
  ... ≤ r + r : add_le_add ha hb
  ... = 2 * r : by simp [mul_two, mul_comm]

/-- The diameter of a ball of radius `r` is at most `2 r`. -/
lemma diam_ball {r : ℝ} (h : r ≥ 0) : diam (ball x r) ≤ 2 * r :=
le_trans (diam_mono ball_subset_closed_ball bounded_closed_ball) (diam_closed_ball h)

end diam

end metric

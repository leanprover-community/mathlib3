/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sébastien Gouëzel
-/
import topology.uniform_space.completion
import topology.metric_space.isometry

/-!
# The completion of a metric space

Completion of uniform spaces are already defined in `topology.uniform_space.completion`. We show
here that the uniform space completion of a metric space inherits a metric space structure,
by extending the distance to the completion and checking that it is indeed a distance, and that
it defines the same uniformity as the already defined uniform structure on the completion
-/

open set filter uniform_space uniform_space.completion
noncomputable theory

universes u
variables {α : Type u} [metric_space α]

namespace metric

/-- The distance on the completion is obtained by extending the distance on the original space,
by uniform continuity. -/
instance : has_dist (completion α) :=
⟨completion.extension₂ dist⟩

/-- The new distance is uniformly continuous. -/
protected lemma completion.uniform_continuous_dist :
  uniform_continuous (λp:completion α × completion α, dist p.1 p.2) :=
uniform_continuous_extension₂ dist

/-- The new distance is an extension of the original distance. -/
protected lemma completion.dist_eq (x y : α) : dist (x : completion α) y = dist x y :=
completion.extension₂_coe_coe uniform_continuous_dist' _ _

/- Let us check that the new distance satisfies the axioms of a distance, by starting from the
properties on α and extending them to `completion α` by continuity. -/
protected lemma completion.dist_self (x : completion α) : dist x x = 0 :=
begin
  apply induction_on x,
  { refine is_closed_eq _ continuous_const,
    exact (completion.uniform_continuous_dist.continuous.comp
             (continuous.prod_mk continuous_id continuous_id) : _) },
  { assume a,
    rw [completion.dist_eq, dist_self] }
end

protected lemma completion.dist_comm (x y : completion α) : dist x y = dist y x :=
begin
  apply induction_on₂ x y,
  { refine is_closed_eq completion.uniform_continuous_dist.continuous _,
    exact (completion.uniform_continuous_dist.continuous.comp continuous_swap : _) },
  { assume a b,
    rw [completion.dist_eq, completion.dist_eq, dist_comm] }
end

protected lemma completion.dist_triangle (x y z : completion α) : dist x z ≤ dist x y + dist y z :=
begin
  apply induction_on₃ x y z,
  { refine is_closed_le _ (continuous.add _ _),
    { have : continuous (λp : completion α × completion α × completion α, (p.1, p.2.2)) :=
        continuous.prod_mk continuous_fst (continuous.comp continuous_snd continuous_snd),
      exact (completion.uniform_continuous_dist.continuous.comp this : _) },
    { have : continuous (λp : completion α × completion α × completion α, (p.1, p.2.1)) :=
        continuous.prod_mk continuous_fst (continuous_fst.comp continuous_snd),
      exact (completion.uniform_continuous_dist.continuous.comp this : _) },
    { have : continuous (λp : completion α × completion α × completion α, (p.2.1, p.2.2)) :=
        continuous.prod_mk (continuous_fst.comp continuous_snd)
                           (continuous.comp continuous_snd continuous_snd),
      exact (continuous.comp completion.uniform_continuous_dist.continuous this : _) } },
  { assume a b c,
    rw [completion.dist_eq, completion.dist_eq, completion.dist_eq],
    exact dist_triangle a b c }
end

/-- Elements of the uniformity (defined generally for completions) can be characterized in terms
of the distance. -/
@[nolint ge_or_gt] -- see Note [nolint_ge]
protected lemma completion.mem_uniformity_dist (s : set (completion α × completion α)) :
  s ∈ uniformity (completion α) ↔ (∃ε>0, ∀{a b}, dist a b < ε → (a, b) ∈ s) :=
begin
  split,
  { /- Start from an entourage `s`. It contains a closed entourage `t`. Its pullback in α is an
    entourage, so it contains an ε-neighborhood of the diagonal by definition of the entourages
    in metric spaces. Then `t` contains an ε-neighborhood of the diagonal in `completion α`, as
    closed properties pass to the completion. -/
    assume hs,
    rcases mem_uniformity_is_closed hs with ⟨t, ht, ⟨tclosed, ts⟩⟩,
    have A : {x : α × α | (coe (x.1), coe (x.2)) ∈ t} ∈ uniformity α :=
      uniform_continuous_def.1 (uniform_continuous_coe α) t ht,
    rcases mem_uniformity_dist.1 A with ⟨ε, εpos, hε⟩,
    refine ⟨ε, εpos, λx y hxy, _⟩,
    have : ε ≤ dist x y ∨ (x, y) ∈ t,
    { apply induction_on₂ x y,
      { have : {x : completion α × completion α | ε ≤ dist (x.fst) (x.snd) ∨ (x.fst, x.snd) ∈ t}
               = {p : completion α × completion α | ε ≤ dist p.1 p.2} ∪ t, by ext; simp,
        rw this,
        apply is_closed_union _ tclosed,
        exact is_closed_le continuous_const completion.uniform_continuous_dist.continuous },
      { assume x y,
        rw completion.dist_eq,
        by_cases h : ε ≤ dist x y,
        { exact or.inl h },
        { have Z := hε (not_le.1 h),
          simp only [set.mem_set_of_eq] at Z,
          exact or.inr Z }}},
    simp only [not_le.mpr hxy, false_or, not_le] at this,
    exact ts this },
  { /- Start from a set `s` containing an ε-neighborhood of the diagonal in `completion α`. To show
    that it is an entourage, we use the fact that `dist` is uniformly continuous on
    `completion α × completion α` (this is a general property of the extension of uniformly
    continuous functions). Therefore, the preimage of the ε-neighborhood of the diagonal in ℝ
    is an entourage in `completion α × completion α`. Massaging this property, it follows that
    the ε-neighborhood of the diagonal is an entourage in `completion α`, and therefore this is
    also the case of `s`. -/
    rintros ⟨ε, εpos, hε⟩,
    let r : set (ℝ × ℝ) := {p | dist p.1 p.2 < ε},
    have : r ∈ uniformity ℝ := metric.dist_mem_uniformity εpos,
    have T := uniform_continuous_def.1 (@completion.uniform_continuous_dist α _) r this,
    simp only [uniformity_prod_eq_prod, mem_prod_iff, exists_prop,
               filter.mem_map, set.mem_set_of_eq] at T,
    rcases T with ⟨t1, ht1, t2, ht2, ht⟩,
    refine mem_sets_of_superset ht1 _,
    have A : ∀a b : completion α, (a, b) ∈ t1 → dist a b < ε,
    { assume a b hab,
      have : ((a, b), (a, a)) ∈ set.prod t1 t2 := ⟨hab, refl_mem_uniformity ht2⟩,
      have I := ht this,
      simp [completion.dist_self, real.dist_eq, completion.dist_comm] at I,
      exact lt_of_le_of_lt (le_abs_self _) I },
    show t1 ⊆ s,
    { rintros ⟨a, b⟩ hp,
      have : dist a b < ε := A a b hp,
      exact hε this }}
end

/-- If two points are at distance 0, then they coincide. -/
protected lemma completion.eq_of_dist_eq_zero (x y : completion α) (h : dist x y = 0) : x = y :=
begin
  /- This follows from the separation of `completion α` and from the description of
  entourages in terms of the distance. -/
  have : separated (completion α) := by apply_instance,
  refine separated_def.1 this x y (λs hs, _),
  rcases (completion.mem_uniformity_dist s).1 hs with ⟨ε, εpos, hε⟩,
  rw ← h at εpos,
  exact hε εpos
end

/- Reformulate `completion.mem_uniformity_dist` in terms that are suitable for the definition
of the metric space structure. -/
@[nolint ge_or_gt] -- see Note [nolint_ge]
protected lemma completion.uniformity_dist' :
  uniformity (completion α) = (⨅ε:{ε:ℝ // ε>0}, principal {p | dist p.1 p.2 < ε.val}) :=
begin
  ext s, rw mem_infi,
  { simp [completion.mem_uniformity_dist, subset_def] },
  { rintro ⟨r, hr⟩ ⟨p, hp⟩, use ⟨min r p, lt_min hr hp⟩,
    simp [lt_min_iff, (≥)] {contextual := tt} },
  { exact ⟨⟨1, zero_lt_one⟩⟩ }
end

@[nolint ge_or_gt] -- see Note [nolint_ge]
protected lemma completion.uniformity_dist :
  uniformity (completion α) = (⨅ ε>0, principal {p | dist p.1 p.2 < ε}) :=
by simpa [infi_subtype] using @completion.uniformity_dist' α _

/-- Metric space structure on the completion of a metric space. -/
instance completion.metric_space : metric_space (completion α) :=
{ dist_self          := completion.dist_self,
  eq_of_dist_eq_zero := completion.eq_of_dist_eq_zero,
  dist_comm          := completion.dist_comm,
  dist_triangle      := completion.dist_triangle,
  to_uniform_space   := by apply_instance,
  uniformity_dist    := completion.uniformity_dist }

/-- The embedding of a metric space in its completion is an isometry. -/
lemma completion.coe_isometry : isometry (coe : α → completion α) :=
isometry_emetric_iff_metric.2 completion.dist_eq

end metric

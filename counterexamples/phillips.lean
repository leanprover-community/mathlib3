/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.normed_space.hahn_banach
import measure_theory.measure.lebesgue

/-!
# A counterexample on Pettis integrability

There are several theories of integration for functions taking values in Banach spaces. Bochner
integration, requiring approximation by simple functions, is the analogue of the one-dimensional
theory. It is very well behaved, but only works for functions with second-countable range.

For functions `f` taking values in a larger Banach space `B`, one can define the Dunford integral
as follows. Assume that, for all continuous linear functional `φ`, the function `φ ∘ f` is
measurable (we say that `f` is weakly measurable, or scalarly measurable) and integrable.
Then `φ ↦ ∫ φ ∘ f` is continuous (by the closed graph theorem), and therefore defines an element
of the bidual `B**`. This is the Dunford integral of `f`.

This Dunford integral is not usable in practice as it does not belong to the right space. Let us
say that a function is Pettis integrable if its Dunford integral belongs to the canonical image of
`B` in `B**`. In this case, we define the Pettis integral as the Dunford integral inside `B`.

This integral is very general, but not really usable to do analysis. This file illustrates this,
by giving an example of a function with nice properties but which is *not* Pettis-integrable.
This function:
- is defined from `[0, 1]` to a complete Banach space;
- is weakly measurable;
- has norm everywhere bounded by `1` (in particular, its norm is integrable);
- and yet it is not Pettis-integrable with respect to Lebesgue measure.

This construction is due to [Ralph S. Phillips, *Integration in a convex linear
topological space*][phillips1940], in Example 10.8. It requires the continuum hypothesis. The
example is the following.

Under the continuum hypothesis, one can find a subset of `ℝ²` which,
along each vertical line, only misses a countable set of points, while it is countable along each
horizontal line. This is due to Sierpinski, and formalized in `sierpinski_pathological_family`.
(In fact, Sierpinski proves that the existence of such a set is equivalent to the continuum
hypothesis).

Let `B` be the set of all bounded functions on `ℝ` (we are really talking about everywhere defined
functions here). Define `f : ℝ → B` by taking `f x` to be the characteristic function of the
vertical slice at position `x` of Sierpinski's set. It is our counterexample.

To show that it is weakly measurable, we should consider `φ ∘ f` where `φ` is an arbitrary
continuous linear form on `B`. There is no reasonable classification of such linear forms (they can
be very wild). But if one restricts such a linear form to characteristic functions, one gets a
finitely additive signed "measure". Such a "measure" can be decomposed into a discrete part
(supported on a countable set) and a continuous part (giving zero mass to countable sets).
For all but countably many points, `f x` will not intersect the discrete support of `φ` thanks to
the definition of the Sierpinski set. This implies that `φ ∘ f` is constant outside of a countable
set, and equal to the total mass of the continuous part of `φ` there. In particular, it is
measurable (and its integral is the total mass of the continuous part of `φ`).

Assume that `f` has a Pettis integral `g`. For all continuous linear form `φ`, then `φ g` should
be the total mass of the continuous part of `φ`. Taking for `φ` the evaluation at the point `x`
(which has no continuous part), one gets `g x = 0`. Take then for `φ` the Lebesgue integral on
`[0, 1]` (or rather an arbitrary extension of Lebesgue integration to all bounded functions,
thanks to Hahn-Banach). Then `φ g` should be the total mass of the continuous part of `φ`,
which is `1`. This contradicts the fact that `g = 0`, and concludes the proof that `f` has no
Pettis integral.

## Implementation notes

The space of all bounded functions is defined as the space of all bounded continuous functions
on a discrete copy of the original type, as mathlib only contains the space of all bounded
continuous functions (which is the useful one).
-/

universe u
variables {α : Type u}
open set bounded_continuous_function measure_theory
open cardinal (aleph)
open_locale cardinal bounded_continuous_function

noncomputable theory

/-- A copy of a type, endowed with the discrete topology -/
def discrete_copy (α : Type u) : Type u := α

instance : topological_space (discrete_copy α) := ⊥
instance : discrete_topology (discrete_copy α) := ⟨rfl⟩
instance [inhabited α] : inhabited (discrete_copy α) := ⟨id default α⟩

namespace phillips_1940

/-!
### Extending the integral

Thanks to Hahn-Banach, one can define a (non-canonical) continuous linear functional on the space
of all bounded functions, coinciding with the integral on the integrable ones.
-/

/-- The subspace of integrable functions in the space of all bounded functions on a type.
This is a technical device, used to apply Hahn-Banach theorem to construct an extension of the
integral to all bounded functions. -/
def bounded_integrable_functions [measurable_space α] (μ : measure α) :
  subspace ℝ (discrete_copy α →ᵇ ℝ) :=
{ carrier   := {f | integrable f μ},
  zero_mem' := integrable_zero _ _ _,
  add_mem'  := λ f g hf hg, integrable.add hf hg,
  smul_mem' := λ c f hf, integrable.smul c hf }

/-- The integral, as a continuous linear map on the subspace of integrable functions in the space
of all bounded functions on a type. This is a technical device, that we will extend through
Hahn-Banach. -/
def bounded_integrable_functions_integral_clm [measurable_space α]
  (μ : measure α) [is_finite_measure μ] : bounded_integrable_functions μ →L[ℝ] ℝ :=
linear_map.mk_continuous
  { to_fun := λ f, ∫ x, f x ∂μ,
    map_add' := λ f g, integral_add f.2 g.2,
    map_smul' := λ c f, integral_smul _ _ }
  (μ univ).to_real
  begin
    assume f,
    rw mul_comm,
    apply norm_integral_le_of_norm_le_const,
    apply filter.eventually_of_forall,
    assume x,
    exact bounded_continuous_function.norm_coe_le_norm f x,
  end

/-- Given a measure, there exists a continuous linear form on the space of all bounded functions
(not necessarily measurable) that coincides with the integral on bounded measurable functions. -/
lemma exists_linear_extension_to_bounded_functions
  [measurable_space α] (μ : measure α) [is_finite_measure μ] :
  ∃ φ : (discrete_copy α →ᵇ ℝ) →L[ℝ] ℝ, ∀ (f : discrete_copy α →ᵇ ℝ),
    integrable f μ → φ f = ∫ x, f x ∂μ :=
begin
  rcases exists_extension_norm_eq _ (bounded_integrable_functions_integral_clm μ) with ⟨φ, hφ⟩,
  exact ⟨φ, λ f hf, hφ.1 ⟨f, hf⟩⟩,
end

/-- An arbitrary extension of the integral to all bounded functions, as a continuous linear map.
It is not at all canonical, and constructed using Hahn-Banach. -/
def _root_.measure_theory.measure.extension_to_bounded_functions
  [measurable_space α] (μ : measure α) [is_finite_measure μ] : (discrete_copy α →ᵇ ℝ) →L[ℝ] ℝ :=
(exists_linear_extension_to_bounded_functions μ).some

lemma extension_to_bounded_functions_apply [measurable_space α] (μ : measure α)
  [is_finite_measure μ] (f : discrete_copy α →ᵇ ℝ) (hf : integrable f μ) :
  μ.extension_to_bounded_functions f = ∫ x, f x ∂μ :=
(exists_linear_extension_to_bounded_functions μ).some_spec f hf

/-!
### Additive measures on the space of all sets

We define bounded finitely additive signed measures on the space of all subsets of a type `α`,
and show that such an object can be split into a discrete part and a continuous part.
-/

/-- A bounded signed finitely additive measure defined on *all* subsets of a type. -/
structure bounded_additive_measure (α : Type u) :=
(to_fun : set α → ℝ)
(additive' : ∀ s t, disjoint s t → to_fun (s ∪ t) = to_fun s + to_fun t)
(exists_bound : ∃ (C : ℝ), ∀ s, |to_fun s| ≤ C)

instance : inhabited (bounded_additive_measure α) :=
⟨{ to_fun := λ s, 0,
  additive' := λ s t hst, by simp,
  exists_bound := ⟨0, λ s, by simp⟩ }⟩

instance : has_coe_to_fun (bounded_additive_measure α) (λ _, set α → ℝ) := ⟨λ f, f.to_fun⟩

namespace bounded_additive_measure

/-- A constant bounding the mass of any set for `f`. -/
def C (f : bounded_additive_measure α) := f.exists_bound.some

lemma additive (f : bounded_additive_measure α) (s t : set α)
  (h : disjoint s t) : f (s ∪ t) = f s + f t :=
f.additive' s t h

lemma abs_le_bound (f : bounded_additive_measure α) (s : set α) :
  |f s| ≤ f.C :=
f.exists_bound.some_spec s

lemma le_bound (f : bounded_additive_measure α) (s : set α) :
  f s ≤ f.C :=
le_trans (le_abs_self _) (f.abs_le_bound s)

@[simp] lemma empty (f : bounded_additive_measure α) : f ∅ = 0 :=
begin
  have : (∅ : set α) = ∅ ∪ ∅, by simp only [empty_union],
  apply_fun f at this,
  rwa [f.additive _ _ (empty_disjoint _), self_eq_add_left] at this,
end

instance : has_neg (bounded_additive_measure α) :=
⟨λ f,
{ to_fun := λ s, - f s,
  additive' := λ s t hst, by simp only [f.additive s t hst, add_comm, neg_add_rev],
  exists_bound := ⟨f.C, λ s, by simp [f.abs_le_bound]⟩ }⟩

@[simp] lemma neg_apply (f : bounded_additive_measure α) (s : set α) : (-f) s = - (f s) := rfl

/-- Restricting a bounded additive measure to a subset still gives a bounded additive measure. -/
def restrict (f : bounded_additive_measure α) (t : set α) : bounded_additive_measure α :=
{ to_fun := λ s, f (t ∩ s),
  additive' := λ s s' h, begin
    rw [← f.additive (t ∩ s) (t ∩ s'), inter_union_distrib_left],
    exact h.mono (inter_subset_right _ _) (inter_subset_right _ _),
  end,
  exists_bound := ⟨f.C, λ s, f.abs_le_bound _⟩ }

@[simp] lemma restrict_apply (f : bounded_additive_measure α) (s t : set α) :
  f.restrict s t = f (s ∩ t) := rfl

/-- There is a maximal countable set of positive measure, in the sense that any countable set
not intersecting it has nonpositive measure. Auxiliary lemma to prove `exists_discrete_support`. -/
lemma exists_discrete_support_nonpos (f : bounded_additive_measure α) :
  ∃ (s : set α), countable s ∧ (∀ t, countable t → f (t \ s) ≤ 0) :=
begin
  /- The idea of the proof is to construct the desired set inductively, adding at each step a
  countable set with close to maximal measure among those points that have not already been chosen.
  Doing this countably many steps will be enough. Indeed, otherwise, a remaining set would have
  positive measure `ε`. This means that at each step the set we have added also had a large measure,
  say at least `ε / 2`. After `n` steps, the set we have constructed has therefore measure at least
  `n * ε / 2`. This is a contradiction since the measures have to remain uniformly bounded.

  We argue from the start by contradiction, as this means that our inductive construction will
  never be stuck, so we won't have to consider this case separately.
  -/
  by_contra h,
  push_neg at h,
  -- We will formulate things in terms of the type of countable subsets of `α`, as this is more
  -- convenient to formalize the inductive construction.
  let A : set (set α) := {t | countable t},
  let empty : A := ⟨∅, countable_empty⟩,
  haveI : nonempty A := ⟨empty⟩,
  -- given a countable set `s`, one can find a set `t` in its complement with measure close to
  -- maximal.
  have : ∀ (s : A), ∃ (t : A), (∀ (u : A), f (u \ s) ≤ 2 * f (t \ s)),
  { assume s,
    have B : bdd_above (range (λ (u : A), f (u \ s))),
      { refine ⟨f.C, λ x hx, _⟩,
        rcases hx with ⟨u, hu⟩,
        rw ← hu,
        exact f.le_bound _ },
    let S := supr (λ (t : A), f (t \ s)),
    have S_pos : 0 < S,
    { rcases h s.1 s.2  with ⟨t, t_count, ht⟩,
      apply ht.trans_le,
      let t' : A := ⟨t, t_count⟩,
      change f (t' \ s) ≤ S,
      exact le_csupr B t' },
    rcases exists_lt_of_lt_csupr (half_lt_self S_pos) with ⟨t, ht⟩,
    refine ⟨t, λ u, _⟩,
    calc f (u \ s) ≤ S : le_csupr B _
      ... = 2 * (S / 2) : by ring
      ... ≤ 2 * f (t \ s) : mul_le_mul_of_nonneg_left ht.le (by norm_num) },
  choose! F hF using this,
  -- iterate the above construction, by adding at each step a set with measure close to maximal in
  -- the complement of already chosen points. This is the set `s n` at step `n`.
  let G : A → A := λ u, ⟨u ∪ F u, u.2.union (F u).2⟩,
  let s : ℕ → A := λ n, G^[n] empty,
  -- We will get a contradiction from the fact that there is a countable set `u` with positive
  -- measure in the complement of `⋃ n, s n`.
  rcases h (⋃ n, s n) (countable_Union (λ n, (s n).2)) with ⟨t, t_count, ht⟩,
  let u : A := ⟨t \ ⋃ n, s n, t_count.mono (diff_subset _ _)⟩,
  set ε := f u with hε,
  have ε_pos : 0 < ε := ht,
  have I1 : ∀ n, ε / 2 ≤ f (s (n+1) \ s n),
  { assume n,
    rw [div_le_iff' (show (0 : ℝ) < 2, by norm_num), hε],
    convert hF (s n) u using 3,
    { dsimp [u],
      ext x,
      simp only [not_exists, mem_Union, mem_diff],
      tauto },
    { simp only [s, function.iterate_succ', subtype.coe_mk, union_diff_left] } },
  have I2 : ∀ (n : ℕ), (n : ℝ) * (ε / 2) ≤ f (s n),
  { assume n,
    induction n with n IH,
    { simp only [s, bounded_additive_measure.empty, id.def, nat.cast_zero, zero_mul,
        function.iterate_zero, subtype.coe_mk], },
    { have : (s (n+1) : set α) = (s (n+1) \ s n) ∪ s n,
        by simp only [s, function.iterate_succ', union_comm, union_diff_self, subtype.coe_mk,
          union_diff_left],
      rw [nat.succ_eq_add_one, this, f.additive],
      swap, { rw disjoint.comm, apply disjoint_diff },
      calc ((n + 1) : ℝ) * (ε / 2) = ε / 2 + n * (ε / 2) : by ring
      ... ≤ f ((s (n + 1)) \ (s n)) + f (s n) : add_le_add (I1 n) IH } },
  rcases exists_nat_gt (f.C / (ε / 2)) with ⟨n, hn⟩,
  have : (n : ℝ) ≤ f.C / (ε / 2),
    by { rw le_div_iff (half_pos ε_pos), exact (I2 n).trans (f.le_bound _) },
  exact lt_irrefl _ (this.trans_lt hn),
end

lemma exists_discrete_support (f : bounded_additive_measure α) :
  ∃ (s : set α), countable s ∧ (∀ t, countable t → f (t \ s) = 0) :=
begin
  rcases f.exists_discrete_support_nonpos with ⟨s₁, s₁_count, h₁⟩,
  rcases (-f).exists_discrete_support_nonpos with ⟨s₂, s₂_count, h₂⟩,
  refine ⟨s₁ ∪ s₂, s₁_count.union s₂_count, λ t ht, le_antisymm _ _⟩,
  { have : t \ (s₁ ∪ s₂) = (t \ (s₁ ∪ s₂)) \ s₁,
      by rw [diff_diff, union_comm, union_assoc, union_self],
    rw this,
    exact h₁ _ (ht.mono (diff_subset _ _)) },
  { have : t \ (s₁ ∪ s₂) = (t \ (s₁ ∪ s₂)) \ s₂,
      by rw [diff_diff, union_assoc, union_self],
    rw this,
    simp only [neg_nonpos, neg_apply] at h₂,
    exact h₂ _ (ht.mono (diff_subset _ _)) },
end

/-- A countable set outside of which the measure gives zero mass to countable sets. We are not
claiming this set is unique, but we make an arbitrary choice of such a set. -/
def discrete_support (f : bounded_additive_measure α) : set α :=
(exists_discrete_support f).some

lemma countable_discrete_support (f : bounded_additive_measure α) :
  countable f.discrete_support :=
(exists_discrete_support f).some_spec.1

lemma apply_countable (f : bounded_additive_measure α) (t : set α) (ht : countable t) :
  f (t \ f.discrete_support) = 0 :=
(exists_discrete_support f).some_spec.2 t ht

/-- The discrete part of a bounded additive measure, obtained by restricting the measure to its
countable support. -/
def discrete_part (f : bounded_additive_measure α) : bounded_additive_measure α :=
f.restrict f.discrete_support

/-- The continuous part of a bounded additive measure, giving zero measure to every countable
set. -/
def continuous_part (f : bounded_additive_measure α) : bounded_additive_measure α :=
f.restrict (univ \ f.discrete_support)

lemma eq_add_parts (f : bounded_additive_measure α) (s : set α) :
  f s = f.discrete_part s + f.continuous_part s :=
begin
  simp only [discrete_part, continuous_part, restrict_apply],
  rw [← f.additive, ← inter_distrib_right],
  { simp only [union_univ, union_diff_self, univ_inter] },
  { have : disjoint f.discrete_support (univ \ f.discrete_support) := disjoint_diff,
    exact this.mono (inter_subset_left _ _) (inter_subset_left _ _) }
end

lemma discrete_part_apply (f : bounded_additive_measure α) (s : set α) :
  f.discrete_part s = f (f.discrete_support ∩ s) := rfl

lemma continuous_part_apply_eq_zero_of_countable (f : bounded_additive_measure α)
  (s : set α) (hs : countable s) : f.continuous_part s = 0 :=
begin
  simp [continuous_part],
  convert f.apply_countable s hs using 2,
  ext x,
  simp [and_comm]
end

lemma continuous_part_apply_diff (f : bounded_additive_measure α)
  (s t : set α) (hs : countable s) : f.continuous_part (t \ s) = f.continuous_part t :=
begin
  conv_rhs { rw ← diff_union_inter t s },
  rw [additive, self_eq_add_right],
  { exact continuous_part_apply_eq_zero_of_countable _ _ (hs.mono (inter_subset_right _ _)) },
  { exact disjoint.mono_right (inter_subset_right _ _) (disjoint.comm.1 disjoint_diff) },
end

end bounded_additive_measure

open bounded_additive_measure

section

/-!
### Relationship between continuous functionals and finitely additive measures.
-/

lemma norm_indicator_le_one (s : set α) (x : α) :
  ∥(indicator s (1 : α → ℝ)) x∥ ≤ 1 :=
by { simp only [indicator, pi.one_apply], split_ifs; norm_num }

/-- A functional in the dual space of bounded functions gives rise to a bounded additive measure,
by applying the functional to the indicator functions. -/
def _root_.continuous_linear_map.to_bounded_additive_measure
  [topological_space α] [discrete_topology α]
  (f : (α →ᵇ ℝ) →L[ℝ] ℝ) : bounded_additive_measure α :=
{ to_fun := λ s, f (of_normed_group_discrete (indicator s 1) 1 (norm_indicator_le_one s)),
  additive' := λ s t hst,
    begin
      have : of_normed_group_discrete (indicator (s ∪ t) 1) 1 (norm_indicator_le_one (s ∪ t))
              = of_normed_group_discrete (indicator s 1) 1 (norm_indicator_le_one s)
              + of_normed_group_discrete (indicator t 1) 1 (norm_indicator_le_one t),
        by { ext x, simp [indicator_union_of_disjoint hst], },
      rw [this, f.map_add],
    end,
  exists_bound := ⟨∥f∥, λ s, begin
    have I : ∥of_normed_group_discrete (indicator s 1) 1 (norm_indicator_le_one s)∥ ≤ 1,
      by apply norm_of_normed_group_le _ zero_le_one,
    apply le_trans (f.le_op_norm _),
    simpa using mul_le_mul_of_nonneg_left I (norm_nonneg f),
  end⟩ }

@[simp] lemma continuous_part_eval_clm_eq_zero [topological_space α] [discrete_topology α]
  (s : set α) (x : α) :
  (eval_clm ℝ x).to_bounded_additive_measure.continuous_part s = 0 :=
let f := (eval_clm ℝ x).to_bounded_additive_measure in calc
  f.continuous_part s
    = f.continuous_part (s \ {x}) : (continuous_part_apply_diff _ _ _ (countable_singleton x)).symm
... = f ((univ \ f.discrete_support) ∩ (s \ {x})) : rfl
... = indicator ((univ \ f.discrete_support) ∩ (s \ {x})) 1 x : rfl
... = 0 : by simp

lemma to_functions_to_measure [measurable_space α] (μ : measure α) [is_finite_measure μ]
  (s : set α) (hs : measurable_set s) :
  μ.extension_to_bounded_functions.to_bounded_additive_measure s = (μ s).to_real :=
begin
  change μ.extension_to_bounded_functions
    (of_normed_group_discrete (indicator s (λ x, 1)) 1 (norm_indicator_le_one s)) = (μ s).to_real,
  rw extension_to_bounded_functions_apply,
  { change ∫ x, s.indicator (λ y, (1 : ℝ)) x ∂μ = _,
    simp [integral_indicator hs] },
  { change integrable (indicator s 1) μ,
    have : integrable (λ x, (1 : ℝ)) μ := integrable_const (1 : ℝ),
    apply this.mono' (measurable.indicator (@measurable_const _ _ _ _ (1 : ℝ)) hs).ae_measurable,
    apply filter.eventually_of_forall,
    exact norm_indicator_le_one _ }
end

lemma to_functions_to_measure_continuous_part [measurable_space α] [measurable_singleton_class α]
  (μ : measure α) [is_finite_measure μ] [has_no_atoms μ]
  (s : set α) (hs : measurable_set s) :
  μ.extension_to_bounded_functions.to_bounded_additive_measure.continuous_part s = (μ s).to_real :=
begin
  let f := μ.extension_to_bounded_functions.to_bounded_additive_measure,
  change f ((univ \ f.discrete_support) ∩ s) = (μ s).to_real,
  rw to_functions_to_measure, swap,
  { exact measurable_set.inter
      (measurable_set.univ.diff (countable.measurable_set f.countable_discrete_support)) hs },
  congr' 1,
  rw [inter_comm, ← inter_diff_assoc, inter_univ],
  exact measure_diff_null (f.countable_discrete_support.measure_zero _)
end

end

/-!
### A set in `ℝ²` large along verticals, small along horizontals

We construct a subset of `ℝ²`, given as a family of sets, which is large along verticals (i.e.,
it only misses a countable set along each vertical) but small along horizontals (it is countable
along horizontals). Such a set can not be measurable as it would contradict Fubini theorem.
We need the continuum hypothesis to construct it.
-/

theorem sierpinski_pathological_family (Hcont : #ℝ = aleph 1) :
  ∃ (f : ℝ → set ℝ), (∀ x, countable (univ \ f x)) ∧ (∀ y, countable {x | y ∈ f x}) :=
begin
  rcases cardinal.ord_eq ℝ with ⟨r, hr, H⟩,
  resetI,
  refine ⟨λ x, {y | r x y}, λ x, _, λ y, _⟩,
  { have : univ \ {y | r x y} = {y | r y x} ∪ {x},
    { ext y,
      simp only [true_and, mem_univ, mem_set_of_eq, mem_insert_iff, union_singleton, mem_diff],
      rcases trichotomous_of r x y with h|rfl|h,
      { simp only [h, not_or_distrib, false_iff, not_true],
        split,
        { rintros rfl, exact irrefl_of r y h },
        { exact asymm h } },
      { simp only [true_or, eq_self_iff_true, iff_true], exact irrefl x },
      { simp only [h, iff_true, or_true], exact asymm h } },
    rw this,
    apply countable.union _ (countable_singleton _),
    rw [cardinal.countable_iff_lt_aleph_one, ← Hcont],
    exact cardinal.card_typein_lt r x H },
  { rw [cardinal.countable_iff_lt_aleph_one, ← Hcont],
    exact cardinal.card_typein_lt r y H }
end

/-- A family of sets in `ℝ` which only miss countably many points, but such that any point is
contained in only countably many of them. -/
def spf (Hcont : #ℝ = aleph 1) (x : ℝ) : set ℝ :=
(sierpinski_pathological_family Hcont).some x

lemma countable_compl_spf (Hcont : #ℝ = aleph 1) (x : ℝ) : countable (univ \ spf Hcont x) :=
(sierpinski_pathological_family Hcont).some_spec.1 x

lemma countable_spf_mem (Hcont : #ℝ = aleph 1) (y : ℝ) : countable {x | y ∈ spf Hcont x} :=
(sierpinski_pathological_family Hcont).some_spec.2 y

/-!
### A counterexample for the Pettis integral

We construct a function `f` from `[0,1]` to a complete Banach space `B`, which is weakly measurable
(i.e., for any continuous linear form `φ` on `B` the function `φ ∘ f` is measurable), bounded in
norm (i.e., for all `x`, one has `∥f x∥ ≤ 1`), and still `f` has no Pettis integral.

This construction, due to Phillips, requires the continuum hypothesis. We will take for `B` the
space of all bounded functions on `ℝ`, with the supremum norm (no measure here, we are really
talking of everywhere defined functions). And `f x` will be the characteristic function of a set
which is large (it has countable complement), as in the Sierpinski pathological family.
-/

/-- A family of bounded functions `f_x` from `ℝ` (seen with the discrete topology) to `ℝ` (in fact
taking values in `{0, 1}`), indexed by a real parameter `x`, corresponding to the characteristic
functions of the different fibers of the Sierpinski pathological family -/
def f (Hcont : #ℝ = aleph 1) (x : ℝ) : (discrete_copy ℝ →ᵇ ℝ) :=
of_normed_group_discrete (indicator (spf Hcont x) 1) 1 (norm_indicator_le_one _)

lemma apply_f_eq_continuous_part (Hcont : #ℝ = aleph 1)
  (φ : (discrete_copy ℝ →ᵇ ℝ) →L[ℝ] ℝ) (x : ℝ)
  (hx : φ.to_bounded_additive_measure.discrete_support ∩ spf Hcont x = ∅) :
  φ (f Hcont x) = φ.to_bounded_additive_measure.continuous_part univ :=
begin
  set ψ := φ.to_bounded_additive_measure with hψ,
  have : φ (f Hcont x) = ψ (spf Hcont x) := rfl,
  have U : univ = spf Hcont x ∪ (univ \ spf Hcont x), by simp only [union_univ, union_diff_self],
  rw [this, eq_add_parts, discrete_part_apply, hx, ψ.empty, zero_add, U,
    ψ.continuous_part.additive _ _ (disjoint_diff),
    ψ.continuous_part_apply_eq_zero_of_countable _ (countable_compl_spf Hcont x), add_zero],
end

lemma countable_ne (Hcont : #ℝ = aleph 1) (φ : (discrete_copy ℝ →ᵇ ℝ) →L[ℝ] ℝ) :
  countable {x | φ.to_bounded_additive_measure.continuous_part univ ≠ φ (f Hcont x)} :=
begin
  have A : {x | φ.to_bounded_additive_measure.continuous_part univ ≠ φ (f Hcont x)}
    ⊆ {x | φ.to_bounded_additive_measure.discrete_support ∩ spf Hcont x ≠ ∅},
  { assume x hx,
    contrapose! hx,
    simp only [not_not, mem_set_of_eq] at hx,
    simp [apply_f_eq_continuous_part Hcont φ x hx], },
  have B : {x | φ.to_bounded_additive_measure.discrete_support ∩ spf Hcont x ≠ ∅}
    ⊆ ⋃ y ∈ φ.to_bounded_additive_measure.discrete_support, {x | y ∈ spf Hcont x},
  { assume x hx,
    dsimp at hx,
    rw [← ne.def, ne_empty_iff_nonempty] at hx,
    simp only [exists_prop, mem_Union, mem_set_of_eq],
    exact hx },
  apply countable.mono (subset.trans A B),
  exact countable.bUnion (countable_discrete_support _) (λ a ha, countable_spf_mem Hcont a),
end

lemma comp_ae_eq_const (Hcont : #ℝ = aleph 1) (φ : (discrete_copy ℝ →ᵇ ℝ) →L[ℝ] ℝ) :
  ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)),
    φ.to_bounded_additive_measure.continuous_part univ = φ (f Hcont x) :=
begin
  apply ae_restrict_of_ae,
  refine measure_mono_null _ ((countable_ne Hcont φ).measure_zero _),
  assume x,
  simp only [imp_self, mem_set_of_eq, mem_compl_eq],
end

lemma integrable_comp (Hcont : #ℝ = aleph 1) (φ : (discrete_copy ℝ →ᵇ ℝ) →L[ℝ] ℝ) :
  integrable_on (λ x, φ (f Hcont x)) (Icc 0 1) :=
begin
  have : integrable_on (λ x, φ.to_bounded_additive_measure.continuous_part univ) (Icc (0 : ℝ) 1)
    volume, by simp [integrable_on_const],
  apply integrable.congr this (comp_ae_eq_const Hcont φ),
end

lemma integral_comp (Hcont : #ℝ = aleph 1) (φ : (discrete_copy ℝ →ᵇ ℝ) →L[ℝ] ℝ) :
  ∫ x in Icc 0 1, φ (f Hcont x) = φ.to_bounded_additive_measure.continuous_part univ :=
begin
  rw ← integral_congr_ae (comp_ae_eq_const Hcont φ),
  simp,
end

/-!
The next few statements show that the function `f Hcont : ℝ → (discrete_copy ℝ →ᵇ ℝ)` takes its
values in a complete space, is scalarly measurable, is everywhere bounded by `1`, and still has
no Pettis integral.
-/

example : complete_space (discrete_copy ℝ →ᵇ ℝ) := by apply_instance

/-- The function `f Hcont : ℝ → (discrete_copy ℝ →ᵇ ℝ)` is scalarly measurable. -/
lemma measurable_comp (Hcont : #ℝ = aleph 1) (φ : (discrete_copy ℝ →ᵇ ℝ) →L[ℝ] ℝ) :
  measurable (λ x, φ (f Hcont x)) :=
begin
  have : measurable (λ x, φ.to_bounded_additive_measure.continuous_part univ) := measurable_const,
  refine this.measurable_of_countable_ne _,
  exact countable_ne Hcont φ,
end

/-- The function `f Hcont : ℝ → (discrete_copy ℝ →ᵇ ℝ)` is uniformly bounded by `1` in norm. -/
lemma norm_bound (Hcont : #ℝ = aleph 1) (x : ℝ) : ∥f Hcont x∥ ≤ 1 :=
norm_of_normed_group_le _ zero_le_one _

/-- The function `f Hcont : ℝ → (discrete_copy ℝ →ᵇ ℝ)` has no Pettis integral. -/
theorem no_pettis_integral (Hcont : #ℝ = aleph 1) :
  ¬ ∃ (g : discrete_copy ℝ →ᵇ ℝ),
      ∀ (φ : (discrete_copy ℝ →ᵇ ℝ) →L[ℝ] ℝ), ∫ x in Icc 0 1, φ (f Hcont x) = φ g :=
begin
  rintros ⟨g, h⟩,
  simp only [integral_comp] at h,
  have : g = 0,
  { ext x,
    have : g x = eval_clm ℝ x g := rfl,
    rw [this, ← h],
    simp },
  simp only [this, continuous_linear_map.map_zero] at h,
  specialize h (volume.restrict (Icc (0 : ℝ) 1)).extension_to_bounded_functions,
  simp_rw [to_functions_to_measure_continuous_part _ _ measurable_set.univ] at h,
  simpa using h,
end

end phillips_1940

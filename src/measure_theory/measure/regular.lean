/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris Van Doorn
-/

import measure_theory.constructions.borel_space

/-!
# Regular measures

A measure is `regular` if it satisfies the following properties:
* it is finite on compact sets;
* it is outer regular for measurable sets with respect to open sets: the measure of any measurable
  set `A` is the infimum of `μ U` over all open sets `U` containing `A`;
* it is inner regular for open sets with respect to compacts sets: the measure of any open set `U`
  is the supremum of `μ K` over all compact sets `K` contained in `U`.

A measure is `weakly_regular` if it satisfies the following properties:
* it is outer regular for measurable sets with respect to open sets: the measure of any measurable
  set `A` is the infimum of `μ U` over all open sets `U` containing `A`;
* it is inner regular for open sets with respect to closed sets: the measure of any open set `U`
  is the supremum of `μ F` over all compact sets `F` contained in `U`.

Regularity implies weak regularity. Both these conditions are registered as typeclasses for a
measure `μ`, and this implication is recorded as an instance.

These conditions imply inner regularity for all measurable sets of finite measure (with respect to
compact sets or closed sets respectively), but in general not for all sets. For a counterexample,
consider the group `ℝ × ℝ` where the first factor has the discrete topology and the second one the
usual topology. It is a locally compact Hausdorff topological group, with Haar measure equal to
Lebesgue measure on each vertical fiber. The set `ℝ × {0}` has infinite measure (by outer
regularity), but any compact set it contains has zero measure (as it is finite).

Several authors require as a definition of regularity that all measurable sets are inner regular.
We have opted for the slightly weaker definition above as it holds for all Haar measures, it is
enough for essentially all applications, and it is equivalent to the other definition when the
measure is finite.

The interest of the notion of weak regularity is that it is enough for many applications, and it
is automatically satisfied by any finite measure on a metric space.

## Main definitions and results

* `regular μ`: a typeclass registering that a measure `μ` on a topological space is regular.
* `measurable_set.measure_eq_infi_is_open'` asserts that, when `μ` is regular, the measure of a
  measurable set is the infimum of the measure of open sets containing it. The unprimed version
  is reserved for weakly regular measures, as it should apply most of the time. Such open sets
  with suitable measures can be constructed with `measurable_set.exists_is_open_lt_of_lt'`.
* `is_open.measure_eq_supr_is_compact` asserts that the measure of an open set is the supremum of
  the measure of compact sets it contains. Such a compact set with suitable measure can be
  constructed with `is_open.exists_lt_is_compact`.
* `measurable_set.measure_eq_supr_is_compact_of_lt_top` asserts that the measure of a measurable set
  of finite measure is the supremum of the measure of compact sets it contains. Such a compact set
  with suitable measure can be constructed with `measurable_set.exists_lt_is_compact_of_lt_top` or
  `measurable_set.exists_lt_is_compact_of_lt_top_of_pos`.
* `regular.of_sigma_compact_space_of_is_locally_finite_measure` is an instance registering that a
  locally finite measure on a locally compact metric space is regular (in fact, an emetric space
  is enough).

* `weakly_regular μ`: a typeclass registering that a measure `μ` on a topological space is
  weakly regular.
* `measurable_set.measure_eq_infi_is_open`, `measurable_set.exists_is_open_lt_of_lt`,
  `is_open.measure_eq_supr_is_closed`, `is_open.exists_lt_is_closed`,
  `measurable_set.measure_eq_supr_is_closed_of_lt_top`,
  `measurable_set.exists_lt_is_closed_of_lt_top` and
  `measurable_set.exists_lt_is_closed_of_lt_top_of_pos`
  state the corresponding properties for weakly regular measures.
* `weakly_regular.of_pseudo_emetric_space_of_is_finite_measure` is an instance registering that a
  finite measure on a metric space is weakly regular (in fact, a pseudo emetric space is enough).

## Implementation notes

The main nontrivial statement is `weakly_regular.exists_closed_subset_self_subset_open`, expressing
that in a finite measure space, if every open set can be approximated from inside by closed sets,
then any measurable set can be approximated from inside by closed sets and from outside by open
sets. This statement is proved by measurable induction, starting from open sets and checking that
it is stable by taking complements (this is the point of this condition, being symmetrical between
inside and outside) and countable disjoint unions.

Once this statement is proved, one deduces results for general measures from this statement, by
restricting them to finite measure sets (and proving that this restriction is weakly regular,
using again the same statement).

## References

[Halmos, Measure Theory, §52][halmos1950measure]. Note that Halmos uses an unusual definition of
Borel sets (for him, they are elements of the `σ`-algebra generated by compact sets!), so his
proofs or statements do not apply directly.

[Billingsley, Convergence of Probability Measures][billingsley1999]
-/

open set filter
open_locale ennreal topological_space nnreal big_operators

namespace measure_theory
namespace measure

variables {α β : Type*} [measurable_space α] [topological_space α] {μ : measure α}

/-- A measure `μ` is outer regular if `μ(A) = inf {μ(U) | A ⊆ U open}` for a measurable set `A`. -/
@[protect_proj] class outer_regular (μ : measure α) : Prop :=
(outer_regular : ∀ ⦃A : set α⦄, measurable_set A →
  (⨅ (U : set α) (h : is_open U) (h2 : A ⊆ U), μ U) ≤ μ A)

/-- A measure `μ` is regular if
  - it is finite on all compact sets;
  - it is outer regular: `μ(A) = inf {μ(U) | A ⊆ U open}` for `A` measurable;
  - it is inner regular for open sets, using compact sets:
    `μ(U) = sup {μ(K) | K ⊆ U compact}` for `U` open. -/
class regular (μ : measure α) extends outer_regular μ : Prop :=
(lt_top_of_is_compact : ∀ ⦃K : set α⦄, is_compact K → μ K < ∞)
(inner_regular : ∀ ⦃U : set α⦄, is_open U →
  μ U ≤ ⨆ (K : set α) (h : is_compact K) (h2 : K ⊆ U), μ K)

/-- A measure `μ` is weakly regular if
  - it is outer regular: `μ(A) = inf { μ(U) | A ⊆ U open }` for `A` measurable;
  - it is inner regular for open sets, using closed sets:
    `μ(U) = sup {μ(F) | F ⊆ U compact}` for `U` open. -/
class weakly_regular (μ : measure α) extends outer_regular μ : Prop :=
(inner_regular : ∀ ⦃U : set α⦄, is_open U →
  μ U ≤ ⨆ (F : set α) (h : is_closed F) (h2 : F ⊆ U), μ F)

/-- A regular measure is weakly regular. -/
@[priority 100] -- see Note [lower instance priority]
instance regular.weakly_regular [t2_space α] [regular μ] : weakly_regular μ :=
{ inner_regular := λ U hU, calc
    μ U ≤ ⨆ (K : set α) (h : is_compact K) (h2 : K ⊆ U), μ K : regular.inner_regular hU
    ... ≤ ⨆ (F : set α) (h : is_closed F) (h2 : F ⊆ U), μ F :
      by { simp only [supr_and'], exact bsupr_le_bsupr' (λ i hi, ⟨hi.1.is_closed, hi.2⟩) } }

namespace outer_regular

instance zero : outer_regular (0 : measure α) :=
⟨λ A hA, binfi_le_of_le univ is_open_univ $ infi_le _ (subset_univ A)⟩

/-- For an outer regular measure, the measure of a set is the infimum of the measures of open sets
containing it. -/
lemma _root_.set.measure_eq_infi_is_open (A : set α) (μ : measure α) [outer_regular μ] :
  μ A = (⨅ (U : set α) (h : is_open U) (h2 : A ⊆ U), μ U) :=
begin
  refine le_antisymm (le_infi $ λ s, le_infi $ λ hs, le_infi $ λ h2s, μ.mono h2s) _,
  rw ← @measure_to_measurable _ _ μ A,
  refine le_trans _ (outer_regular.outer_regular (measurable_set_to_measurable μ A)),
  exact infi_le_infi (λ U, infi_le_infi $ λ hU, infi_le_infi2 $
    λ hAU, ⟨(subset_to_measurable _ _).trans hAU, le_rfl⟩)
end

/-- Given `r` larger than the measure of a set `A`, there exists an open superset of `A` with
measure less than `r`. -/
lemma _root_.set.exists_is_open_lt_of_lt [outer_regular μ] (A : set α) (r : ℝ≥0∞) (hr : μ A < r) :
  ∃ U, is_open U ∧ A ⊆ U ∧ μ U < r :=
begin
  rw A.measure_eq_infi_is_open μ at hr,
  simpa only [infi_lt_iff, exists_prop] using hr
end

/-- Given an outer regular measure, any finite measure set is contained in a finite measure open
set.-/
lemma exists_subset_is_open_measure_lt_top [outer_regular μ] {A : set α} (h'A : μ A ≠ ∞) :
  ∃ U, is_open U ∧ A ⊆ U ∧ μ U < ∞ :=
begin
  rcases A.exists_is_open_lt_of_lt _ (ennreal.lt_add_right h'A ennreal.zero_lt_one)
    with ⟨U, hUo, hBU, hμU⟩,
  exact ⟨U, hUo, hBU, hμU.trans_le le_top⟩
end

protected lemma map [opens_measurable_space α] [measurable_space β] [topological_space β]
  [t2_space β] [borel_space β] (f : α ≃ₜ β) (μ : measure α) [outer_regular μ] :
  (measure.map f μ).outer_regular :=
begin
  refine ⟨λ A hA, le_of_eq _⟩,
  simp only [map_apply f.measurable hA, (f ⁻¹' A).measure_eq_infi_is_open],
  refine infi_congr (preimage f) f.injective.preimage_surjective (λ U, _),
  refine infi_congr_Prop f.is_open_preimage (λ hU, _),
  refine infi_congr_Prop f.surjective.preimage_subset_preimage_iff (λ h2U, _),
  rw [map_apply f.measurable hU.measurable_set]
end

protected lemma smul (μ : measure α) [outer_regular μ] {x : ℝ≥0∞} (hx : x ≠ ∞) :
  (x • μ).outer_regular :=
begin
  rcases eq_or_ne x 0 with rfl|h0,
  { rw zero_smul, exact outer_regular.zero },
  { refine ⟨λ A hA, _⟩,
    simp only [smul_apply],
    refine eq.trans_le _ (ennreal.mul_left_mono $ outer_regular.outer_regular hA),
    simp only [ennreal.mul_infi_of_ne h0 hx] },
end

end outer_regular

namespace regular

instance zero : regular (0 : measure α) :=
⟨λ K hK, ennreal.coe_lt_top, λ U hU, zero_le _⟩

/-- The measure of an open set is the supremum of the measures of compact sets it contains. -/
lemma _root_.is_open.measure_eq_supr_is_compact ⦃U : set α⦄ (hU : is_open U)
  (μ : measure α) [regular μ] :
  μ U = (⨆ (K : set α) (h : is_compact K) (h2 : K ⊆ U), μ K) :=
le_antisymm (regular.inner_regular hU) (supr_le $ λ s, supr_le $ λ hs, supr_le $ λ h2s, μ.mono h2s)

lemma _root_.is_open.exists_lt_is_compact [regular μ] ⦃U : set α⦄ (hU : is_open U)
  {r : ℝ≥0∞} (hr : r < μ U) :
  ∃ K, is_compact K ∧ K ⊆ U ∧ r < μ K :=
begin
  rw hU.measure_eq_supr_is_compact at hr,
  simpa only [lt_supr_iff, exists_prop] using hr
end

lemma _root_.is_open.exists_is_compact_lt_add [regular μ] ⦃U : set α⦄ (hU : is_open U)
  (hμU : μ U ≠ ∞) {r : ℝ≥0∞} (hr : 0 < r) :
  ∃ K, is_compact K ∧ K ⊆ U ∧ μ U < μ K + r :=
begin
  cases eq_or_ne (μ U) 0 with h₀ h₀,
  { refine ⟨∅, is_compact_empty, empty_subset _, _⟩,
    rwa [measure_empty, h₀, zero_add] },
  { rcases hU.exists_lt_is_compact (ennreal.sub_lt_self hμU h₀ hr) with ⟨K, hKc, hKU, hrK⟩,
    exact ⟨K, hKc, hKU, ennreal.lt_add_of_sub_lt (or.inl hμU) hrK⟩ }
end

lemma exists_compact_not_null [regular μ] : (∃ K, is_compact K ∧ μ K ≠ 0) ↔ μ ≠ 0 :=
by simp_rw [ne.def, ← measure_univ_eq_zero, is_open_univ.measure_eq_supr_is_compact,
    ennreal.supr_eq_zero, not_forall, exists_prop, subset_univ, true_and]

/-- If `s` is a measurable set, a regular measure `μ` is finite on `s`, and `r` is a positive
number, then there exist a compact set `K ⊆ s` and an open set `U ⊇ s` such that `μ U < μ K + r`. -/
lemma _root_.measurable_set.exists_is_compact_is_open_lt_add [regular μ]
  [opens_measurable_space α] {s : set α} (hs : measurable_set s) (hμs : μ s ≠ ∞)
  {r : ℝ≥0∞} (hr : 0 < r) :
  ∃ K U, is_compact K ∧ is_open U ∧ K ⊆ s ∧ s ⊆ U ∧ μ U < μ K + r :=
begin
  rcases s.exists_is_open_lt_of_lt (μ s + r / 2) (ennreal.lt_add_right hμs (ennreal.half_pos hr))
    with ⟨U, hUo, hsU, hμU⟩,
  have : μ (U \ s) < r / 2,
  { rw [measure_diff hsU hUo.measurable_set hs hμs],
    refine ennreal.sub_lt_of_lt_add (measure_mono hsU) _, rwa add_comm },
  rcases (U \ s).exists_is_open_lt_of_lt _ this with ⟨U', hU'o, hsU', hμU'⟩,
  rw diff_subset_comm at hsU',
  rcases hUo.exists_is_compact_lt_add (ne_top_of_lt hμU) (ennreal.half_pos hr)
    with ⟨K, hKc, hKU, hKr⟩,
  refine ⟨K \ U', U, hKc.diff hU'o, hUo, λ x hx, hsU' ⟨hKU hx.1, hx.2⟩, hsU, _⟩,
  rw [← ennreal.add_halves r, ← add_assoc],
  refine hKr.trans_le (add_le_add_right _ _),
  calc μ K ≤ μ K - μ U' + μ U' : ennreal.le_sub_add_self
       ... ≤ _                 : add_le_add le_measure_diff hμU'.le,
end

lemma _root_.measurable_set.exists_lt_is_compact_of_ne_top_of_pos [opens_measurable_space α]
  [t2_space α] [regular μ]
  ⦃A : set α⦄ (hA : measurable_set A) (h'A : μ A ≠ ∞) {ε : ℝ≥0∞} (εpos : 0 < ε) :
  ∃ K, is_compact K ∧ K ⊆ A ∧ μ A < μ K + ε :=
begin
  rcases hA.exists_is_compact_is_open_lt_add h'A εpos with ⟨K, U, hK, hU, KA, AU, hμ⟩,
  exact ⟨K, hK, KA, (measure_mono AU).trans_lt hμ⟩
end

lemma _root_.measurable_set.exists_lt_is_compact_of_ne_top [t2_space α] [regular μ]
  [opens_measurable_space α] ⦃A : set α⦄ (hA : measurable_set A) (h'A : μ A ≠ ∞)
  {r : ℝ≥0∞} (hr : r < μ A) :
  ∃ K, is_compact K ∧ K ⊆ A ∧ r < μ K :=
begin
  rcases hA.exists_is_compact_is_open_lt_add h'A (ennreal.zero_lt_sub_iff_lt.2 hr)
    with ⟨K, U, hKc, hUo, hKA, hAU, hKU⟩,
  refine ⟨K, hKc, hKA, lt_of_add_lt_add_right (lt_of_le_of_lt _ hKU)⟩,
  rw ennreal.add_sub_cancel_of_le hr.le, exact measure_mono hAU
end

/-- Given a regular measure, any measurable set of finite mass can be approximated from
inside by compact sets. -/
lemma _root_.measurable_set.measure_eq_supr_is_compact_of_ne_top
  [opens_measurable_space α] [t2_space α] [regular μ]
  ⦃A : set α⦄ (hA : measurable_set A) (h'A : μ A ≠ ∞) :
  μ A = (⨆ (K : set α) (h : is_compact K) (h2 : K ⊆ A), μ K) :=
begin
  refine le_antisymm (le_of_forall_lt $ λ r hr, _) _,
  { simpa only [lt_supr_iff, exists_prop] using hA.exists_lt_is_compact_of_ne_top h'A hr },
  { simp only [supr_le_iff], exact λ K _ hKA, measure_mono hKA }
end

protected lemma map [opens_measurable_space α] [measurable_space β] [topological_space β]
  [t2_space β] [borel_space β] [regular μ] (f : α ≃ₜ β) :
  (measure.map f μ).regular :=
begin
  have hf := f.measurable,
  have h2f := f.to_equiv.injective.preimage_surjective,
  have h3f := f.to_equiv.surjective,
  haveI := outer_regular.map f μ,
  split,
  { intros K hK, rw [map_apply hf hK.measurable_set],
    apply regular.lt_top_of_is_compact,
    rwa f.compact_preimage },
  { intros U hU,
    rw [map_apply hf hU.measurable_set, (hU.preimage f.continuous).measure_eq_supr_is_compact],
    refine ge_of_eq _,
    apply supr_congr (preimage f) h2f,
    intro K,
    apply supr_congr_Prop f.compact_preimage,
    intro hK,
    apply supr_congr_Prop h3f.preimage_subset_preimage_iff,
    intro h2U,
    rw [map_apply hf hK.measurable_set] }
end

protected lemma smul [regular μ] {x : ℝ≥0∞} (hx : x ≠ ∞) :
  (x • μ).regular :=
begin
  haveI := outer_regular.smul μ hx,
  split,
  { exact λ K hK, ennreal.mul_lt_top (lt_top_iff_ne_top.2 hx) (regular.lt_top_of_is_compact hK) },
  { intros U hU, simp only [smul_apply],
    simpa only [ennreal.mul_supr] using (ennreal.mul_left_mono $ regular.inner_regular hU) }
end

/-- A regular measure in a σ-compact space is σ-finite. -/
@[priority 100] -- see Note [lower instance priority]
instance sigma_finite [opens_measurable_space α] [t2_space α] [sigma_compact_space α]
  [regular μ] : sigma_finite μ :=
⟨⟨{ set := compact_covering α,
  set_mem := λ n, (is_compact_compact_covering α n).measurable_set,
  finite := λ n, regular.lt_top_of_is_compact $ is_compact_compact_covering α n,
  spanning := Union_compact_covering α }⟩⟩

end regular

namespace weakly_regular

lemma _root_.is_open.measure_eq_supr_is_closed ⦃U : set α⦄ (hU : is_open U)
  (μ : measure α) [weakly_regular μ] :
  μ U = (⨆ (F : set α) (h : is_closed F) (h2 : F ⊆ U), μ F) :=
le_antisymm (weakly_regular.inner_regular hU)
  (supr_le $ λ s, supr_le $ λ hs, supr_le $ λ h2s, μ.mono h2s)

lemma _root_.is_open.exists_lt_is_closed_of_gt
  [weakly_regular μ] ⦃U : set α⦄ (hU : is_open U) (r : ℝ≥0∞) (hr : r < μ U) :
  ∃ F, is_closed F ∧ F ⊆ U ∧ r < μ F :=
begin
  rw hU.measure_eq_supr_is_closed at hr,
  simpa only [lt_supr_iff, exists_prop] using hr,
end

lemma _root_.is_open.exists_is_closed_lt_add [weakly_regular μ] [opens_measurable_space α]
  ⦃U : set α⦄ (hU : is_open U) (hμU : μ U ≠ ∞) {r : ℝ≥0∞} (hr : 0 < r) :
  ∃ K, is_closed K ∧ K ⊆ U ∧ μ U < μ K + r :=
begin
  cases eq_or_ne (μ U) 0 with h₀ h₀,
  { refine ⟨∅, is_closed_empty, empty_subset _, _⟩,
    rwa [measure_empty, h₀, zero_add] },
  { rcases hU.exists_lt_is_closed_of_gt _ (ennreal.sub_lt_self hμU h₀ hr) with ⟨K, hKc, hKU, hrK⟩,
    exact ⟨K, hKc, hKU, ennreal.lt_add_of_sub_lt (or.inl hμU) hrK⟩ }
end

/-- If `s` is a measurable set, a weakly regular measure `μ` is finite on `s`, and `r` is a positive
number, then there exist a closed set `K ⊆ s` and an open set `U ⊇ s` such that `μ U < μ K + r`. -/
lemma _root_.measurable_set.exists_is_closed_is_open_lt_add [weakly_regular μ]
  [opens_measurable_space α] {s : set α} (hs : measurable_set s) (hμs : μ s ≠ ∞)
  {r : ℝ≥0∞} (hr : 0 < r) :
  ∃ K U, is_closed K ∧ is_open U ∧ K ⊆ s ∧ s ⊆ U ∧ μ U < μ K + r :=
begin
  rcases s.exists_is_open_lt_of_lt (μ s + r / 2) (ennreal.lt_add_right hμs (ennreal.half_pos hr))
    with ⟨U, hUo, hsU, hμU⟩,
  have : μ (U \ s) < r / 2,
  { rw [measure_diff hsU hUo.measurable_set hs hμs],
    refine ennreal.sub_lt_of_lt_add (measure_mono hsU) _, rwa add_comm },
  rcases (U \ s).exists_is_open_lt_of_lt _ this with ⟨U', hU'o, hsU', hμU'⟩,
  rw diff_subset_comm at hsU',
  rcases hUo.exists_is_closed_lt_add (ne_top_of_lt hμU) (ennreal.half_pos hr)
    with ⟨K, hKc, hKU, hKr⟩,
  refine ⟨K \ U', U, hKc.inter hU'o.is_closed_compl, hUo, λ x hx, hsU' ⟨hKU hx.1, hx.2⟩, hsU, _⟩,
  rw [← ennreal.add_halves r, ← add_assoc],
  refine hKr.trans_le (add_le_add_right _ _),
  calc μ K ≤ μ K - μ U' + μ U' : ennreal.le_sub_add_self
       ... ≤ _                 : add_le_add le_measure_diff hμU'.le,
end

/-- Given a weakly regular measure, any measurable set of finite mass can be approximated from
inside by closed sets. -/
lemma _root_.measurable_set.exists_lt_is_closed_of_ne_top [weakly_regular μ]
  [opens_measurable_space α] ⦃A : set α⦄ (hA : measurable_set A) (h'A : μ A ≠ ∞)
  {r : ℝ≥0∞} (hr : r < μ A) :
  ∃ K, is_closed K ∧ K ⊆ A ∧ r < μ K :=
begin
  rcases hA.exists_is_closed_is_open_lt_add h'A (ennreal.zero_lt_sub_iff_lt.2 hr)
    with ⟨K, U, hKc, hUo, hKA, hAU, hKU⟩,
  refine ⟨K, hKc, hKA, lt_of_add_lt_add_right (lt_of_le_of_lt _ hKU)⟩,
  rw ennreal.add_sub_cancel_of_le hr.le, exact measure_mono hAU
end

/-- Given a weakly regular measure, any measurable set of finite mass can be approximated from
inside by closed sets. -/
lemma _root_.measurable_set.measure_eq_supr_is_closed_of_ne_top
  [opens_measurable_space α] [weakly_regular μ]
  ⦃A : set α⦄ (hA : measurable_set A) (h'A : μ A ≠ ∞) :
  μ A = (⨆ (K : set α) (h : is_closed K) (h2 : K ⊆ A), μ K) :=
begin
  refine le_antisymm (le_of_forall_lt $ λ r hr, _) _,
  { simpa only [lt_supr_iff, exists_prop] using hA.exists_lt_is_closed_of_ne_top h'A hr },
  { simp only [supr_le_iff], exact λ K _ hKA, measure_mono hKA }
end

/-- In a finite measure space, assume that any open set can be approximated from inside by closed
sets. Then any measurable set can be approximated from inside by closed sets, and from outside
by open sets. -/
lemma exists_closed_subset_self_subset_open_of_pos [borel_space α]
  (μ : measure α) [is_finite_measure μ]
  (h0 : ∀ (U : set α), is_open U → μ U ≤ ⨆ (F : set α) (hF : is_closed F) (FU : F ⊆ U), μ F) :
  ∀ ⦃s : set α⦄ (hs : measurable_set s),
  ∀ ε > 0, (∃ (U : set α), is_open U ∧ s ⊆ U ∧ μ U ≤ μ s + ε)
    ∧ (∃ (F : set α), is_closed F ∧ F ⊆ s ∧ μ s ≤ μ F + ε) :=
begin
  refine measurable_space.induction_on_inter borel_space.measurable_eq is_pi_system_is_open _ _ _ _,
  /- The proof is by measurable induction: we should check that the property is true for the empty
  set, for open sets, and is stable by taking the complement and by taking countable disjoint
  unions. The point of the property we are proving is that it is stable by taking complements
  (exchanging the roles of closed and open sets and thanks to the finiteness of the measure). -/
  -- check for empty set
  { assume ε hε,
    exact ⟨⟨∅, is_open_empty, subset.refl _, by simp only [measure_empty, zero_le]⟩,
            ⟨∅, is_closed_empty, subset.refl _, by simp only [measure_empty, zero_le]⟩⟩ },
  -- check for open sets. This is essentially our assumption `h0`.
  { assume U hU ε hε,
    refine ⟨⟨U, hU, subset.refl _, le_self_add⟩, _⟩,
    have : μ U + ε ≤ ⨆ (F : set α) (hF : is_closed F) (FU : F ⊆ U), (μ F + ε),
    { haveI : nonempty {i // is_closed i ∧ i ⊆ U} := ⟨⟨∅, is_closed_empty, empty_subset _⟩⟩,
      simp_rw [supr_and', supr_subtype', ← ennreal.supr_add],
      refine add_le_add _ (le_refl _),
      convert h0 U hU using 1,
      simp_rw [supr_and', supr_subtype'], },
    have : μ U < (⨆ (F : set α) (hF : is_closed F) (FU : F ⊆ U), (μ F + ε)),
    { apply lt_of_lt_of_le _ this,
      simpa using (ennreal.add_lt_add_iff_left (measure_ne_top μ U)).2 hε },
    simp only [lt_supr_iff] at this,
    rcases this with ⟨F, F_closed, FU, μF⟩,
    exact ⟨F, F_closed, FU, μF.le⟩ },
  -- check for complements
  { assume s hs h ε εpos,
    rcases h ε εpos with ⟨⟨U, U_open, U_subset, nu_U⟩, ⟨F, F_closed, F_subset, nu_F⟩⟩,
    refine ⟨⟨Fᶜ, is_open_compl_iff.2 F_closed, compl_subset_compl.2 F_subset, _⟩,
            ⟨Uᶜ, is_closed_compl_iff.2 U_open, compl_subset_compl.2 U_subset, _⟩⟩,
    { apply ennreal.le_of_add_le_add_left (measure_ne_top μ F),
      calc
        μ F + μ Fᶜ = μ s + μ sᶜ :
          by rw [measure_add_measure_compl hs, measure_add_measure_compl F_closed.measurable_set]
        ... ≤ (μ F + ε) + μ sᶜ : add_le_add_right nu_F _
        ... = μ F + (μ sᶜ + ε) : by ac_refl },
    { apply ennreal.le_of_add_le_add_left (measure_ne_top μ s),
      calc
        μ s + μ sᶜ = μ U + μ Uᶜ :
          by rw [measure_add_measure_compl hs, measure_add_measure_compl U_open.measurable_set]
        ... ≤ (μ s + ε) + μ Uᶜ : add_le_add nu_U (le_refl _)
        ... = μ s + (μ Uᶜ + ε) : by abel } },
  -- check for disjoint unions
  { assume s s_disj s_meas hs ε εpos,
    split,
    -- the approximating open set is constructed by taking for each `s n` an approximating open set
    -- `U n` with measure at most `μ (s n) + δ n` for a summable `δ`, and taking the union of these.
    { rcases ennreal.exists_pos_sum_of_encodable' εpos.lt.ne' ℕ with ⟨δ, δpos, hδ⟩,
      have : ∀ n, ∃ (U : set α), is_open U ∧ s n ⊆ U ∧ μ U ≤ μ (s n) + δ n :=
        λ n, (hs n _ (δpos n).gt).1,
      choose U hU using this,
      refine ⟨(⋃ n, U n), is_open_Union (λ n, (hU n).1), Union_subset_Union (λ n, (hU n).2.1), _⟩,
      calc
      μ (⋃ (n : ℕ), U n)
          ≤ ∑' n, μ (U n) : measure_Union_le _
      ... ≤ ∑' n, (μ (s n) + δ n) : ennreal.tsum_le_tsum (λ n, (hU n).2.2)
      ... ≤ μ (⋃ (i : ℕ), s i) + ε :
      begin
        rw [ennreal.tsum_add],
        refine add_le_add (le_of_eq _) hδ.le,
        exact (measure_Union s_disj s_meas).symm,
      end },
    -- the approximating closed set is constructed by considering finitely many sets `s i`, which
    -- cover all the measure up to `ε/2`, approximating each of these by a closed set `F i`, and
    -- taking the union of these (finitely many) `F i`.
    { set δ := ε / 2 with hδ,
      have δpos : 0 < δ := ennreal.half_pos εpos.lt.ne',
      have L : tendsto (λ n, ∑ i in finset.range n, μ (s i) + δ) at_top (𝓝 (μ (⋃ i, s i) + δ)),
      { rw measure_Union s_disj s_meas,
        refine tendsto.add (ennreal.tendsto_nat_tsum _) tendsto_const_nhds },
      have nu_lt : μ (⋃ i, s i) < μ (⋃ i, s i) + δ,
        by simpa only [add_zero] using (ennreal.add_lt_add_iff_left (measure_ne_top μ _)).mpr δpos,
      obtain ⟨n, hn, npos⟩ :
        ∃ n, (μ (⋃ (i : ℕ), s i) < ∑ (i : ℕ) in finset.range n, μ (s i) + δ) ∧ (0 < n) :=
      (((tendsto_order.1 L).1 _ nu_lt).and (eventually_gt_at_top 0)).exists,
      have : ∀ i, ∃ (F : set α), is_closed F ∧ F ⊆ s i ∧ μ (s i) ≤ μ F + δ / n :=
        λ i, (hs i _ (ennreal.div_pos_iff.2 ⟨ne_of_gt δpos, ennreal.nat_ne_top n⟩)).2,
      choose F hF using this,
      have F_disj: pairwise (disjoint on F) :=
        s_disj.mono (λ i j hij, disjoint.mono (hF i).2.1 (hF j).2.1 hij),
      refine ⟨⋃ i ∈ finset.range n, F i, _, _, _⟩,
      { exact is_closed_bUnion (by simpa using finite_lt_nat n) (λ i hi, (hF i).1) },
      { assume x hx,
        simp only [exists_prop, mem_Union, finset.mem_range] at hx,
        rcases hx with ⟨i, i_lt, hi⟩,
        simp only [mem_Union],
        exact ⟨i, (hF i).2.1 hi⟩ },
      { calc
        μ (⋃ (i : ℕ), s i)
            ≤ ∑ (i : ℕ) in finset.range n, μ (s i) + δ : hn.le
        ... ≤ (∑ (i : ℕ) in finset.range n, (μ (F i) + δ / n)) + δ :
          add_le_add (finset.sum_le_sum (λ i hi, (hF i).2.2)) (le_refl _)
        ... = μ (⋃ i ∈ finset.range n, F i) + ε :
        begin
          simp only [finset.sum_add_distrib, finset.sum_const, nsmul_eq_mul, finset.card_range],
          rw [ennreal.mul_div_cancel' _ (ennreal.nat_ne_top n),
              measure_bUnion_finset (F_disj.pairwise_on _) (λ i hi, (hF i).1.measurable_set),
              hδ, add_assoc, ennreal.add_halves],
          simpa only [ne.def, nat.cast_eq_zero] using ne_of_gt npos
        end } } }
end

/-- In a finite measure space, if every open set can be approximated from inside by closed sets,
then the measure is weakly regular -/
theorem weakly_regular_of_inner_regular_of_is_finite_measure [borel_space α]
  (μ : measure α) [is_finite_measure μ]
  (h0 : ∀ (U : set α), is_open U → μ U ≤ ⨆ (F : set α) (hF : is_closed F) (FU : F ⊆ U), μ F) :
  weakly_regular μ :=
{ outer_regular := begin
    assume s hs,
    apply ennreal.le_of_forall_pos_le_add (λ ε εpos h, le_of_lt _),
    rcases exists_between (ennreal.coe_lt_coe.2 εpos) with ⟨δ, δpos, δε⟩,
    simp only [infi_lt_iff],
    rcases (exists_closed_subset_self_subset_open_of_pos μ h0 hs δ δpos).1
      with ⟨U, U_open, sU, μU⟩,
    refine ⟨U, U_open, sU, μU.trans_lt _⟩,
    rwa ennreal.add_lt_add_iff_left (measure_ne_top μ s),
  end,
  inner_regular := h0 }

/-- The restriction of a weakly regular measure to an open set of finite measure is
weakly regular. Superseded by `restrict_of_measurable_set`, proving the same statement for
measurable sets instead of open sets. -/
lemma restrict_of_is_open [borel_space α] [weakly_regular μ]
  (U : set α) (hU : is_open U) (h'U : μ U < ∞) : weakly_regular (μ.restrict U) :=
begin
  haveI : fact (μ U < ∞) := ⟨h'U⟩,
  refine weakly_regular_of_inner_regular_of_is_finite_measure _ (λ V V_open, _),
  simp only [restrict_apply' hU.measurable_set],
  refine le_trans (weakly_regular.inner_regular (V_open.inter hU)) _,
  simp only [and_imp, supr_le_iff, subset_inter_iff],
  assume F F_closed FV FU,
  have : F = F ∩ U :=
    subset.antisymm (by simp [subset.refl, FU]) (inter_subset_left _ _),
  conv_lhs {rw this},
  simp_rw [supr_and', supr_subtype'],
  exact le_supr (λ s : {s // is_closed s ∧ s ⊆ V}, μ (s ∩ U)) ⟨F, F_closed, FV⟩,
end

lemma _root_.measurable_set.exists_lt_is_closed_of_ne_top_of_pos [opens_measurable_space α]
  [weakly_regular μ] ⦃A : set α⦄ (hA : measurable_set A) (h'A : μ A ≠ ∞) {ε : ℝ≥0∞} (εpos : 0 < ε) :
  ∃ F, is_closed F ∧ F ⊆ A ∧ μ A < μ F + ε :=
begin
  have : μ A < ⨆ (F : set α) (h : is_closed F) (h2 : F ⊆ A), (μ F + ε),
  { haveI : nonempty {F // is_closed F ∧ F ⊆ A} := ⟨⟨∅, is_closed_empty, empty_subset _⟩⟩,
    simp_rw [hA.measure_eq_supr_is_closed_of_ne_top h'A, supr_and',
      supr_subtype', ← ennreal.supr_add],
    simpa only [add_zero, ennreal.coe_zero] using (ennreal.add_lt_add_iff_left _).mpr εpos,
    convert h'A,
    simp_rw [hA.measure_eq_supr_is_closed_of_ne_top h'A, supr_and', supr_subtype'] },
  simpa only [lt_supr_iff, exists_prop],
end

/-- The restriction of a weakly regular measure to a measurable set of finite measure is
weakly regular. -/
lemma restrict_of_measurable_set [borel_space α] [weakly_regular μ]
  (A : set α) (hA : measurable_set A) (h'A : μ A ≠ ∞) : weakly_regular (μ.restrict A) :=
begin
  haveI : fact (μ A < ∞) := ⟨lt_top_iff_ne_top.2 h'A⟩,
  refine weakly_regular_of_inner_regular_of_is_finite_measure _ (λ V V_open, _),
  simp only [restrict_apply' hA],
  rw (V_open.measurable_set.inter hA).measure_eq_supr_is_closed_of_ne_top,
  { simp only [and_imp, supr_le_iff, subset_inter_iff],
    assume F F_closed FV FU,
    have : F = F ∩ A :=
      subset.antisymm (by simp [subset.refl, FU]) (inter_subset_left _ _),
    conv_lhs {rw this},
    simp_rw [supr_and', supr_subtype'],
    exact le_supr (λ s : {s // is_closed s ∧ s ⊆ V}, μ (s ∩ A)) ⟨F, F_closed, FV⟩ },
  { exact ne_top_of_le_ne_top h'A (measure_mono (inter_subset_right _ _)) },
  { apply_instance }
end

/-- In a metric space (or even a pseudo emetric space), an open set can be approximated from inside
by closed sets. -/
lemma inner_regular_of_pseudo_emetric_space {X : Type*}
  [pseudo_emetric_space X] [measurable_space X] [borel_space X] (μ : measure X)
  (U : set X) (U_open : is_open U) :
  μ U ≤ ⨆ (F : set X) (hF : is_closed F) (FU : F ⊆ U), μ F :=
begin
  rcases U_open.exists_Union_is_closed with ⟨F, F_closed, F_subset, F_Union, F_mono⟩,
  conv_lhs { rw ← F_Union },
  rw measure_Union_eq_supr (λ n, (F_closed n).measurable_set) F_mono.directed_le,
  simp only [supr_le_iff],
  assume n,
  simp_rw [supr_and', supr_subtype'],
  exact le_supr (λ s : {s // is_closed s ∧ s ⊆ U}, μ s) ⟨F n, F_closed n, F_subset n⟩,
end

/-- Any finite measure on a metric space (or even a pseudo emetric space) is weakly regular. -/
@[priority 100] -- see Note [lower instance priority]
instance of_pseudo_emetric_space_of_is_finite_measure {X : Type*} [pseudo_emetric_space X]
  [measurable_space X] [borel_space X] (μ : measure X) [is_finite_measure μ] :
  weakly_regular μ :=
weakly_regular_of_inner_regular_of_is_finite_measure μ $ inner_regular_of_pseudo_emetric_space μ

end weakly_regular

namespace regular

/-- Any locally finite measure on a sigma compact locally compact metric space is regular. -/
@[priority 100] -- see Note [lower instance priority]
instance of_sigma_compact_space_of_is_locally_finite_measure {X : Type*}
  [emetric_space X] [sigma_compact_space X] [locally_compact_space X]
  [measurable_space X] [borel_space X] (μ : measure X)
  [is_locally_finite_measure μ] : regular μ :=
{ lt_top_of_is_compact := λ K hK, hK.measure_lt_top,
  inner_regular :=
  begin
    /- Given an open set, it can be approximated from inside by closed sets thanks to
    `inner_regular_of_pseudo_emetric_space`. Each such closed set `F` can be approximated by a
    compact set `B n ∩ F`, using a compact exhaustion `B n` of the space. -/
    assume U U_open,
    refine (weakly_regular.inner_regular_of_pseudo_emetric_space μ U U_open).trans _,
    simp only [supr_le_iff],
    assume F F_closed FU,
    have B : compact_exhaustion X := default _,
    have : F = ⋃ n, B n ∩ F, by rw [← Union_inter, B.Union_eq, univ_inter],
    rw [this, measure_Union_eq_supr
      (λ n, (B.is_compact n).measurable_set.inter F_closed.measurable_set)],
    { simp_rw [supr_le_iff, supr_and', supr_subtype'],
      assume n,
      exact le_supr (λ K : {K // is_compact K ∧ K ⊆ U}, μ K)
        ⟨B n ∩ F, is_compact.inter_right (B.is_compact n) F_closed,
          subset.trans (inter_subset_right _ _) FU⟩ },
    { apply (monotone_nat_of_le_succ (λ n, _)).directed_le,
      exact inter_subset_inter_left _ (B.subset_succ n) },
  end,
  outer_regular :=
  begin
    /- let `B n` be a compact exhaustion of the space, and let `C n = B n \ B (n-1)`. Consider a
    measurable set `A`. Then `A ∩ C n` is a set of finite measure, that can be approximated by an
    open set `U n` (by using the fact that the measure restricted to `B (n+1)` is finite, and
    therefore weakly regular). The union of the `U n` is an open set containing `A`, with measure
    arbitrarily close to that of `A`.
    -/
    assume A hA,
    apply ennreal.le_of_forall_pos_le_add (λ ε εpos μA, le_of_lt _),
    rcases ennreal.exists_pos_sum_of_encodable' (ennreal.coe_pos.2 εpos).ne' ℕ with ⟨δ, δpos, hδ⟩,
    have B : compact_exhaustion X := default _,
    let C := disjointed (λ n, B n),
    have C_meas : ∀ n, measurable_set (C n) :=
      measurable_set.disjointed (λ n, (B.is_compact n).measurable_set),
    have A_eq : A = (⋃ n, A ∩ C n),
      by simp_rw [← inter_Union, C, Union_disjointed, compact_exhaustion.Union_eq, inter_univ],
    have μA_eq : μ A = ∑' n, μ (A ∩ C n),
    { conv_lhs { rw A_eq },
      rw measure_Union,
      { assume m n hmn,
        exact disjoint.mono (inter_subset_right _ _) (inter_subset_right _ _)
          (disjoint_disjointed _ m n hmn), },
      { exact (λ n, hA.inter (C_meas n)) } },
    have : ∀ n, ∃ U, is_open U ∧ (A ∩ C n ⊆ U) ∧ (μ U ≤ μ (A ∩ C n) + δ n),
    { assume n,
      set ν := μ.restrict (B (n+1)) with hν,
      haveI : is_finite_measure ν :=
      ⟨begin
        rw [restrict_apply measurable_set.univ, univ_inter],
        exact is_compact.measure_lt_top (B.is_compact _),
      end⟩,
      have : (⨅ (U : set X) (h : is_open U) (h2 : A ∩ C n ⊆ U), ν U) < ν (A ∩ C n) + δ n :=
      begin
        refine (outer_regular.outer_regular (hA.inter (C_meas n))).trans_lt _,
        simpa only [add_zero] using (ennreal.add_lt_add_iff_left (measure_ne_top ν _)).mpr (δpos n),
      end,
      simp only [infi_lt_iff] at this,
      rcases this with ⟨U, U_open, UA, νU⟩,
      refine ⟨U ∩ interior (B (n+1)), U_open.inter is_open_interior, _, _⟩,
      { simp only [UA, true_and, subset_inter_iff],
        refine (inter_subset_right _ _).trans _,
        exact (disjointed_subset _ n).trans (B.subset_interior_succ _) },
      { simp only [hν, restrict_apply' (B.is_compact _).measurable_set] at νU,
        calc μ (U ∩ interior (B (n + 1))) ≤ μ (U ∩ B (n + 1)) :
          measure_mono (inter_subset_inter_right _ interior_subset)
        ... ≤ μ (A ∩ C n ∩ B (n + 1)) + δ n : νU.le
        ... ≤ μ (A ∩ C n) + δ n :
          add_le_add (measure_mono (inter_subset_left _ _)) (le_refl _) } },
    choose U hU using this,
    simp_rw [infi_lt_iff],
    refine ⟨⋃ n, U n, is_open_Union (λ n, (hU n).1), _, _⟩,
    { rw A_eq, exact Union_subset_Union (λ n, (hU n).2.1) },
    { calc μ (⋃ (n : ℕ), U n)
          ≤ ∑' n, μ (U n) : measure_Union_le _
      ... ≤ ∑' n, (μ (A ∩ C n) + δ n) : ennreal.tsum_le_tsum (λ n, (hU n).2.2)
      ... < μ A + ε :
        by { rw [ennreal.tsum_add, μA_eq.symm], exact (ennreal.add_lt_add_iff_left μA.ne).2 hδ } }
  end }

end regular

end measure
end measure_theory

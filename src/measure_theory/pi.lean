/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.prod

/-!
# Product measures

In this file we define and prove properties about finite products of measures
(and at some point, countable products of measures).

## Main definition

* `measure_theory.measure.pi`: The product of finitely many σ-finite measures.
  Given `μ : Π i : ι, measure (α i)` for `[fintype ι]` it has type `measure (Π i : ι, α i)`.

## Implementation Notes

We define `measure_theory.outer_measure.pi`, the product of finitely many outer measures, as the
maximal outer measure `n` with the property that `n (pi univ s) ≤ ∏ i, m i (s i)`,
where `pi univ s` is the product of the sets `{ s i | i : ι }`.

We then show that this induces a product of measures, called `measure_theory.measure.pi`.
For a collection of σ-finite measures `μ` and a collection of measurable sets `s` we show that
`measure.pi μ (pi univ s) = ∏ i, m i (s i)`. To do this, we follow the following steps:
* We know that there is some ordering on `ι`, given by an element of `[encodable ι]`.
* Using this, we have an equivalence `measurable_equiv.pi_measurable_equiv_tprod` between
  `Π ι, α i` and an iterated product of `α i`, called `list.tprod α l` for some list `l`.
* On this iterated product we can easily define a product measure `measure_theory.measure.tprod`
  by iterating `measure_theory.measure.prod`
* Using the previous two steps we construct `measure_theory.measure.pi'` on `Π ι, α i` for encodable
  `ι`.
* We know that `measure_theory.measure.pi'` sends products of sets to products of measures, and
  since `measure_theory.measure.pi` is the maximal such measure (or at least, it comes from an outer
  measure which is the maximal such outer measure), we get the same rule for
  `measure_theory.measure.pi`.

## Tags

finitary product measure

-/

noncomputable theory
open function set measure_theory.outer_measure
open_locale classical big_operators

namespace measure_theory

variables {ι : Type*} [fintype ι] {α : ι → Type*} {m : Π i, outer_measure (α i)}

/-- An upper bound for the measure in a finite product space.
  It is defined to by taking the image of the set under all projections, and taking the product
  of the measures of these images.
  For measurable boxes it is equal to the correct measure. -/
@[simp] def pi_premeasure (m : Π i, outer_measure (α i)) (s : set (Π i, α i)) : ennreal :=
∏ i, m i (eval i '' s)

lemma pi_premeasure_pi {s : Π i, set (α i)} (hs : (pi univ s).nonempty) :
  pi_premeasure m (pi univ s) = ∏ i, m i (s i) :=
by simp [hs]

lemma pi_premeasure_pi' [nonempty ι] {s : Π i, set (α i)} :
  pi_premeasure m (pi univ s) = ∏ i, m i (s i) :=
begin
  cases (pi univ s).eq_empty_or_nonempty with h h,
  { rcases univ_pi_eq_empty_iff.mp h with ⟨i, hi⟩,
    have : ∃ i, m i (s i) = 0 := ⟨i, by simp [hi]⟩,
    simpa [h, finset.card_univ, zero_pow (fintype.card_pos_iff.mpr _inst_2),
      @eq_comm _ (0 : ennreal), finset.prod_eq_zero_iff] },
  { simp [h] }
end

lemma pi_premeasure_pi_mono {s t : set (Π i, α i)} (h : s ⊆ t) :
  pi_premeasure m s ≤ pi_premeasure m t :=
finset.prod_le_prod' (λ i _, (m i).mono' (image_subset _ h))

lemma pi_premeasure_pi_eval [nonempty ι] {s : set (Π i, α i)} :
  pi_premeasure m (pi univ (λ i, eval i '' s)) = pi_premeasure m s :=
by simp [pi_premeasure_pi']

namespace outer_measure

/-- `outer_measure.pi m` is the finite product of the outer measures `{m i | i : ι}`.
  It is defined to be the maximal outer measure `n` with the property that
  `n (pi univ s) ≤ ∏ i, m i (s i)`, where `pi univ s` is the product of the sets
  `{ s i | i : ι }`. -/
protected def pi (m : Π i, outer_measure (α i)) : outer_measure (Π i, α i) :=
bounded_by (pi_premeasure m)

lemma pi_pi_le (m : Π i, outer_measure (α i)) (s : Π i, set (α i)) :
  outer_measure.pi m (pi univ s) ≤ ∏ i, m i (s i) :=
by { cases (pi univ s).eq_empty_or_nonempty with h h, simp [h],
     exact (bounded_by_le _).trans_eq (pi_premeasure_pi h) }


lemma le_pi {m : Π i, outer_measure (α i)} {n : outer_measure (Π i, α i)} :
  n ≤ outer_measure.pi m ↔ ∀ (s : Π i, set (α i)), (pi univ s).nonempty →
    n (pi univ s) ≤ ∏ i, m i (s i) :=
begin
  rw [outer_measure.pi, le_bounded_by'], split,
  { intros h s hs, refine (h _ hs).trans_eq (pi_premeasure_pi hs) },
  { intros h s hs, refine le_trans (n.mono $ subset_pi_eval_image univ s) (h _ _),
    simp [univ_pi_nonempty_iff, hs] }
end

end outer_measure


namespace measure

variables [Π i, measurable_space (α i)] (μ : Π i, measure (α i))

section tprod

open list
variables {δ : Type*} {π : δ → Type*} [∀ x, measurable_space (π x)]

/-- A product of measures in `tprod α l`. -/
-- for some reason the equation compiler doesn't like this definition
protected def tprod (l : list δ) (μ : Π i, measure (π i)) : measure (tprod π l) :=
by { induction l with i l ih, exact dirac punit.star, exact (μ i).prod ih }

@[simp] lemma tprod_nil (μ : Π i, measure (π i)) : measure.tprod [] μ = dirac punit.star := rfl

@[simp] lemma tprod_cons (i : δ) (l : list δ) (μ : Π i, measure (π i)) :
  measure.tprod (i :: l) μ = (μ i).prod (measure.tprod l μ) := rfl

instance sigma_finite_tprod (l : list δ) (μ : Π i, measure (π i)) [∀ i, sigma_finite (μ i)] :
  sigma_finite (measure.tprod l μ) :=
begin
  induction l with i l ih,
  { rw [tprod_nil], apply_instance },
  { rw [tprod_cons], resetI, apply_instance }
end

lemma tprod_tprod (l : list δ) (μ : Π i, measure (π i)) [∀ i, sigma_finite (μ i)]
  {s : Π i, set (π i)} (hs : ∀ i, is_measurable (s i)) :
  measure.tprod l μ (set.tprod l s) = (l.map (λ i, (μ i) (s i))).prod :=
begin
  induction l with i l ih, { simp },
  simp_rw [tprod_cons, set.tprod, prod_prod (hs i) (is_measurable.tprod l hs), map_cons,
    prod_cons, ih]
end

lemma tprod_tprod_le (l : list δ) (μ : Π i, measure (π i)) [∀ i, sigma_finite (μ i)]
  (s : Π i, set (π i)) : measure.tprod l μ (set.tprod l s) ≤ (l.map (λ i, (μ i) (s i))).prod :=
begin
  induction l with i l ih, { simp [le_refl] },
  simp_rw [tprod_cons, set.tprod, map_cons, prod_cons],
  refine (prod_prod_le _ _).trans _, exact ennreal.mul_left_mono ih
end

end tprod

section encodable

open list measurable_equiv
variables [encodable ι]

/-- The product measure on an encodable finite type, defined by mapping `measure.tprod` along the
  equivalence `measurable_equiv.pi_measurable_equiv_tprod`.
  The definition `measure_theory.measure.pi` should be used instead of this one. -/
def pi' : measure (Π i, α i) :=
measure.map (tprod.elim' encodable.mem_sorted_univ) (measure.tprod (encodable.sorted_univ ι) μ)

lemma pi'_pi [∀ i, sigma_finite (μ i)] {s : Π i, set (α i)}
  (hs : ∀ i, is_measurable (s i)) : pi' μ (pi univ s) = ∏ i, μ i (s i) :=
begin
  have hl := λ i : ι, encodable.mem_sorted_univ i,
  have hnd := @encodable.sorted_univ_nodup ι _ _,
  rw [pi', map_apply (measurable_tprod_elim' hl) (is_measurable.pi_fintype (λ i _, hs i)),
    elim_preimage_pi hnd, tprod_tprod _ μ hs, ← list.prod_to_finset _ hnd],
  congr' with i, simp [hl]
end

lemma pi'_pi_le [∀ i, sigma_finite (μ i)] {s : Π i, set (α i)} :
  pi' μ (pi univ s) ≤ ∏ i, μ i (s i) :=
begin
  have hl := λ i : ι, encodable.mem_sorted_univ i,
  have hnd := @encodable.sorted_univ_nodup ι _ _,
  apply ((pi_measurable_equiv_tprod hnd hl).symm.map_apply (pi univ s)).trans_le,
  dsimp only [pi_measurable_equiv_tprod, tprod.pi_equiv_tprod, coe_symm_mk, equiv.coe_fn_symm_mk],
  rw [elim_preimage_pi hnd],
  refine (tprod_tprod_le _ _ _).trans_eq _,
  rw [← list.prod_to_finset _ hnd],
  congr' with i, simp [hl]
end

end encodable

lemma pi_caratheodory :
  measurable_space.pi ≤ (outer_measure.pi (λ i, (μ i).to_outer_measure)).caratheodory :=
begin
  refine supr_le _,
  intros i s hs,
  rw [measurable_space.comap] at hs,
  rcases hs with ⟨s, hs, rfl⟩,
  apply bounded_by_caratheodory,
  intro t,
  simp_rw [pi_premeasure],
  refine finset.prod_add_prod_le' (finset.mem_univ i) _ _ _,
  { simp [image_inter_preimage, image_diff_preimage, (μ i).caratheodory hs, le_refl] },
  { rintro j - hj, apply mono', apply image_subset, apply inter_subset_left },
  { rintro j - hj, apply mono', apply image_subset, apply diff_subset }
end

/-- `measure.pi μ` is the finite product of the measures `{μ i | i : ι}`.
  It is defined to be measure corresponding to `measure_theory.outer_measure.pi`. -/
protected def pi : measure (Π i, α i) :=
to_measure (outer_measure.pi (λ i, (μ i).to_outer_measure)) (pi_caratheodory μ)

local attribute [instance] encodable.fintype.encodable
lemma pi_pi [∀ i, sigma_finite (μ i)] (s : Π i, set (α i))
  (hs : ∀ i, is_measurable (s i)) : measure.pi μ (pi univ s) = ∏ i, μ i (s i) :=
begin
  refine le_antisymm _ _,
  { rw [measure.pi, to_measure_apply _ _ (is_measurable.pi_fintype (λ i _, hs i))],
    apply outer_measure.pi_pi_le },
  { rw [← pi'_pi],
    work_on_goal 1 { exact hs },
    simp_rw [measure.pi, to_measure_apply _ _ (is_measurable.pi_fintype (λ i _, hs i)),
      ← to_outer_measure_apply],
    suffices : (pi' μ).to_outer_measure ≤ outer_measure.pi (λ i, (μ i).to_outer_measure),
    { exact this _ },
    clear hs s,
    rw [outer_measure.le_pi],
    intros s hs,
    simp_rw [to_outer_measure_apply],
    exact pi'_pi_le μ }
end

end measure

end measure_theory

/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.box_integral.box.basic

/-!
# Partitions of rectangular boxes in `ℝⁿ`

In this file we define (pre)partitions of rectangular boxes in `ℝⁿ`.  A partition of a box `I` in
`ℝⁿ` (see `box_integral.prepartition` and `box_integral.prepartition.is_partition`) is a finite set
of pairwise disjoint boxes such that their union is exactly `I`. We use `boxes : finset (box ι)` to
store the set of boxes.

Many lemmas about box integrals deal with pairwise disjoint collections of subboxes, so we define a
structure `box_integral.prepartition (I : box_integral.box ι)` that stores a collection of boxes
such that

* each box `J ∈ boxes` is a subbox of `I`;
* the boxes are pairwise disjoint as sets in `ℝⁿ`.

Then we define a predicate `box_integral.prepartition.is_partition`; `π.is_partition` means that the
boxes of `π` actually cover the whole `I`. We also define some operations on prepartitions:

* `box_integral.partition.bUnion`: split each box of a partition into smaller boxes;
* `box_integral.partition.restrict`: restrict a partition to a smaller box.

We also define a `semilattice_inf_top` structure on `box_integral.partition I` for all
`I : box_integral.box ι`.

## Tags

rectangular box, partition
-/

open set finset function
open_locale classical nnreal big_operators
noncomputable theory

namespace box_integral

variables {ι : Type*}

/-- A prepartition of `I : box_integral.box ι` is a finite set of pairwise disjoint subboxes of
`I`. -/
structure prepartition (I : box ι) :=
(boxes : finset (box ι))
(le_of_mem' : ∀ J ∈ boxes, J ≤ I)
(pairwise_disjoint : pairwise_on ↑boxes (disjoint on (coe : box ι → set (ι → ℝ))))

namespace prepartition

variables {I J J₁ J₂ : box ι} (π : prepartition I) {π₁ π₂ : prepartition I} {x : ι → ℝ}

instance : has_mem (box ι) (prepartition I) := ⟨λ J π, J ∈ π.boxes⟩

@[simp] lemma mem_boxes : J ∈ π.boxes ↔ J ∈ π := iff.rfl
@[simp] lemma mem_mk {s h₁ h₂} : J ∈ (mk s h₁ h₂ : prepartition I) ↔ J ∈ s := iff.rfl

lemma disjoint_coe_of_mem (h₁ : J₁ ∈ π) (h₂ : J₂ ∈ π) (h : J₁ ≠ J₂) :
  disjoint (J₁ : set (ι → ℝ)) J₂ :=
π.pairwise_disjoint J₁ h₁ J₂ h₂ h

lemma eq_of_mem_of_mem (h₁ : J₁ ∈ π) (h₂ : J₂ ∈ π) (hx₁ : x ∈ J₁) (hx₂ : x ∈ J₂) :
  J₁ = J₂ :=
by_contra $ λ H, π.disjoint_coe_of_mem h₁ h₂ H ⟨hx₁, hx₂⟩

lemma eq_of_le_of_le (h₁ : J₁ ∈ π) (h₂ : J₂ ∈ π) (hle₁ : J ≤ J₁) (hle₂ : J ≤ J₂) :
  J₁ = J₂ :=
π.eq_of_mem_of_mem h₁ h₂ (hle₁ J.upper_mem) (hle₂ J.upper_mem)

lemma eq_of_le (h₁ : J₁ ∈ π) (h₂ : J₂ ∈ π) (hle : J₁ ≤ J₂) : J₁ = J₂ :=
π.eq_of_le_of_le h₁ h₂ le_rfl hle

lemma le_of_mem (hJ : J ∈ π) : J ≤ I := π.le_of_mem' J hJ

lemma lower_le_lower (hJ : J ∈ π) : I.lower ≤ J.lower := box.antitone_lower (π.le_of_mem hJ)

lemma upper_le_upper (hJ : J ∈ π) : J.upper ≤ I.upper := box.monotone_upper (π.le_of_mem hJ)

lemma injective_boxes : function.injective (boxes : prepartition I → finset (box ι)) :=
by { rintro ⟨s₁, h₁, h₁'⟩ ⟨s₂, h₂, h₂'⟩ (rfl : s₁ = s₂), refl }

@[ext] lemma ext (h : ∀ J, J ∈ π₁ ↔ J ∈ π₂) : π₁ = π₂ := injective_boxes $ finset.ext h

/-- The singleton prepartition `{J}`, `J ≤ I`. -/
@[simps] def single (I J : box ι) (h : J ≤ I) : prepartition I :=
⟨{J}, by simpa, by simp⟩

@[simp] lemma mem_single {J'} (h : J ≤ I) : J' ∈ single I J h ↔ J' = J := mem_singleton

/-- We say that `π ≤ π'` if each box of `π` is a subbox of some box of `π'`. -/
instance : has_le (prepartition I) := ⟨λ π π', ∀ ⦃I⦄, I ∈ π → ∃ I' ∈ π', I ≤ I'⟩

instance : order_top (prepartition I) :=
{ le := (≤),
  le_refl := λ π I hI, ⟨I, hI, le_rfl⟩,
  le_trans := λ π₁ π₂ π₃ h₁₂ h₂₃ I₁ hI₁,
    let ⟨I₂, hI₂, hI₁₂⟩ := h₁₂ hI₁, ⟨I₃, hI₃, hI₂₃⟩ := h₂₃ hI₂ in ⟨I₃, hI₃, hI₁₂.trans hI₂₃⟩,
  le_antisymm :=
    begin
      suffices : ∀ {π₁ π₂ : prepartition I}, π₁ ≤ π₂ → π₂ ≤ π₁ → π₁.boxes ⊆ π₂.boxes,
        from λ π₁ π₂ h₁ h₂, injective_boxes (subset.antisymm (this h₁ h₂) (this h₂ h₁)),
      intros π₁ π₂ h₁ h₂ J hJ,
      rcases h₁ hJ with ⟨J', hJ', hle⟩, rcases h₂ hJ' with ⟨J'', hJ'', hle'⟩,
      obtain rfl : J = J'', from π₁.eq_of_le hJ hJ'' (hle.trans hle'),
      obtain rfl : J' = J, from le_antisymm ‹_› ‹_›,
      assumption
    end,
  top := single I I le_rfl,
  le_top := λ π J hJ, ⟨I, by simp, π.le_of_mem hJ⟩ }

instance : order_bot (prepartition I) :=
{ bot := ⟨∅, λ J hJ, false.elim hJ, λ J hJ, false.elim hJ⟩,
  bot_le := λ π J hJ, false.elim hJ,
  .. prepartition.order_top }

instance : inhabited (prepartition I) := ⟨⊤⟩

lemma le_def : π₁ ≤ π₂ ↔ ∀ J ∈ π₁, ∃ J' ∈ π₂, J ≤ J' := iff.rfl

@[simp] lemma mem_top : J ∈ (⊤ : prepartition I) ↔ J = I := mem_singleton

@[simp] lemma top_boxes : (⊤ : prepartition I).boxes = {I} := rfl

@[simp] lemma not_mem_bot : J ∉ (⊥ : prepartition I) := id

@[simp] lemma bot_boxes : (⊥ : prepartition I).boxes = ∅ := rfl

/-- An auxiliary lemma used to prove that the same point can't belong to more than
`2 ^ fintype.card ι` closed boxes of a prepartition. -/
lemma inj_on_set_of_mem_Icc_set_of_lower_eq (x : ι → ℝ) :
  inj_on (λ J : box ι, {i | J.lower i = x i}) {J | J ∈ π ∧ x ∈ J.Icc} :=
begin
  rintros J₁ ⟨h₁, hx₁⟩ J₂ ⟨h₂, hx₂⟩ (H : {i | J₁.lower i = x i} = {i | J₂.lower i = x i}),
  suffices : ∀ i, (Ioc (J₁.lower i) (J₁.upper i) ∩ Ioc (J₂.lower i) (J₂.upper i)).nonempty,
  { choose y hy₁ hy₂,
    exact π.eq_of_mem_of_mem h₁ h₂ hy₁ hy₂ },
  intro i,
  simp only [set.ext_iff, mem_set_of_eq] at H,
  cases (hx₁.1 i).eq_or_lt with hi₁ hi₁,
  { have hi₂ : J₂.lower i = x i, from (H _).1 hi₁,
    have H₁ : x i < J₁.upper i, by simpa only [hi₁] using J₁.lower_lt_upper i,
    have H₂ : x i < J₂.upper i, by simpa only [hi₂] using J₂.lower_lt_upper i,
    rw [Ioc_inter_Ioc, hi₁, hi₂, sup_idem, set.nonempty_Ioc],
    exact lt_min H₁ H₂ },
  { have hi₂ : J₂.lower i < x i, from (hx₂.1 i).lt_of_ne (mt (H _).2 hi₁.ne),
    exact ⟨x i, ⟨hi₁, hx₁.2 i⟩, ⟨hi₂, hx₂.2 i⟩⟩ }
end

/-- The set of boxes of a prepartition that contain `x` in their closures has cardinality
at most `2 ^ fintype.card ι`. -/
lemma card_filter_mem_Icc_le [fintype ι] (x : ι → ℝ) :
  (π.boxes.filter (λ J : box ι, x ∈ J.Icc)).card ≤ 2 ^ fintype.card ι :=
begin
  rw [← fintype.card_set],
  refine finset.card_le_card_of_inj_on (λ J : box ι, {i | J.lower i = x i})
    (λ _ _, finset.mem_univ _) _,
  simpa only [finset.mem_filter] using π.inj_on_set_of_mem_Icc_set_of_lower_eq x
end

/-- Given a prepartition `π : box_integral.prepartition I`, `π.Union` is the part of `I` covered by
the boxes of `π`. -/
protected def Union : set (ι → ℝ) := ⋃ J ∈ π, ↑J

lemma Union_def : π.Union = ⋃ J ∈ π, ↑J := rfl

lemma Union_def' : π.Union = ⋃ J ∈ π.boxes, ↑J := rfl

@[simp] lemma mem_Union : x ∈ π.Union ↔ ∃ J ∈ π, x ∈ J := set.mem_bUnion_iff

@[simp] lemma Union_single (h : J ≤ I) : (single I J h).Union = J := by simp [Union_def]

@[simp] lemma Union_top : (⊤ : prepartition I).Union = I := by simp [prepartition.Union]

@[simp] lemma Union_eq_empty : π₁.Union = ∅ ↔ π₁ = ⊥ :=
by simp [← injective_boxes.eq_iff, finset.ext_iff, prepartition.Union, imp_false]

@[simp] lemma Union_bot : (⊥ : prepartition I).Union = ∅ := Union_eq_empty.2 rfl

lemma subset_Union (h : J ∈ π) : ↑J ⊆ π.Union := subset_bUnion_of_mem h

lemma Union_subset : π.Union ⊆ I := bUnion_subset π.le_of_mem'

@[mono] lemma Union_mono (h : π₁ ≤ π₂) : π₁.Union ⊆ π₂.Union :=
λ x hx, let ⟨J₁, hJ₁, hx⟩ := π₁.mem_Union.1 hx, ⟨J₂, hJ₂, hle⟩ := h hJ₁
  in π₂.mem_Union.2 ⟨J₂, hJ₂, hle hx⟩

lemma disjoint_boxes_of_disjoint_Union (h : disjoint π₁.Union π₂.Union) :
  disjoint π₁.boxes π₂.boxes :=
finset.disjoint_left.2 $ λ J h₁ h₂, h.mono (π₁.subset_Union h₁) (π₂.subset_Union h₂)
  ⟨J.upper_mem, J.upper_mem⟩

lemma le_iff_nonempty_imp_le_and_Union_subset : π₁ ≤ π₂ ↔
  (∀ (J ∈ π₁) (J' ∈ π₂), (J ∩ J' : set (ι → ℝ)).nonempty → J ≤ J') ∧ π₁.Union ⊆ π₂.Union :=
begin
  fsplit,
  { refine λ H, ⟨λ J hJ J' hJ' Hne, _, Union_mono H⟩,
    rcases H hJ with ⟨J'', hJ'', Hle⟩, rcases Hne with ⟨x, hx, hx'⟩,
    rwa π₂.eq_of_mem_of_mem hJ' hJ'' hx' (Hle hx) },
  { rintro ⟨H, HU⟩ J hJ, simp only [set.subset_def, mem_Union] at HU,
    rcases HU J.upper ⟨J, hJ, J.upper_mem⟩ with ⟨J₂, hJ₂, hx⟩,
    exact ⟨J₂, hJ₂, H _ hJ _ hJ₂ ⟨_, J.upper_mem, hx⟩⟩ }
end

lemma eq_of_boxes_subset_Union_superset (h₁ : π₁.boxes ⊆ π₂.boxes) (h₂ : π₂.Union ⊆ π₁.Union) :
  π₁ = π₂ :=
le_antisymm (λ J hJ, ⟨J, h₁ hJ, le_rfl⟩) $ le_iff_nonempty_imp_le_and_Union_subset.2
  ⟨λ J₁ hJ₁ J₂ hJ₂ Hne, (π₂.eq_of_mem_of_mem hJ₁ (h₁ hJ₂) Hne.some_spec.1 Hne.some_spec.2).le, h₂⟩

/-- Given a prepartition `π` of a box `I` and a collection of prepartitions `πi J` of all boxes
`J ∈ π`, returns the prepartition of `I` into the union of the boxes of all `πi J`.

Though we only use the values of `πi` on the boxes of `π`, we require `πi` to be a globally defined
function. -/
@[simps] def bUnion (πi : Π J : box ι, prepartition J) : prepartition I :=
{ boxes := π.boxes.bUnion $ λ J, (πi J).boxes,
  le_of_mem' := λ J hJ,
    begin
      simp only [finset.mem_bUnion, exists_prop, mem_boxes] at hJ,
      rcases hJ with ⟨J', hJ', hJ⟩,
      exact ((πi J').le_of_mem hJ).trans (π.le_of_mem hJ')
    end,
  pairwise_disjoint :=
    begin
      simp only [pairwise_on, finset.mem_coe, finset.mem_bUnion],
      rintro J₁' ⟨J₁, hJ₁, hJ₁'⟩ J₂' ⟨J₂, hJ₂, hJ₂'⟩ Hne x ⟨hx₁, hx₂⟩, apply Hne,
      obtain rfl : J₁ = J₂,
        from π.eq_of_mem_of_mem hJ₁ hJ₂ ((πi J₁).le_of_mem hJ₁' hx₁)
          ((πi J₂).le_of_mem hJ₂' hx₂),
      exact (πi J₁).eq_of_mem_of_mem hJ₁' hJ₂' hx₁ hx₂
    end }

variables {πi πi₁ πi₂ : Π J : box ι, prepartition J}

@[simp] lemma mem_bUnion : J ∈ π.bUnion πi ↔ ∃ J' ∈ π, J ∈ πi J' :=
by simp [bUnion]

lemma bUnion_le (πi : Π J, prepartition J) : π.bUnion πi ≤ π :=
λ J hJ, let ⟨J', hJ', hJ⟩ := π.mem_bUnion.1 hJ in ⟨J', hJ', (πi J').le_of_mem hJ⟩

@[simp] lemma bUnion_top : π.bUnion (λ _, ⊤) = π := by { ext, simp }

@[congr] lemma bUnion_congr (h : π₁ = π₂) (hi : ∀ J ∈ π₁, πi₁ J = πi₂ J) :
  π₁.bUnion πi₁ = π₂.bUnion πi₂ :=
by { subst π₂, ext J, simp [hi] { contextual := tt } }

lemma bUnion_congr_of_le (h : π₁ = π₂) (hi : ∀ J ≤ I, πi₁ J = πi₂ J) :
  π₁.bUnion πi₁ = π₂.bUnion πi₂ :=
bUnion_congr h $ λ J hJ, hi J (π₁.le_of_mem hJ)

@[simp] lemma Union_bUnion (πi : Π J : box ι, prepartition J) :
  (π.bUnion πi).Union = ⋃ J ∈ π, (πi J).Union :=
by simp [prepartition.Union]

@[simp] lemma sum_bUnion_boxes {M : Type*} [add_comm_monoid M] (π : prepartition I)
  (πi : Π J, prepartition J) (f : box ι → M) :
  ∑ J in π.boxes.bUnion (λ J, (πi J).boxes), f J = ∑ J in π.boxes, ∑ J' in (πi J).boxes, f J' :=
begin
  refine finset.sum_bUnion (λ J₁ h₁ J₂ h₂ hne, finset.disjoint_left.2 $ λ J' h₁' h₂', _),
  exact hne (π.eq_of_le_of_le h₁ h₂ ((πi J₁).le_of_mem h₁') ((πi J₂).le_of_mem h₂'))
end

/-- Given a box `J ∈ π.bUnion πi`, returns the box `J' ∈ π` such that `J ∈ πi J'`.
For `J ∉ π.bUnion πi`, returns `I`. -/
def bUnion_index (πi : Π J, prepartition J) (J : box ι) :
  box ι :=
if hJ : J ∈ π.bUnion πi then (π.mem_bUnion.1 hJ).some else I

lemma bUnion_index_mem (hJ : J ∈ π.bUnion πi) :
  π.bUnion_index πi J ∈ π :=
by { rw [bUnion_index, dif_pos hJ], exact (π.mem_bUnion.1 hJ).some_spec.fst }

lemma bUnion_index_le (πi : Π J, prepartition J) (J : box ι) : π.bUnion_index πi J ≤ I :=
begin
  by_cases hJ : J ∈ π.bUnion πi,
  { exact π.le_of_mem (π.bUnion_index_mem hJ) },
  { rw [bUnion_index, dif_neg hJ], exact le_rfl }
end

lemma mem_bUnion_index (hJ : J ∈ π.bUnion πi) : J ∈ πi (π.bUnion_index πi J) :=
by convert (π.mem_bUnion.1 hJ).some_spec.snd; exact dif_pos hJ

lemma le_bUnion_index (hJ : J ∈ π.bUnion πi) : J ≤ π.bUnion_index πi J :=
le_of_mem _ (π.mem_bUnion_index hJ)

/-- Uniqueness property of `box_integral.partition.bUnion_index`. -/
lemma bUnion_index_of_mem (hJ : J ∈ π) {J'} (hJ' : J' ∈ πi J) : π.bUnion_index πi J' = J :=
have J' ∈ π.bUnion πi, from π.mem_bUnion.2 ⟨J, hJ, hJ'⟩,
π.eq_of_le_of_le (π.bUnion_index_mem this) hJ (π.le_bUnion_index this) (le_of_mem _ hJ')

lemma bUnion_assoc (πi : Π J, prepartition J) (πi' : box ι → Π J : box ι, prepartition J) :
  π.bUnion (λ J, (πi J).bUnion (πi' J)) = (π.bUnion πi).bUnion (λ J, πi' (π.bUnion_index πi J) J) :=
begin
  ext J,
  simp only [mem_bUnion, exists_prop],
  fsplit,
  { rintro ⟨J₁, hJ₁, J₂, hJ₂, hJ⟩,
    refine ⟨J₂, ⟨J₁, hJ₁, hJ₂⟩, _⟩,
    rwa π.bUnion_index_of_mem hJ₁ hJ₂ },
  { rintro ⟨J₁, ⟨J₂, hJ₂, hJ₁⟩, hJ⟩,
    refine ⟨J₂, hJ₂, J₁, hJ₁, _⟩,
    rwa π.bUnion_index_of_mem hJ₂ hJ₁ at hJ }
end

/-- Create a `box_integral.prepartition` from a collection of possibly empty boxes by filtering out
the empty one if it exists. -/
def of_with_bot (boxes : finset (with_bot (box ι)))
  (le_of_mem : ∀ J ∈ boxes, (J : with_bot (box ι)) ≤ I)
  (pairwise_disjoint : pairwise_on (boxes : set (with_bot (box ι))) disjoint) :
  prepartition I :=
{ boxes := boxes.erase_none,
  le_of_mem' := λ J hJ,
    begin
      rw mem_erase_none at hJ,
      simpa only [with_bot.some_eq_coe, with_bot.coe_le_coe] using le_of_mem _ hJ
    end,
  pairwise_disjoint := λ J₁ h₁ J₂ h₂ hne,
    begin
      simp only [mem_coe, mem_erase_none] at h₁ h₂,
      exact box.disjoint_coe.1 (pairwise_disjoint _ h₁ _ h₂ (mt option.some_inj.1 hne))
    end }

@[simp] lemma mem_of_with_bot {boxes : finset (with_bot (box ι))} {h₁ h₂} :
  J ∈ (of_with_bot boxes h₁ h₂ : prepartition I) ↔ (J : with_bot (box ι)) ∈ boxes :=
mem_erase_none

@[simp] lemma Union_of_with_bot (boxes : finset (with_bot (box ι)))
  (le_of_mem : ∀ J ∈ boxes, (J : with_bot (box ι)) ≤ I)
  (pairwise_disjoint : pairwise_on (boxes : set (with_bot (box ι))) disjoint) :
  (of_with_bot boxes le_of_mem pairwise_disjoint).Union = ⋃ J ∈ boxes, ↑J :=
begin
  suffices : (⋃ (J : box ι) (hJ : ↑J ∈ boxes), ↑J) = ⋃ J ∈ boxes, ↑J,
    by simpa [of_with_bot, prepartition.Union],
  simp only [← box.bUnion_coe_eq_coe, @Union_comm _ _ (box ι), @Union_comm _ _ (@eq _ _ _),
    Union_Union_eq_right]
end

lemma of_with_bot_le {boxes : finset (with_bot (box ι))}
  {le_of_mem : ∀ J ∈ boxes, (J : with_bot (box ι)) ≤ I}
  {pairwise_disjoint : pairwise_on (boxes : set (with_bot (box ι))) disjoint}
  (H : ∀ J ∈ boxes, J ≠ ⊥ → ∃ J' ∈ π, J ≤ ↑J') :
  of_with_bot boxes le_of_mem pairwise_disjoint ≤ π :=
have ∀ (J : box ι), ↑J ∈ boxes → ∃ J' ∈ π, J ≤ J',
  from λ J hJ, by simpa only [with_bot.coe_le_coe] using H J hJ (with_bot.coe_ne_bot J),
by simpa [of_with_bot, le_def]

lemma le_of_with_bot {boxes : finset (with_bot (box ι))}
  {le_of_mem : ∀ J ∈ boxes, (J : with_bot (box ι)) ≤ I}
  {pairwise_disjoint : pairwise_on (boxes : set (with_bot (box ι))) disjoint}
  (H : ∀ J ∈ π, ∃ J' ∈ boxes, ↑J ≤ J') :
  π ≤ of_with_bot boxes le_of_mem pairwise_disjoint :=
begin
  intros J hJ,
  rcases H J hJ with ⟨J', J'mem, hle⟩,
  lift J' to box ι using ne_bot_of_le_ne_bot (with_bot.coe_ne_bot _) hle,
  exact ⟨J', mem_of_with_bot.2 J'mem, with_bot.coe_le_coe.1 hle⟩
end

lemma of_with_bot_mono {boxes₁ : finset (with_bot (box ι))}
  {le_of_mem₁ : ∀ J ∈ boxes₁, (J : with_bot (box ι)) ≤ I}
  {pairwise_disjoint₁ : pairwise_on (boxes₁ : set (with_bot (box ι))) disjoint}
  {boxes₂ : finset (with_bot (box ι))}
  {le_of_mem₂ : ∀ J ∈ boxes₂, (J : with_bot (box ι)) ≤ I}
  {pairwise_disjoint₂ : pairwise_on (boxes₂ : set (with_bot (box ι))) disjoint}
  (H : ∀ J ∈ boxes₁, J ≠ ⊥ → ∃ J' ∈ boxes₂, J ≤ J') :
  of_with_bot boxes₁ le_of_mem₁ pairwise_disjoint₁ ≤
    of_with_bot boxes₂ le_of_mem₂ pairwise_disjoint₂ :=
le_of_with_bot _ $ λ J hJ, H J (mem_of_with_bot.1 hJ) (with_bot.coe_ne_bot _)

lemma sum_of_with_bot {M : Type*} [add_comm_monoid M]
  (boxes : finset (with_bot (box ι)))
  (le_of_mem : ∀ J ∈ boxes, (J : with_bot (box ι)) ≤ I)
  (pairwise_disjoint : pairwise_on (boxes : set (with_bot (box ι))) disjoint)
  (f : box ι → M) :
  ∑ J in (of_with_bot boxes le_of_mem pairwise_disjoint).boxes, f J =
    ∑ J in boxes, option.elim J 0 f :=
finset.sum_erase_none _ _

/-- Restrict a prepartition to a box. -/
def restrict (π : prepartition I) (J : box ι) :
  prepartition J :=
of_with_bot (π.boxes.image (λ J', J ⊓ J'))
  (λ J' hJ', by { rcases finset.mem_image.1 hJ' with ⟨J', -, rfl⟩, exact inf_le_left })
  begin
    simp only [pairwise_on, on_fun, finset.mem_coe, finset.mem_image],
    rintro _ ⟨J₁, h₁, rfl⟩ _ ⟨J₂, h₂, rfl⟩ Hne,
    have : J₁ ≠ J₂, by { rintro rfl, exact Hne rfl },
    exact ((box.disjoint_coe.2 $ π.disjoint_coe_of_mem h₁ h₂ this).inf_left' _).inf_right' _
  end

@[simp] lemma mem_restrict : J₁ ∈ π.restrict J ↔ ∃ (J' ∈ π), (J₁ : with_bot (box ι)) = J ⊓ J' :=
by simp [restrict, eq_comm]

lemma mem_restrict' : J₁ ∈ π.restrict J ↔ ∃ (J' ∈ π), (J₁ : set (ι → ℝ)) = J ∩ J' :=
by simp only [mem_restrict, ← box.with_bot_coe_inj, box.coe_inf, box.coe_coe]

@[mono] lemma restrict_mono {π₁ π₂ : prepartition I} (Hle : π₁ ≤ π₂) :
  π₁.restrict J ≤ π₂.restrict J :=
begin
  refine of_with_bot_mono (λ J₁ hJ₁ hne, _),
  rw finset.mem_image at hJ₁, rcases hJ₁ with ⟨J₁, hJ₁, rfl⟩,
  rcases Hle hJ₁ with ⟨J₂, hJ₂, hle⟩,
  exact ⟨_, finset.mem_image_of_mem _ hJ₂, inf_le_inf_left _ $ with_bot.coe_le_coe.2 hle⟩
end

lemma monotone_restrict : monotone (λ π : prepartition I, restrict π J) :=
λ π₁ π₂, restrict_mono

/-- Restricting to a larger box does not change the set of boxes. We cannot claim equality
of prepartitions because they have different types. -/
lemma restrict_boxes_of_le (π : prepartition I) (h : I ≤ J) :
  (π.restrict J).boxes = π.boxes :=
begin
  simp only [restrict, of_with_bot, erase_none_eq_bUnion],
  refine finset.image_bUnion.trans _,
  refine (finset.bUnion_congr rfl _).trans finset.bUnion_singleton_eq_self,
  intros J' hJ',
  rw [inf_of_le_right, ← with_bot.some_eq_coe, option.to_finset_some],
  exact with_bot.coe_le_coe.2 ((π.le_of_mem hJ').trans h)
end

@[simp] lemma restrict_self : π.restrict I = π :=
injective_boxes $ restrict_boxes_of_le π le_rfl

@[simp] lemma Union_restrict : (π.restrict J).Union = J ∩ π.Union :=
by simp [restrict, ← inter_Union, ← Union_def]

@[simp] lemma restrict_bUnion (πi : Π J, prepartition J) (hJ : J ∈ π) :
  (π.bUnion πi).restrict J = πi J :=
begin
  refine (eq_of_boxes_subset_Union_superset (λ J₁ h₁, _) _).symm,
  { refine (mem_restrict _).2 ⟨J₁, π.mem_bUnion.2 ⟨J, hJ, h₁⟩, (inf_of_le_right _).symm⟩,
    exact with_bot.coe_le_coe.2 (le_of_mem _ h₁) },
  { simp only [Union_restrict, Union_bUnion, set.subset_def, set.mem_inter_eq, set.mem_Union],
    rintro x ⟨hxJ, J₁, h₁, hx⟩,
    obtain rfl : J = J₁, from π.eq_of_mem_of_mem hJ h₁ hxJ (Union_subset _ hx),
    exact hx }
end

lemma bUnion_le_iff {πi : Π J, prepartition J} {π' : prepartition I} :
  π.bUnion πi ≤ π' ↔ ∀ J ∈ π, πi J ≤ π'.restrict J :=
begin
  fsplit; intros H J hJ,
  { rw ← π.restrict_bUnion πi hJ, exact restrict_mono H },
  { rw mem_bUnion at hJ, rcases hJ with ⟨J₁, h₁, hJ⟩,
    rcases H J₁ h₁ hJ with ⟨J₂, h₂, Hle⟩,
    rcases π'.mem_restrict.mp h₂ with ⟨J₃, h₃, H⟩,
    exact ⟨J₃, h₃, Hle.trans $ with_bot.coe_le_coe.1 $ H.trans_le inf_le_right⟩ }
end

lemma le_bUnion_iff {πi : Π J, prepartition J} {π' : prepartition I} :
  π' ≤ π.bUnion πi ↔ π' ≤ π ∧ ∀ J ∈ π, π'.restrict J ≤ πi J :=
begin
  refine ⟨λ H, ⟨H.trans (π.bUnion_le πi), λ J hJ, _⟩, _⟩,
  { rw ← π.restrict_bUnion πi hJ, exact restrict_mono H },
  { rintro ⟨H, Hi⟩ J' hJ',
    rcases H hJ' with ⟨J, hJ, hle⟩,
    have : J' ∈ π'.restrict J,
      from π'.mem_restrict.2 ⟨J', hJ', (inf_of_le_right $ with_bot.coe_le_coe.2 hle).symm⟩,
    rcases Hi J hJ this with ⟨Ji, hJi, hlei⟩,
    exact ⟨Ji, π.mem_bUnion.2 ⟨J, hJ, hJi⟩, hlei⟩ }
end

instance : has_inf (prepartition I) :=
⟨λ π₁ π₂, π₁.bUnion (λ J, π₂.restrict J)⟩

lemma inf_def (π₁ π₂ : prepartition I) :
  π₁ ⊓ π₂ = π₁.bUnion (λ J, π₂.restrict J) :=
rfl

@[simp] lemma mem_inf {π₁ π₂ : prepartition I} :
  J ∈ π₁ ⊓ π₂ ↔ ∃ (J₁ ∈ π₁) (J₂ ∈ π₂), (J : with_bot (box ι)) = J₁ ⊓ J₂ :=
by simp only [inf_def, mem_bUnion, mem_restrict]

@[simp] lemma Union_inf (π₁ π₂ : prepartition I) : (π₁ ⊓ π₂).Union = π₁.Union ∩ π₂.Union :=
by simp only [inf_def, Union_bUnion, Union_restrict, ← Union_inter, ← Union_def]

instance : semilattice_inf_top (prepartition I) :=
{ inf_le_left := λ π₁ π₂, π₁.bUnion_le _,
  inf_le_right := λ π₁ π₂, (bUnion_le_iff _).2 (λ J hJ, le_rfl),
  le_inf := λ π π₁ π₂ h₁ h₂, π₁.le_bUnion_iff.2 ⟨h₁, λ J hJ, restrict_mono h₂⟩,
  .. prepartition.order_top, .. prepartition.has_inf }

instance : semilattice_inf_bot (prepartition I) :=
{ .. prepartition.order_bot, .. prepartition.semilattice_inf_top }

/-- The prepartition with boxes `{J ∈ π | p J}`. -/
@[simps] def filter (π : prepartition I) (p : box ι → Prop) : prepartition I :=
{ boxes := π.boxes.filter p,
  le_of_mem' := λ J hJ, π.le_of_mem (mem_filter.1 hJ).1,
  pairwise_disjoint := λ J₁ h₁ J₂ h₂, π.disjoint_coe_of_mem (mem_filter.1 h₁).1
    (mem_filter.1 h₂).1 }

@[simp] lemma mem_filter {p : box ι → Prop} : J ∈ π.filter p ↔ J ∈ π ∧ p J := finset.mem_filter

lemma filter_le (π : prepartition I) (p : box ι → Prop) : π.filter p ≤ π :=
λ J hJ, let ⟨hπ, hp⟩ := π.mem_filter.1 hJ in ⟨J, hπ, le_rfl⟩

lemma filter_of_true {p : box ι → Prop} (hp : ∀ J ∈ π, p J) : π.filter p = π :=
by { ext J, simpa using hp J }

@[simp] lemma filter_true : π.filter (λ _, true) = π := π.filter_of_true (λ _ _, trivial)

@[simp] lemma Union_filter_not (π : prepartition I) (p : box ι → Prop) :
  (π.filter (λ J, ¬p J)).Union = π.Union \ (π.filter p).Union :=
begin
  simp only [prepartition.Union],
  convert (@set.bUnion_diff_bUnion_eq _ (box ι) π.boxes (π.filter p).boxes coe _).symm,
  { ext J x, simp { contextual := tt } },
  { convert π.pairwise_disjoint, simp }
end

lemma sum_fiberwise {α M} [add_comm_monoid M] (π : prepartition I) (f : box ι → α) (g : box ι → M) :
  ∑ y in π.boxes.image f, ∑ J in (π.filter (λ J, f J = y)).boxes, g J = ∑ J in π.boxes, g J :=
by convert sum_fiberwise_of_maps_to (λ _, finset.mem_image_of_mem f) g

/-- Union of two disjoint prepartitions. -/
@[simps] def disj_union (π₁ π₂ : prepartition I) (h : disjoint π₁.Union π₂.Union) :
  prepartition I :=
{ boxes := π₁.boxes ∪ π₂.boxes,
  le_of_mem' := λ J hJ, (finset.mem_union.1 hJ).elim π₁.le_of_mem π₂.le_of_mem,
  pairwise_disjoint :=
    suffices ∀ (J₁ ∈ π₁) (J₂ ∈ π₂), J₁ ≠ J₂ → disjoint (J₁ : set (ι → ℝ)) J₂,
      by simpa [pairwise_on_union_of_symmetric (symmetric_disjoint.comap _), pairwise_disjoint],
    λ J₁ h₁ J₂ h₂ _, h.mono (π₁.subset_Union h₁) (π₂.subset_Union h₂) }

@[simp] lemma mem_disj_union (H : disjoint π₁.Union π₂.Union) :
  J ∈ π₁.disj_union π₂ H ↔ J ∈ π₁ ∨ J ∈ π₂ :=
finset.mem_union

@[simp] lemma Union_disj_union (h : disjoint π₁.Union π₂.Union) :
  (π₁.disj_union π₂ h).Union = π₁.Union ∪ π₂.Union :=
by simp [disj_union, prepartition.Union, Union_or, Union_union_distrib]

@[simp] lemma sum_disj_union_boxes {M : Type*} [add_comm_monoid M]
  (h : disjoint π₁.Union π₂.Union) (f : box ι → M) :
  ∑ J in π₁.boxes ∪ π₂.boxes, f J = ∑ J in π₁.boxes, f J + ∑ J in π₂.boxes, f J :=
sum_union $ disjoint_boxes_of_disjoint_Union h

section distortion

variable [fintype ι]

/-- The distortion of a prepartition is the maximum of the distortions of the boxes of this
prepartition. -/
def distortion : ℝ≥0 := π.boxes.sup box.distortion

lemma distortion_le_of_mem (h : J ∈ π) : J.distortion ≤ π.distortion :=
le_sup h

lemma distortion_le_iff {c : ℝ≥0} : π.distortion ≤ c ↔ ∀ J ∈ π, box.distortion J ≤ c :=
sup_le_iff

lemma distortion_bUnion (π : prepartition I) (πi : Π J, prepartition J) :
  (π.bUnion πi).distortion = π.boxes.sup (λ J, (πi J).distortion) :=
sup_bUnion _ _

@[simp] lemma distortion_disj_union (h : disjoint π₁.Union π₂.Union) :
  (π₁.disj_union π₂ h).distortion = max π₁.distortion π₂.distortion :=
sup_union

lemma distortion_of_const {c} (h₁ : π.boxes.nonempty) (h₂ : ∀ J ∈ π, box.distortion J = c) :
  π.distortion = c :=
(sup_congr rfl h₂).trans (sup_const h₁ _)

@[simp] lemma distortion_top (I : box ι) : distortion (⊤ : prepartition I) = I.distortion :=
sup_singleton

@[simp] lemma distortion_bot (I : box ι) : distortion (⊥ : prepartition I) = 0 := sup_empty

end distortion

/-- A prepartition `π` of `I` is a partition if the boxes of `π` cover the whole `I`. -/
def is_partition (π : prepartition I) := ∀ x ∈ I, ∃ J ∈ π, x ∈ J

lemma is_partition_iff_Union_eq {π : prepartition I} : π.is_partition ↔ π.Union = I :=
by simp_rw [is_partition, set.subset.antisymm_iff, π.Union_subset, true_and, set.subset_def,
  mem_Union, box.mem_coe]

@[simp] lemma is_partition_single_iff (h : J ≤ I) : is_partition (single I J h) ↔ J = I :=
by simp [is_partition_iff_Union_eq]

lemma is_partition_top (I : box ι) : is_partition (⊤ : prepartition I) :=
λ x hx, ⟨I, mem_top.2 rfl, hx⟩

namespace is_partition

variables {π}

lemma Union_eq (h : π.is_partition) : π.Union = I := is_partition_iff_Union_eq.1 h

lemma Union_subset (h : π.is_partition) (π₁ : prepartition I) : π₁.Union ⊆ π.Union :=
h.Union_eq.symm ▸ π₁.Union_subset

protected lemma exists_unique (h : π.is_partition) (hx : x ∈ I) :
  ∃! J ∈ π, x ∈ J :=
begin
  rcases h x hx with ⟨J, h, hx⟩,
  exact exists_unique.intro2 J h hx (λ J' h' hx', π.eq_of_mem_of_mem h' h hx' hx),
end

lemma nonempty_boxes (h : π.is_partition) : π.boxes.nonempty :=
let ⟨J, hJ, _⟩ := h _ I.upper_mem in ⟨J, hJ⟩

lemma eq_of_boxes_subset (h₁ : π₁.is_partition) (h₂ : π₁.boxes ⊆ π₂.boxes) : π₁ = π₂ :=
eq_of_boxes_subset_Union_superset h₂ $ h₁.Union_subset _

lemma le_iff (h : π₂.is_partition) :
  π₁ ≤ π₂ ↔ ∀ (J ∈ π₁) (J' ∈ π₂), (J ∩ J' : set (ι → ℝ)).nonempty → J ≤ J' :=
le_iff_nonempty_imp_le_and_Union_subset.trans $ and_iff_left $ h.Union_subset _

protected lemma bUnion (h : is_partition π) (hi : ∀ J ∈ π, is_partition (πi J)) :
  is_partition (π.bUnion πi) :=
λ x hx, let ⟨J, hJ, hxi⟩ := h x hx, ⟨Ji, hJi, hx⟩ := hi J hJ x hxi in
⟨Ji, π.mem_bUnion.2 ⟨J, hJ, hJi⟩, hx⟩

protected lemma restrict (h : is_partition π) (hJ : J ≤ I) : is_partition (π.restrict J) :=
is_partition_iff_Union_eq.2 $ by simp [h.Union_eq, hJ]

protected lemma inf (h₁ : is_partition π₁) (h₂ : is_partition π₂) :
  is_partition (π₁ ⊓ π₂) :=
is_partition_iff_Union_eq.2 $ by simp [h₁.Union_eq, h₂.Union_eq]

end is_partition

lemma Union_bUnion_partition (h : ∀ J ∈ π, (πi J).is_partition) : (π.bUnion πi).Union = π.Union :=
(Union_bUnion _ _).trans $ Union_congr id surjective_id $ λ J, Union_congr id surjective_id $ λ hJ,
  (h J hJ).Union_eq

lemma is_partition_disj_union_of_eq_diff (h : π₂.Union = I \ π₁.Union) :
  is_partition (π₁.disj_union π₂ (h.symm ▸ disjoint_diff)) :=
is_partition_iff_Union_eq.2 $ (Union_disj_union _).trans $ by simp [h, π₁.Union_subset]

end prepartition

end box_integral

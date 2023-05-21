/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.box_integral.partition.basic

/-!
# Tagged partitions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A tagged (pre)partition is a (pre)partition `π` enriched with a tagged point for each box of
‵π`. For simplicity we require that the function `box_integral.tagged_prepartition.tag` is defined
on all boxes `J : box ι` but use its values only on boxes of the partition. Given `π :
box_integral.tagged_partition I`, we require that each `box_integral.tagged_partition π J` belongs
to `box_integral.box.Icc I`. If for every `J ∈ π`, `π.tag J` belongs to `J.Icc`, then `π` is called
a *Henstock* partition. We do not include this assumption into the definition of a tagged
(pre)partition because McShane integral is defined as a limit along tagged partitions without this
requirement.

### Tags

rectangular box, box partition
-/

noncomputable theory
open_locale classical ennreal nnreal
open set function

namespace box_integral

variables {ι : Type*}

/-- A tagged prepartition is a prepartition enriched with a tagged point for each box of the
prepartition. For simiplicity we require that `tag` is defined for all boxes in `ι → ℝ` but
we will use onle the values of `tag` on the boxes of the partition. -/
structure tagged_prepartition (I : box ι) extends prepartition I :=
(tag : box ι → ι → ℝ)
(tag_mem_Icc : ∀ J, tag J ∈ I.Icc)

namespace tagged_prepartition

variables {I J J₁ J₂ : box ι} (π : tagged_prepartition I) {x : ι → ℝ}

instance : has_mem (box ι) (tagged_prepartition I) := ⟨λ J π, J ∈ π.boxes⟩

@[simp] lemma mem_to_prepartition {π : tagged_prepartition I} :
  J ∈ π.to_prepartition ↔ J ∈ π := iff.rfl

@[simp] lemma mem_mk (π : prepartition I) (f h) :
  J ∈ mk π f h ↔ J ∈ π := iff.rfl

/-- Union of all boxes of a tagged prepartition. -/
def Union : set (ι → ℝ) := π.to_prepartition.Union

lemma Union_def : π.Union = ⋃ J ∈ π, ↑J := rfl

@[simp] lemma Union_mk (π : prepartition I) (f h) : (mk π f h).Union = π.Union := rfl

@[simp] lemma Union_to_prepartition : π.to_prepartition.Union = π.Union := rfl

@[simp] lemma mem_Union : x ∈ π.Union ↔ ∃ J ∈ π, x ∈ J := set.mem_Union₂

lemma subset_Union (h : J ∈ π) : ↑J ⊆ π.Union := subset_bUnion_of_mem h

lemma Union_subset : π.Union ⊆ I := Union₂_subset π.le_of_mem'

/-- A tagged prepartition is a partition if it covers the whole box. -/
def is_partition := π.to_prepartition.is_partition

lemma is_partition_iff_Union_eq : is_partition π ↔ π.Union = I :=
prepartition.is_partition_iff_Union_eq

/-- The tagged partition made of boxes of `π` that satisfy predicate `p`. -/
@[simps { fully_applied := ff }] def filter (p : box ι → Prop) : tagged_prepartition I :=
⟨π.1.filter p, π.2, π.3⟩

@[simp] lemma mem_filter {p : box ι → Prop} : J ∈ π.filter p ↔ J ∈ π ∧ p J :=
finset.mem_filter

@[simp] lemma Union_filter_not (π : tagged_prepartition I) (p : box ι → Prop) :
  (π.filter (λ J, ¬p J)).Union = π.Union \ (π.filter p).Union :=
π.to_prepartition.Union_filter_not p

end tagged_prepartition

namespace prepartition

variables {I J : box ι}

/-- Given a partition `π` of `I : box_integral.box ι` and a collection of tagged partitions
`πi J` of all boxes `J ∈ π`, returns the tagged partition of `I` into all the boxes of `πi J`
with tags coming from `(πi J).tag`. -/
def bUnion_tagged (π : prepartition I) (πi : Π J, tagged_prepartition J) :
  tagged_prepartition I :=
{ to_prepartition := π.bUnion (λ J, (πi J).to_prepartition),
  tag := λ J, (πi (π.bUnion_index (λ J, (πi J).to_prepartition) J)).tag J,
  tag_mem_Icc := λ J, box.le_iff_Icc.1 (π.bUnion_index_le _ _) ((πi _).tag_mem_Icc _) }

@[simp] lemma mem_bUnion_tagged (π : prepartition I) {πi : Π J, tagged_prepartition J} :
  J ∈ π.bUnion_tagged πi ↔ ∃ J' ∈ π, J ∈ πi J' :=
π.mem_bUnion

lemma tag_bUnion_tagged (π : prepartition I) {πi : Π J, tagged_prepartition J} (hJ : J ∈ π) {J'}
  (hJ' : J' ∈ πi J) :
  (π.bUnion_tagged πi).tag J' = (πi J).tag J' :=
begin
  have : J' ∈ π.bUnion_tagged πi, from π.mem_bUnion.2 ⟨J, hJ, hJ'⟩,
  obtain rfl := π.bUnion_index_of_mem hJ hJ',
  refl
end

@[simp] lemma Union_bUnion_tagged (π : prepartition I) (πi : Π J, tagged_prepartition J) :
  (π.bUnion_tagged πi).Union = ⋃ J ∈ π, (πi J).Union :=
Union_bUnion _ _

lemma forall_bUnion_tagged (p : (ι → ℝ) → box ι → Prop) (π : prepartition I)
  (πi : Π J, tagged_prepartition J) :
  (∀ J ∈ π.bUnion_tagged πi, p ((π.bUnion_tagged πi).tag J) J) ↔
    ∀ (J ∈ π) (J' ∈ πi J), p ((πi J).tag J') J' :=
begin
  simp only [bex_imp_distrib, mem_bUnion_tagged],
  refine ⟨λ H J hJ J' hJ', _, λ H J' J hJ hJ', _⟩,
  { rw ← π.tag_bUnion_tagged hJ hJ', exact H J' J hJ hJ' },
  { rw π.tag_bUnion_tagged hJ hJ', exact H J hJ J' hJ' }
end

lemma is_partition.bUnion_tagged {π : prepartition I} (h : is_partition π)
  {πi : Π J, tagged_prepartition J} (hi : ∀ J ∈ π, (πi J).is_partition) :
  (π.bUnion_tagged πi).is_partition :=
h.bUnion hi

end prepartition

namespace tagged_prepartition

variables {I J : box ι} {π π₁ π₂ : tagged_prepartition I} {x : ι → ℝ}

/-- Given a tagged partition `π` of `I` and a (not tagged) partition `πi J hJ` of each `J ∈ π`,
returns the tagged partition of `I` into all the boxes of all `πi J hJ`. The tag of a box `J`
is defined to be the `π.tag` of the box of the partition `π` that includes `J`.

Note that usually the result is not a Henstock partition. -/
@[simps tag { fully_applied := ff }]
def bUnion_prepartition (π : tagged_prepartition I) (πi : Π J, prepartition J) :
  tagged_prepartition I :=
{ to_prepartition := π.to_prepartition.bUnion πi,
  tag := λ J, π.tag (π.to_prepartition.bUnion_index πi J),
  tag_mem_Icc := λ J, π.tag_mem_Icc _ }

lemma is_partition.bUnion_prepartition {π : tagged_prepartition I} (h : is_partition π)
  {πi : Π J, prepartition J} (hi : ∀ J ∈ π, (πi J).is_partition) :
  (π.bUnion_prepartition πi).is_partition :=
h.bUnion hi

/-- Given two partitions `π₁` and `π₁`, one of them tagged and the other is not, returns the tagged
partition with `to_partition = π₁.to_partition ⊓ π₂` and tags coming from `π₁`.

Note that usually the result is not a Henstock partition. -/
def inf_prepartition (π : tagged_prepartition I) (π' : prepartition I) :
  tagged_prepartition I :=
π.bUnion_prepartition $ λ J, π'.restrict J

@[simp] lemma inf_prepartition_to_prepartition (π : tagged_prepartition I) (π' : prepartition I) :
  (π.inf_prepartition π').to_prepartition = π.to_prepartition ⊓ π' := rfl

lemma mem_inf_prepartition_comm :
  J ∈ π₁.inf_prepartition π₂.to_prepartition ↔ J ∈ π₂.inf_prepartition π₁.to_prepartition :=
by simp only [← mem_to_prepartition, inf_prepartition_to_prepartition, inf_comm]

lemma is_partition.inf_prepartition (h₁ : π₁.is_partition) {π₂ : prepartition I}
  (h₂ : π₂.is_partition) :
  (π₁.inf_prepartition π₂).is_partition :=
h₁.inf h₂

open metric

/-- A tagged partition is said to be a Henstock partition if for each `J ∈ π`, the tag of `J`
belongs to `J.Icc`. -/
def is_Henstock (π : tagged_prepartition I) : Prop := ∀ J ∈ π, π.tag J ∈ J.Icc

@[simp] lemma is_Henstock_bUnion_tagged
  {π : prepartition I} {πi : Π J, tagged_prepartition J} :
  is_Henstock (π.bUnion_tagged πi) ↔ ∀ J ∈ π, (πi J).is_Henstock :=
π.forall_bUnion_tagged (λ x J, x ∈ J.Icc) πi

/-- In a Henstock prepartition, there are at most `2 ^ fintype.card ι` boxes with a given tag. -/
lemma is_Henstock.card_filter_tag_eq_le [fintype ι] (h : π.is_Henstock) (x : ι → ℝ) :
  (π.boxes.filter (λ J, π.tag J = x)).card ≤ 2 ^ fintype.card ι :=
calc (π.boxes.filter (λ J, π.tag J = x)).card ≤ (π.boxes.filter (λ J : box ι, x ∈ J.Icc)).card :
  begin
    refine finset.card_le_of_subset (λ J hJ, _),
    rw finset.mem_filter at hJ ⊢, rcases hJ with ⟨hJ, rfl⟩,
    exact ⟨hJ, h J hJ⟩
  end
... ≤ 2 ^ fintype.card ι : π.to_prepartition.card_filter_mem_Icc_le x

/-- A tagged partition `π` is subordinate to `r : (ι → ℝ) → ℝ` if each box `J ∈ π` is included in
the closed ball with center `π.tag J` and radius `r (π.tag J)`. -/
def is_subordinate [fintype ι] (π : tagged_prepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) : Prop :=
∀ J ∈ π, (J : _).Icc ⊆ closed_ball (π.tag J) (r $ π.tag J)

variables {r r₁ r₂ : (ι → ℝ) → Ioi (0 : ℝ)}

@[simp] lemma is_subordinate_bUnion_tagged [fintype ι]
  {π : prepartition I} {πi : Π J, tagged_prepartition J} :
  is_subordinate (π.bUnion_tagged πi) r ↔ ∀ J ∈ π, (πi J).is_subordinate r :=
π.forall_bUnion_tagged (λ x J, J.Icc ⊆ closed_ball x (r x)) πi

lemma is_subordinate.bUnion_prepartition [fintype ι] (h : is_subordinate π r)
  (πi : Π J, prepartition J) :
  is_subordinate (π.bUnion_prepartition πi) r :=
λ J hJ, subset.trans (box.le_iff_Icc.1 $ π.to_prepartition.le_bUnion_index hJ) $
  h _ $ π.to_prepartition.bUnion_index_mem hJ

lemma is_subordinate.inf_prepartition [fintype ι] (h : is_subordinate π r) (π' : prepartition I) :
  is_subordinate (π.inf_prepartition π') r :=
h.bUnion_prepartition _

lemma is_subordinate.mono' [fintype ι] {π : tagged_prepartition I}
  (hr₁ : π.is_subordinate r₁) (h : ∀ J ∈ π, r₁ (π.tag J) ≤ r₂ (π.tag J)) :
  π.is_subordinate r₂ :=
λ J hJ x hx, closed_ball_subset_closed_ball (h _ hJ) (hr₁ _ hJ hx)

lemma is_subordinate.mono [fintype ι] {π : tagged_prepartition I}
  (hr₁ : π.is_subordinate r₁) (h : ∀ x ∈ I.Icc, r₁ x ≤ r₂ x) :
  π.is_subordinate r₂ :=
hr₁.mono' $ λ J _, h _ $ π.tag_mem_Icc J

lemma is_subordinate.diam_le [fintype ι] {π : tagged_prepartition I}
  (h : π.is_subordinate r) (hJ : J ∈ π.boxes) :
  diam J.Icc ≤ 2 * r (π.tag J) :=
calc diam J.Icc ≤ diam (closed_ball (π.tag J) (r $ π.tag J)) :
  diam_mono (h J hJ) bounded_closed_ball
            ... ≤ 2 * r (π.tag J) : diam_closed_ball (le_of_lt (r _).2)

/-- Tagged prepartition with single box and prescribed tag. -/
@[simps { fully_applied := ff }]
def single (I J : box ι) (hJ : J ≤ I) (x : ι → ℝ) (h : x ∈ I.Icc) : tagged_prepartition I :=
⟨prepartition.single I J hJ, λ J, x, λ J, h⟩

@[simp] lemma mem_single {J'} (hJ : J ≤ I) (h : x ∈ I.Icc) : J' ∈ single I J hJ x h ↔ J' = J :=
finset.mem_singleton

instance (I : box ι) : inhabited (tagged_prepartition I) :=
⟨single I I le_rfl I.upper I.upper_mem_Icc⟩

lemma is_partition_single_iff (hJ : J ≤ I) (h : x ∈ I.Icc) :
  (single I J hJ x h).is_partition ↔ J = I :=
prepartition.is_partition_single_iff hJ

lemma is_partition_single (h : x ∈ I.Icc) : (single I I le_rfl x h).is_partition :=
prepartition.is_partition_top I

lemma forall_mem_single (p : (ι → ℝ) → (box ι) → Prop) (hJ : J ≤ I) (h : x ∈ I.Icc) :
  (∀ J' ∈ single I J hJ x h, p ((single I J hJ x h).tag J') J') ↔ p x J :=
by simp

@[simp] lemma is_Henstock_single_iff (hJ : J ≤ I) (h : x ∈ I.Icc) :
  is_Henstock (single I J hJ x h) ↔ x ∈ J.Icc :=
forall_mem_single (λ x J, x ∈ J.Icc) hJ h

@[simp] lemma is_Henstock_single (h : x ∈ I.Icc) : is_Henstock (single I I le_rfl x h) :=
(is_Henstock_single_iff (le_refl I) h).2 h

@[simp] lemma is_subordinate_single [fintype ι] (hJ : J ≤ I) (h : x ∈ I.Icc) :
  is_subordinate (single I J hJ x h) r ↔ J.Icc ⊆ closed_ball x (r x) :=
forall_mem_single (λ x J, J.Icc ⊆ closed_ball x (r x)) hJ h

@[simp] lemma Union_single (hJ : J ≤ I) (h : x ∈ I.Icc) :
  (single I J hJ x h).Union = J :=
prepartition.Union_single hJ

/-- Union of two tagged prepartitions with disjoint unions of boxes. -/
def disj_union (π₁ π₂ : tagged_prepartition I) (h : disjoint π₁.Union π₂.Union) :
  tagged_prepartition I :=
{ to_prepartition := π₁.to_prepartition.disj_union π₂.to_prepartition h,
  tag := π₁.boxes.piecewise π₁.tag π₂.tag,
  tag_mem_Icc := λ J, by { dunfold finset.piecewise, split_ifs,
    exacts [π₁.tag_mem_Icc J, π₂.tag_mem_Icc J]  } }

@[simp] lemma disj_union_boxes (h : disjoint π₁.Union π₂.Union) :
  (π₁.disj_union π₂ h).boxes = π₁.boxes ∪ π₂.boxes := rfl

@[simp] lemma mem_disj_union (h : disjoint π₁.Union π₂.Union) :
  J ∈ π₁.disj_union π₂ h ↔ J ∈ π₁ ∨ J ∈ π₂ :=
finset.mem_union

@[simp] lemma Union_disj_union (h : disjoint π₁.Union π₂.Union) :
  (π₁.disj_union π₂ h).Union = π₁.Union ∪ π₂.Union :=
prepartition.Union_disj_union _

lemma disj_union_tag_of_mem_left (h : disjoint π₁.Union π₂.Union) (hJ : J ∈ π₁) :
  (π₁.disj_union π₂ h).tag J = π₁.tag J :=
dif_pos hJ

lemma disj_union_tag_of_mem_right (h : disjoint π₁.Union π₂.Union) (hJ : J ∈ π₂) :
  (π₁.disj_union π₂ h).tag J = π₂.tag J :=
dif_neg $ λ h₁, h.le_bot ⟨π₁.subset_Union h₁ J.upper_mem, π₂.subset_Union hJ J.upper_mem⟩

lemma is_subordinate.disj_union [fintype ι] (h₁ : is_subordinate π₁ r)
  (h₂ : is_subordinate π₂ r) (h : disjoint π₁.Union π₂.Union) :
  is_subordinate (π₁.disj_union π₂ h) r :=
begin
  refine λ J hJ, (finset.mem_union.1 hJ).elim (λ hJ, _) (λ hJ, _),
  { rw disj_union_tag_of_mem_left _ hJ, exact h₁ _ hJ },
  { rw disj_union_tag_of_mem_right _ hJ, exact h₂ _ hJ }
end

lemma is_Henstock.disj_union (h₁ : is_Henstock π₁) (h₂ : is_Henstock π₂)
  (h : disjoint π₁.Union π₂.Union) :
  is_Henstock (π₁.disj_union π₂ h) :=
begin
  refine λ J hJ, (finset.mem_union.1 hJ).elim (λ hJ, _) (λ hJ, _),
  { rw disj_union_tag_of_mem_left _ hJ, exact h₁ _ hJ },
  { rw disj_union_tag_of_mem_right _ hJ, exact h₂ _ hJ }
end

/-- If `I ≤ J`, then every tagged prepartition of `I` is a tagged prepartition of `J`. -/
def embed_box (I J : box ι) (h : I ≤ J) :
  tagged_prepartition I ↪ tagged_prepartition J :=
{ to_fun := λ π,
  { le_of_mem' := λ J' hJ', (π.le_of_mem' J' hJ').trans h,
    tag_mem_Icc := λ J, box.le_iff_Icc.1 h (π.tag_mem_Icc J),
    .. π },
  inj' := by { rintro ⟨⟨b₁, h₁le, h₁d⟩, t₁, ht₁⟩ ⟨⟨b₂, h₂le, h₂d⟩, t₂, ht₂⟩ H, simpa using H } }

section distortion

variables [fintype ι] (π)
open finset

/-- The distortion of a tagged prepartition is the maximum of distortions of its boxes. -/
def distortion : ℝ≥0 := π.to_prepartition.distortion

lemma distortion_le_of_mem (h : J ∈ π) : J.distortion ≤ π.distortion :=
le_sup h

lemma distortion_le_iff {c : ℝ≥0} : π.distortion ≤ c ↔ ∀ J ∈ π, box.distortion J ≤ c :=
finset.sup_le_iff

@[simp] lemma _root_.box_integral.prepartition.distortion_bUnion_tagged (π : prepartition I)
  (πi : Π J, tagged_prepartition J) :
  (π.bUnion_tagged πi).distortion = π.boxes.sup (λ J, (πi J).distortion) :=
sup_bUnion _ _

@[simp] lemma distortion_bUnion_prepartition (π : tagged_prepartition I)
  (πi : Π J, prepartition J) :
  (π.bUnion_prepartition πi).distortion = π.boxes.sup (λ J, (πi J).distortion) :=
sup_bUnion _ _

@[simp] lemma distortion_disj_union (h : disjoint π₁.Union π₂.Union) :
  (π₁.disj_union π₂ h).distortion = max π₁.distortion π₂.distortion :=
sup_union

lemma distortion_of_const {c} (h₁ : π.boxes.nonempty) (h₂ : ∀ J ∈ π, box.distortion J = c) :
  π.distortion = c :=
(sup_congr rfl h₂).trans (sup_const h₁ _)

@[simp] lemma distortion_single (hJ : J ≤ I) (h : x ∈ I.Icc) :
  distortion (single I J hJ x h) = J.distortion :=
sup_singleton

lemma distortion_filter_le (p : box ι → Prop) : (π.filter p).distortion ≤ π.distortion :=
sup_mono (filter_subset _ _)

end distortion

end tagged_prepartition

end box_integral

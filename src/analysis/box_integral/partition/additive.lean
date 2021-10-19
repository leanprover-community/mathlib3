/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.box_integral.partition.split
import analysis.normed_space.operator_norm
import data.set.intervals.proj_Icc

/-!
# Box additive functions

We say that a function `f : box ι → M` from boxes in `ℝⁿ` to a commutative additive monoid `M` is
*box additive* on subboxes of `I₀ : with_top (box ι)` if for any box `J`, `↑J ≤ I₀`, and a partition
`π` of `J`, `f J = ∑ J' in π.boxes, f J'`. We use `I₀ : with_top (box ι)` instead of `I₀ : box ι` to
use the same definition for functions box additive on subboxes of a box and for functions box
additive on all boxes.

Examples of box-additive functions include the measure of a box and the integral of a fixed
integrable function over a box.

In this file we define box-additive functions and prove that a function such that
`f J = f (J ∩ {x | x i < y}) + f (J ∩ {x | y ≤ x i})` is box-additive.

### Tags

rectangular box, additive function
-/

noncomputable theory
open_locale classical big_operators
open function set

namespace box_integral

variables {ι M : Type*} {n : ℕ}

/-- A function on `box ι` is called box additive if for every box `J` and a partition `π` of `J`
we have `f J = ∑ Ji in π.boxes, f Ji`. A function is called box additive on subboxes of `I : box ι`
if the same property holds for `J ≤ I`. We formalize these two notions in the same definition
using `I : with_bot (box ι)`: the value `I = ⊤` corresponds to functions box additive on the whole
space.  -/
structure box_additive_map (ι M : Type*) [add_comm_monoid M] (I : with_top (box ι)) :=
(to_fun : box ι → M)
(sum_partition_boxes' : ∀ J : box ι, ↑J ≤ I → ∀ π : prepartition J, π.is_partition →
  ∑ Ji in π.boxes, to_fun Ji = to_fun J)

localized "notation ι ` →ᵇᵃ `:25 M := box_integral.box_additive_map ι M ⊤" in box_integral
localized "notation ι ` →ᵇᵃ[`:25 I `] ` M := box_integral.box_additive_map ι M I" in box_integral

namespace box_additive_map

open box prepartition finset

variables {N : Type*} [add_comm_monoid M] [add_comm_monoid N] {I₀ : with_top (box ι)}
  {I J : box ι} {i : ι}

instance : has_coe_to_fun (ι →ᵇᵃ[I₀] M) := ⟨_, to_fun⟩

initialize_simps_projections box_integral.box_additive_map (to_fun → apply)

@[simp] lemma to_fun_eq_coe (f : ι →ᵇᵃ[I₀] M) : f.to_fun = f := rfl

@[simp] lemma coe_mk (f h) : ⇑(mk f h : ι →ᵇᵃ[I₀] M) = f := rfl

lemma coe_injective : injective (λ (f : ι →ᵇᵃ[I₀] M) x, f x) :=
by { rintro ⟨f, hf⟩ ⟨g, hg⟩ (rfl : f = g), refl }

@[simp] lemma coe_inj {f g : ι →ᵇᵃ[I₀] M} : (f : box ι → M) = g ↔ f = g :=
coe_injective.eq_iff

lemma sum_partition_boxes (f : ι →ᵇᵃ[I₀] M) (hI : ↑I ≤ I₀) {π : prepartition I}
  (h : π.is_partition) :
  ∑ J in π.boxes, f J = f I :=
f.sum_partition_boxes' I hI π h

@[simps { fully_applied := ff }] instance : has_zero (ι →ᵇᵃ[I₀] M) :=
⟨⟨0, λ I hI π hπ, sum_const_zero⟩⟩

instance : inhabited (ι →ᵇᵃ[I₀] M) := ⟨0⟩

instance : has_add (ι →ᵇᵃ[I₀] M) :=
⟨λ f g, ⟨f + g, λ I hI π hπ,
  by simp only [pi.add_apply, sum_add_distrib, sum_partition_boxes _ hI hπ]⟩⟩

instance : add_comm_monoid (ι →ᵇᵃ[I₀] M) :=
function.injective.add_comm_monoid _ coe_injective rfl (λ _ _, rfl)

@[simp] lemma map_split_add (f : ι →ᵇᵃ[I₀] M) (hI : ↑I ≤ I₀) (i : ι) (x : ℝ) :
  (I.split_lower i x).elim 0 f + (I.split_upper i x).elim 0 f = f I :=
by rw [← f.sum_partition_boxes hI (is_partition_split I i x), sum_split_boxes]

/-- If `f` is box-additive on subboxes of `I₀`, then it is box-additive on subboxes of any
`I ≤ I₀`. -/
@[simps] def restrict (f : ι →ᵇᵃ[I₀] M) (I : with_top (box ι)) (hI : I ≤ I₀) : ι →ᵇᵃ[I] M :=
⟨f, λ J hJ, f.2 J (hJ.trans hI)⟩

/-- If `f : box ι → M` is box additive on partitions of the form `split I i x`, then it is box
additive. -/
def of_map_split_add [fintype ι] (f : box ι → M) (I₀ : with_top (box ι))
  (hf : ∀ I : box ι, ↑I ≤ I₀ → ∀ {i x}, x ∈ Ioo (I.lower i) (I.upper i) →
    (I.split_lower i x).elim 0 f + (I.split_upper i x).elim 0 f = f I) :
  ι →ᵇᵃ[I₀] M :=
begin
  refine ⟨f, _⟩,
  replace hf : ∀ I : box ι, ↑I ≤ I₀ → ∀ s, ∑ J in (split_many I s).boxes, f J = f I,
  { intros I hI s,
    induction s using finset.induction_on with a s ha ihs, { simp },
    rw [split_many_insert, inf_split, ← ihs, bUnion_boxes, sum_bUnion_boxes],
    refine finset.sum_congr rfl (λ J' hJ', _),
    by_cases h : a.2 ∈ Ioo (J'.lower a.1) (J'.upper a.1),
    { rw sum_split_boxes,
      exact hf _ ((with_top.coe_le_coe.2 $ le_of_mem _ hJ').trans hI) h },
    { rw [split_of_not_mem_Ioo h, top_boxes, finset.sum_singleton] } },
  intros I hI π hπ,
  have Hle : ∀ J ∈ π, ↑J ≤ I₀, from λ J hJ, (with_top.coe_le_coe.2 $ π.le_of_mem hJ).trans hI,
  rcases hπ.exists_split_many_le with ⟨s, hs⟩,
  rw [← hf _ hI, ← inf_of_le_right hs, inf_split_many, bUnion_boxes, sum_bUnion_boxes],
  exact finset.sum_congr rfl (λ J hJ, (hf _ (Hle _ hJ) _).symm)
end

/-- If `g : M → N` is an additive map and `f` is a box additive map, then `g ∘ f` is a box additive
map. -/
@[simps { fully_applied := ff }] def map (f : ι →ᵇᵃ[I₀] M) (g : M →+ N) :
  ι →ᵇᵃ[I₀] N :=
{ to_fun := g ∘ f,
  sum_partition_boxes' := λ I hI π hπ, by rw [← g.map_sum, f.sum_partition_boxes hI hπ] }

/-- If `f` is a box additive function on subboxes of `I` and `π₁`, `π₂` are two prepartitions of
`I` that cover the same part of `I`, then `∑ J in π₁.boxes, f J = ∑ J in π₂.boxes, f J`. -/
lemma sum_boxes_congr [fintype ι] (f : ι →ᵇᵃ[I₀] M) (hI : ↑I ≤ I₀) {π₁ π₂ : prepartition I}
  (h : π₁.Union = π₂.Union) :
  ∑ J in π₁.boxes, f J = ∑ J in π₂.boxes, f J :=
begin
  rcases exists_split_many_inf_eq_filter_of_finite {π₁, π₂} ((finite_singleton _).insert _)
    with ⟨s, hs⟩, simp only [inf_split_many] at hs,
  rcases ⟨hs _ (or.inl rfl), hs _ (or.inr rfl)⟩ with ⟨h₁, h₂⟩, clear hs,
  rw h at h₁,
  calc ∑ J in π₁.boxes, f J = ∑ J in π₁.boxes, ∑ J' in (split_many J s).boxes, f J' :
    finset.sum_congr rfl (λ J hJ, (f.sum_partition_boxes _ (is_partition_split_many _ _)).symm)
  ... = ∑ J in (π₁.bUnion (λ J, split_many J s)).boxes, f J   : (sum_bUnion_boxes _ _ _).symm
  ... = ∑ J in (π₂.bUnion (λ J, split_many J s)).boxes, f J   : by rw [h₁, h₂]
  ... = ∑ J in π₂.boxes, ∑ J' in (split_many J s).boxes, f J' : sum_bUnion_boxes _ _ _
  ... = ∑ J in π₂.boxes, f J :
    finset.sum_congr rfl (λ J hJ, (f.sum_partition_boxes _ (is_partition_split_many _ _))),
  exacts [(with_top.coe_le_coe.2 $ π₁.le_of_mem hJ).trans hI,
    (with_top.coe_le_coe.2 $ π₂.le_of_mem hJ).trans hI]
end

section to_smul

variables {E : Type*} [normed_group E] [normed_space ℝ E]

/-- If `f` is a box-additive map, then so is the map sending `I` to the scalar multiplication
by `f I` as a continuous linear map from `E` to itself. -/
def to_smul (f : ι →ᵇᵃ[I₀] ℝ) : ι →ᵇᵃ[I₀] (E →L[ℝ] E) :=
f.map (continuous_linear_map.lsmul ℝ ℝ).to_linear_map.to_add_monoid_hom

@[simp] lemma to_smul_apply (f : ι →ᵇᵃ[I₀] ℝ) (I : box ι) (x : E) : f.to_smul I x = f I • x := rfl

end to_smul

/-- Given a box `I₀` in `ℝⁿ⁺¹`, `f x : box (fin n) → G` is a family of functions indexed by a real
`x` and for `x ∈ [I₀.lower i, I₀.upper i]`, `f x` is box-additive on subboxes of the `i`-th face of
`I₀`, then `λ J, f (J.upper i) (J.face i) - f (J.lower i) (J.face i)` is box-additive on subboxes of
`I₀`. -/
@[simps] def {u} upper_sub_lower {G : Type u} [add_comm_group G]
  (I₀ : box (fin (n + 1))) (i : fin (n + 1)) (f : ℝ → box (fin n) → G)
  (fb : Icc (I₀.lower i) (I₀.upper i) → fin n →ᵇᵃ[I₀.face i] G)
  (hf : ∀ x (hx : x ∈ Icc (I₀.lower i) (I₀.upper i)) J, f x J = fb ⟨x, hx⟩ J) :
  fin (n + 1) →ᵇᵃ[I₀] G :=
of_map_split_add
  (λ J : box (fin (n + 1)), f (J.upper i) (J.face i) - f (J.lower i) (J.face i)) I₀
  begin
    intros J hJ j,
    rw with_top.coe_le_coe at hJ,
    refine i.succ_above_cases _ _ j,
    { intros x hx,
      simp only [box.split_lower_def hx, box.split_upper_def hx, update_same, 
        ← with_bot.some_eq_coe, option.elim, box.face, (∘), update_noteq (fin.succ_above_ne _ _)],
      abel },
    { clear j, intros j x hx,
      have : (J.face i : with_top (box (fin n))) ≤ I₀.face i,
        from with_top.coe_le_coe.2 (face_mono hJ i),
      rw [le_iff_Icc, @box.Icc_eq_pi _ I₀] at hJ,
      rw [hf _ (hJ J.upper_mem_Icc _ trivial), hf _ (hJ J.lower_mem_Icc _ trivial),
        ← (fb _).map_split_add this j x, ← (fb _).map_split_add this j x],
      have hx' : x ∈ Ioo ((J.face i).lower j) ((J.face i).upper j) := hx,
      simp only [box.split_lower_def hx, box.split_upper_def hx,
        box.split_lower_def hx', box.split_upper_def hx',
        ← with_bot.some_eq_coe, option.elim, box.face_mk,
        update_noteq (fin.succ_above_ne _ _).symm, sub_add_comm,
        update_comp_eq_of_injective _ i.succ_above.injective j x, ← hf],
      simp only [box.face] }
  end

end box_additive_map

end box_integral

/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.finsupp
import algebra.monoid_algebra.support
import algebra.direct_sum.internal
import ring_theory.graded_algebra.basic

/-!
# Internal grading of an `add_monoid_algebra`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we show that an `add_monoid_algebra` has an internal direct sum structure.

## Main results

* `add_monoid_algebra.grade_by R f i`: the `i`th grade of an `add_monoid_algebra R M` given by the
  degree function `f`.
* `add_monoid_algebra.grade R i`: the `i`th grade of an `add_monoid_algebra R M` when the degree
  function is the identity.
* `add_monoid_algebra.grade_by.graded_algebra`: `add_monoid_algebra` is an algebra graded by
  `add_monoid_algebra.grade_by`.
* `add_monoid_algebra.grade.graded_algebra`: `add_monoid_algebra` is an algebra graded by
  `add_monoid_algebra.grade`.
* `add_monoid_algebra.grade_by.is_internal`: propositionally, the statement that
  `add_monoid_algebra.grade_by` defines an internal graded structure.
* `add_monoid_algebra.grade.is_internal`: propositionally, the statement that
  `add_monoid_algebra.grade` defines an internal graded structure when the degree function
  is the identity.
-/

noncomputable theory

namespace add_monoid_algebra
variables {M : Type*} {ι : Type*} {R : Type*} [decidable_eq M]

section
variables (R) [comm_semiring R]

/-- The submodule corresponding to each grade given by the degree function `f`. -/
abbreviation grade_by (f : M → ι) (i : ι) : submodule R (add_monoid_algebra R M) :=
{ carrier := {a | ∀ m, m ∈ a.support → f m = i },
  zero_mem' := set.empty_subset _,
  add_mem' := λ a b ha hb m h,
    or.rec_on (finset.mem_union.mp (finsupp.support_add h)) (ha m) (hb m),
  smul_mem' := λ a m h, set.subset.trans finsupp.support_smul h }

/-- The submodule corresponding to each grade. -/
abbreviation grade (m : M) : submodule R (add_monoid_algebra R M) := grade_by R id m

lemma grade_by_id : grade_by R (id : M → M) = grade R := by refl

lemma mem_grade_by_iff (f : M → ι) (i : ι) (a : add_monoid_algebra R M) :
  a ∈ grade_by R f i ↔ (a.support : set M) ⊆ f ⁻¹' {i} := by refl

lemma mem_grade_iff (m : M) (a : add_monoid_algebra R M) : a ∈ grade R m ↔ a.support ⊆ {m} :=
begin
  rw [← finset.coe_subset, finset.coe_singleton],
  refl
end

lemma mem_grade_iff' (m : M) (a : add_monoid_algebra R M) :
  a ∈ grade R m ↔
    a ∈ ((finsupp.lsingle m : R →ₗ[R] (M →₀ R)).range : submodule R (add_monoid_algebra R M)) :=
begin
  rw [mem_grade_iff, finsupp.support_subset_singleton'],
  apply exists_congr,
  intros r,
  split; exact eq.symm
end

lemma grade_eq_lsingle_range (m : M) : grade R m = (finsupp.lsingle m : R →ₗ[R] (M →₀ R)).range :=
submodule.ext (mem_grade_iff' R m)

lemma single_mem_grade_by {R} [comm_semiring R] (f : M → ι) (m : M) (r : R) :
  finsupp.single m r ∈ grade_by R f (f m) :=
begin
  intros x hx,
  rw finset.mem_singleton.mp (finsupp.support_single_subset hx),
end

lemma single_mem_grade {R} [comm_semiring R] (i : M) (r : R) : finsupp.single i r ∈ grade R i :=
single_mem_grade_by _ _ _

end

open_locale direct_sum

instance grade_by.graded_monoid [add_monoid M] [add_monoid ι] [comm_semiring R] (f : M →+ ι) :
  set_like.graded_monoid (grade_by R f : ι → submodule R (add_monoid_algebra R M)) :=
{ one_mem := λ m h, begin
    rw one_def at h,
    by_cases H : (1 : R) = (0 : R),
    { rw [H , finsupp.single_zero] at h,
      exfalso,
      exact h },
    { rw [finsupp.support_single_ne_zero _ H, finset.mem_singleton] at h,
      rw [h, add_monoid_hom.map_zero] }
  end,
  mul_mem := λ i j a b ha hb c hc, begin
    set h := support_mul a b hc,
    simp only [finset.mem_bUnion] at h,
    rcases h with ⟨ma, ⟨hma, ⟨mb, ⟨hmb, hmc⟩⟩⟩⟩,
    rw [← ha ma hma, ← hb mb hmb, finset.mem_singleton.mp hmc],
    apply add_monoid_hom.map_add
  end }

instance grade.graded_monoid [add_monoid M] [comm_semiring R] :
  set_like.graded_monoid (grade R : M → submodule R (add_monoid_algebra R M)) :=
by apply grade_by.graded_monoid (add_monoid_hom.id _)

variables {R} [add_monoid M] [decidable_eq ι] [add_monoid ι] [comm_semiring R] (f : M →+ ι)

/-- Auxiliary definition; the canonical grade decomposition, used to provide
`direct_sum.decompose`. -/
def decompose_aux : add_monoid_algebra R M →ₐ[R] ⨁ i : ι, grade_by R f i :=
add_monoid_algebra.lift R M _
{ to_fun := λ m, direct_sum.of (λ i : ι, grade_by R f i) (f m.to_add)
    ⟨finsupp.single m.to_add 1, single_mem_grade_by _ _ _⟩,
  map_one' := direct_sum.of_eq_of_graded_monoid_eq (by congr' 2; try {ext};
    simp only [submodule.mem_to_add_submonoid, to_add_one, add_monoid_hom.map_zero]),
  map_mul' := λ i j, begin
    symmetry,
    convert direct_sum.of_mul_of _ _,
    apply direct_sum.of_eq_of_graded_monoid_eq,
    congr' 2,
    { rw [to_add_mul, add_monoid_hom.map_add] },
    { ext,
      simp only [submodule.mem_to_add_submonoid, add_monoid_hom.map_add, to_add_mul] },
    { exact eq.trans (by rw [one_mul, to_add_mul]) single_mul_single.symm }
  end }

lemma decompose_aux_single (m : M) (r : R) :
  decompose_aux f (finsupp.single m r) =
    direct_sum.of (λ i : ι, grade_by R f i) (f m)
      ⟨finsupp.single m r, single_mem_grade_by _ _ _⟩ :=
begin
  refine (lift_single _ _ _).trans _,
  refine (direct_sum.of_smul _ _ _ _).symm.trans _,
  apply direct_sum.of_eq_of_graded_monoid_eq,
  refine sigma.subtype_ext rfl _,
  refine (finsupp.smul_single' _ _ _).trans _,
  rw mul_one,
  refl,
end

lemma decompose_aux_coe {i : ι} (x : grade_by R f i) :
  decompose_aux f ↑x = direct_sum.of (λ i, grade_by R f i) i x :=
begin
  obtain ⟨x, hx⟩ := x,
  revert hx,
  refine finsupp.induction x _ _,
  { intros hx,
    symmetry,
    exact add_monoid_hom.map_zero _ },
  { intros m b y hmy hb ih hmby,
    have : disjoint (finsupp.single m b).support y.support,
    { simpa only [finsupp.support_single_ne_zero _ hb, finset.disjoint_singleton_left] },
    rw [mem_grade_by_iff, finsupp.support_add_eq this, finset.coe_union,
      set.union_subset_iff] at hmby,
    cases hmby with h1 h2,
    have : f m = i,
    { rwa [finsupp.support_single_ne_zero _ hb, finset.coe_singleton,
        set.singleton_subset_iff] at h1 },
    subst this,
    simp only [alg_hom.map_add, submodule.coe_mk, decompose_aux_single f m],
    let ih' := ih h2,
    dsimp at ih',
    rw [ih', ← add_monoid_hom.map_add],
    apply direct_sum.of_eq_of_graded_monoid_eq,
    congr' 2 }
end

instance grade_by.graded_algebra : graded_algebra (grade_by R f) :=
graded_algebra.of_alg_hom _
  (decompose_aux f)
  (begin
    ext : 2,
    simp only [alg_hom.coe_to_monoid_hom, function.comp_app, alg_hom.coe_comp,
        function.comp.left_id, alg_hom.coe_id, add_monoid_algebra.of_apply, monoid_hom.coe_comp],
    rw [decompose_aux_single, direct_sum.coe_alg_hom_of, subtype.coe_mk],
  end)
  (λ i x, by rw [decompose_aux_coe f x])

-- Lean can't find this later without us repeating it
instance grade_by.decomposition : direct_sum.decomposition (grade_by R f) :=
by apply_instance

@[simp] lemma decompose_aux_eq_decompose :
  ⇑(decompose_aux f : add_monoid_algebra R M →ₐ[R] ⨁ i : ι, grade_by R f i) =
    (direct_sum.decompose (grade_by R f)) := rfl

@[simp] lemma grades_by.decompose_single (m : M) (r : R) :
  direct_sum.decompose (grade_by R f) (finsupp.single m r : add_monoid_algebra R M) =
    direct_sum.of (λ i : ι, grade_by R f i) (f m)
      ⟨finsupp.single m r, single_mem_grade_by _ _ _⟩ :=
decompose_aux_single _ _ _

instance grade.graded_algebra : graded_algebra (grade R : ι → submodule _ _) :=
add_monoid_algebra.grade_by.graded_algebra (add_monoid_hom.id _)

-- Lean can't find this later without us repeating it
instance grade.decomposition : direct_sum.decomposition (grade R : ι → submodule _ _) :=
by apply_instance

@[simp]
lemma grade.decompose_single (i : ι) (r : R) :
  direct_sum.decompose (grade R : ι → submodule _ _) (finsupp.single i r : add_monoid_algebra _ _) =
    direct_sum.of (λ i : ι, grade R i) i ⟨finsupp.single i r, single_mem_grade _ _⟩ :=
decompose_aux_single _ _ _

/-- `add_monoid_algebra.gradesby` describe an internally graded algebra -/
lemma grade_by.is_internal : direct_sum.is_internal (grade_by R f) :=
direct_sum.decomposition.is_internal _

/-- `add_monoid_algebra.grades` describe an internally graded algebra -/
lemma grade.is_internal : direct_sum.is_internal (grade R : ι → submodule R _) :=
direct_sum.decomposition.is_internal _

end add_monoid_algebra

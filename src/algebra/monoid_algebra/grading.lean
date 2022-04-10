/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.finsupp
import algebra.monoid_algebra.basic
import algebra.direct_sum.internal

/-!
# Internal grading of an `add_monoid_algebra`

In this file, we show that an `add_monoid_algebra` has an internal direct sum structure.

## Main results

* `add_monoid_algebra.grade_by R f i`: the `i`th grade of an `add_monoid_algebra R M` given by the
  degree function `f`.
* `add_monoid_algebra.grade R i`: the `i`th grade of an `add_monoid_algebra R M` when the degree
  function is the identity.
* `add_monoid_algebra.equiv_grade_by`: the equivalence between an `add_monoid_algebra` and the
  direct sum of its grades.
* `add_monoid_algebra.equiv_grade`: the equivalence between an `add_monoid_algebra` and the direct
  sum of its grades when the degree function is the identity.
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
    a ∈ ((finsupp.lsingle m).range : submodule R (add_monoid_algebra R M)) :=
begin
  rw [mem_grade_iff, finsupp.support_subset_singleton'],
  apply exists_congr,
  intros r,
  split; exact eq.symm
end

lemma grade_eq_lsingle_range (m : M) : grade R m = (finsupp.lsingle m).range :=
submodule.ext (mem_grade_iff' R m)

lemma single_mem_grade_by {R} [comm_semiring R] (f : M → ι) (i : ι) (m : M)
  (h : f m = i) (r : R) :
  finsupp.single m r ∈ grade_by R f i :=
begin
  intros x hx,
  rw finset.mem_singleton.mp (finsupp.support_single_subset hx),
  exact h
end

lemma single_mem_grade {R} [comm_semiring R] (i : M) (r : R) : finsupp.single i r ∈ grade R i :=
single_mem_grade_by _ _ _ rfl _

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
    { rw [finsupp.support_single_ne_zero H, finset.mem_singleton] at h,
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

/-- The canonical grade decomposition. -/
def to_grades_by : add_monoid_algebra R M →ₐ[R] ⨁ i : ι, grade_by R f i :=
add_monoid_algebra.lift R M _
{ to_fun := λ m, direct_sum.of (λ i : ι, grade_by R f i) (f m.to_add)
    ⟨finsupp.single m.to_add 1, single_mem_grade_by _ _ _ rfl _⟩,
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

/-- The canonical grade decomposition. -/
def to_grades : add_monoid_algebra R M →ₐ[R] ⨁ i : M, grade R i :=
to_grades_by (add_monoid_hom.id M)

lemma to_grades_by_single' (i : ι) (m : M) (h : f m = i) (r : R) :
  to_grades_by f (finsupp.single m r) =
    direct_sum.of (λ i : ι, grade_by R f i) i
      ⟨finsupp.single m r, single_mem_grade_by _ _ _ h _⟩ :=
begin
  refine (lift_single _ _ _).trans _,
  refine (direct_sum.of_smul _ _ _ _).symm.trans _,
  apply direct_sum.of_eq_of_graded_monoid_eq,
  ext,
  { exact h },
  { rw graded_monoid.mk,
    simp only [mul_one, to_add_of_add, submodule.coe_mk, finsupp.smul_single',
      submodule.coe_smul_of_tower] }
end

@[simp]
lemma to_grades_by_single (m : M) (r : R) :
  to_grades_by f (finsupp.single m r) = direct_sum.of (λ i : ι, grade_by R f i) (f m)
    ⟨finsupp.single m r, single_mem_grade_by _ _ _ rfl _⟩ :=
by apply to_grades_by_single'

@[simp]
lemma to_grades_single (i : ι) (r : R) :
  to_grades (finsupp.single i r) =
    direct_sum.of (λ i : ι, grade R i) i ⟨finsupp.single i r, single_mem_grade _ _⟩ :=
by apply to_grades_by_single

@[simp]
lemma to_grades_by_coe {i : ι} (x : grade_by R f i) :
  to_grades_by f ↑x = direct_sum.of (λ i, grade_by R f i) i x :=
begin
  obtain ⟨x, hx⟩ := x,
  revert hx,
  refine finsupp.induction x _ _,
  { intros hx,
    symmetry,
    exact add_monoid_hom.map_zero _ },
  { intros m b y hmy hb ih hmby,
    have : disjoint (finsupp.single m b).support y.support,
    { simpa only [finsupp.support_single_ne_zero hb, finset.disjoint_singleton_left] },
    rw [mem_grade_by_iff, finsupp.support_add_eq this, finset.coe_union,
      set.union_subset_iff] at hmby,
    cases hmby with h1 h2,
    have : f m = i,
    { rwa [finsupp.support_single_ne_zero hb, finset.coe_singleton,
        set.singleton_subset_iff] at h1 },
    simp only [alg_hom.map_add, submodule.coe_mk, to_grades_by_single' f i m this],
    let ih' := ih h2,
    dsimp at ih',
    rw [ih', ← add_monoid_hom.map_add],
    apply direct_sum.of_eq_of_graded_monoid_eq,
    congr' 2 }
end

@[simp]
lemma to_grades_coe {i : ι} (x : grade R i) :
  to_grades ↑x = direct_sum.of (λ i, grade R i) i x :=
by apply to_grades_by_coe

/-- The canonical recombination of grades. -/
def of_grades_by : (⨁ i : ι, grade_by R f i) →ₐ[R] add_monoid_algebra R M :=
direct_sum.submodule_coe_alg_hom (grade_by R f)

/-- The canonical recombination of grades. -/
def of_grades : (⨁ i : ι, grade R i) →ₐ[R] add_monoid_algebra R ι :=
of_grades_by (add_monoid_hom.id ι)

@[simp]
lemma of_grades_by_of (i : ι) (x : grade_by R f i) :
  of_grades_by f (direct_sum.of (λ i, grade_by R f i) i x) = x :=
-- Use `simpa only` to help the elaborator decide what to unfold.
by simpa only [of_grades_by] using direct_sum.submodule_coe_alg_hom_of (grade_by R f) i x

@[simp]
lemma of_grades_of (i : ι) (x : grade R i) :
  of_grades (direct_sum.of (λ i, grade R i) i x) = x :=
by apply of_grades_by_of

@[simp]
lemma of_grades_by_comp_to_grades_by :
  (of_grades_by f).comp (to_grades_by f) = alg_hom.id R (add_monoid_algebra R M) :=
begin
  ext : 2,
  dsimp only [monoid_hom.coe_comp, alg_hom.coe_to_monoid_hom, alg_hom.coe_comp, function.comp_app,
    of_apply, alg_hom.coe_id, function.comp.left_id, id],
  rw [to_grades_by_single, of_grades_by_of, subtype.coe_mk],
end

@[simp]
lemma of_grades_comp_to_grades :
  of_grades.comp to_grades = alg_hom.id R (add_monoid_algebra R ι) :=
by apply of_grades_by_comp_to_grades_by

@[simp]
lemma of_grades_by_to_grades_by (x : add_monoid_algebra R M) :
  of_grades_by f (to_grades_by f x) = x :=
alg_hom.congr_fun (of_grades_by_comp_to_grades_by f) x

@[simp]
lemma of_grades_to_grades (x : add_monoid_algebra R ι) : of_grades x.to_grades = x :=
by apply of_grades_by_to_grades_by

@[simp]
lemma to_grades_by_comp_of_grades_by :
  (to_grades_by f).comp (of_grades_by f) = alg_hom.id R (⨁ i : ι, grade_by R f i) :=
begin
  ext : 2,
  dsimp only [direct_sum.lof_eq_of, linear_map.coe_comp, alg_hom.comp_to_linear_map,
    alg_hom.to_linear_map_apply, function.comp_app, alg_hom.coe_id, id],
  rw [of_grades_by_of, to_grades_by_coe],
end

@[simp]
lemma to_grades_comp_of_grades :
  to_grades.comp of_grades = alg_hom.id R (⨁ i : ι, grade R i) :=
by apply to_grades_by_comp_of_grades_by

@[simp]
lemma to_grades_by_of_grades_by (g : ⨁ i : ι, grade_by R f i) :
  to_grades_by f (of_grades_by f g) = g :=
alg_hom.congr_fun (to_grades_by_comp_of_grades_by f) g

@[simp]
lemma to_grades_of_grades (g : ⨁ i : ι, grade R i) : (of_grades g).to_grades = g :=
by apply to_grades_by_of_grades_by

/-- An `add_monoid_algebra R M` is equivalent as an algebra to the direct sum of its grades.
-/
@[simps]
def equiv_grades_by : add_monoid_algebra R M ≃ₐ[R] ⨁ i : ι, grade_by R f i :=
alg_equiv.of_alg_hom _ _ (to_grades_by_comp_of_grades_by f) (of_grades_by_comp_to_grades_by f)

/-- An `add_monoid_algebra R ι` is equivalent as an algebra to the direct sum of its grades.
-/
@[simps]
def equiv_grades : add_monoid_algebra R ι ≃ₐ[R] ⨁ i : ι, grade R i :=
equiv_grades_by (add_monoid_hom.id ι)

/-- `add_monoid_algebra.gradesby` describe an internally graded algebra -/
lemma grade_by.is_internal : direct_sum.submodule_is_internal (grade_by R f) :=
(equiv_grades_by f).symm.bijective

/-- `add_monoid_algebra.grades` describe an internally graded algebra -/
lemma grade.is_internal : direct_sum.submodule_is_internal (grade R : ι → submodule R _) :=
-- Use `simpa only` to help the elaborator decide what to unfold.
by simpa only [grade_by_id] using grade_by.is_internal (add_monoid_hom.id ι)

end add_monoid_algebra

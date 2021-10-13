/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.monoid_algebra.to_direct_sum
import linear_algebra.finsupp

/-!
# Internal grading of an `add_monoid_algebra`

In this file, we show that an `add_monoid_algebra` has an internal direct sum structure.

## Main results

* `add_monoid_algebra.grade R i`: the `i`th grade of an `add_monoid_algebra R ι`
* `add_monoid_algebra.equiv_grade`: the equivalence between an `add_monoid_algebra` and the direct
  sum of its grades.
* `add_monoid_algebra.grade.is_internal`: propositionally, the statement that
  `add_monoid_algebra.grade` defines an internal graded structure.
-/

noncomputable theory

namespace add_monoid_algebra
variables {ι : Type*} {R : Type*}

section
variables (R)

/-- The submodule corresponding to each grade. -/
abbreviation grade [comm_semiring R] (i : ι) : submodule R (add_monoid_algebra R ι) :=
(finsupp.lsingle i).range

end

variables {R} [decidable_eq ι] [add_monoid ι] [comm_semiring R]

open_locale direct_sum

instance grade.gsemiring : direct_sum.gsemiring (λ i : ι, grade R i) :=
direct_sum.gsemiring.of_submodules (grade R) ⟨1, rfl⟩ $ λ i j, begin
  rintros ⟨-, a, rfl⟩ ⟨-, b, rfl⟩,
  exact ⟨_, single_mul_single.symm⟩,
end

/-- The canonical grade decomposition. -/
def to_grades : add_monoid_algebra R ι →ₐ[R] ⨁ i : ι, grade R i :=
add_monoid_algebra.lift _ _ _
{ to_fun := λ i, direct_sum.of (λ i : ι, grade R i) i.to_add ⟨_, 1, rfl⟩,
  map_one' := rfl,
  map_mul' := λ i j, begin
    rw [direct_sum.of_mul_of, to_add_mul],
    congr,
    refine eq.trans _ single_mul_single.symm,
    rw one_mul,
    refl,
  end }

@[simp]
lemma to_grades_single (i : ι) (r : R) :
  to_grades (finsupp.single i r) =
    direct_sum.of (λ i : ι, grade R i) i ⟨finsupp.single _ _, r, rfl⟩ :=
begin
  refine (add_monoid_algebra.lift_single _ _ _).trans _,
  refine (direct_sum.of_smul _ _ _ _).symm.trans _,
  dsimp,
  congr' 1,
  ext : 1,
  refine (finsupp.smul_single _ _ _).trans _,
  rw [smul_eq_mul, mul_one],
  refl
end

@[simp]
lemma to_grades_coe {i : ι} (x : grade R i) :
  to_grades ↑x = direct_sum.of (λ i, grade R i) i x :=
begin
  obtain ⟨-, x, rfl⟩ := x,
  exact to_grades_single _ _,
end

/-- The canonical recombination of grades. -/
def of_grades : (⨁ i : ι, grade R i) →ₐ[R] add_monoid_algebra R ι :=
direct_sum.to_algebra R _ (λ i : ι, submodule.subtype _) rfl (λ _ _ _ _, rfl) (λ r, rfl)

@[simp]
lemma of_grades_of (i : ι) (x : grade R i) :
  of_grades (direct_sum.of (λ i, grade R i) i x) = x :=
direct_sum.to_add_monoid_of _ _ _

@[simp]
lemma of_grades_comp_to_grades : of_grades.comp to_grades = alg_hom.id R (add_monoid_algebra R ι) :=
begin
  ext : 2,
  dsimp,
  rw [to_grades_single, of_grades_of, subtype.coe_mk],
end

@[simp]
lemma of_grades_to_grades (x : add_monoid_algebra R ι) : of_grades x.to_grades = x :=
alg_hom.congr_fun of_grades_comp_to_grades x

@[simp]
lemma to_grades_comp_of_grades :
  to_grades.comp of_grades = alg_hom.id R (⨁ i : ι, grade R i) :=
begin
  ext : 2,
  dsimp [direct_sum.lof_eq_of],
  rw [of_grades_of, to_grades_coe],
end

@[simp]
lemma to_grades_of_grades (g : ⨁ i : ι, grade R i) : (of_grades g).to_grades = g :=
alg_hom.congr_fun to_grades_comp_of_grades g

/-- An `add_monoid_algebra R ι` is equivalent as an algebra to the direct sum of its grades.
-/
@[simps]
def equiv_grades : add_monoid_algebra R ι ≃ₐ[R] ⨁ i : ι, grade R i :=
alg_equiv.of_alg_hom _ _ to_grades_comp_of_grades of_grades_comp_to_grades

/-- `add_monoid_algebra.grades` describe an internally graded algebra -/
lemma grade.is_internal : direct_sum.submodule_is_internal (grade R : ι → submodule R _) :=
equiv_grades.symm.bijective

end add_monoid_algebra

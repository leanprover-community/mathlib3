/-
Copyright (c) 2022 Michael Blyth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Blyth
-/

import linear_algebra.projective_space.basic

/-!
# Independence in Projective Space

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define independence and dependence of families of elements in projective space.

## Implementation Details

We use an inductive definition to define the independence of points in projective
space, where the only constructor assumes an independent family of vectors from the
ambient vector space. Similarly for the definition of dependence.

## Results

- A family of elements is dependent if and only if it is not independent.
- Two elements are dependent if and only if they are equal.

# Future Work

- Define collinearity in projective space.
- Prove the axioms of a projective geometry are satisfied by the dependence relation.
- Define projective linear subspaces.
-/


variables {ι K V : Type*} [field K] [add_comm_group V] [module K V] {f : ι → ℙ K V}

namespace projectivization

/-- A linearly independent family of nonzero vectors gives an independent family of points
in projective space. -/
inductive independent : (ι → ℙ K V) → Prop
| mk (f : ι → V) (hf : ∀ i : ι, f i ≠ 0) (hl : linear_independent K f) :
    independent (λ i, mk K (f i) (hf i))

/-- A family of points in a projective space is independent if and only if the representative
vectors determined by the family are linearly independent. -/
lemma independent_iff : independent f ↔ linear_independent K (projectivization.rep ∘ f) :=
begin
  refine ⟨_, λ h, _⟩,
  { rintros ⟨ff, hff, hh⟩,
    choose a ha using λ (i : ι), exists_smul_eq_mk_rep K (ff i) (hff i),
    convert hh.units_smul a,
    ext i, exact (ha i).symm },
  { convert independent.mk _ _ h,
    { ext, simp only [mk_rep] },
    { intro i, apply rep_nonzero } }
end

/-- A family of points in projective space is independent if and only if the family of
submodules which the points determine is independent in the lattice-theoretic sense. -/
lemma independent_iff_complete_lattice_independent :
  independent f ↔ (complete_lattice.independent $ λ i, (f i).submodule) :=
begin
  refine ⟨_, λ h, _⟩,
  { rintros ⟨f, hf, hi⟩,
    simpa [submodule_mk, complete_lattice.independent_iff_linear_independent_of_ne_zero hf] },
  { rw independent_iff,
    refine h.linear_independent (projectivization.submodule ∘ f) (λ i, _) (λ i, _),
    { simpa only [function.comp_app, submodule_eq] using submodule.mem_span_singleton_self _, },
    { exact rep_nonzero (f i) } },
end

/-- A linearly dependent family of nonzero vectors gives a dependent family of points
in projective space. -/
inductive dependent : (ι → ℙ K V) → Prop
| mk (f : ι → V) (hf : ∀ i : ι, f i ≠ 0) (h : ¬linear_independent K f) :
    dependent (λ i, mk K (f i) (hf i))

/-- A family of points in a projective space is dependent if and only if their
representatives are linearly dependent. -/
lemma dependent_iff : dependent f ↔ ¬ linear_independent K (projectivization.rep ∘ f) :=
begin
  refine ⟨_, λ h, _⟩,
  { rintros ⟨ff, hff, hh1⟩,
    contrapose! hh1,
    choose a ha using λ (i : ι), exists_smul_eq_mk_rep K (ff i) (hff i),
    convert hh1.units_smul a⁻¹,
    ext i,
    simp only [← ha, inv_smul_smul, pi.smul_apply', pi.inv_apply, function.comp_app] },
  { convert dependent.mk _ _ h,
    { ext i, simp only [mk_rep] },
    { exact λ i, rep_nonzero (f i) } }
end

/-- Dependence is the negation of independence. -/
lemma dependent_iff_not_independent : dependent f ↔ ¬ independent f :=
by rw [dependent_iff, independent_iff]

/-- Independence is the negation of dependence. -/
lemma independent_iff_not_dependent : independent f ↔ ¬ dependent f :=
by rw [dependent_iff_not_independent, not_not]

/-- Two points in a projective space are dependent if and only if they are equal. -/
@[simp] lemma dependent_pair_iff_eq (u v : ℙ K V) : dependent ![u, v] ↔ u = v :=
begin
  simp_rw [dependent_iff_not_independent, independent_iff, linear_independent_fin2,
    function.comp_app, matrix.cons_val_one, matrix.head_cons,
    ne.def, matrix.cons_val_zero, not_and, not_forall, not_not,
    ← mk_eq_mk_iff' K _ _ (rep_nonzero u) (rep_nonzero v), mk_rep,
    imp_iff_right_iff],
  exact or.inl (rep_nonzero v),
end

/-- Two points in a projective space are independent if and only if the points are not equal. -/
@[simp] lemma independent_pair_iff_neq (u v : ℙ K V) : independent ![u, v] ↔ u ≠ v :=
by rw [independent_iff_not_dependent, dependent_pair_iff_eq u v]

end projectivization

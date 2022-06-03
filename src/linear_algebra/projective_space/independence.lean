/-
Copyright (c) 2022 Michael Blyth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Blyth
-/

import linear_algebra.projective_space.basic

/-!
# Independence in Projective Space

In this file we define independence and dependence of families of elements in projective space.

## Implementation Details

We use an inductive definition to define that a family of vectors is independent where the only
constructor assumes an independent family of vectors from the ambient vector space.
Similarly for the definition of dependence.

## Results

- A family of elements is dependent iff it is not independent.
- Two elements are dependent iff they are equal.

# Future Work

- Define collinearity in projective space.
- Prove the axioms of a projective geometry are satisfied by the dependece relation.
- Define projective linear subspaces.
-/


variables {K V : Type*} [field K] [add_comm_group V] [module K V]

namespace projectivization

/- A linearly independent familty of nonzero vectors gives an independent family of points
in the projective space. -/
inductive independent {ι : Type*} : (ι → ℙ K V) → Prop
| mk (f : ι → V) (hf : ∀ i : ι, f i ≠ 0) (hl : linear_independent K f) :
    independent (λ i, mk K (f i) (hf i))

/- A family of points in a projective space are independent iff their
representatives are linearly independent. -/
lemma independent_iff (ι : Type*) (f : ι → (ℙ K V)) : independent f ↔
  linear_independent K (projectivization.rep ∘ f) :=
begin
  split,
  { rintro h, induction h with ff hff hh,
    choose a ha using λ (i : ι), exists_smul_eq_mk_rep K (ff i) (hff i),
    convert hh.units_smul a,
    ext i, exact (ha i).symm },
  { intro h,
    convert independent.mk _ _ h,
    { ext, simp only [mk_rep] },
    { intro i, apply rep_nonzero } }
end

/- A linearly dependent family of nonzero vectors gives a dependent family of points
in the projective space. -/
inductive dependent {ι : Type*} : (ι → ℙ K V) → Prop
| mk (f : ι → V) (hf : ∀ i : ι, f i ≠ 0) (h : ¬linear_independent K f) :
    dependent (λ i, mk K (f i) (hf i))

/- A family of points in a projective space is dependent iff their
representatives are linearly dependent. -/
lemma dependent_iff (ι : Type*) (f : ι → (ℙ K V)) : dependent f ↔
  ¬ linear_independent K (projectivization.rep ∘ f) :=
begin
  split,
  { rw ← independent_iff,
    intros h1, induction h1 with ff hff hh1,
    contrapose! hh1, rw independent_iff at hh1,
    choose a ha using λ (i : ι), exists_smul_eq_mk_rep K (ff i) (hff i),
    convert hh1.units_smul a⁻¹,
    ext i, simp only [← ha, inv_smul_smul, pi.smul_apply', pi.inv_apply, function.comp_app] },
  { intro h,
    convert dependent.mk _ _ h,
    { ext, simp only [mk_rep] },
    { intro i, apply rep_nonzero } }
end

/- Dependence is the negation of independence. -/
lemma dependent_iff_not_independent {ι : Type*} (f : ι → ℙ K V) :
  dependent f ↔ ¬ independent f :=
by { rw [dependent_iff, independent_iff] }

/- Independence is the negation of dependence. -/
lemma independent_iff_not_dependent {ι : Type*} (f : ι → ℙ K V) :
  independent f ↔ ¬ dependent f :=
by { rw [dependent_iff, independent_iff, not_not] }


/- Two points in a projective space are dependent iff they are equal. -/
@[simp] lemma pair_dependent_iff_eq (u v : ℙ K V) : dependent ![u, v] ↔ u = v :=
begin
  simp_rw [dependent_iff_not_independent, independent_iff, linear_independent_fin2,
    function.comp_app, matrix.cons_val_one, matrix.head_cons,
    ne.def, matrix.cons_val_zero, not_and, not_forall, not_not,
    ← mk_eq_mk_iff' K _ _ (rep_nonzero u) (rep_nonzero v), mk_rep,
    imp_iff_right_iff],
  exact or.inl (rep_nonzero v),
end

/- Two points in a projective space are independent iff the points are not equal. -/
@[simp] lemma pair_independent_iff_neq (u v : ℙ K V) : (independent ![u, v]) ↔ u ≠ v :=
by { rw [independent_iff_not_dependent, pair_dependent_iff_eq u v] }

end projectivization

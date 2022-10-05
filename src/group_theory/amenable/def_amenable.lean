/-
Copyright (c) 2022 Matthias Uschold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Uschold.
-/

import .mean

/-!
# Amenable Groups

We introduce the concept of amenable groups.
A (topological) group is called `amenable` if there exists a left-invariant mean,
i.e. a mean (a positive, normalised linear function bounded_continuous_function G ℝ → ℝ )
that is invariant under left translation of the argument.


## Main Definitions

- `left_invariant_mean`  : mean with the property of being left-invariant
- `right_invariant_mean` : Alternative variant
- `bi_invariant_mean`    : Alternative variant
- `amenable`             : amenability of a group (defined by nonemptiness of left_invariant_mean)


We will see in `right_bi_invariance.lean` that the alternative variants yield
the same notion of amenability

## Implementation Notes

The notion of a mean is already defined in the file `mean.lean`. This
file defines the left translate of a function and uses this to define
amenability.

## References
* [C. Löh, *Geometric Group Theory*, Definition 9.1.1][loeh17]
* <https://en.wikipedia.org/wiki/Amenable_group>
* [A.L.T. Paterson, *Amenability*, Definition 0.2][Paterson1988]

## Tags

amenable, amenability, invariant mean, left invariant mean
-/

open mean
open classical
open bounded_continuous_function

variables {G:Type*} [topological_space G] [group G] [topological_group G]


/-- left-translate of a function by translating the argument -/
def left_translate (g : G) (f : bounded_continuous_function G ℝ) :
  bounded_continuous_function G ℝ :=
f.comp_continuous (continuous_map.mk (λ h, g⁻¹*h) (continuous_mul_left g⁻¹))



@[simp]
lemma left_translate_eval {g : G} {f : bounded_continuous_function G ℝ} :
  ∀(x:G), left_translate g f x = f(g⁻¹*x) := by tauto



instance left_translate_action  : mul_action G (bounded_continuous_function G ℝ) :=
{ to_has_smul := {smul := (λ g f, left_translate g f)},
  one_smul    :=
                  (begin
                    assume f : bounded_continuous_function G ℝ,
                    simp,
                    ext x,
                    by simp,
                  end),
  mul_smul    :=
                  (begin
                    assume g h f,
                    ext x,
                    simp,
                    congr' 1,
                    by simp [mul_assoc],
                  end )  }


@[simp]
lemma left_translate_smul_simp {g:G} {f:bounded_continuous_function G ℝ} :
  g•f = left_translate g f :=
by refl


/-- right-translate of a function by translating the argument -/
def right_translate (g : G) (f : bounded_continuous_function G ℝ) :
  bounded_continuous_function G ℝ :=
f.comp_continuous (continuous_map.mk (λ h, h*g) (continuous_mul_right g))

@[simp]
lemma right_translate_eval {g : G} {f : bounded_continuous_function G ℝ} :
  ∀(x:G), right_translate g f x = f(x*g) :=
by tauto



/--It is an easy (but important) fact that left and right-translation commute-/
lemma left_right_translate_commute {g h: G} {f : bounded_continuous_function G ℝ} :
  right_translate h (left_translate g f) = left_translate g (right_translate h f) :=
begin
  ext x,
  simp,
  congr' 1,
  by simp [mul_assoc],
end


section invariance_structures

/-!
### Invariance structures

We will defines structures for left-, right- and bi-invariant means.

-/

variable (G)

/--Left invariant means are means that are left invariant-/
structure left_invariant_mean extends mean G := mk ::
(left_invariance: ∀(g:G), ∀(f: bounded_continuous_function G ℝ), lin_map (g•f) = lin_map f)

instance : has_coe (left_invariant_mean G) (mean G) :=
  {coe := left_invariant_mean.to_mean}

@[simp]
lemma left_invariant_mean_eval {m: left_invariant_mean G}
  {f: bounded_continuous_function G ℝ} : m f = m.to_mean f :=
by refl

/--Right invariant means are means that are right invariant-/
structure right_invariant_mean extends mean G := mk ::
(right_invariance: ∀(g:G), ∀(f: bounded_continuous_function G ℝ),
  lin_map (right_translate g f) = lin_map f)

instance right_inv_mean_coe : has_coe (right_invariant_mean G) (mean G) :=
  {coe := right_invariant_mean.to_mean}

/--Bi-invariant means are means that are left and right invariant-/
structure bi_invariant_mean extends left_invariant_mean G := mk ::
(right_invariance: ∀(g:G), ∀(f: bounded_continuous_function G ℝ),
  lin_map (right_translate g f) = lin_map f)

instance : has_coe (bi_invariant_mean G) (left_invariant_mean G) :=
  {coe := bi_invariant_mean.to_left_invariant_mean}
end invariance_structures

/-- A group is amenable if there exists a left-invariant mean-/
@[simp]
def amenable (G:Type*)  [topological_space G] [group G] [topological_group G] : Prop :=
nonempty (left_invariant_mean G)


/-- For amenable groups, we can pick a left-invariant mean.
This is a noncomputable process.
-/
noncomputable def invmean_of_amenable {G:Type*}
  [topological_space G] [group G] [topological_group G]
  (G_am : amenable G) : left_invariant_mean G :=
classical.choice G_am

/--If we can exhibit a mean, the group is amenable-/
lemma amenable_of_invmean
  {G:Type*}  [topological_space G] [group G] [topological_group G]
  (m : left_invariant_mean G) : amenable G :=
nonempty.intro m

/-
Copyright (c) 2022 Matthias Uschold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Matthias Uschold.
-/
import .def_amenable
import topology.continuous_function.bounded
import topology.continuous_function.basic


/-!
# Quotients of Amenable groups

In this file, we prove that quotients of amenable groups are again amenable

## Main Statements
- `amenable_of_quotient'`  : If G →* H is a surjective group homomorphism and G is amenable,
                            then so is H.
- `amenable_of_quotient`   : If G is amenable, then so is G/N for every normal subgroup N.
- `amenable_of_iso`        : Amenability is preserved under (multiplicative) isomorphisms.


## References
* [C. Löh, *Geometric Group Theory*, Proposition 9.1.6 (2)][loeh17]
* [A.L.T. Paterson, *Amenability*, Proposition 0.16 (2)][Paterson1988]


## Tags
quotients, amenable, amenability
-/



open classical
open function



variables
{G:Type*}
[group G]

{H:Type*}
[group H]

(π: G →* H)
(pi_surj : surjective π)


namespace amenable_quotient

open mean

/--The pushforward mean is left-invariant if the
map is surjective-/
lemma mean_pushforward_leftinv
  (m : left_invariant_mean G)
  (pi_surj : surjective π)
  : ∀(h:H), ∀(f: bounded_continuous_function H ℝ),
        (mean_pushforward π m) (left_translate h f)
      = (mean_pushforward π m) f
:= begin
  assume h : H,
  assume f : bounded_continuous_function H ℝ,

  -- h has a preimage under π
  have : ∃ (g:G), π g = h
        := by tauto,
  rcases this with ⟨g, pi_gh⟩,

  --main step: The pullback of (left_translate h f)
  -- is the left_translate of (via g) the pullback of f
  have translate_pullback:
      pull_bcont π (left_translate h f) = left_translate g (pull_bcont π f),
  {
    ext (x:G),
    calc  pull_bcont π (left_translate h f) x
        = (left_translate h f) (π x)
          : by tauto
    ... = f (h⁻¹*(π x))
          : by tauto
    ... = f ((π g)⁻¹ * (π x))
          : by rw pi_gh
    ... = f ((π (g⁻¹)) * (π x))
          : by norm_num
    ... = f (π (g⁻¹ * x))
          : by simp[mul_hom.map_mul]
    ... = (pull_bcont π f) (g⁻¹ * x)
          : by tauto
    ... = (left_translate g (pull_bcont π f)) x
          : by tauto,
  },

  calc  (mean_pushforward π m) (left_translate h f)
      = m (pull_bcont π (left_translate h f))
        : by tauto
  ... = m (left_translate g (pull_bcont π f))
        : by rw translate_pullback
  ... = m (pull_bcont π f)
        : by exact m.left_invariance _ _
  ... = (mean_pushforward π m) f
        : by tauto,
end

/-- pushforward invariant mean-/
@[simp]
noncomputable def inv_mean_pushforward
  (m : left_invariant_mean G)
  (pi_surj : surjective π)
  : left_invariant_mean H
:= left_invariant_mean.mk (mean_pushforward π m)
                  (mean_pushforward_leftinv π  m pi_surj)


end amenable_quotient


/--The target group is amenable if π is surjective -/
theorem amenable_of_quotient'
  (pi_surj : surjective π)
  (G_am: amenable G)
  : amenable H
:= amenable_of_invmean (amenable_quotient.inv_mean_pushforward π (invmean_of_amenable G_am) pi_surj)

/--Formulation with quotients-/
theorem amenable_of_quotient
  {N : subgroup G}
  (nN : N.normal)
  (G_am: amenable G)
  : amenable (G⧸N)
:= amenable_of_quotient' _ (quotient_group.mk'_surjective N) G_am



-- preparations for amenable of iso




/--a multiplicative homomorphism between groups is a monoid homomorphism-/
def monoidhom_of_mulhom
  (f: mul_hom G H)
  : G →* H
:= monoid_hom.mk f.to_fun
      (begin
        have : f.to_fun 1 * f.to_fun 1 = f.to_fun 1,
        {
          calc  f.to_fun 1 * f.to_fun 1
              = f.to_fun (1*1)
                : by rw f.map_mul'
          ... = f.to_fun 1
                : by congr'; by group,
        },
        by finish,
      end)
    f.map_mul'

@[simp]
lemma monoidhom_of_mulhom_to_fun
   {f: mul_hom G H}
  : (monoidhom_of_mulhom f).to_fun = f.to_fun
:= by refl

/--Amenability is preserved under (multiplicative) isomorphisms-/
theorem amenable_of_iso
  {H : Type*} [group H]
  (i : G ≃* H)
  (G_am : amenable G)
  : amenable H
:= begin
  -- we obtain a surjective group hom G →* H
  let p: G →* H := monoidhom_of_mulhom i.to_mul_hom,
  have p_surj : surjective p,
  {
    dsimp[p],
    change surjective (monoidhom_of_mulhom i.to_mul_hom).to_fun,
    rw monoidhom_of_mulhom_to_fun,
    exact mul_equiv.surjective i,
  },
  exact amenable_of_quotient' p p_surj G_am,
end
